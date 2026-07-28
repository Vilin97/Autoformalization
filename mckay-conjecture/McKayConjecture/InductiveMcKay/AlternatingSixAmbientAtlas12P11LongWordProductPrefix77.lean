/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlas12P11LongWordData

/-!
# One checked ATLAS degree-12 power-eleven long-word multiplication

This split generated module keeps each 12 by 12 multiplication
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry00_00 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (0 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (0 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(1 : ℂ)
          - ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(1 : ℂ)
          - ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry00_01 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (0 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (0 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(3 : ℂ) + (3 : ℂ) * ζ ^ 4) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(3 : ℂ) + (3 : ℂ) * ζ ^ 4)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry00_02 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (0 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (0 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - (2 : ℂ) * ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - (2 : ℂ) * ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry00_03 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (0 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (0 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (1 : ℂ)
          + ζ ^ 4
          - (2 : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (1 : ℂ)
          + ζ ^ 4
          - (2 : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry00_04 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (0 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (0 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry00_05 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (0 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (0 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(1 : ℂ)
          - ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(1 : ℂ)
          - ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry00_06 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (0 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (0 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry00_07 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (0 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (0 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry00_08 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (0 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (0 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry00_09 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (0 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (0 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry00_10 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (0 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (0 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry00_11 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (0 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (0 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry01_00 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (1 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (1 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) + ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) + ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry01_01 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (1 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (1 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (3 : ℂ) * ζ ^ 4
          - (3 : ℂ) * ζ ^ 8
          + (3 : ℂ) * ζ ^ 12
          - (3 : ℂ) * ζ ^ 16
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (3 : ℂ) * ζ ^ 4
          - (3 : ℂ) * ζ ^ 8
          + (3 : ℂ) * ζ ^ 12
          - (3 : ℂ) * ζ ^ 16
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry01_02 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (1 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (1 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) + ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) + ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry01_03 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (1 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (1 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry01_04 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (1 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (1 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry01_05 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (1 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (1 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) + ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) + ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry01_06 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (1 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (1 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry01_07 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (1 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (1 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry01_08 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (1 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (1 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry01_09 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (1 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (1 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry01_10 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (1 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (1 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry01_11 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (1 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (1 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry02_00 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (2 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (2 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry02_01 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (2 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (2 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry02_02 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (2 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (2 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + (2 : ℂ) * ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + (2 : ℂ) * ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry02_03 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (2 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (2 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry02_04 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (2 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (2 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry02_05 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (2 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (2 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry02_06 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (2 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (2 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry02_07 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (2 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (2 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry02_08 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (2 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (2 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry02_09 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (2 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (2 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry02_10 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (2 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (2 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry02_11 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (2 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (2 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry03_00 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (3 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (3 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry03_01 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (3 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (3 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry03_02 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (3 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (3 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - (2 : ℂ) * ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - (2 : ℂ) * ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry03_03 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (3 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (3 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) + ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) + ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry03_04 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (3 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (3 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry03_05 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (3 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (3 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry03_06 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (3 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (3 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry03_07 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (3 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (3 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry03_08 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (3 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (3 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry03_09 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (3 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (3 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry03_10 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (3 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (3 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry03_11 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (3 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (3 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry04_00 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (4 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (4 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((4 : ℂ) - (2 : ℂ) * ζ ^ 4 + ζ ^ 8 - ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((4 : ℂ) - (2 : ℂ) * ζ ^ 4 + ζ ^ 8 - ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry04_01 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (4 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (4 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) - ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) - ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry04_02 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (4 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (4 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((3 : ℂ) - ζ ^ 4 + ζ ^ 8 - ζ ^ 12) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((3 : ℂ) - ζ ^ 4 + ζ ^ 8 - ζ ^ 12)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry04_03 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (4 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (4 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(4 : ℂ) + (2 : ℂ) * ζ ^ 4 - ζ ^ 8 + ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(4 : ℂ) + (2 : ℂ) * ζ ^ 4 - ζ ^ 8 + ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry04_04 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (4 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (4 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry04_05 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (4 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (4 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - ζ ^ 4 + ζ ^ 8 - (2 : ℂ) * ζ ^ 12) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - ζ ^ 4 + ζ ^ 8 - (2 : ℂ) * ζ ^ 12)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry04_06 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (4 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (4 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 + ζ ^ 12) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 + ζ ^ 12)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry04_07 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (4 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (4 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry04_08 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (4 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (4 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry04_09 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (4 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (4 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry04_10 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (4 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (4 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry04_11 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (4 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (4 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry05_00 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (5 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (5 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry05_01 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (5 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (5 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(7 : ℂ)
          + (3 : ℂ) * ζ ^ 4
          - (2 : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          + ζ ^ 16
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(7 : ℂ)
          + (3 : ℂ) * ζ ^ 4
          - (2 : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          + ζ ^ 16
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry05_02 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (5 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (5 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry05_03 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (5 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (5 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry05_04 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (5 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (5 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 12) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 12)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry05_05 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (5 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (5 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8 - ζ ^ 12) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8 - ζ ^ 12)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry05_06 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (5 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (5 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 12) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 12)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry05_07 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (5 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (5 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 12) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 12)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry05_08 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (5 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (5 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry05_09 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (5 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (5 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry05_10 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (5 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (5 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry05_11 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (5 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (5 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry06_00 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (6 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (6 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (4 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + ζ ^ 8
          - (3 : ℂ) * ζ ^ 12
          + ζ ^ 16
          - ζ ^ 20
          + ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (4 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + ζ ^ 8
          - (3 : ℂ) * ζ ^ 12
          + ζ ^ 16
          - ζ ^ 20
          + ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry06_01 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (6 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (6 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (3 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          - ζ ^ 8
          - (3 : ℂ) * ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (3 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          - ζ ^ 8
          - (3 : ℂ) * ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry06_02 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (6 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (6 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) + ζ ^ 4 + ζ ^ 8 + ζ ^ 12 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) + ζ ^ 4 + ζ ^ 8 + ζ ^ 12 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry06_03 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (6 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (6 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (2 : ℂ)
          - ζ ^ 4
          - ζ ^ 8
          - (3 : ℂ) * ζ ^ 12
          + (3 : ℂ) * ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (2 : ℂ)
          - ζ ^ 4
          - ζ ^ 8
          - (3 : ℂ) * ζ ^ 12
          + (3 : ℂ) * ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry06_04 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (6 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (6 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (ζ ^ 8 + ζ ^ 12 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(ζ ^ 8 + ζ ^ 12 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry06_05 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (6 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (6 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - ζ ^ 4 + ζ ^ 8 - ζ ^ 12) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - ζ ^ 4 + ζ ^ 8 - ζ ^ 12)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry06_06 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (6 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (6 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 8 + ζ ^ 12 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 8 + ζ ^ 12 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry06_07 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (6 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (6 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry06_08 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (6 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (6 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry06_09 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (6 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (6 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry06_10 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (6 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (6 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 4 + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry06_11 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (6 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (6 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry07_00 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (7 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (7 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry07_01 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (7 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (7 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry07_02 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (7 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (7 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 + (2 : ℂ) * ζ ^ 12 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 + (2 : ℂ) * ζ ^ 12 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry07_03 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (7 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (7 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (2 : ℂ)
          - ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (2 : ℂ)
          - ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry07_04 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (7 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (7 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry07_05 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (7 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (7 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry07_06 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (7 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (7 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - (2 : ℂ) * ζ ^ 8 + ζ ^ 16 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - (2 : ℂ) * ζ ^ 8 + ζ ^ 16 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry07_07 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (7 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (7 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 + ζ ^ 12 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 + ζ ^ 12 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry07_08 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (7 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (7 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry07_09 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (7 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (7 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry07_10 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (7 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (7 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry07_11 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (7 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (7 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry08_00 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (8 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (8 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry08_01 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (8 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (8 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry08_02 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (8 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (8 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry08_03 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (8 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (8 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry08_04 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (8 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (8 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry08_05 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (8 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (8 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry08_06 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (8 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (8 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry08_07 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (8 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (8 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry08_08 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (8 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (8 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry08_09 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (8 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (8 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry08_10 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (8 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (8 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry08_11 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (8 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (8 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry09_00 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (9 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (9 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry09_01 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (9 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (9 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry09_02 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (9 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (9 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry09_03 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (9 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (9 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry09_04 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (9 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (9 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry09_05 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (9 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (9 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry09_06 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (9 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (9 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry09_07 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (9 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (9 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry09_08 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (9 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (9 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry09_09 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (9 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (9 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry09_10 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (9 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (9 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry09_11 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (9 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (9 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry10_00 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (10 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (10 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry10_01 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (10 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (10 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry10_02 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (10 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (10 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry10_03 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (10 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (10 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry10_04 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (10 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (10 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry10_05 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (10 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (10 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry10_06 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (10 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (10 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry10_07 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (10 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (10 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry10_08 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (10 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (10 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry10_09 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (10 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (10 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry10_10 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (10 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (10 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry10_11 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (10 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (10 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry11_00 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (11 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (11 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry11_01 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (11 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (11 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry11_02 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (11 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (11 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry11_03 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (11 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (11 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
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
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry11_04 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (11 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (11 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry11_05 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (11 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (11 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry11_06 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (11 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (11 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry11_07 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (11 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (11 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry11_08 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (11 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (11 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry11_09 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (11 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (11 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry11_10 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (11 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (11 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlas12P11_longPrefix77_entry11_11 :
    (alternatingSixAmbientAtlas12P11LongMatrixAB
        * alternatingSixAmbientAtlas12P11LongMatrixABB)
          (11 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlas12P11LongPrefix77
        (11 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlas12P11LongMatrixAB,
    alternatingSixAmbientAtlas12P11LongMatrixABB,
    alternatingSixAmbientAtlas12P11LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

theorem alternatingSixAmbientAtlas12P11_longPrefix77_mul :
    alternatingSixAmbientAtlas12P11LongMatrixAB *
        alternatingSixAmbientAtlas12P11LongMatrixABB =
      alternatingSixAmbientAtlas12P11LongPrefix77 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry00_00
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry00_01
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry00_02
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry00_03
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry00_04
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry00_05
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry00_06
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry00_07
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry00_08
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry00_09
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry00_10
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry00_11
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry01_00
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry01_01
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry01_02
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry01_03
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry01_04
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry01_05
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry01_06
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry01_07
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry01_08
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry01_09
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry01_10
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry01_11
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry02_00
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry02_01
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry02_02
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry02_03
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry02_04
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry02_05
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry02_06
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry02_07
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry02_08
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry02_09
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry02_10
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry02_11
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry03_00
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry03_01
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry03_02
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry03_03
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry03_04
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry03_05
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry03_06
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry03_07
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry03_08
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry03_09
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry03_10
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry03_11
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry04_00
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry04_01
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry04_02
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry04_03
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry04_04
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry04_05
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry04_06
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry04_07
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry04_08
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry04_09
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry04_10
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry04_11
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry05_00
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry05_01
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry05_02
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry05_03
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry05_04
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry05_05
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry05_06
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry05_07
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry05_08
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry05_09
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry05_10
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry05_11
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry06_00
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry06_01
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry06_02
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry06_03
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry06_04
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry06_05
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry06_06
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry06_07
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry06_08
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry06_09
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry06_10
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry06_11
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry07_00
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry07_01
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry07_02
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry07_03
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry07_04
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry07_05
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry07_06
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry07_07
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry07_08
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry07_09
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry07_10
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry07_11
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry08_00
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry08_01
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry08_02
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry08_03
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry08_04
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry08_05
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry08_06
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry08_07
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry08_08
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry08_09
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry08_10
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry08_11
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry09_00
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry09_01
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry09_02
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry09_03
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry09_04
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry09_05
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry09_06
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry09_07
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry09_08
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry09_09
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry09_10
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry09_11
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry10_00
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry10_01
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry10_02
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry10_03
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry10_04
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry10_05
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry10_06
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry10_07
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry10_08
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry10_09
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry10_10
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry10_11
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry11_00
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry11_01
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry11_02
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry11_03
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry11_04
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry11_05
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry11_06
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry11_07
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry11_08
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry11_09
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry11_10
  · exact alternatingSixAmbientAtlas12P11_longPrefix77_entry11_11

end InductiveMcKay
end McKayConjecture
