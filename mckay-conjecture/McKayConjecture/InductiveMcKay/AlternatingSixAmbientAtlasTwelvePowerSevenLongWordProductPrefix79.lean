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

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (0 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (0 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) + ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) + ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (0 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (0 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) + (2 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) + (2 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (0 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (0 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (0 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (0 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (0 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (0 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (0 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (0 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (0 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (0 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (0 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (0 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (0 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (0 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (0 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (0 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (0 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (0 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (0 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (0 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (1 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (1 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (1 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (1 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (1 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (1 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (1 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (1 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (1 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (1 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (1 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (1 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (1 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (1 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (1 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (1 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (1 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (1 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (1 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (1 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (1 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (1 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (1 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (1 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (2 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (2 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (2 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (2 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (2 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (2 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (2 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (2 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (2 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (2 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (2 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (2 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (2 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (2 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (2 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (2 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (2 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (2 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (2 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (2 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (2 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (2 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (2 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (2 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (3 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (3 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (3 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (3 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (3 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (3 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (3 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (3 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (3 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (3 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (3 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (3 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (3 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (3 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (3 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (3 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (3 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (3 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (3 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (3 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (3 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (3 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (3 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (3 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (4 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (4 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((4 : ℂ) + ζ ^ 4 - ζ ^ 8 - (2 : ℂ) * ζ ^ 16 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((4 : ℂ) + ζ ^ 4 - ζ ^ 8 - (2 : ℂ) * ζ ^ 16 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (4 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (4 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(2 : ℂ) * ζ ^ 4
          + (6 : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(2 : ℂ) * ζ ^ 4
          + (6 : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (4 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (4 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) + ζ ^ 4 - (2 : ℂ) * ζ ^ 8 - ζ ^ 16 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) + ζ ^ 4 - (2 : ℂ) * ζ ^ 8 - ζ ^ 16 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (4 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (4 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) - ζ ^ 4 + (2 : ℂ) * ζ ^ 8 + ζ ^ 16 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) - ζ ^ 4 + (2 : ℂ) * ζ ^ 8 + ζ ^ 16 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (4 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (4 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (3 : ℂ)
          - (2 : ℂ) * ζ ^ 8
          - ζ ^ 12
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (3 : ℂ)
          - (2 : ℂ) * ζ ^ 8
          - ζ ^ 12
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (4 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (4 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((6 : ℂ) + (2 : ℂ) * ζ ^ 12 - (4 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((6 : ℂ) + (2 : ℂ) * ζ ^ 12 - (4 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (4 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (4 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 8 - ζ ^ 12 + ζ ^ 16 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 8 - ζ ^ 12 + ζ ^ 16 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (4 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (4 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (4 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (4 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (4 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (4 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) - (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) - (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (4 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (4 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (4 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (4 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (5 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (5 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 4 + (3 : ℂ) * ζ ^ 8 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 4 + (3 : ℂ) * ζ ^ 8 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (5 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (5 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) - ζ ^ 8 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) - ζ ^ 8 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (5 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (5 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 4 + (3 : ℂ) * ζ ^ 8 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 4 + (3 : ℂ) * ζ ^ 8 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (5 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (5 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) - ζ ^ 8 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) - ζ ^ 8 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (5 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (5 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((3 : ℂ) + ζ ^ 12 - (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((3 : ℂ) + ζ ^ 12 - (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (5 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (5 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(3 : ℂ) + ζ ^ 8 + ζ ^ 16 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(3 : ℂ) + ζ ^ 8 + ζ ^ 16 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (5 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (5 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((3 : ℂ) + ζ ^ 12 - (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((3 : ℂ) + ζ ^ 12 - (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (5 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (5 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(3 : ℂ) + ζ ^ 8 + ζ ^ 16 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(3 : ℂ) + ζ ^ 8 + ζ ^ 16 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (5 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (5 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (5 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (5 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (5 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (5 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (5 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (5 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (6 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (6 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (6 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (6 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) * ζ ^ 4 - (2 : ℂ) * ζ ^ 8 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) * ζ ^ 4 - (2 : ℂ) * ζ ^ 8 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (6 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (6 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (ζ ^ 4 + ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(ζ ^ 4 + ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (6 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (6 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) - ζ ^ 4 + (2 : ℂ) * ζ ^ 8 + ζ ^ 16 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) - ζ ^ 4 + (2 : ℂ) * ζ ^ 8 + ζ ^ 16 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (6 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (6 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (6 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (6 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) + ζ ^ 4 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) + ζ ^ 4 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (6 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (6 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) + ζ ^ 8 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) + ζ ^ 8 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (6 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (6 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) + ζ ^ 4 + (2 : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) + ζ ^ 4 + (2 : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (6 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (6 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (6 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (6 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (6 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (6 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (6 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (6 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) - ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) - ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (7 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (7 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (7 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (7 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 4 + (3 : ℂ) * ζ ^ 8 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 4 + (3 : ℂ) * ζ ^ 8 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (7 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (7 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (7 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (7 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(2 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          - (3 : ℂ) * ζ ^ 8
          + ζ ^ 16
          - ζ ^ 20
          + ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(2 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          - (3 : ℂ) * ζ ^ 8
          + ζ ^ 16
          - ζ ^ 20
          + ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (7 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (7 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (7 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (7 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (7 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (7 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (7 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (7 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) + ζ ^ 4 + ζ ^ 8 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) + ζ ^ 4 + ζ ^ 8 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (7 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (7 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (7 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (7 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (7 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (7 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (7 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (7 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (8 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (8 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (8 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (8 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (8 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (8 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (8 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (8 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (8 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (8 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (8 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (8 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (8 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (8 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (8 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (8 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (8 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (8 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (8 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (8 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (8 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (8 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (8 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (8 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (9 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (9 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (9 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (9 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (9 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (9 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (9 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (9 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (9 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (9 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (9 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (9 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (9 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (9 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (9 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (9 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (9 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (9 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (9 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (9 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (9 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (9 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (9 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (9 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (10 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (10 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (10 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (10 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (10 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (10 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (10 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (10 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (10 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (10 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (10 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (10 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (10 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (10 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (10 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (10 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (10 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (10 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (10 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (10 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (10 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (10 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (10 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (10 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_00 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (11 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (11 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_01 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (11 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (11 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_02 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (11 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (11 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_03 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (11 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (11 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_04 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (11 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (11 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_05 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (11 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (11 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_06 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (11 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (11 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_07 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (11 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (11 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_08 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (11 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (11 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_09 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (11 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (11 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_10 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (11 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (11 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_11 :
    (alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB)
          (11 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79
        (11 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

theorem alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_mul :
    alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixAB *
        alternatingSixAmbientAtlasTwelvePowerSevenLongMatrixABBB =
      alternatingSixAmbientAtlasTwelvePowerSevenLongPrefix79 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry00_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry01_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry02_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry03_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry04_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry05_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry06_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry07_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry08_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry09_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry10_11
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_00
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_01
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_02
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_03
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_04
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_05
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_06
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_07
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_08
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_09
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_10
  · exact alternatingSixAmbientAtlasTwelvePowerSeven_longPrefix79_entry11_11

end InductiveMcKay
end McKayConjecture
