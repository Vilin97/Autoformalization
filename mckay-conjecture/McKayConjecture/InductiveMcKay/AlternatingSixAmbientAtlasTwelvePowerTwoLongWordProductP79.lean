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

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (0 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (0 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - (2 : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - (2 : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (0 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (0 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (0 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + (2 : ℂ) * ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + (2 : ℂ) * ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (0 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (0 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (0 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (0 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (0 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (0 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (0 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (1 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (1 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (1 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (1 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (1 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (1 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (1 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (1 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (1 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (1 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (1 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (1 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (2 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (2 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (2 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (2 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (2 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (2 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (2 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (2 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (2 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (2 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (2 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (2 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (3 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (3 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (3 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (3 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (3 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (3 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (3 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (3 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (3 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (3 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (3 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (3 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (4 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) + (2 : ℂ) * ζ ^ 4 + ζ ^ 8 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) + (2 : ℂ) * ζ ^ 4 + ζ ^ 8 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (4 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((6 : ℂ) - (4 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((6 : ℂ) - (4 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (4 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + (2 : ℂ) * ζ ^ 4) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + (2 : ℂ) * ζ ^ 4)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (4 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - (2 : ℂ) * ζ ^ 4) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - (2 : ℂ) * ζ ^ 4)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (4 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + (2 : ℂ) * ζ ^ 4 + ζ ^ 12) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + (2 : ℂ) * ζ ^ 4 + ζ ^ 12)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (4 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) + (4 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 12) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) + (4 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 12)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (4 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (4 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 - ζ ^ 12) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8 - ζ ^ 12)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (4 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (4 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (4 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (4 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (5 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((3 : ℂ) - (2 : ℂ) * ζ ^ 4 + ζ ^ 8 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((3 : ℂ) - (2 : ℂ) * ζ ^ 4 + ζ ^ 8 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (5 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (5 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((3 : ℂ) - (2 : ℂ) * ζ ^ 4 + ζ ^ 8 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((3 : ℂ) - (2 : ℂ) * ζ ^ 4 + ζ ^ 8 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (5 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (5 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) + (2 : ℂ) * ζ ^ 8 - ζ ^ 12) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) + (2 : ℂ) * ζ ^ 8 - ζ ^ 12)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (5 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (5 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) + (2 : ℂ) * ζ ^ 8 - ζ ^ 12) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) + (2 : ℂ) * ζ ^ 8 - ζ ^ 12)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (5 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 4 - ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 4 - ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (5 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (5 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (5 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (5 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (6 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (6 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (6 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((3 : ℂ) - ζ ^ 8 - ζ ^ 16 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((3 : ℂ) - ζ ^ 8 - ζ ^ 16 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (6 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - (2 : ℂ) * ζ ^ 4) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - (2 : ℂ) * ζ ^ 4)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (6 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (6 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) + ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) + ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (6 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (6 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) + ζ ^ 8 - ζ ^ 12 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) + ζ ^ 8 - ζ ^ 12 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (6 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (6 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (6 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (6 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (7 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (7 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((3 : ℂ) - (2 : ℂ) * ζ ^ 4 + ζ ^ 8 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((3 : ℂ) - (2 : ℂ) * ζ ^ 4 + ζ ^ 8 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (7 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (7 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (7 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (7 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 4 + (2 : ℂ) * ζ ^ 8 - ζ ^ 12 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 4 + (2 : ℂ) * ζ ^ 8 - ζ ^ 12 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (7 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (7 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - (2 : ℂ) * ζ ^ 8 + ζ ^ 12 - ζ ^ 16 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - (2 : ℂ) * ζ ^ 8 + ζ ^ 12 - ζ ^ 16 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (7 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (7 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (7 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (7 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (8 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (8 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (8 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (8 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (8 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (8 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (8 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (8 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (8 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (8 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (8 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (8 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (9 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (9 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (9 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (9 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (9 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (9 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (9 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (9 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (9 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (9 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (9 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (9 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (10 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (10 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (10 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (10 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (10 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (10 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (10 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (10 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (10 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (10 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (10 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (10 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (11 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (11 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (11 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (11 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (11 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (11 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (11 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (11 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (11 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (11 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (11 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79
        (11 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

theorem alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_mul :
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixAB *
        alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB =
      alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix79 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry00_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry01_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry02_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry03_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry04_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry05_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry06_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry07_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry08_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry09_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry10_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longPrefix79_entry11_11

end InductiveMcKay
end McKayConjecture
