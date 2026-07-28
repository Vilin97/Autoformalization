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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (0 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (0 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (1 : ℂ)
          - (6 : ℂ) * ζ ^ 4
          + (5 : ℂ) * ζ ^ 8
          - ζ ^ 16
          + (3 : ℂ) * ζ ^ 20
          - (3 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (1 : ℂ)
          - (6 : ℂ) * ζ ^ 4
          + (5 : ℂ) * ζ ^ 8
          - ζ ^ 16
          + (3 : ℂ) * ζ ^ 20
          - (3 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (0 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (0 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(3 : ℂ) + ζ ^ 4 - ζ ^ 8 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(3 : ℂ) + ζ ^ 4 - ζ ^ 8 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (0 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(2 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          + ζ ^ 8
          - ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
          - ζ ^ 20
          + ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(2 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          + ζ ^ 8
          - ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
          - ζ ^ 20
          + ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (0 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(6 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + (3 : ℂ) * ζ ^ 8
          - (6 : ℂ) * ζ ^ 12
          + (5 : ℂ) * ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(6 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + (3 : ℂ) * ζ ^ 8
          - (6 : ℂ) * ζ ^ 12
          + (5 : ℂ) * ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (0 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(2 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          + ζ ^ 8
          - ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
          - ζ ^ 20
          + ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(2 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          + ζ ^ 8
          - ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
          - ζ ^ 20
          + ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (0 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(2 : ℂ)
          - (3 : ℂ) * ζ ^ 4
          - (2 : ℂ) * ζ ^ 8
          + ζ ^ 12
          - ζ ^ 16
          + (3 : ℂ) * ζ ^ 20
          - (3 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(2 : ℂ)
          - (3 : ℂ) * ζ ^ 4
          - (2 : ℂ) * ζ ^ 8
          + ζ ^ 12
          - ζ ^ 16
          + (3 : ℂ) * ζ ^ 20
          - (3 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (0 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (0 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - (4 : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - (4 : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (0 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (0 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (0 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (1 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((5 : ℂ) - ζ ^ 8 - ζ ^ 16 - (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((5 : ℂ) - ζ ^ 8 - ζ ^ 16 - (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (1 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(6 : ℂ) * ζ ^ 4
          + (5 : ℂ) * ζ ^ 8
          + ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(6 : ℂ) * ζ ^ 4
          + (5 : ℂ) * ζ ^ 8
          + ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (1 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((5 : ℂ) - ζ ^ 8 - ζ ^ 16 - (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((5 : ℂ) - ζ ^ 8 - ζ ^ 16 - (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (1 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(5 : ℂ)
          - (4 : ℂ) * ζ ^ 4
          + (5 : ℂ) * ζ ^ 8
          + ζ ^ 16
          + (4 : ℂ) * ζ ^ 20
          - (4 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(5 : ℂ)
          - (4 : ℂ) * ζ ^ 4
          + (5 : ℂ) * ζ ^ 8
          + ζ ^ 16
          + (4 : ℂ) * ζ ^ 20
          - (4 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (1 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (4 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          - ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (4 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          - ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (1 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(4 : ℂ)
          + ζ ^ 4
          + (3 : ℂ) * ζ ^ 8
          - (6 : ℂ) * ζ ^ 12
          + (6 : ℂ) * ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(4 : ℂ)
          + ζ ^ 4
          + (3 : ℂ) * ζ ^ 8
          - (6 : ℂ) * ζ ^ 12
          + (6 : ℂ) * ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (1 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (4 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          - ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (4 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          - ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (1 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(8 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          - (4 : ℂ) * ζ ^ 12
          + (5 : ℂ) * ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(8 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          - (4 : ℂ) * ζ ^ 12
          + (5 : ℂ) * ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (1 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) + ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) + ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (1 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) - (2 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) - (2 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (1 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) + ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) + ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (1 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (1 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - (3 : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - (3 : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (2 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (2 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(3 : ℂ) * ζ ^ 4 + ζ ^ 8 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(3 : ℂ) * ζ ^ 4 + ζ ^ 8 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (2 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (2 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + (3 : ℂ) * ζ ^ 8
          - ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (2 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + (3 : ℂ) * ζ ^ 8
          - ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (2 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(3 : ℂ) + ζ ^ 4 - (2 : ℂ) * ζ ^ 8 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(3 : ℂ) + ζ ^ 4 - (2 : ℂ) * ζ ^ 8 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (2 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (2 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(2 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + ζ ^ 8
          - (3 : ℂ) * ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(2 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + ζ ^ 8
          - (3 : ℂ) * ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (2 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(2 : ℂ)
          + ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(2 : ℂ)
          + ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (2 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(2 : ℂ) * ζ ^ 4
          - (2 : ℂ) * ζ ^ 8
          + ζ ^ 12
          - ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(2 : ℂ) * ζ ^ 4
          - (2 : ℂ) * ζ ^ 8
          + ζ ^ 12
          - ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (2 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (2 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - (2 : ℂ) * ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - (2 : ℂ) * ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (2 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (2 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (2 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (3 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (ζ ^ 4 - (3 : ℂ) * ζ ^ 8 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(ζ ^ 4 - (3 : ℂ) * ζ ^ 8 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (3 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (2 : ℂ) * ζ ^ 4
          - (3 : ℂ) * ζ ^ 8
          + ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (2 : ℂ) * ζ ^ 4
          - (3 : ℂ) * ζ ^ 8
          + ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (3 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (3 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (3 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (2 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          - ζ ^ 8
          + ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (2 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          - ζ ^ 8
          + ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (3 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (4 : ℂ)
          + ζ ^ 4
          - ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (4 : ℂ)
          + ζ ^ 4
          - ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (3 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 4 - ζ ^ 8 + ζ ^ 12 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (3 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) * ζ ^ 4 + ζ ^ 12 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) * ζ ^ 4 + ζ ^ 12 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (3 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (3 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (3 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (3 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (3 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (4 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(6 : ℂ)
          - ζ ^ 4
          + (3 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + (3 : ℂ) * ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(6 : ℂ)
          - ζ ^ 4
          + (3 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + (3 : ℂ) * ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (4 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(6 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + (9 : ℂ) * ζ ^ 8
          - (6 : ℂ) * ζ ^ 12
          + (5 : ℂ) * ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(6 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + (9 : ℂ) * ζ ^ 8
          - (6 : ℂ) * ζ ^ 12
          + (5 : ℂ) * ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (4 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(6 : ℂ)
          - ζ ^ 4
          + (3 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + (3 : ℂ) * ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(6 : ℂ)
          - ζ ^ 4
          + (3 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + (3 : ℂ) * ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (4 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (3 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          - (3 : ℂ) * ζ ^ 8
          + ζ ^ 12
          - ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (3 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          - (3 : ℂ) * ζ ^ 8
          + ζ ^ 12
          - ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (4 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(4 : ℂ) + ζ ^ 4 - (4 : ℂ) * ζ ^ 8 - ζ ^ 12 + (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(4 : ℂ) + ζ ^ 4 - (4 : ℂ) * ζ ^ 8 - ζ ^ 12 + (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (4 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(12 : ℂ)
          + (3 : ℂ) * ζ ^ 4
          - (3 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
          + (4 : ℂ) * ζ ^ 20
          - (4 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(12 : ℂ)
          + (3 : ℂ) * ζ ^ 4
          - (3 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
          + (4 : ℂ) * ζ ^ 20
          - (4 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (4 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(4 : ℂ) + ζ ^ 4 - (4 : ℂ) * ζ ^ 8 - ζ ^ 12 + (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(4 : ℂ) + ζ ^ 4 - (4 : ℂ) * ζ ^ 8 - ζ ^ 12 + (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (4 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (2 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + (4 : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (2 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + (4 : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (4 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (4 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (8 : ℂ)
          - (4 : ℂ) * ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          + (4 : ℂ) * ζ ^ 12
          - (4 : ℂ) * ζ ^ 16
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (8 : ℂ)
          - (4 : ℂ) * ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          + (4 : ℂ) * ζ ^ 12
          - (4 : ℂ) * ζ ^ 16
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (4 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (4 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (4 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - ζ ^ 4 + (3 : ℂ) * ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - ζ ^ 4 + (3 : ℂ) * ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (5 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + (2 : ℂ) * ζ ^ 8 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + (2 : ℂ) * ζ ^ 8 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (5 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(8 : ℂ)
          - (4 : ℂ) * ζ ^ 4
          + (8 : ℂ) * ζ ^ 8
          - (5 : ℂ) * ζ ^ 12
          + (5 : ℂ) * ζ ^ 16
          + (3 : ℂ) * ζ ^ 20
          - (3 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(8 : ℂ)
          - (4 : ℂ) * ζ ^ 4
          + (8 : ℂ) * ζ ^ 8
          - (5 : ℂ) * ζ ^ 12
          + (5 : ℂ) * ζ ^ 16
          + (3 : ℂ) * ζ ^ 20
          - (3 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (5 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + (2 : ℂ) * ζ ^ 8 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + (2 : ℂ) * ζ ^ 8 - ζ ^ 16 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (5 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(7 : ℂ)
          - ζ ^ 4
          + (4 : ℂ) * ζ ^ 8
          - (4 : ℂ) * ζ ^ 12
          + (5 : ℂ) * ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(7 : ℂ)
          - ζ ^ 4
          + (4 : ℂ) * ζ ^ 8
          - (4 : ℂ) * ζ ^ 12
          + (5 : ℂ) * ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (5 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) * ζ ^ 4 - ζ ^ 8 - ζ ^ 12 + ζ ^ 16 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) * ζ ^ 4 - ζ ^ 8 - ζ ^ 12 + ζ ^ 16 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (5 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(10 : ℂ)
          + (3 : ℂ) * ζ ^ 4
          - (7 : ℂ) * ζ ^ 8
          - (4 : ℂ) * ζ ^ 12
          + (3 : ℂ) * ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(10 : ℂ)
          + (3 : ℂ) * ζ ^ 4
          - (7 : ℂ) * ζ ^ 8
          - (4 : ℂ) * ζ ^ 12
          + (3 : ℂ) * ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (5 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) * ζ ^ 4 - ζ ^ 8 - ζ ^ 12 + ζ ^ 16 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) * ζ ^ 4 - ζ ^ 8 - ζ ^ 12 + ζ ^ 16 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (5 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(8 : ℂ)
          - (3 : ℂ) * ζ ^ 8
          - ζ ^ 12
          + ζ ^ 16
          + (3 : ℂ) * ζ ^ 20
          - (3 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(8 : ℂ)
          - (3 : ℂ) * ζ ^ 8
          - ζ ^ 12
          + ζ ^ 16
          + (3 : ℂ) * ζ ^ 20
          - (3 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (5 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) + ζ ^ 4 - (2 : ℂ) * ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) + ζ ^ 4 - (2 : ℂ) * ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (5 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (4 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          - (2 : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (4 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          - (2 : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (5 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) + ζ ^ 4 - (2 : ℂ) * ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) + ζ ^ 4 - (2 : ℂ) * ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (5 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (5 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (6 : ℂ)
          - (3 : ℂ) * ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          + (3 : ℂ) * ζ ^ 12
          - (3 : ℂ) * ζ ^ 16
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (6 : ℂ)
          - (3 : ℂ) * ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          + (3 : ℂ) * ζ ^ 12
          - (3 : ℂ) * ζ ^ 16
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (6 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(1 : ℂ)
          - ζ ^ 4
          + (4 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(1 : ℂ)
          - ζ ^ 4
          + (4 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (6 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 4 + (3 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 4 + (3 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (6 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(5 : ℂ)
          - ζ ^ 4
          + (5 : ℂ) * ζ ^ 8
          - (3 : ℂ) * ζ ^ 12
          + (3 : ℂ) * ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(5 : ℂ)
          - ζ ^ 4
          + (5 : ℂ) * ζ ^ 8
          - (3 : ℂ) * ζ ^ 12
          + (3 : ℂ) * ζ ^ 16
          + (2 : ℂ) * ζ ^ 20
          - (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (6 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (4 : ℂ)
          + ζ ^ 4
          - (4 : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (4 : ℂ)
          + ζ ^ 4
          - (4 : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (6 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(4 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          - ζ ^ 8
          - ζ ^ 12
          + ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(4 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          - ζ ^ 8
          - ζ ^ 12
          + ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (6 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(4 : ℂ) + ζ ^ 4 - ζ ^ 12 + (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(4 : ℂ) + ζ ^ 4 - ζ ^ 12 + (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (6 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(6 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          - (3 : ℂ) * ζ ^ 8
          - ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(6 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          - (3 : ℂ) * ζ ^ 8
          - ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
          + ζ ^ 20
          - ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (6 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (4 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + (3 : ℂ) * ζ ^ 8
          + ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (4 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + (3 : ℂ) * ζ ^ 8
          + ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (6 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - ζ ^ 4 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - ζ ^ 4 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (6 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (4 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (4 : ℂ)
          - (2 : ℂ) * ζ ^ 4
          + ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          - (2 : ℂ) * ζ ^ 16
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (6 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - ζ ^ 4 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - ζ ^ 4 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (6 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (6 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (7 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (6 : ℂ)
          + ζ ^ 4
          - (3 : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          - (3 : ℂ) * ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (6 : ℂ)
          + ζ ^ 4
          - (3 : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 12
          - (3 : ℂ) * ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (7 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (4 : ℂ)
          - (4 : ℂ) * ζ ^ 8
          + (3 : ℂ) * ζ ^ 12
          - (3 : ℂ) * ζ ^ 16
          - ζ ^ 20
          + ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (4 : ℂ)
          - (4 : ℂ) * ζ ^ 8
          + (3 : ℂ) * ζ ^ 12
          - (3 : ℂ) * ζ ^ 16
          - ζ ^ 20
          + ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (7 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (2 : ℂ)
          + ζ ^ 4
          - (2 : ℂ) * ζ ^ 8
          + ζ ^ 12
          - ζ ^ 16
          - ζ ^ 20
          + ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (2 : ℂ)
          + ζ ^ 4
          - (2 : ℂ) * ζ ^ 8
          + ζ ^ 12
          - ζ ^ 16
          - ζ ^ 20
          + ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (7 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(3 : ℂ) + ζ ^ 16 + ζ ^ 20 - ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(3 : ℂ) + ζ ^ 16 + ζ ^ 20 - ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (7 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((4 : ℂ) - ζ ^ 4 + (4 : ℂ) * ζ ^ 8 + ζ ^ 12 - (2 : ℂ) * ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((4 : ℂ) - ζ ^ 4 + (4 : ℂ) * ζ ^ 8 + ζ ^ 12 - (2 : ℂ) * ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (7 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (6 : ℂ)
          - ζ ^ 4
          + ζ ^ 8
          - ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (6 : ℂ)
          - ζ ^ 4
          + ζ ^ 8
          - ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (7 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((2 : ℂ) - ζ ^ 4 + (2 : ℂ) * ζ ^ 8 + ζ ^ 12 - ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((2 : ℂ) - ζ ^ 4 + (2 : ℂ) * ζ ^ 8 + ζ ^ 12 - ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (7 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) * ζ ^ 8 + ζ ^ 16 - ζ ^ 20 + ζ ^ 24) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) * ζ ^ 8 + ζ ^ 16 - ζ ^ 20 + ζ ^ 24)) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (7 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (7 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(4 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          - (2 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(4 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          - (2 : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + (2 : ℂ) * ζ ^ 16
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (7 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (7 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (7 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) + ζ ^ 4 - ζ ^ 8 - ζ ^ 12 + ζ ^ 16) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) + ζ ^ 4 - ζ ^ 8 - ζ ^ 12 + ζ ^ 16)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (8 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (8 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (8 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (8 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (8 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (8 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (8 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (8 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(2 : ℂ) + (2 : ℂ) * ζ ^ 4 - (2 : ℂ) * ζ ^ 8) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(2 : ℂ) + (2 : ℂ) * ζ ^ 4 - (2 : ℂ) * ζ ^ 8)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (8 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (8 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (8 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (8 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (8 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (9 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (9 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (9 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (9 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (9 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (9 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (9 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (9 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (9 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (9 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (9 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (9 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (9 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (10 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (10 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (10 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (10 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (10 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (10 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (10 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (10 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (10 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (10 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (10 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (10 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (10 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_00 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (0 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (11 : Fin 12) (0 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_01 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (1 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (11 : Fin 12) (1 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_02 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (2 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (11 : Fin 12) (2 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_03 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (3 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (11 : Fin 12) (3 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_04 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (4 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (11 : Fin 12) (4 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_05 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (5 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (11 : Fin 12) (5 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_06 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (6 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (11 : Fin 12) (6 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
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
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_07 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (7 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (11 : Fin 12) (7 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_08 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (8 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (11 : Fin 12) (8 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_09 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (9 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (11 : Fin 12) (9 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_10 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (10 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (11 : Fin 12) (10 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_11 :
    (alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77
        * alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB)
          (11 : Fin 12) (11 : Fin 12) =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77
        (11 : Fin 12) (11 : Fin 12) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77,
    alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB,
    alternatingSixAmbientAtlasTwelvePowerTwoLongState77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

theorem alternatingSixAmbientAtlasTwelvePowerTwo_longState77_mul :
    alternatingSixAmbientAtlasTwelvePowerTwoLongPrefix77 *
        alternatingSixAmbientAtlasTwelvePowerTwoLongMatrixABBB =
      alternatingSixAmbientAtlasTwelvePowerTwoLongState77 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry00_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry01_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry02_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry03_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry04_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry05_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry06_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry07_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry08_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry09_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry10_11
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_00
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_01
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_02
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_03
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_04
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_05
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_06
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_07
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_08
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_09
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_10
  · exact alternatingSixAmbientAtlasTwelvePowerTwo_longState77_entry11_11

end InductiveMcKay
end McKayConjecture
