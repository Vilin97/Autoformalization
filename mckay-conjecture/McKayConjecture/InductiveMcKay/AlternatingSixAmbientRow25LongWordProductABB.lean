/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow25LongWordData

/-!
# One checked row-25 long-word multiplication

This split generated module keeps each 10 by 10 multiplication
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
private theorem alternatingSixAmbientRow25_longMatrixABB_entry00_00 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (0 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (0 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 9) : ℂ)
          - ((1 / 9) : ℂ) * ζ ^ 4
          + ((5 / 18) : ℂ) * ζ ^ 5
          + ((1 / 9) : ℂ) * ζ ^ 8
          - ((5 / 18) : ℂ) * ζ ^ 9
          + ((1 / 18) : ℂ) * ζ ^ 10
          + ((5 / 18) : ℂ) * ζ ^ 13
          - ((1 / 18) : ℂ) * ζ ^ 14
          - ((11 / 18) : ℂ) * ζ ^ 15
          + ((1 / 18) : ℂ) * ζ ^ 18
          + ((11 / 18) : ℂ) * ζ ^ 19
          - ((5 / 9) : ℂ) * ζ ^ 20
          - ((11 / 18) : ℂ) * ζ ^ 23
          + ((5 / 9) : ℂ) * ζ ^ 24
          - ((5 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 9) : ℂ)
          - ((1 / 9) : ℂ) * ζ ^ 4
          + ((5 / 18) : ℂ) * ζ ^ 5
          + ((1 / 9) : ℂ) * ζ ^ 8
          - ((5 / 18) : ℂ) * ζ ^ 9
          + ((1 / 18) : ℂ) * ζ ^ 10
          + ((5 / 18) : ℂ) * ζ ^ 13
          - ((1 / 18) : ℂ) * ζ ^ 14
          - ((11 / 18) : ℂ) * ζ ^ 15
          + ((1 / 18) : ℂ) * ζ ^ 18
          + ((11 / 18) : ℂ) * ζ ^ 19
          - ((5 / 9) : ℂ) * ζ ^ 20
          - ((11 / 18) : ℂ) * ζ ^ 23
          + ((5 / 9) : ℂ) * ζ ^ 24
          - ((5 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry00_01 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (0 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (0 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((5 / 18) : ℂ)
          + ((5 / 18) : ℂ) * ζ ^ 4
          - ((4 / 9) : ℂ) * ζ ^ 5
          - ((5 / 18) : ℂ) * ζ ^ 8
          + ((4 / 9) : ℂ) * ζ ^ 9
          + ((11 / 18) : ℂ) * ζ ^ 10
          - ((4 / 9) : ℂ) * ζ ^ 13
          - ((11 / 18) : ℂ) * ζ ^ 14
          + ((7 / 9) : ℂ) * ζ ^ 15
          + ((11 / 18) : ℂ) * ζ ^ 18
          - ((7 / 9) : ℂ) * ζ ^ 19
          + ((25 / 18) : ℂ) * ζ ^ 20
          + ((7 / 9) : ℂ) * ζ ^ 23
          - ((25 / 18) : ℂ) * ζ ^ 24
          + ((25 / 18) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((5 / 18) : ℂ)
          + ((5 / 18) : ℂ) * ζ ^ 4
          - ((4 / 9) : ℂ) * ζ ^ 5
          - ((5 / 18) : ℂ) * ζ ^ 8
          + ((4 / 9) : ℂ) * ζ ^ 9
          + ((11 / 18) : ℂ) * ζ ^ 10
          - ((4 / 9) : ℂ) * ζ ^ 13
          - ((11 / 18) : ℂ) * ζ ^ 14
          + ((7 / 9) : ℂ) * ζ ^ 15
          + ((11 / 18) : ℂ) * ζ ^ 18
          - ((7 / 9) : ℂ) * ζ ^ 19
          + ((25 / 18) : ℂ) * ζ ^ 20
          + ((7 / 9) : ℂ) * ζ ^ 23
          - ((25 / 18) : ℂ) * ζ ^ 24
          + ((25 / 18) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry00_02 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (0 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (0 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 9) : ℂ)
          - ((1 / 9) : ℂ) * ζ ^ 4
          - ((1 / 18) : ℂ) * ζ ^ 5
          + ((1 / 9) : ℂ) * ζ ^ 8
          + ((1 / 18) : ℂ) * ζ ^ 9
          + ((1 / 18) : ℂ) * ζ ^ 10
          - ((1 / 18) : ℂ) * ζ ^ 13
          - ((1 / 18) : ℂ) * ζ ^ 14
          + ((1 / 18) : ℂ) * ζ ^ 15
          + ((1 / 18) : ℂ) * ζ ^ 18
          - ((1 / 18) : ℂ) * ζ ^ 19
          + ((10 / 9) : ℂ) * ζ ^ 20
          + ((1 / 18) : ℂ) * ζ ^ 23
          - ((10 / 9) : ℂ) * ζ ^ 24
          + ((10 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 9) : ℂ)
          - ((1 / 9) : ℂ) * ζ ^ 4
          - ((1 / 18) : ℂ) * ζ ^ 5
          + ((1 / 9) : ℂ) * ζ ^ 8
          + ((1 / 18) : ℂ) * ζ ^ 9
          + ((1 / 18) : ℂ) * ζ ^ 10
          - ((1 / 18) : ℂ) * ζ ^ 13
          - ((1 / 18) : ℂ) * ζ ^ 14
          + ((1 / 18) : ℂ) * ζ ^ 15
          + ((1 / 18) : ℂ) * ζ ^ 18
          - ((1 / 18) : ℂ) * ζ ^ 19
          + ((10 / 9) : ℂ) * ζ ^ 20
          + ((1 / 18) : ℂ) * ζ ^ 23
          - ((10 / 9) : ℂ) * ζ ^ 24
          + ((10 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry00_03 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (0 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (0 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 2) : ℂ)
          - ((1 / 2) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 5
          + ((1 / 2) : ℂ) * ζ ^ 8
          - ((1 / 2) : ℂ) * ζ ^ 9
          - ((1 / 3) : ℂ) * ζ ^ 10
          + ((1 / 2) : ℂ) * ζ ^ 13
          + ((1 / 3) : ℂ) * ζ ^ 14
          - ((1 / 3) : ℂ) * ζ ^ 15
          - ((1 / 3) : ℂ) * ζ ^ 18
          + ((1 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 2) : ℂ)
          - ((1 / 2) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 5
          + ((1 / 2) : ℂ) * ζ ^ 8
          - ((1 / 2) : ℂ) * ζ ^ 9
          - ((1 / 3) : ℂ) * ζ ^ 10
          + ((1 / 2) : ℂ) * ζ ^ 13
          + ((1 / 3) : ℂ) * ζ ^ 14
          - ((1 / 3) : ℂ) * ζ ^ 15
          - ((1 / 3) : ℂ) * ζ ^ 18
          + ((1 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry00_04 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (0 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (0 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 3) : ℂ)
          - ((2 / 3) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 5
          + ((2 / 3) : ℂ) * ζ ^ 8
          - ((1 / 2) : ℂ) * ζ ^ 9
          - ((1 / 6) : ℂ) * ζ ^ 10
          + ((1 / 2) : ℂ) * ζ ^ 13
          + ((1 / 6) : ℂ) * ζ ^ 14
          - ((2 / 3) : ℂ) * ζ ^ 15
          - ((1 / 6) : ℂ) * ζ ^ 18
          + ((2 / 3) : ℂ) * ζ ^ 19
          + ((1 / 6) : ℂ) * ζ ^ 20
          - ((2 / 3) : ℂ) * ζ ^ 23
          - ((1 / 6) : ℂ) * ζ ^ 24
          + ((1 / 6) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 3) : ℂ)
          - ((2 / 3) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 5
          + ((2 / 3) : ℂ) * ζ ^ 8
          - ((1 / 2) : ℂ) * ζ ^ 9
          - ((1 / 6) : ℂ) * ζ ^ 10
          + ((1 / 2) : ℂ) * ζ ^ 13
          + ((1 / 6) : ℂ) * ζ ^ 14
          - ((2 / 3) : ℂ) * ζ ^ 15
          - ((1 / 6) : ℂ) * ζ ^ 18
          + ((2 / 3) : ℂ) * ζ ^ 19
          + ((1 / 6) : ℂ) * ζ ^ 20
          - ((2 / 3) : ℂ) * ζ ^ 23
          - ((1 / 6) : ℂ) * ζ ^ 24
          + ((1 / 6) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry00_05 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (0 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (0 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 2) : ℂ)
          - ((1 / 2) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 8
          - ((1 / 6) : ℂ) * ζ ^ 10
          + ((1 / 6) : ℂ) * ζ ^ 14
          - ((1 / 3) : ℂ) * ζ ^ 15
          - ((1 / 6) : ℂ) * ζ ^ 18
          + ((1 / 3) : ℂ) * ζ ^ 19
          + ((1 / 2) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 23
          - ((1 / 2) : ℂ) * ζ ^ 24
          + ((1 / 2) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 2) : ℂ)
          - ((1 / 2) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 8
          - ((1 / 6) : ℂ) * ζ ^ 10
          + ((1 / 6) : ℂ) * ζ ^ 14
          - ((1 / 3) : ℂ) * ζ ^ 15
          - ((1 / 6) : ℂ) * ζ ^ 18
          + ((1 / 3) : ℂ) * ζ ^ 19
          + ((1 / 2) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 23
          - ((1 / 2) : ℂ) * ζ ^ 24
          + ((1 / 2) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry00_06 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (0 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (0 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 6) : ℂ)
          - ((1 / 6) : ℂ) * ζ ^ 4
          + ((5 / 6) : ℂ) * ζ ^ 5
          + ((1 / 6) : ℂ) * ζ ^ 8
          - ((5 / 6) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 10
          + ((5 / 6) : ℂ) * ζ ^ 13
          - ((1 / 3) : ℂ) * ζ ^ 14
          - ((1 / 3) : ℂ) * ζ ^ 15
          + ((1 / 3) : ℂ) * ζ ^ 18
          + ((1 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 6) : ℂ)
          - ((1 / 6) : ℂ) * ζ ^ 4
          + ((5 / 6) : ℂ) * ζ ^ 5
          + ((1 / 6) : ℂ) * ζ ^ 8
          - ((5 / 6) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 10
          + ((5 / 6) : ℂ) * ζ ^ 13
          - ((1 / 3) : ℂ) * ζ ^ 14
          - ((1 / 3) : ℂ) * ζ ^ 15
          + ((1 / 3) : ℂ) * ζ ^ 18
          + ((1 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry00_07 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (0 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (0 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((5 / 9) : ℂ)
          - ((5 / 9) : ℂ) * ζ ^ 4
          - ((11 / 18) : ℂ) * ζ ^ 5
          + ((5 / 9) : ℂ) * ζ ^ 8
          + ((11 / 18) : ℂ) * ζ ^ 9
          + ((5 / 18) : ℂ) * ζ ^ 10
          - ((11 / 18) : ℂ) * ζ ^ 13
          - ((5 / 18) : ℂ) * ζ ^ 14
          + ((5 / 18) : ℂ) * ζ ^ 15
          + ((5 / 18) : ℂ) * ζ ^ 18
          - ((5 / 18) : ℂ) * ζ ^ 19
          + ((5 / 9) : ℂ) * ζ ^ 20
          + ((5 / 18) : ℂ) * ζ ^ 23
          - ((5 / 9) : ℂ) * ζ ^ 24
          + ((5 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((5 / 9) : ℂ)
          - ((5 / 9) : ℂ) * ζ ^ 4
          - ((11 / 18) : ℂ) * ζ ^ 5
          + ((5 / 9) : ℂ) * ζ ^ 8
          + ((11 / 18) : ℂ) * ζ ^ 9
          + ((5 / 18) : ℂ) * ζ ^ 10
          - ((11 / 18) : ℂ) * ζ ^ 13
          - ((5 / 18) : ℂ) * ζ ^ 14
          + ((5 / 18) : ℂ) * ζ ^ 15
          + ((5 / 18) : ℂ) * ζ ^ 18
          - ((5 / 18) : ℂ) * ζ ^ 19
          + ((5 / 9) : ℂ) * ζ ^ 20
          + ((5 / 18) : ℂ) * ζ ^ 23
          - ((5 / 9) : ℂ) * ζ ^ 24
          + ((5 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry00_08 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (0 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (0 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 9) : ℂ)
          + ((7 / 9) : ℂ) * ζ ^ 4
          + ((1 / 18) : ℂ) * ζ ^ 5
          - ((7 / 9) : ℂ) * ζ ^ 8
          - ((1 / 18) : ℂ) * ζ ^ 9
          + ((5 / 18) : ℂ) * ζ ^ 10
          + ((1 / 18) : ℂ) * ζ ^ 13
          - ((5 / 18) : ℂ) * ζ ^ 14
          + ((13 / 9) : ℂ) * ζ ^ 15
          + ((5 / 18) : ℂ) * ζ ^ 18
          - ((13 / 9) : ℂ) * ζ ^ 19
          + ((13 / 18) : ℂ) * ζ ^ 20
          + ((13 / 9) : ℂ) * ζ ^ 23
          - ((13 / 18) : ℂ) * ζ ^ 24
          + ((13 / 18) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 9) : ℂ)
          + ((7 / 9) : ℂ) * ζ ^ 4
          + ((1 / 18) : ℂ) * ζ ^ 5
          - ((7 / 9) : ℂ) * ζ ^ 8
          - ((1 / 18) : ℂ) * ζ ^ 9
          + ((5 / 18) : ℂ) * ζ ^ 10
          + ((1 / 18) : ℂ) * ζ ^ 13
          - ((5 / 18) : ℂ) * ζ ^ 14
          + ((13 / 9) : ℂ) * ζ ^ 15
          + ((5 / 18) : ℂ) * ζ ^ 18
          - ((13 / 9) : ℂ) * ζ ^ 19
          + ((13 / 18) : ℂ) * ζ ^ 20
          + ((13 / 9) : ℂ) * ζ ^ 23
          - ((13 / 18) : ℂ) * ζ ^ 24
          + ((13 / 18) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry00_09 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (0 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (0 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((2 / 3) : ℂ) * ζ ^ 15
          + ((2 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ((2 / 3) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((2 / 3) : ℂ) * ζ ^ 15
          + ((2 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ((2 / 3) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry01_00 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (1 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (1 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((2 / 3) : ℂ)
          + ((2 / 3) : ℂ) * ζ ^ 4
          + ((1 / 6) : ℂ) * ζ ^ 5
          - ((2 / 3) : ℂ) * ζ ^ 8
          - ((1 / 6) : ℂ) * ζ ^ 9
          - ((1 / 6) : ℂ) * ζ ^ 10
          + ((1 / 6) : ℂ) * ζ ^ 13
          + ((1 / 6) : ℂ) * ζ ^ 14
          - ((1 / 6) : ℂ) * ζ ^ 15
          - ((1 / 6) : ℂ) * ζ ^ 18
          + ((1 / 6) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 6) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((2 / 3) : ℂ)
          + ((2 / 3) : ℂ) * ζ ^ 4
          + ((1 / 6) : ℂ) * ζ ^ 5
          - ((2 / 3) : ℂ) * ζ ^ 8
          - ((1 / 6) : ℂ) * ζ ^ 9
          - ((1 / 6) : ℂ) * ζ ^ 10
          + ((1 / 6) : ℂ) * ζ ^ 13
          + ((1 / 6) : ℂ) * ζ ^ 14
          - ((1 / 6) : ℂ) * ζ ^ 15
          - ((1 / 6) : ℂ) * ζ ^ 18
          + ((1 / 6) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 6) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry01_01 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (1 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (1 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 6) : ℂ)
          - ((1 / 6) : ℂ) * ζ ^ 4
          + ((4 / 3) : ℂ) * ζ ^ 5
          + ((1 / 6) : ℂ) * ζ ^ 8
          - ((4 / 3) : ℂ) * ζ ^ 9
          + ((3 / 2) : ℂ) * ζ ^ 10
          + ((4 / 3) : ℂ) * ζ ^ 13
          - ((3 / 2) : ℂ) * ζ ^ 14
          + ζ ^ 15
          + ((3 / 2) : ℂ) * ζ ^ 18
          - ζ ^ 19
          + ((3 / 2) : ℂ) * ζ ^ 20
          + ζ ^ 23
          - ((3 / 2) : ℂ) * ζ ^ 24
          + ((3 / 2) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 6) : ℂ)
          - ((1 / 6) : ℂ) * ζ ^ 4
          + ((4 / 3) : ℂ) * ζ ^ 5
          + ((1 / 6) : ℂ) * ζ ^ 8
          - ((4 / 3) : ℂ) * ζ ^ 9
          + ((3 / 2) : ℂ) * ζ ^ 10
          + ((4 / 3) : ℂ) * ζ ^ 13
          - ((3 / 2) : ℂ) * ζ ^ 14
          + ζ ^ 15
          + ((3 / 2) : ℂ) * ζ ^ 18
          - ζ ^ 19
          + ((3 / 2) : ℂ) * ζ ^ 20
          + ζ ^ 23
          - ((3 / 2) : ℂ) * ζ ^ 24
          + ((3 / 2) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry01_02 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (1 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (1 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((4 / 3) : ℂ)
          - ((4 / 3) : ℂ) * ζ ^ 4
          + ((7 / 6) : ℂ) * ζ ^ 5
          + ((4 / 3) : ℂ) * ζ ^ 8
          - ((7 / 6) : ℂ) * ζ ^ 9
          + ((1 / 2) : ℂ) * ζ ^ 10
          + ((7 / 6) : ℂ) * ζ ^ 13
          - ((1 / 2) : ℂ) * ζ ^ 14
          + ((3 / 2) : ℂ) * ζ ^ 15
          + ((1 / 2) : ℂ) * ζ ^ 18
          - ((3 / 2) : ℂ) * ζ ^ 19
          + ζ ^ 20
          + ((3 / 2) : ℂ) * ζ ^ 23
          - ζ ^ 24
          + ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((4 / 3) : ℂ)
          - ((4 / 3) : ℂ) * ζ ^ 4
          + ((7 / 6) : ℂ) * ζ ^ 5
          + ((4 / 3) : ℂ) * ζ ^ 8
          - ((7 / 6) : ℂ) * ζ ^ 9
          + ((1 / 2) : ℂ) * ζ ^ 10
          + ((7 / 6) : ℂ) * ζ ^ 13
          - ((1 / 2) : ℂ) * ζ ^ 14
          + ((3 / 2) : ℂ) * ζ ^ 15
          + ((1 / 2) : ℂ) * ζ ^ 18
          - ((3 / 2) : ℂ) * ζ ^ 19
          + ζ ^ 20
          + ((3 / 2) : ℂ) * ζ ^ 23
          - ζ ^ 24
          + ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry01_03 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (1 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (1 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 2) : ℂ)
          - ((1 / 2) : ℂ) * ζ ^ 4
          - ((1 / 2) : ℂ) * ζ ^ 5
          + ((1 / 2) : ℂ) * ζ ^ 8
          + ((1 / 2) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 10
          - ((1 / 2) : ℂ) * ζ ^ 13
          - ((1 / 3) : ℂ) * ζ ^ 14
          + ((1 / 3) : ℂ) * ζ ^ 15
          + ((1 / 3) : ℂ) * ζ ^ 18
          - ((1 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          + ((1 / 3) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 2) : ℂ)
          - ((1 / 2) : ℂ) * ζ ^ 4
          - ((1 / 2) : ℂ) * ζ ^ 5
          + ((1 / 2) : ℂ) * ζ ^ 8
          + ((1 / 2) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 10
          - ((1 / 2) : ℂ) * ζ ^ 13
          - ((1 / 3) : ℂ) * ζ ^ 14
          + ((1 / 3) : ℂ) * ζ ^ 15
          + ((1 / 3) : ℂ) * ζ ^ 18
          - ((1 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          + ((1 / 3) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry01_04 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (1 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (1 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(1 : ℂ)
          + ζ ^ 4
          - ((1 / 2) : ℂ) * ζ ^ 5
          - ζ ^ 8
          + ((1 / 2) : ℂ) * ζ ^ 9
          + ((1 / 6) : ℂ) * ζ ^ 10
          - ((1 / 2) : ℂ) * ζ ^ 13
          - ((1 / 6) : ℂ) * ζ ^ 14
          - ((4 / 3) : ℂ) * ζ ^ 15
          + ((1 / 6) : ℂ) * ζ ^ 18
          + ((4 / 3) : ℂ) * ζ ^ 19
          - ((1 / 6) : ℂ) * ζ ^ 20
          - ((4 / 3) : ℂ) * ζ ^ 23
          + ((1 / 6) : ℂ) * ζ ^ 24
          - ((1 / 6) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(1 : ℂ)
          + ζ ^ 4
          - ((1 / 2) : ℂ) * ζ ^ 5
          - ζ ^ 8
          + ((1 / 2) : ℂ) * ζ ^ 9
          + ((1 / 6) : ℂ) * ζ ^ 10
          - ((1 / 2) : ℂ) * ζ ^ 13
          - ((1 / 6) : ℂ) * ζ ^ 14
          - ((4 / 3) : ℂ) * ζ ^ 15
          + ((1 / 6) : ℂ) * ζ ^ 18
          + ((4 / 3) : ℂ) * ζ ^ 19
          - ((1 / 6) : ℂ) * ζ ^ 20
          - ((4 / 3) : ℂ) * ζ ^ 23
          + ((1 / 6) : ℂ) * ζ ^ 24
          - ((1 / 6) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry01_05 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (1 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (1 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 2) : ℂ)
          - ((1 / 2) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 8
          + ((7 / 6) : ℂ) * ζ ^ 10
          - ((7 / 6) : ℂ) * ζ ^ 14
          + ((2 / 3) : ℂ) * ζ ^ 15
          + ((7 / 6) : ℂ) * ζ ^ 18
          - ((2 / 3) : ℂ) * ζ ^ 19
          + ((5 / 6) : ℂ) * ζ ^ 20
          + ((2 / 3) : ℂ) * ζ ^ 23
          - ((5 / 6) : ℂ) * ζ ^ 24
          + ((5 / 6) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 2) : ℂ)
          - ((1 / 2) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 8
          + ((7 / 6) : ℂ) * ζ ^ 10
          - ((7 / 6) : ℂ) * ζ ^ 14
          + ((2 / 3) : ℂ) * ζ ^ 15
          + ((7 / 6) : ℂ) * ζ ^ 18
          - ((2 / 3) : ℂ) * ζ ^ 19
          + ((5 / 6) : ℂ) * ζ ^ 20
          + ((2 / 3) : ℂ) * ζ ^ 23
          - ((5 / 6) : ℂ) * ζ ^ 24
          + ((5 / 6) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry01_06 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (1 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (1 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 2) : ℂ)
          - ((1 / 2) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 5
          + ((1 / 2) : ℂ) * ζ ^ 8
          - ((1 / 2) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 10
          + ((1 / 2) : ℂ) * ζ ^ 13
          - ((1 / 3) : ℂ) * ζ ^ 14
          - ((2 / 3) : ℂ) * ζ ^ 15
          + ((1 / 3) : ℂ) * ζ ^ 18
          + ((2 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ((2 / 3) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 2) : ℂ)
          - ((1 / 2) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 5
          + ((1 / 2) : ℂ) * ζ ^ 8
          - ((1 / 2) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 10
          + ((1 / 2) : ℂ) * ζ ^ 13
          - ((1 / 3) : ℂ) * ζ ^ 14
          - ((2 / 3) : ℂ) * ζ ^ 15
          + ((1 / 3) : ℂ) * ζ ^ 18
          + ((2 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ((2 / 3) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry01_07 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (1 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (1 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          + ((5 / 6) : ℂ) * ζ ^ 5
          - ((1 / 3) : ℂ) * ζ ^ 8
          - ((5 / 6) : ℂ) * ζ ^ 9
          + ((1 / 6) : ℂ) * ζ ^ 10
          + ((5 / 6) : ℂ) * ζ ^ 13
          - ((1 / 6) : ℂ) * ζ ^ 14
          + ((1 / 6) : ℂ) * ζ ^ 15
          + ((1 / 6) : ℂ) * ζ ^ 18
          - ((1 / 6) : ℂ) * ζ ^ 19
          + ((1 / 3) : ℂ) * ζ ^ 20
          + ((1 / 6) : ℂ) * ζ ^ 23
          - ((1 / 3) : ℂ) * ζ ^ 24
          + ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          + ((5 / 6) : ℂ) * ζ ^ 5
          - ((1 / 3) : ℂ) * ζ ^ 8
          - ((5 / 6) : ℂ) * ζ ^ 9
          + ((1 / 6) : ℂ) * ζ ^ 10
          + ((5 / 6) : ℂ) * ζ ^ 13
          - ((1 / 6) : ℂ) * ζ ^ 14
          + ((1 / 6) : ℂ) * ζ ^ 15
          + ((1 / 6) : ℂ) * ζ ^ 18
          - ((1 / 6) : ℂ) * ζ ^ 19
          + ((1 / 3) : ℂ) * ζ ^ 20
          + ((1 / 6) : ℂ) * ζ ^ 23
          - ((1 / 3) : ℂ) * ζ ^ 24
          + ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry01_08 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (1 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (1 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          + ((5 / 6) : ℂ) * ζ ^ 5
          - ((1 / 3) : ℂ) * ζ ^ 8
          - ((5 / 6) : ℂ) * ζ ^ 9
          + ((1 / 6) : ℂ) * ζ ^ 10
          + ((5 / 6) : ℂ) * ζ ^ 13
          - ((1 / 6) : ℂ) * ζ ^ 14
          + ((5 / 3) : ℂ) * ζ ^ 15
          + ((1 / 6) : ℂ) * ζ ^ 18
          - ((5 / 3) : ℂ) * ζ ^ 19
          + ((5 / 6) : ℂ) * ζ ^ 20
          + ((5 / 3) : ℂ) * ζ ^ 23
          - ((5 / 6) : ℂ) * ζ ^ 24
          + ((5 / 6) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          + ((5 / 6) : ℂ) * ζ ^ 5
          - ((1 / 3) : ℂ) * ζ ^ 8
          - ((5 / 6) : ℂ) * ζ ^ 9
          + ((1 / 6) : ℂ) * ζ ^ 10
          + ((5 / 6) : ℂ) * ζ ^ 13
          - ((1 / 6) : ℂ) * ζ ^ 14
          + ((5 / 3) : ℂ) * ζ ^ 15
          + ((1 / 6) : ℂ) * ζ ^ 18
          - ((5 / 3) : ℂ) * ζ ^ 19
          + ((5 / 6) : ℂ) * ζ ^ 20
          + ((5 / 3) : ℂ) * ζ ^ 23
          - ((5 / 6) : ℂ) * ζ ^ 24
          + ((5 / 6) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry01_09 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (1 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (1 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry02_00 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (2 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (2 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (1 : ℂ)
          - ζ ^ 4
          + ((2 / 3) : ℂ) * ζ ^ 5
          + ζ ^ 8
          - ((2 / 3) : ℂ) * ζ ^ 9
          - ((2 / 3) : ℂ) * ζ ^ 10
          + ((2 / 3) : ℂ) * ζ ^ 13
          + ((2 / 3) : ℂ) * ζ ^ 14
          + ((2 / 3) : ℂ) * ζ ^ 15
          - ((2 / 3) : ℂ) * ζ ^ 18
          - ((2 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          + ((2 / 3) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (1 : ℂ)
          - ζ ^ 4
          + ((2 / 3) : ℂ) * ζ ^ 5
          + ζ ^ 8
          - ((2 / 3) : ℂ) * ζ ^ 9
          - ((2 / 3) : ℂ) * ζ ^ 10
          + ((2 / 3) : ℂ) * ζ ^ 13
          + ((2 / 3) : ℂ) * ζ ^ 14
          + ((2 / 3) : ℂ) * ζ ^ 15
          - ((2 / 3) : ℂ) * ζ ^ 18
          - ((2 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          + ((2 / 3) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry02_01 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (2 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (2 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((4 / 9) : ℂ)
          + ((4 / 9) : ℂ) * ζ ^ 4
          - ((16 / 9) : ℂ) * ζ ^ 5
          - ((4 / 9) : ℂ) * ζ ^ 8
          + ((16 / 9) : ℂ) * ζ ^ 9
          + ((10 / 9) : ℂ) * ζ ^ 10
          - ((16 / 9) : ℂ) * ζ ^ 13
          - ((10 / 9) : ℂ) * ζ ^ 14
          - ((8 / 9) : ℂ) * ζ ^ 15
          + ((10 / 9) : ℂ) * ζ ^ 18
          + ((8 / 9) : ℂ) * ζ ^ 19
          - ((13 / 9) : ℂ) * ζ ^ 20
          - ((8 / 9) : ℂ) * ζ ^ 23
          + ((13 / 9) : ℂ) * ζ ^ 24
          - ((13 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((4 / 9) : ℂ)
          + ((4 / 9) : ℂ) * ζ ^ 4
          - ((16 / 9) : ℂ) * ζ ^ 5
          - ((4 / 9) : ℂ) * ζ ^ 8
          + ((16 / 9) : ℂ) * ζ ^ 9
          + ((10 / 9) : ℂ) * ζ ^ 10
          - ((16 / 9) : ℂ) * ζ ^ 13
          - ((10 / 9) : ℂ) * ζ ^ 14
          - ((8 / 9) : ℂ) * ζ ^ 15
          + ((10 / 9) : ℂ) * ζ ^ 18
          + ((8 / 9) : ℂ) * ζ ^ 19
          - ((13 / 9) : ℂ) * ζ ^ 20
          - ((8 / 9) : ℂ) * ζ ^ 23
          + ((13 / 9) : ℂ) * ζ ^ 24
          - ((13 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry02_02 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (2 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (2 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((17 / 9) : ℂ)
          + ((17 / 9) : ℂ) * ζ ^ 4
          - ((8 / 9) : ℂ) * ζ ^ 5
          - ((17 / 9) : ℂ) * ζ ^ 8
          + ((8 / 9) : ℂ) * ζ ^ 9
          + ((17 / 9) : ℂ) * ζ ^ 10
          - ((8 / 9) : ℂ) * ζ ^ 13
          - ((17 / 9) : ℂ) * ζ ^ 14
          - ((7 / 9) : ℂ) * ζ ^ 15
          + ((17 / 9) : ℂ) * ζ ^ 18
          + ((7 / 9) : ℂ) * ζ ^ 19
          - ((5 / 9) : ℂ) * ζ ^ 20
          - ((7 / 9) : ℂ) * ζ ^ 23
          + ((5 / 9) : ℂ) * ζ ^ 24
          - ((5 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((17 / 9) : ℂ)
          + ((17 / 9) : ℂ) * ζ ^ 4
          - ((8 / 9) : ℂ) * ζ ^ 5
          - ((17 / 9) : ℂ) * ζ ^ 8
          + ((8 / 9) : ℂ) * ζ ^ 9
          + ((17 / 9) : ℂ) * ζ ^ 10
          - ((8 / 9) : ℂ) * ζ ^ 13
          - ((17 / 9) : ℂ) * ζ ^ 14
          - ((7 / 9) : ℂ) * ζ ^ 15
          + ((17 / 9) : ℂ) * ζ ^ 18
          + ((7 / 9) : ℂ) * ζ ^ 19
          - ((5 / 9) : ℂ) * ζ ^ 20
          - ((7 / 9) : ℂ) * ζ ^ 23
          + ((5 / 9) : ℂ) * ζ ^ 24
          - ((5 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry02_03 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (2 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (2 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 9) : ℂ)
          + ((1 / 9) : ℂ) * ζ ^ 4
          - ((10 / 9) : ℂ) * ζ ^ 5
          - ((1 / 9) : ℂ) * ζ ^ 8
          + ((10 / 9) : ℂ) * ζ ^ 9
          - ((5 / 9) : ℂ) * ζ ^ 10
          - ((10 / 9) : ℂ) * ζ ^ 13
          + ((5 / 9) : ℂ) * ζ ^ 14
          - ((8 / 9) : ℂ) * ζ ^ 15
          - ((5 / 9) : ℂ) * ζ ^ 18
          + ((8 / 9) : ℂ) * ζ ^ 19
          - ((10 / 9) : ℂ) * ζ ^ 20
          - ((8 / 9) : ℂ) * ζ ^ 23
          + ((10 / 9) : ℂ) * ζ ^ 24
          - ((10 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 9) : ℂ)
          + ((1 / 9) : ℂ) * ζ ^ 4
          - ((10 / 9) : ℂ) * ζ ^ 5
          - ((1 / 9) : ℂ) * ζ ^ 8
          + ((10 / 9) : ℂ) * ζ ^ 9
          - ((5 / 9) : ℂ) * ζ ^ 10
          - ((10 / 9) : ℂ) * ζ ^ 13
          + ((5 / 9) : ℂ) * ζ ^ 14
          - ((8 / 9) : ℂ) * ζ ^ 15
          - ((5 / 9) : ℂ) * ζ ^ 18
          + ((8 / 9) : ℂ) * ζ ^ 19
          - ((10 / 9) : ℂ) * ζ ^ 20
          - ((8 / 9) : ℂ) * ζ ^ 23
          + ((10 / 9) : ℂ) * ζ ^ 24
          - ((10 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry02_04 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (2 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (2 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((19 / 9) : ℂ)
          - ((19 / 9) : ℂ) * ζ ^ 4
          + ((1 / 9) : ℂ) * ζ ^ 5
          + ((19 / 9) : ℂ) * ζ ^ 8
          - ((1 / 9) : ℂ) * ζ ^ 9
          - ((7 / 9) : ℂ) * ζ ^ 10
          + ((1 / 9) : ℂ) * ζ ^ 13
          + ((7 / 9) : ℂ) * ζ ^ 14
          - ((1 / 9) : ℂ) * ζ ^ 15
          - ((7 / 9) : ℂ) * ζ ^ 18
          + ((1 / 9) : ℂ) * ζ ^ 19
          + ((10 / 9) : ℂ) * ζ ^ 20
          - ((1 / 9) : ℂ) * ζ ^ 23
          - ((10 / 9) : ℂ) * ζ ^ 24
          + ((10 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((19 / 9) : ℂ)
          - ((19 / 9) : ℂ) * ζ ^ 4
          + ((1 / 9) : ℂ) * ζ ^ 5
          + ((19 / 9) : ℂ) * ζ ^ 8
          - ((1 / 9) : ℂ) * ζ ^ 9
          - ((7 / 9) : ℂ) * ζ ^ 10
          + ((1 / 9) : ℂ) * ζ ^ 13
          + ((7 / 9) : ℂ) * ζ ^ 14
          - ((1 / 9) : ℂ) * ζ ^ 15
          - ((7 / 9) : ℂ) * ζ ^ 18
          + ((1 / 9) : ℂ) * ζ ^ 19
          + ((10 / 9) : ℂ) * ζ ^ 20
          - ((1 / 9) : ℂ) * ζ ^ 23
          - ((10 / 9) : ℂ) * ζ ^ 24
          + ((10 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry02_05 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (2 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (2 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((10 / 9) : ℂ)
          - ((10 / 9) : ℂ) * ζ ^ 4
          - ((8 / 9) : ℂ) * ζ ^ 5
          + ((10 / 9) : ℂ) * ζ ^ 8
          + ((8 / 9) : ℂ) * ζ ^ 9
          + ((14 / 9) : ℂ) * ζ ^ 10
          - ((8 / 9) : ℂ) * ζ ^ 13
          - ((14 / 9) : ℂ) * ζ ^ 14
          - ((1 / 9) : ℂ) * ζ ^ 15
          + ((14 / 9) : ℂ) * ζ ^ 18
          + ((1 / 9) : ℂ) * ζ ^ 19
          - ((11 / 9) : ℂ) * ζ ^ 20
          - ((1 / 9) : ℂ) * ζ ^ 23
          + ((11 / 9) : ℂ) * ζ ^ 24
          - ((11 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((10 / 9) : ℂ)
          - ((10 / 9) : ℂ) * ζ ^ 4
          - ((8 / 9) : ℂ) * ζ ^ 5
          + ((10 / 9) : ℂ) * ζ ^ 8
          + ((8 / 9) : ℂ) * ζ ^ 9
          + ((14 / 9) : ℂ) * ζ ^ 10
          - ((8 / 9) : ℂ) * ζ ^ 13
          - ((14 / 9) : ℂ) * ζ ^ 14
          - ((1 / 9) : ℂ) * ζ ^ 15
          + ((14 / 9) : ℂ) * ζ ^ 18
          + ((1 / 9) : ℂ) * ζ ^ 19
          - ((11 / 9) : ℂ) * ζ ^ 20
          - ((1 / 9) : ℂ) * ζ ^ 23
          + ((11 / 9) : ℂ) * ζ ^ 24
          - ((11 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry02_06 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (2 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (2 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 9) : ℂ)
          + ((1 / 9) : ℂ) * ζ ^ 4
          - ((10 / 9) : ℂ) * ζ ^ 5
          - ((1 / 9) : ℂ) * ζ ^ 8
          + ((10 / 9) : ℂ) * ζ ^ 9
          - ((20 / 9) : ℂ) * ζ ^ 10
          - ((10 / 9) : ℂ) * ζ ^ 13
          + ((20 / 9) : ℂ) * ζ ^ 14
          - ((5 / 9) : ℂ) * ζ ^ 15
          - ((20 / 9) : ℂ) * ζ ^ 18
          + ((5 / 9) : ℂ) * ζ ^ 19
          + ((2 / 9) : ℂ) * ζ ^ 20
          - ((5 / 9) : ℂ) * ζ ^ 23
          - ((2 / 9) : ℂ) * ζ ^ 24
          + ((2 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 9) : ℂ)
          + ((1 / 9) : ℂ) * ζ ^ 4
          - ((10 / 9) : ℂ) * ζ ^ 5
          - ((1 / 9) : ℂ) * ζ ^ 8
          + ((10 / 9) : ℂ) * ζ ^ 9
          - ((20 / 9) : ℂ) * ζ ^ 10
          - ((10 / 9) : ℂ) * ζ ^ 13
          + ((20 / 9) : ℂ) * ζ ^ 14
          - ((5 / 9) : ℂ) * ζ ^ 15
          - ((20 / 9) : ℂ) * ζ ^ 18
          + ((5 / 9) : ℂ) * ζ ^ 19
          + ((2 / 9) : ℂ) * ζ ^ 20
          - ((5 / 9) : ℂ) * ζ ^ 23
          - ((2 / 9) : ℂ) * ζ ^ 24
          + ((2 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry02_07 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (2 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (2 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          - ζ ^ 5
          - ((1 / 3) : ℂ) * ζ ^ 8
          + ζ ^ 9
          + ζ ^ 10
          - ζ ^ 13
          - ζ ^ 14
          - ((5 / 3) : ℂ) * ζ ^ 15
          + ζ ^ 18
          + ((5 / 3) : ℂ) * ζ ^ 19
          - ((5 / 3) : ℂ) * ζ ^ 23
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          - ζ ^ 5
          - ((1 / 3) : ℂ) * ζ ^ 8
          + ζ ^ 9
          + ζ ^ 10
          - ζ ^ 13
          - ζ ^ 14
          - ((5 / 3) : ℂ) * ζ ^ 15
          + ζ ^ 18
          + ((5 / 3) : ℂ) * ζ ^ 19
          - ((5 / 3) : ℂ) * ζ ^ 23
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry02_08 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (2 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (2 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(3 : ℂ)
          + (3 : ℂ) * ζ ^ 4
          + ζ ^ 5
          - (3 : ℂ) * ζ ^ 8
          - ζ ^ 9
          + (2 : ℂ) * ζ ^ 10
          + ζ ^ 13
          - (2 : ℂ) * ζ ^ 14
          - ((1 / 3) : ℂ) * ζ ^ 15
          + (2 : ℂ) * ζ ^ 18
          + ((1 / 3) : ℂ) * ζ ^ 19
          - ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 23
          + ζ ^ 24
          - ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(3 : ℂ)
          + (3 : ℂ) * ζ ^ 4
          + ζ ^ 5
          - (3 : ℂ) * ζ ^ 8
          - ζ ^ 9
          + (2 : ℂ) * ζ ^ 10
          + ζ ^ 13
          - (2 : ℂ) * ζ ^ 14
          - ((1 / 3) : ℂ) * ζ ^ 15
          + (2 : ℂ) * ζ ^ 18
          + ((1 / 3) : ℂ) * ζ ^ 19
          - ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 23
          + ζ ^ 24
          - ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry02_09 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (2 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (2 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ζ ^ 5
          - ζ ^ 9
          + ζ ^ 13
          + ζ ^ 15
          - ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          + ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ζ ^ 5
          - ζ ^ 9
          + ζ ^ 13
          + ζ ^ 15
          - ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          + ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry03_00 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (3 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (3 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          - ((1 / 3) : ℂ) * ζ ^ 8
          + ((2 / 3) : ℂ) * ζ ^ 10
          - ((2 / 3) : ℂ) * ζ ^ 14
          - ((1 / 3) : ℂ) * ζ ^ 15
          + ((2 / 3) : ℂ) * ζ ^ 18
          + ((1 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 23
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          - ((1 / 3) : ℂ) * ζ ^ 8
          + ((2 / 3) : ℂ) * ζ ^ 10
          - ((2 / 3) : ℂ) * ζ ^ 14
          - ((1 / 3) : ℂ) * ζ ^ 15
          + ((2 / 3) : ℂ) * ζ ^ 18
          + ((1 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 23
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry03_01 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (3 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (3 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((10 / 9) : ℂ)
          - ((10 / 9) : ℂ) * ζ ^ 4
          + ((7 / 9) : ℂ) * ζ ^ 5
          + ((10 / 9) : ℂ) * ζ ^ 8
          - ((7 / 9) : ℂ) * ζ ^ 9
          - ((7 / 9) : ℂ) * ζ ^ 10
          + ((7 / 9) : ℂ) * ζ ^ 13
          + ((7 / 9) : ℂ) * ζ ^ 14
          + ((8 / 9) : ℂ) * ζ ^ 15
          - ((7 / 9) : ℂ) * ζ ^ 18
          - ((8 / 9) : ℂ) * ζ ^ 19
          + ((7 / 9) : ℂ) * ζ ^ 20
          + ((8 / 9) : ℂ) * ζ ^ 23
          - ((7 / 9) : ℂ) * ζ ^ 24
          + ((7 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((10 / 9) : ℂ)
          - ((10 / 9) : ℂ) * ζ ^ 4
          + ((7 / 9) : ℂ) * ζ ^ 5
          + ((10 / 9) : ℂ) * ζ ^ 8
          - ((7 / 9) : ℂ) * ζ ^ 9
          - ((7 / 9) : ℂ) * ζ ^ 10
          + ((7 / 9) : ℂ) * ζ ^ 13
          + ((7 / 9) : ℂ) * ζ ^ 14
          + ((8 / 9) : ℂ) * ζ ^ 15
          - ((7 / 9) : ℂ) * ζ ^ 18
          - ((8 / 9) : ℂ) * ζ ^ 19
          + ((7 / 9) : ℂ) * ζ ^ 20
          + ((8 / 9) : ℂ) * ζ ^ 23
          - ((7 / 9) : ℂ) * ζ ^ 24
          + ((7 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry03_02 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (3 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (3 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((11 / 9) : ℂ)
          - ((11 / 9) : ℂ) * ζ ^ 4
          + ((8 / 9) : ℂ) * ζ ^ 5
          + ((11 / 9) : ℂ) * ζ ^ 8
          - ((8 / 9) : ℂ) * ζ ^ 9
          - ((11 / 9) : ℂ) * ζ ^ 10
          + ((8 / 9) : ℂ) * ζ ^ 13
          + ((11 / 9) : ℂ) * ζ ^ 14
          - ((2 / 9) : ℂ) * ζ ^ 15
          - ((11 / 9) : ℂ) * ζ ^ 18
          + ((2 / 9) : ℂ) * ζ ^ 19
          + ((2 / 9) : ℂ) * ζ ^ 20
          - ((2 / 9) : ℂ) * ζ ^ 23
          - ((2 / 9) : ℂ) * ζ ^ 24
          + ((2 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((11 / 9) : ℂ)
          - ((11 / 9) : ℂ) * ζ ^ 4
          + ((8 / 9) : ℂ) * ζ ^ 5
          + ((11 / 9) : ℂ) * ζ ^ 8
          - ((8 / 9) : ℂ) * ζ ^ 9
          - ((11 / 9) : ℂ) * ζ ^ 10
          + ((8 / 9) : ℂ) * ζ ^ 13
          + ((11 / 9) : ℂ) * ζ ^ 14
          - ((2 / 9) : ℂ) * ζ ^ 15
          - ((11 / 9) : ℂ) * ζ ^ 18
          + ((2 / 9) : ℂ) * ζ ^ 19
          + ((2 / 9) : ℂ) * ζ ^ 20
          - ((2 / 9) : ℂ) * ζ ^ 23
          - ((2 / 9) : ℂ) * ζ ^ 24
          + ((2 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry03_03 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (3 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (3 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((5 / 9) : ℂ)
          + ((5 / 9) : ℂ) * ζ ^ 4
          + ((7 / 9) : ℂ) * ζ ^ 5
          - ((5 / 9) : ℂ) * ζ ^ 8
          - ((7 / 9) : ℂ) * ζ ^ 9
          - ((1 / 9) : ℂ) * ζ ^ 10
          + ((7 / 9) : ℂ) * ζ ^ 13
          + ((1 / 9) : ℂ) * ζ ^ 14
          + ((2 / 9) : ℂ) * ζ ^ 15
          - ((1 / 9) : ℂ) * ζ ^ 18
          - ((2 / 9) : ℂ) * ζ ^ 19
          + ((10 / 9) : ℂ) * ζ ^ 20
          + ((2 / 9) : ℂ) * ζ ^ 23
          - ((10 / 9) : ℂ) * ζ ^ 24
          + ((10 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((5 / 9) : ℂ)
          + ((5 / 9) : ℂ) * ζ ^ 4
          + ((7 / 9) : ℂ) * ζ ^ 5
          - ((5 / 9) : ℂ) * ζ ^ 8
          - ((7 / 9) : ℂ) * ζ ^ 9
          - ((1 / 9) : ℂ) * ζ ^ 10
          + ((7 / 9) : ℂ) * ζ ^ 13
          + ((1 / 9) : ℂ) * ζ ^ 14
          + ((2 / 9) : ℂ) * ζ ^ 15
          - ((1 / 9) : ℂ) * ζ ^ 18
          - ((2 / 9) : ℂ) * ζ ^ 19
          + ((10 / 9) : ℂ) * ζ ^ 20
          + ((2 / 9) : ℂ) * ζ ^ 23
          - ((10 / 9) : ℂ) * ζ ^ 24
          + ((10 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry03_04 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (3 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (3 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((13 / 9) : ℂ)
          + ((13 / 9) : ℂ) * ζ ^ 4
          - ((7 / 9) : ℂ) * ζ ^ 5
          - ((13 / 9) : ℂ) * ζ ^ 8
          + ((7 / 9) : ℂ) * ζ ^ 9
          + ((4 / 9) : ℂ) * ζ ^ 10
          - ((7 / 9) : ℂ) * ζ ^ 13
          - ((4 / 9) : ℂ) * ζ ^ 14
          + ((7 / 9) : ℂ) * ζ ^ 15
          + ((4 / 9) : ℂ) * ζ ^ 18
          - ((7 / 9) : ℂ) * ζ ^ 19
          - ((1 / 9) : ℂ) * ζ ^ 20
          + ((7 / 9) : ℂ) * ζ ^ 23
          + ((1 / 9) : ℂ) * ζ ^ 24
          - ((1 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((13 / 9) : ℂ)
          + ((13 / 9) : ℂ) * ζ ^ 4
          - ((7 / 9) : ℂ) * ζ ^ 5
          - ((13 / 9) : ℂ) * ζ ^ 8
          + ((7 / 9) : ℂ) * ζ ^ 9
          + ((4 / 9) : ℂ) * ζ ^ 10
          - ((7 / 9) : ℂ) * ζ ^ 13
          - ((4 / 9) : ℂ) * ζ ^ 14
          + ((7 / 9) : ℂ) * ζ ^ 15
          + ((4 / 9) : ℂ) * ζ ^ 18
          - ((7 / 9) : ℂ) * ζ ^ 19
          - ((1 / 9) : ℂ) * ζ ^ 20
          + ((7 / 9) : ℂ) * ζ ^ 23
          + ((1 / 9) : ℂ) * ζ ^ 24
          - ((1 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry03_05 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (3 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (3 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((5 / 9) : ℂ)
          - ((5 / 9) : ℂ) * ζ ^ 4
          + ((11 / 9) : ℂ) * ζ ^ 5
          + ((5 / 9) : ℂ) * ζ ^ 8
          - ((11 / 9) : ℂ) * ζ ^ 9
          - ((8 / 9) : ℂ) * ζ ^ 10
          + ((11 / 9) : ℂ) * ζ ^ 13
          + ((8 / 9) : ℂ) * ζ ^ 14
          + ((7 / 9) : ℂ) * ζ ^ 15
          - ((8 / 9) : ℂ) * ζ ^ 18
          - ((7 / 9) : ℂ) * ζ ^ 19
          + ((11 / 9) : ℂ) * ζ ^ 20
          + ((7 / 9) : ℂ) * ζ ^ 23
          - ((11 / 9) : ℂ) * ζ ^ 24
          + ((11 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((5 / 9) : ℂ)
          - ((5 / 9) : ℂ) * ζ ^ 4
          + ((11 / 9) : ℂ) * ζ ^ 5
          + ((5 / 9) : ℂ) * ζ ^ 8
          - ((11 / 9) : ℂ) * ζ ^ 9
          - ((8 / 9) : ℂ) * ζ ^ 10
          + ((11 / 9) : ℂ) * ζ ^ 13
          + ((8 / 9) : ℂ) * ζ ^ 14
          + ((7 / 9) : ℂ) * ζ ^ 15
          - ((8 / 9) : ℂ) * ζ ^ 18
          - ((7 / 9) : ℂ) * ζ ^ 19
          + ((11 / 9) : ℂ) * ζ ^ 20
          + ((7 / 9) : ℂ) * ζ ^ 23
          - ((11 / 9) : ℂ) * ζ ^ 24
          + ((11 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry03_06 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (3 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (3 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((5 / 9) : ℂ)
          + ((5 / 9) : ℂ) * ζ ^ 4
          + ((7 / 9) : ℂ) * ζ ^ 5
          - ((5 / 9) : ℂ) * ζ ^ 8
          - ((7 / 9) : ℂ) * ζ ^ 9
          + ((5 / 9) : ℂ) * ζ ^ 10
          + ((7 / 9) : ℂ) * ζ ^ 13
          - ((5 / 9) : ℂ) * ζ ^ 14
          - ((1 / 9) : ℂ) * ζ ^ 15
          + ((5 / 9) : ℂ) * ζ ^ 18
          + ((1 / 9) : ℂ) * ζ ^ 19
          - ((2 / 9) : ℂ) * ζ ^ 20
          - ((1 / 9) : ℂ) * ζ ^ 23
          + ((2 / 9) : ℂ) * ζ ^ 24
          - ((2 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((5 / 9) : ℂ)
          + ((5 / 9) : ℂ) * ζ ^ 4
          + ((7 / 9) : ℂ) * ζ ^ 5
          - ((5 / 9) : ℂ) * ζ ^ 8
          - ((7 / 9) : ℂ) * ζ ^ 9
          + ((5 / 9) : ℂ) * ζ ^ 10
          + ((7 / 9) : ℂ) * ζ ^ 13
          - ((5 / 9) : ℂ) * ζ ^ 14
          - ((1 / 9) : ℂ) * ζ ^ 15
          + ((5 / 9) : ℂ) * ζ ^ 18
          + ((1 / 9) : ℂ) * ζ ^ 19
          - ((2 / 9) : ℂ) * ζ ^ 20
          - ((1 / 9) : ℂ) * ζ ^ 23
          + ((2 / 9) : ℂ) * ζ ^ 24
          - ((2 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry03_07 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (3 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (3 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          + ((1 / 3) : ℂ) * ζ ^ 5
          - ((1 / 3) : ℂ) * ζ ^ 8
          - ((1 / 3) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 13
          + ((1 / 3) : ℂ) * ζ ^ 15
          - ((1 / 3) : ℂ) * ζ ^ 19
          - ((5 / 3) : ℂ) * ζ ^ 20
          + ((1 / 3) : ℂ) * ζ ^ 23
          + ((5 / 3) : ℂ) * ζ ^ 24
          - ((5 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          + ((1 / 3) : ℂ) * ζ ^ 5
          - ((1 / 3) : ℂ) * ζ ^ 8
          - ((1 / 3) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 13
          + ((1 / 3) : ℂ) * ζ ^ 15
          - ((1 / 3) : ℂ) * ζ ^ 19
          - ((5 / 3) : ℂ) * ζ ^ 20
          + ((1 / 3) : ℂ) * ζ ^ 23
          + ((5 / 3) : ℂ) * ζ ^ 24
          - ((5 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry03_08 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (3 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (3 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((7 / 3) : ℂ)
          - ((7 / 3) : ℂ) * ζ ^ 4
          - ((2 / 3) : ℂ) * ζ ^ 5
          + ((7 / 3) : ℂ) * ζ ^ 8
          + ((2 / 3) : ℂ) * ζ ^ 9
          - ζ ^ 10
          - ((2 / 3) : ℂ) * ζ ^ 13
          + ζ ^ 14
          - ζ ^ 18
          + ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 24
          + ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((7 / 3) : ℂ)
          - ((7 / 3) : ℂ) * ζ ^ 4
          - ((2 / 3) : ℂ) * ζ ^ 5
          + ((7 / 3) : ℂ) * ζ ^ 8
          + ((2 / 3) : ℂ) * ζ ^ 9
          - ζ ^ 10
          - ((2 / 3) : ℂ) * ζ ^ 13
          + ζ ^ 14
          - ζ ^ 18
          + ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 24
          + ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry03_09 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (3 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (3 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        (1 : ℂ)
          - ζ ^ 4
          + ζ ^ 8
          + ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 24
          + ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        (1 : ℂ)
          - ζ ^ 4
          + ζ ^ 8
          + ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 24
          + ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry04_00 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (4 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (4 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((5 / 9) : ℂ)
          - ((5 / 9) : ℂ) * ζ ^ 4
          + ((2 / 9) : ℂ) * ζ ^ 5
          + ((5 / 9) : ℂ) * ζ ^ 8
          - ((2 / 9) : ℂ) * ζ ^ 9
          - ((2 / 9) : ℂ) * ζ ^ 10
          + ((2 / 9) : ℂ) * ζ ^ 13
          + ((2 / 9) : ℂ) * ζ ^ 14
          - ((14 / 9) : ℂ) * ζ ^ 15
          - ((2 / 9) : ℂ) * ζ ^ 18
          + ((14 / 9) : ℂ) * ζ ^ 19
          - ((1 / 9) : ℂ) * ζ ^ 20
          - ((14 / 9) : ℂ) * ζ ^ 23
          + ((1 / 9) : ℂ) * ζ ^ 24
          - ((1 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((5 / 9) : ℂ)
          - ((5 / 9) : ℂ) * ζ ^ 4
          + ((2 / 9) : ℂ) * ζ ^ 5
          + ((5 / 9) : ℂ) * ζ ^ 8
          - ((2 / 9) : ℂ) * ζ ^ 9
          - ((2 / 9) : ℂ) * ζ ^ 10
          + ((2 / 9) : ℂ) * ζ ^ 13
          + ((2 / 9) : ℂ) * ζ ^ 14
          - ((14 / 9) : ℂ) * ζ ^ 15
          - ((2 / 9) : ℂ) * ζ ^ 18
          + ((14 / 9) : ℂ) * ζ ^ 19
          - ((1 / 9) : ℂ) * ζ ^ 20
          - ((14 / 9) : ℂ) * ζ ^ 23
          + ((1 / 9) : ℂ) * ζ ^ 24
          - ((1 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry04_01 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (4 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (4 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 9) : ℂ)
          - ((2 / 9) : ℂ) * ζ ^ 4
          - ((1 / 9) : ℂ) * ζ ^ 5
          + ((2 / 9) : ℂ) * ζ ^ 8
          + ((1 / 9) : ℂ) * ζ ^ 9
          - ((2 / 9) : ℂ) * ζ ^ 10
          - ((1 / 9) : ℂ) * ζ ^ 13
          + ((2 / 9) : ℂ) * ζ ^ 14
          + ((16 / 9) : ℂ) * ζ ^ 15
          - ((2 / 9) : ℂ) * ζ ^ 18
          - ((16 / 9) : ℂ) * ζ ^ 19
          + ((11 / 9) : ℂ) * ζ ^ 20
          + ((16 / 9) : ℂ) * ζ ^ 23
          - ((11 / 9) : ℂ) * ζ ^ 24
          + ((11 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 9) : ℂ)
          - ((2 / 9) : ℂ) * ζ ^ 4
          - ((1 / 9) : ℂ) * ζ ^ 5
          + ((2 / 9) : ℂ) * ζ ^ 8
          + ((1 / 9) : ℂ) * ζ ^ 9
          - ((2 / 9) : ℂ) * ζ ^ 10
          - ((1 / 9) : ℂ) * ζ ^ 13
          + ((2 / 9) : ℂ) * ζ ^ 14
          + ((16 / 9) : ℂ) * ζ ^ 15
          - ((2 / 9) : ℂ) * ζ ^ 18
          - ((16 / 9) : ℂ) * ζ ^ 19
          + ((11 / 9) : ℂ) * ζ ^ 20
          + ((16 / 9) : ℂ) * ζ ^ 23
          - ((11 / 9) : ℂ) * ζ ^ 24
          + ((11 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry04_02 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (4 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (4 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((7 / 9) : ℂ)
          - ((7 / 9) : ℂ) * ζ ^ 4
          - ((2 / 9) : ℂ) * ζ ^ 5
          + ((7 / 9) : ℂ) * ζ ^ 8
          + ((2 / 9) : ℂ) * ζ ^ 9
          + ((5 / 9) : ℂ) * ζ ^ 10
          - ((2 / 9) : ℂ) * ζ ^ 13
          - ((5 / 9) : ℂ) * ζ ^ 14
          + ((14 / 9) : ℂ) * ζ ^ 15
          + ((5 / 9) : ℂ) * ζ ^ 18
          - ((14 / 9) : ℂ) * ζ ^ 19
          + ((16 / 9) : ℂ) * ζ ^ 20
          + ((14 / 9) : ℂ) * ζ ^ 23
          - ((16 / 9) : ℂ) * ζ ^ 24
          + ((16 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((7 / 9) : ℂ)
          - ((7 / 9) : ℂ) * ζ ^ 4
          - ((2 / 9) : ℂ) * ζ ^ 5
          + ((7 / 9) : ℂ) * ζ ^ 8
          + ((2 / 9) : ℂ) * ζ ^ 9
          + ((5 / 9) : ℂ) * ζ ^ 10
          - ((2 / 9) : ℂ) * ζ ^ 13
          - ((5 / 9) : ℂ) * ζ ^ 14
          + ((14 / 9) : ℂ) * ζ ^ 15
          + ((5 / 9) : ℂ) * ζ ^ 18
          - ((14 / 9) : ℂ) * ζ ^ 19
          + ((16 / 9) : ℂ) * ζ ^ 20
          + ((14 / 9) : ℂ) * ζ ^ 23
          - ((16 / 9) : ℂ) * ζ ^ 24
          + ((16 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry04_03 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (4 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (4 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((2 / 9) : ℂ)
          + ((2 / 9) : ℂ) * ζ ^ 4
          - ((5 / 9) : ℂ) * ζ ^ 5
          - ((2 / 9) : ℂ) * ζ ^ 8
          + ((5 / 9) : ℂ) * ζ ^ 9
          - ((13 / 9) : ℂ) * ζ ^ 10
          - ((5 / 9) : ℂ) * ζ ^ 13
          + ((13 / 9) : ℂ) * ζ ^ 14
          - ((10 / 9) : ℂ) * ζ ^ 15
          - ((13 / 9) : ℂ) * ζ ^ 18
          + ((10 / 9) : ℂ) * ζ ^ 19
          - ((8 / 9) : ℂ) * ζ ^ 20
          - ((10 / 9) : ℂ) * ζ ^ 23
          + ((8 / 9) : ℂ) * ζ ^ 24
          - ((8 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((2 / 9) : ℂ)
          + ((2 / 9) : ℂ) * ζ ^ 4
          - ((5 / 9) : ℂ) * ζ ^ 5
          - ((2 / 9) : ℂ) * ζ ^ 8
          + ((5 / 9) : ℂ) * ζ ^ 9
          - ((13 / 9) : ℂ) * ζ ^ 10
          - ((5 / 9) : ℂ) * ζ ^ 13
          + ((13 / 9) : ℂ) * ζ ^ 14
          - ((10 / 9) : ℂ) * ζ ^ 15
          - ((13 / 9) : ℂ) * ζ ^ 18
          + ((10 / 9) : ℂ) * ζ ^ 19
          - ((8 / 9) : ℂ) * ζ ^ 20
          - ((10 / 9) : ℂ) * ζ ^ 23
          + ((8 / 9) : ℂ) * ζ ^ 24
          - ((8 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry04_04 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (4 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (4 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((5 / 9) : ℂ)
          - ((5 / 9) : ℂ) * ζ ^ 4
          + ((5 / 9) : ℂ) * ζ ^ 5
          + ((5 / 9) : ℂ) * ζ ^ 8
          - ((5 / 9) : ℂ) * ζ ^ 9
          - ((11 / 9) : ℂ) * ζ ^ 10
          + ((5 / 9) : ℂ) * ζ ^ 13
          + ((11 / 9) : ℂ) * ζ ^ 14
          + ((1 / 9) : ℂ) * ζ ^ 15
          - ((11 / 9) : ℂ) * ζ ^ 18
          - ((1 / 9) : ℂ) * ζ ^ 19
          - ((4 / 9) : ℂ) * ζ ^ 20
          + ((1 / 9) : ℂ) * ζ ^ 23
          + ((4 / 9) : ℂ) * ζ ^ 24
          - ((4 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((5 / 9) : ℂ)
          - ((5 / 9) : ℂ) * ζ ^ 4
          + ((5 / 9) : ℂ) * ζ ^ 5
          + ((5 / 9) : ℂ) * ζ ^ 8
          - ((5 / 9) : ℂ) * ζ ^ 9
          - ((11 / 9) : ℂ) * ζ ^ 10
          + ((5 / 9) : ℂ) * ζ ^ 13
          + ((11 / 9) : ℂ) * ζ ^ 14
          + ((1 / 9) : ℂ) * ζ ^ 15
          - ((11 / 9) : ℂ) * ζ ^ 18
          - ((1 / 9) : ℂ) * ζ ^ 19
          - ((4 / 9) : ℂ) * ζ ^ 20
          + ((1 / 9) : ℂ) * ζ ^ 23
          + ((4 / 9) : ℂ) * ζ ^ 24
          - ((4 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry04_05 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (4 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (4 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 9) : ℂ)
          - ((2 / 9) : ℂ) * ζ ^ 4
          - ((4 / 9) : ℂ) * ζ ^ 5
          + ((2 / 9) : ℂ) * ζ ^ 8
          + ((4 / 9) : ℂ) * ζ ^ 9
          - ((14 / 9) : ℂ) * ζ ^ 10
          - ((4 / 9) : ℂ) * ζ ^ 13
          + ((14 / 9) : ℂ) * ζ ^ 14
          + ((7 / 9) : ℂ) * ζ ^ 15
          - ((14 / 9) : ℂ) * ζ ^ 18
          - ((7 / 9) : ℂ) * ζ ^ 19
          + ((5 / 9) : ℂ) * ζ ^ 20
          + ((7 / 9) : ℂ) * ζ ^ 23
          - ((5 / 9) : ℂ) * ζ ^ 24
          + ((5 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 9) : ℂ)
          - ((2 / 9) : ℂ) * ζ ^ 4
          - ((4 / 9) : ℂ) * ζ ^ 5
          + ((2 / 9) : ℂ) * ζ ^ 8
          + ((4 / 9) : ℂ) * ζ ^ 9
          - ((14 / 9) : ℂ) * ζ ^ 10
          - ((4 / 9) : ℂ) * ζ ^ 13
          + ((14 / 9) : ℂ) * ζ ^ 14
          + ((7 / 9) : ℂ) * ζ ^ 15
          - ((14 / 9) : ℂ) * ζ ^ 18
          - ((7 / 9) : ℂ) * ζ ^ 19
          + ((5 / 9) : ℂ) * ζ ^ 20
          + ((7 / 9) : ℂ) * ζ ^ 23
          - ((5 / 9) : ℂ) * ζ ^ 24
          + ((5 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry04_06 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (4 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (4 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 9) : ℂ)
          - ((1 / 9) : ℂ) * ζ ^ 4
          + ((1 / 9) : ℂ) * ζ ^ 5
          + ((1 / 9) : ℂ) * ζ ^ 8
          - ((1 / 9) : ℂ) * ζ ^ 9
          - ((4 / 9) : ℂ) * ζ ^ 10
          + ((1 / 9) : ℂ) * ζ ^ 13
          + ((4 / 9) : ℂ) * ζ ^ 14
          - ((13 / 9) : ℂ) * ζ ^ 15
          - ((4 / 9) : ℂ) * ζ ^ 18
          + ((13 / 9) : ℂ) * ζ ^ 19
          - ((2 / 9) : ℂ) * ζ ^ 20
          - ((13 / 9) : ℂ) * ζ ^ 23
          + ((2 / 9) : ℂ) * ζ ^ 24
          - ((2 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 9) : ℂ)
          - ((1 / 9) : ℂ) * ζ ^ 4
          + ((1 / 9) : ℂ) * ζ ^ 5
          + ((1 / 9) : ℂ) * ζ ^ 8
          - ((1 / 9) : ℂ) * ζ ^ 9
          - ((4 / 9) : ℂ) * ζ ^ 10
          + ((1 / 9) : ℂ) * ζ ^ 13
          + ((4 / 9) : ℂ) * ζ ^ 14
          - ((13 / 9) : ℂ) * ζ ^ 15
          - ((4 / 9) : ℂ) * ζ ^ 18
          + ((13 / 9) : ℂ) * ζ ^ 19
          - ((2 / 9) : ℂ) * ζ ^ 20
          - ((13 / 9) : ℂ) * ζ ^ 23
          + ((2 / 9) : ℂ) * ζ ^ 24
          - ((2 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry04_07 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (4 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (4 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 9) : ℂ)
          - ((1 / 9) : ℂ) * ζ ^ 4
          - ((5 / 9) : ℂ) * ζ ^ 5
          + ((1 / 9) : ℂ) * ζ ^ 8
          + ((5 / 9) : ℂ) * ζ ^ 9
          + ((5 / 9) : ℂ) * ζ ^ 10
          - ((5 / 9) : ℂ) * ζ ^ 13
          - ((5 / 9) : ℂ) * ζ ^ 14
          - ((1 / 9) : ℂ) * ζ ^ 15
          + ((5 / 9) : ℂ) * ζ ^ 18
          + ((1 / 9) : ℂ) * ζ ^ 19
          + ((4 / 9) : ℂ) * ζ ^ 20
          - ((1 / 9) : ℂ) * ζ ^ 23
          - ((4 / 9) : ℂ) * ζ ^ 24
          + ((4 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 9) : ℂ)
          - ((1 / 9) : ℂ) * ζ ^ 4
          - ((5 / 9) : ℂ) * ζ ^ 5
          + ((1 / 9) : ℂ) * ζ ^ 8
          + ((5 / 9) : ℂ) * ζ ^ 9
          + ((5 / 9) : ℂ) * ζ ^ 10
          - ((5 / 9) : ℂ) * ζ ^ 13
          - ((5 / 9) : ℂ) * ζ ^ 14
          - ((1 / 9) : ℂ) * ζ ^ 15
          + ((5 / 9) : ℂ) * ζ ^ 18
          + ((1 / 9) : ℂ) * ζ ^ 19
          + ((4 / 9) : ℂ) * ζ ^ 20
          - ((1 / 9) : ℂ) * ζ ^ 23
          - ((4 / 9) : ℂ) * ζ ^ 24
          + ((4 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry04_08 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (4 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (4 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((10 / 9) : ℂ)
          - ((10 / 9) : ℂ) * ζ ^ 4
          - ((2 / 9) : ℂ) * ζ ^ 5
          + ((10 / 9) : ℂ) * ζ ^ 8
          + ((2 / 9) : ℂ) * ζ ^ 9
          + ((14 / 9) : ℂ) * ζ ^ 10
          - ((2 / 9) : ℂ) * ζ ^ 13
          - ((14 / 9) : ℂ) * ζ ^ 14
          + ((17 / 9) : ℂ) * ζ ^ 15
          + ((14 / 9) : ℂ) * ζ ^ 18
          - ((17 / 9) : ℂ) * ζ ^ 19
          + ((7 / 9) : ℂ) * ζ ^ 20
          + ((17 / 9) : ℂ) * ζ ^ 23
          - ((7 / 9) : ℂ) * ζ ^ 24
          + ((7 / 9) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((10 / 9) : ℂ)
          - ((10 / 9) : ℂ) * ζ ^ 4
          - ((2 / 9) : ℂ) * ζ ^ 5
          + ((10 / 9) : ℂ) * ζ ^ 8
          + ((2 / 9) : ℂ) * ζ ^ 9
          + ((14 / 9) : ℂ) * ζ ^ 10
          - ((2 / 9) : ℂ) * ζ ^ 13
          - ((14 / 9) : ℂ) * ζ ^ 14
          + ((17 / 9) : ℂ) * ζ ^ 15
          + ((14 / 9) : ℂ) * ζ ^ 18
          - ((17 / 9) : ℂ) * ζ ^ 19
          + ((7 / 9) : ℂ) * ζ ^ 20
          + ((17 / 9) : ℂ) * ζ ^ 23
          - ((7 / 9) : ℂ) * ζ ^ 24
          + ((7 / 9) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry04_09 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (4 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (4 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 3) : ℂ) * ζ ^ 15
          + ((1 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 3) : ℂ) * ζ ^ 15
          + ((1 / 3) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry05_00 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (5 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (5 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((2 / 3) : ℂ)
          + ((2 / 3) : ℂ) * ζ ^ 4
          - ((1 / 2) : ℂ) * ζ ^ 5
          - ((2 / 3) : ℂ) * ζ ^ 8
          + ((1 / 2) : ℂ) * ζ ^ 9
          - ((1 / 6) : ℂ) * ζ ^ 10
          - ((1 / 2) : ℂ) * ζ ^ 13
          + ((1 / 6) : ℂ) * ζ ^ 14
          + ((1 / 2) : ℂ) * ζ ^ 15
          - ((1 / 6) : ℂ) * ζ ^ 18
          - ((1 / 2) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          + ((1 / 2) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((2 / 3) : ℂ)
          + ((2 / 3) : ℂ) * ζ ^ 4
          - ((1 / 2) : ℂ) * ζ ^ 5
          - ((2 / 3) : ℂ) * ζ ^ 8
          + ((1 / 2) : ℂ) * ζ ^ 9
          - ((1 / 6) : ℂ) * ζ ^ 10
          - ((1 / 2) : ℂ) * ζ ^ 13
          + ((1 / 6) : ℂ) * ζ ^ 14
          + ((1 / 2) : ℂ) * ζ ^ 15
          - ((1 / 6) : ℂ) * ζ ^ 18
          - ((1 / 2) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          + ((1 / 2) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry05_01 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (5 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (5 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 6) : ℂ)
          + ((1 / 6) : ℂ) * ζ ^ 4
          + ((4 / 3) : ℂ) * ζ ^ 5
          - ((1 / 6) : ℂ) * ζ ^ 8
          - ((4 / 3) : ℂ) * ζ ^ 9
          + ((3 / 2) : ℂ) * ζ ^ 10
          + ((4 / 3) : ℂ) * ζ ^ 13
          - ((3 / 2) : ℂ) * ζ ^ 14
          - ((1 / 3) : ℂ) * ζ ^ 15
          + ((3 / 2) : ℂ) * ζ ^ 18
          + ((1 / 3) : ℂ) * ζ ^ 19
          - ((1 / 6) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 23
          + ((1 / 6) : ℂ) * ζ ^ 24
          - ((1 / 6) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 6) : ℂ)
          + ((1 / 6) : ℂ) * ζ ^ 4
          + ((4 / 3) : ℂ) * ζ ^ 5
          - ((1 / 6) : ℂ) * ζ ^ 8
          - ((4 / 3) : ℂ) * ζ ^ 9
          + ((3 / 2) : ℂ) * ζ ^ 10
          + ((4 / 3) : ℂ) * ζ ^ 13
          - ((3 / 2) : ℂ) * ζ ^ 14
          - ((1 / 3) : ℂ) * ζ ^ 15
          + ((3 / 2) : ℂ) * ζ ^ 18
          + ((1 / 3) : ℂ) * ζ ^ 19
          - ((1 / 6) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 23
          + ((1 / 6) : ℂ) * ζ ^ 24
          - ((1 / 6) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry05_02 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (5 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (5 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 3) : ℂ)
          - ((2 / 3) : ℂ) * ζ ^ 4
          + ((7 / 6) : ℂ) * ζ ^ 5
          + ((2 / 3) : ℂ) * ζ ^ 8
          - ((7 / 6) : ℂ) * ζ ^ 9
          + ((1 / 2) : ℂ) * ζ ^ 10
          + ((7 / 6) : ℂ) * ζ ^ 13
          - ((1 / 2) : ℂ) * ζ ^ 14
          - ((1 / 6) : ℂ) * ζ ^ 15
          + ((1 / 2) : ℂ) * ζ ^ 18
          + ((1 / 6) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 6) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 3) : ℂ)
          - ((2 / 3) : ℂ) * ζ ^ 4
          + ((7 / 6) : ℂ) * ζ ^ 5
          + ((2 / 3) : ℂ) * ζ ^ 8
          - ((7 / 6) : ℂ) * ζ ^ 9
          + ((1 / 2) : ℂ) * ζ ^ 10
          + ((7 / 6) : ℂ) * ζ ^ 13
          - ((1 / 2) : ℂ) * ζ ^ 14
          - ((1 / 6) : ℂ) * ζ ^ 15
          + ((1 / 2) : ℂ) * ζ ^ 18
          + ((1 / 6) : ℂ) * ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 6) : ℂ) * ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry05_03 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (5 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (5 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 6) : ℂ)
          - ((1 / 6) : ℂ) * ζ ^ 4
          - ((1 / 6) : ℂ) * ζ ^ 5
          + ((1 / 6) : ℂ) * ζ ^ 8
          + ((1 / 6) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 10
          - ((1 / 6) : ℂ) * ζ ^ 13
          - ((1 / 3) : ℂ) * ζ ^ 14
          + ((2 / 3) : ℂ) * ζ ^ 15
          + ((1 / 3) : ℂ) * ζ ^ 18
          - ((2 / 3) : ℂ) * ζ ^ 19
          + ((2 / 3) : ℂ) * ζ ^ 23
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 6) : ℂ)
          - ((1 / 6) : ℂ) * ζ ^ 4
          - ((1 / 6) : ℂ) * ζ ^ 5
          + ((1 / 6) : ℂ) * ζ ^ 8
          + ((1 / 6) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 10
          - ((1 / 6) : ℂ) * ζ ^ 13
          - ((1 / 3) : ℂ) * ζ ^ 14
          + ((2 / 3) : ℂ) * ζ ^ 15
          + ((1 / 3) : ℂ) * ζ ^ 18
          - ((2 / 3) : ℂ) * ζ ^ 19
          + ((2 / 3) : ℂ) * ζ ^ 23
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry05_04 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (5 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (5 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((2 / 3) : ℂ)
          + ((2 / 3) : ℂ) * ζ ^ 4
          + ((1 / 6) : ℂ) * ζ ^ 5
          - ((2 / 3) : ℂ) * ζ ^ 8
          - ((1 / 6) : ℂ) * ζ ^ 9
          + ((1 / 6) : ℂ) * ζ ^ 10
          + ((1 / 6) : ℂ) * ζ ^ 13
          - ((1 / 6) : ℂ) * ζ ^ 14
          - ((2 / 3) : ℂ) * ζ ^ 15
          + ((1 / 6) : ℂ) * ζ ^ 18
          + ((2 / 3) : ℂ) * ζ ^ 19
          + ((1 / 2) : ℂ) * ζ ^ 20
          - ((2 / 3) : ℂ) * ζ ^ 23
          - ((1 / 2) : ℂ) * ζ ^ 24
          + ((1 / 2) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((2 / 3) : ℂ)
          + ((2 / 3) : ℂ) * ζ ^ 4
          + ((1 / 6) : ℂ) * ζ ^ 5
          - ((2 / 3) : ℂ) * ζ ^ 8
          - ((1 / 6) : ℂ) * ζ ^ 9
          + ((1 / 6) : ℂ) * ζ ^ 10
          + ((1 / 6) : ℂ) * ζ ^ 13
          - ((1 / 6) : ℂ) * ζ ^ 14
          - ((2 / 3) : ℂ) * ζ ^ 15
          + ((1 / 6) : ℂ) * ζ ^ 18
          + ((2 / 3) : ℂ) * ζ ^ 19
          + ((1 / 2) : ℂ) * ζ ^ 20
          - ((2 / 3) : ℂ) * ζ ^ 23
          - ((1 / 2) : ℂ) * ζ ^ 24
          + ((1 / 2) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry05_05 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (5 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (5 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 6) : ℂ)
          + ((1 / 6) : ℂ) * ζ ^ 4
          + ((2 / 3) : ℂ) * ζ ^ 5
          - ((1 / 6) : ℂ) * ζ ^ 8
          - ((2 / 3) : ℂ) * ζ ^ 9
          + ((7 / 6) : ℂ) * ζ ^ 10
          + ((2 / 3) : ℂ) * ζ ^ 13
          - ((7 / 6) : ℂ) * ζ ^ 14
          - ((2 / 3) : ℂ) * ζ ^ 15
          + ((7 / 6) : ℂ) * ζ ^ 18
          + ((2 / 3) : ℂ) * ζ ^ 19
          - ((1 / 2) : ℂ) * ζ ^ 20
          - ((2 / 3) : ℂ) * ζ ^ 23
          + ((1 / 2) : ℂ) * ζ ^ 24
          - ((1 / 2) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 6) : ℂ)
          + ((1 / 6) : ℂ) * ζ ^ 4
          + ((2 / 3) : ℂ) * ζ ^ 5
          - ((1 / 6) : ℂ) * ζ ^ 8
          - ((2 / 3) : ℂ) * ζ ^ 9
          + ((7 / 6) : ℂ) * ζ ^ 10
          + ((2 / 3) : ℂ) * ζ ^ 13
          - ((7 / 6) : ℂ) * ζ ^ 14
          - ((2 / 3) : ℂ) * ζ ^ 15
          + ((7 / 6) : ℂ) * ζ ^ 18
          + ((2 / 3) : ℂ) * ζ ^ 19
          - ((1 / 2) : ℂ) * ζ ^ 20
          - ((2 / 3) : ℂ) * ζ ^ 23
          + ((1 / 2) : ℂ) * ζ ^ 24
          - ((1 / 2) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry05_06 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (5 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (5 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 6) : ℂ)
          - ((1 / 6) : ℂ) * ζ ^ 4
          - ((1 / 6) : ℂ) * ζ ^ 5
          + ((1 / 6) : ℂ) * ζ ^ 8
          + ((1 / 6) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 10
          - ((1 / 6) : ℂ) * ζ ^ 13
          - ((1 / 3) : ℂ) * ζ ^ 14
          + ((2 / 3) : ℂ) * ζ ^ 15
          + ((1 / 3) : ℂ) * ζ ^ 18
          - ((2 / 3) : ℂ) * ζ ^ 19
          + ((2 / 3) : ℂ) * ζ ^ 23
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 6) : ℂ)
          - ((1 / 6) : ℂ) * ζ ^ 4
          - ((1 / 6) : ℂ) * ζ ^ 5
          + ((1 / 6) : ℂ) * ζ ^ 8
          + ((1 / 6) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 10
          - ((1 / 6) : ℂ) * ζ ^ 13
          - ((1 / 3) : ℂ) * ζ ^ 14
          + ((2 / 3) : ℂ) * ζ ^ 15
          + ((1 / 3) : ℂ) * ζ ^ 18
          - ((2 / 3) : ℂ) * ζ ^ 19
          + ((2 / 3) : ℂ) * ζ ^ 23
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry05_07 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (5 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (5 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 3) : ℂ)
          - ((2 / 3) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 5
          + ((2 / 3) : ℂ) * ζ ^ 8
          - ((1 / 2) : ℂ) * ζ ^ 9
          + ((1 / 6) : ℂ) * ζ ^ 10
          + ((1 / 2) : ℂ) * ζ ^ 13
          - ((1 / 6) : ℂ) * ζ ^ 14
          - ((1 / 2) : ℂ) * ζ ^ 15
          + ((1 / 6) : ℂ) * ζ ^ 18
          + ((1 / 2) : ℂ) * ζ ^ 19
          + ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 2) : ℂ) * ζ ^ 23
          - ((1 / 3) : ℂ) * ζ ^ 24
          + ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 3) : ℂ)
          - ((2 / 3) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 5
          + ((2 / 3) : ℂ) * ζ ^ 8
          - ((1 / 2) : ℂ) * ζ ^ 9
          + ((1 / 6) : ℂ) * ζ ^ 10
          + ((1 / 2) : ℂ) * ζ ^ 13
          - ((1 / 6) : ℂ) * ζ ^ 14
          - ((1 / 2) : ℂ) * ζ ^ 15
          + ((1 / 6) : ℂ) * ζ ^ 18
          + ((1 / 2) : ℂ) * ζ ^ 19
          + ((1 / 3) : ℂ) * ζ ^ 20
          - ((1 / 2) : ℂ) * ζ ^ 23
          - ((1 / 3) : ℂ) * ζ ^ 24
          + ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry05_08 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (5 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (5 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          + ((3 / 2) : ℂ) * ζ ^ 5
          - ((1 / 3) : ℂ) * ζ ^ 8
          - ((3 / 2) : ℂ) * ζ ^ 9
          + ((1 / 6) : ℂ) * ζ ^ 10
          + ((3 / 2) : ℂ) * ζ ^ 13
          - ((1 / 6) : ℂ) * ζ ^ 14
          + ((1 / 6) : ℂ) * ζ ^ 18
          - ((1 / 6) : ℂ) * ζ ^ 20
          + ((1 / 6) : ℂ) * ζ ^ 24
          - ((1 / 6) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          + ((3 / 2) : ℂ) * ζ ^ 5
          - ((1 / 3) : ℂ) * ζ ^ 8
          - ((3 / 2) : ℂ) * ζ ^ 9
          + ((1 / 6) : ℂ) * ζ ^ 10
          + ((3 / 2) : ℂ) * ζ ^ 13
          - ((1 / 6) : ℂ) * ζ ^ 14
          + ((1 / 6) : ℂ) * ζ ^ 18
          - ((1 / 6) : ℂ) * ζ ^ 20
          + ((1 / 6) : ℂ) * ζ ^ 24
          - ((1 / 6) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry05_09 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (5 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (5 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry06_00 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (6 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (6 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry06_01 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (6 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (6 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry06_02 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (6 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (6 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry06_03 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (6 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (6 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry06_04 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (6 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (6 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry06_05 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (6 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (6 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry06_06 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (6 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (6 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry06_07 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (6 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (6 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry06_08 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (6 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (6 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry06_09 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (6 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (6 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry07_00 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (7 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (7 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry07_01 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (7 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (7 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (ζ ^ 5 - ζ ^ 9 + ζ ^ 13 - ζ ^ 15 + ζ ^ 19 - ζ ^ 23) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(ζ ^ 5 - ζ ^ 9 + ζ ^ 13 - ζ ^ 15 + ζ ^ 19 - ζ ^ 23)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry07_02 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (7 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (7 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry07_03 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (7 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (7 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(1 : ℂ)
          + ζ ^ 4
          - ζ ^ 5
          - ζ ^ 8
          + ζ ^ 9
          - ζ ^ 13
          - ζ ^ 20
          + ζ ^ 24
          - ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(1 : ℂ)
          + ζ ^ 4
          - ζ ^ 5
          - ζ ^ 8
          + ζ ^ 9
          - ζ ^ 13
          - ζ ^ 20
          + ζ ^ 24
          - ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry07_04 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (7 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (7 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry07_05 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (7 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (7 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry07_06 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (7 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (7 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 5 + ζ ^ 9 - ζ ^ 13 - ζ ^ 15 + ζ ^ 19 - ζ ^ 23) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 5 + ζ ^ 9 - ζ ^ 13 - ζ ^ 15 + ζ ^ 19 - ζ ^ 23)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry07_07 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (7 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (7 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry07_08 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (7 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (7 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (ζ ^ 5 - ζ ^ 9 + ζ ^ 13) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(ζ ^ 5 - ζ ^ 9 + ζ ^ 13)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry07_09 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (7 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (7 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry08_00 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (8 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (8 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((2 / 3) : ℂ)
          + ((2 / 3) : ℂ) * ζ ^ 4
          - ((2 / 3) : ℂ) * ζ ^ 8
          - ((1 / 3) : ℂ) * ζ ^ 15
          + ((1 / 3) : ℂ) * ζ ^ 19
          - ((2 / 3) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 23
          + ((2 / 3) : ℂ) * ζ ^ 24
          - ((2 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((2 / 3) : ℂ)
          + ((2 / 3) : ℂ) * ζ ^ 4
          - ((2 / 3) : ℂ) * ζ ^ 8
          - ((1 / 3) : ℂ) * ζ ^ 15
          + ((1 / 3) : ℂ) * ζ ^ 19
          - ((2 / 3) : ℂ) * ζ ^ 20
          - ((1 / 3) : ℂ) * ζ ^ 23
          + ((2 / 3) : ℂ) * ζ ^ 24
          - ((2 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry08_01 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (8 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (8 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((4 / 3) : ℂ)
          - ((4 / 3) : ℂ) * ζ ^ 4
          + ((2 / 3) : ℂ) * ζ ^ 5
          + ((4 / 3) : ℂ) * ζ ^ 8
          - ((2 / 3) : ℂ) * ζ ^ 9
          + ((2 / 3) : ℂ) * ζ ^ 13
          + ((1 / 3) : ℂ) * ζ ^ 15
          - ((1 / 3) : ℂ) * ζ ^ 19
          + ((4 / 3) : ℂ) * ζ ^ 20
          + ((1 / 3) : ℂ) * ζ ^ 23
          - ((4 / 3) : ℂ) * ζ ^ 24
          + ((4 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((4 / 3) : ℂ)
          - ((4 / 3) : ℂ) * ζ ^ 4
          + ((2 / 3) : ℂ) * ζ ^ 5
          + ((4 / 3) : ℂ) * ζ ^ 8
          - ((2 / 3) : ℂ) * ζ ^ 9
          + ((2 / 3) : ℂ) * ζ ^ 13
          + ((1 / 3) : ℂ) * ζ ^ 15
          - ((1 / 3) : ℂ) * ζ ^ 19
          + ((4 / 3) : ℂ) * ζ ^ 20
          + ((1 / 3) : ℂ) * ζ ^ 23
          - ((4 / 3) : ℂ) * ζ ^ 24
          + ((4 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry08_02 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (8 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (8 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 3) : ℂ)
          - ((2 / 3) : ℂ) * ζ ^ 4
          + ((1 / 3) : ℂ) * ζ ^ 5
          + ((2 / 3) : ℂ) * ζ ^ 8
          - ((1 / 3) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 13
          + ((2 / 3) : ℂ) * ζ ^ 15
          - ((2 / 3) : ℂ) * ζ ^ 19
          + ((2 / 3) : ℂ) * ζ ^ 20
          + ((2 / 3) : ℂ) * ζ ^ 23
          - ((2 / 3) : ℂ) * ζ ^ 24
          + ((2 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 3) : ℂ)
          - ((2 / 3) : ℂ) * ζ ^ 4
          + ((1 / 3) : ℂ) * ζ ^ 5
          + ((2 / 3) : ℂ) * ζ ^ 8
          - ((1 / 3) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 13
          + ((2 / 3) : ℂ) * ζ ^ 15
          - ((2 / 3) : ℂ) * ζ ^ 19
          + ((2 / 3) : ℂ) * ζ ^ 20
          + ((2 / 3) : ℂ) * ζ ^ 23
          - ((2 / 3) : ℂ) * ζ ^ 24
          + ((2 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry08_03 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (8 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (8 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          + ((2 / 3) : ℂ) * ζ ^ 5
          - ((1 / 3) : ℂ) * ζ ^ 8
          - ((2 / 3) : ℂ) * ζ ^ 9
          + ((2 / 3) : ℂ) * ζ ^ 13
          - ζ ^ 15
          + ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          + ((2 / 3) : ℂ) * ζ ^ 5
          - ((1 / 3) : ℂ) * ζ ^ 8
          - ((2 / 3) : ℂ) * ζ ^ 9
          + ((2 / 3) : ℂ) * ζ ^ 13
          - ζ ^ 15
          + ζ ^ 19
          - ((1 / 3) : ℂ) * ζ ^ 20
          - ζ ^ 23
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry08_04 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (8 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (8 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 3) : ℂ)
          - ((1 / 3) : ℂ) * ζ ^ 4
          + ((1 / 3) : ℂ) * ζ ^ 5
          + ((1 / 3) : ℂ) * ζ ^ 8
          - ((1 / 3) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 13
          - ζ ^ 15
          + ζ ^ 19
          + ((1 / 3) : ℂ) * ζ ^ 20
          - ζ ^ 23
          - ((1 / 3) : ℂ) * ζ ^ 24
          + ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 3) : ℂ)
          - ((1 / 3) : ℂ) * ζ ^ 4
          + ((1 / 3) : ℂ) * ζ ^ 5
          + ((1 / 3) : ℂ) * ζ ^ 8
          - ((1 / 3) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 13
          - ζ ^ 15
          + ζ ^ 19
          + ((1 / 3) : ℂ) * ζ ^ 20
          - ζ ^ 23
          - ((1 / 3) : ℂ) * ζ ^ 24
          + ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry08_05 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (8 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (8 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 3) : ℂ)
          - ((1 / 3) : ℂ) * ζ ^ 4
          + ((1 / 3) : ℂ) * ζ ^ 5
          + ((1 / 3) : ℂ) * ζ ^ 8
          - ((1 / 3) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 13
          - ζ ^ 15
          + ζ ^ 19
          + ((1 / 3) : ℂ) * ζ ^ 20
          - ζ ^ 23
          - ((1 / 3) : ℂ) * ζ ^ 24
          + ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 3) : ℂ)
          - ((1 / 3) : ℂ) * ζ ^ 4
          + ((1 / 3) : ℂ) * ζ ^ 5
          + ((1 / 3) : ℂ) * ζ ^ 8
          - ((1 / 3) : ℂ) * ζ ^ 9
          + ((1 / 3) : ℂ) * ζ ^ 13
          - ζ ^ 15
          + ζ ^ 19
          + ((1 / 3) : ℂ) * ζ ^ 20
          - ζ ^ 23
          - ((1 / 3) : ℂ) * ζ ^ 24
          + ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry08_06 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (8 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (8 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          + ((2 / 3) : ℂ) * ζ ^ 5
          - ((1 / 3) : ℂ) * ζ ^ 8
          - ((2 / 3) : ℂ) * ζ ^ 9
          + ((2 / 3) : ℂ) * ζ ^ 13
          - ((1 / 3) : ℂ) * ζ ^ 20
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 3) : ℂ)
          + ((1 / 3) : ℂ) * ζ ^ 4
          + ((2 / 3) : ℂ) * ζ ^ 5
          - ((1 / 3) : ℂ) * ζ ^ 8
          - ((2 / 3) : ℂ) * ζ ^ 9
          + ((2 / 3) : ℂ) * ζ ^ 13
          - ((1 / 3) : ℂ) * ζ ^ 20
          + ((1 / 3) : ℂ) * ζ ^ 24
          - ((1 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry08_07 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (8 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (8 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 3) : ℂ)
          - ((2 / 3) : ℂ) * ζ ^ 4
          + ((2 / 3) : ℂ) * ζ ^ 8
          + ((1 / 3) : ℂ) * ζ ^ 15
          - ((1 / 3) : ℂ) * ζ ^ 19
          + ((2 / 3) : ℂ) * ζ ^ 20
          + ((1 / 3) : ℂ) * ζ ^ 23
          - ((2 / 3) : ℂ) * ζ ^ 24
          + ((2 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 3) : ℂ)
          - ((2 / 3) : ℂ) * ζ ^ 4
          + ((2 / 3) : ℂ) * ζ ^ 8
          + ((1 / 3) : ℂ) * ζ ^ 15
          - ((1 / 3) : ℂ) * ζ ^ 19
          + ((2 / 3) : ℂ) * ζ ^ 20
          + ((1 / 3) : ℂ) * ζ ^ 23
          - ((2 / 3) : ℂ) * ζ ^ 24
          + ((2 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry08_08 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (8 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (8 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 3) : ℂ)
          - ((2 / 3) : ℂ) * ζ ^ 4
          + ζ ^ 5
          + ((2 / 3) : ℂ) * ζ ^ 8
          - ζ ^ 9
          + ζ ^ 13
          + ((4 / 3) : ℂ) * ζ ^ 15
          - ((4 / 3) : ℂ) * ζ ^ 19
          + ((2 / 3) : ℂ) * ζ ^ 20
          + ((4 / 3) : ℂ) * ζ ^ 23
          - ((2 / 3) : ℂ) * ζ ^ 24
          + ((2 / 3) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 3) : ℂ)
          - ((2 / 3) : ℂ) * ζ ^ 4
          + ζ ^ 5
          + ((2 / 3) : ℂ) * ζ ^ 8
          - ζ ^ 9
          + ζ ^ 13
          + ((4 / 3) : ℂ) * ζ ^ 15
          - ((4 / 3) : ℂ) * ζ ^ 19
          + ((2 / 3) : ℂ) * ζ ^ 20
          + ((4 / 3) : ℂ) * ζ ^ 23
          - ((2 / 3) : ℂ) * ζ ^ 24
          + ((2 / 3) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry08_09 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (8 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (8 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry09_00 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (9 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (9 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry09_01 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (9 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (9 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry09_02 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (9 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (9 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry09_03 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (9 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (9 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry09_04 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (9 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (9 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry09_05 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (9 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (9 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry09_06 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (9 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (9 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry09_07 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (9 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (9 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry09_08 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (9 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (9 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow25_longMatrixABB_entry09_09 :
    (alternatingSixAmbientRow25LongMatrixAB
        * alternatingSixFiveAmbient_row25_matrixB)
          (9 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow25LongMatrixABB
        (9 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow25LongMatrixAB,
    alternatingSixFiveAmbient_row25_matrixB,
    alternatingSixAmbientRow25LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

theorem alternatingSixAmbientRow25_longMatrixABB_mul :
    alternatingSixAmbientRow25LongMatrixAB *
        alternatingSixFiveAmbient_row25_matrixB =
      alternatingSixAmbientRow25LongMatrixABB := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientRow25_longMatrixABB_entry00_00
  · exact alternatingSixAmbientRow25_longMatrixABB_entry00_01
  · exact alternatingSixAmbientRow25_longMatrixABB_entry00_02
  · exact alternatingSixAmbientRow25_longMatrixABB_entry00_03
  · exact alternatingSixAmbientRow25_longMatrixABB_entry00_04
  · exact alternatingSixAmbientRow25_longMatrixABB_entry00_05
  · exact alternatingSixAmbientRow25_longMatrixABB_entry00_06
  · exact alternatingSixAmbientRow25_longMatrixABB_entry00_07
  · exact alternatingSixAmbientRow25_longMatrixABB_entry00_08
  · exact alternatingSixAmbientRow25_longMatrixABB_entry00_09
  · exact alternatingSixAmbientRow25_longMatrixABB_entry01_00
  · exact alternatingSixAmbientRow25_longMatrixABB_entry01_01
  · exact alternatingSixAmbientRow25_longMatrixABB_entry01_02
  · exact alternatingSixAmbientRow25_longMatrixABB_entry01_03
  · exact alternatingSixAmbientRow25_longMatrixABB_entry01_04
  · exact alternatingSixAmbientRow25_longMatrixABB_entry01_05
  · exact alternatingSixAmbientRow25_longMatrixABB_entry01_06
  · exact alternatingSixAmbientRow25_longMatrixABB_entry01_07
  · exact alternatingSixAmbientRow25_longMatrixABB_entry01_08
  · exact alternatingSixAmbientRow25_longMatrixABB_entry01_09
  · exact alternatingSixAmbientRow25_longMatrixABB_entry02_00
  · exact alternatingSixAmbientRow25_longMatrixABB_entry02_01
  · exact alternatingSixAmbientRow25_longMatrixABB_entry02_02
  · exact alternatingSixAmbientRow25_longMatrixABB_entry02_03
  · exact alternatingSixAmbientRow25_longMatrixABB_entry02_04
  · exact alternatingSixAmbientRow25_longMatrixABB_entry02_05
  · exact alternatingSixAmbientRow25_longMatrixABB_entry02_06
  · exact alternatingSixAmbientRow25_longMatrixABB_entry02_07
  · exact alternatingSixAmbientRow25_longMatrixABB_entry02_08
  · exact alternatingSixAmbientRow25_longMatrixABB_entry02_09
  · exact alternatingSixAmbientRow25_longMatrixABB_entry03_00
  · exact alternatingSixAmbientRow25_longMatrixABB_entry03_01
  · exact alternatingSixAmbientRow25_longMatrixABB_entry03_02
  · exact alternatingSixAmbientRow25_longMatrixABB_entry03_03
  · exact alternatingSixAmbientRow25_longMatrixABB_entry03_04
  · exact alternatingSixAmbientRow25_longMatrixABB_entry03_05
  · exact alternatingSixAmbientRow25_longMatrixABB_entry03_06
  · exact alternatingSixAmbientRow25_longMatrixABB_entry03_07
  · exact alternatingSixAmbientRow25_longMatrixABB_entry03_08
  · exact alternatingSixAmbientRow25_longMatrixABB_entry03_09
  · exact alternatingSixAmbientRow25_longMatrixABB_entry04_00
  · exact alternatingSixAmbientRow25_longMatrixABB_entry04_01
  · exact alternatingSixAmbientRow25_longMatrixABB_entry04_02
  · exact alternatingSixAmbientRow25_longMatrixABB_entry04_03
  · exact alternatingSixAmbientRow25_longMatrixABB_entry04_04
  · exact alternatingSixAmbientRow25_longMatrixABB_entry04_05
  · exact alternatingSixAmbientRow25_longMatrixABB_entry04_06
  · exact alternatingSixAmbientRow25_longMatrixABB_entry04_07
  · exact alternatingSixAmbientRow25_longMatrixABB_entry04_08
  · exact alternatingSixAmbientRow25_longMatrixABB_entry04_09
  · exact alternatingSixAmbientRow25_longMatrixABB_entry05_00
  · exact alternatingSixAmbientRow25_longMatrixABB_entry05_01
  · exact alternatingSixAmbientRow25_longMatrixABB_entry05_02
  · exact alternatingSixAmbientRow25_longMatrixABB_entry05_03
  · exact alternatingSixAmbientRow25_longMatrixABB_entry05_04
  · exact alternatingSixAmbientRow25_longMatrixABB_entry05_05
  · exact alternatingSixAmbientRow25_longMatrixABB_entry05_06
  · exact alternatingSixAmbientRow25_longMatrixABB_entry05_07
  · exact alternatingSixAmbientRow25_longMatrixABB_entry05_08
  · exact alternatingSixAmbientRow25_longMatrixABB_entry05_09
  · exact alternatingSixAmbientRow25_longMatrixABB_entry06_00
  · exact alternatingSixAmbientRow25_longMatrixABB_entry06_01
  · exact alternatingSixAmbientRow25_longMatrixABB_entry06_02
  · exact alternatingSixAmbientRow25_longMatrixABB_entry06_03
  · exact alternatingSixAmbientRow25_longMatrixABB_entry06_04
  · exact alternatingSixAmbientRow25_longMatrixABB_entry06_05
  · exact alternatingSixAmbientRow25_longMatrixABB_entry06_06
  · exact alternatingSixAmbientRow25_longMatrixABB_entry06_07
  · exact alternatingSixAmbientRow25_longMatrixABB_entry06_08
  · exact alternatingSixAmbientRow25_longMatrixABB_entry06_09
  · exact alternatingSixAmbientRow25_longMatrixABB_entry07_00
  · exact alternatingSixAmbientRow25_longMatrixABB_entry07_01
  · exact alternatingSixAmbientRow25_longMatrixABB_entry07_02
  · exact alternatingSixAmbientRow25_longMatrixABB_entry07_03
  · exact alternatingSixAmbientRow25_longMatrixABB_entry07_04
  · exact alternatingSixAmbientRow25_longMatrixABB_entry07_05
  · exact alternatingSixAmbientRow25_longMatrixABB_entry07_06
  · exact alternatingSixAmbientRow25_longMatrixABB_entry07_07
  · exact alternatingSixAmbientRow25_longMatrixABB_entry07_08
  · exact alternatingSixAmbientRow25_longMatrixABB_entry07_09
  · exact alternatingSixAmbientRow25_longMatrixABB_entry08_00
  · exact alternatingSixAmbientRow25_longMatrixABB_entry08_01
  · exact alternatingSixAmbientRow25_longMatrixABB_entry08_02
  · exact alternatingSixAmbientRow25_longMatrixABB_entry08_03
  · exact alternatingSixAmbientRow25_longMatrixABB_entry08_04
  · exact alternatingSixAmbientRow25_longMatrixABB_entry08_05
  · exact alternatingSixAmbientRow25_longMatrixABB_entry08_06
  · exact alternatingSixAmbientRow25_longMatrixABB_entry08_07
  · exact alternatingSixAmbientRow25_longMatrixABB_entry08_08
  · exact alternatingSixAmbientRow25_longMatrixABB_entry08_09
  · exact alternatingSixAmbientRow25_longMatrixABB_entry09_00
  · exact alternatingSixAmbientRow25_longMatrixABB_entry09_01
  · exact alternatingSixAmbientRow25_longMatrixABB_entry09_02
  · exact alternatingSixAmbientRow25_longMatrixABB_entry09_03
  · exact alternatingSixAmbientRow25_longMatrixABB_entry09_04
  · exact alternatingSixAmbientRow25_longMatrixABB_entry09_05
  · exact alternatingSixAmbientRow25_longMatrixABB_entry09_06
  · exact alternatingSixAmbientRow25_longMatrixABB_entry09_07
  · exact alternatingSixAmbientRow25_longMatrixABB_entry09_08
  · exact alternatingSixAmbientRow25_longMatrixABB_entry09_09

end InductiveMcKay
end McKayConjecture
