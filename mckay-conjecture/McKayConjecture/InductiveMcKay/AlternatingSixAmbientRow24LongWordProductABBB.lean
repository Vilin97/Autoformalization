/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow24LongWordData

/-!
# One checked row-24 long-word multiplication

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
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry00_00 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (0 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((39 / 34) : ℂ)
          - ((39 / 34) : ℂ) * ζ ^ 4
          - ((7 / 34) : ℂ) * ζ ^ 5
          + ((39 / 34) : ℂ) * ζ ^ 8
          + ((7 / 34) : ℂ) * ζ ^ 9
          - ((7 / 34) : ℂ) * ζ ^ 13
          + ((45 / 34) : ℂ) * ζ ^ 15
          - ((45 / 34) : ℂ) * ζ ^ 19
          + ((39 / 34) : ℂ) * ζ ^ 20
          + ((45 / 34) : ℂ) * ζ ^ 23
          - ((39 / 34) : ℂ) * ζ ^ 24
          + ((39 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((39 / 34) : ℂ)
          - ((39 / 34) : ℂ) * ζ ^ 4
          - ((7 / 34) : ℂ) * ζ ^ 5
          + ((39 / 34) : ℂ) * ζ ^ 8
          + ((7 / 34) : ℂ) * ζ ^ 9
          - ((7 / 34) : ℂ) * ζ ^ 13
          + ((45 / 34) : ℂ) * ζ ^ 15
          - ((45 / 34) : ℂ) * ζ ^ 19
          + ((39 / 34) : ℂ) * ζ ^ 20
          + ((45 / 34) : ℂ) * ζ ^ 23
          - ((39 / 34) : ℂ) * ζ ^ 24
          + ((39 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry00_01 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (0 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((7 / 17) : ℂ)
          - ((7 / 17) : ℂ) * ζ ^ 4
          + ((14 / 17) : ℂ) * ζ ^ 5
          + ((7 / 17) : ℂ) * ζ ^ 8
          - ((14 / 17) : ℂ) * ζ ^ 9
          + ((14 / 17) : ℂ) * ζ ^ 13
          - ((5 / 17) : ℂ) * ζ ^ 15
          + ((5 / 17) : ℂ) * ζ ^ 19
          + ((7 / 17) : ℂ) * ζ ^ 20
          - ((5 / 17) : ℂ) * ζ ^ 23
          - ((7 / 17) : ℂ) * ζ ^ 24
          + ((7 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((7 / 17) : ℂ)
          - ((7 / 17) : ℂ) * ζ ^ 4
          + ((14 / 17) : ℂ) * ζ ^ 5
          + ((7 / 17) : ℂ) * ζ ^ 8
          - ((14 / 17) : ℂ) * ζ ^ 9
          + ((14 / 17) : ℂ) * ζ ^ 13
          - ((5 / 17) : ℂ) * ζ ^ 15
          + ((5 / 17) : ℂ) * ζ ^ 19
          + ((7 / 17) : ℂ) * ζ ^ 20
          - ((5 / 17) : ℂ) * ζ ^ 23
          - ((7 / 17) : ℂ) * ζ ^ 24
          + ((7 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry00_02 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (0 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((19 / 17) : ℂ)
          - ((19 / 17) : ℂ) * ζ ^ 4
          + ((38 / 17) : ℂ) * ζ ^ 5
          + ((19 / 17) : ℂ) * ζ ^ 8
          - ((38 / 17) : ℂ) * ζ ^ 9
          + ((38 / 17) : ℂ) * ζ ^ 13
          + ((1 / 17) : ℂ) * ζ ^ 15
          - ((1 / 17) : ℂ) * ζ ^ 19
          + ((19 / 17) : ℂ) * ζ ^ 20
          + ((1 / 17) : ℂ) * ζ ^ 23
          - ((19 / 17) : ℂ) * ζ ^ 24
          + ((19 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((19 / 17) : ℂ)
          - ((19 / 17) : ℂ) * ζ ^ 4
          + ((38 / 17) : ℂ) * ζ ^ 5
          + ((19 / 17) : ℂ) * ζ ^ 8
          - ((38 / 17) : ℂ) * ζ ^ 9
          + ((38 / 17) : ℂ) * ζ ^ 13
          + ((1 / 17) : ℂ) * ζ ^ 15
          - ((1 / 17) : ℂ) * ζ ^ 19
          + ((19 / 17) : ℂ) * ζ ^ 20
          + ((1 / 17) : ℂ) * ζ ^ 23
          - ((19 / 17) : ℂ) * ζ ^ 24
          + ((19 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry00_03 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (0 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((55 / 34) : ℂ)
          + ((55 / 34) : ℂ) * ζ ^ 4
          + ((9 / 34) : ℂ) * ζ ^ 5
          - ((55 / 34) : ℂ) * ζ ^ 8
          - ((9 / 34) : ℂ) * ζ ^ 9
          + ((9 / 34) : ℂ) * ζ ^ 13
          - ((19 / 34) : ℂ) * ζ ^ 15
          + ((19 / 34) : ℂ) * ζ ^ 19
          - ((55 / 34) : ℂ) * ζ ^ 20
          - ((19 / 34) : ℂ) * ζ ^ 23
          + ((55 / 34) : ℂ) * ζ ^ 24
          - ((55 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((55 / 34) : ℂ)
          + ((55 / 34) : ℂ) * ζ ^ 4
          + ((9 / 34) : ℂ) * ζ ^ 5
          - ((55 / 34) : ℂ) * ζ ^ 8
          - ((9 / 34) : ℂ) * ζ ^ 9
          + ((9 / 34) : ℂ) * ζ ^ 13
          - ((19 / 34) : ℂ) * ζ ^ 15
          + ((19 / 34) : ℂ) * ζ ^ 19
          - ((55 / 34) : ℂ) * ζ ^ 20
          - ((19 / 34) : ℂ) * ζ ^ 23
          + ((55 / 34) : ℂ) * ζ ^ 24
          - ((55 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry00_04 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (0 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((28 / 17) : ℂ)
          + ((28 / 17) : ℂ) * ζ ^ 4
          - ((22 / 17) : ℂ) * ζ ^ 5
          - ((28 / 17) : ℂ) * ζ ^ 8
          + ((22 / 17) : ℂ) * ζ ^ 9
          - ((22 / 17) : ℂ) * ζ ^ 13
          + ((3 / 17) : ℂ) * ζ ^ 15
          - ((3 / 17) : ℂ) * ζ ^ 19
          - ((28 / 17) : ℂ) * ζ ^ 20
          + ((3 / 17) : ℂ) * ζ ^ 23
          + ((28 / 17) : ℂ) * ζ ^ 24
          - ((28 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((28 / 17) : ℂ)
          + ((28 / 17) : ℂ) * ζ ^ 4
          - ((22 / 17) : ℂ) * ζ ^ 5
          - ((28 / 17) : ℂ) * ζ ^ 8
          + ((22 / 17) : ℂ) * ζ ^ 9
          - ((22 / 17) : ℂ) * ζ ^ 13
          + ((3 / 17) : ℂ) * ζ ^ 15
          - ((3 / 17) : ℂ) * ζ ^ 19
          - ((28 / 17) : ℂ) * ζ ^ 20
          + ((3 / 17) : ℂ) * ζ ^ 23
          + ((28 / 17) : ℂ) * ζ ^ 24
          - ((28 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry00_05 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (0 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((33 / 34) : ℂ)
          - ((33 / 34) : ℂ) * ζ ^ 4
          + ((15 / 34) : ℂ) * ζ ^ 5
          + ((33 / 34) : ℂ) * ζ ^ 8
          - ((15 / 34) : ℂ) * ζ ^ 9
          + ((15 / 34) : ℂ) * ζ ^ 13
          - ((9 / 34) : ℂ) * ζ ^ 15
          + ((9 / 34) : ℂ) * ζ ^ 19
          + ((33 / 34) : ℂ) * ζ ^ 20
          - ((9 / 34) : ℂ) * ζ ^ 23
          - ((33 / 34) : ℂ) * ζ ^ 24
          + ((33 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((33 / 34) : ℂ)
          - ((33 / 34) : ℂ) * ζ ^ 4
          + ((15 / 34) : ℂ) * ζ ^ 5
          + ((33 / 34) : ℂ) * ζ ^ 8
          - ((15 / 34) : ℂ) * ζ ^ 9
          + ((15 / 34) : ℂ) * ζ ^ 13
          - ((9 / 34) : ℂ) * ζ ^ 15
          + ((9 / 34) : ℂ) * ζ ^ 19
          + ((33 / 34) : ℂ) * ζ ^ 20
          - ((9 / 34) : ℂ) * ζ ^ 23
          - ((33 / 34) : ℂ) * ζ ^ 24
          + ((33 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry00_06 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (0 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((13 / 17) : ℂ)
          + ((13 / 17) : ℂ) * ζ ^ 4
          + ((8 / 17) : ℂ) * ζ ^ 5
          - ((13 / 17) : ℂ) * ζ ^ 8
          - ((8 / 17) : ℂ) * ζ ^ 9
          + ((8 / 17) : ℂ) * ζ ^ 13
          - ((32 / 17) : ℂ) * ζ ^ 15
          + ((32 / 17) : ℂ) * ζ ^ 19
          - ((13 / 17) : ℂ) * ζ ^ 20
          - ((32 / 17) : ℂ) * ζ ^ 23
          + ((13 / 17) : ℂ) * ζ ^ 24
          - ((13 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((13 / 17) : ℂ)
          + ((13 / 17) : ℂ) * ζ ^ 4
          + ((8 / 17) : ℂ) * ζ ^ 5
          - ((13 / 17) : ℂ) * ζ ^ 8
          - ((8 / 17) : ℂ) * ζ ^ 9
          + ((8 / 17) : ℂ) * ζ ^ 13
          - ((32 / 17) : ℂ) * ζ ^ 15
          + ((32 / 17) : ℂ) * ζ ^ 19
          - ((13 / 17) : ℂ) * ζ ^ 20
          - ((32 / 17) : ℂ) * ζ ^ 23
          + ((13 / 17) : ℂ) * ζ ^ 24
          - ((13 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry00_07 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (0 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((5 / 17) : ℂ)
          - ((5 / 17) : ℂ) * ζ ^ 4
          - ((7 / 17) : ℂ) * ζ ^ 5
          + ((5 / 17) : ℂ) * ζ ^ 8
          + ((7 / 17) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 13
          + ((11 / 17) : ℂ) * ζ ^ 15
          - ((11 / 17) : ℂ) * ζ ^ 19
          + ((5 / 17) : ℂ) * ζ ^ 20
          + ((11 / 17) : ℂ) * ζ ^ 23
          - ((5 / 17) : ℂ) * ζ ^ 24
          + ((5 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((5 / 17) : ℂ)
          - ((5 / 17) : ℂ) * ζ ^ 4
          - ((7 / 17) : ℂ) * ζ ^ 5
          + ((5 / 17) : ℂ) * ζ ^ 8
          + ((7 / 17) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 13
          + ((11 / 17) : ℂ) * ζ ^ 15
          - ((11 / 17) : ℂ) * ζ ^ 19
          + ((5 / 17) : ℂ) * ζ ^ 20
          + ((11 / 17) : ℂ) * ζ ^ 23
          - ((5 / 17) : ℂ) * ζ ^ 24
          + ((5 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry00_08 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (0 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((20 / 17) : ℂ)
          + ((20 / 17) : ℂ) * ζ ^ 4
          - ((6 / 17) : ℂ) * ζ ^ 5
          - ((20 / 17) : ℂ) * ζ ^ 8
          + ((6 / 17) : ℂ) * ζ ^ 9
          - ((6 / 17) : ℂ) * ζ ^ 13
          - ((10 / 17) : ℂ) * ζ ^ 15
          + ((10 / 17) : ℂ) * ζ ^ 19
          - ((20 / 17) : ℂ) * ζ ^ 20
          - ((10 / 17) : ℂ) * ζ ^ 23
          + ((20 / 17) : ℂ) * ζ ^ 24
          - ((20 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((20 / 17) : ℂ)
          + ((20 / 17) : ℂ) * ζ ^ 4
          - ((6 / 17) : ℂ) * ζ ^ 5
          - ((20 / 17) : ℂ) * ζ ^ 8
          + ((6 / 17) : ℂ) * ζ ^ 9
          - ((6 / 17) : ℂ) * ζ ^ 13
          - ((10 / 17) : ℂ) * ζ ^ 15
          + ((10 / 17) : ℂ) * ζ ^ 19
          - ((20 / 17) : ℂ) * ζ ^ 20
          - ((10 / 17) : ℂ) * ζ ^ 23
          + ((20 / 17) : ℂ) * ζ ^ 24
          - ((20 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry00_09 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (0 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
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
          + ((1 / 2) : ℂ) * ζ ^ 13
          + ((1 / 2) : ℂ) * ζ ^ 15
          - ((1 / 2) : ℂ) * ζ ^ 19
          + ((1 / 2) : ℂ) * ζ ^ 20
          + ((1 / 2) : ℂ) * ζ ^ 23
          - ((1 / 2) : ℂ) * ζ ^ 24
          + ((1 / 2) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 2) : ℂ)
          - ((1 / 2) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 5
          + ((1 / 2) : ℂ) * ζ ^ 8
          - ((1 / 2) : ℂ) * ζ ^ 9
          + ((1 / 2) : ℂ) * ζ ^ 13
          + ((1 / 2) : ℂ) * ζ ^ 15
          - ((1 / 2) : ℂ) * ζ ^ 19
          + ((1 / 2) : ℂ) * ζ ^ 20
          + ((1 / 2) : ℂ) * ζ ^ 23
          - ((1 / 2) : ℂ) * ζ ^ 24
          + ((1 / 2) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry01_00 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (1 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((29 / 34) : ℂ)
          - ((29 / 34) : ℂ) * ζ ^ 4
          + ((47 / 34) : ℂ) * ζ ^ 5
          + ((29 / 34) : ℂ) * ζ ^ 8
          - ((47 / 34) : ℂ) * ζ ^ 9
          - ((11 / 17) : ℂ) * ζ ^ 10
          + ((47 / 34) : ℂ) * ζ ^ 13
          + ((11 / 17) : ℂ) * ζ ^ 14
          - ((19 / 34) : ℂ) * ζ ^ 15
          - ((11 / 17) : ℂ) * ζ ^ 18
          + ((19 / 34) : ℂ) * ζ ^ 19
          - ((1 / 34) : ℂ) * ζ ^ 20
          - ((19 / 34) : ℂ) * ζ ^ 23
          + ((1 / 34) : ℂ) * ζ ^ 24
          - ((1 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((29 / 34) : ℂ)
          - ((29 / 34) : ℂ) * ζ ^ 4
          + ((47 / 34) : ℂ) * ζ ^ 5
          + ((29 / 34) : ℂ) * ζ ^ 8
          - ((47 / 34) : ℂ) * ζ ^ 9
          - ((11 / 17) : ℂ) * ζ ^ 10
          + ((47 / 34) : ℂ) * ζ ^ 13
          + ((11 / 17) : ℂ) * ζ ^ 14
          - ((19 / 34) : ℂ) * ζ ^ 15
          - ((11 / 17) : ℂ) * ζ ^ 18
          + ((19 / 34) : ℂ) * ζ ^ 19
          - ((1 / 34) : ℂ) * ζ ^ 20
          - ((19 / 34) : ℂ) * ζ ^ 23
          + ((1 / 34) : ℂ) * ζ ^ 24
          - ((1 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry01_01 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (1 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((39 / 34) : ℂ)
          + ((39 / 34) : ℂ) * ζ ^ 4
          + ((5 / 17) : ℂ) * ζ ^ 5
          - ((39 / 34) : ℂ) * ζ ^ 8
          - ((5 / 17) : ℂ) * ζ ^ 9
          - ((11 / 34) : ℂ) * ζ ^ 10
          + ((5 / 17) : ℂ) * ζ ^ 13
          + ((11 / 34) : ℂ) * ζ ^ 14
          - ((18 / 17) : ℂ) * ζ ^ 15
          - ((11 / 34) : ℂ) * ζ ^ 18
          + ((18 / 17) : ℂ) * ζ ^ 19
          - ((11 / 34) : ℂ) * ζ ^ 20
          - ((18 / 17) : ℂ) * ζ ^ 23
          + ((11 / 34) : ℂ) * ζ ^ 24
          - ((11 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((39 / 34) : ℂ)
          + ((39 / 34) : ℂ) * ζ ^ 4
          + ((5 / 17) : ℂ) * ζ ^ 5
          - ((39 / 34) : ℂ) * ζ ^ 8
          - ((5 / 17) : ℂ) * ζ ^ 9
          - ((11 / 34) : ℂ) * ζ ^ 10
          + ((5 / 17) : ℂ) * ζ ^ 13
          + ((11 / 34) : ℂ) * ζ ^ 14
          - ((18 / 17) : ℂ) * ζ ^ 15
          - ((11 / 34) : ℂ) * ζ ^ 18
          + ((18 / 17) : ℂ) * ζ ^ 19
          - ((11 / 34) : ℂ) * ζ ^ 20
          - ((18 / 17) : ℂ) * ζ ^ 23
          + ((11 / 34) : ℂ) * ζ ^ 24
          - ((11 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry01_02 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (1 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((19 / 17) : ℂ)
          + ((19 / 17) : ℂ) * ζ ^ 4
          - ((22 / 17) : ℂ) * ζ ^ 5
          - ((19 / 17) : ℂ) * ζ ^ 8
          + ((22 / 17) : ℂ) * ζ ^ 9
          - ((19 / 17) : ℂ) * ζ ^ 10
          - ((22 / 17) : ℂ) * ζ ^ 13
          + ((19 / 17) : ℂ) * ζ ^ 14
          - ((63 / 34) : ℂ) * ζ ^ 15
          - ((19 / 17) : ℂ) * ζ ^ 18
          + ((63 / 34) : ℂ) * ζ ^ 19
          - ((25 / 34) : ℂ) * ζ ^ 20
          - ((63 / 34) : ℂ) * ζ ^ 23
          + ((25 / 34) : ℂ) * ζ ^ 24
          - ((25 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((19 / 17) : ℂ)
          + ((19 / 17) : ℂ) * ζ ^ 4
          - ((22 / 17) : ℂ) * ζ ^ 5
          - ((19 / 17) : ℂ) * ζ ^ 8
          + ((22 / 17) : ℂ) * ζ ^ 9
          - ((19 / 17) : ℂ) * ζ ^ 10
          - ((22 / 17) : ℂ) * ζ ^ 13
          + ((19 / 17) : ℂ) * ζ ^ 14
          - ((63 / 34) : ℂ) * ζ ^ 15
          - ((19 / 17) : ℂ) * ζ ^ 18
          + ((63 / 34) : ℂ) * ζ ^ 19
          - ((25 / 34) : ℂ) * ζ ^ 20
          - ((63 / 34) : ℂ) * ζ ^ 23
          + ((25 / 34) : ℂ) * ζ ^ 24
          - ((25 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry01_03 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (1 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((20 / 17) : ℂ)
          + ((20 / 17) : ℂ) * ζ ^ 4
          - ((6 / 17) : ℂ) * ζ ^ 5
          - ((20 / 17) : ℂ) * ζ ^ 8
          + ((6 / 17) : ℂ) * ζ ^ 9
          + ζ ^ 10
          - ((6 / 17) : ℂ) * ζ ^ 13
          - ζ ^ 14
          + ((20 / 17) : ℂ) * ζ ^ 15
          + ζ ^ 18
          - ((20 / 17) : ℂ) * ζ ^ 19
          + ((6 / 17) : ℂ) * ζ ^ 20
          + ((20 / 17) : ℂ) * ζ ^ 23
          - ((6 / 17) : ℂ) * ζ ^ 24
          + ((6 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((20 / 17) : ℂ)
          + ((20 / 17) : ℂ) * ζ ^ 4
          - ((6 / 17) : ℂ) * ζ ^ 5
          - ((20 / 17) : ℂ) * ζ ^ 8
          + ((6 / 17) : ℂ) * ζ ^ 9
          + ζ ^ 10
          - ((6 / 17) : ℂ) * ζ ^ 13
          - ζ ^ 14
          + ((20 / 17) : ℂ) * ζ ^ 15
          + ζ ^ 18
          - ((20 / 17) : ℂ) * ζ ^ 19
          + ((6 / 17) : ℂ) * ζ ^ 20
          + ((20 / 17) : ℂ) * ζ ^ 23
          - ((6 / 17) : ℂ) * ζ ^ 24
          + ((6 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry01_04 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (1 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 17) : ℂ)
          + ((7 / 17) : ℂ) * ζ ^ 4
          + ((29 / 34) : ℂ) * ζ ^ 5
          - ((7 / 17) : ℂ) * ζ ^ 8
          - ((29 / 34) : ℂ) * ζ ^ 9
          + ((29 / 34) : ℂ) * ζ ^ 10
          + ((29 / 34) : ℂ) * ζ ^ 13
          - ((29 / 34) : ℂ) * ζ ^ 14
          + ((95 / 34) : ℂ) * ζ ^ 15
          + ((29 / 34) : ℂ) * ζ ^ 18
          - ((95 / 34) : ℂ) * ζ ^ 19
          + ((3 / 17) : ℂ) * ζ ^ 20
          + ((95 / 34) : ℂ) * ζ ^ 23
          - ((3 / 17) : ℂ) * ζ ^ 24
          + ((3 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 17) : ℂ)
          + ((7 / 17) : ℂ) * ζ ^ 4
          + ((29 / 34) : ℂ) * ζ ^ 5
          - ((7 / 17) : ℂ) * ζ ^ 8
          - ((29 / 34) : ℂ) * ζ ^ 9
          + ((29 / 34) : ℂ) * ζ ^ 10
          + ((29 / 34) : ℂ) * ζ ^ 13
          - ((29 / 34) : ℂ) * ζ ^ 14
          + ((95 / 34) : ℂ) * ζ ^ 15
          + ((29 / 34) : ℂ) * ζ ^ 18
          - ((95 / 34) : ℂ) * ζ ^ 19
          + ((3 / 17) : ℂ) * ζ ^ 20
          + ((95 / 34) : ℂ) * ζ ^ 23
          - ((3 / 17) : ℂ) * ζ ^ 24
          + ((3 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry01_05 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (1 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((2 / 17) : ℂ)
          + ((2 / 17) : ℂ) * ζ ^ 4
          - ((15 / 34) : ℂ) * ζ ^ 5
          - ((2 / 17) : ℂ) * ζ ^ 8
          + ((15 / 34) : ℂ) * ζ ^ 9
          - ((31 / 34) : ℂ) * ζ ^ 10
          - ((15 / 34) : ℂ) * ζ ^ 13
          + ((31 / 34) : ℂ) * ζ ^ 14
          - ((26 / 17) : ℂ) * ζ ^ 15
          - ((31 / 34) : ℂ) * ζ ^ 18
          + ((26 / 17) : ℂ) * ζ ^ 19
          - ((31 / 34) : ℂ) * ζ ^ 20
          - ((26 / 17) : ℂ) * ζ ^ 23
          + ((31 / 34) : ℂ) * ζ ^ 24
          - ((31 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((2 / 17) : ℂ)
          + ((2 / 17) : ℂ) * ζ ^ 4
          - ((15 / 34) : ℂ) * ζ ^ 5
          - ((2 / 17) : ℂ) * ζ ^ 8
          + ((15 / 34) : ℂ) * ζ ^ 9
          - ((31 / 34) : ℂ) * ζ ^ 10
          - ((15 / 34) : ℂ) * ζ ^ 13
          + ((31 / 34) : ℂ) * ζ ^ 14
          - ((26 / 17) : ℂ) * ζ ^ 15
          - ((31 / 34) : ℂ) * ζ ^ 18
          + ((26 / 17) : ℂ) * ζ ^ 19
          - ((31 / 34) : ℂ) * ζ ^ 20
          - ((26 / 17) : ℂ) * ζ ^ 23
          + ((31 / 34) : ℂ) * ζ ^ 24
          - ((31 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry01_06 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (1 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((21 / 17) : ℂ)
          + ((21 / 17) : ℂ) * ζ ^ 4
          - ((13 / 17) : ℂ) * ζ ^ 5
          - ((21 / 17) : ℂ) * ζ ^ 8
          + ((13 / 17) : ℂ) * ζ ^ 9
          + ((7 / 17) : ℂ) * ζ ^ 10
          - ((13 / 17) : ℂ) * ζ ^ 13
          - ((7 / 17) : ℂ) * ζ ^ 14
          + ((15 / 34) : ℂ) * ζ ^ 15
          + ((7 / 17) : ℂ) * ζ ^ 18
          - ((15 / 34) : ℂ) * ζ ^ 19
          - ((9 / 34) : ℂ) * ζ ^ 20
          + ((15 / 34) : ℂ) * ζ ^ 23
          + ((9 / 34) : ℂ) * ζ ^ 24
          - ((9 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((21 / 17) : ℂ)
          + ((21 / 17) : ℂ) * ζ ^ 4
          - ((13 / 17) : ℂ) * ζ ^ 5
          - ((21 / 17) : ℂ) * ζ ^ 8
          + ((13 / 17) : ℂ) * ζ ^ 9
          + ((7 / 17) : ℂ) * ζ ^ 10
          - ((13 / 17) : ℂ) * ζ ^ 13
          - ((7 / 17) : ℂ) * ζ ^ 14
          + ((15 / 34) : ℂ) * ζ ^ 15
          + ((7 / 17) : ℂ) * ζ ^ 18
          - ((15 / 34) : ℂ) * ζ ^ 19
          - ((9 / 34) : ℂ) * ζ ^ 20
          + ((15 / 34) : ℂ) * ζ ^ 23
          + ((9 / 34) : ℂ) * ζ ^ 24
          - ((9 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry01_07 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (1 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((67 / 34) : ℂ)
          - ((67 / 34) : ℂ) * ζ ^ 4
          + ((13 / 34) : ℂ) * ζ ^ 5
          + ((67 / 34) : ℂ) * ζ ^ 8
          - ((13 / 34) : ℂ) * ζ ^ 9
          - ((2 / 17) : ℂ) * ζ ^ 10
          + ((13 / 34) : ℂ) * ζ ^ 13
          + ((2 / 17) : ℂ) * ζ ^ 14
          - ((7 / 34) : ℂ) * ζ ^ 15
          - ((2 / 17) : ℂ) * ζ ^ 18
          + ((7 / 34) : ℂ) * ζ ^ 19
          + ((19 / 34) : ℂ) * ζ ^ 20
          - ((7 / 34) : ℂ) * ζ ^ 23
          - ((19 / 34) : ℂ) * ζ ^ 24
          + ((19 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((67 / 34) : ℂ)
          - ((67 / 34) : ℂ) * ζ ^ 4
          + ((13 / 34) : ℂ) * ζ ^ 5
          + ((67 / 34) : ℂ) * ζ ^ 8
          - ((13 / 34) : ℂ) * ζ ^ 9
          - ((2 / 17) : ℂ) * ζ ^ 10
          + ((13 / 34) : ℂ) * ζ ^ 13
          + ((2 / 17) : ℂ) * ζ ^ 14
          - ((7 / 34) : ℂ) * ζ ^ 15
          - ((2 / 17) : ℂ) * ζ ^ 18
          + ((7 / 34) : ℂ) * ζ ^ 19
          + ((19 / 34) : ℂ) * ζ ^ 20
          - ((7 / 34) : ℂ) * ζ ^ 23
          - ((19 / 34) : ℂ) * ζ ^ 24
          + ((19 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry01_08 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (1 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((18 / 17) : ℂ)
          + ((18 / 17) : ℂ) * ζ ^ 4
          + ((11 / 17) : ℂ) * ζ ^ 5
          - ((18 / 17) : ℂ) * ζ ^ 8
          - ((11 / 17) : ℂ) * ζ ^ 9
          - ((8 / 17) : ℂ) * ζ ^ 10
          + ((11 / 17) : ℂ) * ζ ^ 13
          + ((8 / 17) : ℂ) * ζ ^ 14
          + ((26 / 17) : ℂ) * ζ ^ 15
          - ((8 / 17) : ℂ) * ζ ^ 18
          - ((26 / 17) : ℂ) * ζ ^ 19
          - ((1 / 17) : ℂ) * ζ ^ 20
          + ((26 / 17) : ℂ) * ζ ^ 23
          + ((1 / 17) : ℂ) * ζ ^ 24
          - ((1 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((18 / 17) : ℂ)
          + ((18 / 17) : ℂ) * ζ ^ 4
          + ((11 / 17) : ℂ) * ζ ^ 5
          - ((18 / 17) : ℂ) * ζ ^ 8
          - ((11 / 17) : ℂ) * ζ ^ 9
          - ((8 / 17) : ℂ) * ζ ^ 10
          + ((11 / 17) : ℂ) * ζ ^ 13
          + ((8 / 17) : ℂ) * ζ ^ 14
          + ((26 / 17) : ℂ) * ζ ^ 15
          - ((8 / 17) : ℂ) * ζ ^ 18
          - ((26 / 17) : ℂ) * ζ ^ 19
          - ((1 / 17) : ℂ) * ζ ^ 20
          + ((26 / 17) : ℂ) * ζ ^ 23
          + ((1 / 17) : ℂ) * ζ ^ 24
          - ((1 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry01_09 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (1 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 34) : ℂ)
          + ((7 / 34) : ℂ) * ζ ^ 4
          - ((35 / 34) : ℂ) * ζ ^ 5
          - ((7 / 34) : ℂ) * ζ ^ 8
          + ((35 / 34) : ℂ) * ζ ^ 9
          - ((4 / 17) : ℂ) * ζ ^ 10
          - ((35 / 34) : ℂ) * ζ ^ 13
          + ((4 / 17) : ℂ) * ζ ^ 14
          - ((23 / 17) : ℂ) * ζ ^ 15
          - ((4 / 17) : ℂ) * ζ ^ 18
          + ((23 / 17) : ℂ) * ζ ^ 19
          - ((13 / 17) : ℂ) * ζ ^ 20
          - ((23 / 17) : ℂ) * ζ ^ 23
          + ((13 / 17) : ℂ) * ζ ^ 24
          - ((13 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 34) : ℂ)
          + ((7 / 34) : ℂ) * ζ ^ 4
          - ((35 / 34) : ℂ) * ζ ^ 5
          - ((7 / 34) : ℂ) * ζ ^ 8
          + ((35 / 34) : ℂ) * ζ ^ 9
          - ((4 / 17) : ℂ) * ζ ^ 10
          - ((35 / 34) : ℂ) * ζ ^ 13
          + ((4 / 17) : ℂ) * ζ ^ 14
          - ((23 / 17) : ℂ) * ζ ^ 15
          - ((4 / 17) : ℂ) * ζ ^ 18
          + ((23 / 17) : ℂ) * ζ ^ 19
          - ((13 / 17) : ℂ) * ζ ^ 20
          - ((23 / 17) : ℂ) * ζ ^ 23
          + ((13 / 17) : ℂ) * ζ ^ 24
          - ((13 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry02_00 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (2 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((27 / 34) : ℂ)
          + ((27 / 34) : ℂ) * ζ ^ 4
          - ((83 / 34) : ℂ) * ζ ^ 5
          - ((27 / 34) : ℂ) * ζ ^ 8
          + ((83 / 34) : ℂ) * ζ ^ 9
          - ((29 / 17) : ℂ) * ζ ^ 10
          - ((83 / 34) : ℂ) * ζ ^ 13
          + ((29 / 17) : ℂ) * ζ ^ 14
          - ((21 / 17) : ℂ) * ζ ^ 15
          - ((29 / 17) : ℂ) * ζ ^ 18
          + ((21 / 17) : ℂ) * ζ ^ 19
          - ((62 / 17) : ℂ) * ζ ^ 20
          - ((21 / 17) : ℂ) * ζ ^ 23
          + ((62 / 17) : ℂ) * ζ ^ 24
          - ((62 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((27 / 34) : ℂ)
          + ((27 / 34) : ℂ) * ζ ^ 4
          - ((83 / 34) : ℂ) * ζ ^ 5
          - ((27 / 34) : ℂ) * ζ ^ 8
          + ((83 / 34) : ℂ) * ζ ^ 9
          - ((29 / 17) : ℂ) * ζ ^ 10
          - ((83 / 34) : ℂ) * ζ ^ 13
          + ((29 / 17) : ℂ) * ζ ^ 14
          - ((21 / 17) : ℂ) * ζ ^ 15
          - ((29 / 17) : ℂ) * ζ ^ 18
          + ((21 / 17) : ℂ) * ζ ^ 19
          - ((62 / 17) : ℂ) * ζ ^ 20
          - ((21 / 17) : ℂ) * ζ ^ 23
          + ((62 / 17) : ℂ) * ζ ^ 24
          - ((62 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry02_01 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (2 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 17) : ℂ)
          - ((2 / 17) : ℂ) * ζ ^ 4
          - ((9 / 17) : ℂ) * ζ ^ 5
          + ((2 / 17) : ℂ) * ζ ^ 8
          + ((9 / 17) : ℂ) * ζ ^ 9
          + ((8 / 17) : ℂ) * ζ ^ 10
          - ((9 / 17) : ℂ) * ζ ^ 13
          - ((8 / 17) : ℂ) * ζ ^ 14
          + ((53 / 17) : ℂ) * ζ ^ 15
          + ((8 / 17) : ℂ) * ζ ^ 18
          - ((53 / 17) : ℂ) * ζ ^ 19
          + ((40 / 17) : ℂ) * ζ ^ 20
          + ((53 / 17) : ℂ) * ζ ^ 23
          - ((40 / 17) : ℂ) * ζ ^ 24
          + ((40 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 17) : ℂ)
          - ((2 / 17) : ℂ) * ζ ^ 4
          - ((9 / 17) : ℂ) * ζ ^ 5
          + ((2 / 17) : ℂ) * ζ ^ 8
          + ((9 / 17) : ℂ) * ζ ^ 9
          + ((8 / 17) : ℂ) * ζ ^ 10
          - ((9 / 17) : ℂ) * ζ ^ 13
          - ((8 / 17) : ℂ) * ζ ^ 14
          + ((53 / 17) : ℂ) * ζ ^ 15
          + ((8 / 17) : ℂ) * ζ ^ 18
          - ((53 / 17) : ℂ) * ζ ^ 19
          + ((40 / 17) : ℂ) * ζ ^ 20
          + ((53 / 17) : ℂ) * ζ ^ 23
          - ((40 / 17) : ℂ) * ζ ^ 24
          + ((40 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry02_02 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (2 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((38 / 17) : ℂ)
          + ((38 / 17) : ℂ) * ζ ^ 4
          - ((40 / 17) : ℂ) * ζ ^ 5
          - ((38 / 17) : ℂ) * ζ ^ 8
          + ((40 / 17) : ℂ) * ζ ^ 9
          - ((13 / 17) : ℂ) * ζ ^ 10
          - ((40 / 17) : ℂ) * ζ ^ 13
          + ((13 / 17) : ℂ) * ζ ^ 14
          - ((30 / 17) : ℂ) * ζ ^ 15
          - ((13 / 17) : ℂ) * ζ ^ 18
          + ((30 / 17) : ℂ) * ζ ^ 19
          + ((26 / 17) : ℂ) * ζ ^ 20
          - ((30 / 17) : ℂ) * ζ ^ 23
          - ((26 / 17) : ℂ) * ζ ^ 24
          + ((26 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((38 / 17) : ℂ)
          + ((38 / 17) : ℂ) * ζ ^ 4
          - ((40 / 17) : ℂ) * ζ ^ 5
          - ((38 / 17) : ℂ) * ζ ^ 8
          + ((40 / 17) : ℂ) * ζ ^ 9
          - ((13 / 17) : ℂ) * ζ ^ 10
          - ((40 / 17) : ℂ) * ζ ^ 13
          + ((13 / 17) : ℂ) * ζ ^ 14
          - ((30 / 17) : ℂ) * ζ ^ 15
          - ((13 / 17) : ℂ) * ζ ^ 18
          + ((30 / 17) : ℂ) * ζ ^ 19
          + ((26 / 17) : ℂ) * ζ ^ 20
          - ((30 / 17) : ℂ) * ζ ^ 23
          - ((26 / 17) : ℂ) * ζ ^ 24
          + ((26 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry02_03 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (2 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((31 / 34) : ℂ)
          - ((31 / 34) : ℂ) * ζ ^ 4
          + ((15 / 34) : ℂ) * ζ ^ 5
          + ((31 / 34) : ℂ) * ζ ^ 8
          - ((15 / 34) : ℂ) * ζ ^ 9
          + ((21 / 17) : ℂ) * ζ ^ 10
          + ((15 / 34) : ℂ) * ζ ^ 13
          - ((21 / 17) : ℂ) * ζ ^ 14
          - ((9 / 17) : ℂ) * ζ ^ 15
          + ((21 / 17) : ℂ) * ζ ^ 18
          + ((9 / 17) : ℂ) * ζ ^ 19
          + (3 : ℂ) * ζ ^ 20
          - ((9 / 17) : ℂ) * ζ ^ 23
          - (3 : ℂ) * ζ ^ 24
          + (3 : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((31 / 34) : ℂ)
          - ((31 / 34) : ℂ) * ζ ^ 4
          + ((15 / 34) : ℂ) * ζ ^ 5
          + ((31 / 34) : ℂ) * ζ ^ 8
          - ((15 / 34) : ℂ) * ζ ^ 9
          + ((21 / 17) : ℂ) * ζ ^ 10
          + ((15 / 34) : ℂ) * ζ ^ 13
          - ((21 / 17) : ℂ) * ζ ^ 14
          - ((9 / 17) : ℂ) * ζ ^ 15
          + ((21 / 17) : ℂ) * ζ ^ 18
          + ((9 / 17) : ℂ) * ζ ^ 19
          + (3 : ℂ) * ζ ^ 20
          - ((9 / 17) : ℂ) * ζ ^ 23
          - (3 : ℂ) * ζ ^ 24
          + (3 : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry02_04 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (2 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((9 / 17) : ℂ)
          - ((9 / 17) : ℂ) * ζ ^ 4
          + ((9 / 17) : ℂ) * ζ ^ 8
          + ((32 / 17) : ℂ) * ζ ^ 10
          - ((32 / 17) : ℂ) * ζ ^ 14
          + ((5 / 17) : ℂ) * ζ ^ 15
          + ((32 / 17) : ℂ) * ζ ^ 18
          - ((5 / 17) : ℂ) * ζ ^ 19
          + ((35 / 17) : ℂ) * ζ ^ 20
          + ((5 / 17) : ℂ) * ζ ^ 23
          - ((35 / 17) : ℂ) * ζ ^ 24
          + ((35 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((9 / 17) : ℂ)
          - ((9 / 17) : ℂ) * ζ ^ 4
          + ((9 / 17) : ℂ) * ζ ^ 8
          + ((32 / 17) : ℂ) * ζ ^ 10
          - ((32 / 17) : ℂ) * ζ ^ 14
          + ((5 / 17) : ℂ) * ζ ^ 15
          + ((32 / 17) : ℂ) * ζ ^ 18
          - ((5 / 17) : ℂ) * ζ ^ 19
          + ((35 / 17) : ℂ) * ζ ^ 20
          + ((5 / 17) : ℂ) * ζ ^ 23
          - ((35 / 17) : ℂ) * ζ ^ 24
          + ((35 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry02_05 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (2 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((5 / 34) : ℂ)
          - ((5 / 34) : ℂ) * ζ ^ 4
          + ((5 / 34) : ℂ) * ζ ^ 5
          + ((5 / 34) : ℂ) * ζ ^ 8
          - ((5 / 34) : ℂ) * ζ ^ 9
          + ((12 / 17) : ℂ) * ζ ^ 10
          + ((5 / 34) : ℂ) * ζ ^ 13
          - ((12 / 17) : ℂ) * ζ ^ 14
          + ((41 / 17) : ℂ) * ζ ^ 15
          + ((12 / 17) : ℂ) * ζ ^ 18
          - ((41 / 17) : ℂ) * ζ ^ 19
          + ((41 / 17) : ℂ) * ζ ^ 23
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((5 / 34) : ℂ)
          - ((5 / 34) : ℂ) * ζ ^ 4
          + ((5 / 34) : ℂ) * ζ ^ 5
          + ((5 / 34) : ℂ) * ζ ^ 8
          - ((5 / 34) : ℂ) * ζ ^ 9
          + ((12 / 17) : ℂ) * ζ ^ 10
          + ((5 / 34) : ℂ) * ζ ^ 13
          - ((12 / 17) : ℂ) * ζ ^ 14
          + ((41 / 17) : ℂ) * ζ ^ 15
          + ((12 / 17) : ℂ) * ζ ^ 18
          - ((41 / 17) : ℂ) * ζ ^ 19
          + ((41 / 17) : ℂ) * ζ ^ 23
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry02_06 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (2 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((8 / 17) : ℂ)
          + ((8 / 17) : ℂ) * ζ ^ 4
          + ζ ^ 5
          - ((8 / 17) : ℂ) * ζ ^ 8
          - ζ ^ 9
          + ((66 / 17) : ℂ) * ζ ^ 10
          + ζ ^ 13
          - ((66 / 17) : ℂ) * ζ ^ 14
          + ((66 / 17) : ℂ) * ζ ^ 15
          + ((66 / 17) : ℂ) * ζ ^ 18
          - ((66 / 17) : ℂ) * ζ ^ 19
          + ((55 / 17) : ℂ) * ζ ^ 20
          + ((66 / 17) : ℂ) * ζ ^ 23
          - ((55 / 17) : ℂ) * ζ ^ 24
          + ((55 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((8 / 17) : ℂ)
          + ((8 / 17) : ℂ) * ζ ^ 4
          + ζ ^ 5
          - ((8 / 17) : ℂ) * ζ ^ 8
          - ζ ^ 9
          + ((66 / 17) : ℂ) * ζ ^ 10
          + ζ ^ 13
          - ((66 / 17) : ℂ) * ζ ^ 14
          + ((66 / 17) : ℂ) * ζ ^ 15
          + ((66 / 17) : ℂ) * ζ ^ 18
          - ((66 / 17) : ℂ) * ζ ^ 19
          + ((55 / 17) : ℂ) * ζ ^ 20
          + ((66 / 17) : ℂ) * ζ ^ 23
          - ((55 / 17) : ℂ) * ζ ^ 24
          + ((55 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry02_07 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (2 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((6 / 17) : ℂ)
          - ((6 / 17) : ℂ) * ζ ^ 4
          + ((11 / 17) : ℂ) * ζ ^ 5
          + ((6 / 17) : ℂ) * ζ ^ 8
          - ((11 / 17) : ℂ) * ζ ^ 9
          - ((2 / 17) : ℂ) * ζ ^ 10
          + ((11 / 17) : ℂ) * ζ ^ 13
          + ((2 / 17) : ℂ) * ζ ^ 14
          - ((2 / 17) : ℂ) * ζ ^ 15
          - ((2 / 17) : ℂ) * ζ ^ 18
          + ((2 / 17) : ℂ) * ζ ^ 19
          - ((30 / 17) : ℂ) * ζ ^ 20
          - ((2 / 17) : ℂ) * ζ ^ 23
          + ((30 / 17) : ℂ) * ζ ^ 24
          - ((30 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((6 / 17) : ℂ)
          - ((6 / 17) : ℂ) * ζ ^ 4
          + ((11 / 17) : ℂ) * ζ ^ 5
          + ((6 / 17) : ℂ) * ζ ^ 8
          - ((11 / 17) : ℂ) * ζ ^ 9
          - ((2 / 17) : ℂ) * ζ ^ 10
          + ((11 / 17) : ℂ) * ζ ^ 13
          + ((2 / 17) : ℂ) * ζ ^ 14
          - ((2 / 17) : ℂ) * ζ ^ 15
          - ((2 / 17) : ℂ) * ζ ^ 18
          + ((2 / 17) : ℂ) * ζ ^ 19
          - ((30 / 17) : ℂ) * ζ ^ 20
          - ((2 / 17) : ℂ) * ζ ^ 23
          + ((30 / 17) : ℂ) * ζ ^ 24
          - ((30 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry02_08 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (2 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((5 / 17) : ℂ)
          - ((5 / 17) : ℂ) * ζ ^ 4
          + ((12 / 17) : ℂ) * ζ ^ 5
          + ((5 / 17) : ℂ) * ζ ^ 8
          - ((12 / 17) : ℂ) * ζ ^ 9
          + ((38 / 17) : ℂ) * ζ ^ 10
          + ((12 / 17) : ℂ) * ζ ^ 13
          - ((38 / 17) : ℂ) * ζ ^ 14
          + ((45 / 17) : ℂ) * ζ ^ 15
          + ((38 / 17) : ℂ) * ζ ^ 18
          - ((45 / 17) : ℂ) * ζ ^ 19
          + ((23 / 17) : ℂ) * ζ ^ 20
          + ((45 / 17) : ℂ) * ζ ^ 23
          - ((23 / 17) : ℂ) * ζ ^ 24
          + ((23 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((5 / 17) : ℂ)
          - ((5 / 17) : ℂ) * ζ ^ 4
          + ((12 / 17) : ℂ) * ζ ^ 5
          + ((5 / 17) : ℂ) * ζ ^ 8
          - ((12 / 17) : ℂ) * ζ ^ 9
          + ((38 / 17) : ℂ) * ζ ^ 10
          + ((12 / 17) : ℂ) * ζ ^ 13
          - ((38 / 17) : ℂ) * ζ ^ 14
          + ((45 / 17) : ℂ) * ζ ^ 15
          + ((38 / 17) : ℂ) * ζ ^ 18
          - ((45 / 17) : ℂ) * ζ ^ 19
          + ((23 / 17) : ℂ) * ζ ^ 20
          + ((45 / 17) : ℂ) * ζ ^ 23
          - ((23 / 17) : ℂ) * ζ ^ 24
          + ((23 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry02_09 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (2 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((11 / 34) : ℂ)
          - ((11 / 34) : ℂ) * ζ ^ 4
          - ((115 / 34) : ℂ) * ζ ^ 5
          + ((11 / 34) : ℂ) * ζ ^ 8
          + ((115 / 34) : ℂ) * ζ ^ 9
          - ((18 / 17) : ℂ) * ζ ^ 10
          - ((115 / 34) : ℂ) * ζ ^ 13
          + ((18 / 17) : ℂ) * ζ ^ 14
          - ((10 / 17) : ℂ) * ζ ^ 15
          - ((18 / 17) : ℂ) * ζ ^ 18
          + ((10 / 17) : ℂ) * ζ ^ 19
          + ((1 / 17) : ℂ) * ζ ^ 20
          - ((10 / 17) : ℂ) * ζ ^ 23
          - ((1 / 17) : ℂ) * ζ ^ 24
          + ((1 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((11 / 34) : ℂ)
          - ((11 / 34) : ℂ) * ζ ^ 4
          - ((115 / 34) : ℂ) * ζ ^ 5
          + ((11 / 34) : ℂ) * ζ ^ 8
          + ((115 / 34) : ℂ) * ζ ^ 9
          - ((18 / 17) : ℂ) * ζ ^ 10
          - ((115 / 34) : ℂ) * ζ ^ 13
          + ((18 / 17) : ℂ) * ζ ^ 14
          - ((10 / 17) : ℂ) * ζ ^ 15
          - ((18 / 17) : ℂ) * ζ ^ 18
          + ((10 / 17) : ℂ) * ζ ^ 19
          + ((1 / 17) : ℂ) * ζ ^ 20
          - ((10 / 17) : ℂ) * ζ ^ 23
          - ((1 / 17) : ℂ) * ζ ^ 24
          + ((1 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry03_00 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (3 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((21 / 17) : ℂ)
          - ((21 / 17) : ℂ) * ζ ^ 4
          + ((42 / 17) : ℂ) * ζ ^ 5
          + ((21 / 17) : ℂ) * ζ ^ 8
          - ((42 / 17) : ℂ) * ζ ^ 9
          + ζ ^ 10
          + ((42 / 17) : ℂ) * ζ ^ 13
          - ζ ^ 14
          + ((35 / 34) : ℂ) * ζ ^ 15
          + ζ ^ 18
          - ((35 / 34) : ℂ) * ζ ^ 19
          + ((87 / 34) : ℂ) * ζ ^ 20
          + ((35 / 34) : ℂ) * ζ ^ 23
          - ((87 / 34) : ℂ) * ζ ^ 24
          + ((87 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((21 / 17) : ℂ)
          - ((21 / 17) : ℂ) * ζ ^ 4
          + ((42 / 17) : ℂ) * ζ ^ 5
          + ((21 / 17) : ℂ) * ζ ^ 8
          - ((42 / 17) : ℂ) * ζ ^ 9
          + ζ ^ 10
          + ((42 / 17) : ℂ) * ζ ^ 13
          - ζ ^ 14
          + ((35 / 34) : ℂ) * ζ ^ 15
          + ζ ^ 18
          - ((35 / 34) : ℂ) * ζ ^ 19
          + ((87 / 34) : ℂ) * ζ ^ 20
          + ((35 / 34) : ℂ) * ζ ^ 23
          - ((87 / 34) : ℂ) * ζ ^ 24
          + ((87 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry03_01 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (3 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((61 / 34) : ℂ)
          + ((61 / 34) : ℂ) * ζ ^ 4
          - ((11 / 17) : ℂ) * ζ ^ 5
          - ((61 / 34) : ℂ) * ζ ^ 8
          + ((11 / 17) : ℂ) * ζ ^ 9
          - ((21 / 34) : ℂ) * ζ ^ 10
          - ((11 / 17) : ℂ) * ζ ^ 13
          + ((21 / 34) : ℂ) * ζ ^ 14
          - ((35 / 17) : ℂ) * ζ ^ 15
          - ((21 / 34) : ℂ) * ζ ^ 18
          + ((35 / 17) : ℂ) * ζ ^ 19
          - ((39 / 34) : ℂ) * ζ ^ 20
          - ((35 / 17) : ℂ) * ζ ^ 23
          + ((39 / 34) : ℂ) * ζ ^ 24
          - ((39 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((61 / 34) : ℂ)
          + ((61 / 34) : ℂ) * ζ ^ 4
          - ((11 / 17) : ℂ) * ζ ^ 5
          - ((61 / 34) : ℂ) * ζ ^ 8
          + ((11 / 17) : ℂ) * ζ ^ 9
          - ((21 / 34) : ℂ) * ζ ^ 10
          - ((11 / 17) : ℂ) * ζ ^ 13
          + ((21 / 34) : ℂ) * ζ ^ 14
          - ((35 / 17) : ℂ) * ζ ^ 15
          - ((21 / 34) : ℂ) * ζ ^ 18
          + ((35 / 17) : ℂ) * ζ ^ 19
          - ((39 / 34) : ℂ) * ζ ^ 20
          - ((35 / 17) : ℂ) * ζ ^ 23
          + ((39 / 34) : ℂ) * ζ ^ 24
          - ((39 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry03_02 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (3 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((10 / 17) : ℂ)
          - ((10 / 17) : ℂ) * ζ ^ 4
          + ((20 / 17) : ℂ) * ζ ^ 5
          + ((10 / 17) : ℂ) * ζ ^ 8
          - ((20 / 17) : ℂ) * ζ ^ 9
          + ((20 / 17) : ℂ) * ζ ^ 13
          + ((9 / 34) : ℂ) * ζ ^ 15
          - ((9 / 34) : ℂ) * ζ ^ 19
          - ((33 / 34) : ℂ) * ζ ^ 20
          + ((9 / 34) : ℂ) * ζ ^ 23
          + ((33 / 34) : ℂ) * ζ ^ 24
          - ((33 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((10 / 17) : ℂ)
          - ((10 / 17) : ℂ) * ζ ^ 4
          + ((20 / 17) : ℂ) * ζ ^ 5
          + ((10 / 17) : ℂ) * ζ ^ 8
          - ((20 / 17) : ℂ) * ζ ^ 9
          + ((20 / 17) : ℂ) * ζ ^ 13
          + ((9 / 34) : ℂ) * ζ ^ 15
          - ((9 / 34) : ℂ) * ζ ^ 19
          - ((33 / 34) : ℂ) * ζ ^ 20
          + ((9 / 34) : ℂ) * ζ ^ 23
          + ((33 / 34) : ℂ) * ζ ^ 24
          - ((33 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry03_03 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (3 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 34) : ℂ)
          + ((1 / 34) : ℂ) * ζ ^ 4
          - ((39 / 34) : ℂ) * ζ ^ 5
          - ((1 / 34) : ℂ) * ζ ^ 8
          + ((39 / 34) : ℂ) * ζ ^ 9
          - ((3 / 17) : ℂ) * ζ ^ 10
          - ((39 / 34) : ℂ) * ζ ^ 13
          + ((3 / 17) : ℂ) * ζ ^ 14
          + ((8 / 17) : ℂ) * ζ ^ 15
          - ((3 / 17) : ℂ) * ζ ^ 18
          - ((8 / 17) : ℂ) * ζ ^ 19
          - ((40 / 17) : ℂ) * ζ ^ 20
          + ((8 / 17) : ℂ) * ζ ^ 23
          + ((40 / 17) : ℂ) * ζ ^ 24
          - ((40 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 34) : ℂ)
          + ((1 / 34) : ℂ) * ζ ^ 4
          - ((39 / 34) : ℂ) * ζ ^ 5
          - ((1 / 34) : ℂ) * ζ ^ 8
          + ((39 / 34) : ℂ) * ζ ^ 9
          - ((3 / 17) : ℂ) * ζ ^ 10
          - ((39 / 34) : ℂ) * ζ ^ 13
          + ((3 / 17) : ℂ) * ζ ^ 14
          + ((8 / 17) : ℂ) * ζ ^ 15
          - ((3 / 17) : ℂ) * ζ ^ 18
          - ((8 / 17) : ℂ) * ζ ^ 19
          - ((40 / 17) : ℂ) * ζ ^ 20
          + ((8 / 17) : ℂ) * ζ ^ 23
          + ((40 / 17) : ℂ) * ζ ^ 24
          - ((40 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry03_04 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (3 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((20 / 17) : ℂ)
          - ((20 / 17) : ℂ) * ζ ^ 4
          - ((21 / 34) : ℂ) * ζ ^ 5
          + ((20 / 17) : ℂ) * ζ ^ 8
          + ((21 / 34) : ℂ) * ζ ^ 9
          - ((15 / 34) : ℂ) * ζ ^ 10
          - ((21 / 34) : ℂ) * ζ ^ 13
          + ((15 / 34) : ℂ) * ζ ^ 14
          - ((23 / 34) : ℂ) * ζ ^ 15
          - ((15 / 34) : ℂ) * ζ ^ 18
          + ((23 / 34) : ℂ) * ζ ^ 19
          - ((27 / 17) : ℂ) * ζ ^ 20
          - ((23 / 34) : ℂ) * ζ ^ 23
          + ((27 / 17) : ℂ) * ζ ^ 24
          - ((27 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((20 / 17) : ℂ)
          - ((20 / 17) : ℂ) * ζ ^ 4
          - ((21 / 34) : ℂ) * ζ ^ 5
          + ((20 / 17) : ℂ) * ζ ^ 8
          + ((21 / 34) : ℂ) * ζ ^ 9
          - ((15 / 34) : ℂ) * ζ ^ 10
          - ((21 / 34) : ℂ) * ζ ^ 13
          + ((15 / 34) : ℂ) * ζ ^ 14
          - ((23 / 34) : ℂ) * ζ ^ 15
          - ((15 / 34) : ℂ) * ζ ^ 18
          + ((23 / 34) : ℂ) * ζ ^ 19
          - ((27 / 17) : ℂ) * ζ ^ 20
          - ((23 / 34) : ℂ) * ζ ^ 23
          + ((27 / 17) : ℂ) * ζ ^ 24
          - ((27 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry03_05 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (3 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((55 / 34) : ℂ)
          + ((55 / 34) : ℂ) * ζ ^ 4
          - ((16 / 17) : ℂ) * ζ ^ 5
          - ((55 / 34) : ℂ) * ζ ^ 8
          + ((16 / 17) : ℂ) * ζ ^ 9
          - ((31 / 34) : ℂ) * ζ ^ 10
          - ((16 / 17) : ℂ) * ζ ^ 13
          + ((31 / 34) : ℂ) * ζ ^ 14
          - ((36 / 17) : ℂ) * ζ ^ 15
          - ((31 / 34) : ℂ) * ζ ^ 18
          + ((36 / 17) : ℂ) * ζ ^ 19
          + ((31 / 34) : ℂ) * ζ ^ 20
          - ((36 / 17) : ℂ) * ζ ^ 23
          - ((31 / 34) : ℂ) * ζ ^ 24
          + ((31 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((55 / 34) : ℂ)
          + ((55 / 34) : ℂ) * ζ ^ 4
          - ((16 / 17) : ℂ) * ζ ^ 5
          - ((55 / 34) : ℂ) * ζ ^ 8
          + ((16 / 17) : ℂ) * ζ ^ 9
          - ((31 / 34) : ℂ) * ζ ^ 10
          - ((16 / 17) : ℂ) * ζ ^ 13
          + ((31 / 34) : ℂ) * ζ ^ 14
          - ((36 / 17) : ℂ) * ζ ^ 15
          - ((31 / 34) : ℂ) * ζ ^ 18
          + ((36 / 17) : ℂ) * ζ ^ 19
          + ((31 / 34) : ℂ) * ζ ^ 20
          - ((36 / 17) : ℂ) * ζ ^ 23
          - ((31 / 34) : ℂ) * ζ ^ 24
          + ((31 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry03_06 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (3 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((31 / 17) : ℂ)
          + ((31 / 17) : ℂ) * ζ ^ 4
          - ((58 / 17) : ℂ) * ζ ^ 5
          - ((31 / 17) : ℂ) * ζ ^ 8
          + ((58 / 17) : ℂ) * ζ ^ 9
          - ((43 / 17) : ℂ) * ζ ^ 10
          - ((58 / 17) : ℂ) * ζ ^ 13
          + ((43 / 17) : ℂ) * ζ ^ 14
          - ((9 / 2) : ℂ) * ζ ^ 15
          - ((43 / 17) : ℂ) * ζ ^ 18
          + ((9 / 2) : ℂ) * ζ ^ 19
          - ((47 / 34) : ℂ) * ζ ^ 20
          - ((9 / 2) : ℂ) * ζ ^ 23
          + ((47 / 34) : ℂ) * ζ ^ 24
          - ((47 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((31 / 17) : ℂ)
          + ((31 / 17) : ℂ) * ζ ^ 4
          - ((58 / 17) : ℂ) * ζ ^ 5
          - ((31 / 17) : ℂ) * ζ ^ 8
          + ((58 / 17) : ℂ) * ζ ^ 9
          - ((43 / 17) : ℂ) * ζ ^ 10
          - ((58 / 17) : ℂ) * ζ ^ 13
          + ((43 / 17) : ℂ) * ζ ^ 14
          - ((9 / 2) : ℂ) * ζ ^ 15
          - ((43 / 17) : ℂ) * ζ ^ 18
          + ((9 / 2) : ℂ) * ζ ^ 19
          - ((47 / 34) : ℂ) * ζ ^ 20
          - ((9 / 2) : ℂ) * ζ ^ 23
          + ((47 / 34) : ℂ) * ζ ^ 24
          - ((47 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry03_07 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (3 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((13 / 34) : ℂ)
          + ((13 / 34) : ℂ) * ζ ^ 4
          + ((21 / 34) : ℂ) * ζ ^ 5
          - ((13 / 34) : ℂ) * ζ ^ 8
          - ((21 / 34) : ℂ) * ζ ^ 9
          - ((4 / 17) : ℂ) * ζ ^ 10
          + ((21 / 34) : ℂ) * ζ ^ 13
          + ((4 / 17) : ℂ) * ζ ^ 14
          + ((23 / 34) : ℂ) * ζ ^ 15
          - ((4 / 17) : ℂ) * ζ ^ 18
          - ((23 / 34) : ℂ) * ζ ^ 19
          + ((27 / 34) : ℂ) * ζ ^ 20
          + ((23 / 34) : ℂ) * ζ ^ 23
          - ((27 / 34) : ℂ) * ζ ^ 24
          + ((27 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((13 / 34) : ℂ)
          + ((13 / 34) : ℂ) * ζ ^ 4
          + ((21 / 34) : ℂ) * ζ ^ 5
          - ((13 / 34) : ℂ) * ζ ^ 8
          - ((21 / 34) : ℂ) * ζ ^ 9
          - ((4 / 17) : ℂ) * ζ ^ 10
          + ((21 / 34) : ℂ) * ζ ^ 13
          + ((4 / 17) : ℂ) * ζ ^ 14
          + ((23 / 34) : ℂ) * ζ ^ 15
          - ((4 / 17) : ℂ) * ζ ^ 18
          - ((23 / 34) : ℂ) * ζ ^ 19
          + ((27 / 34) : ℂ) * ζ ^ 20
          + ((23 / 34) : ℂ) * ζ ^ 23
          - ((27 / 34) : ℂ) * ζ ^ 24
          + ((27 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry03_08 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (3 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((21 / 17) : ℂ)
          + ((21 / 17) : ℂ) * ζ ^ 4
          - ((29 / 17) : ℂ) * ζ ^ 5
          - ((21 / 17) : ℂ) * ζ ^ 8
          + ((29 / 17) : ℂ) * ζ ^ 9
          - ((25 / 17) : ℂ) * ζ ^ 10
          - ((29 / 17) : ℂ) * ζ ^ 13
          + ((25 / 17) : ℂ) * ζ ^ 14
          - ((28 / 17) : ℂ) * ζ ^ 15
          - ((25 / 17) : ℂ) * ζ ^ 18
          + ((28 / 17) : ℂ) * ζ ^ 19
          - ((7 / 17) : ℂ) * ζ ^ 20
          - ((28 / 17) : ℂ) * ζ ^ 23
          + ((7 / 17) : ℂ) * ζ ^ 24
          - ((7 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((21 / 17) : ℂ)
          + ((21 / 17) : ℂ) * ζ ^ 4
          - ((29 / 17) : ℂ) * ζ ^ 5
          - ((21 / 17) : ℂ) * ζ ^ 8
          + ((29 / 17) : ℂ) * ζ ^ 9
          - ((25 / 17) : ℂ) * ζ ^ 10
          - ((29 / 17) : ℂ) * ζ ^ 13
          + ((25 / 17) : ℂ) * ζ ^ 14
          - ((28 / 17) : ℂ) * ζ ^ 15
          - ((25 / 17) : ℂ) * ζ ^ 18
          + ((28 / 17) : ℂ) * ζ ^ 19
          - ((7 / 17) : ℂ) * ζ ^ 20
          - ((28 / 17) : ℂ) * ζ ^ 23
          + ((7 / 17) : ℂ) * ζ ^ 24
          - ((7 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry03_09 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (3 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 17) : ℂ)
          + ((1 / 17) : ℂ) * ζ ^ 4
          + ((46 / 17) : ℂ) * ζ ^ 5
          - ((1 / 17) : ℂ) * ζ ^ 8
          - ((46 / 17) : ℂ) * ζ ^ 9
          + ((11 / 17) : ℂ) * ζ ^ 10
          + ((46 / 17) : ℂ) * ζ ^ 13
          - ((11 / 17) : ℂ) * ζ ^ 14
          + ((8 / 17) : ℂ) * ζ ^ 15
          + ((11 / 17) : ℂ) * ζ ^ 18
          - ((8 / 17) : ℂ) * ζ ^ 19
          + ((6 / 17) : ℂ) * ζ ^ 20
          + ((8 / 17) : ℂ) * ζ ^ 23
          - ((6 / 17) : ℂ) * ζ ^ 24
          + ((6 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 17) : ℂ)
          + ((1 / 17) : ℂ) * ζ ^ 4
          + ((46 / 17) : ℂ) * ζ ^ 5
          - ((1 / 17) : ℂ) * ζ ^ 8
          - ((46 / 17) : ℂ) * ζ ^ 9
          + ((11 / 17) : ℂ) * ζ ^ 10
          + ((46 / 17) : ℂ) * ζ ^ 13
          - ((11 / 17) : ℂ) * ζ ^ 14
          + ((8 / 17) : ℂ) * ζ ^ 15
          + ((11 / 17) : ℂ) * ζ ^ 18
          - ((8 / 17) : ℂ) * ζ ^ 19
          + ((6 / 17) : ℂ) * ζ ^ 20
          + ((8 / 17) : ℂ) * ζ ^ 23
          - ((6 / 17) : ℂ) * ζ ^ 24
          + ((6 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry04_00 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (4 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((3 / 34) : ℂ)
          - ((3 / 34) : ℂ) * ζ ^ 4
          - ((9 / 34) : ℂ) * ζ ^ 5
          + ((3 / 34) : ℂ) * ζ ^ 8
          + ((9 / 34) : ℂ) * ζ ^ 9
          + ((2 / 17) : ℂ) * ζ ^ 10
          - ((9 / 34) : ℂ) * ζ ^ 13
          - ((2 / 17) : ℂ) * ζ ^ 14
          - ((19 / 17) : ℂ) * ζ ^ 15
          + ((2 / 17) : ℂ) * ζ ^ 18
          + ((19 / 17) : ℂ) * ζ ^ 19
          + ((5 / 17) : ℂ) * ζ ^ 20
          - ((19 / 17) : ℂ) * ζ ^ 23
          - ((5 / 17) : ℂ) * ζ ^ 24
          + ((5 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((3 / 34) : ℂ)
          - ((3 / 34) : ℂ) * ζ ^ 4
          - ((9 / 34) : ℂ) * ζ ^ 5
          + ((3 / 34) : ℂ) * ζ ^ 8
          + ((9 / 34) : ℂ) * ζ ^ 9
          + ((2 / 17) : ℂ) * ζ ^ 10
          - ((9 / 34) : ℂ) * ζ ^ 13
          - ((2 / 17) : ℂ) * ζ ^ 14
          - ((19 / 17) : ℂ) * ζ ^ 15
          + ((2 / 17) : ℂ) * ζ ^ 18
          + ((19 / 17) : ℂ) * ζ ^ 19
          + ((5 / 17) : ℂ) * ζ ^ 20
          - ((19 / 17) : ℂ) * ζ ^ 23
          - ((5 / 17) : ℂ) * ζ ^ 24
          + ((5 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry04_01 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (4 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((11 / 17) : ℂ)
          - ((11 / 17) : ℂ) * ζ ^ 4
          + ((18 / 17) : ℂ) * ζ ^ 5
          + ((11 / 17) : ℂ) * ζ ^ 8
          - ((18 / 17) : ℂ) * ζ ^ 9
          - ((8 / 17) : ℂ) * ζ ^ 10
          + ((18 / 17) : ℂ) * ζ ^ 13
          + ((8 / 17) : ℂ) * ζ ^ 14
          - ((9 / 17) : ℂ) * ζ ^ 15
          - ((8 / 17) : ℂ) * ζ ^ 18
          + ((9 / 17) : ℂ) * ζ ^ 19
          + ((14 / 17) : ℂ) * ζ ^ 20
          - ((9 / 17) : ℂ) * ζ ^ 23
          - ((14 / 17) : ℂ) * ζ ^ 24
          + ((14 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((11 / 17) : ℂ)
          - ((11 / 17) : ℂ) * ζ ^ 4
          + ((18 / 17) : ℂ) * ζ ^ 5
          + ((11 / 17) : ℂ) * ζ ^ 8
          - ((18 / 17) : ℂ) * ζ ^ 9
          - ((8 / 17) : ℂ) * ζ ^ 10
          + ((18 / 17) : ℂ) * ζ ^ 13
          + ((8 / 17) : ℂ) * ζ ^ 14
          - ((9 / 17) : ℂ) * ζ ^ 15
          - ((8 / 17) : ℂ) * ζ ^ 18
          + ((9 / 17) : ℂ) * ζ ^ 19
          + ((14 / 17) : ℂ) * ζ ^ 20
          - ((9 / 17) : ℂ) * ζ ^ 23
          - ((14 / 17) : ℂ) * ζ ^ 24
          + ((14 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry04_02 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (4 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((8 / 17) : ℂ)
          - ((8 / 17) : ℂ) * ζ ^ 4
          - ((7 / 17) : ℂ) * ζ ^ 5
          + ((8 / 17) : ℂ) * ζ ^ 8
          + ((7 / 17) : ℂ) * ζ ^ 9
          + ((5 / 17) : ℂ) * ζ ^ 10
          - ((7 / 17) : ℂ) * ζ ^ 13
          - ((5 / 17) : ℂ) * ζ ^ 14
          + ((29 / 17) : ℂ) * ζ ^ 15
          + ((5 / 17) : ℂ) * ζ ^ 18
          - ((29 / 17) : ℂ) * ζ ^ 19
          - ((13 / 17) : ℂ) * ζ ^ 20
          + ((29 / 17) : ℂ) * ζ ^ 23
          + ((13 / 17) : ℂ) * ζ ^ 24
          - ((13 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((8 / 17) : ℂ)
          - ((8 / 17) : ℂ) * ζ ^ 4
          - ((7 / 17) : ℂ) * ζ ^ 5
          + ((8 / 17) : ℂ) * ζ ^ 8
          + ((7 / 17) : ℂ) * ζ ^ 9
          + ((5 / 17) : ℂ) * ζ ^ 10
          - ((7 / 17) : ℂ) * ζ ^ 13
          - ((5 / 17) : ℂ) * ζ ^ 14
          + ((29 / 17) : ℂ) * ζ ^ 15
          + ((5 / 17) : ℂ) * ζ ^ 18
          - ((29 / 17) : ℂ) * ζ ^ 19
          - ((13 / 17) : ℂ) * ζ ^ 20
          + ((29 / 17) : ℂ) * ζ ^ 23
          + ((13 / 17) : ℂ) * ζ ^ 24
          - ((13 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry04_03 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (4 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((33 / 34) : ℂ)
          + ((33 / 34) : ℂ) * ζ ^ 4
          + ((31 / 34) : ℂ) * ζ ^ 5
          - ((33 / 34) : ℂ) * ζ ^ 8
          - ((31 / 34) : ℂ) * ζ ^ 9
          - ((5 / 17) : ℂ) * ζ ^ 10
          + ((31 / 34) : ℂ) * ζ ^ 13
          + ((5 / 17) : ℂ) * ζ ^ 14
          + ((5 / 17) : ℂ) * ζ ^ 15
          - ((5 / 17) : ℂ) * ζ ^ 18
          - ((5 / 17) : ℂ) * ζ ^ 19
          - ((4 / 17) : ℂ) * ζ ^ 20
          + ((5 / 17) : ℂ) * ζ ^ 23
          + ((4 / 17) : ℂ) * ζ ^ 24
          - ((4 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((33 / 34) : ℂ)
          + ((33 / 34) : ℂ) * ζ ^ 4
          + ((31 / 34) : ℂ) * ζ ^ 5
          - ((33 / 34) : ℂ) * ζ ^ 8
          - ((31 / 34) : ℂ) * ζ ^ 9
          - ((5 / 17) : ℂ) * ζ ^ 10
          + ((31 / 34) : ℂ) * ζ ^ 13
          + ((5 / 17) : ℂ) * ζ ^ 14
          + ((5 / 17) : ℂ) * ζ ^ 15
          - ((5 / 17) : ℂ) * ζ ^ 18
          - ((5 / 17) : ℂ) * ζ ^ 19
          - ((4 / 17) : ℂ) * ζ ^ 20
          + ((5 / 17) : ℂ) * ζ ^ 23
          + ((4 / 17) : ℂ) * ζ ^ 24
          - ((4 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry04_04 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (4 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((10 / 17) : ℂ)
          + ((10 / 17) : ℂ) * ζ ^ 4
          + ((13 / 17) : ℂ) * ζ ^ 5
          - ((10 / 17) : ℂ) * ζ ^ 8
          - ((13 / 17) : ℂ) * ζ ^ 9
          - ((2 / 17) : ℂ) * ζ ^ 10
          + ((13 / 17) : ℂ) * ζ ^ 13
          + ((2 / 17) : ℂ) * ζ ^ 14
          - ((15 / 17) : ℂ) * ζ ^ 15
          - ((2 / 17) : ℂ) * ζ ^ 18
          + ((15 / 17) : ℂ) * ζ ^ 19
          + ((12 / 17) : ℂ) * ζ ^ 20
          - ((15 / 17) : ℂ) * ζ ^ 23
          - ((12 / 17) : ℂ) * ζ ^ 24
          + ((12 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((10 / 17) : ℂ)
          + ((10 / 17) : ℂ) * ζ ^ 4
          + ((13 / 17) : ℂ) * ζ ^ 5
          - ((10 / 17) : ℂ) * ζ ^ 8
          - ((13 / 17) : ℂ) * ζ ^ 9
          - ((2 / 17) : ℂ) * ζ ^ 10
          + ((13 / 17) : ℂ) * ζ ^ 13
          + ((2 / 17) : ℂ) * ζ ^ 14
          - ((15 / 17) : ℂ) * ζ ^ 15
          - ((2 / 17) : ℂ) * ζ ^ 18
          + ((15 / 17) : ℂ) * ζ ^ 19
          + ((12 / 17) : ℂ) * ζ ^ 20
          - ((15 / 17) : ℂ) * ζ ^ 23
          - ((12 / 17) : ℂ) * ζ ^ 24
          + ((12 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry04_05 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (4 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((13 / 34) : ℂ)
          - ((13 / 34) : ℂ) * ζ ^ 4
          - ((5 / 34) : ℂ) * ζ ^ 5
          + ((13 / 34) : ℂ) * ζ ^ 8
          + ((5 / 34) : ℂ) * ζ ^ 9
          + ((3 / 17) : ℂ) * ζ ^ 10
          - ((5 / 34) : ℂ) * ζ ^ 13
          - ((3 / 17) : ℂ) * ζ ^ 14
          - ((3 / 17) : ℂ) * ζ ^ 15
          + ((3 / 17) : ℂ) * ζ ^ 18
          + ((3 / 17) : ℂ) * ζ ^ 19
          + ((16 / 17) : ℂ) * ζ ^ 20
          - ((3 / 17) : ℂ) * ζ ^ 23
          - ((16 / 17) : ℂ) * ζ ^ 24
          + ((16 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((13 / 34) : ℂ)
          - ((13 / 34) : ℂ) * ζ ^ 4
          - ((5 / 34) : ℂ) * ζ ^ 5
          + ((13 / 34) : ℂ) * ζ ^ 8
          + ((5 / 34) : ℂ) * ζ ^ 9
          + ((3 / 17) : ℂ) * ζ ^ 10
          - ((5 / 34) : ℂ) * ζ ^ 13
          - ((3 / 17) : ℂ) * ζ ^ 14
          - ((3 / 17) : ℂ) * ζ ^ 15
          + ((3 / 17) : ℂ) * ζ ^ 18
          + ((3 / 17) : ℂ) * ζ ^ 19
          + ((16 / 17) : ℂ) * ζ ^ 20
          - ((3 / 17) : ℂ) * ζ ^ 23
          - ((16 / 17) : ℂ) * ζ ^ 24
          + ((16 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry04_06 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (4 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((16 / 17) : ℂ)
          - ((16 / 17) : ℂ) * ζ ^ 4
          + ((3 / 17) : ℂ) * ζ ^ 5
          + ((16 / 17) : ℂ) * ζ ^ 8
          - ((3 / 17) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 10
          + ((3 / 17) : ℂ) * ζ ^ 13
          + ((7 / 17) : ℂ) * ζ ^ 14
          + ((24 / 17) : ℂ) * ζ ^ 15
          - ((7 / 17) : ℂ) * ζ ^ 18
          - ((24 / 17) : ℂ) * ζ ^ 19
          + ((25 / 17) : ℂ) * ζ ^ 20
          + ((24 / 17) : ℂ) * ζ ^ 23
          - ((25 / 17) : ℂ) * ζ ^ 24
          + ((25 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((16 / 17) : ℂ)
          - ((16 / 17) : ℂ) * ζ ^ 4
          + ((3 / 17) : ℂ) * ζ ^ 5
          + ((16 / 17) : ℂ) * ζ ^ 8
          - ((3 / 17) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 10
          + ((3 / 17) : ℂ) * ζ ^ 13
          + ((7 / 17) : ℂ) * ζ ^ 14
          + ((24 / 17) : ℂ) * ζ ^ 15
          - ((7 / 17) : ℂ) * ζ ^ 18
          - ((24 / 17) : ℂ) * ζ ^ 19
          + ((25 / 17) : ℂ) * ζ ^ 20
          + ((24 / 17) : ℂ) * ζ ^ 23
          - ((25 / 17) : ℂ) * ζ ^ 24
          + ((25 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry04_07 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (4 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((3 / 17) : ℂ)
          - ((3 / 17) : ℂ) * ζ ^ 4
          - ((9 / 17) : ℂ) * ζ ^ 5
          + ((3 / 17) : ℂ) * ζ ^ 8
          + ((9 / 17) : ℂ) * ζ ^ 9
          - ((13 / 17) : ℂ) * ζ ^ 10
          - ((9 / 17) : ℂ) * ζ ^ 13
          + ((13 / 17) : ℂ) * ζ ^ 14
          + ((13 / 17) : ℂ) * ζ ^ 15
          - ((13 / 17) : ℂ) * ζ ^ 18
          - ((13 / 17) : ℂ) * ζ ^ 19
          - ((7 / 17) : ℂ) * ζ ^ 20
          + ((13 / 17) : ℂ) * ζ ^ 23
          + ((7 / 17) : ℂ) * ζ ^ 24
          - ((7 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((3 / 17) : ℂ)
          - ((3 / 17) : ℂ) * ζ ^ 4
          - ((9 / 17) : ℂ) * ζ ^ 5
          + ((3 / 17) : ℂ) * ζ ^ 8
          + ((9 / 17) : ℂ) * ζ ^ 9
          - ((13 / 17) : ℂ) * ζ ^ 10
          - ((9 / 17) : ℂ) * ζ ^ 13
          + ((13 / 17) : ℂ) * ζ ^ 14
          + ((13 / 17) : ℂ) * ζ ^ 15
          - ((13 / 17) : ℂ) * ζ ^ 18
          - ((13 / 17) : ℂ) * ζ ^ 19
          - ((7 / 17) : ℂ) * ζ ^ 20
          + ((13 / 17) : ℂ) * ζ ^ 23
          + ((7 / 17) : ℂ) * ζ ^ 24
          - ((7 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry04_08 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (4 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((12 / 17) : ℂ)
          + ((12 / 17) : ℂ) * ζ ^ 4
          + ((19 / 17) : ℂ) * ζ ^ 5
          - ((12 / 17) : ℂ) * ζ ^ 8
          - ((19 / 17) : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 10
          + ((19 / 17) : ℂ) * ζ ^ 13
          - ((1 / 17) : ℂ) * ζ ^ 14
          - ((1 / 17) : ℂ) * ζ ^ 15
          + ((1 / 17) : ℂ) * ζ ^ 18
          + ((1 / 17) : ℂ) * ζ ^ 19
          + ((28 / 17) : ℂ) * ζ ^ 20
          - ((1 / 17) : ℂ) * ζ ^ 23
          - ((28 / 17) : ℂ) * ζ ^ 24
          + ((28 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((12 / 17) : ℂ)
          + ((12 / 17) : ℂ) * ζ ^ 4
          + ((19 / 17) : ℂ) * ζ ^ 5
          - ((12 / 17) : ℂ) * ζ ^ 8
          - ((19 / 17) : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 10
          + ((19 / 17) : ℂ) * ζ ^ 13
          - ((1 / 17) : ℂ) * ζ ^ 14
          - ((1 / 17) : ℂ) * ζ ^ 15
          + ((1 / 17) : ℂ) * ζ ^ 18
          + ((1 / 17) : ℂ) * ζ ^ 19
          + ((28 / 17) : ℂ) * ζ ^ 20
          - ((1 / 17) : ℂ) * ζ ^ 23
          - ((28 / 17) : ℂ) * ζ ^ 24
          + ((28 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry04_09 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (4 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 2) : ℂ)
          + ((1 / 2) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 5
          - ((1 / 2) : ℂ) * ζ ^ 8
          - ((1 / 2) : ℂ) * ζ ^ 9
          + ((1 / 2) : ℂ) * ζ ^ 13
          - ζ ^ 20
          + ζ ^ 24
          - ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 2) : ℂ)
          + ((1 / 2) : ℂ) * ζ ^ 4
          + ((1 / 2) : ℂ) * ζ ^ 5
          - ((1 / 2) : ℂ) * ζ ^ 8
          - ((1 / 2) : ℂ) * ζ ^ 9
          + ((1 / 2) : ℂ) * ζ ^ 13
          - ζ ^ 20
          + ζ ^ 24
          - ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry05_00 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (5 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((27 / 34) : ℂ)
          + ((27 / 34) : ℂ) * ζ ^ 4
          - ((37 / 34) : ℂ) * ζ ^ 5
          - ((27 / 34) : ℂ) * ζ ^ 8
          + ((37 / 34) : ℂ) * ζ ^ 9
          - ((37 / 34) : ℂ) * ζ ^ 13
          - ((5 / 34) : ℂ) * ζ ^ 15
          + ((5 / 34) : ℂ) * ζ ^ 19
          - ((27 / 34) : ℂ) * ζ ^ 20
          - ((5 / 34) : ℂ) * ζ ^ 23
          + ((27 / 34) : ℂ) * ζ ^ 24
          - ((27 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((27 / 34) : ℂ)
          + ((27 / 34) : ℂ) * ζ ^ 4
          - ((37 / 34) : ℂ) * ζ ^ 5
          - ((27 / 34) : ℂ) * ζ ^ 8
          + ((37 / 34) : ℂ) * ζ ^ 9
          - ((37 / 34) : ℂ) * ζ ^ 13
          - ((5 / 34) : ℂ) * ζ ^ 15
          + ((5 / 34) : ℂ) * ζ ^ 19
          - ((27 / 34) : ℂ) * ζ ^ 20
          - ((5 / 34) : ℂ) * ζ ^ 23
          + ((27 / 34) : ℂ) * ζ ^ 24
          - ((27 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry05_01 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (5 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((3 / 17) : ℂ)
          - ((3 / 17) : ℂ) * ζ ^ 4
          + ((6 / 17) : ℂ) * ζ ^ 5
          + ((3 / 17) : ℂ) * ζ ^ 8
          - ((6 / 17) : ℂ) * ζ ^ 9
          + ((6 / 17) : ℂ) * ζ ^ 13
          + ((10 / 17) : ℂ) * ζ ^ 15
          - ((10 / 17) : ℂ) * ζ ^ 19
          + ((3 / 17) : ℂ) * ζ ^ 20
          + ((10 / 17) : ℂ) * ζ ^ 23
          - ((3 / 17) : ℂ) * ζ ^ 24
          + ((3 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((3 / 17) : ℂ)
          - ((3 / 17) : ℂ) * ζ ^ 4
          + ((6 / 17) : ℂ) * ζ ^ 5
          + ((3 / 17) : ℂ) * ζ ^ 8
          - ((6 / 17) : ℂ) * ζ ^ 9
          + ((6 / 17) : ℂ) * ζ ^ 13
          + ((10 / 17) : ℂ) * ζ ^ 15
          - ((10 / 17) : ℂ) * ζ ^ 19
          + ((3 / 17) : ℂ) * ζ ^ 20
          + ((10 / 17) : ℂ) * ζ ^ 23
          - ((3 / 17) : ℂ) * ζ ^ 24
          + ((3 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry05_02 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (5 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((13 / 17) : ℂ)
          - ((13 / 17) : ℂ) * ζ ^ 4
          - ((8 / 17) : ℂ) * ζ ^ 5
          + ((13 / 17) : ℂ) * ζ ^ 8
          + ((8 / 17) : ℂ) * ζ ^ 9
          - ((8 / 17) : ℂ) * ζ ^ 13
          + ((15 / 17) : ℂ) * ζ ^ 15
          - ((15 / 17) : ℂ) * ζ ^ 19
          + ((13 / 17) : ℂ) * ζ ^ 20
          + ((15 / 17) : ℂ) * ζ ^ 23
          - ((13 / 17) : ℂ) * ζ ^ 24
          + ((13 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((13 / 17) : ℂ)
          - ((13 / 17) : ℂ) * ζ ^ 4
          - ((8 / 17) : ℂ) * ζ ^ 5
          + ((13 / 17) : ℂ) * ζ ^ 8
          + ((8 / 17) : ℂ) * ζ ^ 9
          - ((8 / 17) : ℂ) * ζ ^ 13
          + ((15 / 17) : ℂ) * ζ ^ 15
          - ((15 / 17) : ℂ) * ζ ^ 19
          + ((13 / 17) : ℂ) * ζ ^ 20
          + ((15 / 17) : ℂ) * ζ ^ 23
          - ((13 / 17) : ℂ) * ζ ^ 24
          + ((13 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry05_03 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (5 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((25 / 34) : ℂ)
          - ((25 / 34) : ℂ) * ζ ^ 4
          + ((33 / 34) : ℂ) * ζ ^ 5
          + ((25 / 34) : ℂ) * ζ ^ 8
          - ((33 / 34) : ℂ) * ζ ^ 9
          + ((33 / 34) : ℂ) * ζ ^ 13
          - ((13 / 34) : ℂ) * ζ ^ 15
          + ((13 / 34) : ℂ) * ζ ^ 19
          + ((25 / 34) : ℂ) * ζ ^ 20
          - ((13 / 34) : ℂ) * ζ ^ 23
          - ((25 / 34) : ℂ) * ζ ^ 24
          + ((25 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((25 / 34) : ℂ)
          - ((25 / 34) : ℂ) * ζ ^ 4
          + ((33 / 34) : ℂ) * ζ ^ 5
          + ((25 / 34) : ℂ) * ζ ^ 8
          - ((33 / 34) : ℂ) * ζ ^ 9
          + ((33 / 34) : ℂ) * ζ ^ 13
          - ((13 / 34) : ℂ) * ζ ^ 15
          + ((13 / 34) : ℂ) * ζ ^ 19
          + ((25 / 34) : ℂ) * ζ ^ 20
          - ((13 / 34) : ℂ) * ζ ^ 23
          - ((25 / 34) : ℂ) * ζ ^ 24
          + ((25 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry05_04 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (5 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((5 / 17) : ℂ)
          - ((5 / 17) : ℂ) * ζ ^ 4
          + ((27 / 17) : ℂ) * ζ ^ 5
          + ((5 / 17) : ℂ) * ζ ^ 8
          - ((27 / 17) : ℂ) * ζ ^ 9
          + ((27 / 17) : ℂ) * ζ ^ 13
          - ((23 / 17) : ℂ) * ζ ^ 15
          + ((23 / 17) : ℂ) * ζ ^ 19
          + ((5 / 17) : ℂ) * ζ ^ 20
          - ((23 / 17) : ℂ) * ζ ^ 23
          - ((5 / 17) : ℂ) * ζ ^ 24
          + ((5 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((5 / 17) : ℂ)
          - ((5 / 17) : ℂ) * ζ ^ 4
          + ((27 / 17) : ℂ) * ζ ^ 5
          + ((5 / 17) : ℂ) * ζ ^ 8
          - ((27 / 17) : ℂ) * ζ ^ 9
          + ((27 / 17) : ℂ) * ζ ^ 13
          - ((23 / 17) : ℂ) * ζ ^ 15
          + ((23 / 17) : ℂ) * ζ ^ 19
          + ((5 / 17) : ℂ) * ζ ^ 20
          - ((23 / 17) : ℂ) * ζ ^ 23
          - ((5 / 17) : ℂ) * ζ ^ 24
          + ((5 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry05_05 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (5 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((19 / 34) : ℂ)
          - ((19 / 34) : ℂ) * ζ ^ 4
          - ((13 / 34) : ℂ) * ζ ^ 5
          + ((19 / 34) : ℂ) * ζ ^ 8
          + ((13 / 34) : ℂ) * ζ ^ 9
          - ((13 / 34) : ℂ) * ζ ^ 13
          + ((35 / 34) : ℂ) * ζ ^ 15
          - ((35 / 34) : ℂ) * ζ ^ 19
          + ((19 / 34) : ℂ) * ζ ^ 20
          + ((35 / 34) : ℂ) * ζ ^ 23
          - ((19 / 34) : ℂ) * ζ ^ 24
          + ((19 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((19 / 34) : ℂ)
          - ((19 / 34) : ℂ) * ζ ^ 4
          - ((13 / 34) : ℂ) * ζ ^ 5
          + ((19 / 34) : ℂ) * ζ ^ 8
          + ((13 / 34) : ℂ) * ζ ^ 9
          - ((13 / 34) : ℂ) * ζ ^ 13
          + ((35 / 34) : ℂ) * ζ ^ 15
          - ((35 / 34) : ℂ) * ζ ^ 19
          + ((19 / 34) : ℂ) * ζ ^ 20
          + ((35 / 34) : ℂ) * ζ ^ 23
          - ((19 / 34) : ℂ) * ζ ^ 24
          + ((19 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry05_06 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (5 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((26 / 17) : ℂ)
          - ((26 / 17) : ℂ) * ζ ^ 4
          + ((18 / 17) : ℂ) * ζ ^ 5
          + ((26 / 17) : ℂ) * ζ ^ 8
          - ((18 / 17) : ℂ) * ζ ^ 9
          + ((18 / 17) : ℂ) * ζ ^ 13
          + ((13 / 17) : ℂ) * ζ ^ 15
          - ((13 / 17) : ℂ) * ζ ^ 19
          + ((26 / 17) : ℂ) * ζ ^ 20
          + ((13 / 17) : ℂ) * ζ ^ 23
          - ((26 / 17) : ℂ) * ζ ^ 24
          + ((26 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((26 / 17) : ℂ)
          - ((26 / 17) : ℂ) * ζ ^ 4
          + ((18 / 17) : ℂ) * ζ ^ 5
          + ((26 / 17) : ℂ) * ζ ^ 8
          - ((18 / 17) : ℂ) * ζ ^ 9
          + ((18 / 17) : ℂ) * ζ ^ 13
          + ((13 / 17) : ℂ) * ζ ^ 15
          - ((13 / 17) : ℂ) * ζ ^ 19
          + ((26 / 17) : ℂ) * ζ ^ 20
          + ((13 / 17) : ℂ) * ζ ^ 23
          - ((26 / 17) : ℂ) * ζ ^ 24
          + ((26 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry05_07 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (5 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((10 / 17) : ℂ)
          + ((10 / 17) : ℂ) * ζ ^ 4
          - ((3 / 17) : ℂ) * ζ ^ 5
          - ((10 / 17) : ℂ) * ζ ^ 8
          + ((3 / 17) : ℂ) * ζ ^ 9
          - ((3 / 17) : ℂ) * ζ ^ 13
          - ((5 / 17) : ℂ) * ζ ^ 15
          + ((5 / 17) : ℂ) * ζ ^ 19
          - ((10 / 17) : ℂ) * ζ ^ 20
          - ((5 / 17) : ℂ) * ζ ^ 23
          + ((10 / 17) : ℂ) * ζ ^ 24
          - ((10 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((10 / 17) : ℂ)
          + ((10 / 17) : ℂ) * ζ ^ 4
          - ((3 / 17) : ℂ) * ζ ^ 5
          - ((10 / 17) : ℂ) * ζ ^ 8
          + ((3 / 17) : ℂ) * ζ ^ 9
          - ((3 / 17) : ℂ) * ζ ^ 13
          - ((5 / 17) : ℂ) * ζ ^ 15
          + ((5 / 17) : ℂ) * ζ ^ 19
          - ((10 / 17) : ℂ) * ζ ^ 20
          - ((5 / 17) : ℂ) * ζ ^ 23
          + ((10 / 17) : ℂ) * ζ ^ 24
          - ((10 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry05_08 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (5 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((6 / 17) : ℂ)
          - ((6 / 17) : ℂ) * ζ ^ 4
          + ((12 / 17) : ℂ) * ζ ^ 5
          + ((6 / 17) : ℂ) * ζ ^ 8
          - ((12 / 17) : ℂ) * ζ ^ 9
          + ((12 / 17) : ℂ) * ζ ^ 13
          + ((3 / 17) : ℂ) * ζ ^ 15
          - ((3 / 17) : ℂ) * ζ ^ 19
          + ((6 / 17) : ℂ) * ζ ^ 20
          + ((3 / 17) : ℂ) * ζ ^ 23
          - ((6 / 17) : ℂ) * ζ ^ 24
          + ((6 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((6 / 17) : ℂ)
          - ((6 / 17) : ℂ) * ζ ^ 4
          + ((12 / 17) : ℂ) * ζ ^ 5
          + ((6 / 17) : ℂ) * ζ ^ 8
          - ((12 / 17) : ℂ) * ζ ^ 9
          + ((12 / 17) : ℂ) * ζ ^ 13
          + ((3 / 17) : ℂ) * ζ ^ 15
          - ((3 / 17) : ℂ) * ζ ^ 19
          + ((6 / 17) : ℂ) * ζ ^ 20
          + ((3 / 17) : ℂ) * ζ ^ 23
          - ((6 / 17) : ℂ) * ζ ^ 24
          + ((6 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry05_09 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (5 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
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
          - ((1 / 2) : ℂ) * ζ ^ 13
          + ((1 / 2) : ℂ) * ζ ^ 15
          - ((1 / 2) : ℂ) * ζ ^ 19
          + ((1 / 2) : ℂ) * ζ ^ 20
          + ((1 / 2) : ℂ) * ζ ^ 23
          - ((1 / 2) : ℂ) * ζ ^ 24
          + ((1 / 2) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 2) : ℂ)
          - ((1 / 2) : ℂ) * ζ ^ 4
          - ((1 / 2) : ℂ) * ζ ^ 5
          + ((1 / 2) : ℂ) * ζ ^ 8
          + ((1 / 2) : ℂ) * ζ ^ 9
          - ((1 / 2) : ℂ) * ζ ^ 13
          + ((1 / 2) : ℂ) * ζ ^ 15
          - ((1 / 2) : ℂ) * ζ ^ 19
          + ((1 / 2) : ℂ) * ζ ^ 20
          + ((1 / 2) : ℂ) * ζ ^ 23
          - ((1 / 2) : ℂ) * ζ ^ 24
          + ((1 / 2) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry06_00 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (6 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((11 / 34) : ℂ)
          - ((11 / 34) : ℂ) * ζ ^ 4
          - ((4 / 17) : ℂ) * ζ ^ 5
          + ((11 / 34) : ℂ) * ζ ^ 8
          + ((4 / 17) : ℂ) * ζ ^ 9
          - ((9 / 34) : ℂ) * ζ ^ 10
          - ((4 / 17) : ℂ) * ζ ^ 13
          + ((9 / 34) : ℂ) * ζ ^ 14
          + ((31 / 17) : ℂ) * ζ ^ 15
          - ((9 / 34) : ℂ) * ζ ^ 18
          - ((31 / 17) : ℂ) * ζ ^ 19
          + ((7 / 34) : ℂ) * ζ ^ 20
          + ((31 / 17) : ℂ) * ζ ^ 23
          - ((7 / 34) : ℂ) * ζ ^ 24
          + ((7 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((11 / 34) : ℂ)
          - ((11 / 34) : ℂ) * ζ ^ 4
          - ((4 / 17) : ℂ) * ζ ^ 5
          + ((11 / 34) : ℂ) * ζ ^ 8
          + ((4 / 17) : ℂ) * ζ ^ 9
          - ((9 / 34) : ℂ) * ζ ^ 10
          - ((4 / 17) : ℂ) * ζ ^ 13
          + ((9 / 34) : ℂ) * ζ ^ 14
          + ((31 / 17) : ℂ) * ζ ^ 15
          - ((9 / 34) : ℂ) * ζ ^ 18
          - ((31 / 17) : ℂ) * ζ ^ 19
          + ((7 / 34) : ℂ) * ζ ^ 20
          + ((31 / 17) : ℂ) * ζ ^ 23
          - ((7 / 34) : ℂ) * ζ ^ 24
          + ((7 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry06_01 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (6 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((25 / 34) : ℂ)
          - ((25 / 34) : ℂ) * ζ ^ 4
          - ((7 / 17) : ℂ) * ζ ^ 5
          + ((25 / 34) : ℂ) * ζ ^ 8
          + ((7 / 17) : ℂ) * ζ ^ 9
          - ((9 / 34) : ℂ) * ζ ^ 10
          - ((7 / 17) : ℂ) * ζ ^ 13
          + ((9 / 34) : ℂ) * ζ ^ 14
          - ((15 / 17) : ℂ) * ζ ^ 15
          - ((9 / 34) : ℂ) * ζ ^ 18
          + ((15 / 17) : ℂ) * ζ ^ 19
          - ((7 / 34) : ℂ) * ζ ^ 20
          - ((15 / 17) : ℂ) * ζ ^ 23
          + ((7 / 34) : ℂ) * ζ ^ 24
          - ((7 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((25 / 34) : ℂ)
          - ((25 / 34) : ℂ) * ζ ^ 4
          - ((7 / 17) : ℂ) * ζ ^ 5
          + ((25 / 34) : ℂ) * ζ ^ 8
          + ((7 / 17) : ℂ) * ζ ^ 9
          - ((9 / 34) : ℂ) * ζ ^ 10
          - ((7 / 17) : ℂ) * ζ ^ 13
          + ((9 / 34) : ℂ) * ζ ^ 14
          - ((15 / 17) : ℂ) * ζ ^ 15
          - ((9 / 34) : ℂ) * ζ ^ 18
          + ((15 / 17) : ℂ) * ζ ^ 19
          - ((7 / 34) : ℂ) * ζ ^ 20
          - ((15 / 17) : ℂ) * ζ ^ 23
          + ((7 / 34) : ℂ) * ζ ^ 24
          - ((7 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry06_02 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (6 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 17) : ℂ)
          - ((1 / 17) : ℂ) * ζ ^ 4
          - ((27 / 17) : ℂ) * ζ ^ 5
          + ((1 / 17) : ℂ) * ζ ^ 8
          + ((27 / 17) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 10
          - ((27 / 17) : ℂ) * ζ ^ 13
          + ((7 / 17) : ℂ) * ζ ^ 14
          - ((97 / 34) : ℂ) * ζ ^ 15
          - ((7 / 17) : ℂ) * ζ ^ 18
          + ((97 / 34) : ℂ) * ζ ^ 19
          - ((53 / 34) : ℂ) * ζ ^ 20
          - ((97 / 34) : ℂ) * ζ ^ 23
          + ((53 / 34) : ℂ) * ζ ^ 24
          - ((53 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 17) : ℂ)
          - ((1 / 17) : ℂ) * ζ ^ 4
          - ((27 / 17) : ℂ) * ζ ^ 5
          + ((1 / 17) : ℂ) * ζ ^ 8
          + ((27 / 17) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 10
          - ((27 / 17) : ℂ) * ζ ^ 13
          + ((7 / 17) : ℂ) * ζ ^ 14
          - ((97 / 34) : ℂ) * ζ ^ 15
          - ((7 / 17) : ℂ) * ζ ^ 18
          + ((97 / 34) : ℂ) * ζ ^ 19
          - ((53 / 34) : ℂ) * ζ ^ 20
          - ((97 / 34) : ℂ) * ζ ^ 23
          + ((53 / 34) : ℂ) * ζ ^ 24
          - ((53 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry06_03 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (6 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((6 / 17) : ℂ)
          - ((6 / 17) : ℂ) * ζ ^ 4
          + ((27 / 34) : ℂ) * ζ ^ 5
          + ((6 / 17) : ℂ) * ζ ^ 8
          - ((27 / 34) : ℂ) * ζ ^ 9
          + ((57 / 34) : ℂ) * ζ ^ 10
          + ((27 / 34) : ℂ) * ζ ^ 13
          - ((57 / 34) : ℂ) * ζ ^ 14
          - ((1 / 2) : ℂ) * ζ ^ 15
          + ((57 / 34) : ℂ) * ζ ^ 18
          + ((1 / 2) : ℂ) * ζ ^ 19
          + ((5 / 17) : ℂ) * ζ ^ 20
          - ((1 / 2) : ℂ) * ζ ^ 23
          - ((5 / 17) : ℂ) * ζ ^ 24
          + ((5 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((6 / 17) : ℂ)
          - ((6 / 17) : ℂ) * ζ ^ 4
          + ((27 / 34) : ℂ) * ζ ^ 5
          + ((6 / 17) : ℂ) * ζ ^ 8
          - ((27 / 34) : ℂ) * ζ ^ 9
          + ((57 / 34) : ℂ) * ζ ^ 10
          + ((27 / 34) : ℂ) * ζ ^ 13
          - ((57 / 34) : ℂ) * ζ ^ 14
          - ((1 / 2) : ℂ) * ζ ^ 15
          + ((57 / 34) : ℂ) * ζ ^ 18
          + ((1 / 2) : ℂ) * ζ ^ 19
          + ((5 / 17) : ℂ) * ζ ^ 20
          - ((1 / 2) : ℂ) * ζ ^ 23
          - ((5 / 17) : ℂ) * ζ ^ 24
          + ((5 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry06_04 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (6 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((18 / 17) : ℂ)
          - ((18 / 17) : ℂ) * ζ ^ 4
          + ((41 / 34) : ℂ) * ζ ^ 5
          + ((18 / 17) : ℂ) * ζ ^ 8
          - ((41 / 34) : ℂ) * ζ ^ 9
          + ((57 / 34) : ℂ) * ζ ^ 10
          + ((41 / 34) : ℂ) * ζ ^ 13
          - ((57 / 34) : ℂ) * ζ ^ 14
          + ((39 / 34) : ℂ) * ζ ^ 15
          + ((57 / 34) : ℂ) * ζ ^ 18
          - ((39 / 34) : ℂ) * ζ ^ 19
          + ((10 / 17) : ℂ) * ζ ^ 20
          + ((39 / 34) : ℂ) * ζ ^ 23
          - ((10 / 17) : ℂ) * ζ ^ 24
          + ((10 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((18 / 17) : ℂ)
          - ((18 / 17) : ℂ) * ζ ^ 4
          + ((41 / 34) : ℂ) * ζ ^ 5
          + ((18 / 17) : ℂ) * ζ ^ 8
          - ((41 / 34) : ℂ) * ζ ^ 9
          + ((57 / 34) : ℂ) * ζ ^ 10
          + ((41 / 34) : ℂ) * ζ ^ 13
          - ((57 / 34) : ℂ) * ζ ^ 14
          + ((39 / 34) : ℂ) * ζ ^ 15
          + ((57 / 34) : ℂ) * ζ ^ 18
          - ((39 / 34) : ℂ) * ζ ^ 19
          + ((10 / 17) : ℂ) * ζ ^ 20
          + ((39 / 34) : ℂ) * ζ ^ 23
          - ((10 / 17) : ℂ) * ζ ^ 24
          + ((10 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry06_05 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (6 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 17) : ℂ)
          + ((1 / 17) : ℂ) * ζ ^ 4
          - ((15 / 17) : ℂ) * ζ ^ 5
          - ((1 / 17) : ℂ) * ζ ^ 8
          + ((15 / 17) : ℂ) * ζ ^ 9
          - ((26 / 17) : ℂ) * ζ ^ 10
          - ((15 / 17) : ℂ) * ζ ^ 13
          + ((26 / 17) : ℂ) * ζ ^ 14
          - ((5 / 34) : ℂ) * ζ ^ 15
          - ((26 / 17) : ℂ) * ζ ^ 18
          + ((5 / 34) : ℂ) * ζ ^ 19
          - ((23 / 34) : ℂ) * ζ ^ 20
          - ((5 / 34) : ℂ) * ζ ^ 23
          + ((23 / 34) : ℂ) * ζ ^ 24
          - ((23 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 17) : ℂ)
          + ((1 / 17) : ℂ) * ζ ^ 4
          - ((15 / 17) : ℂ) * ζ ^ 5
          - ((1 / 17) : ℂ) * ζ ^ 8
          + ((15 / 17) : ℂ) * ζ ^ 9
          - ((26 / 17) : ℂ) * ζ ^ 10
          - ((15 / 17) : ℂ) * ζ ^ 13
          + ((26 / 17) : ℂ) * ζ ^ 14
          - ((5 / 34) : ℂ) * ζ ^ 15
          - ((26 / 17) : ℂ) * ζ ^ 18
          + ((5 / 34) : ℂ) * ζ ^ 19
          - ((23 / 34) : ℂ) * ζ ^ 20
          - ((5 / 34) : ℂ) * ζ ^ 23
          + ((23 / 34) : ℂ) * ζ ^ 24
          - ((23 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry06_06 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (6 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 17) : ℂ)
          - ((2 / 17) : ℂ) * ζ ^ 4
          - ((26 / 17) : ℂ) * ζ ^ 5
          + ((2 / 17) : ℂ) * ζ ^ 8
          + ((26 / 17) : ℂ) * ζ ^ 9
          - ((9 / 17) : ℂ) * ζ ^ 10
          - ((26 / 17) : ℂ) * ζ ^ 13
          + ((9 / 17) : ℂ) * ζ ^ 14
          + ((3 / 34) : ℂ) * ζ ^ 15
          - ((9 / 17) : ℂ) * ζ ^ 18
          - ((3 / 34) : ℂ) * ζ ^ 19
          - ((7 / 34) : ℂ) * ζ ^ 20
          + ((3 / 34) : ℂ) * ζ ^ 23
          + ((7 / 34) : ℂ) * ζ ^ 24
          - ((7 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 17) : ℂ)
          - ((2 / 17) : ℂ) * ζ ^ 4
          - ((26 / 17) : ℂ) * ζ ^ 5
          + ((2 / 17) : ℂ) * ζ ^ 8
          + ((26 / 17) : ℂ) * ζ ^ 9
          - ((9 / 17) : ℂ) * ζ ^ 10
          - ((26 / 17) : ℂ) * ζ ^ 13
          + ((9 / 17) : ℂ) * ζ ^ 14
          + ((3 / 34) : ℂ) * ζ ^ 15
          - ((9 / 17) : ℂ) * ζ ^ 18
          - ((3 / 34) : ℂ) * ζ ^ 19
          - ((7 / 34) : ℂ) * ζ ^ 20
          + ((3 / 34) : ℂ) * ζ ^ 23
          + ((7 / 34) : ℂ) * ζ ^ 24
          - ((7 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry06_07 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (6 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((11 / 34) : ℂ)
          + ((11 / 34) : ℂ) * ζ ^ 4
          + ((9 / 34) : ℂ) * ζ ^ 5
          - ((11 / 34) : ℂ) * ζ ^ 8
          - ((9 / 34) : ℂ) * ζ ^ 9
          - ((3 / 17) : ℂ) * ζ ^ 10
          + ((9 / 34) : ℂ) * ζ ^ 13
          + ((3 / 17) : ℂ) * ζ ^ 14
          - ((1 / 34) : ℂ) * ζ ^ 15
          - ((3 / 17) : ℂ) * ζ ^ 18
          + ((1 / 34) : ℂ) * ζ ^ 19
          + ((5 / 34) : ℂ) * ζ ^ 20
          - ((1 / 34) : ℂ) * ζ ^ 23
          - ((5 / 34) : ℂ) * ζ ^ 24
          + ((5 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((11 / 34) : ℂ)
          + ((11 / 34) : ℂ) * ζ ^ 4
          + ((9 / 34) : ℂ) * ζ ^ 5
          - ((11 / 34) : ℂ) * ζ ^ 8
          - ((9 / 34) : ℂ) * ζ ^ 9
          - ((3 / 17) : ℂ) * ζ ^ 10
          + ((9 / 34) : ℂ) * ζ ^ 13
          + ((3 / 17) : ℂ) * ζ ^ 14
          - ((1 / 34) : ℂ) * ζ ^ 15
          - ((3 / 17) : ℂ) * ζ ^ 18
          + ((1 / 34) : ℂ) * ζ ^ 19
          + ((5 / 34) : ℂ) * ζ ^ 20
          - ((1 / 34) : ℂ) * ζ ^ 23
          - ((5 / 34) : ℂ) * ζ ^ 24
          + ((5 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry06_08 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (6 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 17) : ℂ)
          + ((1 / 17) : ℂ) * ζ ^ 4
          + ((5 / 17) : ℂ) * ζ ^ 5
          - ((1 / 17) : ℂ) * ζ ^ 8
          - ((5 / 17) : ℂ) * ζ ^ 9
          + ((14 / 17) : ℂ) * ζ ^ 10
          + ((5 / 17) : ℂ) * ζ ^ 13
          - ((14 / 17) : ℂ) * ζ ^ 14
          + ((26 / 17) : ℂ) * ζ ^ 15
          + ((14 / 17) : ℂ) * ζ ^ 18
          - ((26 / 17) : ℂ) * ζ ^ 19
          + ((13 / 17) : ℂ) * ζ ^ 20
          + ((26 / 17) : ℂ) * ζ ^ 23
          - ((13 / 17) : ℂ) * ζ ^ 24
          + ((13 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 17) : ℂ)
          + ((1 / 17) : ℂ) * ζ ^ 4
          + ((5 / 17) : ℂ) * ζ ^ 5
          - ((1 / 17) : ℂ) * ζ ^ 8
          - ((5 / 17) : ℂ) * ζ ^ 9
          + ((14 / 17) : ℂ) * ζ ^ 10
          + ((5 / 17) : ℂ) * ζ ^ 13
          - ((14 / 17) : ℂ) * ζ ^ 14
          + ((26 / 17) : ℂ) * ζ ^ 15
          + ((14 / 17) : ℂ) * ζ ^ 18
          - ((26 / 17) : ℂ) * ζ ^ 19
          + ((13 / 17) : ℂ) * ζ ^ 20
          + ((26 / 17) : ℂ) * ζ ^ 23
          - ((13 / 17) : ℂ) * ζ ^ 24
          + ((13 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry06_09 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (6 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((71 / 34) : ℂ)
          - ((71 / 34) : ℂ) * ζ ^ 4
          - ((1 / 17) : ℂ) * ζ ^ 5
          + ((71 / 34) : ℂ) * ζ ^ 8
          + ((1 / 17) : ℂ) * ζ ^ 9
          - ((33 / 34) : ℂ) * ζ ^ 10
          - ((1 / 17) : ℂ) * ζ ^ 13
          + ((33 / 34) : ℂ) * ζ ^ 14
          - ((41 / 34) : ℂ) * ζ ^ 15
          - ((33 / 34) : ℂ) * ζ ^ 18
          + ((41 / 34) : ℂ) * ζ ^ 19
          - ((9 / 17) : ℂ) * ζ ^ 20
          - ((41 / 34) : ℂ) * ζ ^ 23
          + ((9 / 17) : ℂ) * ζ ^ 24
          - ((9 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((71 / 34) : ℂ)
          - ((71 / 34) : ℂ) * ζ ^ 4
          - ((1 / 17) : ℂ) * ζ ^ 5
          + ((71 / 34) : ℂ) * ζ ^ 8
          + ((1 / 17) : ℂ) * ζ ^ 9
          - ((33 / 34) : ℂ) * ζ ^ 10
          - ((1 / 17) : ℂ) * ζ ^ 13
          + ((33 / 34) : ℂ) * ζ ^ 14
          - ((41 / 34) : ℂ) * ζ ^ 15
          - ((33 / 34) : ℂ) * ζ ^ 18
          + ((41 / 34) : ℂ) * ζ ^ 19
          - ((9 / 17) : ℂ) * ζ ^ 20
          - ((41 / 34) : ℂ) * ζ ^ 23
          + ((9 / 17) : ℂ) * ζ ^ 24
          - ((9 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry07_00 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (7 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((16 / 17) : ℂ)
          + ((16 / 17) : ℂ) * ζ ^ 4
          + ((27 / 34) : ℂ) * ζ ^ 5
          - ((16 / 17) : ℂ) * ζ ^ 8
          - ((27 / 34) : ℂ) * ζ ^ 9
          + ((29 / 34) : ℂ) * ζ ^ 10
          + ((27 / 34) : ℂ) * ζ ^ 13
          - ((29 / 34) : ℂ) * ζ ^ 14
          - ((3 / 17) : ℂ) * ζ ^ 15
          + ((29 / 34) : ℂ) * ζ ^ 18
          + ((3 / 17) : ℂ) * ζ ^ 19
          + ((25 / 34) : ℂ) * ζ ^ 20
          - ((3 / 17) : ℂ) * ζ ^ 23
          - ((25 / 34) : ℂ) * ζ ^ 24
          + ((25 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((16 / 17) : ℂ)
          + ((16 / 17) : ℂ) * ζ ^ 4
          + ((27 / 34) : ℂ) * ζ ^ 5
          - ((16 / 17) : ℂ) * ζ ^ 8
          - ((27 / 34) : ℂ) * ζ ^ 9
          + ((29 / 34) : ℂ) * ζ ^ 10
          + ((27 / 34) : ℂ) * ζ ^ 13
          - ((29 / 34) : ℂ) * ζ ^ 14
          - ((3 / 17) : ℂ) * ζ ^ 15
          + ((29 / 34) : ℂ) * ζ ^ 18
          + ((3 / 17) : ℂ) * ζ ^ 19
          + ((25 / 34) : ℂ) * ζ ^ 20
          - ((3 / 17) : ℂ) * ζ ^ 23
          - ((25 / 34) : ℂ) * ζ ^ 24
          + ((25 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry07_01 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (7 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((21 / 34) : ℂ)
          - ((21 / 34) : ℂ) * ζ ^ 4
          + ((10 / 17) : ℂ) * ζ ^ 5
          + ((21 / 34) : ℂ) * ζ ^ 8
          - ((10 / 17) : ℂ) * ζ ^ 9
          + ((7 / 34) : ℂ) * ζ ^ 10
          + ((10 / 17) : ℂ) * ζ ^ 13
          - ((7 / 34) : ℂ) * ζ ^ 14
          - ((6 / 17) : ℂ) * ζ ^ 15
          + ((7 / 34) : ℂ) * ζ ^ 18
          + ((6 / 17) : ℂ) * ζ ^ 19
          - ((1 / 34) : ℂ) * ζ ^ 20
          - ((6 / 17) : ℂ) * ζ ^ 23
          + ((1 / 34) : ℂ) * ζ ^ 24
          - ((1 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((21 / 34) : ℂ)
          - ((21 / 34) : ℂ) * ζ ^ 4
          + ((10 / 17) : ℂ) * ζ ^ 5
          + ((21 / 34) : ℂ) * ζ ^ 8
          - ((10 / 17) : ℂ) * ζ ^ 9
          + ((7 / 34) : ℂ) * ζ ^ 10
          + ((10 / 17) : ℂ) * ζ ^ 13
          - ((7 / 34) : ℂ) * ζ ^ 14
          - ((6 / 17) : ℂ) * ζ ^ 15
          + ((7 / 34) : ℂ) * ζ ^ 18
          + ((6 / 17) : ℂ) * ζ ^ 19
          - ((1 / 34) : ℂ) * ζ ^ 20
          - ((6 / 17) : ℂ) * ζ ^ 23
          + ((1 / 34) : ℂ) * ζ ^ 24
          - ((1 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry07_02 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (7 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((28 / 17) : ℂ)
          - ((28 / 17) : ℂ) * ζ ^ 4
          - ((13 / 17) : ℂ) * ζ ^ 5
          + ((28 / 17) : ℂ) * ζ ^ 8
          + ((13 / 17) : ℂ) * ζ ^ 9
          + ((15 / 17) : ℂ) * ζ ^ 10
          - ((13 / 17) : ℂ) * ζ ^ 13
          - ((15 / 17) : ℂ) * ζ ^ 14
          + ((55 / 34) : ℂ) * ζ ^ 15
          + ((15 / 17) : ℂ) * ζ ^ 18
          - ((55 / 34) : ℂ) * ζ ^ 19
          + ((7 / 34) : ℂ) * ζ ^ 20
          + ((55 / 34) : ℂ) * ζ ^ 23
          - ((7 / 34) : ℂ) * ζ ^ 24
          + ((7 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((28 / 17) : ℂ)
          - ((28 / 17) : ℂ) * ζ ^ 4
          - ((13 / 17) : ℂ) * ζ ^ 5
          + ((28 / 17) : ℂ) * ζ ^ 8
          + ((13 / 17) : ℂ) * ζ ^ 9
          + ((15 / 17) : ℂ) * ζ ^ 10
          - ((13 / 17) : ℂ) * ζ ^ 13
          - ((15 / 17) : ℂ) * ζ ^ 14
          + ((55 / 34) : ℂ) * ζ ^ 15
          + ((15 / 17) : ℂ) * ζ ^ 18
          - ((55 / 34) : ℂ) * ζ ^ 19
          + ((7 / 34) : ℂ) * ζ ^ 20
          + ((55 / 34) : ℂ) * ζ ^ 23
          - ((7 / 34) : ℂ) * ζ ^ 24
          + ((7 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry07_03 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (7 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 34) : ℂ)
          + ((7 / 34) : ℂ) * ζ ^ 4
          + ((21 / 17) : ℂ) * ζ ^ 5
          - ((7 / 34) : ℂ) * ζ ^ 8
          - ((21 / 17) : ℂ) * ζ ^ 9
          - ((41 / 34) : ℂ) * ζ ^ 10
          + ((21 / 17) : ℂ) * ζ ^ 13
          + ((41 / 34) : ℂ) * ζ ^ 14
          + ((5 / 34) : ℂ) * ζ ^ 15
          - ((41 / 34) : ℂ) * ζ ^ 18
          - ((5 / 34) : ℂ) * ζ ^ 19
          - ((15 / 17) : ℂ) * ζ ^ 20
          + ((5 / 34) : ℂ) * ζ ^ 23
          + ((15 / 17) : ℂ) * ζ ^ 24
          - ((15 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 34) : ℂ)
          + ((7 / 34) : ℂ) * ζ ^ 4
          + ((21 / 17) : ℂ) * ζ ^ 5
          - ((7 / 34) : ℂ) * ζ ^ 8
          - ((21 / 17) : ℂ) * ζ ^ 9
          - ((41 / 34) : ℂ) * ζ ^ 10
          + ((21 / 17) : ℂ) * ζ ^ 13
          + ((41 / 34) : ℂ) * ζ ^ 14
          + ((5 / 34) : ℂ) * ζ ^ 15
          - ((41 / 34) : ℂ) * ζ ^ 18
          - ((5 / 34) : ℂ) * ζ ^ 19
          - ((15 / 17) : ℂ) * ζ ^ 20
          + ((5 / 34) : ℂ) * ζ ^ 23
          + ((15 / 17) : ℂ) * ζ ^ 24
          - ((15 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry07_04 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (7 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((25 / 17) : ℂ)
          + ((25 / 17) : ℂ) * ζ ^ 4
          + ((63 / 34) : ℂ) * ζ ^ 5
          - ((25 / 17) : ℂ) * ζ ^ 8
          - ((63 / 34) : ℂ) * ζ ^ 9
          - ((31 / 34) : ℂ) * ζ ^ 10
          + ((63 / 34) : ℂ) * ζ ^ 13
          + ((31 / 34) : ℂ) * ζ ^ 14
          + ((11 / 34) : ℂ) * ζ ^ 15
          - ((31 / 34) : ℂ) * ζ ^ 18
          - ((11 / 34) : ℂ) * ζ ^ 19
          - ((12 / 17) : ℂ) * ζ ^ 20
          + ((11 / 34) : ℂ) * ζ ^ 23
          + ((12 / 17) : ℂ) * ζ ^ 24
          - ((12 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((25 / 17) : ℂ)
          + ((25 / 17) : ℂ) * ζ ^ 4
          + ((63 / 34) : ℂ) * ζ ^ 5
          - ((25 / 17) : ℂ) * ζ ^ 8
          - ((63 / 34) : ℂ) * ζ ^ 9
          - ((31 / 34) : ℂ) * ζ ^ 10
          + ((63 / 34) : ℂ) * ζ ^ 13
          + ((31 / 34) : ℂ) * ζ ^ 14
          + ((11 / 34) : ℂ) * ζ ^ 15
          - ((31 / 34) : ℂ) * ζ ^ 18
          - ((11 / 34) : ℂ) * ζ ^ 19
          - ((12 / 17) : ℂ) * ζ ^ 20
          + ((11 / 34) : ℂ) * ζ ^ 23
          + ((12 / 17) : ℂ) * ζ ^ 24
          - ((12 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry07_05 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (7 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((19 / 34) : ℂ)
          - ((19 / 34) : ℂ) * ζ ^ 4
          - ((31 / 34) : ℂ) * ζ ^ 5
          + ((19 / 34) : ℂ) * ζ ^ 8
          + ((31 / 34) : ℂ) * ζ ^ 9
          + ((16 / 17) : ℂ) * ζ ^ 10
          - ((31 / 34) : ℂ) * ζ ^ 13
          - ((16 / 17) : ℂ) * ζ ^ 14
          + ((5 / 34) : ℂ) * ζ ^ 15
          + ((16 / 17) : ℂ) * ζ ^ 18
          - ((5 / 34) : ℂ) * ζ ^ 19
          + ((1 / 34) : ℂ) * ζ ^ 20
          + ((5 / 34) : ℂ) * ζ ^ 23
          - ((1 / 34) : ℂ) * ζ ^ 24
          + ((1 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((19 / 34) : ℂ)
          - ((19 / 34) : ℂ) * ζ ^ 4
          - ((31 / 34) : ℂ) * ζ ^ 5
          + ((19 / 34) : ℂ) * ζ ^ 8
          + ((31 / 34) : ℂ) * ζ ^ 9
          + ((16 / 17) : ℂ) * ζ ^ 10
          - ((31 / 34) : ℂ) * ζ ^ 13
          - ((16 / 17) : ℂ) * ζ ^ 14
          + ((5 / 34) : ℂ) * ζ ^ 15
          + ((16 / 17) : ℂ) * ζ ^ 18
          - ((5 / 34) : ℂ) * ζ ^ 19
          + ((1 / 34) : ℂ) * ζ ^ 20
          + ((5 / 34) : ℂ) * ζ ^ 23
          - ((1 / 34) : ℂ) * ζ ^ 24
          + ((1 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry07_06 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (7 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((22 / 17) : ℂ)
          - ((22 / 17) : ℂ) * ζ ^ 4
          - ((13 / 17) : ℂ) * ζ ^ 5
          + ((22 / 17) : ℂ) * ζ ^ 8
          + ((13 / 17) : ℂ) * ζ ^ 9
          - ((12 / 17) : ℂ) * ζ ^ 10
          - ((13 / 17) : ℂ) * ζ ^ 13
          + ((12 / 17) : ℂ) * ζ ^ 14
          + ((9 / 34) : ℂ) * ζ ^ 15
          - ((12 / 17) : ℂ) * ζ ^ 18
          - ((9 / 34) : ℂ) * ζ ^ 19
          - ((39 / 34) : ℂ) * ζ ^ 20
          + ((9 / 34) : ℂ) * ζ ^ 23
          + ((39 / 34) : ℂ) * ζ ^ 24
          - ((39 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((22 / 17) : ℂ)
          - ((22 / 17) : ℂ) * ζ ^ 4
          - ((13 / 17) : ℂ) * ζ ^ 5
          + ((22 / 17) : ℂ) * ζ ^ 8
          + ((13 / 17) : ℂ) * ζ ^ 9
          - ((12 / 17) : ℂ) * ζ ^ 10
          - ((13 / 17) : ℂ) * ζ ^ 13
          + ((12 / 17) : ℂ) * ζ ^ 14
          + ((9 / 34) : ℂ) * ζ ^ 15
          - ((12 / 17) : ℂ) * ζ ^ 18
          - ((9 / 34) : ℂ) * ζ ^ 19
          - ((39 / 34) : ℂ) * ζ ^ 20
          + ((9 / 34) : ℂ) * ζ ^ 23
          + ((39 / 34) : ℂ) * ζ ^ 24
          - ((39 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry07_07 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (7 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((33 / 34) : ℂ)
          - ((33 / 34) : ℂ) * ζ ^ 4
          - ((3 / 34) : ℂ) * ζ ^ 5
          + ((33 / 34) : ℂ) * ζ ^ 8
          + ((3 / 34) : ℂ) * ζ ^ 9
          - ((1 / 17) : ℂ) * ζ ^ 10
          - ((3 / 34) : ℂ) * ζ ^ 13
          + ((1 / 17) : ℂ) * ζ ^ 14
          + ((1 / 34) : ℂ) * ζ ^ 15
          - ((1 / 17) : ℂ) * ζ ^ 18
          - ((1 / 34) : ℂ) * ζ ^ 19
          + ((27 / 34) : ℂ) * ζ ^ 20
          + ((1 / 34) : ℂ) * ζ ^ 23
          - ((27 / 34) : ℂ) * ζ ^ 24
          + ((27 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((33 / 34) : ℂ)
          - ((33 / 34) : ℂ) * ζ ^ 4
          - ((3 / 34) : ℂ) * ζ ^ 5
          + ((33 / 34) : ℂ) * ζ ^ 8
          + ((3 / 34) : ℂ) * ζ ^ 9
          - ((1 / 17) : ℂ) * ζ ^ 10
          - ((3 / 34) : ℂ) * ζ ^ 13
          + ((1 / 17) : ℂ) * ζ ^ 14
          + ((1 / 34) : ℂ) * ζ ^ 15
          - ((1 / 17) : ℂ) * ζ ^ 18
          - ((1 / 34) : ℂ) * ζ ^ 19
          + ((27 / 34) : ℂ) * ζ ^ 20
          + ((1 / 34) : ℂ) * ζ ^ 23
          - ((27 / 34) : ℂ) * ζ ^ 24
          + ((27 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry07_08 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (7 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((19 / 17) : ℂ)
          + ((19 / 17) : ℂ) * ζ ^ 4
          + ((27 / 17) : ℂ) * ζ ^ 5
          - ((19 / 17) : ℂ) * ζ ^ 8
          - ((27 / 17) : ℂ) * ζ ^ 9
          - ((6 / 17) : ℂ) * ζ ^ 10
          + ((27 / 17) : ℂ) * ζ ^ 13
          + ((6 / 17) : ℂ) * ζ ^ 14
          - ((3 / 17) : ℂ) * ζ ^ 15
          - ((6 / 17) : ℂ) * ζ ^ 18
          + ((3 / 17) : ℂ) * ζ ^ 19
          - ((16 / 17) : ℂ) * ζ ^ 20
          - ((3 / 17) : ℂ) * ζ ^ 23
          + ((16 / 17) : ℂ) * ζ ^ 24
          - ((16 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((19 / 17) : ℂ)
          + ((19 / 17) : ℂ) * ζ ^ 4
          + ((27 / 17) : ℂ) * ζ ^ 5
          - ((19 / 17) : ℂ) * ζ ^ 8
          - ((27 / 17) : ℂ) * ζ ^ 9
          - ((6 / 17) : ℂ) * ζ ^ 10
          + ((27 / 17) : ℂ) * ζ ^ 13
          + ((6 / 17) : ℂ) * ζ ^ 14
          - ((3 / 17) : ℂ) * ζ ^ 15
          - ((6 / 17) : ℂ) * ζ ^ 18
          + ((3 / 17) : ℂ) * ζ ^ 19
          - ((16 / 17) : ℂ) * ζ ^ 20
          - ((3 / 17) : ℂ) * ζ ^ 23
          + ((16 / 17) : ℂ) * ζ ^ 24
          - ((16 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry07_09 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (7 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((16 / 17) : ℂ)
          + ((16 / 17) : ℂ) * ζ ^ 4
          - ((41 / 34) : ℂ) * ζ ^ 5
          - ((16 / 17) : ℂ) * ζ ^ 8
          + ((41 / 34) : ℂ) * ζ ^ 9
          + ((29 / 34) : ℂ) * ζ ^ 10
          - ((41 / 34) : ℂ) * ζ ^ 13
          - ((29 / 34) : ℂ) * ζ ^ 14
          + ((1 / 34) : ℂ) * ζ ^ 15
          + ((29 / 34) : ℂ) * ζ ^ 18
          - ((1 / 34) : ℂ) * ζ ^ 19
          - ((6 / 17) : ℂ) * ζ ^ 20
          + ((1 / 34) : ℂ) * ζ ^ 23
          + ((6 / 17) : ℂ) * ζ ^ 24
          - ((6 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((16 / 17) : ℂ)
          + ((16 / 17) : ℂ) * ζ ^ 4
          - ((41 / 34) : ℂ) * ζ ^ 5
          - ((16 / 17) : ℂ) * ζ ^ 8
          + ((41 / 34) : ℂ) * ζ ^ 9
          + ((29 / 34) : ℂ) * ζ ^ 10
          - ((41 / 34) : ℂ) * ζ ^ 13
          - ((29 / 34) : ℂ) * ζ ^ 14
          + ((1 / 34) : ℂ) * ζ ^ 15
          + ((29 / 34) : ℂ) * ζ ^ 18
          - ((1 / 34) : ℂ) * ζ ^ 19
          - ((6 / 17) : ℂ) * ζ ^ 20
          + ((1 / 34) : ℂ) * ζ ^ 23
          + ((6 / 17) : ℂ) * ζ ^ 24
          - ((6 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry08_00 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (8 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 34) : ℂ)
          + ((7 / 34) : ℂ) * ζ ^ 4
          - ((55 / 34) : ℂ) * ζ ^ 5
          - ((7 / 34) : ℂ) * ζ ^ 8
          + ((55 / 34) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 10
          - ((55 / 34) : ℂ) * ζ ^ 13
          + ((7 / 17) : ℂ) * ζ ^ 14
          + ((23 / 17) : ℂ) * ζ ^ 15
          - ((7 / 17) : ℂ) * ζ ^ 18
          - ((23 / 17) : ℂ) * ζ ^ 19
          - ((28 / 17) : ℂ) * ζ ^ 20
          + ((23 / 17) : ℂ) * ζ ^ 23
          + ((28 / 17) : ℂ) * ζ ^ 24
          - ((28 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 34) : ℂ)
          + ((7 / 34) : ℂ) * ζ ^ 4
          - ((55 / 34) : ℂ) * ζ ^ 5
          - ((7 / 34) : ℂ) * ζ ^ 8
          + ((55 / 34) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 10
          - ((55 / 34) : ℂ) * ζ ^ 13
          + ((7 / 17) : ℂ) * ζ ^ 14
          + ((23 / 17) : ℂ) * ζ ^ 15
          - ((7 / 17) : ℂ) * ζ ^ 18
          - ((23 / 17) : ℂ) * ζ ^ 19
          - ((28 / 17) : ℂ) * ζ ^ 20
          + ((23 / 17) : ℂ) * ζ ^ 23
          + ((28 / 17) : ℂ) * ζ ^ 24
          - ((28 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry08_01 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (8 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((9 / 34) : ℂ)
          - ((9 / 34) : ℂ) * ζ ^ 4
          - ((14 / 17) : ℂ) * ζ ^ 5
          + ((9 / 34) : ℂ) * ζ ^ 8
          + ((14 / 17) : ℂ) * ζ ^ 9
          - ((7 / 34) : ℂ) * ζ ^ 10
          - ((14 / 17) : ℂ) * ζ ^ 13
          + ((7 / 34) : ℂ) * ζ ^ 14
          + ((13 / 17) : ℂ) * ζ ^ 15
          - ((7 / 34) : ℂ) * ζ ^ 18
          - ((13 / 17) : ℂ) * ζ ^ 19
          - ((5 / 34) : ℂ) * ζ ^ 20
          + ((13 / 17) : ℂ) * ζ ^ 23
          + ((5 / 34) : ℂ) * ζ ^ 24
          - ((5 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((9 / 34) : ℂ)
          - ((9 / 34) : ℂ) * ζ ^ 4
          - ((14 / 17) : ℂ) * ζ ^ 5
          + ((9 / 34) : ℂ) * ζ ^ 8
          + ((14 / 17) : ℂ) * ζ ^ 9
          - ((7 / 34) : ℂ) * ζ ^ 10
          - ((14 / 17) : ℂ) * ζ ^ 13
          + ((7 / 34) : ℂ) * ζ ^ 14
          + ((13 / 17) : ℂ) * ζ ^ 15
          - ((7 / 34) : ℂ) * ζ ^ 18
          - ((13 / 17) : ℂ) * ζ ^ 19
          - ((5 / 34) : ℂ) * ζ ^ 20
          + ((13 / 17) : ℂ) * ζ ^ 23
          + ((5 / 34) : ℂ) * ζ ^ 24
          - ((5 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry08_02 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (8 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((21 / 17) : ℂ)
          - ((21 / 17) : ℂ) * ζ ^ 4
          - ((22 / 17) : ℂ) * ζ ^ 5
          + ((21 / 17) : ℂ) * ζ ^ 8
          + ((22 / 17) : ℂ) * ζ ^ 9
          - ((9 / 17) : ℂ) * ζ ^ 10
          - ((22 / 17) : ℂ) * ζ ^ 13
          + ((9 / 17) : ℂ) * ζ ^ 14
          - ((61 / 34) : ℂ) * ζ ^ 15
          - ((9 / 17) : ℂ) * ζ ^ 18
          + ((61 / 34) : ℂ) * ζ ^ 19
          + ((35 / 34) : ℂ) * ζ ^ 20
          - ((61 / 34) : ℂ) * ζ ^ 23
          - ((35 / 34) : ℂ) * ζ ^ 24
          + ((35 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((21 / 17) : ℂ)
          - ((21 / 17) : ℂ) * ζ ^ 4
          - ((22 / 17) : ℂ) * ζ ^ 5
          + ((21 / 17) : ℂ) * ζ ^ 8
          + ((22 / 17) : ℂ) * ζ ^ 9
          - ((9 / 17) : ℂ) * ζ ^ 10
          - ((22 / 17) : ℂ) * ζ ^ 13
          + ((9 / 17) : ℂ) * ζ ^ 14
          - ((61 / 34) : ℂ) * ζ ^ 15
          - ((9 / 17) : ℂ) * ζ ^ 18
          + ((61 / 34) : ℂ) * ζ ^ 19
          + ((35 / 34) : ℂ) * ζ ^ 20
          - ((61 / 34) : ℂ) * ζ ^ 23
          - ((35 / 34) : ℂ) * ζ ^ 24
          + ((35 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry08_03 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (8 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 17) : ℂ)
          + ((1 / 17) : ℂ) * ζ ^ 4
          + ((15 / 17) : ℂ) * ζ ^ 5
          - ((1 / 17) : ℂ) * ζ ^ 8
          - ((15 / 17) : ℂ) * ζ ^ 9
          + ζ ^ 10
          + ((15 / 17) : ℂ) * ζ ^ 13
          - ζ ^ 14
          - ((3 / 2) : ℂ) * ζ ^ 15
          + ζ ^ 18
          + ((3 / 2) : ℂ) * ζ ^ 19
          + ((3 / 2) : ℂ) * ζ ^ 20
          - ((3 / 2) : ℂ) * ζ ^ 23
          - ((3 / 2) : ℂ) * ζ ^ 24
          + ((3 / 2) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 17) : ℂ)
          + ((1 / 17) : ℂ) * ζ ^ 4
          + ((15 / 17) : ℂ) * ζ ^ 5
          - ((1 / 17) : ℂ) * ζ ^ 8
          - ((15 / 17) : ℂ) * ζ ^ 9
          + ζ ^ 10
          + ((15 / 17) : ℂ) * ζ ^ 13
          - ζ ^ 14
          - ((3 / 2) : ℂ) * ζ ^ 15
          + ζ ^ 18
          + ((3 / 2) : ℂ) * ζ ^ 19
          + ((3 / 2) : ℂ) * ζ ^ 20
          - ((3 / 2) : ℂ) * ζ ^ 23
          - ((3 / 2) : ℂ) * ζ ^ 24
          + ((3 / 2) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry08_04 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (8 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((35 / 17) : ℂ)
          + ((35 / 17) : ℂ) * ζ ^ 4
          + ((57 / 34) : ℂ) * ζ ^ 5
          - ((35 / 17) : ℂ) * ζ ^ 8
          - ((57 / 34) : ℂ) * ζ ^ 9
          + ((71 / 34) : ℂ) * ζ ^ 10
          + ((57 / 34) : ℂ) * ζ ^ 13
          - ((71 / 34) : ℂ) * ζ ^ 14
          + ((7 / 34) : ℂ) * ζ ^ 15
          + ((71 / 34) : ℂ) * ζ ^ 18
          - ((7 / 34) : ℂ) * ζ ^ 19
          + ((1 / 17) : ℂ) * ζ ^ 20
          + ((7 / 34) : ℂ) * ζ ^ 23
          - ((1 / 17) : ℂ) * ζ ^ 24
          + ((1 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((35 / 17) : ℂ)
          + ((35 / 17) : ℂ) * ζ ^ 4
          + ((57 / 34) : ℂ) * ζ ^ 5
          - ((35 / 17) : ℂ) * ζ ^ 8
          - ((57 / 34) : ℂ) * ζ ^ 9
          + ((71 / 34) : ℂ) * ζ ^ 10
          + ((57 / 34) : ℂ) * ζ ^ 13
          - ((71 / 34) : ℂ) * ζ ^ 14
          + ((7 / 34) : ℂ) * ζ ^ 15
          + ((71 / 34) : ℂ) * ζ ^ 18
          - ((7 / 34) : ℂ) * ζ ^ 19
          + ((1 / 17) : ℂ) * ζ ^ 20
          + ((7 / 34) : ℂ) * ζ ^ 23
          - ((1 / 17) : ℂ) * ζ ^ 24
          + ((1 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry08_05 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (8 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((9 / 17) : ℂ)
          - ((9 / 17) : ℂ) * ζ ^ 4
          - ((21 / 34) : ℂ) * ζ ^ 5
          + ((9 / 17) : ℂ) * ζ ^ 8
          + ((21 / 34) : ℂ) * ζ ^ 9
          - ((29 / 34) : ℂ) * ζ ^ 10
          - ((21 / 34) : ℂ) * ζ ^ 13
          + ((29 / 34) : ℂ) * ζ ^ 14
          + ((27 / 34) : ℂ) * ζ ^ 15
          - ((29 / 34) : ℂ) * ζ ^ 18
          - ((27 / 34) : ℂ) * ζ ^ 19
          - ζ ^ 20
          + ((27 / 34) : ℂ) * ζ ^ 23
          + ζ ^ 24
          - ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((9 / 17) : ℂ)
          - ((9 / 17) : ℂ) * ζ ^ 4
          - ((21 / 34) : ℂ) * ζ ^ 5
          + ((9 / 17) : ℂ) * ζ ^ 8
          + ((21 / 34) : ℂ) * ζ ^ 9
          - ((29 / 34) : ℂ) * ζ ^ 10
          - ((21 / 34) : ℂ) * ζ ^ 13
          + ((29 / 34) : ℂ) * ζ ^ 14
          + ((27 / 34) : ℂ) * ζ ^ 15
          - ((29 / 34) : ℂ) * ζ ^ 18
          - ((27 / 34) : ℂ) * ζ ^ 19
          - ζ ^ 20
          + ((27 / 34) : ℂ) * ζ ^ 23
          + ζ ^ 24
          - ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry08_06 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (8 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((8 / 17) : ℂ)
          - ((8 / 17) : ℂ) * ζ ^ 4
          + ((19 / 17) : ℂ) * ζ ^ 5
          + ((8 / 17) : ℂ) * ζ ^ 8
          - ((19 / 17) : ℂ) * ζ ^ 9
          + ((6 / 17) : ℂ) * ζ ^ 10
          + ((19 / 17) : ℂ) * ζ ^ 13
          - ((6 / 17) : ℂ) * ζ ^ 14
          + ((11 / 34) : ℂ) * ζ ^ 15
          + ((6 / 17) : ℂ) * ζ ^ 18
          - ((11 / 34) : ℂ) * ζ ^ 19
          + ((25 / 34) : ℂ) * ζ ^ 20
          + ((11 / 34) : ℂ) * ζ ^ 23
          - ((25 / 34) : ℂ) * ζ ^ 24
          + ((25 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((8 / 17) : ℂ)
          - ((8 / 17) : ℂ) * ζ ^ 4
          + ((19 / 17) : ℂ) * ζ ^ 5
          + ((8 / 17) : ℂ) * ζ ^ 8
          - ((19 / 17) : ℂ) * ζ ^ 9
          + ((6 / 17) : ℂ) * ζ ^ 10
          + ((19 / 17) : ℂ) * ζ ^ 13
          - ((6 / 17) : ℂ) * ζ ^ 14
          + ((11 / 34) : ℂ) * ζ ^ 15
          + ((6 / 17) : ℂ) * ζ ^ 18
          - ((11 / 34) : ℂ) * ζ ^ 19
          + ((25 / 34) : ℂ) * ζ ^ 20
          + ((11 / 34) : ℂ) * ζ ^ 23
          - ((25 / 34) : ℂ) * ζ ^ 24
          + ((25 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry08_07 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (8 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 34) : ℂ)
          - ((1 / 34) : ℂ) * ζ ^ 4
          - ((7 / 34) : ℂ) * ζ ^ 5
          + ((1 / 34) : ℂ) * ζ ^ 8
          + ((7 / 34) : ℂ) * ζ ^ 9
          + ((8 / 17) : ℂ) * ζ ^ 10
          - ((7 / 34) : ℂ) * ζ ^ 13
          - ((8 / 17) : ℂ) * ζ ^ 14
          - ((15 / 34) : ℂ) * ζ ^ 15
          + ((8 / 17) : ℂ) * ζ ^ 18
          + ((15 / 34) : ℂ) * ζ ^ 19
          - ((9 / 34) : ℂ) * ζ ^ 20
          - ((15 / 34) : ℂ) * ζ ^ 23
          + ((9 / 34) : ℂ) * ζ ^ 24
          - ((9 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 34) : ℂ)
          - ((1 / 34) : ℂ) * ζ ^ 4
          - ((7 / 34) : ℂ) * ζ ^ 5
          + ((1 / 34) : ℂ) * ζ ^ 8
          + ((7 / 34) : ℂ) * ζ ^ 9
          + ((8 / 17) : ℂ) * ζ ^ 10
          - ((7 / 34) : ℂ) * ζ ^ 13
          - ((8 / 17) : ℂ) * ζ ^ 14
          - ((15 / 34) : ℂ) * ζ ^ 15
          + ((8 / 17) : ℂ) * ζ ^ 18
          + ((15 / 34) : ℂ) * ζ ^ 19
          - ((9 / 34) : ℂ) * ζ ^ 20
          - ((15 / 34) : ℂ) * ζ ^ 23
          + ((9 / 34) : ℂ) * ζ ^ 24
          - ((9 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry08_08 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (8 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 17) : ℂ)
          + ((7 / 17) : ℂ) * ζ ^ 4
          + ((19 / 17) : ℂ) * ζ ^ 5
          - ((7 / 17) : ℂ) * ζ ^ 8
          - ((19 / 17) : ℂ) * ζ ^ 9
          + ((15 / 17) : ℂ) * ζ ^ 10
          + ((19 / 17) : ℂ) * ζ ^ 13
          - ((15 / 17) : ℂ) * ζ ^ 14
          + ((16 / 17) : ℂ) * ζ ^ 15
          + ((15 / 17) : ℂ) * ζ ^ 18
          - ((16 / 17) : ℂ) * ζ ^ 19
          - ((11 / 17) : ℂ) * ζ ^ 20
          + ((16 / 17) : ℂ) * ζ ^ 23
          + ((11 / 17) : ℂ) * ζ ^ 24
          - ((11 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 17) : ℂ)
          + ((7 / 17) : ℂ) * ζ ^ 4
          + ((19 / 17) : ℂ) * ζ ^ 5
          - ((7 / 17) : ℂ) * ζ ^ 8
          - ((19 / 17) : ℂ) * ζ ^ 9
          + ((15 / 17) : ℂ) * ζ ^ 10
          + ((19 / 17) : ℂ) * ζ ^ 13
          - ((15 / 17) : ℂ) * ζ ^ 14
          + ((16 / 17) : ℂ) * ζ ^ 15
          + ((15 / 17) : ℂ) * ζ ^ 18
          - ((16 / 17) : ℂ) * ζ ^ 19
          - ((11 / 17) : ℂ) * ζ ^ 20
          + ((16 / 17) : ℂ) * ζ ^ 23
          + ((11 / 17) : ℂ) * ζ ^ 24
          - ((11 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry08_09 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (8 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((45 / 34) : ℂ)
          - ((45 / 34) : ℂ) * ζ ^ 4
          - ((81 / 34) : ℂ) * ζ ^ 5
          + ((45 / 34) : ℂ) * ζ ^ 8
          + ((81 / 34) : ℂ) * ζ ^ 9
          - ((18 / 17) : ℂ) * ζ ^ 10
          - ((81 / 34) : ℂ) * ζ ^ 13
          + ((18 / 17) : ℂ) * ζ ^ 14
          - ((37 / 34) : ℂ) * ζ ^ 15
          - ((18 / 17) : ℂ) * ζ ^ 18
          + ((37 / 34) : ℂ) * ζ ^ 19
          + ((19 / 34) : ℂ) * ζ ^ 20
          - ((37 / 34) : ℂ) * ζ ^ 23
          - ((19 / 34) : ℂ) * ζ ^ 24
          + ((19 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((45 / 34) : ℂ)
          - ((45 / 34) : ℂ) * ζ ^ 4
          - ((81 / 34) : ℂ) * ζ ^ 5
          + ((45 / 34) : ℂ) * ζ ^ 8
          + ((81 / 34) : ℂ) * ζ ^ 9
          - ((18 / 17) : ℂ) * ζ ^ 10
          - ((81 / 34) : ℂ) * ζ ^ 13
          + ((18 / 17) : ℂ) * ζ ^ 14
          - ((37 / 34) : ℂ) * ζ ^ 15
          - ((18 / 17) : ℂ) * ζ ^ 18
          + ((37 / 34) : ℂ) * ζ ^ 19
          + ((19 / 34) : ℂ) * ζ ^ 20
          - ((37 / 34) : ℂ) * ζ ^ 23
          - ((19 / 34) : ℂ) * ζ ^ 24
          + ((19 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry09_00 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (9 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((22 / 17) : ℂ)
          - ((22 / 17) : ℂ) * ζ ^ 4
          - ((21 / 34) : ℂ) * ζ ^ 5
          + ((22 / 17) : ℂ) * ζ ^ 8
          + ((21 / 34) : ℂ) * ζ ^ 9
          + ((3 / 34) : ℂ) * ζ ^ 10
          - ((21 / 34) : ℂ) * ζ ^ 13
          - ((3 / 34) : ℂ) * ζ ^ 14
          + ((37 / 34) : ℂ) * ζ ^ 15
          + ((3 / 34) : ℂ) * ζ ^ 18
          - ((37 / 34) : ℂ) * ζ ^ 19
          + ((14 / 17) : ℂ) * ζ ^ 20
          + ((37 / 34) : ℂ) * ζ ^ 23
          - ((14 / 17) : ℂ) * ζ ^ 24
          + ((14 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((22 / 17) : ℂ)
          - ((22 / 17) : ℂ) * ζ ^ 4
          - ((21 / 34) : ℂ) * ζ ^ 5
          + ((22 / 17) : ℂ) * ζ ^ 8
          + ((21 / 34) : ℂ) * ζ ^ 9
          + ((3 / 34) : ℂ) * ζ ^ 10
          - ((21 / 34) : ℂ) * ζ ^ 13
          - ((3 / 34) : ℂ) * ζ ^ 14
          + ((37 / 34) : ℂ) * ζ ^ 15
          + ((3 / 34) : ℂ) * ζ ^ 18
          - ((37 / 34) : ℂ) * ζ ^ 19
          + ((14 / 17) : ℂ) * ζ ^ 20
          + ((37 / 34) : ℂ) * ζ ^ 23
          - ((14 / 17) : ℂ) * ζ ^ 24
          + ((14 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry09_01 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (9 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((15 / 34) : ℂ)
          + ((15 / 34) : ℂ) * ζ ^ 4
          - ((6 / 17) : ℂ) * ζ ^ 5
          - ((15 / 34) : ℂ) * ζ ^ 8
          + ((6 / 17) : ℂ) * ζ ^ 9
          - ((15 / 34) : ℂ) * ζ ^ 10
          - ((6 / 17) : ℂ) * ζ ^ 13
          + ((15 / 34) : ℂ) * ζ ^ 14
          - ((1 / 17) : ℂ) * ζ ^ 15
          - ((15 / 34) : ℂ) * ζ ^ 18
          + ((1 / 17) : ℂ) * ζ ^ 19
          + ((5 / 34) : ℂ) * ζ ^ 20
          - ((1 / 17) : ℂ) * ζ ^ 23
          - ((5 / 34) : ℂ) * ζ ^ 24
          + ((5 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((15 / 34) : ℂ)
          + ((15 / 34) : ℂ) * ζ ^ 4
          - ((6 / 17) : ℂ) * ζ ^ 5
          - ((15 / 34) : ℂ) * ζ ^ 8
          + ((6 / 17) : ℂ) * ζ ^ 9
          - ((15 / 34) : ℂ) * ζ ^ 10
          - ((6 / 17) : ℂ) * ζ ^ 13
          + ((15 / 34) : ℂ) * ζ ^ 14
          - ((1 / 17) : ℂ) * ζ ^ 15
          - ((15 / 34) : ℂ) * ζ ^ 18
          + ((1 / 17) : ℂ) * ζ ^ 19
          + ((5 / 34) : ℂ) * ζ ^ 20
          - ((1 / 17) : ℂ) * ζ ^ 23
          - ((5 / 34) : ℂ) * ζ ^ 24
          + ((5 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry09_02 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (9 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((4 / 17) : ℂ)
          - ((4 / 17) : ℂ) * ζ ^ 4
          + ((29 / 17) : ℂ) * ζ ^ 5
          + ((4 / 17) : ℂ) * ζ ^ 8
          - ((29 / 17) : ℂ) * ζ ^ 9
          - ((9 / 17) : ℂ) * ζ ^ 10
          + ((29 / 17) : ℂ) * ζ ^ 13
          + ((9 / 17) : ℂ) * ζ ^ 14
          - ((11 / 34) : ℂ) * ζ ^ 15
          - ((9 / 17) : ℂ) * ζ ^ 18
          + ((11 / 34) : ℂ) * ζ ^ 19
          - ((1 / 34) : ℂ) * ζ ^ 20
          - ((11 / 34) : ℂ) * ζ ^ 23
          + ((1 / 34) : ℂ) * ζ ^ 24
          - ((1 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((4 / 17) : ℂ)
          - ((4 / 17) : ℂ) * ζ ^ 4
          + ((29 / 17) : ℂ) * ζ ^ 5
          + ((4 / 17) : ℂ) * ζ ^ 8
          - ((29 / 17) : ℂ) * ζ ^ 9
          - ((9 / 17) : ℂ) * ζ ^ 10
          + ((29 / 17) : ℂ) * ζ ^ 13
          + ((9 / 17) : ℂ) * ζ ^ 14
          - ((11 / 34) : ℂ) * ζ ^ 15
          - ((9 / 17) : ℂ) * ζ ^ 18
          + ((11 / 34) : ℂ) * ζ ^ 19
          - ((1 / 34) : ℂ) * ζ ^ 20
          - ((11 / 34) : ℂ) * ζ ^ 23
          + ((1 / 34) : ℂ) * ζ ^ 24
          - ((1 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry09_03 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (9 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((19 / 34) : ℂ)
          - ((19 / 34) : ℂ) * ζ ^ 4
          - ((1 / 17) : ℂ) * ζ ^ 5
          + ((19 / 34) : ℂ) * ζ ^ 8
          + ((1 / 17) : ℂ) * ζ ^ 9
          + ((5 / 34) : ℂ) * ζ ^ 10
          - ((1 / 17) : ℂ) * ζ ^ 13
          - ((5 / 34) : ℂ) * ζ ^ 14
          - ζ ^ 15
          + ((5 / 34) : ℂ) * ζ ^ 18
          + ζ ^ 19
          - ((37 / 34) : ℂ) * ζ ^ 20
          - ζ ^ 23
          + ((37 / 34) : ℂ) * ζ ^ 24
          - ((37 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((19 / 34) : ℂ)
          - ((19 / 34) : ℂ) * ζ ^ 4
          - ((1 / 17) : ℂ) * ζ ^ 5
          + ((19 / 34) : ℂ) * ζ ^ 8
          + ((1 / 17) : ℂ) * ζ ^ 9
          + ((5 / 34) : ℂ) * ζ ^ 10
          - ((1 / 17) : ℂ) * ζ ^ 13
          - ((5 / 34) : ℂ) * ζ ^ 14
          - ζ ^ 15
          + ((5 / 34) : ℂ) * ζ ^ 18
          + ζ ^ 19
          - ((37 / 34) : ℂ) * ζ ^ 20
          - ζ ^ 23
          + ((37 / 34) : ℂ) * ζ ^ 24
          - ((37 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry09_04 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (9 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((13 / 17) : ℂ)
          - ((13 / 17) : ℂ) * ζ ^ 4
          - ((55 / 34) : ℂ) * ζ ^ 5
          + ((13 / 17) : ℂ) * ζ ^ 8
          + ((55 / 34) : ℂ) * ζ ^ 9
          + ((41 / 34) : ℂ) * ζ ^ 10
          - ((55 / 34) : ℂ) * ζ ^ 13
          - ((41 / 34) : ℂ) * ζ ^ 14
          - ((45 / 34) : ℂ) * ζ ^ 15
          + ((41 / 34) : ℂ) * ζ ^ 18
          + ((45 / 34) : ℂ) * ζ ^ 19
          - ((8 / 17) : ℂ) * ζ ^ 20
          - ((45 / 34) : ℂ) * ζ ^ 23
          + ((8 / 17) : ℂ) * ζ ^ 24
          - ((8 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((13 / 17) : ℂ)
          - ((13 / 17) : ℂ) * ζ ^ 4
          - ((55 / 34) : ℂ) * ζ ^ 5
          + ((13 / 17) : ℂ) * ζ ^ 8
          + ((55 / 34) : ℂ) * ζ ^ 9
          + ((41 / 34) : ℂ) * ζ ^ 10
          - ((55 / 34) : ℂ) * ζ ^ 13
          - ((41 / 34) : ℂ) * ζ ^ 14
          - ((45 / 34) : ℂ) * ζ ^ 15
          + ((41 / 34) : ℂ) * ζ ^ 18
          + ((45 / 34) : ℂ) * ζ ^ 19
          - ((8 / 17) : ℂ) * ζ ^ 20
          - ((45 / 34) : ℂ) * ζ ^ 23
          + ((8 / 17) : ℂ) * ζ ^ 24
          - ((8 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry09_05 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (9 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((31 / 34) : ℂ)
          + ((31 / 34) : ℂ) * ζ ^ 4
          + ((3 / 34) : ℂ) * ζ ^ 5
          - ((31 / 34) : ℂ) * ζ ^ 8
          - ((3 / 34) : ℂ) * ζ ^ 9
          - ((3 / 17) : ℂ) * ζ ^ 10
          + ((3 / 34) : ℂ) * ζ ^ 13
          + ((3 / 17) : ℂ) * ζ ^ 14
          - ((3 / 17) : ℂ) * ζ ^ 15
          - ((3 / 17) : ℂ) * ζ ^ 18
          + ((3 / 17) : ℂ) * ζ ^ 19
          + ((6 / 17) : ℂ) * ζ ^ 20
          - ((3 / 17) : ℂ) * ζ ^ 23
          - ((6 / 17) : ℂ) * ζ ^ 24
          + ((6 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((31 / 34) : ℂ)
          + ((31 / 34) : ℂ) * ζ ^ 4
          + ((3 / 34) : ℂ) * ζ ^ 5
          - ((31 / 34) : ℂ) * ζ ^ 8
          - ((3 / 34) : ℂ) * ζ ^ 9
          - ((3 / 17) : ℂ) * ζ ^ 10
          + ((3 / 34) : ℂ) * ζ ^ 13
          + ((3 / 17) : ℂ) * ζ ^ 14
          - ((3 / 17) : ℂ) * ζ ^ 15
          - ((3 / 17) : ℂ) * ζ ^ 18
          + ((3 / 17) : ℂ) * ζ ^ 19
          + ((6 / 17) : ℂ) * ζ ^ 20
          - ((3 / 17) : ℂ) * ζ ^ 23
          - ((6 / 17) : ℂ) * ζ ^ 24
          + ((6 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry09_06 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (9 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((26 / 17) : ℂ)
          + ((26 / 17) : ℂ) * ζ ^ 4
          - ((24 / 17) : ℂ) * ζ ^ 5
          - ((26 / 17) : ℂ) * ζ ^ 8
          + ((24 / 17) : ℂ) * ζ ^ 9
          + ((5 / 17) : ℂ) * ζ ^ 10
          - ((24 / 17) : ℂ) * ζ ^ 13
          - ((5 / 17) : ℂ) * ζ ^ 14
          - ((61 / 34) : ℂ) * ζ ^ 15
          + ((5 / 17) : ℂ) * ζ ^ 18
          + ((61 / 34) : ℂ) * ζ ^ 19
          - ((9 / 34) : ℂ) * ζ ^ 20
          - ((61 / 34) : ℂ) * ζ ^ 23
          + ((9 / 34) : ℂ) * ζ ^ 24
          - ((9 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((26 / 17) : ℂ)
          + ((26 / 17) : ℂ) * ζ ^ 4
          - ((24 / 17) : ℂ) * ζ ^ 5
          - ((26 / 17) : ℂ) * ζ ^ 8
          + ((24 / 17) : ℂ) * ζ ^ 9
          + ((5 / 17) : ℂ) * ζ ^ 10
          - ((24 / 17) : ℂ) * ζ ^ 13
          - ((5 / 17) : ℂ) * ζ ^ 14
          - ((61 / 34) : ℂ) * ζ ^ 15
          + ((5 / 17) : ℂ) * ζ ^ 18
          + ((61 / 34) : ℂ) * ζ ^ 19
          - ((9 / 34) : ℂ) * ζ ^ 20
          - ((61 / 34) : ℂ) * ζ ^ 23
          + ((9 / 34) : ℂ) * ζ ^ 24
          - ((9 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry09_07 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (9 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((23 / 34) : ℂ)
          + ((23 / 34) : ℂ) * ζ ^ 4
          + ((5 / 34) : ℂ) * ζ ^ 5
          - ((23 / 34) : ℂ) * ζ ^ 8
          - ((5 / 34) : ℂ) * ζ ^ 9
          + ((5 / 34) : ℂ) * ζ ^ 13
          + ((43 / 34) : ℂ) * ζ ^ 15
          - ((43 / 34) : ℂ) * ζ ^ 19
          + ((1 / 34) : ℂ) * ζ ^ 20
          + ((43 / 34) : ℂ) * ζ ^ 23
          - ((1 / 34) : ℂ) * ζ ^ 24
          + ((1 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((23 / 34) : ℂ)
          + ((23 / 34) : ℂ) * ζ ^ 4
          + ((5 / 34) : ℂ) * ζ ^ 5
          - ((23 / 34) : ℂ) * ζ ^ 8
          - ((5 / 34) : ℂ) * ζ ^ 9
          + ((5 / 34) : ℂ) * ζ ^ 13
          + ((43 / 34) : ℂ) * ζ ^ 15
          - ((43 / 34) : ℂ) * ζ ^ 19
          + ((1 / 34) : ℂ) * ζ ^ 20
          + ((43 / 34) : ℂ) * ζ ^ 23
          - ((1 / 34) : ℂ) * ζ ^ 24
          + ((1 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry09_08 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (9 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((2 / 17) : ℂ)
          + ((2 / 17) : ℂ) * ζ ^ 4
          - ((30 / 17) : ℂ) * ζ ^ 5
          - ((2 / 17) : ℂ) * ζ ^ 8
          + ((30 / 17) : ℂ) * ζ ^ 9
          + ((33 / 17) : ℂ) * ζ ^ 10
          - ((30 / 17) : ℂ) * ζ ^ 13
          - ((33 / 17) : ℂ) * ζ ^ 14
          - ((30 / 17) : ℂ) * ζ ^ 15
          + ((33 / 17) : ℂ) * ζ ^ 18
          + ((30 / 17) : ℂ) * ζ ^ 19
          - ((5 / 17) : ℂ) * ζ ^ 20
          - ((30 / 17) : ℂ) * ζ ^ 23
          + ((5 / 17) : ℂ) * ζ ^ 24
          - ((5 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((2 / 17) : ℂ)
          + ((2 / 17) : ℂ) * ζ ^ 4
          - ((30 / 17) : ℂ) * ζ ^ 5
          - ((2 / 17) : ℂ) * ζ ^ 8
          + ((30 / 17) : ℂ) * ζ ^ 9
          + ((33 / 17) : ℂ) * ζ ^ 10
          - ((30 / 17) : ℂ) * ζ ^ 13
          - ((33 / 17) : ℂ) * ζ ^ 14
          - ((30 / 17) : ℂ) * ζ ^ 15
          + ((33 / 17) : ℂ) * ζ ^ 18
          + ((30 / 17) : ℂ) * ζ ^ 19
          - ((5 / 17) : ℂ) * ζ ^ 20
          - ((30 / 17) : ℂ) * ζ ^ 23
          + ((5 / 17) : ℂ) * ζ ^ 24
          - ((5 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixABBB_entry09_09 :
    (alternatingSixAmbientRow24LongMatrixABB
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixABBB
        (9 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((12 / 17) : ℂ)
          - ((12 / 17) : ℂ) * ζ ^ 4
          + ((35 / 34) : ℂ) * ζ ^ 5
          + ((12 / 17) : ℂ) * ζ ^ 8
          - ((35 / 34) : ℂ) * ζ ^ 9
          - ((43 / 34) : ℂ) * ζ ^ 10
          + ((35 / 34) : ℂ) * ζ ^ 13
          + ((43 / 34) : ℂ) * ζ ^ 14
          + ((6 / 17) : ℂ) * ζ ^ 15
          - ((43 / 34) : ℂ) * ζ ^ 18
          - ((6 / 17) : ℂ) * ζ ^ 19
          + ((9 / 34) : ℂ) * ζ ^ 20
          + ((6 / 17) : ℂ) * ζ ^ 23
          - ((9 / 34) : ℂ) * ζ ^ 24
          + ((9 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((12 / 17) : ℂ)
          - ((12 / 17) : ℂ) * ζ ^ 4
          + ((35 / 34) : ℂ) * ζ ^ 5
          + ((12 / 17) : ℂ) * ζ ^ 8
          - ((35 / 34) : ℂ) * ζ ^ 9
          - ((43 / 34) : ℂ) * ζ ^ 10
          + ((35 / 34) : ℂ) * ζ ^ 13
          + ((43 / 34) : ℂ) * ζ ^ 14
          + ((6 / 17) : ℂ) * ζ ^ 15
          - ((43 / 34) : ℂ) * ζ ^ 18
          - ((6 / 17) : ℂ) * ζ ^ 19
          + ((9 / 34) : ℂ) * ζ ^ 20
          + ((6 / 17) : ℂ) * ζ ^ 23
          - ((9 / 34) : ℂ) * ζ ^ 24
          + ((9 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

theorem alternatingSixAmbientRow24_longMatrixABBB_mul :
    alternatingSixAmbientRow24LongMatrixABB *
        alternatingSixFiveAmbient_row24_matrixB =
      alternatingSixAmbientRow24LongMatrixABBB := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry00_00
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry00_01
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry00_02
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry00_03
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry00_04
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry00_05
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry00_06
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry00_07
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry00_08
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry00_09
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry01_00
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry01_01
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry01_02
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry01_03
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry01_04
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry01_05
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry01_06
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry01_07
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry01_08
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry01_09
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry02_00
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry02_01
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry02_02
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry02_03
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry02_04
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry02_05
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry02_06
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry02_07
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry02_08
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry02_09
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry03_00
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry03_01
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry03_02
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry03_03
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry03_04
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry03_05
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry03_06
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry03_07
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry03_08
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry03_09
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry04_00
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry04_01
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry04_02
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry04_03
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry04_04
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry04_05
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry04_06
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry04_07
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry04_08
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry04_09
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry05_00
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry05_01
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry05_02
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry05_03
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry05_04
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry05_05
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry05_06
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry05_07
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry05_08
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry05_09
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry06_00
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry06_01
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry06_02
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry06_03
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry06_04
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry06_05
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry06_06
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry06_07
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry06_08
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry06_09
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry07_00
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry07_01
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry07_02
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry07_03
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry07_04
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry07_05
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry07_06
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry07_07
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry07_08
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry07_09
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry08_00
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry08_01
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry08_02
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry08_03
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry08_04
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry08_05
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry08_06
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry08_07
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry08_08
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry08_09
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry09_00
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry09_01
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry09_02
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry09_03
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry09_04
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry09_05
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry09_06
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry09_07
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry09_08
  · exact alternatingSixAmbientRow24_longMatrixABBB_entry09_09

end InductiveMcKay
end McKayConjecture
