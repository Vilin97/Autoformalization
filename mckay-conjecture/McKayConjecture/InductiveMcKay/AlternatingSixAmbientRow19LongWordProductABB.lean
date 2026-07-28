/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow19LongWordData

/-!
# One checked row-19 long-word multiplication

This split generated module keeps each 8 by 8 multiplication
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
private theorem alternatingSixAmbientRow19_longMatrixABB_entry00_00 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (0 : Fin 8) (0 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (0 : Fin 8) (0 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((15 / 11) : ℂ)
          + ((15 / 11) : ℂ) * ζ ^ 4
          - ((3 / 11) : ℂ) * ζ ^ 8
          + ((2 / 11) : ℂ) * ζ ^ 12
          - ((13 / 11) : ℂ) * ζ ^ 16
          + ((7 / 11) : ℂ) * ζ ^ 20
          - ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((15 / 11) : ℂ)
          + ((15 / 11) : ℂ) * ζ ^ 4
          - ((3 / 11) : ℂ) * ζ ^ 8
          + ((2 / 11) : ℂ) * ζ ^ 12
          - ((13 / 11) : ℂ) * ζ ^ 16
          + ((7 / 11) : ℂ) * ζ ^ 20
          - ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry00_01 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (0 : Fin 8) (1 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (0 : Fin 8) (1 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((19 / 11) : ℂ)
          + ((19 / 11) : ℂ) * ζ ^ 4
          - ((2 / 11) : ℂ) * ζ ^ 8
          - ((25 / 11) : ℂ) * ζ ^ 12
          + ((24 / 11) : ℂ) * ζ ^ 16
          - ((36 / 11) : ℂ) * ζ ^ 20
          - ((1 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((19 / 11) : ℂ)
          + ((19 / 11) : ℂ) * ζ ^ 4
          - ((2 / 11) : ℂ) * ζ ^ 8
          - ((25 / 11) : ℂ) * ζ ^ 12
          + ((24 / 11) : ℂ) * ζ ^ 16
          - ((36 / 11) : ℂ) * ζ ^ 20
          - ((1 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry00_02 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (0 : Fin 8) (2 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (0 : Fin 8) (2 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((23 / 11) : ℂ)
          + ((23 / 11) : ℂ) * ζ ^ 4
          - ((16 / 11) : ℂ) * ζ ^ 8
          + ((37 / 11) : ℂ) * ζ ^ 12
          - ((38 / 11) : ℂ) * ζ ^ 16
          + ((16 / 11) : ℂ) * ζ ^ 20
          - ((1 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((23 / 11) : ℂ)
          + ((23 / 11) : ℂ) * ζ ^ 4
          - ((16 / 11) : ℂ) * ζ ^ 8
          + ((37 / 11) : ℂ) * ζ ^ 12
          - ((38 / 11) : ℂ) * ζ ^ 16
          + ((16 / 11) : ℂ) * ζ ^ 20
          - ((1 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry00_03 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (0 : Fin 8) (3 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (0 : Fin 8) (3 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((10 / 11) : ℂ)
          - ((10 / 11) : ℂ) * ζ ^ 4
          + ((8 / 11) : ℂ) * ζ ^ 8
          - ((12 / 11) : ℂ) * ζ ^ 12
          + ((27 / 11) : ℂ) * ζ ^ 16
          - ((6 / 11) : ℂ) * ζ ^ 20
          + ((15 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((10 / 11) : ℂ)
          - ((10 / 11) : ℂ) * ζ ^ 4
          + ((8 / 11) : ℂ) * ζ ^ 8
          - ((12 / 11) : ℂ) * ζ ^ 12
          + ((27 / 11) : ℂ) * ζ ^ 16
          - ((6 / 11) : ℂ) * ζ ^ 20
          + ((15 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry00_04 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (0 : Fin 8) (4 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (0 : Fin 8) (4 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((7 / 11) : ℂ)
          - ((7 / 11) : ℂ) * ζ ^ 4
          + ((1 / 11) : ℂ) * ζ ^ 8
          + ((17 / 11) : ℂ) * ζ ^ 12
          - ((18 / 11) : ℂ) * ζ ^ 16
          + ((12 / 11) : ℂ) * ζ ^ 20
          - ((1 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((7 / 11) : ℂ)
          - ((7 / 11) : ℂ) * ζ ^ 4
          + ((1 / 11) : ℂ) * ζ ^ 8
          + ((17 / 11) : ℂ) * ζ ^ 12
          - ((18 / 11) : ℂ) * ζ ^ 16
          + ((12 / 11) : ℂ) * ζ ^ 20
          - ((1 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry00_05 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (0 : Fin 8) (5 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (0 : Fin 8) (5 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 11) : ℂ)
          - ((1 / 11) : ℂ) * ζ ^ 4
          + ((3 / 11) : ℂ) * ζ ^ 8
          + ((19 / 11) : ℂ) * ζ ^ 12
          - ((23 / 11) : ℂ) * ζ ^ 16
          + ((14 / 11) : ℂ) * ζ ^ 20
          - ((4 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 11) : ℂ)
          - ((1 / 11) : ℂ) * ζ ^ 4
          + ((3 / 11) : ℂ) * ζ ^ 8
          + ((19 / 11) : ℂ) * ζ ^ 12
          - ((23 / 11) : ℂ) * ζ ^ 16
          + ((14 / 11) : ℂ) * ζ ^ 20
          - ((4 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry00_06 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (0 : Fin 8) (6 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (0 : Fin 8) (6 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((14 / 11) : ℂ)
          - ((14 / 11) : ℂ) * ζ ^ 4
          + ((16 / 11) : ℂ) * ζ ^ 8
          - ((30 / 11) : ℂ) * ζ ^ 12
          + ((30 / 11) : ℂ) * ζ ^ 16
          - ((17 / 11) : ℂ) * ζ ^ 20
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((14 / 11) : ℂ)
          - ((14 / 11) : ℂ) * ζ ^ 4
          + ((16 / 11) : ℂ) * ζ ^ 8
          - ((30 / 11) : ℂ) * ζ ^ 12
          + ((30 / 11) : ℂ) * ζ ^ 16
          - ((17 / 11) : ℂ) * ζ ^ 20
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry00_07 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (0 : Fin 8) (7 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (0 : Fin 8) (7 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((20 / 11) : ℂ)
          - ((20 / 11) : ℂ) * ζ ^ 4
          + ((3 / 11) : ℂ) * ζ ^ 8
          - ((23 / 11) : ℂ) * ζ ^ 12
          + ((26 / 11) : ℂ) * ζ ^ 16
          - ((15 / 11) : ℂ) * ζ ^ 20
          + ((3 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((20 / 11) : ℂ)
          - ((20 / 11) : ℂ) * ζ ^ 4
          + ((3 / 11) : ℂ) * ζ ^ 8
          - ((23 / 11) : ℂ) * ζ ^ 12
          + ((26 / 11) : ℂ) * ζ ^ 16
          - ((15 / 11) : ℂ) * ζ ^ 20
          + ((3 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry01_00 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (1 : Fin 8) (0 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (1 : Fin 8) (0 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((9 / 11) : ℂ)
          + ((9 / 11) : ℂ) * ζ ^ 4
          - ((19 / 11) : ℂ) * ζ ^ 8
          + ((18 / 11) : ℂ) * ζ ^ 12
          + ((5 / 11) : ℂ) * ζ ^ 16
          + ((6 / 11) : ℂ) * ζ ^ 20
          + ((23 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((9 / 11) : ℂ)
          + ((9 / 11) : ℂ) * ζ ^ 4
          - ((19 / 11) : ℂ) * ζ ^ 8
          + ((18 / 11) : ℂ) * ζ ^ 12
          + ((5 / 11) : ℂ) * ζ ^ 16
          + ((6 / 11) : ℂ) * ζ ^ 20
          + ((23 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry01_01 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (1 : Fin 8) (1 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (1 : Fin 8) (1 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((18 / 11) : ℂ)
          + ((18 / 11) : ℂ) * ζ ^ 4
          + ((19 / 11) : ℂ) * ζ ^ 8
          - ((29 / 11) : ℂ) * ζ ^ 12
          + ((14 / 11) : ℂ) * ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          - ((15 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((18 / 11) : ℂ)
          + ((18 / 11) : ℂ) * ζ ^ 4
          + ((19 / 11) : ℂ) * ζ ^ 8
          - ((29 / 11) : ℂ) * ζ ^ 12
          + ((14 / 11) : ℂ) * ζ ^ 16
          - (2 : ℂ) * ζ ^ 20
          - ((15 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry01_02 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (1 : Fin 8) (2 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (1 : Fin 8) (2 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((16 / 11) : ℂ)
          + ((16 / 11) : ℂ) * ζ ^ 4
          - ((14 / 11) : ℂ) * ζ ^ 8
          + ((20 / 11) : ℂ) * ζ ^ 12
          - ((3 / 11) : ℂ) * ζ ^ 16
          + ((3 / 11) : ℂ) * ζ ^ 20
          + ((17 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((16 / 11) : ℂ)
          + ((16 / 11) : ℂ) * ζ ^ 4
          - ((14 / 11) : ℂ) * ζ ^ 8
          + ((20 / 11) : ℂ) * ζ ^ 12
          - ((3 / 11) : ℂ) * ζ ^ 16
          + ((3 / 11) : ℂ) * ζ ^ 20
          + ((17 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry01_03 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (1 : Fin 8) (3 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (1 : Fin 8) (3 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((6 / 11) : ℂ)
          - ((6 / 11) : ℂ) * ζ ^ 4
          + ((4 / 11) : ℂ) * ζ ^ 8
          - ((10 / 11) : ℂ) * ζ ^ 12
          + ((6 / 11) : ℂ) * ζ ^ 16
          - ((5 / 11) : ℂ) * ζ ^ 20
          - ((4 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((6 / 11) : ℂ)
          - ((6 / 11) : ℂ) * ζ ^ 4
          + ((4 / 11) : ℂ) * ζ ^ 8
          - ((10 / 11) : ℂ) * ζ ^ 12
          + ((6 / 11) : ℂ) * ζ ^ 16
          - ((5 / 11) : ℂ) * ζ ^ 20
          - ((4 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry01_04 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (1 : Fin 8) (4 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (1 : Fin 8) (4 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 11) : ℂ)
          - ((2 / 11) : ℂ) * ζ ^ 4
          + ((2 / 11) : ℂ) * ζ ^ 8
          + ((14 / 11) : ℂ) * ζ ^ 12
          - ((10 / 11) : ℂ) * ζ ^ 16
          + ((8 / 11) : ℂ) * ζ ^ 20
          + ((4 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 11) : ℂ)
          - ((2 / 11) : ℂ) * ζ ^ 4
          + ((2 / 11) : ℂ) * ζ ^ 8
          + ((14 / 11) : ℂ) * ζ ^ 12
          - ((10 / 11) : ℂ) * ζ ^ 16
          + ((8 / 11) : ℂ) * ζ ^ 20
          + ((4 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry01_05 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (1 : Fin 8) (5 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (1 : Fin 8) (5 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((6 / 11) : ℂ)
          + ((6 / 11) : ℂ) * ζ ^ 4
          - ((2 / 11) : ℂ) * ζ ^ 8
          + ((8 / 11) : ℂ) * ζ ^ 12
          - ((10 / 11) : ℂ) * ζ ^ 16
          + ((10 / 11) : ℂ) * ζ ^ 20
          - ((2 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((6 / 11) : ℂ)
          + ((6 / 11) : ℂ) * ζ ^ 4
          - ((2 / 11) : ℂ) * ζ ^ 8
          + ((8 / 11) : ℂ) * ζ ^ 12
          - ((10 / 11) : ℂ) * ζ ^ 16
          + ((10 / 11) : ℂ) * ζ ^ 20
          - ((2 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry01_06 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (1 : Fin 8) (6 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (1 : Fin 8) (6 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((15 / 11) : ℂ)
          - ((15 / 11) : ℂ) * ζ ^ 4
          + ((15 / 11) : ℂ) * ζ ^ 8
          - ((20 / 11) : ℂ) * ζ ^ 12
          + ((17 / 11) : ℂ) * ζ ^ 16
          - ((9 / 11) : ℂ) * ζ ^ 20
          - ((3 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((15 / 11) : ℂ)
          - ((15 / 11) : ℂ) * ζ ^ 4
          + ((15 / 11) : ℂ) * ζ ^ 8
          - ((20 / 11) : ℂ) * ζ ^ 12
          + ((17 / 11) : ℂ) * ζ ^ 16
          - ((9 / 11) : ℂ) * ζ ^ 20
          - ((3 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry01_07 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (1 : Fin 8) (7 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (1 : Fin 8) (7 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((12 / 11) : ℂ)
          - ((12 / 11) : ℂ) * ζ ^ 4
          + ((1 / 11) : ℂ) * ζ ^ 8
          - ((21 / 11) : ℂ) * ζ ^ 12
          + ((1 / 11) : ℂ) * ζ ^ 16
          - ((6 / 11) : ℂ) * ζ ^ 20
          - ((20 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((12 / 11) : ℂ)
          - ((12 / 11) : ℂ) * ζ ^ 4
          + ((1 / 11) : ℂ) * ζ ^ 8
          - ((21 / 11) : ℂ) * ζ ^ 12
          + ((1 / 11) : ℂ) * ζ ^ 16
          - ((6 / 11) : ℂ) * ζ ^ 20
          - ((20 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry02_00 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (2 : Fin 8) (0 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (2 : Fin 8) (0 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 11) : ℂ)
          - ((1 / 11) : ℂ) * ζ ^ 4
          - ((2 / 11) : ℂ) * ζ ^ 8
          + ((8 / 11) : ℂ) * ζ ^ 12
          - ((8 / 11) : ℂ) * ζ ^ 16
          + ((6 / 11) : ℂ) * ζ ^ 20
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 11) : ℂ)
          - ((1 / 11) : ℂ) * ζ ^ 4
          - ((2 / 11) : ℂ) * ζ ^ 8
          + ((8 / 11) : ℂ) * ζ ^ 12
          - ((8 / 11) : ℂ) * ζ ^ 16
          + ((6 / 11) : ℂ) * ζ ^ 20
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry02_01 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (2 : Fin 8) (1 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (2 : Fin 8) (1 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((10 / 11) : ℂ)
          + ((10 / 11) : ℂ) * ζ ^ 4
          - ((2 / 11) : ℂ) * ζ ^ 8
          + ((8 / 11) : ℂ) * ζ ^ 12
          - ((8 / 11) : ℂ) * ζ ^ 16
          + ((6 / 11) : ℂ) * ζ ^ 20
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((10 / 11) : ℂ)
          + ((10 / 11) : ℂ) * ζ ^ 4
          - ((2 / 11) : ℂ) * ζ ^ 8
          + ((8 / 11) : ℂ) * ζ ^ 12
          - ((8 / 11) : ℂ) * ζ ^ 16
          + ((6 / 11) : ℂ) * ζ ^ 20
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry02_02 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (2 : Fin 8) (2 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (2 : Fin 8) (2 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
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
private theorem alternatingSixAmbientRow19_longMatrixABB_entry02_03 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (2 : Fin 8) (3 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (2 : Fin 8) (3 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((2 / 11) : ℂ)
          + ((2 / 11) : ℂ) * ζ ^ 4
          - ((7 / 11) : ℂ) * ζ ^ 8
          + ((6 / 11) : ℂ) * ζ ^ 12
          - ((6 / 11) : ℂ) * ζ ^ 16
          - ((1 / 11) : ℂ) * ζ ^ 20
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((2 / 11) : ℂ)
          + ((2 / 11) : ℂ) * ζ ^ 4
          - ((7 / 11) : ℂ) * ζ ^ 8
          + ((6 / 11) : ℂ) * ζ ^ 12
          - ((6 / 11) : ℂ) * ζ ^ 16
          - ((1 / 11) : ℂ) * ζ ^ 20
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry02_04 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (2 : Fin 8) (4 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (2 : Fin 8) (4 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((9 / 11) : ℂ)
          - ((9 / 11) : ℂ) * ζ ^ 4
          + ((4 / 11) : ℂ) * ζ ^ 8
          - ((5 / 11) : ℂ) * ζ ^ 12
          + ((5 / 11) : ℂ) * ζ ^ 16
          - ((1 / 11) : ℂ) * ζ ^ 20
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((9 / 11) : ℂ)
          - ((9 / 11) : ℂ) * ζ ^ 4
          + ((4 / 11) : ℂ) * ζ ^ 8
          - ((5 / 11) : ℂ) * ζ ^ 12
          + ((5 / 11) : ℂ) * ζ ^ 16
          - ((1 / 11) : ℂ) * ζ ^ 20
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry02_05 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (2 : Fin 8) (5 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (2 : Fin 8) (5 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((7 / 11) : ℂ)
          - ((7 / 11) : ℂ) * ζ ^ 4
          - ((3 / 11) : ℂ) * ζ ^ 8
          + ((1 / 11) : ℂ) * ζ ^ 12
          - ((1 / 11) : ℂ) * ζ ^ 16
          - ((2 / 11) : ℂ) * ζ ^ 20
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((7 / 11) : ℂ)
          - ((7 / 11) : ℂ) * ζ ^ 4
          - ((3 / 11) : ℂ) * ζ ^ 8
          + ((1 / 11) : ℂ) * ζ ^ 12
          - ((1 / 11) : ℂ) * ζ ^ 16
          - ((2 / 11) : ℂ) * ζ ^ 20
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry02_06 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (2 : Fin 8) (6 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (2 : Fin 8) (6 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((25 / 11) : ℂ)
          + ((25 / 11) : ℂ) * ζ ^ 4
          - ((16 / 11) : ℂ) * ζ ^ 8
          - ((2 / 11) : ℂ) * ζ ^ 12
          + ((2 / 11) : ℂ) * ζ ^ 16
          - ((18 / 11) : ℂ) * ζ ^ 20
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((25 / 11) : ℂ)
          + ((25 / 11) : ℂ) * ζ ^ 4
          - ((16 / 11) : ℂ) * ζ ^ 8
          - ((2 / 11) : ℂ) * ζ ^ 12
          + ((2 / 11) : ℂ) * ζ ^ 16
          - ((18 / 11) : ℂ) * ζ ^ 20
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry02_07 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (2 : Fin 8) (7 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (2 : Fin 8) (7 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((13 / 11) : ℂ)
          + ((13 / 11) : ℂ) * ζ ^ 4
          - ((7 / 11) : ℂ) * ζ ^ 8
          - ((5 / 11) : ℂ) * ζ ^ 12
          + ((5 / 11) : ℂ) * ζ ^ 16
          - ((12 / 11) : ℂ) * ζ ^ 20
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((13 / 11) : ℂ)
          + ((13 / 11) : ℂ) * ζ ^ 4
          - ((7 / 11) : ℂ) * ζ ^ 8
          - ((5 / 11) : ℂ) * ζ ^ 12
          + ((5 / 11) : ℂ) * ζ ^ 16
          - ((12 / 11) : ℂ) * ζ ^ 20
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry03_00 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (3 : Fin 8) (0 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (3 : Fin 8) (0 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((3 / 11) : ℂ)
          + ((3 / 11) : ℂ) * ζ ^ 4
          + ζ ^ 8
          - ((20 / 11) : ℂ) * ζ ^ 12
          - ((6 / 11) : ℂ) * ζ ^ 16
          + ((4 / 11) : ℂ) * ζ ^ 20
          - ((26 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((3 / 11) : ℂ)
          + ((3 / 11) : ℂ) * ζ ^ 4
          + ζ ^ 8
          - ((20 / 11) : ℂ) * ζ ^ 12
          - ((6 / 11) : ℂ) * ζ ^ 16
          + ((4 / 11) : ℂ) * ζ ^ 20
          - ((26 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry03_01 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (3 : Fin 8) (1 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (3 : Fin 8) (1 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((17 / 11) : ℂ)
          + ((17 / 11) : ℂ) * ζ ^ 4
          + ((9 / 11) : ℂ) * ζ ^ 8
          - ((10 / 11) : ℂ) * ζ ^ 12
          - ((3 / 11) : ℂ) * ζ ^ 16
          + ((2 / 11) : ℂ) * ζ ^ 20
          - ((13 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((17 / 11) : ℂ)
          + ((17 / 11) : ℂ) * ζ ^ 4
          + ((9 / 11) : ℂ) * ζ ^ 8
          - ((10 / 11) : ℂ) * ζ ^ 12
          - ((3 / 11) : ℂ) * ζ ^ 16
          + ((2 / 11) : ℂ) * ζ ^ 20
          - ((13 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry03_02 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (3 : Fin 8) (2 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (3 : Fin 8) (2 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((24 / 11) : ℂ)
          - ((24 / 11) : ℂ) * ζ ^ 4
          + ((10 / 11) : ℂ) * ζ ^ 8
          + ((3 / 11) : ℂ) * ζ ^ 12
          - ((1 / 11) : ℂ) * ζ ^ 16
          + ((1 / 11) : ℂ) * ζ ^ 20
          + ((2 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((24 / 11) : ℂ)
          - ((24 / 11) : ℂ) * ζ ^ 4
          + ((10 / 11) : ℂ) * ζ ^ 8
          + ((3 / 11) : ℂ) * ζ ^ 12
          - ((1 / 11) : ℂ) * ζ ^ 16
          + ((1 / 11) : ℂ) * ζ ^ 20
          + ((2 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry03_03 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (3 : Fin 8) (3 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (3 : Fin 8) (3 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((9 / 11) : ℂ)
          + ((9 / 11) : ℂ) * ζ ^ 4
          + ((7 / 11) : ℂ) * ζ ^ 8
          + ((1 / 11) : ℂ) * ζ ^ 12
          + ((10 / 11) : ℂ) * ζ ^ 16
          - ((2 / 11) : ℂ) * ζ ^ 20
          + ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((9 / 11) : ℂ)
          + ((9 / 11) : ℂ) * ζ ^ 4
          + ((7 / 11) : ℂ) * ζ ^ 8
          + ((1 / 11) : ℂ) * ζ ^ 12
          + ((10 / 11) : ℂ) * ζ ^ 16
          - ((2 / 11) : ℂ) * ζ ^ 20
          + ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry03_04 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (3 : Fin 8) (4 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (3 : Fin 8) (4 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((8 / 11) : ℂ)
          - ((8 / 11) : ℂ) * ζ ^ 4
          - ((12 / 11) : ℂ) * ζ ^ 8
          + ((9 / 11) : ℂ) * ζ ^ 12
          - ((10 / 11) : ℂ) * ζ ^ 16
          + ((6 / 11) : ℂ) * ζ ^ 20
          - ((1 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((8 / 11) : ℂ)
          - ((8 / 11) : ℂ) * ζ ^ 4
          - ((12 / 11) : ℂ) * ζ ^ 8
          + ((9 / 11) : ℂ) * ζ ^ 12
          - ((10 / 11) : ℂ) * ζ ^ 16
          + ((6 / 11) : ℂ) * ζ ^ 20
          - ((1 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry03_05 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (3 : Fin 8) (5 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (3 : Fin 8) (5 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((9 / 11) : ℂ)
          - ((9 / 11) : ℂ) * ζ ^ 4
          - ((4 / 11) : ℂ) * ζ ^ 8
          + ((15 / 11) : ℂ) * ζ ^ 12
          - ((2 / 11) : ℂ) * ζ ^ 16
          - ((1 / 11) : ℂ) * ζ ^ 20
          + ((13 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((9 / 11) : ℂ)
          - ((9 / 11) : ℂ) * ζ ^ 4
          - ((4 / 11) : ℂ) * ζ ^ 8
          + ((15 / 11) : ℂ) * ζ ^ 12
          - ((2 / 11) : ℂ) * ζ ^ 16
          - ((1 / 11) : ℂ) * ζ ^ 20
          + ((13 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry03_06 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (3 : Fin 8) (6 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (3 : Fin 8) (6 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((6 / 11) : ℂ)
          + ((6 / 11) : ℂ) * ζ ^ 4
          + ((8 / 11) : ℂ) * ζ ^ 8
          - ((2 / 11) : ℂ) * ζ ^ 12
          + ((3 / 11) : ℂ) * ζ ^ 16
          + ((13 / 11) : ℂ) * ζ ^ 20
          + ((1 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((6 / 11) : ℂ)
          + ((6 / 11) : ℂ) * ζ ^ 4
          + ((8 / 11) : ℂ) * ζ ^ 8
          - ((2 / 11) : ℂ) * ζ ^ 12
          + ((3 / 11) : ℂ) * ζ ^ 16
          + ((13 / 11) : ℂ) * ζ ^ 20
          + ((1 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry03_07 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (3 : Fin 8) (7 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (3 : Fin 8) (7 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 11) : ℂ)
          + ((7 / 11) : ℂ) * ζ ^ 4
          + ((6 / 11) : ℂ) * ζ ^ 8
          - ((10 / 11) : ℂ) * ζ ^ 12
          + ((12 / 11) : ℂ) * ζ ^ 16
          - ((6 / 11) : ℂ) * ζ ^ 20
          + ((2 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 11) : ℂ)
          + ((7 / 11) : ℂ) * ζ ^ 4
          + ((6 / 11) : ℂ) * ζ ^ 8
          - ((10 / 11) : ℂ) * ζ ^ 12
          + ((12 / 11) : ℂ) * ζ ^ 16
          - ((6 / 11) : ℂ) * ζ ^ 20
          + ((2 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry04_00 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (4 : Fin 8) (0 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (4 : Fin 8) (0 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((3 / 11) : ℂ)
          - ((3 / 11) : ℂ) * ζ ^ 4
          - ((14 / 11) : ℂ) * ζ ^ 8
          + ((10 / 11) : ℂ) * ζ ^ 12
          + ((3 / 11) : ℂ) * ζ ^ 16
          + ((9 / 11) : ℂ) * ζ ^ 20
          + ((13 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((3 / 11) : ℂ)
          - ((3 / 11) : ℂ) * ζ ^ 4
          - ((14 / 11) : ℂ) * ζ ^ 8
          + ((10 / 11) : ℂ) * ζ ^ 12
          + ((3 / 11) : ℂ) * ζ ^ 16
          + ((9 / 11) : ℂ) * ζ ^ 20
          + ((13 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry04_01 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (4 : Fin 8) (1 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (4 : Fin 8) (1 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((3 / 11) : ℂ)
          + ((3 / 11) : ℂ) * ζ ^ 4
          - ((7 / 11) : ℂ) * ζ ^ 8
          - ((14 / 11) : ℂ) * ζ ^ 12
          + ((20 / 11) : ℂ) * ζ ^ 16
          - ((17 / 11) : ℂ) * ζ ^ 20
          + ((6 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((3 / 11) : ℂ)
          + ((3 / 11) : ℂ) * ζ ^ 4
          - ((7 / 11) : ℂ) * ζ ^ 8
          - ((14 / 11) : ℂ) * ζ ^ 12
          + ((20 / 11) : ℂ) * ζ ^ 16
          - ((17 / 11) : ℂ) * ζ ^ 20
          + ((6 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry04_02 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (4 : Fin 8) (2 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (4 : Fin 8) (2 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 11) : ℂ)
          + ((7 / 11) : ℂ) * ζ ^ 4
          + ((9 / 11) : ℂ) * ζ ^ 8
          + ((6 / 11) : ℂ) * ζ ^ 12
          - ((13 / 11) : ℂ) * ζ ^ 16
          + ((13 / 11) : ℂ) * ζ ^ 20
          - ((7 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 11) : ℂ)
          + ((7 / 11) : ℂ) * ζ ^ 4
          + ((9 / 11) : ℂ) * ζ ^ 8
          + ((6 / 11) : ℂ) * ζ ^ 12
          - ((13 / 11) : ℂ) * ζ ^ 16
          + ((13 / 11) : ℂ) * ζ ^ 20
          - ((7 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry04_03 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (4 : Fin 8) (3 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (4 : Fin 8) (3 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((14 / 11) : ℂ)
          + ((14 / 11) : ℂ) * ζ ^ 4
          - ((13 / 11) : ℂ) * ζ ^ 8
          - ((10 / 11) : ℂ) * ζ ^ 12
          + ((12 / 11) : ℂ) * ζ ^ 16
          - ((17 / 11) : ℂ) * ζ ^ 20
          + ((2 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((14 / 11) : ℂ)
          + ((14 / 11) : ℂ) * ζ ^ 4
          - ((13 / 11) : ℂ) * ζ ^ 8
          - ((10 / 11) : ℂ) * ζ ^ 12
          + ((12 / 11) : ℂ) * ζ ^ 16
          - ((17 / 11) : ℂ) * ζ ^ 20
          + ((2 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry04_04 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (4 : Fin 8) (4 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (4 : Fin 8) (4 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((9 / 11) : ℂ)
          - ((9 / 11) : ℂ) * ζ ^ 4
          + ((4 / 11) : ℂ) * ζ ^ 8
          + ((17 / 11) : ℂ) * ζ ^ 12
          - ((17 / 11) : ℂ) * ζ ^ 16
          + ((21 / 11) : ℂ) * ζ ^ 20
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((9 / 11) : ℂ)
          - ((9 / 11) : ℂ) * ζ ^ 4
          + ((4 / 11) : ℂ) * ζ ^ 8
          + ((17 / 11) : ℂ) * ζ ^ 12
          - ((17 / 11) : ℂ) * ζ ^ 16
          + ((21 / 11) : ℂ) * ζ ^ 20
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry04_05 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (4 : Fin 8) (5 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (4 : Fin 8) (5 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 11) : ℂ)
          + ((7 / 11) : ℂ) * ζ ^ 4
          + ((4 / 11) : ℂ) * ζ ^ 8
          + ((6 / 11) : ℂ) * ζ ^ 12
          - ((9 / 11) : ℂ) * ζ ^ 16
          + ((5 / 11) : ℂ) * ζ ^ 20
          - ((3 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 11) : ℂ)
          + ((7 / 11) : ℂ) * ζ ^ 4
          + ((4 / 11) : ℂ) * ζ ^ 8
          + ((6 / 11) : ℂ) * ζ ^ 12
          - ((9 / 11) : ℂ) * ζ ^ 16
          + ((5 / 11) : ℂ) * ζ ^ 20
          - ((3 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry04_06 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (4 : Fin 8) (6 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (4 : Fin 8) (6 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((16 / 11) : ℂ)
          - ((16 / 11) : ℂ) * ζ ^ 4
          + ((14 / 11) : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + ((27 / 11) : ℂ) * ζ ^ 16
          - ((21 / 11) : ℂ) * ζ ^ 20
          + ((5 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((16 / 11) : ℂ)
          - ((16 / 11) : ℂ) * ζ ^ 4
          + ((14 / 11) : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + ((27 / 11) : ℂ) * ζ ^ 16
          - ((21 / 11) : ℂ) * ζ ^ 20
          + ((5 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry04_07 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (4 : Fin 8) (7 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (4 : Fin 8) (7 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((12 / 11) : ℂ)
          - ((12 / 11) : ℂ) * ζ ^ 4
          + ((7 / 11) : ℂ) * ζ ^ 8
          - ((21 / 11) : ℂ) * ζ ^ 12
          + ((16 / 11) : ℂ) * ζ ^ 16
          - ((14 / 11) : ℂ) * ζ ^ 20
          - ((5 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((12 / 11) : ℂ)
          - ((12 / 11) : ℂ) * ζ ^ 4
          + ((7 / 11) : ℂ) * ζ ^ 8
          - ((21 / 11) : ℂ) * ζ ^ 12
          + ((16 / 11) : ℂ) * ζ ^ 16
          - ((14 / 11) : ℂ) * ζ ^ 20
          - ((5 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry05_00 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (5 : Fin 8) (0 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (5 : Fin 8) (0 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((10 / 11) : ℂ)
          - ((10 / 11) : ℂ) * ζ ^ 4
          - ((16 / 11) : ℂ) * ζ ^ 8
          + ζ ^ 12
          - ((1 / 11) : ℂ) * ζ ^ 16
          + ((13 / 11) : ℂ) * ζ ^ 20
          + ((10 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((10 / 11) : ℂ)
          - ((10 / 11) : ℂ) * ζ ^ 4
          - ((16 / 11) : ℂ) * ζ ^ 8
          + ζ ^ 12
          - ((1 / 11) : ℂ) * ζ ^ 16
          + ((13 / 11) : ℂ) * ζ ^ 20
          + ((10 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry05_01 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (5 : Fin 8) (1 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (5 : Fin 8) (1 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((4 / 11) : ℂ)
          - ((4 / 11) : ℂ) * ζ ^ 4
          + ((24 / 11) : ℂ) * ζ ^ 8
          - ((13 / 11) : ℂ) * ζ ^ 12
          + ((5 / 11) : ℂ) * ζ ^ 16
          - ((2 / 11) : ℂ) * ζ ^ 20
          - ((8 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((4 / 11) : ℂ)
          - ((4 / 11) : ℂ) * ζ ^ 4
          + ((24 / 11) : ℂ) * ζ ^ 8
          - ((13 / 11) : ℂ) * ζ ^ 12
          + ((5 / 11) : ℂ) * ζ ^ 16
          - ((2 / 11) : ℂ) * ζ ^ 20
          - ((8 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry05_02 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (5 : Fin 8) (2 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (5 : Fin 8) (2 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 11) : ℂ)
          + ((7 / 11) : ℂ) * ζ ^ 4
          - ((13 / 11) : ℂ) * ζ ^ 8
          + ((17 / 11) : ℂ) * ζ ^ 12
          - ((13 / 11) : ℂ) * ζ ^ 16
          + ((13 / 11) : ℂ) * ζ ^ 20
          + ((4 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 11) : ℂ)
          + ((7 / 11) : ℂ) * ζ ^ 4
          - ((13 / 11) : ℂ) * ζ ^ 8
          + ((17 / 11) : ℂ) * ζ ^ 12
          - ((13 / 11) : ℂ) * ζ ^ 16
          + ((13 / 11) : ℂ) * ζ ^ 20
          + ((4 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry05_03 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (5 : Fin 8) (3 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (5 : Fin 8) (3 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((6 / 11) : ℂ)
          + ((6 / 11) : ℂ) * ζ ^ 4
          + ((2 / 11) : ℂ) * ζ ^ 8
          - ((12 / 11) : ℂ) * ζ ^ 12
          - ((2 / 11) : ℂ) * ζ ^ 16
          - ((3 / 11) : ℂ) * ζ ^ 20
          - ((14 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((6 / 11) : ℂ)
          + ((6 / 11) : ℂ) * ζ ^ 4
          + ((2 / 11) : ℂ) * ζ ^ 8
          - ((12 / 11) : ℂ) * ζ ^ 12
          - ((2 / 11) : ℂ) * ζ ^ 16
          - ((3 / 11) : ℂ) * ζ ^ 20
          - ((14 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry05_04 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (5 : Fin 8) (4 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (5 : Fin 8) (4 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((5 / 11) : ℂ)
          + ((5 / 11) : ℂ) * ζ ^ 4
          - ((14 / 11) : ℂ) * ζ ^ 8
          + ((4 / 11) : ℂ) * ζ ^ 12
          + ((2 / 11) : ℂ) * ζ ^ 16
          + ((2 / 11) : ℂ) * ζ ^ 20
          + ((6 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((5 / 11) : ℂ)
          + ((5 / 11) : ℂ) * ζ ^ 4
          - ((14 / 11) : ℂ) * ζ ^ 8
          + ((4 / 11) : ℂ) * ζ ^ 12
          + ((2 / 11) : ℂ) * ζ ^ 16
          + ((2 / 11) : ℂ) * ζ ^ 20
          + ((6 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry05_05 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (5 : Fin 8) (5 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (5 : Fin 8) (5 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((2 / 11) : ℂ)
          + ((2 / 11) : ℂ) * ζ ^ 4
          + ((1 / 11) : ℂ) * ζ ^ 8
          + ((2 / 11) : ℂ) * ζ ^ 12
          + ((7 / 11) : ℂ) * ζ ^ 16
          - ζ ^ 20
          + ((9 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((2 / 11) : ℂ)
          + ((2 / 11) : ℂ) * ζ ^ 4
          + ((1 / 11) : ℂ) * ζ ^ 8
          + ((2 / 11) : ℂ) * ζ ^ 12
          + ((7 / 11) : ℂ) * ζ ^ 16
          - ζ ^ 20
          + ((9 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry05_06 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (5 : Fin 8) (6 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (5 : Fin 8) (6 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((6 / 11) : ℂ)
          - ((6 / 11) : ℂ) * ζ ^ 4
          + ((9 / 11) : ℂ) * ζ ^ 8
          - ((3 / 11) : ℂ) * ζ ^ 12
          - ((5 / 11) : ℂ) * ζ ^ 16
          + ζ ^ 20
          - ((8 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((6 / 11) : ℂ)
          - ((6 / 11) : ℂ) * ζ ^ 4
          + ((9 / 11) : ℂ) * ζ ^ 8
          - ((3 / 11) : ℂ) * ζ ^ 12
          - ((5 / 11) : ℂ) * ζ ^ 16
          + ζ ^ 20
          - ((8 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry05_07 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (5 : Fin 8) (7 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (5 : Fin 8) (7 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((9 / 11) : ℂ)
          - ((9 / 11) : ℂ) * ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          - ((23 / 11) : ℂ) * ζ ^ 12
          + ((2 / 11) : ℂ) * ζ ^ 16
          - ((21 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((9 / 11) : ℂ)
          - ((9 / 11) : ℂ) * ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          - ((23 / 11) : ℂ) * ζ ^ 12
          + ((2 / 11) : ℂ) * ζ ^ 16
          - ((21 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry06_00 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (6 : Fin 8) (0 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (6 : Fin 8) (0 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((9 / 11) : ℂ)
          - ((9 / 11) : ℂ) * ζ ^ 4
          - ((3 / 11) : ℂ) * ζ ^ 8
          - ((8 / 11) : ℂ) * ζ ^ 12
          + ((7 / 11) : ℂ) * ζ ^ 16
          + ((18 / 11) : ℂ) * ζ ^ 20
          - ((1 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((9 / 11) : ℂ)
          - ((9 / 11) : ℂ) * ζ ^ 4
          - ((3 / 11) : ℂ) * ζ ^ 8
          - ((8 / 11) : ℂ) * ζ ^ 12
          + ((7 / 11) : ℂ) * ζ ^ 16
          + ((18 / 11) : ℂ) * ζ ^ 20
          - ((1 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry06_01 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (6 : Fin 8) (1 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (6 : Fin 8) (1 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(2 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          + ((24 / 11) : ℂ) * ζ ^ 8
          - (3 : ℂ) * ζ ^ 12
          + ((5 / 11) : ℂ) * ζ ^ 16
          - ((10 / 11) : ℂ) * ζ ^ 20
          - ((28 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(2 : ℂ)
          + (2 : ℂ) * ζ ^ 4
          + ((24 / 11) : ℂ) * ζ ^ 8
          - (3 : ℂ) * ζ ^ 12
          + ((5 / 11) : ℂ) * ζ ^ 16
          - ((10 / 11) : ℂ) * ζ ^ 20
          - ((28 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry06_02 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (6 : Fin 8) (2 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (6 : Fin 8) (2 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((6 / 11) : ℂ)
          - ((6 / 11) : ℂ) * ζ ^ 4
          - ((3 / 11) : ℂ) * ζ ^ 8
          + ((9 / 11) : ℂ) * ζ ^ 12
          + ((8 / 11) : ℂ) * ζ ^ 16
          + ((3 / 11) : ℂ) * ζ ^ 20
          + ((17 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((6 / 11) : ℂ)
          - ((6 / 11) : ℂ) * ζ ^ 4
          - ((3 / 11) : ℂ) * ζ ^ 8
          + ((9 / 11) : ℂ) * ζ ^ 12
          + ((8 / 11) : ℂ) * ζ ^ 16
          + ((3 / 11) : ℂ) * ζ ^ 20
          + ((17 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry06_03 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (6 : Fin 8) (3 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (6 : Fin 8) (3 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((8 / 11) : ℂ)
          + ((8 / 11) : ℂ) * ζ ^ 4
          + ((5 / 11) : ℂ) * ζ ^ 8
          - ((2 / 11) : ℂ) * ζ ^ 12
          + ((2 / 11) : ℂ) * ζ ^ 16
          + ((4 / 11) : ℂ) * ζ ^ 20
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((8 / 11) : ℂ)
          + ((8 / 11) : ℂ) * ζ ^ 4
          + ((5 / 11) : ℂ) * ζ ^ 8
          - ((2 / 11) : ℂ) * ζ ^ 12
          + ((2 / 11) : ℂ) * ζ ^ 16
          + ((4 / 11) : ℂ) * ζ ^ 20
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry06_04 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (6 : Fin 8) (4 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (6 : Fin 8) (4 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((10 / 11) : ℂ)
          - ((10 / 11) : ℂ) * ζ ^ 4
          - ((8 / 11) : ℂ) * ζ ^ 8
          + ζ ^ 12
          - ((14 / 11) : ℂ) * ζ ^ 16
          + ((6 / 11) : ℂ) * ζ ^ 20
          - ((3 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((10 / 11) : ℂ)
          - ((10 / 11) : ℂ) * ζ ^ 4
          - ((8 / 11) : ℂ) * ζ ^ 8
          + ζ ^ 12
          - ((14 / 11) : ℂ) * ζ ^ 16
          + ((6 / 11) : ℂ) * ζ ^ 20
          - ((3 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry06_05 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (6 : Fin 8) (5 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (6 : Fin 8) (5 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 11) : ℂ)
          + ((1 / 11) : ℂ) * ζ ^ 4
          - ζ ^ 8
          + ((13 / 11) : ℂ) * ζ ^ 12
          + ((4 / 11) : ℂ) * ζ ^ 16
          - ((16 / 11) : ℂ) * ζ ^ 20
          + ((17 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 11) : ℂ)
          + ((1 / 11) : ℂ) * ζ ^ 4
          - ζ ^ 8
          + ((13 / 11) : ℂ) * ζ ^ 12
          + ((4 / 11) : ℂ) * ζ ^ 16
          - ((16 / 11) : ℂ) * ζ ^ 20
          + ((17 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry06_06 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (6 : Fin 8) (6 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (6 : Fin 8) (6 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((16 / 11) : ℂ)
          - ((16 / 11) : ℂ) * ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          + ((3 / 11) : ℂ) * ζ ^ 12
          + ((21 / 11) : ℂ) * ζ ^ 20
          + ((3 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((16 / 11) : ℂ)
          - ((16 / 11) : ℂ) * ζ ^ 4
          + (2 : ℂ) * ζ ^ 8
          + ((3 / 11) : ℂ) * ζ ^ 12
          + ((21 / 11) : ℂ) * ζ ^ 20
          + ((3 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry06_07 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (6 : Fin 8) (7 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (6 : Fin 8) (7 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((9 / 11) : ℂ)
          - ((9 / 11) : ℂ) * ζ ^ 4
          + ((24 / 11) : ℂ) * ζ ^ 8
          - ((24 / 11) : ℂ) * ζ ^ 12
          + ((19 / 11) : ℂ) * ζ ^ 16
          - ((8 / 11) : ℂ) * ζ ^ 20
          - ((5 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((9 / 11) : ℂ)
          - ((9 / 11) : ℂ) * ζ ^ 4
          + ((24 / 11) : ℂ) * ζ ^ 8
          - ((24 / 11) : ℂ) * ζ ^ 12
          + ((19 / 11) : ℂ) * ζ ^ 16
          - ((8 / 11) : ℂ) * ζ ^ 20
          - ((5 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry07_00 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (7 : Fin 8) (0 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (7 : Fin 8) (0 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((20 / 11) : ℂ)
          + ((20 / 11) : ℂ) * ζ ^ 4
          + ((8 / 11) : ℂ) * ζ ^ 8
          - ((2 / 11) : ℂ) * ζ ^ 12
          - ((1 / 11) : ℂ) * ζ ^ 16
          - ((34 / 11) : ℂ) * ζ ^ 20
          - ((3 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((20 / 11) : ℂ)
          + ((20 / 11) : ℂ) * ζ ^ 4
          + ((8 / 11) : ℂ) * ζ ^ 8
          - ((2 / 11) : ℂ) * ζ ^ 12
          - ((1 / 11) : ℂ) * ζ ^ 16
          - ((34 / 11) : ℂ) * ζ ^ 20
          - ((3 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry07_01 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (7 : Fin 8) (1 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (7 : Fin 8) (1 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((3 / 11) : ℂ)
          + ((3 / 11) : ℂ) * ζ ^ 4
          - ((21 / 11) : ℂ) * ζ ^ 8
          + (3 : ℂ) * ζ ^ 12
          - ((18 / 11) : ℂ) * ζ ^ 16
          + ((25 / 11) : ℂ) * ζ ^ 20
          + ((15 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((3 / 11) : ℂ)
          + ((3 / 11) : ℂ) * ζ ^ 4
          - ((21 / 11) : ℂ) * ζ ^ 8
          + (3 : ℂ) * ζ ^ 12
          - ((18 / 11) : ℂ) * ζ ^ 16
          + ((25 / 11) : ℂ) * ζ ^ 20
          + ((15 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry07_02 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (7 : Fin 8) (2 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (7 : Fin 8) (2 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((7 / 11) : ℂ)
          - ((7 / 11) : ℂ) * ζ ^ 4
          + ((13 / 11) : ℂ) * ζ ^ 8
          - ((17 / 11) : ℂ) * ζ ^ 12
          + ((2 / 11) : ℂ) * ζ ^ 16
          - ((13 / 11) : ℂ) * ζ ^ 20
          - ((15 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((7 / 11) : ℂ)
          - ((7 / 11) : ℂ) * ζ ^ 4
          + ((13 / 11) : ℂ) * ζ ^ 8
          - ((17 / 11) : ℂ) * ζ ^ 12
          + ((2 / 11) : ℂ) * ζ ^ 16
          - ((13 / 11) : ℂ) * ζ ^ 20
          - ((15 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry07_03 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (7 : Fin 8) (3 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (7 : Fin 8) (3 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((4 / 11) : ℂ)
          - ((4 / 11) : ℂ) * ζ ^ 4
          - ((8 / 11) : ℂ) * ζ ^ 8
          + ((16 / 11) : ℂ) * ζ ^ 12
          - ((16 / 11) : ℂ) * ζ ^ 16
          + ((12 / 11) : ℂ) * ζ ^ 20
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((4 / 11) : ℂ)
          - ((4 / 11) : ℂ) * ζ ^ 4
          - ((8 / 11) : ℂ) * ζ ^ 8
          + ((16 / 11) : ℂ) * ζ ^ 12
          - ((16 / 11) : ℂ) * ζ ^ 16
          + ((12 / 11) : ℂ) * ζ ^ 20
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry07_04 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (7 : Fin 8) (4 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (7 : Fin 8) (4 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((3 / 11) : ℂ)
          - ((3 / 11) : ℂ) * ζ ^ 4
          + ((19 / 11) : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + ((24 / 11) : ℂ) * ζ ^ 16
          - ((15 / 11) : ℂ) * ζ ^ 20
          + ((2 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((3 / 11) : ℂ)
          - ((3 / 11) : ℂ) * ζ ^ 4
          + ((19 / 11) : ℂ) * ζ ^ 8
          - (2 : ℂ) * ζ ^ 12
          + ((24 / 11) : ℂ) * ζ ^ 16
          - ((15 / 11) : ℂ) * ζ ^ 20
          + ((2 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry07_05 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (7 : Fin 8) (5 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (7 : Fin 8) (5 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((9 / 11) : ℂ)
          - ((9 / 11) : ℂ) * ζ ^ 4
          + ((9 / 11) : ℂ) * ζ ^ 8
          - ((16 / 11) : ℂ) * ζ ^ 12
          + ((1 / 11) : ℂ) * ζ ^ 16
          + ((18 / 11) : ℂ) * ζ ^ 20
          - ((15 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((9 / 11) : ℂ)
          - ((9 / 11) : ℂ) * ζ ^ 4
          + ((9 / 11) : ℂ) * ζ ^ 8
          - ((16 / 11) : ℂ) * ζ ^ 12
          + ((1 / 11) : ℂ) * ζ ^ 16
          + ((18 / 11) : ℂ) * ζ ^ 20
          - ((15 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry07_06 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (7 : Fin 8) (6 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (7 : Fin 8) (6 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((20 / 11) : ℂ)
          + ((20 / 11) : ℂ) * ζ ^ 4
          - ((40 / 11) : ℂ) * ζ ^ 8
          + ((9 / 11) : ℂ) * ζ ^ 12
          - ((14 / 11) : ℂ) * ζ ^ 20
          + ((9 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((20 / 11) : ℂ)
          + ((20 / 11) : ℂ) * ζ ^ 4
          - ((40 / 11) : ℂ) * ζ ^ 8
          + ((9 / 11) : ℂ) * ζ ^ 12
          - ((14 / 11) : ℂ) * ζ ^ 20
          + ((9 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow19_longMatrixABB_entry07_07 :
    (alternatingSixAmbientRow19LongMatrixAB
        * alternatingSixFiveAmbient_row19_matrixB)
          (7 : Fin 8) (7 : Fin 8) =
      alternatingSixAmbientRow19LongMatrixABB
        (7 : Fin 8) (7 : Fin 8) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow19LongMatrixAB,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixAmbientRow19LongMatrixABB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(1 : ℂ)
          + ζ ^ 4
          - ((39 / 11) : ℂ) * ζ ^ 8
          + ((38 / 11) : ℂ) * ζ ^ 12
          - ((20 / 11) : ℂ) * ζ ^ 16
          + ((9 / 11) : ℂ) * ζ ^ 20
          + ((18 / 11) : ℂ) * ζ ^ 24
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(1 : ℂ)
          + ζ ^ 4
          - ((39 / 11) : ℂ) * ζ ^ 8
          + ((38 / 11) : ℂ) * ζ ^ 12
          - ((20 / 11) : ℂ) * ζ ^ 16
          + ((9 / 11) : ℂ) * ζ ^ 20
          + ((18 / 11) : ℂ) * ζ ^ 24
      )) *
        alternatingSixComplexCyclotomicRoot_relation

theorem alternatingSixAmbientRow19_longMatrixABB_mul :
    alternatingSixAmbientRow19LongMatrixAB *
        alternatingSixFiveAmbient_row19_matrixB =
      alternatingSixAmbientRow19LongMatrixABB := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientRow19_longMatrixABB_entry00_00
  · exact alternatingSixAmbientRow19_longMatrixABB_entry00_01
  · exact alternatingSixAmbientRow19_longMatrixABB_entry00_02
  · exact alternatingSixAmbientRow19_longMatrixABB_entry00_03
  · exact alternatingSixAmbientRow19_longMatrixABB_entry00_04
  · exact alternatingSixAmbientRow19_longMatrixABB_entry00_05
  · exact alternatingSixAmbientRow19_longMatrixABB_entry00_06
  · exact alternatingSixAmbientRow19_longMatrixABB_entry00_07
  · exact alternatingSixAmbientRow19_longMatrixABB_entry01_00
  · exact alternatingSixAmbientRow19_longMatrixABB_entry01_01
  · exact alternatingSixAmbientRow19_longMatrixABB_entry01_02
  · exact alternatingSixAmbientRow19_longMatrixABB_entry01_03
  · exact alternatingSixAmbientRow19_longMatrixABB_entry01_04
  · exact alternatingSixAmbientRow19_longMatrixABB_entry01_05
  · exact alternatingSixAmbientRow19_longMatrixABB_entry01_06
  · exact alternatingSixAmbientRow19_longMatrixABB_entry01_07
  · exact alternatingSixAmbientRow19_longMatrixABB_entry02_00
  · exact alternatingSixAmbientRow19_longMatrixABB_entry02_01
  · exact alternatingSixAmbientRow19_longMatrixABB_entry02_02
  · exact alternatingSixAmbientRow19_longMatrixABB_entry02_03
  · exact alternatingSixAmbientRow19_longMatrixABB_entry02_04
  · exact alternatingSixAmbientRow19_longMatrixABB_entry02_05
  · exact alternatingSixAmbientRow19_longMatrixABB_entry02_06
  · exact alternatingSixAmbientRow19_longMatrixABB_entry02_07
  · exact alternatingSixAmbientRow19_longMatrixABB_entry03_00
  · exact alternatingSixAmbientRow19_longMatrixABB_entry03_01
  · exact alternatingSixAmbientRow19_longMatrixABB_entry03_02
  · exact alternatingSixAmbientRow19_longMatrixABB_entry03_03
  · exact alternatingSixAmbientRow19_longMatrixABB_entry03_04
  · exact alternatingSixAmbientRow19_longMatrixABB_entry03_05
  · exact alternatingSixAmbientRow19_longMatrixABB_entry03_06
  · exact alternatingSixAmbientRow19_longMatrixABB_entry03_07
  · exact alternatingSixAmbientRow19_longMatrixABB_entry04_00
  · exact alternatingSixAmbientRow19_longMatrixABB_entry04_01
  · exact alternatingSixAmbientRow19_longMatrixABB_entry04_02
  · exact alternatingSixAmbientRow19_longMatrixABB_entry04_03
  · exact alternatingSixAmbientRow19_longMatrixABB_entry04_04
  · exact alternatingSixAmbientRow19_longMatrixABB_entry04_05
  · exact alternatingSixAmbientRow19_longMatrixABB_entry04_06
  · exact alternatingSixAmbientRow19_longMatrixABB_entry04_07
  · exact alternatingSixAmbientRow19_longMatrixABB_entry05_00
  · exact alternatingSixAmbientRow19_longMatrixABB_entry05_01
  · exact alternatingSixAmbientRow19_longMatrixABB_entry05_02
  · exact alternatingSixAmbientRow19_longMatrixABB_entry05_03
  · exact alternatingSixAmbientRow19_longMatrixABB_entry05_04
  · exact alternatingSixAmbientRow19_longMatrixABB_entry05_05
  · exact alternatingSixAmbientRow19_longMatrixABB_entry05_06
  · exact alternatingSixAmbientRow19_longMatrixABB_entry05_07
  · exact alternatingSixAmbientRow19_longMatrixABB_entry06_00
  · exact alternatingSixAmbientRow19_longMatrixABB_entry06_01
  · exact alternatingSixAmbientRow19_longMatrixABB_entry06_02
  · exact alternatingSixAmbientRow19_longMatrixABB_entry06_03
  · exact alternatingSixAmbientRow19_longMatrixABB_entry06_04
  · exact alternatingSixAmbientRow19_longMatrixABB_entry06_05
  · exact alternatingSixAmbientRow19_longMatrixABB_entry06_06
  · exact alternatingSixAmbientRow19_longMatrixABB_entry06_07
  · exact alternatingSixAmbientRow19_longMatrixABB_entry07_00
  · exact alternatingSixAmbientRow19_longMatrixABB_entry07_01
  · exact alternatingSixAmbientRow19_longMatrixABB_entry07_02
  · exact alternatingSixAmbientRow19_longMatrixABB_entry07_03
  · exact alternatingSixAmbientRow19_longMatrixABB_entry07_04
  · exact alternatingSixAmbientRow19_longMatrixABB_entry07_05
  · exact alternatingSixAmbientRow19_longMatrixABB_entry07_06
  · exact alternatingSixAmbientRow19_longMatrixABB_entry07_07

end InductiveMcKay
end McKayConjecture
