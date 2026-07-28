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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry00_00 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (0 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry00_01 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (0 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry00_02 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (0 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry00_03 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (0 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry00_04 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (0 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry00_05 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (0 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry00_06 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (0 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry00_07 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (0 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry00_08 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (0 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry00_09 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (0 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (0 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry01_00 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (1 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((9 / 34) : ℂ)
          - ((9 / 34) : ℂ) * ζ ^ 4
          - ((47 / 34) : ℂ) * ζ ^ 5
          + ((9 / 34) : ℂ) * ζ ^ 8
          + ((47 / 34) : ℂ) * ζ ^ 9
          + ((3 / 17) : ℂ) * ζ ^ 10
          - ((47 / 34) : ℂ) * ζ ^ 13
          - ((3 / 17) : ℂ) * ζ ^ 14
          + ((33 / 34) : ℂ) * ζ ^ 15
          + ((3 / 17) : ℂ) * ζ ^ 18
          - ((33 / 34) : ℂ) * ζ ^ 19
          - ((43 / 34) : ℂ) * ζ ^ 20
          + ((33 / 34) : ℂ) * ζ ^ 23
          + ((43 / 34) : ℂ) * ζ ^ 24
          - ((43 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((9 / 34) : ℂ)
          - ((9 / 34) : ℂ) * ζ ^ 4
          - ((47 / 34) : ℂ) * ζ ^ 5
          + ((9 / 34) : ℂ) * ζ ^ 8
          + ((47 / 34) : ℂ) * ζ ^ 9
          + ((3 / 17) : ℂ) * ζ ^ 10
          - ((47 / 34) : ℂ) * ζ ^ 13
          - ((3 / 17) : ℂ) * ζ ^ 14
          + ((33 / 34) : ℂ) * ζ ^ 15
          + ((3 / 17) : ℂ) * ζ ^ 18
          - ((33 / 34) : ℂ) * ζ ^ 19
          - ((43 / 34) : ℂ) * ζ ^ 20
          + ((33 / 34) : ℂ) * ζ ^ 23
          + ((43 / 34) : ℂ) * ζ ^ 24
          - ((43 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry01_01 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (1 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((3 / 2) : ℂ)
          - ((3 / 2) : ℂ) * ζ ^ 4
          + ((14 / 17) : ℂ) * ζ ^ 5
          + ((3 / 2) : ℂ) * ζ ^ 8
          - ((14 / 17) : ℂ) * ζ ^ 9
          + ((5 / 34) : ℂ) * ζ ^ 10
          + ((14 / 17) : ℂ) * ζ ^ 13
          - ((5 / 34) : ℂ) * ζ ^ 14
          + ((33 / 17) : ℂ) * ζ ^ 15
          + ((5 / 34) : ℂ) * ζ ^ 18
          - ((33 / 17) : ℂ) * ζ ^ 19
          + ((27 / 34) : ℂ) * ζ ^ 20
          + ((33 / 17) : ℂ) * ζ ^ 23
          - ((27 / 34) : ℂ) * ζ ^ 24
          + ((27 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((3 / 2) : ℂ)
          - ((3 / 2) : ℂ) * ζ ^ 4
          + ((14 / 17) : ℂ) * ζ ^ 5
          + ((3 / 2) : ℂ) * ζ ^ 8
          - ((14 / 17) : ℂ) * ζ ^ 9
          + ((5 / 34) : ℂ) * ζ ^ 10
          + ((14 / 17) : ℂ) * ζ ^ 13
          - ((5 / 34) : ℂ) * ζ ^ 14
          + ((33 / 17) : ℂ) * ζ ^ 15
          + ((5 / 34) : ℂ) * ζ ^ 18
          - ((33 / 17) : ℂ) * ζ ^ 19
          + ((27 / 34) : ℂ) * ζ ^ 20
          + ((33 / 17) : ℂ) * ζ ^ 23
          - ((27 / 34) : ℂ) * ζ ^ 24
          + ((27 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry01_02 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (1 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((41 / 17) : ℂ)
          - ((41 / 17) : ℂ) * ζ ^ 4
          + ((22 / 17) : ℂ) * ζ ^ 5
          + ((41 / 17) : ℂ) * ζ ^ 8
          - ((22 / 17) : ℂ) * ζ ^ 9
          - ((1 / 17) : ℂ) * ζ ^ 10
          + ((22 / 17) : ℂ) * ζ ^ 13
          + ((1 / 17) : ℂ) * ζ ^ 14
          + ((29 / 34) : ℂ) * ζ ^ 15
          - ((1 / 17) : ℂ) * ζ ^ 18
          - ((29 / 34) : ℂ) * ζ ^ 19
          + ((83 / 34) : ℂ) * ζ ^ 20
          + ((29 / 34) : ℂ) * ζ ^ 23
          - ((83 / 34) : ℂ) * ζ ^ 24
          + ((83 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((41 / 17) : ℂ)
          - ((41 / 17) : ℂ) * ζ ^ 4
          + ((22 / 17) : ℂ) * ζ ^ 5
          + ((41 / 17) : ℂ) * ζ ^ 8
          - ((22 / 17) : ℂ) * ζ ^ 9
          - ((1 / 17) : ℂ) * ζ ^ 10
          + ((22 / 17) : ℂ) * ζ ^ 13
          + ((1 / 17) : ℂ) * ζ ^ 14
          + ((29 / 34) : ℂ) * ζ ^ 15
          - ((1 / 17) : ℂ) * ζ ^ 18
          - ((29 / 34) : ℂ) * ζ ^ 19
          + ((83 / 34) : ℂ) * ζ ^ 20
          + ((29 / 34) : ℂ) * ζ ^ 23
          - ((83 / 34) : ℂ) * ζ ^ 24
          + ((83 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry01_03 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (1 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((10 / 17) : ℂ)
          + ((10 / 17) : ℂ) * ζ ^ 4
          + ((2 / 17) : ℂ) * ζ ^ 5
          - ((10 / 17) : ℂ) * ζ ^ 8
          - ((2 / 17) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 10
          + ((2 / 17) : ℂ) * ζ ^ 13
          + ((7 / 17) : ℂ) * ζ ^ 14
          - ((35 / 17) : ℂ) * ζ ^ 15
          - ((7 / 17) : ℂ) * ζ ^ 18
          + ((35 / 17) : ℂ) * ζ ^ 19
          + ((9 / 17) : ℂ) * ζ ^ 20
          - ((35 / 17) : ℂ) * ζ ^ 23
          - ((9 / 17) : ℂ) * ζ ^ 24
          + ((9 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((10 / 17) : ℂ)
          + ((10 / 17) : ℂ) * ζ ^ 4
          + ((2 / 17) : ℂ) * ζ ^ 5
          - ((10 / 17) : ℂ) * ζ ^ 8
          - ((2 / 17) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 10
          + ((2 / 17) : ℂ) * ζ ^ 13
          + ((7 / 17) : ℂ) * ζ ^ 14
          - ((35 / 17) : ℂ) * ζ ^ 15
          - ((7 / 17) : ℂ) * ζ ^ 18
          + ((35 / 17) : ℂ) * ζ ^ 19
          + ((9 / 17) : ℂ) * ζ ^ 20
          - ((35 / 17) : ℂ) * ζ ^ 23
          - ((9 / 17) : ℂ) * ζ ^ 24
          + ((9 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry01_04 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (1 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(3 : ℂ)
          + (3 : ℂ) * ζ ^ 4
          - ((23 / 34) : ℂ) * ζ ^ 5
          - (3 : ℂ) * ζ ^ 8
          + ((23 / 34) : ℂ) * ζ ^ 9
          + ((5 / 34) : ℂ) * ζ ^ 10
          - ((23 / 34) : ℂ) * ζ ^ 13
          - ((5 / 34) : ℂ) * ζ ^ 14
          - ((35 / 34) : ℂ) * ζ ^ 15
          + ((5 / 34) : ℂ) * ζ ^ 18
          + ((35 / 34) : ℂ) * ζ ^ 19
          - ((11 / 17) : ℂ) * ζ ^ 20
          - ((35 / 34) : ℂ) * ζ ^ 23
          + ((11 / 17) : ℂ) * ζ ^ 24
          - ((11 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(3 : ℂ)
          + (3 : ℂ) * ζ ^ 4
          - ((23 / 34) : ℂ) * ζ ^ 5
          - (3 : ℂ) * ζ ^ 8
          + ((23 / 34) : ℂ) * ζ ^ 9
          + ((5 / 34) : ℂ) * ζ ^ 10
          - ((23 / 34) : ℂ) * ζ ^ 13
          - ((5 / 34) : ℂ) * ζ ^ 14
          - ((35 / 34) : ℂ) * ζ ^ 15
          + ((5 / 34) : ℂ) * ζ ^ 18
          + ((35 / 34) : ℂ) * ζ ^ 19
          - ((11 / 17) : ℂ) * ζ ^ 20
          - ((35 / 34) : ℂ) * ζ ^ 23
          + ((11 / 17) : ℂ) * ζ ^ 24
          - ((11 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry01_05 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (1 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((35 / 17) : ℂ)
          - ((35 / 17) : ℂ) * ζ ^ 4
          + ((55 / 34) : ℂ) * ζ ^ 5
          + ((35 / 17) : ℂ) * ζ ^ 8
          - ((55 / 34) : ℂ) * ζ ^ 9
          + ((1 / 2) : ℂ) * ζ ^ 10
          + ((55 / 34) : ℂ) * ζ ^ 13
          - ((1 / 2) : ℂ) * ζ ^ 14
          + ((33 / 17) : ℂ) * ζ ^ 15
          + ((1 / 2) : ℂ) * ζ ^ 18
          - ((33 / 17) : ℂ) * ζ ^ 19
          + ((13 / 34) : ℂ) * ζ ^ 20
          + ((33 / 17) : ℂ) * ζ ^ 23
          - ((13 / 34) : ℂ) * ζ ^ 24
          + ((13 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((35 / 17) : ℂ)
          - ((35 / 17) : ℂ) * ζ ^ 4
          + ((55 / 34) : ℂ) * ζ ^ 5
          + ((35 / 17) : ℂ) * ζ ^ 8
          - ((55 / 34) : ℂ) * ζ ^ 9
          + ((1 / 2) : ℂ) * ζ ^ 10
          + ((55 / 34) : ℂ) * ζ ^ 13
          - ((1 / 2) : ℂ) * ζ ^ 14
          + ((33 / 17) : ℂ) * ζ ^ 15
          + ((1 / 2) : ℂ) * ζ ^ 18
          - ((33 / 17) : ℂ) * ζ ^ 19
          + ((13 / 34) : ℂ) * ζ ^ 20
          + ((33 / 17) : ℂ) * ζ ^ 23
          - ((13 / 34) : ℂ) * ζ ^ 24
          + ((13 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry01_06 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (1 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((3 / 17) : ℂ)
          + ((3 / 17) : ℂ) * ζ ^ 4
          + ((49 / 17) : ℂ) * ζ ^ 5
          - ((3 / 17) : ℂ) * ζ ^ 8
          - ((49 / 17) : ℂ) * ζ ^ 9
          + ((8 / 17) : ℂ) * ζ ^ 10
          + ((49 / 17) : ℂ) * ζ ^ 13
          - ((8 / 17) : ℂ) * ζ ^ 14
          - ((7 / 34) : ℂ) * ζ ^ 15
          + ((8 / 17) : ℂ) * ζ ^ 18
          + ((7 / 34) : ℂ) * ζ ^ 19
          + ((7 / 34) : ℂ) * ζ ^ 20
          - ((7 / 34) : ℂ) * ζ ^ 23
          - ((7 / 34) : ℂ) * ζ ^ 24
          + ((7 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((3 / 17) : ℂ)
          + ((3 / 17) : ℂ) * ζ ^ 4
          + ((49 / 17) : ℂ) * ζ ^ 5
          - ((3 / 17) : ℂ) * ζ ^ 8
          - ((49 / 17) : ℂ) * ζ ^ 9
          + ((8 / 17) : ℂ) * ζ ^ 10
          + ((49 / 17) : ℂ) * ζ ^ 13
          - ((8 / 17) : ℂ) * ζ ^ 14
          - ((7 / 34) : ℂ) * ζ ^ 15
          + ((8 / 17) : ℂ) * ζ ^ 18
          + ((7 / 34) : ℂ) * ζ ^ 19
          + ((7 / 34) : ℂ) * ζ ^ 20
          - ((7 / 34) : ℂ) * ζ ^ 23
          - ((7 / 34) : ℂ) * ζ ^ 24
          + ((7 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry01_07 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (1 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((3 / 34) : ℂ)
          - ((3 / 34) : ℂ) * ζ ^ 4
          - ((27 / 34) : ℂ) * ζ ^ 5
          + ((3 / 34) : ℂ) * ζ ^ 8
          + ((27 / 34) : ℂ) * ζ ^ 9
          + ((18 / 17) : ℂ) * ζ ^ 10
          - ((27 / 34) : ℂ) * ζ ^ 13
          - ((18 / 17) : ℂ) * ζ ^ 14
          + ((3 / 34) : ℂ) * ζ ^ 15
          + ((18 / 17) : ℂ) * ζ ^ 18
          - ((3 / 34) : ℂ) * ζ ^ 19
          - ((19 / 34) : ℂ) * ζ ^ 20
          + ((3 / 34) : ℂ) * ζ ^ 23
          + ((19 / 34) : ℂ) * ζ ^ 24
          - ((19 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((3 / 34) : ℂ)
          - ((3 / 34) : ℂ) * ζ ^ 4
          - ((27 / 34) : ℂ) * ζ ^ 5
          + ((3 / 34) : ℂ) * ζ ^ 8
          + ((27 / 34) : ℂ) * ζ ^ 9
          + ((18 / 17) : ℂ) * ζ ^ 10
          - ((27 / 34) : ℂ) * ζ ^ 13
          - ((18 / 17) : ℂ) * ζ ^ 14
          + ((3 / 34) : ℂ) * ζ ^ 15
          + ((18 / 17) : ℂ) * ζ ^ 18
          - ((3 / 34) : ℂ) * ζ ^ 19
          - ((19 / 34) : ℂ) * ζ ^ 20
          + ((3 / 34) : ℂ) * ζ ^ 23
          + ((19 / 34) : ℂ) * ζ ^ 24
          - ((19 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry01_08 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (1 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
          + ((15 / 17) : ℂ) * ζ ^ 13
          - ((9 / 17) : ℂ) * ζ ^ 15
          + ((9 / 17) : ℂ) * ζ ^ 19
          - ((18 / 17) : ℂ) * ζ ^ 20
          - ((9 / 17) : ℂ) * ζ ^ 23
          + ((18 / 17) : ℂ) * ζ ^ 24
          - ((18 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 17) : ℂ)
          + ((1 / 17) : ℂ) * ζ ^ 4
          + ((15 / 17) : ℂ) * ζ ^ 5
          - ((1 / 17) : ℂ) * ζ ^ 8
          - ((15 / 17) : ℂ) * ζ ^ 9
          + ((15 / 17) : ℂ) * ζ ^ 13
          - ((9 / 17) : ℂ) * ζ ^ 15
          + ((9 / 17) : ℂ) * ζ ^ 19
          - ((18 / 17) : ℂ) * ζ ^ 20
          - ((9 / 17) : ℂ) * ζ ^ 23
          + ((18 / 17) : ℂ) * ζ ^ 24
          - ((18 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry01_09 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (1 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (1 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((23 / 34) : ℂ)
          - ((23 / 34) : ℂ) * ζ ^ 4
          - ((55 / 34) : ℂ) * ζ ^ 5
          + ((23 / 34) : ℂ) * ζ ^ 8
          + ((55 / 34) : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 10
          - ((55 / 34) : ℂ) * ζ ^ 13
          - ((1 / 17) : ℂ) * ζ ^ 14
          + ((10 / 17) : ℂ) * ζ ^ 15
          + ((1 / 17) : ℂ) * ζ ^ 18
          - ((10 / 17) : ℂ) * ζ ^ 19
          + ((16 / 17) : ℂ) * ζ ^ 20
          + ((10 / 17) : ℂ) * ζ ^ 23
          - ((16 / 17) : ℂ) * ζ ^ 24
          + ((16 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((23 / 34) : ℂ)
          - ((23 / 34) : ℂ) * ζ ^ 4
          - ((55 / 34) : ℂ) * ζ ^ 5
          + ((23 / 34) : ℂ) * ζ ^ 8
          + ((55 / 34) : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 10
          - ((55 / 34) : ℂ) * ζ ^ 13
          - ((1 / 17) : ℂ) * ζ ^ 14
          + ((10 / 17) : ℂ) * ζ ^ 15
          + ((1 / 17) : ℂ) * ζ ^ 18
          - ((10 / 17) : ℂ) * ζ ^ 19
          + ((16 / 17) : ℂ) * ζ ^ 20
          + ((10 / 17) : ℂ) * ζ ^ 23
          - ((16 / 17) : ℂ) * ζ ^ 24
          + ((16 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry02_00 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (2 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((11 / 34) : ℂ)
          + ((11 / 34) : ℂ) * ζ ^ 4
          + ((38 / 17) : ℂ) * ζ ^ 5
          - ((11 / 34) : ℂ) * ζ ^ 8
          - ((38 / 17) : ℂ) * ζ ^ 9
          + ((43 / 34) : ℂ) * ζ ^ 10
          + ((38 / 17) : ℂ) * ζ ^ 13
          - ((43 / 34) : ℂ) * ζ ^ 14
          - ((3 / 34) : ℂ) * ζ ^ 15
          + ((43 / 34) : ℂ) * ζ ^ 18
          + ((3 / 34) : ℂ) * ζ ^ 19
          + ((13 / 17) : ℂ) * ζ ^ 20
          - ((3 / 34) : ℂ) * ζ ^ 23
          - ((13 / 17) : ℂ) * ζ ^ 24
          + ((13 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((11 / 34) : ℂ)
          + ((11 / 34) : ℂ) * ζ ^ 4
          + ((38 / 17) : ℂ) * ζ ^ 5
          - ((11 / 34) : ℂ) * ζ ^ 8
          - ((38 / 17) : ℂ) * ζ ^ 9
          + ((43 / 34) : ℂ) * ζ ^ 10
          + ((38 / 17) : ℂ) * ζ ^ 13
          - ((43 / 34) : ℂ) * ζ ^ 14
          - ((3 / 34) : ℂ) * ζ ^ 15
          + ((43 / 34) : ℂ) * ζ ^ 18
          + ((3 / 34) : ℂ) * ζ ^ 19
          + ((13 / 17) : ℂ) * ζ ^ 20
          - ((3 / 34) : ℂ) * ζ ^ 23
          - ((13 / 17) : ℂ) * ζ ^ 24
          + ((13 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry02_01 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (2 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((4 / 17) : ℂ)
          + ((4 / 17) : ℂ) * ζ ^ 4
          + ((7 / 17) : ℂ) * ζ ^ 5
          - ((4 / 17) : ℂ) * ζ ^ 8
          - ((7 / 17) : ℂ) * ζ ^ 9
          + ((30 / 17) : ℂ) * ζ ^ 10
          + ((7 / 17) : ℂ) * ζ ^ 13
          - ((30 / 17) : ℂ) * ζ ^ 14
          + ((33 / 17) : ℂ) * ζ ^ 15
          + ((30 / 17) : ℂ) * ζ ^ 18
          - ((33 / 17) : ℂ) * ζ ^ 19
          - ((3 / 17) : ℂ) * ζ ^ 20
          + ((33 / 17) : ℂ) * ζ ^ 23
          + ((3 / 17) : ℂ) * ζ ^ 24
          - ((3 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((4 / 17) : ℂ)
          + ((4 / 17) : ℂ) * ζ ^ 4
          + ((7 / 17) : ℂ) * ζ ^ 5
          - ((4 / 17) : ℂ) * ζ ^ 8
          - ((7 / 17) : ℂ) * ζ ^ 9
          + ((30 / 17) : ℂ) * ζ ^ 10
          + ((7 / 17) : ℂ) * ζ ^ 13
          - ((30 / 17) : ℂ) * ζ ^ 14
          + ((33 / 17) : ℂ) * ζ ^ 15
          + ((30 / 17) : ℂ) * ζ ^ 18
          - ((33 / 17) : ℂ) * ζ ^ 19
          - ((3 / 17) : ℂ) * ζ ^ 20
          + ((33 / 17) : ℂ) * ζ ^ 23
          + ((3 / 17) : ℂ) * ζ ^ 24
          - ((3 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry02_02 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (2 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((16 / 17) : ℂ)
          - ((16 / 17) : ℂ) * ζ ^ 4
          + ((61 / 17) : ℂ) * ζ ^ 5
          + ((16 / 17) : ℂ) * ζ ^ 8
          - ((61 / 17) : ℂ) * ζ ^ 9
          + ((41 / 17) : ℂ) * ζ ^ 10
          + ((61 / 17) : ℂ) * ζ ^ 13
          - ((41 / 17) : ℂ) * ζ ^ 14
          + ((67 / 17) : ℂ) * ζ ^ 15
          + ((41 / 17) : ℂ) * ζ ^ 18
          - ((67 / 17) : ℂ) * ζ ^ 19
          + ((72 / 17) : ℂ) * ζ ^ 20
          + ((67 / 17) : ℂ) * ζ ^ 23
          - ((72 / 17) : ℂ) * ζ ^ 24
          + ((72 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((16 / 17) : ℂ)
          - ((16 / 17) : ℂ) * ζ ^ 4
          + ((61 / 17) : ℂ) * ζ ^ 5
          + ((16 / 17) : ℂ) * ζ ^ 8
          - ((61 / 17) : ℂ) * ζ ^ 9
          + ((41 / 17) : ℂ) * ζ ^ 10
          + ((61 / 17) : ℂ) * ζ ^ 13
          - ((41 / 17) : ℂ) * ζ ^ 14
          + ((67 / 17) : ℂ) * ζ ^ 15
          + ((41 / 17) : ℂ) * ζ ^ 18
          - ((67 / 17) : ℂ) * ζ ^ 19
          + ((72 / 17) : ℂ) * ζ ^ 20
          + ((67 / 17) : ℂ) * ζ ^ 23
          - ((72 / 17) : ℂ) * ζ ^ 24
          + ((72 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry02_03 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (2 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((29 / 34) : ℂ)
          + ((29 / 34) : ℂ) * ζ ^ 4
          - ((56 / 17) : ℂ) * ζ ^ 5
          - ((29 / 34) : ℂ) * ζ ^ 8
          + ((56 / 17) : ℂ) * ζ ^ 9
          - ((125 / 34) : ℂ) * ζ ^ 10
          - ((56 / 17) : ℂ) * ζ ^ 13
          + ((125 / 34) : ℂ) * ζ ^ 14
          - ((37 / 34) : ℂ) * ζ ^ 15
          - ((125 / 34) : ℂ) * ζ ^ 18
          + ((37 / 34) : ℂ) * ζ ^ 19
          - ((42 / 17) : ℂ) * ζ ^ 20
          - ((37 / 34) : ℂ) * ζ ^ 23
          + ((42 / 17) : ℂ) * ζ ^ 24
          - ((42 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((29 / 34) : ℂ)
          + ((29 / 34) : ℂ) * ζ ^ 4
          - ((56 / 17) : ℂ) * ζ ^ 5
          - ((29 / 34) : ℂ) * ζ ^ 8
          + ((56 / 17) : ℂ) * ζ ^ 9
          - ((125 / 34) : ℂ) * ζ ^ 10
          - ((56 / 17) : ℂ) * ζ ^ 13
          + ((125 / 34) : ℂ) * ζ ^ 14
          - ((37 / 34) : ℂ) * ζ ^ 15
          - ((125 / 34) : ℂ) * ζ ^ 18
          + ((37 / 34) : ℂ) * ζ ^ 19
          - ((42 / 17) : ℂ) * ζ ^ 20
          - ((37 / 34) : ℂ) * ζ ^ 23
          + ((42 / 17) : ℂ) * ζ ^ 24
          - ((42 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry02_04 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (2 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((35 / 17) : ℂ)
          + ((35 / 17) : ℂ) * ζ ^ 4
          - ((46 / 17) : ℂ) * ζ ^ 5
          - ((35 / 17) : ℂ) * ζ ^ 8
          + ((46 / 17) : ℂ) * ζ ^ 9
          - ((88 / 17) : ℂ) * ζ ^ 10
          - ((46 / 17) : ℂ) * ζ ^ 13
          + ((88 / 17) : ℂ) * ζ ^ 14
          - ((32 / 17) : ℂ) * ζ ^ 15
          - ((88 / 17) : ℂ) * ζ ^ 18
          + ((32 / 17) : ℂ) * ζ ^ 19
          - ((69 / 17) : ℂ) * ζ ^ 20
          - ((32 / 17) : ℂ) * ζ ^ 23
          + ((69 / 17) : ℂ) * ζ ^ 24
          - ((69 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((35 / 17) : ℂ)
          + ((35 / 17) : ℂ) * ζ ^ 4
          - ((46 / 17) : ℂ) * ζ ^ 5
          - ((35 / 17) : ℂ) * ζ ^ 8
          + ((46 / 17) : ℂ) * ζ ^ 9
          - ((88 / 17) : ℂ) * ζ ^ 10
          - ((46 / 17) : ℂ) * ζ ^ 13
          + ((88 / 17) : ℂ) * ζ ^ 14
          - ((32 / 17) : ℂ) * ζ ^ 15
          - ((88 / 17) : ℂ) * ζ ^ 18
          + ((32 / 17) : ℂ) * ζ ^ 19
          - ((69 / 17) : ℂ) * ζ ^ 20
          - ((32 / 17) : ℂ) * ζ ^ 23
          + ((69 / 17) : ℂ) * ζ ^ 24
          - ((69 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry02_05 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (2 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((19 / 34) : ℂ)
          - ((19 / 34) : ℂ) * ζ ^ 4
          + ((32 / 17) : ℂ) * ζ ^ 5
          + ((19 / 34) : ℂ) * ζ ^ 8
          - ((32 / 17) : ℂ) * ζ ^ 9
          + ((103 / 34) : ℂ) * ζ ^ 10
          + ((32 / 17) : ℂ) * ζ ^ 13
          - ((103 / 34) : ℂ) * ζ ^ 14
          + ((3 / 2) : ℂ) * ζ ^ 15
          + ((103 / 34) : ℂ) * ζ ^ 18
          - ((3 / 2) : ℂ) * ζ ^ 19
          + ((32 / 17) : ℂ) * ζ ^ 20
          + ((3 / 2) : ℂ) * ζ ^ 23
          - ((32 / 17) : ℂ) * ζ ^ 24
          + ((32 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((19 / 34) : ℂ)
          - ((19 / 34) : ℂ) * ζ ^ 4
          + ((32 / 17) : ℂ) * ζ ^ 5
          + ((19 / 34) : ℂ) * ζ ^ 8
          - ((32 / 17) : ℂ) * ζ ^ 9
          + ((103 / 34) : ℂ) * ζ ^ 10
          + ((32 / 17) : ℂ) * ζ ^ 13
          - ((103 / 34) : ℂ) * ζ ^ 14
          + ((3 / 2) : ℂ) * ζ ^ 15
          + ((103 / 34) : ℂ) * ζ ^ 18
          - ((3 / 2) : ℂ) * ζ ^ 19
          + ((32 / 17) : ℂ) * ζ ^ 20
          + ((3 / 2) : ℂ) * ζ ^ 23
          - ((32 / 17) : ℂ) * ζ ^ 24
          + ((32 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry02_06 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (2 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((19 / 17) : ℂ)
          + ((19 / 17) : ℂ) * ζ ^ 4
          + ((9 / 17) : ℂ) * ζ ^ 5
          - ((19 / 17) : ℂ) * ζ ^ 8
          - ((9 / 17) : ℂ) * ζ ^ 9
          - ((8 / 17) : ℂ) * ζ ^ 10
          + ((9 / 17) : ℂ) * ζ ^ 13
          + ((8 / 17) : ℂ) * ζ ^ 14
          - ((24 / 17) : ℂ) * ζ ^ 15
          - ((8 / 17) : ℂ) * ζ ^ 18
          + ((24 / 17) : ℂ) * ζ ^ 19
          - ((33 / 17) : ℂ) * ζ ^ 20
          - ((24 / 17) : ℂ) * ζ ^ 23
          + ((33 / 17) : ℂ) * ζ ^ 24
          - ((33 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((19 / 17) : ℂ)
          + ((19 / 17) : ℂ) * ζ ^ 4
          + ((9 / 17) : ℂ) * ζ ^ 5
          - ((19 / 17) : ℂ) * ζ ^ 8
          - ((9 / 17) : ℂ) * ζ ^ 9
          - ((8 / 17) : ℂ) * ζ ^ 10
          + ((9 / 17) : ℂ) * ζ ^ 13
          + ((8 / 17) : ℂ) * ζ ^ 14
          - ((24 / 17) : ℂ) * ζ ^ 15
          - ((8 / 17) : ℂ) * ζ ^ 18
          + ((24 / 17) : ℂ) * ζ ^ 19
          - ((33 / 17) : ℂ) * ζ ^ 20
          - ((24 / 17) : ℂ) * ζ ^ 23
          + ((33 / 17) : ℂ) * ζ ^ 24
          - ((33 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry02_07 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (2 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((14 / 17) : ℂ)
          - ((14 / 17) : ℂ) * ζ ^ 4
          + ((4 / 17) : ℂ) * ζ ^ 5
          + ((14 / 17) : ℂ) * ζ ^ 8
          - ((4 / 17) : ℂ) * ζ ^ 9
          + ((20 / 17) : ℂ) * ζ ^ 10
          + ((4 / 17) : ℂ) * ζ ^ 13
          - ((20 / 17) : ℂ) * ζ ^ 14
          - ζ ^ 15
          + ((20 / 17) : ℂ) * ζ ^ 18
          + ζ ^ 19
          + ((5 / 17) : ℂ) * ζ ^ 20
          - ζ ^ 23
          - ((5 / 17) : ℂ) * ζ ^ 24
          + ((5 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((14 / 17) : ℂ)
          - ((14 / 17) : ℂ) * ζ ^ 4
          + ((4 / 17) : ℂ) * ζ ^ 5
          + ((14 / 17) : ℂ) * ζ ^ 8
          - ((4 / 17) : ℂ) * ζ ^ 9
          + ((20 / 17) : ℂ) * ζ ^ 10
          + ((4 / 17) : ℂ) * ζ ^ 13
          - ((20 / 17) : ℂ) * ζ ^ 14
          - ζ ^ 15
          + ((20 / 17) : ℂ) * ζ ^ 18
          + ζ ^ 19
          + ((5 / 17) : ℂ) * ζ ^ 20
          - ζ ^ 23
          - ((5 / 17) : ℂ) * ζ ^ 24
          + ((5 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry02_08 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (2 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((16 / 17) : ℂ)
          + ((16 / 17) : ℂ) * ζ ^ 4
          - ((22 / 17) : ℂ) * ζ ^ 5
          - ((16 / 17) : ℂ) * ζ ^ 8
          + ((22 / 17) : ℂ) * ζ ^ 9
          - ((48 / 17) : ℂ) * ζ ^ 10
          - ((22 / 17) : ℂ) * ζ ^ 13
          + ((48 / 17) : ℂ) * ζ ^ 14
          - ((24 / 17) : ℂ) * ζ ^ 15
          - ((48 / 17) : ℂ) * ζ ^ 18
          + ((24 / 17) : ℂ) * ζ ^ 19
          - ((60 / 17) : ℂ) * ζ ^ 20
          - ((24 / 17) : ℂ) * ζ ^ 23
          + ((60 / 17) : ℂ) * ζ ^ 24
          - ((60 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((16 / 17) : ℂ)
          + ((16 / 17) : ℂ) * ζ ^ 4
          - ((22 / 17) : ℂ) * ζ ^ 5
          - ((16 / 17) : ℂ) * ζ ^ 8
          + ((22 / 17) : ℂ) * ζ ^ 9
          - ((48 / 17) : ℂ) * ζ ^ 10
          - ((22 / 17) : ℂ) * ζ ^ 13
          + ((48 / 17) : ℂ) * ζ ^ 14
          - ((24 / 17) : ℂ) * ζ ^ 15
          - ((48 / 17) : ℂ) * ζ ^ 18
          + ((24 / 17) : ℂ) * ζ ^ 19
          - ((60 / 17) : ℂ) * ζ ^ 20
          - ((24 / 17) : ℂ) * ζ ^ 23
          + ((60 / 17) : ℂ) * ζ ^ 24
          - ((60 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry02_09 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (2 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (2 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((71 / 34) : ℂ)
          + ((71 / 34) : ℂ) * ζ ^ 4
          + ((1 / 17) : ℂ) * ζ ^ 5
          - ((71 / 34) : ℂ) * ζ ^ 8
          - ((1 / 17) : ℂ) * ζ ^ 9
          + ((101 / 34) : ℂ) * ζ ^ 10
          + ((1 / 17) : ℂ) * ζ ^ 13
          - ((101 / 34) : ℂ) * ζ ^ 14
          + ((75 / 34) : ℂ) * ζ ^ 15
          + ((101 / 34) : ℂ) * ζ ^ 18
          - ((75 / 34) : ℂ) * ζ ^ 19
          + ((43 / 17) : ℂ) * ζ ^ 20
          + ((75 / 34) : ℂ) * ζ ^ 23
          - ((43 / 17) : ℂ) * ζ ^ 24
          + ((43 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((71 / 34) : ℂ)
          + ((71 / 34) : ℂ) * ζ ^ 4
          + ((1 / 17) : ℂ) * ζ ^ 5
          - ((71 / 34) : ℂ) * ζ ^ 8
          - ((1 / 17) : ℂ) * ζ ^ 9
          + ((101 / 34) : ℂ) * ζ ^ 10
          + ((1 / 17) : ℂ) * ζ ^ 13
          - ((101 / 34) : ℂ) * ζ ^ 14
          + ((75 / 34) : ℂ) * ζ ^ 15
          + ((101 / 34) : ℂ) * ζ ^ 18
          - ((75 / 34) : ℂ) * ζ ^ 19
          + ((43 / 17) : ℂ) * ζ ^ 20
          + ((75 / 34) : ℂ) * ζ ^ 23
          - ((43 / 17) : ℂ) * ζ ^ 24
          + ((43 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry03_00 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (3 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((41 / 17) : ℂ)
          - ((41 / 17) : ℂ) * ζ ^ 4
          + ((19 / 34) : ℂ) * ζ ^ 5
          + ((41 / 17) : ℂ) * ζ ^ 8
          - ((19 / 34) : ℂ) * ζ ^ 9
          - ((1 / 34) : ℂ) * ζ ^ 10
          + ((19 / 34) : ℂ) * ζ ^ 13
          + ((1 / 34) : ℂ) * ζ ^ 14
          + ((30 / 17) : ℂ) * ζ ^ 15
          - ((1 / 34) : ℂ) * ζ ^ 18
          - ((30 / 17) : ℂ) * ζ ^ 19
          + ((5 / 34) : ℂ) * ζ ^ 20
          + ((30 / 17) : ℂ) * ζ ^ 23
          - ((5 / 34) : ℂ) * ζ ^ 24
          + ((5 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((41 / 17) : ℂ)
          - ((41 / 17) : ℂ) * ζ ^ 4
          + ((19 / 34) : ℂ) * ζ ^ 5
          + ((41 / 17) : ℂ) * ζ ^ 8
          - ((19 / 34) : ℂ) * ζ ^ 9
          - ((1 / 34) : ℂ) * ζ ^ 10
          + ((19 / 34) : ℂ) * ζ ^ 13
          + ((1 / 34) : ℂ) * ζ ^ 14
          + ((30 / 17) : ℂ) * ζ ^ 15
          - ((1 / 34) : ℂ) * ζ ^ 18
          - ((30 / 17) : ℂ) * ζ ^ 19
          + ((5 / 34) : ℂ) * ζ ^ 20
          + ((30 / 17) : ℂ) * ζ ^ 23
          - ((5 / 34) : ℂ) * ζ ^ 24
          + ((5 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry03_01 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (3 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((6 / 17) : ℂ)
          + ((6 / 17) : ℂ) * ζ ^ 4
          + ((4 / 17) : ℂ) * ζ ^ 5
          - ((6 / 17) : ℂ) * ζ ^ 8
          - ((4 / 17) : ℂ) * ζ ^ 9
          - ((36 / 17) : ℂ) * ζ ^ 10
          + ((4 / 17) : ℂ) * ζ ^ 13
          + ((36 / 17) : ℂ) * ζ ^ 14
          - ((33 / 17) : ℂ) * ζ ^ 15
          - ((36 / 17) : ℂ) * ζ ^ 18
          + ((33 / 17) : ℂ) * ζ ^ 19
          + ((10 / 17) : ℂ) * ζ ^ 20
          - ((33 / 17) : ℂ) * ζ ^ 23
          - ((10 / 17) : ℂ) * ζ ^ 24
          + ((10 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((6 / 17) : ℂ)
          + ((6 / 17) : ℂ) * ζ ^ 4
          + ((4 / 17) : ℂ) * ζ ^ 5
          - ((6 / 17) : ℂ) * ζ ^ 8
          - ((4 / 17) : ℂ) * ζ ^ 9
          - ((36 / 17) : ℂ) * ζ ^ 10
          + ((4 / 17) : ℂ) * ζ ^ 13
          + ((36 / 17) : ℂ) * ζ ^ 14
          - ((33 / 17) : ℂ) * ζ ^ 15
          - ((36 / 17) : ℂ) * ζ ^ 18
          + ((33 / 17) : ℂ) * ζ ^ 19
          + ((10 / 17) : ℂ) * ζ ^ 20
          - ((33 / 17) : ℂ) * ζ ^ 23
          - ((10 / 17) : ℂ) * ζ ^ 24
          + ((10 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry03_02 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (3 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((9 / 17) : ℂ)
          - ((9 / 17) : ℂ) * ζ ^ 4
          - ((23 / 17) : ℂ) * ζ ^ 5
          + ((9 / 17) : ℂ) * ζ ^ 8
          + ((23 / 17) : ℂ) * ζ ^ 9
          - ((48 / 17) : ℂ) * ζ ^ 10
          - ((23 / 17) : ℂ) * ζ ^ 13
          + ((48 / 17) : ℂ) * ζ ^ 14
          - ((46 / 17) : ℂ) * ζ ^ 15
          - ((48 / 17) : ℂ) * ζ ^ 18
          + ((46 / 17) : ℂ) * ζ ^ 19
          - ((53 / 17) : ℂ) * ζ ^ 20
          - ((46 / 17) : ℂ) * ζ ^ 23
          + ((53 / 17) : ℂ) * ζ ^ 24
          - ((53 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((9 / 17) : ℂ)
          - ((9 / 17) : ℂ) * ζ ^ 4
          - ((23 / 17) : ℂ) * ζ ^ 5
          + ((9 / 17) : ℂ) * ζ ^ 8
          + ((23 / 17) : ℂ) * ζ ^ 9
          - ((48 / 17) : ℂ) * ζ ^ 10
          - ((23 / 17) : ℂ) * ζ ^ 13
          + ((48 / 17) : ℂ) * ζ ^ 14
          - ((46 / 17) : ℂ) * ζ ^ 15
          - ((48 / 17) : ℂ) * ζ ^ 18
          + ((46 / 17) : ℂ) * ζ ^ 19
          - ((53 / 17) : ℂ) * ζ ^ 20
          - ((46 / 17) : ℂ) * ζ ^ 23
          + ((53 / 17) : ℂ) * ζ ^ 24
          - ((53 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry03_03 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (3 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 17) : ℂ)
          + ((7 / 17) : ℂ) * ζ ^ 4
          - ((3 / 34) : ℂ) * ζ ^ 5
          - ((7 / 17) : ℂ) * ζ ^ 8
          + ((3 / 34) : ℂ) * ζ ^ 9
          + ((101 / 34) : ℂ) * ζ ^ 10
          - ((3 / 34) : ℂ) * ζ ^ 13
          - ((101 / 34) : ℂ) * ζ ^ 14
          - ((14 / 17) : ℂ) * ζ ^ 15
          + ((101 / 34) : ℂ) * ζ ^ 18
          + ((14 / 17) : ℂ) * ζ ^ 19
          + ((33 / 34) : ℂ) * ζ ^ 20
          - ((14 / 17) : ℂ) * ζ ^ 23
          - ((33 / 34) : ℂ) * ζ ^ 24
          + ((33 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 17) : ℂ)
          + ((7 / 17) : ℂ) * ζ ^ 4
          - ((3 / 34) : ℂ) * ζ ^ 5
          - ((7 / 17) : ℂ) * ζ ^ 8
          + ((3 / 34) : ℂ) * ζ ^ 9
          + ((101 / 34) : ℂ) * ζ ^ 10
          - ((3 / 34) : ℂ) * ζ ^ 13
          - ((101 / 34) : ℂ) * ζ ^ 14
          - ((14 / 17) : ℂ) * ζ ^ 15
          + ((101 / 34) : ℂ) * ζ ^ 18
          + ((14 / 17) : ℂ) * ζ ^ 19
          + ((33 / 34) : ℂ) * ζ ^ 20
          - ((14 / 17) : ℂ) * ζ ^ 23
          - ((33 / 34) : ℂ) * ζ ^ 24
          + ((33 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry03_04 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (3 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((24 / 17) : ℂ)
          - ((24 / 17) : ℂ) * ζ ^ 4
          - ((6 / 17) : ℂ) * ζ ^ 5
          + ((24 / 17) : ℂ) * ζ ^ 8
          + ((6 / 17) : ℂ) * ζ ^ 9
          + ((79 / 17) : ℂ) * ζ ^ 10
          - ((6 / 17) : ℂ) * ζ ^ 13
          - ((79 / 17) : ℂ) * ζ ^ 14
          - ((1 / 17) : ℂ) * ζ ^ 15
          + ((79 / 17) : ℂ) * ζ ^ 18
          + ((1 / 17) : ℂ) * ζ ^ 19
          + ((39 / 17) : ℂ) * ζ ^ 20
          - ((1 / 17) : ℂ) * ζ ^ 23
          - ((39 / 17) : ℂ) * ζ ^ 24
          + ((39 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((24 / 17) : ℂ)
          - ((24 / 17) : ℂ) * ζ ^ 4
          - ((6 / 17) : ℂ) * ζ ^ 5
          + ((24 / 17) : ℂ) * ζ ^ 8
          + ((6 / 17) : ℂ) * ζ ^ 9
          + ((79 / 17) : ℂ) * ζ ^ 10
          - ((6 / 17) : ℂ) * ζ ^ 13
          - ((79 / 17) : ℂ) * ζ ^ 14
          - ((1 / 17) : ℂ) * ζ ^ 15
          + ((79 / 17) : ℂ) * ζ ^ 18
          + ((1 / 17) : ℂ) * ζ ^ 19
          + ((39 / 17) : ℂ) * ζ ^ 20
          - ((1 / 17) : ℂ) * ζ ^ 23
          - ((39 / 17) : ℂ) * ζ ^ 24
          + ((39 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry03_05 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (3 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((14 / 17) : ℂ)
          + ((14 / 17) : ℂ) * ζ ^ 4
          - ((7 / 34) : ℂ) * ζ ^ 5
          - ((14 / 17) : ℂ) * ζ ^ 8
          + ((7 / 34) : ℂ) * ζ ^ 9
          - ((123 / 34) : ℂ) * ζ ^ 10
          - ((7 / 34) : ℂ) * ζ ^ 13
          + ((123 / 34) : ℂ) * ζ ^ 14
          - ((20 / 17) : ℂ) * ζ ^ 15
          - ((123 / 34) : ℂ) * ζ ^ 18
          + ((20 / 17) : ℂ) * ζ ^ 19
          - ((13 / 34) : ℂ) * ζ ^ 20
          - ((20 / 17) : ℂ) * ζ ^ 23
          + ((13 / 34) : ℂ) * ζ ^ 24
          - ((13 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((14 / 17) : ℂ)
          + ((14 / 17) : ℂ) * ζ ^ 4
          - ((7 / 34) : ℂ) * ζ ^ 5
          - ((14 / 17) : ℂ) * ζ ^ 8
          + ((7 / 34) : ℂ) * ζ ^ 9
          - ((123 / 34) : ℂ) * ζ ^ 10
          - ((7 / 34) : ℂ) * ζ ^ 13
          + ((123 / 34) : ℂ) * ζ ^ 14
          - ((20 / 17) : ℂ) * ζ ^ 15
          - ((123 / 34) : ℂ) * ζ ^ 18
          + ((20 / 17) : ℂ) * ζ ^ 19
          - ((13 / 34) : ℂ) * ζ ^ 20
          - ((20 / 17) : ℂ) * ζ ^ 23
          + ((13 / 34) : ℂ) * ζ ^ 24
          - ((13 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry03_06 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (3 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((33 / 17) : ℂ)
          + ((33 / 17) : ℂ) * ζ ^ 4
          - ((21 / 17) : ℂ) * ζ ^ 5
          - ((33 / 17) : ℂ) * ζ ^ 8
          + ((21 / 17) : ℂ) * ζ ^ 9
          - ((29 / 17) : ℂ) * ζ ^ 10
          - ((21 / 17) : ℂ) * ζ ^ 13
          + ((29 / 17) : ℂ) * ζ ^ 14
          - ((8 / 17) : ℂ) * ζ ^ 15
          - ((29 / 17) : ℂ) * ζ ^ 18
          + ((8 / 17) : ℂ) * ζ ^ 19
          + ((32 / 17) : ℂ) * ζ ^ 20
          - ((8 / 17) : ℂ) * ζ ^ 23
          - ((32 / 17) : ℂ) * ζ ^ 24
          + ((32 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((33 / 17) : ℂ)
          + ((33 / 17) : ℂ) * ζ ^ 4
          - ((21 / 17) : ℂ) * ζ ^ 5
          - ((33 / 17) : ℂ) * ζ ^ 8
          + ((21 / 17) : ℂ) * ζ ^ 9
          - ((29 / 17) : ℂ) * ζ ^ 10
          - ((21 / 17) : ℂ) * ζ ^ 13
          + ((29 / 17) : ℂ) * ζ ^ 14
          - ((8 / 17) : ℂ) * ζ ^ 15
          - ((29 / 17) : ℂ) * ζ ^ 18
          + ((8 / 17) : ℂ) * ζ ^ 19
          + ((32 / 17) : ℂ) * ζ ^ 20
          - ((8 / 17) : ℂ) * ζ ^ 23
          - ((32 / 17) : ℂ) * ζ ^ 24
          + ((32 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry03_07 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (3 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 17) : ℂ)
          - ((2 / 17) : ℂ) * ζ ^ 4
          + ((8 / 17) : ℂ) * ζ ^ 5
          + ((2 / 17) : ℂ) * ζ ^ 8
          - ((8 / 17) : ℂ) * ζ ^ 9
          - ((9 / 17) : ℂ) * ζ ^ 10
          + ((8 / 17) : ℂ) * ζ ^ 13
          + ((9 / 17) : ℂ) * ζ ^ 14
          + ((30 / 17) : ℂ) * ζ ^ 15
          - ((9 / 17) : ℂ) * ζ ^ 18
          - ((30 / 17) : ℂ) * ζ ^ 19
          - ((6 / 17) : ℂ) * ζ ^ 20
          + ((30 / 17) : ℂ) * ζ ^ 23
          + ((6 / 17) : ℂ) * ζ ^ 24
          - ((6 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 17) : ℂ)
          - ((2 / 17) : ℂ) * ζ ^ 4
          + ((8 / 17) : ℂ) * ζ ^ 5
          + ((2 / 17) : ℂ) * ζ ^ 8
          - ((8 / 17) : ℂ) * ζ ^ 9
          - ((9 / 17) : ℂ) * ζ ^ 10
          + ((8 / 17) : ℂ) * ζ ^ 13
          + ((9 / 17) : ℂ) * ζ ^ 14
          + ((30 / 17) : ℂ) * ζ ^ 15
          - ((9 / 17) : ℂ) * ζ ^ 18
          - ((30 / 17) : ℂ) * ζ ^ 19
          - ((6 / 17) : ℂ) * ζ ^ 20
          + ((30 / 17) : ℂ) * ζ ^ 23
          + ((6 / 17) : ℂ) * ζ ^ 24
          - ((6 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry03_08 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (3 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((6 / 17) : ℂ) * ζ ^ 5
          + ((6 / 17) : ℂ) * ζ ^ 9
          + ((22 / 17) : ℂ) * ζ ^ 10
          - ((6 / 17) : ℂ) * ζ ^ 13
          - ((22 / 17) : ℂ) * ζ ^ 14
          + ((1 / 17) : ℂ) * ζ ^ 15
          + ((22 / 17) : ℂ) * ζ ^ 18
          - ((1 / 17) : ℂ) * ζ ^ 19
          + ((50 / 17) : ℂ) * ζ ^ 20
          + ((1 / 17) : ℂ) * ζ ^ 23
          - ((50 / 17) : ℂ) * ζ ^ 24
          + ((50 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((6 / 17) : ℂ) * ζ ^ 5
          + ((6 / 17) : ℂ) * ζ ^ 9
          + ((22 / 17) : ℂ) * ζ ^ 10
          - ((6 / 17) : ℂ) * ζ ^ 13
          - ((22 / 17) : ℂ) * ζ ^ 14
          + ((1 / 17) : ℂ) * ζ ^ 15
          + ((22 / 17) : ℂ) * ζ ^ 18
          - ((1 / 17) : ℂ) * ζ ^ 19
          + ((50 / 17) : ℂ) * ζ ^ 20
          + ((1 / 17) : ℂ) * ζ ^ 23
          - ((50 / 17) : ℂ) * ζ ^ 24
          + ((50 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry03_09 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (3 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (3 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((32 / 17) : ℂ)
          - ((32 / 17) : ℂ) * ζ ^ 4
          + ((31 / 34) : ℂ) * ζ ^ 5
          + ((32 / 17) : ℂ) * ζ ^ 8
          - ((31 / 34) : ℂ) * ζ ^ 9
          - ((75 / 34) : ℂ) * ζ ^ 10
          + ((31 / 34) : ℂ) * ζ ^ 13
          + ((75 / 34) : ℂ) * ζ ^ 14
          - ((18 / 17) : ℂ) * ζ ^ 15
          - ((75 / 34) : ℂ) * ζ ^ 18
          + ((18 / 17) : ℂ) * ζ ^ 19
          - ((61 / 34) : ℂ) * ζ ^ 20
          - ((18 / 17) : ℂ) * ζ ^ 23
          + ((61 / 34) : ℂ) * ζ ^ 24
          - ((61 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((32 / 17) : ℂ)
          - ((32 / 17) : ℂ) * ζ ^ 4
          + ((31 / 34) : ℂ) * ζ ^ 5
          + ((32 / 17) : ℂ) * ζ ^ 8
          - ((31 / 34) : ℂ) * ζ ^ 9
          - ((75 / 34) : ℂ) * ζ ^ 10
          + ((31 / 34) : ℂ) * ζ ^ 13
          + ((75 / 34) : ℂ) * ζ ^ 14
          - ((18 / 17) : ℂ) * ζ ^ 15
          - ((75 / 34) : ℂ) * ζ ^ 18
          + ((18 / 17) : ℂ) * ζ ^ 19
          - ((61 / 34) : ℂ) * ζ ^ 20
          - ((18 / 17) : ℂ) * ζ ^ 23
          + ((61 / 34) : ℂ) * ζ ^ 24
          - ((61 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry04_00 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (4 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((9 / 34) : ℂ)
          + ((9 / 34) : ℂ) * ζ ^ 4
          - ((1 / 34) : ℂ) * ζ ^ 5
          - ((9 / 34) : ℂ) * ζ ^ 8
          + ((1 / 34) : ℂ) * ζ ^ 9
          - ((1 / 34) : ℂ) * ζ ^ 13
          - ((13 / 34) : ℂ) * ζ ^ 15
          + ((13 / 34) : ℂ) * ζ ^ 19
          - ((9 / 34) : ℂ) * ζ ^ 20
          - ((13 / 34) : ℂ) * ζ ^ 23
          + ((9 / 34) : ℂ) * ζ ^ 24
          - ((9 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((9 / 34) : ℂ)
          + ((9 / 34) : ℂ) * ζ ^ 4
          - ((1 / 34) : ℂ) * ζ ^ 5
          - ((9 / 34) : ℂ) * ζ ^ 8
          + ((1 / 34) : ℂ) * ζ ^ 9
          - ((1 / 34) : ℂ) * ζ ^ 13
          - ((13 / 34) : ℂ) * ζ ^ 15
          + ((13 / 34) : ℂ) * ζ ^ 19
          - ((9 / 34) : ℂ) * ζ ^ 20
          - ((13 / 34) : ℂ) * ζ ^ 23
          + ((9 / 34) : ℂ) * ζ ^ 24
          - ((9 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry04_01 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (4 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 17) : ℂ)
          - ((1 / 17) : ℂ) * ζ ^ 4
          + ((2 / 17) : ℂ) * ζ ^ 5
          + ((1 / 17) : ℂ) * ζ ^ 8
          - ((2 / 17) : ℂ) * ζ ^ 9
          + ((2 / 17) : ℂ) * ζ ^ 13
          + ((9 / 17) : ℂ) * ζ ^ 15
          - ((9 / 17) : ℂ) * ζ ^ 19
          + ((1 / 17) : ℂ) * ζ ^ 20
          + ((9 / 17) : ℂ) * ζ ^ 23
          - ((1 / 17) : ℂ) * ζ ^ 24
          + ((1 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 17) : ℂ)
          - ((1 / 17) : ℂ) * ζ ^ 4
          + ((2 / 17) : ℂ) * ζ ^ 5
          + ((1 / 17) : ℂ) * ζ ^ 8
          - ((2 / 17) : ℂ) * ζ ^ 9
          + ((2 / 17) : ℂ) * ζ ^ 13
          + ((9 / 17) : ℂ) * ζ ^ 15
          - ((9 / 17) : ℂ) * ζ ^ 19
          + ((1 / 17) : ℂ) * ζ ^ 20
          + ((9 / 17) : ℂ) * ζ ^ 23
          - ((1 / 17) : ℂ) * ζ ^ 24
          + ((1 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry04_02 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (4 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 17) : ℂ)
          + ((7 / 17) : ℂ) * ζ ^ 4
          + ((3 / 17) : ℂ) * ζ ^ 5
          - ((7 / 17) : ℂ) * ζ ^ 8
          - ((3 / 17) : ℂ) * ζ ^ 9
          + ((3 / 17) : ℂ) * ζ ^ 13
          + ((22 / 17) : ℂ) * ζ ^ 15
          - ((22 / 17) : ℂ) * ζ ^ 19
          - ((7 / 17) : ℂ) * ζ ^ 20
          + ((22 / 17) : ℂ) * ζ ^ 23
          + ((7 / 17) : ℂ) * ζ ^ 24
          - ((7 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 17) : ℂ)
          + ((7 / 17) : ℂ) * ζ ^ 4
          + ((3 / 17) : ℂ) * ζ ^ 5
          - ((7 / 17) : ℂ) * ζ ^ 8
          - ((3 / 17) : ℂ) * ζ ^ 9
          + ((3 / 17) : ℂ) * ζ ^ 13
          + ((22 / 17) : ℂ) * ζ ^ 15
          - ((22 / 17) : ℂ) * ζ ^ 19
          - ((7 / 17) : ℂ) * ζ ^ 20
          + ((22 / 17) : ℂ) * ζ ^ 23
          + ((7 / 17) : ℂ) * ζ ^ 24
          - ((7 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry04_03 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (4 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((31 / 34) : ℂ)
          - ((31 / 34) : ℂ) * ζ ^ 4
          - ((23 / 34) : ℂ) * ζ ^ 5
          + ((31 / 34) : ℂ) * ζ ^ 8
          + ((23 / 34) : ℂ) * ζ ^ 9
          - ((23 / 34) : ℂ) * ζ ^ 13
          + ((7 / 34) : ℂ) * ζ ^ 15
          - ((7 / 34) : ℂ) * ζ ^ 19
          + ((31 / 34) : ℂ) * ζ ^ 20
          + ((7 / 34) : ℂ) * ζ ^ 23
          - ((31 / 34) : ℂ) * ζ ^ 24
          + ((31 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((31 / 34) : ℂ)
          - ((31 / 34) : ℂ) * ζ ^ 4
          - ((23 / 34) : ℂ) * ζ ^ 5
          + ((31 / 34) : ℂ) * ζ ^ 8
          + ((23 / 34) : ℂ) * ζ ^ 9
          - ((23 / 34) : ℂ) * ζ ^ 13
          + ((7 / 34) : ℂ) * ζ ^ 15
          - ((7 / 34) : ℂ) * ζ ^ 19
          + ((31 / 34) : ℂ) * ζ ^ 20
          + ((7 / 34) : ℂ) * ζ ^ 23
          - ((31 / 34) : ℂ) * ζ ^ 24
          + ((31 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry04_04 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (4 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
          - ((2 / 17) : ℂ) * ζ ^ 15
          + ((2 / 17) : ℂ) * ζ ^ 19
          + ((13 / 17) : ℂ) * ζ ^ 20
          - ((2 / 17) : ℂ) * ζ ^ 23
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
          - ((2 / 17) : ℂ) * ζ ^ 15
          + ((2 / 17) : ℂ) * ζ ^ 19
          + ((13 / 17) : ℂ) * ζ ^ 20
          - ((2 / 17) : ℂ) * ζ ^ 23
          - ((13 / 17) : ℂ) * ζ ^ 24
          + ((13 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry04_05 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (4 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((5 / 34) : ℂ)
          + ((5 / 34) : ℂ) * ζ ^ 4
          + ((7 / 34) : ℂ) * ζ ^ 5
          - ((5 / 34) : ℂ) * ζ ^ 8
          - ((7 / 34) : ℂ) * ζ ^ 9
          + ((7 / 34) : ℂ) * ζ ^ 13
          + ((23 / 34) : ℂ) * ζ ^ 15
          - ((23 / 34) : ℂ) * ζ ^ 19
          - ((5 / 34) : ℂ) * ζ ^ 20
          + ((23 / 34) : ℂ) * ζ ^ 23
          + ((5 / 34) : ℂ) * ζ ^ 24
          - ((5 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((5 / 34) : ℂ)
          + ((5 / 34) : ℂ) * ζ ^ 4
          + ((7 / 34) : ℂ) * ζ ^ 5
          - ((5 / 34) : ℂ) * ζ ^ 8
          - ((7 / 34) : ℂ) * ζ ^ 9
          + ((7 / 34) : ℂ) * ζ ^ 13
          + ((23 / 34) : ℂ) * ζ ^ 15
          - ((23 / 34) : ℂ) * ζ ^ 19
          - ((5 / 34) : ℂ) * ζ ^ 20
          + ((23 / 34) : ℂ) * ζ ^ 23
          + ((5 / 34) : ℂ) * ζ ^ 24
          - ((5 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry04_06 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (4 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry04_07 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (4 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((9 / 17) : ℂ)
          + ((9 / 17) : ℂ) * ζ ^ 4
          - ((1 / 17) : ℂ) * ζ ^ 5
          - ((9 / 17) : ℂ) * ζ ^ 8
          + ((1 / 17) : ℂ) * ζ ^ 9
          - ((1 / 17) : ℂ) * ζ ^ 13
          - ((13 / 17) : ℂ) * ζ ^ 15
          + ((13 / 17) : ℂ) * ζ ^ 19
          - ((9 / 17) : ℂ) * ζ ^ 20
          - ((13 / 17) : ℂ) * ζ ^ 23
          + ((9 / 17) : ℂ) * ζ ^ 24
          - ((9 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((9 / 17) : ℂ)
          + ((9 / 17) : ℂ) * ζ ^ 4
          - ((1 / 17) : ℂ) * ζ ^ 5
          - ((9 / 17) : ℂ) * ζ ^ 8
          + ((1 / 17) : ℂ) * ζ ^ 9
          - ((1 / 17) : ℂ) * ζ ^ 13
          - ((13 / 17) : ℂ) * ζ ^ 15
          + ((13 / 17) : ℂ) * ζ ^ 19
          - ((9 / 17) : ℂ) * ζ ^ 20
          - ((13 / 17) : ℂ) * ζ ^ 23
          + ((9 / 17) : ℂ) * ζ ^ 24
          - ((9 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry04_08 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (4 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((19 / 17) : ℂ)
          - ((19 / 17) : ℂ) * ζ ^ 4
          - ((13 / 17) : ℂ) * ζ ^ 5
          + ((19 / 17) : ℂ) * ζ ^ 8
          + ((13 / 17) : ℂ) * ζ ^ 9
          - ((13 / 17) : ℂ) * ζ ^ 13
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
          - ((13 / 17) : ℂ) * ζ ^ 5
          + ((19 / 17) : ℂ) * ζ ^ 8
          + ((13 / 17) : ℂ) * ζ ^ 9
          - ((13 / 17) : ℂ) * ζ ^ 13
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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry04_09 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (4 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (4 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
          + ((1 / 2) : ℂ) * ζ ^ 15
          - ((1 / 2) : ℂ) * ζ ^ 19
          - ((1 / 2) : ℂ) * ζ ^ 20
          + ((1 / 2) : ℂ) * ζ ^ 23
          + ((1 / 2) : ℂ) * ζ ^ 24
          - ((1 / 2) : ℂ) * ζ ^ 28
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
          + ((1 / 2) : ℂ) * ζ ^ 15
          - ((1 / 2) : ℂ) * ζ ^ 19
          - ((1 / 2) : ℂ) * ζ ^ 20
          + ((1 / 2) : ℂ) * ζ ^ 23
          + ((1 / 2) : ℂ) * ζ ^ 24
          - ((1 / 2) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry05_00 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (5 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((39 / 34) : ℂ)
          + ((39 / 34) : ℂ) * ζ ^ 4
          + ((7 / 34) : ℂ) * ζ ^ 5
          - ((39 / 34) : ℂ) * ζ ^ 8
          - ((7 / 34) : ℂ) * ζ ^ 9
          + ((7 / 34) : ℂ) * ζ ^ 13
          - ((45 / 34) : ℂ) * ζ ^ 15
          + ((45 / 34) : ℂ) * ζ ^ 19
          - ((39 / 34) : ℂ) * ζ ^ 20
          - ((45 / 34) : ℂ) * ζ ^ 23
          + ((39 / 34) : ℂ) * ζ ^ 24
          - ((39 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((39 / 34) : ℂ)
          + ((39 / 34) : ℂ) * ζ ^ 4
          + ((7 / 34) : ℂ) * ζ ^ 5
          - ((39 / 34) : ℂ) * ζ ^ 8
          - ((7 / 34) : ℂ) * ζ ^ 9
          + ((7 / 34) : ℂ) * ζ ^ 13
          - ((45 / 34) : ℂ) * ζ ^ 15
          + ((45 / 34) : ℂ) * ζ ^ 19
          - ((39 / 34) : ℂ) * ζ ^ 20
          - ((45 / 34) : ℂ) * ζ ^ 23
          + ((39 / 34) : ℂ) * ζ ^ 24
          - ((39 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry05_01 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (5 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 17) : ℂ)
          + ((7 / 17) : ℂ) * ζ ^ 4
          - ((14 / 17) : ℂ) * ζ ^ 5
          - ((7 / 17) : ℂ) * ζ ^ 8
          + ((14 / 17) : ℂ) * ζ ^ 9
          - ((14 / 17) : ℂ) * ζ ^ 13
          + ((5 / 17) : ℂ) * ζ ^ 15
          - ((5 / 17) : ℂ) * ζ ^ 19
          - ((7 / 17) : ℂ) * ζ ^ 20
          + ((5 / 17) : ℂ) * ζ ^ 23
          + ((7 / 17) : ℂ) * ζ ^ 24
          - ((7 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 17) : ℂ)
          + ((7 / 17) : ℂ) * ζ ^ 4
          - ((14 / 17) : ℂ) * ζ ^ 5
          - ((7 / 17) : ℂ) * ζ ^ 8
          + ((14 / 17) : ℂ) * ζ ^ 9
          - ((14 / 17) : ℂ) * ζ ^ 13
          + ((5 / 17) : ℂ) * ζ ^ 15
          - ((5 / 17) : ℂ) * ζ ^ 19
          - ((7 / 17) : ℂ) * ζ ^ 20
          + ((5 / 17) : ℂ) * ζ ^ 23
          + ((7 / 17) : ℂ) * ζ ^ 24
          - ((7 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry05_02 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (5 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((19 / 17) : ℂ)
          + ((19 / 17) : ℂ) * ζ ^ 4
          - ((38 / 17) : ℂ) * ζ ^ 5
          - ((19 / 17) : ℂ) * ζ ^ 8
          + ((38 / 17) : ℂ) * ζ ^ 9
          - ((38 / 17) : ℂ) * ζ ^ 13
          - ((1 / 17) : ℂ) * ζ ^ 15
          + ((1 / 17) : ℂ) * ζ ^ 19
          - ((19 / 17) : ℂ) * ζ ^ 20
          - ((1 / 17) : ℂ) * ζ ^ 23
          + ((19 / 17) : ℂ) * ζ ^ 24
          - ((19 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((19 / 17) : ℂ)
          + ((19 / 17) : ℂ) * ζ ^ 4
          - ((38 / 17) : ℂ) * ζ ^ 5
          - ((19 / 17) : ℂ) * ζ ^ 8
          + ((38 / 17) : ℂ) * ζ ^ 9
          - ((38 / 17) : ℂ) * ζ ^ 13
          - ((1 / 17) : ℂ) * ζ ^ 15
          + ((1 / 17) : ℂ) * ζ ^ 19
          - ((19 / 17) : ℂ) * ζ ^ 20
          - ((1 / 17) : ℂ) * ζ ^ 23
          + ((19 / 17) : ℂ) * ζ ^ 24
          - ((19 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry05_03 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (5 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((55 / 34) : ℂ)
          - ((55 / 34) : ℂ) * ζ ^ 4
          - ((9 / 34) : ℂ) * ζ ^ 5
          + ((55 / 34) : ℂ) * ζ ^ 8
          + ((9 / 34) : ℂ) * ζ ^ 9
          - ((9 / 34) : ℂ) * ζ ^ 13
          + ((19 / 34) : ℂ) * ζ ^ 15
          - ((19 / 34) : ℂ) * ζ ^ 19
          + ((55 / 34) : ℂ) * ζ ^ 20
          + ((19 / 34) : ℂ) * ζ ^ 23
          - ((55 / 34) : ℂ) * ζ ^ 24
          + ((55 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((55 / 34) : ℂ)
          - ((55 / 34) : ℂ) * ζ ^ 4
          - ((9 / 34) : ℂ) * ζ ^ 5
          + ((55 / 34) : ℂ) * ζ ^ 8
          + ((9 / 34) : ℂ) * ζ ^ 9
          - ((9 / 34) : ℂ) * ζ ^ 13
          + ((19 / 34) : ℂ) * ζ ^ 15
          - ((19 / 34) : ℂ) * ζ ^ 19
          + ((55 / 34) : ℂ) * ζ ^ 20
          + ((19 / 34) : ℂ) * ζ ^ 23
          - ((55 / 34) : ℂ) * ζ ^ 24
          + ((55 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry05_04 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (5 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((28 / 17) : ℂ)
          - ((28 / 17) : ℂ) * ζ ^ 4
          + ((22 / 17) : ℂ) * ζ ^ 5
          + ((28 / 17) : ℂ) * ζ ^ 8
          - ((22 / 17) : ℂ) * ζ ^ 9
          + ((22 / 17) : ℂ) * ζ ^ 13
          - ((3 / 17) : ℂ) * ζ ^ 15
          + ((3 / 17) : ℂ) * ζ ^ 19
          + ((28 / 17) : ℂ) * ζ ^ 20
          - ((3 / 17) : ℂ) * ζ ^ 23
          - ((28 / 17) : ℂ) * ζ ^ 24
          + ((28 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((28 / 17) : ℂ)
          - ((28 / 17) : ℂ) * ζ ^ 4
          + ((22 / 17) : ℂ) * ζ ^ 5
          + ((28 / 17) : ℂ) * ζ ^ 8
          - ((22 / 17) : ℂ) * ζ ^ 9
          + ((22 / 17) : ℂ) * ζ ^ 13
          - ((3 / 17) : ℂ) * ζ ^ 15
          + ((3 / 17) : ℂ) * ζ ^ 19
          + ((28 / 17) : ℂ) * ζ ^ 20
          - ((3 / 17) : ℂ) * ζ ^ 23
          - ((28 / 17) : ℂ) * ζ ^ 24
          + ((28 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry05_05 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (5 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((33 / 34) : ℂ)
          + ((33 / 34) : ℂ) * ζ ^ 4
          - ((15 / 34) : ℂ) * ζ ^ 5
          - ((33 / 34) : ℂ) * ζ ^ 8
          + ((15 / 34) : ℂ) * ζ ^ 9
          - ((15 / 34) : ℂ) * ζ ^ 13
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
        -((33 / 34) : ℂ)
          + ((33 / 34) : ℂ) * ζ ^ 4
          - ((15 / 34) : ℂ) * ζ ^ 5
          - ((33 / 34) : ℂ) * ζ ^ 8
          + ((15 / 34) : ℂ) * ζ ^ 9
          - ((15 / 34) : ℂ) * ζ ^ 13
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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry05_06 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (5 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
          + ((32 / 17) : ℂ) * ζ ^ 15
          - ((32 / 17) : ℂ) * ζ ^ 19
          + ((13 / 17) : ℂ) * ζ ^ 20
          + ((32 / 17) : ℂ) * ζ ^ 23
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
          + ((32 / 17) : ℂ) * ζ ^ 15
          - ((32 / 17) : ℂ) * ζ ^ 19
          + ((13 / 17) : ℂ) * ζ ^ 20
          + ((32 / 17) : ℂ) * ζ ^ 23
          - ((13 / 17) : ℂ) * ζ ^ 24
          + ((13 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry05_07 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (5 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((5 / 17) : ℂ)
          + ((5 / 17) : ℂ) * ζ ^ 4
          + ((7 / 17) : ℂ) * ζ ^ 5
          - ((5 / 17) : ℂ) * ζ ^ 8
          - ((7 / 17) : ℂ) * ζ ^ 9
          + ((7 / 17) : ℂ) * ζ ^ 13
          - ((11 / 17) : ℂ) * ζ ^ 15
          + ((11 / 17) : ℂ) * ζ ^ 19
          - ((5 / 17) : ℂ) * ζ ^ 20
          - ((11 / 17) : ℂ) * ζ ^ 23
          + ((5 / 17) : ℂ) * ζ ^ 24
          - ((5 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((5 / 17) : ℂ)
          + ((5 / 17) : ℂ) * ζ ^ 4
          + ((7 / 17) : ℂ) * ζ ^ 5
          - ((5 / 17) : ℂ) * ζ ^ 8
          - ((7 / 17) : ℂ) * ζ ^ 9
          + ((7 / 17) : ℂ) * ζ ^ 13
          - ((11 / 17) : ℂ) * ζ ^ 15
          + ((11 / 17) : ℂ) * ζ ^ 19
          - ((5 / 17) : ℂ) * ζ ^ 20
          - ((11 / 17) : ℂ) * ζ ^ 23
          + ((5 / 17) : ℂ) * ζ ^ 24
          - ((5 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry05_08 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (5 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((20 / 17) : ℂ)
          - ((20 / 17) : ℂ) * ζ ^ 4
          + ((6 / 17) : ℂ) * ζ ^ 5
          + ((20 / 17) : ℂ) * ζ ^ 8
          - ((6 / 17) : ℂ) * ζ ^ 9
          + ((6 / 17) : ℂ) * ζ ^ 13
          + ((10 / 17) : ℂ) * ζ ^ 15
          - ((10 / 17) : ℂ) * ζ ^ 19
          + ((20 / 17) : ℂ) * ζ ^ 20
          + ((10 / 17) : ℂ) * ζ ^ 23
          - ((20 / 17) : ℂ) * ζ ^ 24
          + ((20 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((20 / 17) : ℂ)
          - ((20 / 17) : ℂ) * ζ ^ 4
          + ((6 / 17) : ℂ) * ζ ^ 5
          + ((20 / 17) : ℂ) * ζ ^ 8
          - ((6 / 17) : ℂ) * ζ ^ 9
          + ((6 / 17) : ℂ) * ζ ^ 13
          + ((10 / 17) : ℂ) * ζ ^ 15
          - ((10 / 17) : ℂ) * ζ ^ 19
          + ((20 / 17) : ℂ) * ζ ^ 20
          + ((10 / 17) : ℂ) * ζ ^ 23
          - ((20 / 17) : ℂ) * ζ ^ 24
          + ((20 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry05_09 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (5 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (5 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 2) : ℂ)
          + ((1 / 2) : ℂ) * ζ ^ 4
          - ((1 / 2) : ℂ) * ζ ^ 5
          - ((1 / 2) : ℂ) * ζ ^ 8
          + ((1 / 2) : ℂ) * ζ ^ 9
          - ((1 / 2) : ℂ) * ζ ^ 13
          - ((1 / 2) : ℂ) * ζ ^ 15
          + ((1 / 2) : ℂ) * ζ ^ 19
          - ((1 / 2) : ℂ) * ζ ^ 20
          - ((1 / 2) : ℂ) * ζ ^ 23
          + ((1 / 2) : ℂ) * ζ ^ 24
          - ((1 / 2) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 2) : ℂ)
          + ((1 / 2) : ℂ) * ζ ^ 4
          - ((1 / 2) : ℂ) * ζ ^ 5
          - ((1 / 2) : ℂ) * ζ ^ 8
          + ((1 / 2) : ℂ) * ζ ^ 9
          - ((1 / 2) : ℂ) * ζ ^ 13
          - ((1 / 2) : ℂ) * ζ ^ 15
          + ((1 / 2) : ℂ) * ζ ^ 19
          - ((1 / 2) : ℂ) * ζ ^ 20
          - ((1 / 2) : ℂ) * ζ ^ 23
          + ((1 / 2) : ℂ) * ζ ^ 24
          - ((1 / 2) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry06_00 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (6 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((39 / 17) : ℂ)
          + ((39 / 17) : ℂ) * ζ ^ 4
          - ((93 / 34) : ℂ) * ζ ^ 5
          - ((39 / 17) : ℂ) * ζ ^ 8
          + ((93 / 34) : ℂ) * ζ ^ 9
          - ((61 / 34) : ℂ) * ζ ^ 10
          - ((93 / 34) : ℂ) * ζ ^ 13
          + ((61 / 34) : ℂ) * ζ ^ 14
          - ((135 / 34) : ℂ) * ζ ^ 15
          - ((61 / 34) : ℂ) * ζ ^ 18
          + ((135 / 34) : ℂ) * ζ ^ 19
          - ((47 / 17) : ℂ) * ζ ^ 20
          - ((135 / 34) : ℂ) * ζ ^ 23
          + ((47 / 17) : ℂ) * ζ ^ 24
          - ((47 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((39 / 17) : ℂ)
          + ((39 / 17) : ℂ) * ζ ^ 4
          - ((93 / 34) : ℂ) * ζ ^ 5
          - ((39 / 17) : ℂ) * ζ ^ 8
          + ((93 / 34) : ℂ) * ζ ^ 9
          - ((61 / 34) : ℂ) * ζ ^ 10
          - ((93 / 34) : ℂ) * ζ ^ 13
          + ((61 / 34) : ℂ) * ζ ^ 14
          - ((135 / 34) : ℂ) * ζ ^ 15
          - ((61 / 34) : ℂ) * ζ ^ 18
          + ((135 / 34) : ℂ) * ζ ^ 19
          - ((47 / 17) : ℂ) * ζ ^ 20
          - ((135 / 34) : ℂ) * ζ ^ 23
          + ((47 / 17) : ℂ) * ζ ^ 24
          - ((47 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry06_01 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (6 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((29 / 17) : ℂ)
          - ((29 / 17) : ℂ) * ζ ^ 4
          + ((27 / 17) : ℂ) * ζ ^ 5
          + ((29 / 17) : ℂ) * ζ ^ 8
          - ((27 / 17) : ℂ) * ζ ^ 9
          + ((23 / 17) : ℂ) * ζ ^ 10
          + ((27 / 17) : ℂ) * ζ ^ 13
          - ((23 / 17) : ℂ) * ζ ^ 14
          + ((39 / 17) : ℂ) * ζ ^ 15
          + ((23 / 17) : ℂ) * ζ ^ 18
          - ((39 / 17) : ℂ) * ζ ^ 19
          + ((37 / 17) : ℂ) * ζ ^ 20
          + ((39 / 17) : ℂ) * ζ ^ 23
          - ((37 / 17) : ℂ) * ζ ^ 24
          + ((37 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((29 / 17) : ℂ)
          - ((29 / 17) : ℂ) * ζ ^ 4
          + ((27 / 17) : ℂ) * ζ ^ 5
          + ((29 / 17) : ℂ) * ζ ^ 8
          - ((27 / 17) : ℂ) * ζ ^ 9
          + ((23 / 17) : ℂ) * ζ ^ 10
          + ((27 / 17) : ℂ) * ζ ^ 13
          - ((23 / 17) : ℂ) * ζ ^ 14
          + ((39 / 17) : ℂ) * ζ ^ 15
          + ((23 / 17) : ℂ) * ζ ^ 18
          - ((39 / 17) : ℂ) * ζ ^ 19
          + ((37 / 17) : ℂ) * ζ ^ 20
          + ((39 / 17) : ℂ) * ζ ^ 23
          - ((37 / 17) : ℂ) * ζ ^ 24
          + ((37 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry06_02 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (6 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((38 / 17) : ℂ)
          + ((38 / 17) : ℂ) * ζ ^ 4
          - ((27 / 17) : ℂ) * ζ ^ 5
          - ((38 / 17) : ℂ) * ζ ^ 8
          + ((27 / 17) : ℂ) * ζ ^ 9
          + ((30 / 17) : ℂ) * ζ ^ 10
          - ((27 / 17) : ℂ) * ζ ^ 13
          - ((30 / 17) : ℂ) * ζ ^ 14
          + ((7 / 17) : ℂ) * ζ ^ 15
          + ((30 / 17) : ℂ) * ζ ^ 18
          - ((7 / 17) : ℂ) * ζ ^ 19
          + ((13 / 17) : ℂ) * ζ ^ 20
          + ((7 / 17) : ℂ) * ζ ^ 23
          - ((13 / 17) : ℂ) * ζ ^ 24
          + ((13 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((38 / 17) : ℂ)
          + ((38 / 17) : ℂ) * ζ ^ 4
          - ((27 / 17) : ℂ) * ζ ^ 5
          - ((38 / 17) : ℂ) * ζ ^ 8
          + ((27 / 17) : ℂ) * ζ ^ 9
          + ((30 / 17) : ℂ) * ζ ^ 10
          - ((27 / 17) : ℂ) * ζ ^ 13
          - ((30 / 17) : ℂ) * ζ ^ 14
          + ((7 / 17) : ℂ) * ζ ^ 15
          + ((30 / 17) : ℂ) * ζ ^ 18
          - ((7 / 17) : ℂ) * ζ ^ 19
          + ((13 / 17) : ℂ) * ζ ^ 20
          + ((7 / 17) : ℂ) * ζ ^ 23
          - ((13 / 17) : ℂ) * ζ ^ 24
          + ((13 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry06_03 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (6 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((23 / 17) : ℂ)
          + ((23 / 17) : ℂ) * ζ ^ 4
          + ((61 / 34) : ℂ) * ζ ^ 5
          - ((23 / 17) : ℂ) * ζ ^ 8
          - ((61 / 34) : ℂ) * ζ ^ 9
          - ((1 / 2) : ℂ) * ζ ^ 10
          + ((61 / 34) : ℂ) * ζ ^ 13
          + ((1 / 2) : ℂ) * ζ ^ 14
          + ((93 / 34) : ℂ) * ζ ^ 15
          - ((1 / 2) : ℂ) * ζ ^ 18
          - ((93 / 34) : ℂ) * ζ ^ 19
          + ((42 / 17) : ℂ) * ζ ^ 20
          + ((93 / 34) : ℂ) * ζ ^ 23
          - ((42 / 17) : ℂ) * ζ ^ 24
          + ((42 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((23 / 17) : ℂ)
          + ((23 / 17) : ℂ) * ζ ^ 4
          + ((61 / 34) : ℂ) * ζ ^ 5
          - ((23 / 17) : ℂ) * ζ ^ 8
          - ((61 / 34) : ℂ) * ζ ^ 9
          - ((1 / 2) : ℂ) * ζ ^ 10
          + ((61 / 34) : ℂ) * ζ ^ 13
          + ((1 / 2) : ℂ) * ζ ^ 14
          + ((93 / 34) : ℂ) * ζ ^ 15
          - ((1 / 2) : ℂ) * ζ ^ 18
          - ((93 / 34) : ℂ) * ζ ^ 19
          + ((42 / 17) : ℂ) * ζ ^ 20
          + ((93 / 34) : ℂ) * ζ ^ 23
          - ((42 / 17) : ℂ) * ζ ^ 24
          + ((42 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry06_04 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (6 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((31 / 17) : ℂ)
          + ((31 / 17) : ℂ) * ζ ^ 4
          + ((29 / 17) : ℂ) * ζ ^ 5
          - ((31 / 17) : ℂ) * ζ ^ 8
          - ((29 / 17) : ℂ) * ζ ^ 9
          - ((22 / 17) : ℂ) * ζ ^ 10
          + ((29 / 17) : ℂ) * ζ ^ 13
          + ((22 / 17) : ℂ) * ζ ^ 14
          + ((33 / 17) : ℂ) * ζ ^ 15
          - ((22 / 17) : ℂ) * ζ ^ 18
          - ((33 / 17) : ℂ) * ζ ^ 19
          + ((35 / 17) : ℂ) * ζ ^ 20
          + ((33 / 17) : ℂ) * ζ ^ 23
          - ((35 / 17) : ℂ) * ζ ^ 24
          + ((35 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((31 / 17) : ℂ)
          + ((31 / 17) : ℂ) * ζ ^ 4
          + ((29 / 17) : ℂ) * ζ ^ 5
          - ((31 / 17) : ℂ) * ζ ^ 8
          - ((29 / 17) : ℂ) * ζ ^ 9
          - ((22 / 17) : ℂ) * ζ ^ 10
          + ((29 / 17) : ℂ) * ζ ^ 13
          + ((22 / 17) : ℂ) * ζ ^ 14
          + ((33 / 17) : ℂ) * ζ ^ 15
          - ((22 / 17) : ℂ) * ζ ^ 18
          - ((33 / 17) : ℂ) * ζ ^ 19
          + ((35 / 17) : ℂ) * ζ ^ 20
          + ((33 / 17) : ℂ) * ζ ^ 23
          - ((35 / 17) : ℂ) * ζ ^ 24
          + ((35 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry06_05 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (6 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((47 / 17) : ℂ)
          - ((47 / 17) : ℂ) * ζ ^ 4
          + ((55 / 34) : ℂ) * ζ ^ 5
          + ((47 / 17) : ℂ) * ζ ^ 8
          - ((55 / 34) : ℂ) * ζ ^ 9
          + ((91 / 34) : ℂ) * ζ ^ 10
          + ((55 / 34) : ℂ) * ζ ^ 13
          - ((91 / 34) : ℂ) * ζ ^ 14
          + ((31 / 34) : ℂ) * ζ ^ 15
          + ((91 / 34) : ℂ) * ζ ^ 18
          - ((31 / 34) : ℂ) * ζ ^ 19
          + ((2 / 17) : ℂ) * ζ ^ 20
          + ((31 / 34) : ℂ) * ζ ^ 23
          - ((2 / 17) : ℂ) * ζ ^ 24
          + ((2 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((47 / 17) : ℂ)
          - ((47 / 17) : ℂ) * ζ ^ 4
          + ((55 / 34) : ℂ) * ζ ^ 5
          + ((47 / 17) : ℂ) * ζ ^ 8
          - ((55 / 34) : ℂ) * ζ ^ 9
          + ((91 / 34) : ℂ) * ζ ^ 10
          + ((55 / 34) : ℂ) * ζ ^ 13
          - ((91 / 34) : ℂ) * ζ ^ 14
          + ((31 / 34) : ℂ) * ζ ^ 15
          + ((91 / 34) : ℂ) * ζ ^ 18
          - ((31 / 34) : ℂ) * ζ ^ 19
          + ((2 / 17) : ℂ) * ζ ^ 20
          + ((31 / 34) : ℂ) * ζ ^ 23
          - ((2 / 17) : ℂ) * ζ ^ 24
          + ((2 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry06_06 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (6 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((60 / 17) : ℂ)
          - ((60 / 17) : ℂ) * ζ ^ 4
          + ((76 / 17) : ℂ) * ζ ^ 5
          + ((60 / 17) : ℂ) * ζ ^ 8
          - ((76 / 17) : ℂ) * ζ ^ 9
          + ((65 / 17) : ℂ) * ζ ^ 10
          + ((76 / 17) : ℂ) * ζ ^ 13
          - ((65 / 17) : ℂ) * ζ ^ 14
          + ((87 / 17) : ℂ) * ζ ^ 15
          + ((65 / 17) : ℂ) * ζ ^ 18
          - ((87 / 17) : ℂ) * ζ ^ 19
          + ((33 / 17) : ℂ) * ζ ^ 20
          + ((87 / 17) : ℂ) * ζ ^ 23
          - ((33 / 17) : ℂ) * ζ ^ 24
          + ((33 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((60 / 17) : ℂ)
          - ((60 / 17) : ℂ) * ζ ^ 4
          + ((76 / 17) : ℂ) * ζ ^ 5
          + ((60 / 17) : ℂ) * ζ ^ 8
          - ((76 / 17) : ℂ) * ζ ^ 9
          + ((65 / 17) : ℂ) * ζ ^ 10
          + ((76 / 17) : ℂ) * ζ ^ 13
          - ((65 / 17) : ℂ) * ζ ^ 14
          + ((87 / 17) : ℂ) * ζ ^ 15
          + ((65 / 17) : ℂ) * ζ ^ 18
          - ((87 / 17) : ℂ) * ζ ^ 19
          + ((33 / 17) : ℂ) * ζ ^ 20
          + ((87 / 17) : ℂ) * ζ ^ 23
          - ((33 / 17) : ℂ) * ζ ^ 24
          + ((33 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry06_07 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (6 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((16 / 17) : ℂ)
          - ((16 / 17) : ℂ) * ζ ^ 4
          - ((21 / 17) : ℂ) * ζ ^ 5
          + ((16 / 17) : ℂ) * ζ ^ 8
          + ((21 / 17) : ℂ) * ζ ^ 9
          - ((21 / 17) : ℂ) * ζ ^ 10
          - ((21 / 17) : ℂ) * ζ ^ 13
          + ((21 / 17) : ℂ) * ζ ^ 14
          - ((19 / 17) : ℂ) * ζ ^ 15
          - ((21 / 17) : ℂ) * ζ ^ 18
          + ((19 / 17) : ℂ) * ζ ^ 19
          - ((22 / 17) : ℂ) * ζ ^ 20
          - ((19 / 17) : ℂ) * ζ ^ 23
          + ((22 / 17) : ℂ) * ζ ^ 24
          - ((22 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((16 / 17) : ℂ)
          - ((16 / 17) : ℂ) * ζ ^ 4
          - ((21 / 17) : ℂ) * ζ ^ 5
          + ((16 / 17) : ℂ) * ζ ^ 8
          + ((21 / 17) : ℂ) * ζ ^ 9
          - ((21 / 17) : ℂ) * ζ ^ 10
          - ((21 / 17) : ℂ) * ζ ^ 13
          + ((21 / 17) : ℂ) * ζ ^ 14
          - ((19 / 17) : ℂ) * ζ ^ 15
          - ((21 / 17) : ℂ) * ζ ^ 18
          + ((19 / 17) : ℂ) * ζ ^ 19
          - ((22 / 17) : ℂ) * ζ ^ 20
          - ((19 / 17) : ℂ) * ζ ^ 23
          + ((22 / 17) : ℂ) * ζ ^ 24
          - ((22 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry06_08 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (6 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((15 / 17) : ℂ)
          - ((15 / 17) : ℂ) * ζ ^ 4
          + ((56 / 17) : ℂ) * ζ ^ 5
          + ((15 / 17) : ℂ) * ζ ^ 8
          - ((56 / 17) : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 10
          + ((56 / 17) : ℂ) * ζ ^ 13
          - ((1 / 17) : ℂ) * ζ ^ 14
          + ((49 / 17) : ℂ) * ζ ^ 15
          + ((1 / 17) : ℂ) * ζ ^ 18
          - ((49 / 17) : ℂ) * ζ ^ 19
          + ((26 / 17) : ℂ) * ζ ^ 20
          + ((49 / 17) : ℂ) * ζ ^ 23
          - ((26 / 17) : ℂ) * ζ ^ 24
          + ((26 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((15 / 17) : ℂ)
          - ((15 / 17) : ℂ) * ζ ^ 4
          + ((56 / 17) : ℂ) * ζ ^ 5
          + ((15 / 17) : ℂ) * ζ ^ 8
          - ((56 / 17) : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 10
          + ((56 / 17) : ℂ) * ζ ^ 13
          - ((1 / 17) : ℂ) * ζ ^ 14
          + ((49 / 17) : ℂ) * ζ ^ 15
          + ((1 / 17) : ℂ) * ζ ^ 18
          - ((49 / 17) : ℂ) * ζ ^ 19
          + ((26 / 17) : ℂ) * ζ ^ 20
          + ((49 / 17) : ℂ) * ζ ^ 23
          - ((26 / 17) : ℂ) * ζ ^ 24
          + ((26 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry06_09 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (6 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (6 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((24 / 17) : ℂ)
          + ((24 / 17) : ℂ) * ζ ^ 4
          - ((87 / 34) : ℂ) * ζ ^ 5
          - ((24 / 17) : ℂ) * ζ ^ 8
          + ((87 / 34) : ℂ) * ζ ^ 9
          + ((35 / 34) : ℂ) * ζ ^ 10
          - ((87 / 34) : ℂ) * ζ ^ 13
          - ((35 / 34) : ℂ) * ζ ^ 14
          - ((7 / 34) : ℂ) * ζ ^ 15
          + ((35 / 34) : ℂ) * ζ ^ 18
          + ((7 / 34) : ℂ) * ζ ^ 19
          - ((9 / 17) : ℂ) * ζ ^ 20
          - ((7 / 34) : ℂ) * ζ ^ 23
          + ((9 / 17) : ℂ) * ζ ^ 24
          - ((9 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((24 / 17) : ℂ)
          + ((24 / 17) : ℂ) * ζ ^ 4
          - ((87 / 34) : ℂ) * ζ ^ 5
          - ((24 / 17) : ℂ) * ζ ^ 8
          + ((87 / 34) : ℂ) * ζ ^ 9
          + ((35 / 34) : ℂ) * ζ ^ 10
          - ((87 / 34) : ℂ) * ζ ^ 13
          - ((35 / 34) : ℂ) * ζ ^ 14
          - ((7 / 34) : ℂ) * ζ ^ 15
          + ((35 / 34) : ℂ) * ζ ^ 18
          + ((7 / 34) : ℂ) * ζ ^ 19
          - ((9 / 17) : ℂ) * ζ ^ 20
          - ((7 / 34) : ℂ) * ζ ^ 23
          + ((9 / 17) : ℂ) * ζ ^ 24
          - ((9 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry07_00 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (7 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((13 / 17) : ℂ)
          - ((13 / 17) : ℂ) * ζ ^ 4
          + ((29 / 34) : ℂ) * ζ ^ 5
          + ((13 / 17) : ℂ) * ζ ^ 8
          - ((29 / 34) : ℂ) * ζ ^ 9
          + ((5 / 34) : ℂ) * ζ ^ 10
          + ((29 / 34) : ℂ) * ζ ^ 13
          - ((5 / 34) : ℂ) * ζ ^ 14
          + ((1 / 17) : ℂ) * ζ ^ 15
          + ((5 / 34) : ℂ) * ζ ^ 18
          - ((1 / 17) : ℂ) * ζ ^ 19
          + ((35 / 34) : ℂ) * ζ ^ 20
          + ((1 / 17) : ℂ) * ζ ^ 23
          - ((35 / 34) : ℂ) * ζ ^ 24
          + ((35 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((13 / 17) : ℂ)
          - ((13 / 17) : ℂ) * ζ ^ 4
          + ((29 / 34) : ℂ) * ζ ^ 5
          + ((13 / 17) : ℂ) * ζ ^ 8
          - ((29 / 34) : ℂ) * ζ ^ 9
          + ((5 / 34) : ℂ) * ζ ^ 10
          + ((29 / 34) : ℂ) * ζ ^ 13
          - ((5 / 34) : ℂ) * ζ ^ 14
          + ((1 / 17) : ℂ) * ζ ^ 15
          + ((5 / 34) : ℂ) * ζ ^ 18
          - ((1 / 17) : ℂ) * ζ ^ 19
          + ((35 / 34) : ℂ) * ζ ^ 20
          + ((1 / 17) : ℂ) * ζ ^ 23
          - ((35 / 34) : ℂ) * ζ ^ 24
          + ((35 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry07_01 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (7 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((5 / 17) : ℂ)
          + ((5 / 17) : ℂ) * ζ ^ 4
          + ((7 / 17) : ℂ) * ζ ^ 5
          - ((5 / 17) : ℂ) * ζ ^ 8
          - ((7 / 17) : ℂ) * ζ ^ 9
          + ((7 / 17) : ℂ) * ζ ^ 13
          - ((9 / 17) : ℂ) * ζ ^ 15
          + ((9 / 17) : ℂ) * ζ ^ 19
          - ((1 / 17) : ℂ) * ζ ^ 20
          - ((9 / 17) : ℂ) * ζ ^ 23
          + ((1 / 17) : ℂ) * ζ ^ 24
          - ((1 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((5 / 17) : ℂ)
          + ((5 / 17) : ℂ) * ζ ^ 4
          + ((7 / 17) : ℂ) * ζ ^ 5
          - ((5 / 17) : ℂ) * ζ ^ 8
          - ((7 / 17) : ℂ) * ζ ^ 9
          + ((7 / 17) : ℂ) * ζ ^ 13
          - ((9 / 17) : ℂ) * ζ ^ 15
          + ((9 / 17) : ℂ) * ζ ^ 19
          - ((1 / 17) : ℂ) * ζ ^ 20
          - ((9 / 17) : ℂ) * ζ ^ 23
          + ((1 / 17) : ℂ) * ζ ^ 24
          - ((1 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry07_02 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (7 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((7 / 17) : ℂ)
          - ((7 / 17) : ℂ) * ζ ^ 4
          + ((15 / 17) : ℂ) * ζ ^ 5
          + ((7 / 17) : ℂ) * ζ ^ 8
          - ((15 / 17) : ℂ) * ζ ^ 9
          + ((2 / 17) : ℂ) * ζ ^ 10
          + ((15 / 17) : ℂ) * ζ ^ 13
          - ((2 / 17) : ℂ) * ζ ^ 14
          - ((1 / 17) : ℂ) * ζ ^ 15
          + ((2 / 17) : ℂ) * ζ ^ 18
          + ((1 / 17) : ℂ) * ζ ^ 19
          - ((10 / 17) : ℂ) * ζ ^ 20
          - ((1 / 17) : ℂ) * ζ ^ 23
          + ((10 / 17) : ℂ) * ζ ^ 24
          - ((10 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((7 / 17) : ℂ)
          - ((7 / 17) : ℂ) * ζ ^ 4
          + ((15 / 17) : ℂ) * ζ ^ 5
          + ((7 / 17) : ℂ) * ζ ^ 8
          - ((15 / 17) : ℂ) * ζ ^ 9
          + ((2 / 17) : ℂ) * ζ ^ 10
          + ((15 / 17) : ℂ) * ζ ^ 13
          - ((2 / 17) : ℂ) * ζ ^ 14
          - ((1 / 17) : ℂ) * ζ ^ 15
          + ((2 / 17) : ℂ) * ζ ^ 18
          + ((1 / 17) : ℂ) * ζ ^ 19
          - ((10 / 17) : ℂ) * ζ ^ 20
          - ((1 / 17) : ℂ) * ζ ^ 23
          + ((10 / 17) : ℂ) * ζ ^ 24
          - ((10 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry07_03 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (7 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((12 / 17) : ℂ)
          + ((12 / 17) : ℂ) * ζ ^ 4
          - ((1 / 34) : ℂ) * ζ ^ 5
          - ((12 / 17) : ℂ) * ζ ^ 8
          + ((1 / 34) : ℂ) * ζ ^ 9
          + ((9 / 34) : ℂ) * ζ ^ 10
          - ((1 / 34) : ℂ) * ζ ^ 13
          - ((9 / 34) : ℂ) * ζ ^ 14
          + ((15 / 17) : ℂ) * ζ ^ 15
          + ((9 / 34) : ℂ) * ζ ^ 18
          - ((15 / 17) : ℂ) * ζ ^ 19
          - ((27 / 34) : ℂ) * ζ ^ 20
          + ((15 / 17) : ℂ) * ζ ^ 23
          + ((27 / 34) : ℂ) * ζ ^ 24
          - ((27 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((12 / 17) : ℂ)
          + ((12 / 17) : ℂ) * ζ ^ 4
          - ((1 / 34) : ℂ) * ζ ^ 5
          - ((12 / 17) : ℂ) * ζ ^ 8
          + ((1 / 34) : ℂ) * ζ ^ 9
          + ((9 / 34) : ℂ) * ζ ^ 10
          - ((1 / 34) : ℂ) * ζ ^ 13
          - ((9 / 34) : ℂ) * ζ ^ 14
          + ((15 / 17) : ℂ) * ζ ^ 15
          + ((9 / 34) : ℂ) * ζ ^ 18
          - ((15 / 17) : ℂ) * ζ ^ 19
          - ((27 / 34) : ℂ) * ζ ^ 20
          + ((15 / 17) : ℂ) * ζ ^ 23
          + ((27 / 34) : ℂ) * ζ ^ 24
          - ((27 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry07_04 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (7 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((3 / 17) : ℂ)
          - ((3 / 17) : ℂ) * ζ ^ 4
          - ((2 / 17) : ℂ) * ζ ^ 5
          + ((3 / 17) : ℂ) * ζ ^ 8
          + ((2 / 17) : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 10
          - ((2 / 17) : ℂ) * ζ ^ 13
          - ((1 / 17) : ℂ) * ζ ^ 14
          + ((20 / 17) : ℂ) * ζ ^ 15
          + ((1 / 17) : ℂ) * ζ ^ 18
          - ((20 / 17) : ℂ) * ζ ^ 19
          - ((15 / 17) : ℂ) * ζ ^ 20
          + ((20 / 17) : ℂ) * ζ ^ 23
          + ((15 / 17) : ℂ) * ζ ^ 24
          - ((15 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((3 / 17) : ℂ)
          - ((3 / 17) : ℂ) * ζ ^ 4
          - ((2 / 17) : ℂ) * ζ ^ 5
          + ((3 / 17) : ℂ) * ζ ^ 8
          + ((2 / 17) : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 10
          - ((2 / 17) : ℂ) * ζ ^ 13
          - ((1 / 17) : ℂ) * ζ ^ 14
          + ((20 / 17) : ℂ) * ζ ^ 15
          + ((1 / 17) : ℂ) * ζ ^ 18
          - ((20 / 17) : ℂ) * ζ ^ 19
          - ((15 / 17) : ℂ) * ζ ^ 20
          + ((20 / 17) : ℂ) * ζ ^ 23
          + ((15 / 17) : ℂ) * ζ ^ 24
          - ((15 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry07_05 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (7 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((25 / 34) : ℂ) * ζ ^ 5
          + ((25 / 34) : ℂ) * ζ ^ 9
          + ((1 / 34) : ℂ) * ζ ^ 10
          - ((25 / 34) : ℂ) * ζ ^ 13
          - ((1 / 34) : ℂ) * ζ ^ 14
          - ((6 / 17) : ℂ) * ζ ^ 15
          + ((1 / 34) : ℂ) * ζ ^ 18
          + ((6 / 17) : ℂ) * ζ ^ 19
          + ((23 / 34) : ℂ) * ζ ^ 20
          - ((6 / 17) : ℂ) * ζ ^ 23
          - ((23 / 34) : ℂ) * ζ ^ 24
          + ((23 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((25 / 34) : ℂ) * ζ ^ 5
          + ((25 / 34) : ℂ) * ζ ^ 9
          + ((1 / 34) : ℂ) * ζ ^ 10
          - ((25 / 34) : ℂ) * ζ ^ 13
          - ((1 / 34) : ℂ) * ζ ^ 14
          - ((6 / 17) : ℂ) * ζ ^ 15
          + ((1 / 34) : ℂ) * ζ ^ 18
          + ((6 / 17) : ℂ) * ζ ^ 19
          + ((23 / 34) : ℂ) * ζ ^ 20
          - ((6 / 17) : ℂ) * ζ ^ 23
          - ((23 / 34) : ℂ) * ζ ^ 24
          + ((23 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry07_06 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (7 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((3 / 17) : ℂ)
          + ((3 / 17) : ℂ) * ζ ^ 4
          - ((24 / 17) : ℂ) * ζ ^ 5
          - ((3 / 17) : ℂ) * ζ ^ 8
          + ((24 / 17) : ℂ) * ζ ^ 9
          - ((2 / 17) : ℂ) * ζ ^ 10
          - ((24 / 17) : ℂ) * ζ ^ 13
          + ((2 / 17) : ℂ) * ζ ^ 14
          + ((9 / 17) : ℂ) * ζ ^ 15
          - ((2 / 17) : ℂ) * ζ ^ 18
          - ((9 / 17) : ℂ) * ζ ^ 19
          + ((9 / 17) : ℂ) * ζ ^ 20
          + ((9 / 17) : ℂ) * ζ ^ 23
          - ((9 / 17) : ℂ) * ζ ^ 24
          + ((9 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((3 / 17) : ℂ)
          + ((3 / 17) : ℂ) * ζ ^ 4
          - ((24 / 17) : ℂ) * ζ ^ 5
          - ((3 / 17) : ℂ) * ζ ^ 8
          + ((24 / 17) : ℂ) * ζ ^ 9
          - ((2 / 17) : ℂ) * ζ ^ 10
          - ((24 / 17) : ℂ) * ζ ^ 13
          + ((2 / 17) : ℂ) * ζ ^ 14
          + ((9 / 17) : ℂ) * ζ ^ 15
          - ((2 / 17) : ℂ) * ζ ^ 18
          - ((9 / 17) : ℂ) * ζ ^ 19
          + ((9 / 17) : ℂ) * ζ ^ 20
          + ((9 / 17) : ℂ) * ζ ^ 23
          - ((9 / 17) : ℂ) * ζ ^ 24
          + ((9 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry07_07 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (7 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((5 / 17) : ℂ)
          - ((5 / 17) : ℂ) * ζ ^ 4
          - ((3 / 17) : ℂ) * ζ ^ 5
          + ((5 / 17) : ℂ) * ζ ^ 8
          + ((3 / 17) : ℂ) * ζ ^ 9
          - ((9 / 17) : ℂ) * ζ ^ 10
          - ((3 / 17) : ℂ) * ζ ^ 13
          + ((9 / 17) : ℂ) * ζ ^ 14
          - ((8 / 17) : ℂ) * ζ ^ 15
          - ((9 / 17) : ℂ) * ζ ^ 18
          + ((8 / 17) : ℂ) * ζ ^ 19
          + ((3 / 17) : ℂ) * ζ ^ 20
          - ((8 / 17) : ℂ) * ζ ^ 23
          - ((3 / 17) : ℂ) * ζ ^ 24
          + ((3 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((5 / 17) : ℂ)
          - ((5 / 17) : ℂ) * ζ ^ 4
          - ((3 / 17) : ℂ) * ζ ^ 5
          + ((5 / 17) : ℂ) * ζ ^ 8
          + ((3 / 17) : ℂ) * ζ ^ 9
          - ((9 / 17) : ℂ) * ζ ^ 10
          - ((3 / 17) : ℂ) * ζ ^ 13
          + ((9 / 17) : ℂ) * ζ ^ 14
          - ((8 / 17) : ℂ) * ζ ^ 15
          - ((9 / 17) : ℂ) * ζ ^ 18
          + ((8 / 17) : ℂ) * ζ ^ 19
          + ((3 / 17) : ℂ) * ζ ^ 20
          - ((8 / 17) : ℂ) * ζ ^ 23
          - ((3 / 17) : ℂ) * ζ ^ 24
          + ((3 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry07_08 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (7 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((6 / 17) : ℂ)
          + ((6 / 17) : ℂ) * ζ ^ 4
          - ((2 / 17) : ℂ) * ζ ^ 5
          - ((6 / 17) : ℂ) * ζ ^ 8
          + ((2 / 17) : ℂ) * ζ ^ 9
          + ((3 / 17) : ℂ) * ζ ^ 10
          - ((2 / 17) : ℂ) * ζ ^ 13
          - ((3 / 17) : ℂ) * ζ ^ 14
          + ((27 / 17) : ℂ) * ζ ^ 15
          + ((3 / 17) : ℂ) * ζ ^ 18
          - ((27 / 17) : ℂ) * ζ ^ 19
          + ((8 / 17) : ℂ) * ζ ^ 20
          + ((27 / 17) : ℂ) * ζ ^ 23
          - ((8 / 17) : ℂ) * ζ ^ 24
          + ((8 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((6 / 17) : ℂ)
          + ((6 / 17) : ℂ) * ζ ^ 4
          - ((2 / 17) : ℂ) * ζ ^ 5
          - ((6 / 17) : ℂ) * ζ ^ 8
          + ((2 / 17) : ℂ) * ζ ^ 9
          + ((3 / 17) : ℂ) * ζ ^ 10
          - ((2 / 17) : ℂ) * ζ ^ 13
          - ((3 / 17) : ℂ) * ζ ^ 14
          + ((27 / 17) : ℂ) * ζ ^ 15
          + ((3 / 17) : ℂ) * ζ ^ 18
          - ((27 / 17) : ℂ) * ζ ^ 19
          + ((8 / 17) : ℂ) * ζ ^ 20
          + ((27 / 17) : ℂ) * ζ ^ 23
          - ((8 / 17) : ℂ) * ζ ^ 24
          + ((8 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry07_09 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (7 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (7 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((5 / 17) : ℂ)
          - ((5 / 17) : ℂ) * ζ ^ 4
          + ((33 / 34) : ℂ) * ζ ^ 5
          + ((5 / 17) : ℂ) * ζ ^ 8
          - ((33 / 34) : ℂ) * ζ ^ 9
          + ((9 / 34) : ℂ) * ζ ^ 10
          + ((33 / 34) : ℂ) * ζ ^ 13
          - ((9 / 34) : ℂ) * ζ ^ 14
          - ((6 / 17) : ℂ) * ζ ^ 15
          + ((9 / 34) : ℂ) * ζ ^ 18
          + ((6 / 17) : ℂ) * ζ ^ 19
          - ((9 / 34) : ℂ) * ζ ^ 20
          - ((6 / 17) : ℂ) * ζ ^ 23
          + ((9 / 34) : ℂ) * ζ ^ 24
          - ((9 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((5 / 17) : ℂ)
          - ((5 / 17) : ℂ) * ζ ^ 4
          + ((33 / 34) : ℂ) * ζ ^ 5
          + ((5 / 17) : ℂ) * ζ ^ 8
          - ((33 / 34) : ℂ) * ζ ^ 9
          + ((9 / 34) : ℂ) * ζ ^ 10
          + ((33 / 34) : ℂ) * ζ ^ 13
          - ((9 / 34) : ℂ) * ζ ^ 14
          - ((6 / 17) : ℂ) * ζ ^ 15
          + ((9 / 34) : ℂ) * ζ ^ 18
          + ((6 / 17) : ℂ) * ζ ^ 19
          - ((9 / 34) : ℂ) * ζ ^ 20
          - ((6 / 17) : ℂ) * ζ ^ 23
          + ((9 / 34) : ℂ) * ζ ^ 24
          - ((9 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry08_00 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (8 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((6 / 17) : ℂ)
          + ((6 / 17) : ℂ) * ζ ^ 4
          + ((65 / 34) : ℂ) * ζ ^ 5
          - ((6 / 17) : ℂ) * ζ ^ 8
          - ((65 / 34) : ℂ) * ζ ^ 9
          + ((25 / 34) : ℂ) * ζ ^ 10
          + ((65 / 34) : ℂ) * ζ ^ 13
          - ((25 / 34) : ℂ) * ζ ^ 14
          + ((20 / 17) : ℂ) * ζ ^ 15
          + ((25 / 34) : ℂ) * ζ ^ 18
          - ((20 / 17) : ℂ) * ζ ^ 19
          + ((31 / 34) : ℂ) * ζ ^ 20
          + ((20 / 17) : ℂ) * ζ ^ 23
          - ((31 / 34) : ℂ) * ζ ^ 24
          + ((31 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((6 / 17) : ℂ)
          + ((6 / 17) : ℂ) * ζ ^ 4
          + ((65 / 34) : ℂ) * ζ ^ 5
          - ((6 / 17) : ℂ) * ζ ^ 8
          - ((65 / 34) : ℂ) * ζ ^ 9
          + ((25 / 34) : ℂ) * ζ ^ 10
          + ((65 / 34) : ℂ) * ζ ^ 13
          - ((25 / 34) : ℂ) * ζ ^ 14
          + ((20 / 17) : ℂ) * ζ ^ 15
          + ((25 / 34) : ℂ) * ζ ^ 18
          - ((20 / 17) : ℂ) * ζ ^ 19
          + ((31 / 34) : ℂ) * ζ ^ 20
          + ((20 / 17) : ℂ) * ζ ^ 23
          - ((31 / 34) : ℂ) * ζ ^ 24
          + ((31 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry08_01 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (8 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((29 / 34) : ℂ)
          + ((29 / 34) : ℂ) * ζ ^ 4
          - ((8 / 17) : ℂ) * ζ ^ 5
          - ((29 / 34) : ℂ) * ζ ^ 8
          + ((8 / 17) : ℂ) * ζ ^ 9
          - ((1 / 34) : ℂ) * ζ ^ 10
          - ((8 / 17) : ℂ) * ζ ^ 13
          + ((1 / 34) : ℂ) * ζ ^ 14
          - ((24 / 17) : ℂ) * ζ ^ 15
          - ((1 / 34) : ℂ) * ζ ^ 18
          + ((24 / 17) : ℂ) * ζ ^ 19
          - ((41 / 34) : ℂ) * ζ ^ 20
          - ((24 / 17) : ℂ) * ζ ^ 23
          + ((41 / 34) : ℂ) * ζ ^ 24
          - ((41 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((29 / 34) : ℂ)
          + ((29 / 34) : ℂ) * ζ ^ 4
          - ((8 / 17) : ℂ) * ζ ^ 5
          - ((29 / 34) : ℂ) * ζ ^ 8
          + ((8 / 17) : ℂ) * ζ ^ 9
          - ((1 / 34) : ℂ) * ζ ^ 10
          - ((8 / 17) : ℂ) * ζ ^ 13
          + ((1 / 34) : ℂ) * ζ ^ 14
          - ((24 / 17) : ℂ) * ζ ^ 15
          - ((1 / 34) : ℂ) * ζ ^ 18
          + ((24 / 17) : ℂ) * ζ ^ 19
          - ((41 / 34) : ℂ) * ζ ^ 20
          - ((24 / 17) : ℂ) * ζ ^ 23
          + ((41 / 34) : ℂ) * ζ ^ 24
          - ((41 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry08_02 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (8 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((36 / 17) : ℂ)
          - ((36 / 17) : ℂ) * ζ ^ 4
          - ((8 / 17) : ℂ) * ζ ^ 5
          + ((36 / 17) : ℂ) * ζ ^ 8
          + ((8 / 17) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 10
          - ((8 / 17) : ℂ) * ζ ^ 13
          + ((7 / 17) : ℂ) * ζ ^ 14
          - ((29 / 34) : ℂ) * ζ ^ 15
          - ((7 / 17) : ℂ) * ζ ^ 18
          + ((29 / 34) : ℂ) * ζ ^ 19
          + ((15 / 34) : ℂ) * ζ ^ 20
          - ((29 / 34) : ℂ) * ζ ^ 23
          - ((15 / 34) : ℂ) * ζ ^ 24
          + ((15 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((36 / 17) : ℂ)
          - ((36 / 17) : ℂ) * ζ ^ 4
          - ((8 / 17) : ℂ) * ζ ^ 5
          + ((36 / 17) : ℂ) * ζ ^ 8
          + ((8 / 17) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 10
          - ((8 / 17) : ℂ) * ζ ^ 13
          + ((7 / 17) : ℂ) * ζ ^ 14
          - ((29 / 34) : ℂ) * ζ ^ 15
          - ((7 / 17) : ℂ) * ζ ^ 18
          + ((29 / 34) : ℂ) * ζ ^ 19
          + ((15 / 34) : ℂ) * ζ ^ 20
          - ((29 / 34) : ℂ) * ζ ^ 23
          - ((15 / 34) : ℂ) * ζ ^ 24
          + ((15 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry08_03 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (8 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((11 / 34) : ℂ)
          + ((11 / 34) : ℂ) * ζ ^ 4
          + ((2 / 17) : ℂ) * ζ ^ 5
          - ((11 / 34) : ℂ) * ζ ^ 8
          - ((2 / 17) : ℂ) * ζ ^ 9
          + ((1 / 34) : ℂ) * ζ ^ 10
          + ((2 / 17) : ℂ) * ζ ^ 13
          - ((1 / 34) : ℂ) * ζ ^ 14
          + ((1 / 34) : ℂ) * ζ ^ 15
          + ((1 / 34) : ℂ) * ζ ^ 18
          - ((1 / 34) : ℂ) * ζ ^ 19
          - ((18 / 17) : ℂ) * ζ ^ 20
          + ((1 / 34) : ℂ) * ζ ^ 23
          + ((18 / 17) : ℂ) * ζ ^ 24
          - ((18 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((11 / 34) : ℂ)
          + ((11 / 34) : ℂ) * ζ ^ 4
          + ((2 / 17) : ℂ) * ζ ^ 5
          - ((11 / 34) : ℂ) * ζ ^ 8
          - ((2 / 17) : ℂ) * ζ ^ 9
          + ((1 / 34) : ℂ) * ζ ^ 10
          + ((2 / 17) : ℂ) * ζ ^ 13
          - ((1 / 34) : ℂ) * ζ ^ 14
          + ((1 / 34) : ℂ) * ζ ^ 15
          + ((1 / 34) : ℂ) * ζ ^ 18
          - ((1 / 34) : ℂ) * ζ ^ 19
          - ((18 / 17) : ℂ) * ζ ^ 20
          + ((1 / 34) : ℂ) * ζ ^ 23
          + ((18 / 17) : ℂ) * ζ ^ 24
          - ((18 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry08_04 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (8 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((10 / 17) : ℂ)
          + ((10 / 17) : ℂ) * ζ ^ 4
          + ((63 / 34) : ℂ) * ζ ^ 5
          - ((10 / 17) : ℂ) * ζ ^ 8
          - ((63 / 34) : ℂ) * ζ ^ 9
          - ((15 / 34) : ℂ) * ζ ^ 10
          + ((63 / 34) : ℂ) * ζ ^ 13
          + ((15 / 34) : ℂ) * ζ ^ 14
          + ((37 / 34) : ℂ) * ζ ^ 15
          - ((15 / 34) : ℂ) * ζ ^ 18
          - ((37 / 34) : ℂ) * ζ ^ 19
          - ((35 / 17) : ℂ) * ζ ^ 20
          + ((37 / 34) : ℂ) * ζ ^ 23
          + ((35 / 17) : ℂ) * ζ ^ 24
          - ((35 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((10 / 17) : ℂ)
          + ((10 / 17) : ℂ) * ζ ^ 4
          + ((63 / 34) : ℂ) * ζ ^ 5
          - ((10 / 17) : ℂ) * ζ ^ 8
          - ((63 / 34) : ℂ) * ζ ^ 9
          - ((15 / 34) : ℂ) * ζ ^ 10
          + ((63 / 34) : ℂ) * ζ ^ 13
          + ((15 / 34) : ℂ) * ζ ^ 14
          + ((37 / 34) : ℂ) * ζ ^ 15
          - ((15 / 34) : ℂ) * ζ ^ 18
          - ((37 / 34) : ℂ) * ζ ^ 19
          - ((35 / 17) : ℂ) * ζ ^ 20
          + ((37 / 34) : ℂ) * ζ ^ 23
          + ((35 / 17) : ℂ) * ζ ^ 24
          - ((35 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry08_05 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (8 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((13 / 34) : ℂ)
          + ((13 / 34) : ℂ) * ζ ^ 4
          - ((55 / 34) : ℂ) * ζ ^ 5
          - ((13 / 34) : ℂ) * ζ ^ 8
          + ((55 / 34) : ℂ) * ζ ^ 9
          - ((12 / 17) : ℂ) * ζ ^ 10
          - ((55 / 34) : ℂ) * ζ ^ 13
          + ((12 / 17) : ℂ) * ζ ^ 14
          - ((27 / 34) : ℂ) * ζ ^ 15
          - ((12 / 17) : ℂ) * ζ ^ 18
          + ((27 / 34) : ℂ) * ζ ^ 19
          - ((9 / 34) : ℂ) * ζ ^ 20
          - ((27 / 34) : ℂ) * ζ ^ 23
          + ((9 / 34) : ℂ) * ζ ^ 24
          - ((9 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((13 / 34) : ℂ)
          + ((13 / 34) : ℂ) * ζ ^ 4
          - ((55 / 34) : ℂ) * ζ ^ 5
          - ((13 / 34) : ℂ) * ζ ^ 8
          + ((55 / 34) : ℂ) * ζ ^ 9
          - ((12 / 17) : ℂ) * ζ ^ 10
          - ((55 / 34) : ℂ) * ζ ^ 13
          + ((12 / 17) : ℂ) * ζ ^ 14
          - ((27 / 34) : ℂ) * ζ ^ 15
          - ((12 / 17) : ℂ) * ζ ^ 18
          + ((27 / 34) : ℂ) * ζ ^ 19
          - ((9 / 34) : ℂ) * ζ ^ 20
          - ((27 / 34) : ℂ) * ζ ^ 23
          + ((9 / 34) : ℂ) * ζ ^ 24
          - ((9 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry08_06 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (8 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((13 / 17) : ℂ)
          + ((13 / 17) : ℂ) * ζ ^ 4
          - ((30 / 17) : ℂ) * ζ ^ 5
          - ((13 / 17) : ℂ) * ζ ^ 8
          + ((30 / 17) : ℂ) * ζ ^ 9
          - ((25 / 17) : ℂ) * ζ ^ 10
          - ((30 / 17) : ℂ) * ζ ^ 13
          + ((25 / 17) : ℂ) * ζ ^ 14
          - ((29 / 34) : ℂ) * ζ ^ 15
          - ((25 / 17) : ℂ) * ζ ^ 18
          + ((29 / 34) : ℂ) * ζ ^ 19
          - ((45 / 34) : ℂ) * ζ ^ 20
          - ((29 / 34) : ℂ) * ζ ^ 23
          + ((45 / 34) : ℂ) * ζ ^ 24
          - ((45 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((13 / 17) : ℂ)
          + ((13 / 17) : ℂ) * ζ ^ 4
          - ((30 / 17) : ℂ) * ζ ^ 5
          - ((13 / 17) : ℂ) * ζ ^ 8
          + ((30 / 17) : ℂ) * ζ ^ 9
          - ((25 / 17) : ℂ) * ζ ^ 10
          - ((30 / 17) : ℂ) * ζ ^ 13
          + ((25 / 17) : ℂ) * ζ ^ 14
          - ((29 / 34) : ℂ) * ζ ^ 15
          - ((25 / 17) : ℂ) * ζ ^ 18
          + ((29 / 34) : ℂ) * ζ ^ 19
          - ((45 / 34) : ℂ) * ζ ^ 20
          - ((29 / 34) : ℂ) * ζ ^ 23
          + ((45 / 34) : ℂ) * ζ ^ 24
          - ((45 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry08_07 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (8 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((35 / 34) : ℂ)
          - ((35 / 34) : ℂ) * ζ ^ 4
          + ((7 / 34) : ℂ) * ζ ^ 5
          + ((35 / 34) : ℂ) * ζ ^ 8
          - ((7 / 34) : ℂ) * ζ ^ 9
          + ((5 / 17) : ℂ) * ζ ^ 10
          + ((7 / 34) : ℂ) * ζ ^ 13
          - ((5 / 17) : ℂ) * ζ ^ 14
          - ((19 / 34) : ℂ) * ζ ^ 15
          + ((5 / 17) : ℂ) * ζ ^ 18
          + ((19 / 34) : ℂ) * ζ ^ 19
          + ((41 / 34) : ℂ) * ζ ^ 20
          - ((19 / 34) : ℂ) * ζ ^ 23
          - ((41 / 34) : ℂ) * ζ ^ 24
          + ((41 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((35 / 34) : ℂ)
          - ((35 / 34) : ℂ) * ζ ^ 4
          + ((7 / 34) : ℂ) * ζ ^ 5
          + ((35 / 34) : ℂ) * ζ ^ 8
          - ((7 / 34) : ℂ) * ζ ^ 9
          + ((5 / 17) : ℂ) * ζ ^ 10
          + ((7 / 34) : ℂ) * ζ ^ 13
          - ((5 / 17) : ℂ) * ζ ^ 14
          - ((19 / 34) : ℂ) * ζ ^ 15
          + ((5 / 17) : ℂ) * ζ ^ 18
          + ((19 / 34) : ℂ) * ζ ^ 19
          + ((41 / 34) : ℂ) * ζ ^ 20
          - ((19 / 34) : ℂ) * ζ ^ 23
          - ((41 / 34) : ℂ) * ζ ^ 24
          + ((41 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry08_08 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (8 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((33 / 17) : ℂ)
          + ((33 / 17) : ℂ) * ζ ^ 4
          + ζ ^ 5
          - ((33 / 17) : ℂ) * ζ ^ 8
          - ζ ^ 9
          - ((21 / 17) : ℂ) * ζ ^ 10
          + ζ ^ 13
          + ((21 / 17) : ℂ) * ζ ^ 14
          + ((9 / 17) : ℂ) * ζ ^ 15
          - ((21 / 17) : ℂ) * ζ ^ 18
          - ((9 / 17) : ℂ) * ζ ^ 19
          - (2 : ℂ) * ζ ^ 20
          + ((9 / 17) : ℂ) * ζ ^ 23
          + (2 : ℂ) * ζ ^ 24
          - (2 : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((33 / 17) : ℂ)
          + ((33 / 17) : ℂ) * ζ ^ 4
          + ζ ^ 5
          - ((33 / 17) : ℂ) * ζ ^ 8
          - ζ ^ 9
          - ((21 / 17) : ℂ) * ζ ^ 10
          + ζ ^ 13
          + ((21 / 17) : ℂ) * ζ ^ 14
          + ((9 / 17) : ℂ) * ζ ^ 15
          - ((21 / 17) : ℂ) * ζ ^ 18
          - ((9 / 17) : ℂ) * ζ ^ 19
          - (2 : ℂ) * ζ ^ 20
          + ((9 / 17) : ℂ) * ζ ^ 23
          + (2 : ℂ) * ζ ^ 24
          - (2 : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry08_09 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (8 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (8 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((12 / 17) : ℂ)
          - ((12 / 17) : ℂ) * ζ ^ 4
          - ((33 / 34) : ℂ) * ζ ^ 5
          + ((12 / 17) : ℂ) * ζ ^ 8
          + ((33 / 34) : ℂ) * ζ ^ 9
          + ((25 / 34) : ℂ) * ζ ^ 10
          - ((33 / 34) : ℂ) * ζ ^ 13
          - ((25 / 34) : ℂ) * ζ ^ 14
          - ((5 / 34) : ℂ) * ζ ^ 15
          + ((25 / 34) : ℂ) * ζ ^ 18
          + ((5 / 34) : ℂ) * ζ ^ 19
          + ((13 / 17) : ℂ) * ζ ^ 20
          - ((5 / 34) : ℂ) * ζ ^ 23
          - ((13 / 17) : ℂ) * ζ ^ 24
          + ((13 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((12 / 17) : ℂ)
          - ((12 / 17) : ℂ) * ζ ^ 4
          - ((33 / 34) : ℂ) * ζ ^ 5
          + ((12 / 17) : ℂ) * ζ ^ 8
          + ((33 / 34) : ℂ) * ζ ^ 9
          + ((25 / 34) : ℂ) * ζ ^ 10
          - ((33 / 34) : ℂ) * ζ ^ 13
          - ((25 / 34) : ℂ) * ζ ^ 14
          - ((5 / 34) : ℂ) * ζ ^ 15
          + ((25 / 34) : ℂ) * ζ ^ 18
          + ((5 / 34) : ℂ) * ζ ^ 19
          + ((13 / 17) : ℂ) * ζ ^ 20
          - ((5 / 34) : ℂ) * ζ ^ 23
          - ((13 / 17) : ℂ) * ζ ^ 24
          + ((13 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry09_00 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (9 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((33 / 34) : ℂ)
          - ((33 / 34) : ℂ) * ζ ^ 4
          + ((37 / 34) : ℂ) * ζ ^ 5
          + ((33 / 34) : ℂ) * ζ ^ 8
          - ((37 / 34) : ℂ) * ζ ^ 9
          + ((5 / 17) : ℂ) * ζ ^ 10
          + ((37 / 34) : ℂ) * ζ ^ 13
          - ((5 / 17) : ℂ) * ζ ^ 14
          + ((33 / 17) : ℂ) * ζ ^ 15
          + ((5 / 17) : ℂ) * ζ ^ 18
          - ((33 / 17) : ℂ) * ζ ^ 19
          + ((12 / 17) : ℂ) * ζ ^ 20
          + ((33 / 17) : ℂ) * ζ ^ 23
          - ((12 / 17) : ℂ) * ζ ^ 24
          + ((12 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((33 / 34) : ℂ)
          - ((33 / 34) : ℂ) * ζ ^ 4
          + ((37 / 34) : ℂ) * ζ ^ 5
          + ((33 / 34) : ℂ) * ζ ^ 8
          - ((37 / 34) : ℂ) * ζ ^ 9
          + ((5 / 17) : ℂ) * ζ ^ 10
          + ((37 / 34) : ℂ) * ζ ^ 13
          - ((5 / 17) : ℂ) * ζ ^ 14
          + ((33 / 17) : ℂ) * ζ ^ 15
          + ((5 / 17) : ℂ) * ζ ^ 18
          - ((33 / 17) : ℂ) * ζ ^ 19
          + ((12 / 17) : ℂ) * ζ ^ 20
          + ((33 / 17) : ℂ) * ζ ^ 23
          - ((12 / 17) : ℂ) * ζ ^ 24
          + ((12 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry09_01 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (9 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((13 / 17) : ℂ)
          + ((13 / 17) : ℂ) * ζ ^ 4
          - ((13 / 17) : ℂ) * ζ ^ 5
          - ((13 / 17) : ℂ) * ζ ^ 8
          + ((13 / 17) : ℂ) * ζ ^ 9
          - ((8 / 17) : ℂ) * ζ ^ 10
          - ((13 / 17) : ℂ) * ζ ^ 13
          + ((8 / 17) : ℂ) * ζ ^ 14
          - ((19 / 17) : ℂ) * ζ ^ 15
          - ((8 / 17) : ℂ) * ζ ^ 18
          + ((19 / 17) : ℂ) * ζ ^ 19
          - ((6 / 17) : ℂ) * ζ ^ 20
          - ((19 / 17) : ℂ) * ζ ^ 23
          + ((6 / 17) : ℂ) * ζ ^ 24
          - ((6 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((13 / 17) : ℂ)
          + ((13 / 17) : ℂ) * ζ ^ 4
          - ((13 / 17) : ℂ) * ζ ^ 5
          - ((13 / 17) : ℂ) * ζ ^ 8
          + ((13 / 17) : ℂ) * ζ ^ 9
          - ((8 / 17) : ℂ) * ζ ^ 10
          - ((13 / 17) : ℂ) * ζ ^ 13
          + ((8 / 17) : ℂ) * ζ ^ 14
          - ((19 / 17) : ℂ) * ζ ^ 15
          - ((8 / 17) : ℂ) * ζ ^ 18
          + ((19 / 17) : ℂ) * ζ ^ 19
          - ((6 / 17) : ℂ) * ζ ^ 20
          - ((19 / 17) : ℂ) * ζ ^ 23
          + ((6 / 17) : ℂ) * ζ ^ 24
          - ((6 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry09_02 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (9 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
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
          - ((22 / 17) : ℂ) * ζ ^ 15
          - ((13 / 17) : ℂ) * ζ ^ 18
          + ((22 / 17) : ℂ) * ζ ^ 19
          - ((9 / 17) : ℂ) * ζ ^ 20
          - ((22 / 17) : ℂ) * ζ ^ 23
          + ((9 / 17) : ℂ) * ζ ^ 24
          - ((9 / 17) : ℂ) * ζ ^ 28
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
          - ((22 / 17) : ℂ) * ζ ^ 15
          - ((13 / 17) : ℂ) * ζ ^ 18
          + ((22 / 17) : ℂ) * ζ ^ 19
          - ((9 / 17) : ℂ) * ζ ^ 20
          - ((22 / 17) : ℂ) * ζ ^ 23
          + ((9 / 17) : ℂ) * ζ ^ 24
          - ((9 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry09_03 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (9 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((1 / 34) : ℂ)
          + ((1 / 34) : ℂ) * ζ ^ 4
          - ((5 / 34) : ℂ) * ζ ^ 5
          - ((1 / 34) : ℂ) * ζ ^ 8
          + ((5 / 34) : ℂ) * ζ ^ 9
          + ((14 / 17) : ℂ) * ζ ^ 10
          - ((5 / 34) : ℂ) * ζ ^ 13
          - ((14 / 17) : ℂ) * ζ ^ 14
          - ((19 / 17) : ℂ) * ζ ^ 15
          + ((14 / 17) : ℂ) * ζ ^ 18
          + ((19 / 17) : ℂ) * ζ ^ 19
          - ((9 / 17) : ℂ) * ζ ^ 20
          - ((19 / 17) : ℂ) * ζ ^ 23
          + ((9 / 17) : ℂ) * ζ ^ 24
          - ((9 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((1 / 34) : ℂ)
          + ((1 / 34) : ℂ) * ζ ^ 4
          - ((5 / 34) : ℂ) * ζ ^ 5
          - ((1 / 34) : ℂ) * ζ ^ 8
          + ((5 / 34) : ℂ) * ζ ^ 9
          + ((14 / 17) : ℂ) * ζ ^ 10
          - ((5 / 34) : ℂ) * ζ ^ 13
          - ((14 / 17) : ℂ) * ζ ^ 14
          - ((19 / 17) : ℂ) * ζ ^ 15
          + ((14 / 17) : ℂ) * ζ ^ 18
          + ((19 / 17) : ℂ) * ζ ^ 19
          - ((9 / 17) : ℂ) * ζ ^ 20
          - ((19 / 17) : ℂ) * ζ ^ 23
          + ((9 / 17) : ℂ) * ζ ^ 24
          - ((9 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry09_04 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (9 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((18 / 17) : ℂ)
          - ((18 / 17) : ℂ) * ζ ^ 4
          + ((5 / 17) : ℂ) * ζ ^ 5
          + ((18 / 17) : ℂ) * ζ ^ 8
          - ((5 / 17) : ℂ) * ζ ^ 9
          + ((23 / 17) : ℂ) * ζ ^ 10
          + ((5 / 17) : ℂ) * ζ ^ 13
          - ((23 / 17) : ℂ) * ζ ^ 14
          - ((1 / 17) : ℂ) * ζ ^ 15
          + ((23 / 17) : ℂ) * ζ ^ 18
          + ((1 / 17) : ℂ) * ζ ^ 19
          - ((9 / 17) : ℂ) * ζ ^ 20
          - ((1 / 17) : ℂ) * ζ ^ 23
          + ((9 / 17) : ℂ) * ζ ^ 24
          - ((9 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((18 / 17) : ℂ)
          - ((18 / 17) : ℂ) * ζ ^ 4
          + ((5 / 17) : ℂ) * ζ ^ 5
          + ((18 / 17) : ℂ) * ζ ^ 8
          - ((5 / 17) : ℂ) * ζ ^ 9
          + ((23 / 17) : ℂ) * ζ ^ 10
          + ((5 / 17) : ℂ) * ζ ^ 13
          - ((23 / 17) : ℂ) * ζ ^ 14
          - ((1 / 17) : ℂ) * ζ ^ 15
          + ((23 / 17) : ℂ) * ζ ^ 18
          + ((1 / 17) : ℂ) * ζ ^ 19
          - ((9 / 17) : ℂ) * ζ ^ 20
          - ((1 / 17) : ℂ) * ζ ^ 23
          + ((9 / 17) : ℂ) * ζ ^ 24
          - ((9 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry09_05 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (9 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((33 / 34) : ℂ)
          + ((33 / 34) : ℂ) * ζ ^ 4
          - ((59 / 34) : ℂ) * ζ ^ 5
          - ((33 / 34) : ℂ) * ζ ^ 8
          + ((59 / 34) : ℂ) * ζ ^ 9
          - ((27 / 17) : ℂ) * ζ ^ 10
          - ((59 / 34) : ℂ) * ζ ^ 13
          + ((27 / 17) : ℂ) * ζ ^ 14
          - ((2 / 17) : ℂ) * ζ ^ 15
          - ((27 / 17) : ℂ) * ζ ^ 18
          + ((2 / 17) : ℂ) * ζ ^ 19
          + ((2 / 17) : ℂ) * ζ ^ 20
          - ((2 / 17) : ℂ) * ζ ^ 23
          - ((2 / 17) : ℂ) * ζ ^ 24
          + ((2 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((33 / 34) : ℂ)
          + ((33 / 34) : ℂ) * ζ ^ 4
          - ((59 / 34) : ℂ) * ζ ^ 5
          - ((33 / 34) : ℂ) * ζ ^ 8
          + ((59 / 34) : ℂ) * ζ ^ 9
          - ((27 / 17) : ℂ) * ζ ^ 10
          - ((59 / 34) : ℂ) * ζ ^ 13
          + ((27 / 17) : ℂ) * ζ ^ 14
          - ((2 / 17) : ℂ) * ζ ^ 15
          - ((27 / 17) : ℂ) * ζ ^ 18
          + ((2 / 17) : ℂ) * ζ ^ 19
          + ((2 / 17) : ℂ) * ζ ^ 20
          - ((2 / 17) : ℂ) * ζ ^ 23
          - ((2 / 17) : ℂ) * ζ ^ 24
          + ((2 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry09_06 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (9 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((11 / 17) : ℂ)
          + ((11 / 17) : ℂ) * ζ ^ 4
          - ((42 / 17) : ℂ) * ζ ^ 5
          - ((11 / 17) : ℂ) * ζ ^ 8
          + ((42 / 17) : ℂ) * ζ ^ 9
          - ((23 / 17) : ℂ) * ζ ^ 10
          - ((42 / 17) : ℂ) * ζ ^ 13
          + ((23 / 17) : ℂ) * ζ ^ 14
          - ((7 / 17) : ℂ) * ζ ^ 15
          - ((23 / 17) : ℂ) * ζ ^ 18
          + ((7 / 17) : ℂ) * ζ ^ 19
          + ((10 / 17) : ℂ) * ζ ^ 20
          - ((7 / 17) : ℂ) * ζ ^ 23
          - ((10 / 17) : ℂ) * ζ ^ 24
          + ((10 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((11 / 17) : ℂ)
          + ((11 / 17) : ℂ) * ζ ^ 4
          - ((42 / 17) : ℂ) * ζ ^ 5
          - ((11 / 17) : ℂ) * ζ ^ 8
          + ((42 / 17) : ℂ) * ζ ^ 9
          - ((23 / 17) : ℂ) * ζ ^ 10
          - ((42 / 17) : ℂ) * ζ ^ 13
          + ((23 / 17) : ℂ) * ζ ^ 14
          - ((7 / 17) : ℂ) * ζ ^ 15
          - ((23 / 17) : ℂ) * ζ ^ 18
          + ((7 / 17) : ℂ) * ζ ^ 19
          + ((10 / 17) : ℂ) * ζ ^ 20
          - ((7 / 17) : ℂ) * ζ ^ 23
          - ((10 / 17) : ℂ) * ζ ^ 24
          + ((10 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry09_07 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (9 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 17) : ℂ)
          - ((1 / 17) : ℂ) * ζ ^ 4
          + ((19 / 17) : ℂ) * ζ ^ 5
          + ((1 / 17) : ℂ) * ζ ^ 8
          - ((19 / 17) : ℂ) * ζ ^ 9
          + ((19 / 17) : ℂ) * ζ ^ 13
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
        ((1 / 17) : ℂ)
          - ((1 / 17) : ℂ) * ζ ^ 4
          + ((19 / 17) : ℂ) * ζ ^ 5
          + ((1 / 17) : ℂ) * ζ ^ 8
          - ((19 / 17) : ℂ) * ζ ^ 9
          + ((19 / 17) : ℂ) * ζ ^ 13
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
private theorem alternatingSixAmbientRow24_longMatrixAB_entry09_08 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (9 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((11 / 17) : ℂ)
          + ((11 / 17) : ℂ) * ζ ^ 4
          - ((18 / 17) : ℂ) * ζ ^ 5
          - ((11 / 17) : ℂ) * ζ ^ 8
          + ((18 / 17) : ℂ) * ζ ^ 9
          + ((8 / 17) : ℂ) * ζ ^ 10
          - ((18 / 17) : ℂ) * ζ ^ 13
          - ((8 / 17) : ℂ) * ζ ^ 14
          + ((16 / 17) : ℂ) * ζ ^ 15
          + ((8 / 17) : ℂ) * ζ ^ 18
          - ((16 / 17) : ℂ) * ζ ^ 19
          + ((16 / 17) : ℂ) * ζ ^ 23
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((11 / 17) : ℂ)
          + ((11 / 17) : ℂ) * ζ ^ 4
          - ((18 / 17) : ℂ) * ζ ^ 5
          - ((11 / 17) : ℂ) * ζ ^ 8
          + ((18 / 17) : ℂ) * ζ ^ 9
          + ((8 / 17) : ℂ) * ζ ^ 10
          - ((18 / 17) : ℂ) * ζ ^ 13
          - ((8 / 17) : ℂ) * ζ ^ 14
          + ((16 / 17) : ℂ) * ζ ^ 15
          + ((8 / 17) : ℂ) * ζ ^ 18
          - ((16 / 17) : ℂ) * ζ ^ 19
          + ((16 / 17) : ℂ) * ζ ^ 23
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longMatrixAB_entry09_09 :
    (alternatingSixFiveAmbient_row24_matrixA
        * alternatingSixFiveAmbient_row24_matrixB)
          (9 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongMatrixAB
        (9 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row24_matrixA,
    alternatingSixFiveAmbient_row24_matrixB,
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((29 / 34) : ℂ)
          - ((29 / 34) : ℂ) * ζ ^ 4
          + ((9 / 34) : ℂ) * ζ ^ 5
          + ((29 / 34) : ℂ) * ζ ^ 8
          - ((9 / 34) : ℂ) * ζ ^ 9
          - ((15 / 17) : ℂ) * ζ ^ 10
          + ((9 / 34) : ℂ) * ζ ^ 13
          + ((15 / 17) : ℂ) * ζ ^ 14
          - ((14 / 17) : ℂ) * ζ ^ 15
          - ((15 / 17) : ℂ) * ζ ^ 18
          + ((14 / 17) : ℂ) * ζ ^ 19
          - ((2 / 17) : ℂ) * ζ ^ 20
          - ((14 / 17) : ℂ) * ζ ^ 23
          + ((2 / 17) : ℂ) * ζ ^ 24
          - ((2 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((29 / 34) : ℂ)
          - ((29 / 34) : ℂ) * ζ ^ 4
          + ((9 / 34) : ℂ) * ζ ^ 5
          + ((29 / 34) : ℂ) * ζ ^ 8
          - ((9 / 34) : ℂ) * ζ ^ 9
          - ((15 / 17) : ℂ) * ζ ^ 10
          + ((9 / 34) : ℂ) * ζ ^ 13
          + ((15 / 17) : ℂ) * ζ ^ 14
          - ((14 / 17) : ℂ) * ζ ^ 15
          - ((15 / 17) : ℂ) * ζ ^ 18
          + ((14 / 17) : ℂ) * ζ ^ 19
          - ((2 / 17) : ℂ) * ζ ^ 20
          - ((14 / 17) : ℂ) * ζ ^ 23
          + ((2 / 17) : ℂ) * ζ ^ 24
          - ((2 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

theorem alternatingSixAmbientRow24_longMatrixAB_mul :
    alternatingSixFiveAmbient_row24_matrixA *
        alternatingSixFiveAmbient_row24_matrixB =
      alternatingSixAmbientRow24LongMatrixAB := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientRow24_longMatrixAB_entry00_00
  · exact alternatingSixAmbientRow24_longMatrixAB_entry00_01
  · exact alternatingSixAmbientRow24_longMatrixAB_entry00_02
  · exact alternatingSixAmbientRow24_longMatrixAB_entry00_03
  · exact alternatingSixAmbientRow24_longMatrixAB_entry00_04
  · exact alternatingSixAmbientRow24_longMatrixAB_entry00_05
  · exact alternatingSixAmbientRow24_longMatrixAB_entry00_06
  · exact alternatingSixAmbientRow24_longMatrixAB_entry00_07
  · exact alternatingSixAmbientRow24_longMatrixAB_entry00_08
  · exact alternatingSixAmbientRow24_longMatrixAB_entry00_09
  · exact alternatingSixAmbientRow24_longMatrixAB_entry01_00
  · exact alternatingSixAmbientRow24_longMatrixAB_entry01_01
  · exact alternatingSixAmbientRow24_longMatrixAB_entry01_02
  · exact alternatingSixAmbientRow24_longMatrixAB_entry01_03
  · exact alternatingSixAmbientRow24_longMatrixAB_entry01_04
  · exact alternatingSixAmbientRow24_longMatrixAB_entry01_05
  · exact alternatingSixAmbientRow24_longMatrixAB_entry01_06
  · exact alternatingSixAmbientRow24_longMatrixAB_entry01_07
  · exact alternatingSixAmbientRow24_longMatrixAB_entry01_08
  · exact alternatingSixAmbientRow24_longMatrixAB_entry01_09
  · exact alternatingSixAmbientRow24_longMatrixAB_entry02_00
  · exact alternatingSixAmbientRow24_longMatrixAB_entry02_01
  · exact alternatingSixAmbientRow24_longMatrixAB_entry02_02
  · exact alternatingSixAmbientRow24_longMatrixAB_entry02_03
  · exact alternatingSixAmbientRow24_longMatrixAB_entry02_04
  · exact alternatingSixAmbientRow24_longMatrixAB_entry02_05
  · exact alternatingSixAmbientRow24_longMatrixAB_entry02_06
  · exact alternatingSixAmbientRow24_longMatrixAB_entry02_07
  · exact alternatingSixAmbientRow24_longMatrixAB_entry02_08
  · exact alternatingSixAmbientRow24_longMatrixAB_entry02_09
  · exact alternatingSixAmbientRow24_longMatrixAB_entry03_00
  · exact alternatingSixAmbientRow24_longMatrixAB_entry03_01
  · exact alternatingSixAmbientRow24_longMatrixAB_entry03_02
  · exact alternatingSixAmbientRow24_longMatrixAB_entry03_03
  · exact alternatingSixAmbientRow24_longMatrixAB_entry03_04
  · exact alternatingSixAmbientRow24_longMatrixAB_entry03_05
  · exact alternatingSixAmbientRow24_longMatrixAB_entry03_06
  · exact alternatingSixAmbientRow24_longMatrixAB_entry03_07
  · exact alternatingSixAmbientRow24_longMatrixAB_entry03_08
  · exact alternatingSixAmbientRow24_longMatrixAB_entry03_09
  · exact alternatingSixAmbientRow24_longMatrixAB_entry04_00
  · exact alternatingSixAmbientRow24_longMatrixAB_entry04_01
  · exact alternatingSixAmbientRow24_longMatrixAB_entry04_02
  · exact alternatingSixAmbientRow24_longMatrixAB_entry04_03
  · exact alternatingSixAmbientRow24_longMatrixAB_entry04_04
  · exact alternatingSixAmbientRow24_longMatrixAB_entry04_05
  · exact alternatingSixAmbientRow24_longMatrixAB_entry04_06
  · exact alternatingSixAmbientRow24_longMatrixAB_entry04_07
  · exact alternatingSixAmbientRow24_longMatrixAB_entry04_08
  · exact alternatingSixAmbientRow24_longMatrixAB_entry04_09
  · exact alternatingSixAmbientRow24_longMatrixAB_entry05_00
  · exact alternatingSixAmbientRow24_longMatrixAB_entry05_01
  · exact alternatingSixAmbientRow24_longMatrixAB_entry05_02
  · exact alternatingSixAmbientRow24_longMatrixAB_entry05_03
  · exact alternatingSixAmbientRow24_longMatrixAB_entry05_04
  · exact alternatingSixAmbientRow24_longMatrixAB_entry05_05
  · exact alternatingSixAmbientRow24_longMatrixAB_entry05_06
  · exact alternatingSixAmbientRow24_longMatrixAB_entry05_07
  · exact alternatingSixAmbientRow24_longMatrixAB_entry05_08
  · exact alternatingSixAmbientRow24_longMatrixAB_entry05_09
  · exact alternatingSixAmbientRow24_longMatrixAB_entry06_00
  · exact alternatingSixAmbientRow24_longMatrixAB_entry06_01
  · exact alternatingSixAmbientRow24_longMatrixAB_entry06_02
  · exact alternatingSixAmbientRow24_longMatrixAB_entry06_03
  · exact alternatingSixAmbientRow24_longMatrixAB_entry06_04
  · exact alternatingSixAmbientRow24_longMatrixAB_entry06_05
  · exact alternatingSixAmbientRow24_longMatrixAB_entry06_06
  · exact alternatingSixAmbientRow24_longMatrixAB_entry06_07
  · exact alternatingSixAmbientRow24_longMatrixAB_entry06_08
  · exact alternatingSixAmbientRow24_longMatrixAB_entry06_09
  · exact alternatingSixAmbientRow24_longMatrixAB_entry07_00
  · exact alternatingSixAmbientRow24_longMatrixAB_entry07_01
  · exact alternatingSixAmbientRow24_longMatrixAB_entry07_02
  · exact alternatingSixAmbientRow24_longMatrixAB_entry07_03
  · exact alternatingSixAmbientRow24_longMatrixAB_entry07_04
  · exact alternatingSixAmbientRow24_longMatrixAB_entry07_05
  · exact alternatingSixAmbientRow24_longMatrixAB_entry07_06
  · exact alternatingSixAmbientRow24_longMatrixAB_entry07_07
  · exact alternatingSixAmbientRow24_longMatrixAB_entry07_08
  · exact alternatingSixAmbientRow24_longMatrixAB_entry07_09
  · exact alternatingSixAmbientRow24_longMatrixAB_entry08_00
  · exact alternatingSixAmbientRow24_longMatrixAB_entry08_01
  · exact alternatingSixAmbientRow24_longMatrixAB_entry08_02
  · exact alternatingSixAmbientRow24_longMatrixAB_entry08_03
  · exact alternatingSixAmbientRow24_longMatrixAB_entry08_04
  · exact alternatingSixAmbientRow24_longMatrixAB_entry08_05
  · exact alternatingSixAmbientRow24_longMatrixAB_entry08_06
  · exact alternatingSixAmbientRow24_longMatrixAB_entry08_07
  · exact alternatingSixAmbientRow24_longMatrixAB_entry08_08
  · exact alternatingSixAmbientRow24_longMatrixAB_entry08_09
  · exact alternatingSixAmbientRow24_longMatrixAB_entry09_00
  · exact alternatingSixAmbientRow24_longMatrixAB_entry09_01
  · exact alternatingSixAmbientRow24_longMatrixAB_entry09_02
  · exact alternatingSixAmbientRow24_longMatrixAB_entry09_03
  · exact alternatingSixAmbientRow24_longMatrixAB_entry09_04
  · exact alternatingSixAmbientRow24_longMatrixAB_entry09_05
  · exact alternatingSixAmbientRow24_longMatrixAB_entry09_06
  · exact alternatingSixAmbientRow24_longMatrixAB_entry09_07
  · exact alternatingSixAmbientRow24_longMatrixAB_entry09_08
  · exact alternatingSixAmbientRow24_longMatrixAB_entry09_09

end InductiveMcKay
end McKayConjecture
