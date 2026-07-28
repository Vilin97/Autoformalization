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
private theorem alternatingSixAmbientRow24_longPrefix77_entry00_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (0 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (0 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((45 / 34) : ℂ)
          + ((45 / 34) : ℂ) * ζ ^ 4
          - ((109 / 34) : ℂ) * ζ ^ 5
          - ((45 / 34) : ℂ) * ζ ^ 8
          + ((109 / 34) : ℂ) * ζ ^ 9
          - ((36 / 17) : ℂ) * ζ ^ 10
          - ((109 / 34) : ℂ) * ζ ^ 13
          + ((36 / 17) : ℂ) * ζ ^ 14
          - ((33 / 17) : ℂ) * ζ ^ 15
          - ((36 / 17) : ℂ) * ζ ^ 18
          + ((33 / 17) : ℂ) * ζ ^ 19
          - ((41 / 17) : ℂ) * ζ ^ 20
          - ((33 / 17) : ℂ) * ζ ^ 23
          + ((41 / 17) : ℂ) * ζ ^ 24
          - ((41 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((45 / 34) : ℂ)
          + ((45 / 34) : ℂ) * ζ ^ 4
          - ((109 / 34) : ℂ) * ζ ^ 5
          - ((45 / 34) : ℂ) * ζ ^ 8
          + ((109 / 34) : ℂ) * ζ ^ 9
          - ((36 / 17) : ℂ) * ζ ^ 10
          - ((109 / 34) : ℂ) * ζ ^ 13
          + ((36 / 17) : ℂ) * ζ ^ 14
          - ((33 / 17) : ℂ) * ζ ^ 15
          - ((36 / 17) : ℂ) * ζ ^ 18
          + ((33 / 17) : ℂ) * ζ ^ 19
          - ((41 / 17) : ℂ) * ζ ^ 20
          - ((33 / 17) : ℂ) * ζ ^ 23
          + ((41 / 17) : ℂ) * ζ ^ 24
          - ((41 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry00_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (0 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (0 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((14 / 17) : ℂ)
          - ((14 / 17) : ℂ) * ζ ^ 4
          + ((9 / 17) : ℂ) * ζ ^ 5
          + ((14 / 17) : ℂ) * ζ ^ 8
          - ((9 / 17) : ℂ) * ζ ^ 9
          + ((13 / 17) : ℂ) * ζ ^ 10
          + ((9 / 17) : ℂ) * ζ ^ 13
          - ((13 / 17) : ℂ) * ζ ^ 14
          + ((37 / 34) : ℂ) * ζ ^ 15
          + ((13 / 17) : ℂ) * ζ ^ 18
          - ((37 / 34) : ℂ) * ζ ^ 19
          + ((21 / 34) : ℂ) * ζ ^ 20
          + ((37 / 34) : ℂ) * ζ ^ 23
          - ((21 / 34) : ℂ) * ζ ^ 24
          + ((21 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((14 / 17) : ℂ)
          - ((14 / 17) : ℂ) * ζ ^ 4
          + ((9 / 17) : ℂ) * ζ ^ 5
          + ((14 / 17) : ℂ) * ζ ^ 8
          - ((9 / 17) : ℂ) * ζ ^ 9
          + ((13 / 17) : ℂ) * ζ ^ 10
          + ((9 / 17) : ℂ) * ζ ^ 13
          - ((13 / 17) : ℂ) * ζ ^ 14
          + ((37 / 34) : ℂ) * ζ ^ 15
          + ((13 / 17) : ℂ) * ζ ^ 18
          - ((37 / 34) : ℂ) * ζ ^ 19
          + ((21 / 34) : ℂ) * ζ ^ 20
          + ((37 / 34) : ℂ) * ζ ^ 23
          - ((21 / 34) : ℂ) * ζ ^ 24
          + ((21 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry00_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (0 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (0 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((67 / 34) : ℂ)
          - ((67 / 34) : ℂ) * ζ ^ 4
          - ((27 / 34) : ℂ) * ζ ^ 5
          + ((67 / 34) : ℂ) * ζ ^ 8
          + ((27 / 34) : ℂ) * ζ ^ 9
          + ((9 / 17) : ℂ) * ζ ^ 10
          - ((27 / 34) : ℂ) * ζ ^ 13
          - ((9 / 17) : ℂ) * ζ ^ 14
          + ((75 / 34) : ℂ) * ζ ^ 15
          + ((9 / 17) : ℂ) * ζ ^ 18
          - ((75 / 34) : ℂ) * ζ ^ 19
          + ((61 / 34) : ℂ) * ζ ^ 20
          + ((75 / 34) : ℂ) * ζ ^ 23
          - ((61 / 34) : ℂ) * ζ ^ 24
          + ((61 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((67 / 34) : ℂ)
          - ((67 / 34) : ℂ) * ζ ^ 4
          - ((27 / 34) : ℂ) * ζ ^ 5
          + ((67 / 34) : ℂ) * ζ ^ 8
          + ((27 / 34) : ℂ) * ζ ^ 9
          + ((9 / 17) : ℂ) * ζ ^ 10
          - ((27 / 34) : ℂ) * ζ ^ 13
          - ((9 / 17) : ℂ) * ζ ^ 14
          + ((75 / 34) : ℂ) * ζ ^ 15
          + ((9 / 17) : ℂ) * ζ ^ 18
          - ((75 / 34) : ℂ) * ζ ^ 19
          + ((61 / 34) : ℂ) * ζ ^ 20
          + ((75 / 34) : ℂ) * ζ ^ 23
          - ((61 / 34) : ℂ) * ζ ^ 24
          + ((61 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry00_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (0 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (0 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((1 / 34) : ℂ)
          - ((1 / 34) : ℂ) * ζ ^ 4
          + ((111 / 34) : ℂ) * ζ ^ 5
          + ((1 / 34) : ℂ) * ζ ^ 8
          - ((111 / 34) : ℂ) * ζ ^ 9
          - ((10 / 17) : ℂ) * ζ ^ 10
          + ((111 / 34) : ℂ) * ζ ^ 13
          + ((10 / 17) : ℂ) * ζ ^ 14
          + ((25 / 34) : ℂ) * ζ ^ 15
          - ((10 / 17) : ℂ) * ζ ^ 18
          - ((25 / 34) : ℂ) * ζ ^ 19
          + ((113 / 34) : ℂ) * ζ ^ 20
          + ((25 / 34) : ℂ) * ζ ^ 23
          - ((113 / 34) : ℂ) * ζ ^ 24
          + ((113 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((1 / 34) : ℂ)
          - ((1 / 34) : ℂ) * ζ ^ 4
          + ((111 / 34) : ℂ) * ζ ^ 5
          + ((1 / 34) : ℂ) * ζ ^ 8
          - ((111 / 34) : ℂ) * ζ ^ 9
          - ((10 / 17) : ℂ) * ζ ^ 10
          + ((111 / 34) : ℂ) * ζ ^ 13
          + ((10 / 17) : ℂ) * ζ ^ 14
          + ((25 / 34) : ℂ) * ζ ^ 15
          - ((10 / 17) : ℂ) * ζ ^ 18
          - ((25 / 34) : ℂ) * ζ ^ 19
          + ((113 / 34) : ℂ) * ζ ^ 20
          + ((25 / 34) : ℂ) * ζ ^ 23
          - ((113 / 34) : ℂ) * ζ ^ 24
          + ((113 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry00_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (0 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (0 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((77 / 34) : ℂ)
          + ((77 / 34) : ℂ) * ζ ^ 4
          + ((52 / 17) : ℂ) * ζ ^ 5
          - ((77 / 34) : ℂ) * ζ ^ 8
          - ((52 / 17) : ℂ) * ζ ^ 9
          - ((45 / 34) : ℂ) * ζ ^ 10
          + ((52 / 17) : ℂ) * ζ ^ 13
          + ((45 / 34) : ℂ) * ζ ^ 14
          - ((24 / 17) : ℂ) * ζ ^ 15
          - ((45 / 34) : ℂ) * ζ ^ 18
          + ((24 / 17) : ℂ) * ζ ^ 19
          + ((67 / 34) : ℂ) * ζ ^ 20
          - ((24 / 17) : ℂ) * ζ ^ 23
          - ((67 / 34) : ℂ) * ζ ^ 24
          + ((67 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((77 / 34) : ℂ)
          + ((77 / 34) : ℂ) * ζ ^ 4
          + ((52 / 17) : ℂ) * ζ ^ 5
          - ((77 / 34) : ℂ) * ζ ^ 8
          - ((52 / 17) : ℂ) * ζ ^ 9
          - ((45 / 34) : ℂ) * ζ ^ 10
          + ((52 / 17) : ℂ) * ζ ^ 13
          + ((45 / 34) : ℂ) * ζ ^ 14
          - ((24 / 17) : ℂ) * ζ ^ 15
          - ((45 / 34) : ℂ) * ζ ^ 18
          + ((24 / 17) : ℂ) * ζ ^ 19
          + ((67 / 34) : ℂ) * ζ ^ 20
          - ((24 / 17) : ℂ) * ζ ^ 23
          - ((67 / 34) : ℂ) * ζ ^ 24
          + ((67 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry00_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (0 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (0 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((29 / 17) : ℂ)
          - ((29 / 17) : ℂ) * ζ ^ 4
          - ((7 / 34) : ℂ) * ζ ^ 5
          + ((29 / 17) : ℂ) * ζ ^ 8
          + ((7 / 34) : ℂ) * ζ ^ 9
          + ((77 / 34) : ℂ) * ζ ^ 10
          - ((7 / 34) : ℂ) * ζ ^ 13
          - ((77 / 34) : ℂ) * ζ ^ 14
          + ((14 / 17) : ℂ) * ζ ^ 15
          + ((77 / 34) : ℂ) * ζ ^ 18
          - ((14 / 17) : ℂ) * ζ ^ 19
          - ((31 / 34) : ℂ) * ζ ^ 20
          + ((14 / 17) : ℂ) * ζ ^ 23
          + ((31 / 34) : ℂ) * ζ ^ 24
          - ((31 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((29 / 17) : ℂ)
          - ((29 / 17) : ℂ) * ζ ^ 4
          - ((7 / 34) : ℂ) * ζ ^ 5
          + ((29 / 17) : ℂ) * ζ ^ 8
          + ((7 / 34) : ℂ) * ζ ^ 9
          + ((77 / 34) : ℂ) * ζ ^ 10
          - ((7 / 34) : ℂ) * ζ ^ 13
          - ((77 / 34) : ℂ) * ζ ^ 14
          + ((14 / 17) : ℂ) * ζ ^ 15
          + ((77 / 34) : ℂ) * ζ ^ 18
          - ((14 / 17) : ℂ) * ζ ^ 19
          - ((31 / 34) : ℂ) * ζ ^ 20
          + ((14 / 17) : ℂ) * ζ ^ 23
          + ((31 / 34) : ℂ) * ζ ^ 24
          - ((31 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry00_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (0 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (0 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((53 / 17) : ℂ)
          - ((53 / 17) : ℂ) * ζ ^ 4
          + ((53 / 17) : ℂ) * ζ ^ 5
          + ((53 / 17) : ℂ) * ζ ^ 8
          - ((53 / 17) : ℂ) * ζ ^ 9
          + ((64 / 17) : ℂ) * ζ ^ 10
          + ((53 / 17) : ℂ) * ζ ^ 13
          - ((64 / 17) : ℂ) * ζ ^ 14
          + ((131 / 34) : ℂ) * ζ ^ 15
          + ((64 / 17) : ℂ) * ζ ^ 18
          - ((131 / 34) : ℂ) * ζ ^ 19
          + ((73 / 34) : ℂ) * ζ ^ 20
          + ((131 / 34) : ℂ) * ζ ^ 23
          - ((73 / 34) : ℂ) * ζ ^ 24
          + ((73 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((53 / 17) : ℂ)
          - ((53 / 17) : ℂ) * ζ ^ 4
          + ((53 / 17) : ℂ) * ζ ^ 5
          + ((53 / 17) : ℂ) * ζ ^ 8
          - ((53 / 17) : ℂ) * ζ ^ 9
          + ((64 / 17) : ℂ) * ζ ^ 10
          + ((53 / 17) : ℂ) * ζ ^ 13
          - ((64 / 17) : ℂ) * ζ ^ 14
          + ((131 / 34) : ℂ) * ζ ^ 15
          + ((64 / 17) : ℂ) * ζ ^ 18
          - ((131 / 34) : ℂ) * ζ ^ 19
          + ((73 / 34) : ℂ) * ζ ^ 20
          + ((131 / 34) : ℂ) * ζ ^ 23
          - ((73 / 34) : ℂ) * ζ ^ 24
          + ((73 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry00_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (0 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (0 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((69 / 34) : ℂ)
          + ((69 / 34) : ℂ) * ζ ^ 4
          - ((5 / 2) : ℂ) * ζ ^ 5
          - ((69 / 34) : ℂ) * ζ ^ 8
          + ((5 / 2) : ℂ) * ζ ^ 9
          - ((32 / 17) : ℂ) * ζ ^ 10
          - ((5 / 2) : ℂ) * ζ ^ 13
          + ((32 / 17) : ℂ) * ζ ^ 14
          - ((23 / 17) : ℂ) * ζ ^ 15
          - ((32 / 17) : ℂ) * ζ ^ 18
          + ((23 / 17) : ℂ) * ζ ^ 19
          - ((37 / 17) : ℂ) * ζ ^ 20
          - ((23 / 17) : ℂ) * ζ ^ 23
          + ((37 / 17) : ℂ) * ζ ^ 24
          - ((37 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((69 / 34) : ℂ)
          + ((69 / 34) : ℂ) * ζ ^ 4
          - ((5 / 2) : ℂ) * ζ ^ 5
          - ((69 / 34) : ℂ) * ζ ^ 8
          + ((5 / 2) : ℂ) * ζ ^ 9
          - ((32 / 17) : ℂ) * ζ ^ 10
          - ((5 / 2) : ℂ) * ζ ^ 13
          + ((32 / 17) : ℂ) * ζ ^ 14
          - ((23 / 17) : ℂ) * ζ ^ 15
          - ((32 / 17) : ℂ) * ζ ^ 18
          + ((23 / 17) : ℂ) * ζ ^ 19
          - ((37 / 17) : ℂ) * ζ ^ 20
          - ((23 / 17) : ℂ) * ζ ^ 23
          + ((37 / 17) : ℂ) * ζ ^ 24
          - ((37 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry00_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (0 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (0 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((4 / 17) : ℂ)
          + ((4 / 17) : ℂ) * ζ ^ 4
          + ((88 / 17) : ℂ) * ζ ^ 5
          - ((4 / 17) : ℂ) * ζ ^ 8
          - ((88 / 17) : ℂ) * ζ ^ 9
          + ((5 / 17) : ℂ) * ζ ^ 10
          + ((88 / 17) : ℂ) * ζ ^ 13
          - ((5 / 17) : ℂ) * ζ ^ 14
          + ((20 / 17) : ℂ) * ζ ^ 15
          + ((5 / 17) : ℂ) * ζ ^ 18
          - ((20 / 17) : ℂ) * ζ ^ 19
          + ((37 / 17) : ℂ) * ζ ^ 20
          + ((20 / 17) : ℂ) * ζ ^ 23
          - ((37 / 17) : ℂ) * ζ ^ 24
          + ((37 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((4 / 17) : ℂ)
          + ((4 / 17) : ℂ) * ζ ^ 4
          + ((88 / 17) : ℂ) * ζ ^ 5
          - ((4 / 17) : ℂ) * ζ ^ 8
          - ((88 / 17) : ℂ) * ζ ^ 9
          + ((5 / 17) : ℂ) * ζ ^ 10
          + ((88 / 17) : ℂ) * ζ ^ 13
          - ((5 / 17) : ℂ) * ζ ^ 14
          + ((20 / 17) : ℂ) * ζ ^ 15
          + ((5 / 17) : ℂ) * ζ ^ 18
          - ((20 / 17) : ℂ) * ζ ^ 19
          + ((37 / 17) : ℂ) * ζ ^ 20
          + ((20 / 17) : ℂ) * ζ ^ 23
          - ((37 / 17) : ℂ) * ζ ^ 24
          + ((37 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry00_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (0 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (0 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((25 / 17) : ℂ)
          - ((25 / 17) : ℂ) * ζ ^ 4
          - ((59 / 34) : ℂ) * ζ ^ 5
          + ((25 / 17) : ℂ) * ζ ^ 8
          + ((59 / 34) : ℂ) * ζ ^ 9
          + ((39 / 34) : ℂ) * ζ ^ 10
          - ((59 / 34) : ℂ) * ζ ^ 13
          - ((39 / 34) : ℂ) * ζ ^ 14
          + ((25 / 17) : ℂ) * ζ ^ 15
          + ((39 / 34) : ℂ) * ζ ^ 18
          - ((25 / 17) : ℂ) * ζ ^ 19
          - ((5 / 34) : ℂ) * ζ ^ 20
          + ((25 / 17) : ℂ) * ζ ^ 23
          + ((5 / 34) : ℂ) * ζ ^ 24
          - ((5 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((25 / 17) : ℂ)
          - ((25 / 17) : ℂ) * ζ ^ 4
          - ((59 / 34) : ℂ) * ζ ^ 5
          + ((25 / 17) : ℂ) * ζ ^ 8
          + ((59 / 34) : ℂ) * ζ ^ 9
          + ((39 / 34) : ℂ) * ζ ^ 10
          - ((59 / 34) : ℂ) * ζ ^ 13
          - ((39 / 34) : ℂ) * ζ ^ 14
          + ((25 / 17) : ℂ) * ζ ^ 15
          + ((39 / 34) : ℂ) * ζ ^ 18
          - ((25 / 17) : ℂ) * ζ ^ 19
          - ((5 / 34) : ℂ) * ζ ^ 20
          + ((25 / 17) : ℂ) * ζ ^ 23
          + ((5 / 34) : ℂ) * ζ ^ 24
          - ((5 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry01_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (1 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (1 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((94 / 17) : ℂ)
          + ((94 / 17) : ℂ) * ζ ^ 4
          - ((199 / 34) : ℂ) * ζ ^ 5
          - ((94 / 17) : ℂ) * ζ ^ 8
          + ((199 / 34) : ℂ) * ζ ^ 9
          - ((173 / 34) : ℂ) * ζ ^ 10
          - ((199 / 34) : ℂ) * ζ ^ 13
          + ((173 / 34) : ℂ) * ζ ^ 14
          - ((60 / 17) : ℂ) * ζ ^ 15
          - ((173 / 34) : ℂ) * ζ ^ 18
          + ((60 / 17) : ℂ) * ζ ^ 19
          - ((41 / 34) : ℂ) * ζ ^ 20
          - ((60 / 17) : ℂ) * ζ ^ 23
          + ((41 / 34) : ℂ) * ζ ^ 24
          - ((41 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((94 / 17) : ℂ)
          + ((94 / 17) : ℂ) * ζ ^ 4
          - ((199 / 34) : ℂ) * ζ ^ 5
          - ((94 / 17) : ℂ) * ζ ^ 8
          + ((199 / 34) : ℂ) * ζ ^ 9
          - ((173 / 34) : ℂ) * ζ ^ 10
          - ((199 / 34) : ℂ) * ζ ^ 13
          + ((173 / 34) : ℂ) * ζ ^ 14
          - ((60 / 17) : ℂ) * ζ ^ 15
          - ((173 / 34) : ℂ) * ζ ^ 18
          + ((60 / 17) : ℂ) * ζ ^ 19
          - ((41 / 34) : ℂ) * ζ ^ 20
          - ((60 / 17) : ℂ) * ζ ^ 23
          + ((41 / 34) : ℂ) * ζ ^ 24
          - ((41 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry01_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (1 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (1 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((59 / 17) : ℂ)
          + ((59 / 17) : ℂ) * ζ ^ 4
          - ((97 / 17) : ℂ) * ζ ^ 5
          - ((59 / 17) : ℂ) * ζ ^ 8
          + ((97 / 17) : ℂ) * ζ ^ 9
          - ((94 / 17) : ℂ) * ζ ^ 10
          - ((97 / 17) : ℂ) * ζ ^ 13
          + ((94 / 17) : ℂ) * ζ ^ 14
          - ((74 / 17) : ℂ) * ζ ^ 15
          - ((94 / 17) : ℂ) * ζ ^ 18
          + ((74 / 17) : ℂ) * ζ ^ 19
          - ((27 / 17) : ℂ) * ζ ^ 20
          - ((74 / 17) : ℂ) * ζ ^ 23
          + ((27 / 17) : ℂ) * ζ ^ 24
          - ((27 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((59 / 17) : ℂ)
          + ((59 / 17) : ℂ) * ζ ^ 4
          - ((97 / 17) : ℂ) * ζ ^ 5
          - ((59 / 17) : ℂ) * ζ ^ 8
          + ((97 / 17) : ℂ) * ζ ^ 9
          - ((94 / 17) : ℂ) * ζ ^ 10
          - ((97 / 17) : ℂ) * ζ ^ 13
          + ((94 / 17) : ℂ) * ζ ^ 14
          - ((74 / 17) : ℂ) * ζ ^ 15
          - ((94 / 17) : ℂ) * ζ ^ 18
          + ((74 / 17) : ℂ) * ζ ^ 19
          - ((27 / 17) : ℂ) * ζ ^ 20
          - ((74 / 17) : ℂ) * ζ ^ 23
          + ((27 / 17) : ℂ) * ζ ^ 24
          - ((27 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry01_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (1 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (1 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((27 / 17) : ℂ)
          - ((27 / 17) : ℂ) * ζ ^ 4
          - ((39 / 17) : ℂ) * ζ ^ 5
          + ((27 / 17) : ℂ) * ζ ^ 8
          + ((39 / 17) : ℂ) * ζ ^ 9
          - ((118 / 17) : ℂ) * ζ ^ 10
          - ((39 / 17) : ℂ) * ζ ^ 13
          + ((118 / 17) : ℂ) * ζ ^ 14
          - (10 : ℂ) * ζ ^ 15
          - ((118 / 17) : ℂ) * ζ ^ 18
          + (10 : ℂ) * ζ ^ 19
          - ((89 / 17) : ℂ) * ζ ^ 20
          - (10 : ℂ) * ζ ^ 23
          + ((89 / 17) : ℂ) * ζ ^ 24
          - ((89 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((27 / 17) : ℂ)
          - ((27 / 17) : ℂ) * ζ ^ 4
          - ((39 / 17) : ℂ) * ζ ^ 5
          + ((27 / 17) : ℂ) * ζ ^ 8
          + ((39 / 17) : ℂ) * ζ ^ 9
          - ((118 / 17) : ℂ) * ζ ^ 10
          - ((39 / 17) : ℂ) * ζ ^ 13
          + ((118 / 17) : ℂ) * ζ ^ 14
          - (10 : ℂ) * ζ ^ 15
          - ((118 / 17) : ℂ) * ζ ^ 18
          + (10 : ℂ) * ζ ^ 19
          - ((89 / 17) : ℂ) * ζ ^ 20
          - (10 : ℂ) * ζ ^ 23
          + ((89 / 17) : ℂ) * ζ ^ 24
          - ((89 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry01_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (1 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (1 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((75 / 17) : ℂ)
          - ((75 / 17) : ℂ) * ζ ^ 4
          + ((353 / 34) : ℂ) * ζ ^ 5
          + ((75 / 17) : ℂ) * ζ ^ 8
          - ((353 / 34) : ℂ) * ζ ^ 9
          + ((259 / 34) : ℂ) * ζ ^ 10
          + ((353 / 34) : ℂ) * ζ ^ 13
          - ((259 / 34) : ℂ) * ζ ^ 14
          - ((31 / 17) : ℂ) * ζ ^ 15
          + ((259 / 34) : ℂ) * ζ ^ 18
          + ((31 / 17) : ℂ) * ζ ^ 19
          - ((21 / 34) : ℂ) * ζ ^ 20
          - ((31 / 17) : ℂ) * ζ ^ 23
          + ((21 / 34) : ℂ) * ζ ^ 24
          - ((21 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((75 / 17) : ℂ)
          - ((75 / 17) : ℂ) * ζ ^ 4
          + ((353 / 34) : ℂ) * ζ ^ 5
          + ((75 / 17) : ℂ) * ζ ^ 8
          - ((353 / 34) : ℂ) * ζ ^ 9
          + ((259 / 34) : ℂ) * ζ ^ 10
          + ((353 / 34) : ℂ) * ζ ^ 13
          - ((259 / 34) : ℂ) * ζ ^ 14
          - ((31 / 17) : ℂ) * ζ ^ 15
          + ((259 / 34) : ℂ) * ζ ^ 18
          + ((31 / 17) : ℂ) * ζ ^ 19
          - ((21 / 34) : ℂ) * ζ ^ 20
          - ((31 / 17) : ℂ) * ζ ^ 23
          + ((21 / 34) : ℂ) * ζ ^ 24
          - ((21 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry01_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (1 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (1 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((56 / 17) : ℂ)
          - ((56 / 17) : ℂ) * ζ ^ 4
          + ((175 / 17) : ℂ) * ζ ^ 5
          + ((56 / 17) : ℂ) * ζ ^ 8
          - ((175 / 17) : ℂ) * ζ ^ 9
          + ((245 / 17) : ℂ) * ζ ^ 10
          + ((175 / 17) : ℂ) * ζ ^ 13
          - ((245 / 17) : ℂ) * ζ ^ 14
          + ((95 / 17) : ℂ) * ζ ^ 15
          + ((245 / 17) : ℂ) * ζ ^ 18
          - ((95 / 17) : ℂ) * ζ ^ 19
          + ((26 / 17) : ℂ) * ζ ^ 20
          + ((95 / 17) : ℂ) * ζ ^ 23
          - ((26 / 17) : ℂ) * ζ ^ 24
          + ((26 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((56 / 17) : ℂ)
          - ((56 / 17) : ℂ) * ζ ^ 4
          + ((175 / 17) : ℂ) * ζ ^ 5
          + ((56 / 17) : ℂ) * ζ ^ 8
          - ((175 / 17) : ℂ) * ζ ^ 9
          + ((245 / 17) : ℂ) * ζ ^ 10
          + ((175 / 17) : ℂ) * ζ ^ 13
          - ((245 / 17) : ℂ) * ζ ^ 14
          + ((95 / 17) : ℂ) * ζ ^ 15
          + ((245 / 17) : ℂ) * ζ ^ 18
          - ((95 / 17) : ℂ) * ζ ^ 19
          + ((26 / 17) : ℂ) * ζ ^ 20
          + ((95 / 17) : ℂ) * ζ ^ 23
          - ((26 / 17) : ℂ) * ζ ^ 24
          + ((26 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry01_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (1 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (1 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((70 / 17) : ℂ)
          + ((70 / 17) : ℂ) * ζ ^ 4
          - ((343 / 34) : ℂ) * ζ ^ 5
          - ((70 / 17) : ℂ) * ζ ^ 8
          + ((343 / 34) : ℂ) * ζ ^ 9
          - ((279 / 34) : ℂ) * ζ ^ 10
          - ((343 / 34) : ℂ) * ζ ^ 13
          + ((279 / 34) : ℂ) * ζ ^ 14
          - (3 : ℂ) * ζ ^ 15
          - ((279 / 34) : ℂ) * ζ ^ 18
          + (3 : ℂ) * ζ ^ 19
          - ((159 / 34) : ℂ) * ζ ^ 20
          - (3 : ℂ) * ζ ^ 23
          + ((159 / 34) : ℂ) * ζ ^ 24
          - ((159 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((70 / 17) : ℂ)
          + ((70 / 17) : ℂ) * ζ ^ 4
          - ((343 / 34) : ℂ) * ζ ^ 5
          - ((70 / 17) : ℂ) * ζ ^ 8
          + ((343 / 34) : ℂ) * ζ ^ 9
          - ((279 / 34) : ℂ) * ζ ^ 10
          - ((343 / 34) : ℂ) * ζ ^ 13
          + ((279 / 34) : ℂ) * ζ ^ 14
          - (3 : ℂ) * ζ ^ 15
          - ((279 / 34) : ℂ) * ζ ^ 18
          + (3 : ℂ) * ζ ^ 19
          - ((159 / 34) : ℂ) * ζ ^ 20
          - (3 : ℂ) * ζ ^ 23
          + ((159 / 34) : ℂ) * ζ ^ 24
          - ((159 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry01_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (1 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (1 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((62 / 17) : ℂ)
          - ((62 / 17) : ℂ) * ζ ^ 4
          + ((39 / 17) : ℂ) * ζ ^ 5
          + ((62 / 17) : ℂ) * ζ ^ 8
          - ((39 / 17) : ℂ) * ζ ^ 9
          + ((39 / 17) : ℂ) * ζ ^ 13
          + ((71 / 17) : ℂ) * ζ ^ 15
          - ((71 / 17) : ℂ) * ζ ^ 19
          + ((40 / 17) : ℂ) * ζ ^ 20
          + ((71 / 17) : ℂ) * ζ ^ 23
          - ((40 / 17) : ℂ) * ζ ^ 24
          + ((40 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((62 / 17) : ℂ)
          - ((62 / 17) : ℂ) * ζ ^ 4
          + ((39 / 17) : ℂ) * ζ ^ 5
          + ((62 / 17) : ℂ) * ζ ^ 8
          - ((39 / 17) : ℂ) * ζ ^ 9
          + ((39 / 17) : ℂ) * ζ ^ 13
          + ((71 / 17) : ℂ) * ζ ^ 15
          - ((71 / 17) : ℂ) * ζ ^ 19
          + ((40 / 17) : ℂ) * ζ ^ 20
          + ((71 / 17) : ℂ) * ζ ^ 23
          - ((40 / 17) : ℂ) * ζ ^ 24
          + ((40 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry01_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (1 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (1 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 17) : ℂ)
          + ((7 / 17) : ℂ) * ζ ^ 4
          + ((1 / 17) : ℂ) * ζ ^ 5
          - ((7 / 17) : ℂ) * ζ ^ 8
          - ((1 / 17) : ℂ) * ζ ^ 9
          - ((21 / 17) : ℂ) * ζ ^ 10
          + ((1 / 17) : ℂ) * ζ ^ 13
          + ((21 / 17) : ℂ) * ζ ^ 14
          + ((23 / 17) : ℂ) * ζ ^ 15
          - ((21 / 17) : ℂ) * ζ ^ 18
          - ((23 / 17) : ℂ) * ζ ^ 19
          + ((45 / 17) : ℂ) * ζ ^ 20
          + ((23 / 17) : ℂ) * ζ ^ 23
          - ((45 / 17) : ℂ) * ζ ^ 24
          + ((45 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 17) : ℂ)
          + ((7 / 17) : ℂ) * ζ ^ 4
          + ((1 / 17) : ℂ) * ζ ^ 5
          - ((7 / 17) : ℂ) * ζ ^ 8
          - ((1 / 17) : ℂ) * ζ ^ 9
          - ((21 / 17) : ℂ) * ζ ^ 10
          + ((1 / 17) : ℂ) * ζ ^ 13
          + ((21 / 17) : ℂ) * ζ ^ 14
          + ((23 / 17) : ℂ) * ζ ^ 15
          - ((21 / 17) : ℂ) * ζ ^ 18
          - ((23 / 17) : ℂ) * ζ ^ 19
          + ((45 / 17) : ℂ) * ζ ^ 20
          + ((23 / 17) : ℂ) * ζ ^ 23
          - ((45 / 17) : ℂ) * ζ ^ 24
          + ((45 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry01_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (1 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (1 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((73 / 17) : ℂ)
          + ((73 / 17) : ℂ) * ζ ^ 4
          + ((4 / 17) : ℂ) * ζ ^ 5
          - ((73 / 17) : ℂ) * ζ ^ 8
          - ((4 / 17) : ℂ) * ζ ^ 9
          + ((130 / 17) : ℂ) * ζ ^ 10
          + ((4 / 17) : ℂ) * ζ ^ 13
          - ((130 / 17) : ℂ) * ζ ^ 14
          + ((22 / 17) : ℂ) * ζ ^ 15
          + ((130 / 17) : ℂ) * ζ ^ 18
          - ((22 / 17) : ℂ) * ζ ^ 19
          - ζ ^ 20
          + ((22 / 17) : ℂ) * ζ ^ 23
          + ζ ^ 24
          - ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((73 / 17) : ℂ)
          + ((73 / 17) : ℂ) * ζ ^ 4
          + ((4 / 17) : ℂ) * ζ ^ 5
          - ((73 / 17) : ℂ) * ζ ^ 8
          - ((4 / 17) : ℂ) * ζ ^ 9
          + ((130 / 17) : ℂ) * ζ ^ 10
          + ((4 / 17) : ℂ) * ζ ^ 13
          - ((130 / 17) : ℂ) * ζ ^ 14
          + ((22 / 17) : ℂ) * ζ ^ 15
          + ((130 / 17) : ℂ) * ζ ^ 18
          - ((22 / 17) : ℂ) * ζ ^ 19
          - ζ ^ 20
          + ((22 / 17) : ℂ) * ζ ^ 23
          + ζ ^ 24
          - ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry01_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (1 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (1 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((27 / 17) : ℂ)
          - ((27 / 17) : ℂ) * ζ ^ 4
          - ((95 / 34) : ℂ) * ζ ^ 5
          + ((27 / 17) : ℂ) * ζ ^ 8
          + ((95 / 34) : ℂ) * ζ ^ 9
          - ((253 / 34) : ℂ) * ζ ^ 10
          - ((95 / 34) : ℂ) * ζ ^ 13
          + ((253 / 34) : ℂ) * ζ ^ 14
          - ((92 / 17) : ℂ) * ζ ^ 15
          - ((253 / 34) : ℂ) * ζ ^ 18
          + ((92 / 17) : ℂ) * ζ ^ 19
          - ((53 / 34) : ℂ) * ζ ^ 20
          - ((92 / 17) : ℂ) * ζ ^ 23
          + ((53 / 34) : ℂ) * ζ ^ 24
          - ((53 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((27 / 17) : ℂ)
          - ((27 / 17) : ℂ) * ζ ^ 4
          - ((95 / 34) : ℂ) * ζ ^ 5
          + ((27 / 17) : ℂ) * ζ ^ 8
          + ((95 / 34) : ℂ) * ζ ^ 9
          - ((253 / 34) : ℂ) * ζ ^ 10
          - ((95 / 34) : ℂ) * ζ ^ 13
          + ((253 / 34) : ℂ) * ζ ^ 14
          - ((92 / 17) : ℂ) * ζ ^ 15
          - ((253 / 34) : ℂ) * ζ ^ 18
          + ((92 / 17) : ℂ) * ζ ^ 19
          - ((53 / 34) : ℂ) * ζ ^ 20
          - ((92 / 17) : ℂ) * ζ ^ 23
          + ((53 / 34) : ℂ) * ζ ^ 24
          - ((53 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry02_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (2 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (2 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((23 / 17) : ℂ)
          + ((23 / 17) : ℂ) * ζ ^ 4
          - ((7 / 2) : ℂ) * ζ ^ 5
          - ((23 / 17) : ℂ) * ζ ^ 8
          + ((7 / 2) : ℂ) * ζ ^ 9
          - ((71 / 34) : ℂ) * ζ ^ 10
          - ((7 / 2) : ℂ) * ζ ^ 13
          + ((71 / 34) : ℂ) * ζ ^ 14
          - ((5 / 34) : ℂ) * ζ ^ 15
          - ((71 / 34) : ℂ) * ζ ^ 18
          + ((5 / 34) : ℂ) * ζ ^ 19
          - ((16 / 17) : ℂ) * ζ ^ 20
          - ((5 / 34) : ℂ) * ζ ^ 23
          + ((16 / 17) : ℂ) * ζ ^ 24
          - ((16 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((23 / 17) : ℂ)
          + ((23 / 17) : ℂ) * ζ ^ 4
          - ((7 / 2) : ℂ) * ζ ^ 5
          - ((23 / 17) : ℂ) * ζ ^ 8
          + ((7 / 2) : ℂ) * ζ ^ 9
          - ((71 / 34) : ℂ) * ζ ^ 10
          - ((7 / 2) : ℂ) * ζ ^ 13
          + ((71 / 34) : ℂ) * ζ ^ 14
          - ((5 / 34) : ℂ) * ζ ^ 15
          - ((71 / 34) : ℂ) * ζ ^ 18
          + ((5 / 34) : ℂ) * ζ ^ 19
          - ((16 / 17) : ℂ) * ζ ^ 20
          - ((5 / 34) : ℂ) * ζ ^ 23
          + ((16 / 17) : ℂ) * ζ ^ 24
          - ((16 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry02_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (2 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (2 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((23 / 17) : ℂ)
          + ((23 / 17) : ℂ) * ζ ^ 4
          - ((57 / 17) : ℂ) * ζ ^ 5
          - ((23 / 17) : ℂ) * ζ ^ 8
          + ((57 / 17) : ℂ) * ζ ^ 9
          - ((73 / 17) : ℂ) * ζ ^ 10
          - ((57 / 17) : ℂ) * ζ ^ 13
          + ((73 / 17) : ℂ) * ζ ^ 14
          - ((113 / 34) : ℂ) * ζ ^ 15
          - ((73 / 17) : ℂ) * ζ ^ 18
          + ((113 / 34) : ℂ) * ζ ^ 19
          - ((33 / 34) : ℂ) * ζ ^ 20
          - ((113 / 34) : ℂ) * ζ ^ 23
          + ((33 / 34) : ℂ) * ζ ^ 24
          - ((33 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((23 / 17) : ℂ)
          + ((23 / 17) : ℂ) * ζ ^ 4
          - ((57 / 17) : ℂ) * ζ ^ 5
          - ((23 / 17) : ℂ) * ζ ^ 8
          + ((57 / 17) : ℂ) * ζ ^ 9
          - ((73 / 17) : ℂ) * ζ ^ 10
          - ((57 / 17) : ℂ) * ζ ^ 13
          + ((73 / 17) : ℂ) * ζ ^ 14
          - ((113 / 34) : ℂ) * ζ ^ 15
          - ((73 / 17) : ℂ) * ζ ^ 18
          + ((113 / 34) : ℂ) * ζ ^ 19
          - ((33 / 34) : ℂ) * ζ ^ 20
          - ((113 / 34) : ℂ) * ζ ^ 23
          + ((33 / 34) : ℂ) * ζ ^ 24
          - ((33 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry02_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (2 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (2 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((63 / 34) : ℂ)
          - ((63 / 34) : ℂ) * ζ ^ 4
          - ((59 / 34) : ℂ) * ζ ^ 5
          + ((63 / 34) : ℂ) * ζ ^ 8
          + ((59 / 34) : ℂ) * ζ ^ 9
          - ((83 / 17) : ℂ) * ζ ^ 10
          - ((59 / 34) : ℂ) * ζ ^ 13
          + ((83 / 17) : ℂ) * ζ ^ 14
          - ((175 / 34) : ℂ) * ζ ^ 15
          - ((83 / 17) : ℂ) * ζ ^ 18
          + ((175 / 34) : ℂ) * ζ ^ 19
          - ((77 / 34) : ℂ) * ζ ^ 20
          - ((175 / 34) : ℂ) * ζ ^ 23
          + ((77 / 34) : ℂ) * ζ ^ 24
          - ((77 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((63 / 34) : ℂ)
          - ((63 / 34) : ℂ) * ζ ^ 4
          - ((59 / 34) : ℂ) * ζ ^ 5
          + ((63 / 34) : ℂ) * ζ ^ 8
          + ((59 / 34) : ℂ) * ζ ^ 9
          - ((83 / 17) : ℂ) * ζ ^ 10
          - ((59 / 34) : ℂ) * ζ ^ 13
          + ((83 / 17) : ℂ) * ζ ^ 14
          - ((175 / 34) : ℂ) * ζ ^ 15
          - ((83 / 17) : ℂ) * ζ ^ 18
          + ((175 / 34) : ℂ) * ζ ^ 19
          - ((77 / 34) : ℂ) * ζ ^ 20
          - ((175 / 34) : ℂ) * ζ ^ 23
          + ((77 / 34) : ℂ) * ζ ^ 24
          - ((77 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry02_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (2 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (2 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((28 / 17) : ℂ)
          - ((28 / 17) : ℂ) * ζ ^ 4
          + ((11 / 2) : ℂ) * ζ ^ 5
          + ((28 / 17) : ℂ) * ζ ^ 8
          - ((11 / 2) : ℂ) * ζ ^ 9
          + ((167 / 34) : ℂ) * ζ ^ 10
          + ((11 / 2) : ℂ) * ζ ^ 13
          - ((167 / 34) : ℂ) * ζ ^ 14
          - ((48 / 17) : ℂ) * ζ ^ 15
          + ((167 / 34) : ℂ) * ζ ^ 18
          + ((48 / 17) : ℂ) * ζ ^ 19
          + ((7 / 34) : ℂ) * ζ ^ 20
          - ((48 / 17) : ℂ) * ζ ^ 23
          - ((7 / 34) : ℂ) * ζ ^ 24
          + ((7 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((28 / 17) : ℂ)
          - ((28 / 17) : ℂ) * ζ ^ 4
          + ((11 / 2) : ℂ) * ζ ^ 5
          + ((28 / 17) : ℂ) * ζ ^ 8
          - ((11 / 2) : ℂ) * ζ ^ 9
          + ((167 / 34) : ℂ) * ζ ^ 10
          + ((11 / 2) : ℂ) * ζ ^ 13
          - ((167 / 34) : ℂ) * ζ ^ 14
          - ((48 / 17) : ℂ) * ζ ^ 15
          + ((167 / 34) : ℂ) * ζ ^ 18
          + ((48 / 17) : ℂ) * ζ ^ 19
          + ((7 / 34) : ℂ) * ζ ^ 20
          - ((48 / 17) : ℂ) * ζ ^ 23
          - ((7 / 34) : ℂ) * ζ ^ 24
          + ((7 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry02_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (2 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (2 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((39 / 34) : ℂ)
          - ((39 / 34) : ℂ) * ζ ^ 4
          + ((99 / 17) : ℂ) * ζ ^ 5
          + ((39 / 34) : ℂ) * ζ ^ 8
          - ((99 / 17) : ℂ) * ζ ^ 9
          + ((291 / 34) : ℂ) * ζ ^ 10
          + ((99 / 17) : ℂ) * ζ ^ 13
          - ((291 / 34) : ℂ) * ζ ^ 14
          + ((31 / 17) : ℂ) * ζ ^ 15
          + ((291 / 34) : ℂ) * ζ ^ 18
          - ((31 / 17) : ℂ) * ζ ^ 19
          + ((31 / 34) : ℂ) * ζ ^ 20
          + ((31 / 17) : ℂ) * ζ ^ 23
          - ((31 / 34) : ℂ) * ζ ^ 24
          + ((31 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((39 / 34) : ℂ)
          - ((39 / 34) : ℂ) * ζ ^ 4
          + ((99 / 17) : ℂ) * ζ ^ 5
          + ((39 / 34) : ℂ) * ζ ^ 8
          - ((99 / 17) : ℂ) * ζ ^ 9
          + ((291 / 34) : ℂ) * ζ ^ 10
          + ((99 / 17) : ℂ) * ζ ^ 13
          - ((291 / 34) : ℂ) * ζ ^ 14
          + ((31 / 17) : ℂ) * ζ ^ 15
          + ((291 / 34) : ℂ) * ζ ^ 18
          - ((31 / 17) : ℂ) * ζ ^ 19
          + ((31 / 34) : ℂ) * ζ ^ 20
          + ((31 / 17) : ℂ) * ζ ^ 23
          - ((31 / 34) : ℂ) * ζ ^ 24
          + ((31 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry02_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (2 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (2 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((3 / 2) : ℂ)
          + ((3 / 2) : ℂ) * ζ ^ 4
          - ((193 / 34) : ℂ) * ζ ^ 5
          - ((3 / 2) : ℂ) * ζ ^ 8
          + ((193 / 34) : ℂ) * ζ ^ 9
          - ((108 / 17) : ℂ) * ζ ^ 10
          - ((193 / 34) : ℂ) * ζ ^ 13
          + ((108 / 17) : ℂ) * ζ ^ 14
          - ((37 / 34) : ℂ) * ζ ^ 15
          - ((108 / 17) : ℂ) * ζ ^ 18
          + ((37 / 34) : ℂ) * ζ ^ 19
          - ((77 / 34) : ℂ) * ζ ^ 20
          - ((37 / 34) : ℂ) * ζ ^ 23
          + ((77 / 34) : ℂ) * ζ ^ 24
          - ((77 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((3 / 2) : ℂ)
          + ((3 / 2) : ℂ) * ζ ^ 4
          - ((193 / 34) : ℂ) * ζ ^ 5
          - ((3 / 2) : ℂ) * ζ ^ 8
          + ((193 / 34) : ℂ) * ζ ^ 9
          - ((108 / 17) : ℂ) * ζ ^ 10
          - ((193 / 34) : ℂ) * ζ ^ 13
          + ((108 / 17) : ℂ) * ζ ^ 14
          - ((37 / 34) : ℂ) * ζ ^ 15
          - ((108 / 17) : ℂ) * ζ ^ 18
          + ((37 / 34) : ℂ) * ζ ^ 19
          - ((77 / 34) : ℂ) * ζ ^ 20
          - ((37 / 34) : ℂ) * ζ ^ 23
          + ((77 / 34) : ℂ) * ζ ^ 24
          - ((77 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry02_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (2 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (2 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((19 / 17) : ℂ)
          - ((19 / 17) : ℂ) * ζ ^ 4
          + ((20 / 17) : ℂ) * ζ ^ 5
          + ((19 / 17) : ℂ) * ζ ^ 8
          - ((20 / 17) : ℂ) * ζ ^ 9
          - ((36 / 17) : ℂ) * ζ ^ 10
          + ((20 / 17) : ℂ) * ζ ^ 13
          + ((36 / 17) : ℂ) * ζ ^ 14
          - ((9 / 34) : ℂ) * ζ ^ 15
          - ((36 / 17) : ℂ) * ζ ^ 18
          + ((9 / 34) : ℂ) * ζ ^ 19
          + ((49 / 34) : ℂ) * ζ ^ 20
          - ((9 / 34) : ℂ) * ζ ^ 23
          - ((49 / 34) : ℂ) * ζ ^ 24
          + ((49 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((19 / 17) : ℂ)
          - ((19 / 17) : ℂ) * ζ ^ 4
          + ((20 / 17) : ℂ) * ζ ^ 5
          + ((19 / 17) : ℂ) * ζ ^ 8
          - ((20 / 17) : ℂ) * ζ ^ 9
          - ((36 / 17) : ℂ) * ζ ^ 10
          + ((20 / 17) : ℂ) * ζ ^ 13
          + ((36 / 17) : ℂ) * ζ ^ 14
          - ((9 / 34) : ℂ) * ζ ^ 15
          - ((36 / 17) : ℂ) * ζ ^ 18
          + ((9 / 34) : ℂ) * ζ ^ 19
          + ((49 / 34) : ℂ) * ζ ^ 20
          - ((9 / 34) : ℂ) * ζ ^ 23
          - ((49 / 34) : ℂ) * ζ ^ 24
          + ((49 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry02_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (2 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (2 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((9 / 34) : ℂ)
          + ((9 / 34) : ℂ) * ζ ^ 4
          - ((7 / 34) : ℂ) * ζ ^ 5
          - ((9 / 34) : ℂ) * ζ ^ 8
          + ((7 / 34) : ℂ) * ζ ^ 9
          + ((11 / 17) : ℂ) * ζ ^ 10
          - ((7 / 34) : ℂ) * ζ ^ 13
          - ((11 / 17) : ℂ) * ζ ^ 14
          + ((33 / 17) : ℂ) * ζ ^ 15
          + ((11 / 17) : ℂ) * ζ ^ 18
          - ((33 / 17) : ℂ) * ζ ^ 19
          + ((22 / 17) : ℂ) * ζ ^ 20
          + ((33 / 17) : ℂ) * ζ ^ 23
          - ((22 / 17) : ℂ) * ζ ^ 24
          + ((22 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((9 / 34) : ℂ)
          + ((9 / 34) : ℂ) * ζ ^ 4
          - ((7 / 34) : ℂ) * ζ ^ 5
          - ((9 / 34) : ℂ) * ζ ^ 8
          + ((7 / 34) : ℂ) * ζ ^ 9
          + ((11 / 17) : ℂ) * ζ ^ 10
          - ((7 / 34) : ℂ) * ζ ^ 13
          - ((11 / 17) : ℂ) * ζ ^ 14
          + ((33 / 17) : ℂ) * ζ ^ 15
          + ((11 / 17) : ℂ) * ζ ^ 18
          - ((33 / 17) : ℂ) * ζ ^ 19
          + ((22 / 17) : ℂ) * ζ ^ 20
          + ((33 / 17) : ℂ) * ζ ^ 23
          - ((22 / 17) : ℂ) * ζ ^ 24
          + ((22 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry02_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (2 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (2 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((47 / 17) : ℂ)
          + ((47 / 17) : ℂ) * ζ ^ 4
          + ((4 / 17) : ℂ) * ζ ^ 5
          - ((47 / 17) : ℂ) * ζ ^ 8
          - ((4 / 17) : ℂ) * ζ ^ 9
          + ((60 / 17) : ℂ) * ζ ^ 10
          + ((4 / 17) : ℂ) * ζ ^ 13
          - ((60 / 17) : ℂ) * ζ ^ 14
          - ((11 / 17) : ℂ) * ζ ^ 15
          + ((60 / 17) : ℂ) * ζ ^ 18
          + ((11 / 17) : ℂ) * ζ ^ 19
          - ((7 / 17) : ℂ) * ζ ^ 20
          - ((11 / 17) : ℂ) * ζ ^ 23
          + ((7 / 17) : ℂ) * ζ ^ 24
          - ((7 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((47 / 17) : ℂ)
          + ((47 / 17) : ℂ) * ζ ^ 4
          + ((4 / 17) : ℂ) * ζ ^ 5
          - ((47 / 17) : ℂ) * ζ ^ 8
          - ((4 / 17) : ℂ) * ζ ^ 9
          + ((60 / 17) : ℂ) * ζ ^ 10
          + ((4 / 17) : ℂ) * ζ ^ 13
          - ((60 / 17) : ℂ) * ζ ^ 14
          - ((11 / 17) : ℂ) * ζ ^ 15
          + ((60 / 17) : ℂ) * ζ ^ 18
          + ((11 / 17) : ℂ) * ζ ^ 19
          - ((7 / 17) : ℂ) * ζ ^ 20
          - ((11 / 17) : ℂ) * ζ ^ 23
          + ((7 / 17) : ℂ) * ζ ^ 24
          - ((7 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry02_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (2 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (2 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((43 / 34) : ℂ)
          - ((43 / 34) : ℂ) * ζ ^ 4
          - ((47 / 34) : ℂ) * ζ ^ 5
          + ((43 / 34) : ℂ) * ζ ^ 8
          + ((47 / 34) : ℂ) * ζ ^ 9
          - ((82 / 17) : ℂ) * ζ ^ 10
          - ((47 / 34) : ℂ) * ζ ^ 13
          + ((82 / 17) : ℂ) * ζ ^ 14
          - ((93 / 34) : ℂ) * ζ ^ 15
          - ((82 / 17) : ℂ) * ζ ^ 18
          + ((93 / 34) : ℂ) * ζ ^ 19
          - ((23 / 34) : ℂ) * ζ ^ 20
          - ((93 / 34) : ℂ) * ζ ^ 23
          + ((23 / 34) : ℂ) * ζ ^ 24
          - ((23 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((43 / 34) : ℂ)
          - ((43 / 34) : ℂ) * ζ ^ 4
          - ((47 / 34) : ℂ) * ζ ^ 5
          + ((43 / 34) : ℂ) * ζ ^ 8
          + ((47 / 34) : ℂ) * ζ ^ 9
          - ((82 / 17) : ℂ) * ζ ^ 10
          - ((47 / 34) : ℂ) * ζ ^ 13
          + ((82 / 17) : ℂ) * ζ ^ 14
          - ((93 / 34) : ℂ) * ζ ^ 15
          - ((82 / 17) : ℂ) * ζ ^ 18
          + ((93 / 34) : ℂ) * ζ ^ 19
          - ((23 / 34) : ℂ) * ζ ^ 20
          - ((93 / 34) : ℂ) * ζ ^ 23
          + ((23 / 34) : ℂ) * ζ ^ 24
          - ((23 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry03_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (3 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (3 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((113 / 34) : ℂ)
          - ((113 / 34) : ℂ) * ζ ^ 4
          + ((87 / 34) : ℂ) * ζ ^ 5
          + ((113 / 34) : ℂ) * ζ ^ 8
          - ((87 / 34) : ℂ) * ζ ^ 9
          + ((48 / 17) : ℂ) * ζ ^ 10
          + ((87 / 34) : ℂ) * ζ ^ 13
          - ((48 / 17) : ℂ) * ζ ^ 14
          + ((37 / 17) : ℂ) * ζ ^ 15
          + ((48 / 17) : ℂ) * ζ ^ 18
          - ((37 / 17) : ℂ) * ζ ^ 19
          + ((86 / 17) : ℂ) * ζ ^ 20
          + ((37 / 17) : ℂ) * ζ ^ 23
          - ((86 / 17) : ℂ) * ζ ^ 24
          + ((86 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((113 / 34) : ℂ)
          - ((113 / 34) : ℂ) * ζ ^ 4
          + ((87 / 34) : ℂ) * ζ ^ 5
          + ((113 / 34) : ℂ) * ζ ^ 8
          - ((87 / 34) : ℂ) * ζ ^ 9
          + ((48 / 17) : ℂ) * ζ ^ 10
          + ((87 / 34) : ℂ) * ζ ^ 13
          - ((48 / 17) : ℂ) * ζ ^ 14
          + ((37 / 17) : ℂ) * ζ ^ 15
          + ((48 / 17) : ℂ) * ζ ^ 18
          - ((37 / 17) : ℂ) * ζ ^ 19
          + ((86 / 17) : ℂ) * ζ ^ 20
          + ((37 / 17) : ℂ) * ζ ^ 23
          - ((86 / 17) : ℂ) * ζ ^ 24
          + ((86 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry03_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (3 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (3 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((50 / 17) : ℂ)
          + ((50 / 17) : ℂ) * ζ ^ 4
          - ((30 / 17) : ℂ) * ζ ^ 5
          - ((50 / 17) : ℂ) * ζ ^ 8
          + ((30 / 17) : ℂ) * ζ ^ 9
          - ((30 / 17) : ℂ) * ζ ^ 10
          - ((30 / 17) : ℂ) * ζ ^ 13
          + ((30 / 17) : ℂ) * ζ ^ 14
          - ((82 / 17) : ℂ) * ζ ^ 15
          - ((30 / 17) : ℂ) * ζ ^ 18
          + ((82 / 17) : ℂ) * ζ ^ 19
          - ((27 / 17) : ℂ) * ζ ^ 20
          - ((82 / 17) : ℂ) * ζ ^ 23
          + ((27 / 17) : ℂ) * ζ ^ 24
          - ((27 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((50 / 17) : ℂ)
          + ((50 / 17) : ℂ) * ζ ^ 4
          - ((30 / 17) : ℂ) * ζ ^ 5
          - ((50 / 17) : ℂ) * ζ ^ 8
          + ((30 / 17) : ℂ) * ζ ^ 9
          - ((30 / 17) : ℂ) * ζ ^ 10
          - ((30 / 17) : ℂ) * ζ ^ 13
          + ((30 / 17) : ℂ) * ζ ^ 14
          - ((82 / 17) : ℂ) * ζ ^ 15
          - ((30 / 17) : ℂ) * ζ ^ 18
          + ((82 / 17) : ℂ) * ζ ^ 19
          - ((27 / 17) : ℂ) * ζ ^ 20
          - ((82 / 17) : ℂ) * ζ ^ 23
          + ((27 / 17) : ℂ) * ζ ^ 24
          - ((27 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry03_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (3 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (3 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((78 / 17) : ℂ)
          + ((78 / 17) : ℂ) * ζ ^ 4
          + ((22 / 17) : ℂ) * ζ ^ 5
          - ((78 / 17) : ℂ) * ζ ^ 8
          - ((22 / 17) : ℂ) * ζ ^ 9
          - ((86 / 17) : ℂ) * ζ ^ 10
          + ((22 / 17) : ℂ) * ζ ^ 13
          + ((86 / 17) : ℂ) * ζ ^ 14
          - ((91 / 17) : ℂ) * ζ ^ 15
          - ((86 / 17) : ℂ) * ζ ^ 18
          + ((91 / 17) : ℂ) * ζ ^ 19
          - ((59 / 17) : ℂ) * ζ ^ 20
          - ((91 / 17) : ℂ) * ζ ^ 23
          + ((59 / 17) : ℂ) * ζ ^ 24
          - ((59 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((78 / 17) : ℂ)
          + ((78 / 17) : ℂ) * ζ ^ 4
          + ((22 / 17) : ℂ) * ζ ^ 5
          - ((78 / 17) : ℂ) * ζ ^ 8
          - ((22 / 17) : ℂ) * ζ ^ 9
          - ((86 / 17) : ℂ) * ζ ^ 10
          + ((22 / 17) : ℂ) * ζ ^ 13
          + ((86 / 17) : ℂ) * ζ ^ 14
          - ((91 / 17) : ℂ) * ζ ^ 15
          - ((86 / 17) : ℂ) * ζ ^ 18
          + ((91 / 17) : ℂ) * ζ ^ 19
          - ((59 / 17) : ℂ) * ζ ^ 20
          - ((91 / 17) : ℂ) * ζ ^ 23
          + ((59 / 17) : ℂ) * ζ ^ 24
          - ((59 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry03_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (3 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (3 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((99 / 34) : ℂ)
          + ((99 / 34) : ℂ) * ζ ^ 4
          + ((29 / 34) : ℂ) * ζ ^ 5
          - ((99 / 34) : ℂ) * ζ ^ 8
          - ((29 / 34) : ℂ) * ζ ^ 9
          + ((6 / 17) : ℂ) * ζ ^ 10
          + ((29 / 34) : ℂ) * ζ ^ 13
          - ((6 / 17) : ℂ) * ζ ^ 14
          + ((28 / 17) : ℂ) * ζ ^ 15
          + ((6 / 17) : ℂ) * ζ ^ 18
          - ((28 / 17) : ℂ) * ζ ^ 19
          - ((104 / 17) : ℂ) * ζ ^ 20
          + ((28 / 17) : ℂ) * ζ ^ 23
          + ((104 / 17) : ℂ) * ζ ^ 24
          - ((104 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((99 / 34) : ℂ)
          + ((99 / 34) : ℂ) * ζ ^ 4
          + ((29 / 34) : ℂ) * ζ ^ 5
          - ((99 / 34) : ℂ) * ζ ^ 8
          - ((29 / 34) : ℂ) * ζ ^ 9
          + ((6 / 17) : ℂ) * ζ ^ 10
          + ((29 / 34) : ℂ) * ζ ^ 13
          - ((6 / 17) : ℂ) * ζ ^ 14
          + ((28 / 17) : ℂ) * ζ ^ 15
          + ((6 / 17) : ℂ) * ζ ^ 18
          - ((28 / 17) : ℂ) * ζ ^ 19
          - ((104 / 17) : ℂ) * ζ ^ 20
          + ((28 / 17) : ℂ) * ζ ^ 23
          + ((104 / 17) : ℂ) * ζ ^ 24
          - ((104 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry03_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (3 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (3 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((36 / 17) : ℂ)
          - ((36 / 17) : ℂ) * ζ ^ 4
          + ((3 / 17) : ℂ) * ζ ^ 5
          + ((36 / 17) : ℂ) * ζ ^ 8
          - ((3 / 17) : ℂ) * ζ ^ 9
          + ((49 / 17) : ℂ) * ζ ^ 10
          + ((3 / 17) : ℂ) * ζ ^ 13
          - ((49 / 17) : ℂ) * ζ ^ 14
          + ((95 / 17) : ℂ) * ζ ^ 15
          + ((49 / 17) : ℂ) * ζ ^ 18
          - ((95 / 17) : ℂ) * ζ ^ 19
          - ((74 / 17) : ℂ) * ζ ^ 20
          + ((95 / 17) : ℂ) * ζ ^ 23
          + ((74 / 17) : ℂ) * ζ ^ 24
          - ((74 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((36 / 17) : ℂ)
          - ((36 / 17) : ℂ) * ζ ^ 4
          + ((3 / 17) : ℂ) * ζ ^ 5
          + ((36 / 17) : ℂ) * ζ ^ 8
          - ((3 / 17) : ℂ) * ζ ^ 9
          + ((49 / 17) : ℂ) * ζ ^ 10
          + ((3 / 17) : ℂ) * ζ ^ 13
          - ((49 / 17) : ℂ) * ζ ^ 14
          + ((95 / 17) : ℂ) * ζ ^ 15
          + ((49 / 17) : ℂ) * ζ ^ 18
          - ((95 / 17) : ℂ) * ζ ^ 19
          - ((74 / 17) : ℂ) * ζ ^ 20
          + ((95 / 17) : ℂ) * ζ ^ 23
          + ((74 / 17) : ℂ) * ζ ^ 24
          - ((74 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry03_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (3 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (3 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((67 / 34) : ℂ)
          + ((67 / 34) : ℂ) * ζ ^ 4
          - ((125 / 34) : ℂ) * ζ ^ 5
          - ((67 / 34) : ℂ) * ζ ^ 8
          + ((125 / 34) : ℂ) * ζ ^ 9
          - ((59 / 17) : ℂ) * ζ ^ 10
          - ((125 / 34) : ℂ) * ζ ^ 13
          + ((59 / 17) : ℂ) * ζ ^ 14
          - ((92 / 17) : ℂ) * ζ ^ 15
          - ((59 / 17) : ℂ) * ζ ^ 18
          + ((92 / 17) : ℂ) * ζ ^ 19
          + ((18 / 17) : ℂ) * ζ ^ 20
          - ((92 / 17) : ℂ) * ζ ^ 23
          - ((18 / 17) : ℂ) * ζ ^ 24
          + ((18 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((67 / 34) : ℂ)
          + ((67 / 34) : ℂ) * ζ ^ 4
          - ((125 / 34) : ℂ) * ζ ^ 5
          - ((67 / 34) : ℂ) * ζ ^ 8
          + ((125 / 34) : ℂ) * ζ ^ 9
          - ((59 / 17) : ℂ) * ζ ^ 10
          - ((125 / 34) : ℂ) * ζ ^ 13
          + ((59 / 17) : ℂ) * ζ ^ 14
          - ((92 / 17) : ℂ) * ζ ^ 15
          - ((59 / 17) : ℂ) * ζ ^ 18
          + ((92 / 17) : ℂ) * ζ ^ 19
          + ((18 / 17) : ℂ) * ζ ^ 20
          - ((92 / 17) : ℂ) * ζ ^ 23
          - ((18 / 17) : ℂ) * ζ ^ 24
          + ((18 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry03_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (3 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (3 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((103 / 17) : ℂ)
          + ((103 / 17) : ℂ) * ζ ^ 4
          - ((101 / 17) : ℂ) * ζ ^ 5
          - ((103 / 17) : ℂ) * ζ ^ 8
          + ((101 / 17) : ℂ) * ζ ^ 9
          - ((96 / 17) : ℂ) * ζ ^ 10
          - ((101 / 17) : ℂ) * ζ ^ 13
          + ((96 / 17) : ℂ) * ζ ^ 14
          - ((160 / 17) : ℂ) * ζ ^ 15
          - ((96 / 17) : ℂ) * ζ ^ 18
          + ((160 / 17) : ℂ) * ζ ^ 19
          - ((89 / 17) : ℂ) * ζ ^ 20
          - ((160 / 17) : ℂ) * ζ ^ 23
          + ((89 / 17) : ℂ) * ζ ^ 24
          - ((89 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((103 / 17) : ℂ)
          + ((103 / 17) : ℂ) * ζ ^ 4
          - ((101 / 17) : ℂ) * ζ ^ 5
          - ((103 / 17) : ℂ) * ζ ^ 8
          + ((101 / 17) : ℂ) * ζ ^ 9
          - ((96 / 17) : ℂ) * ζ ^ 10
          - ((101 / 17) : ℂ) * ζ ^ 13
          + ((96 / 17) : ℂ) * ζ ^ 14
          - ((160 / 17) : ℂ) * ζ ^ 15
          - ((96 / 17) : ℂ) * ζ ^ 18
          + ((160 / 17) : ℂ) * ζ ^ 19
          - ((89 / 17) : ℂ) * ζ ^ 20
          - ((160 / 17) : ℂ) * ζ ^ 23
          + ((89 / 17) : ℂ) * ζ ^ 24
          - ((89 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry03_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (3 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (3 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((52 / 17) : ℂ)
          - ((52 / 17) : ℂ) * ζ ^ 4
          + ((52 / 17) : ℂ) * ζ ^ 5
          + ((52 / 17) : ℂ) * ζ ^ 8
          - ((52 / 17) : ℂ) * ζ ^ 9
          + ((49 / 17) : ℂ) * ζ ^ 10
          + ((52 / 17) : ℂ) * ζ ^ 13
          - ((49 / 17) : ℂ) * ζ ^ 14
          + ((63 / 17) : ℂ) * ζ ^ 15
          + ((49 / 17) : ℂ) * ζ ^ 18
          - ((63 / 17) : ℂ) * ζ ^ 19
          + ((83 / 17) : ℂ) * ζ ^ 20
          + ((63 / 17) : ℂ) * ζ ^ 23
          - ((83 / 17) : ℂ) * ζ ^ 24
          + ((83 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((52 / 17) : ℂ)
          - ((52 / 17) : ℂ) * ζ ^ 4
          + ((52 / 17) : ℂ) * ζ ^ 5
          + ((52 / 17) : ℂ) * ζ ^ 8
          - ((52 / 17) : ℂ) * ζ ^ 9
          + ((49 / 17) : ℂ) * ζ ^ 10
          + ((52 / 17) : ℂ) * ζ ^ 13
          - ((49 / 17) : ℂ) * ζ ^ 14
          + ((63 / 17) : ℂ) * ζ ^ 15
          + ((49 / 17) : ℂ) * ζ ^ 18
          - ((63 / 17) : ℂ) * ζ ^ 19
          + ((83 / 17) : ℂ) * ζ ^ 20
          + ((63 / 17) : ℂ) * ζ ^ 23
          - ((83 / 17) : ℂ) * ζ ^ 24
          + ((83 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry03_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (3 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (3 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((25 / 17) : ℂ)
          + ((25 / 17) : ℂ) * ζ ^ 4
          - ((121 / 17) : ℂ) * ζ ^ 5
          - ((25 / 17) : ℂ) * ζ ^ 8
          + ((121 / 17) : ℂ) * ζ ^ 9
          - ((6 / 17) : ℂ) * ζ ^ 10
          - ((121 / 17) : ℂ) * ζ ^ 13
          + ((6 / 17) : ℂ) * ζ ^ 14
          - ((45 / 17) : ℂ) * ζ ^ 15
          - ((6 / 17) : ℂ) * ζ ^ 18
          + ((45 / 17) : ℂ) * ζ ^ 19
          - ((100 / 17) : ℂ) * ζ ^ 20
          - ((45 / 17) : ℂ) * ζ ^ 23
          + ((100 / 17) : ℂ) * ζ ^ 24
          - ((100 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((25 / 17) : ℂ)
          + ((25 / 17) : ℂ) * ζ ^ 4
          - ((121 / 17) : ℂ) * ζ ^ 5
          - ((25 / 17) : ℂ) * ζ ^ 8
          + ((121 / 17) : ℂ) * ζ ^ 9
          - ((6 / 17) : ℂ) * ζ ^ 10
          - ((121 / 17) : ℂ) * ζ ^ 13
          + ((6 / 17) : ℂ) * ζ ^ 14
          - ((45 / 17) : ℂ) * ζ ^ 15
          - ((6 / 17) : ℂ) * ζ ^ 18
          + ((45 / 17) : ℂ) * ζ ^ 19
          - ((100 / 17) : ℂ) * ζ ^ 20
          - ((45 / 17) : ℂ) * ζ ^ 23
          + ((100 / 17) : ℂ) * ζ ^ 24
          - ((100 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry03_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (3 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (3 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((63 / 34) : ℂ)
          + ((63 / 34) : ℂ) * ζ ^ 4
          + ((91 / 34) : ℂ) * ζ ^ 5
          - ((63 / 34) : ℂ) * ζ ^ 8
          - ((91 / 34) : ℂ) * ζ ^ 9
          - ((38 / 17) : ℂ) * ζ ^ 10
          + ((91 / 34) : ℂ) * ζ ^ 13
          + ((38 / 17) : ℂ) * ζ ^ 14
          - ((57 / 17) : ℂ) * ζ ^ 15
          - ((38 / 17) : ℂ) * ζ ^ 18
          + ((57 / 17) : ℂ) * ζ ^ 19
          + ((4 / 17) : ℂ) * ζ ^ 20
          - ((57 / 17) : ℂ) * ζ ^ 23
          - ((4 / 17) : ℂ) * ζ ^ 24
          + ((4 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((63 / 34) : ℂ)
          + ((63 / 34) : ℂ) * ζ ^ 4
          + ((91 / 34) : ℂ) * ζ ^ 5
          - ((63 / 34) : ℂ) * ζ ^ 8
          - ((91 / 34) : ℂ) * ζ ^ 9
          - ((38 / 17) : ℂ) * ζ ^ 10
          + ((91 / 34) : ℂ) * ζ ^ 13
          + ((38 / 17) : ℂ) * ζ ^ 14
          - ((57 / 17) : ℂ) * ζ ^ 15
          - ((38 / 17) : ℂ) * ζ ^ 18
          + ((57 / 17) : ℂ) * ζ ^ 19
          + ((4 / 17) : ℂ) * ζ ^ 20
          - ((57 / 17) : ℂ) * ζ ^ 23
          - ((4 / 17) : ℂ) * ζ ^ 24
          + ((4 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry04_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (4 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (4 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((21 / 17) : ℂ)
          - ((21 / 17) : ℂ) * ζ ^ 4
          - (2 : ℂ) * ζ ^ 5
          + ((21 / 17) : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 10
          - (2 : ℂ) * ζ ^ 13
          - ((1 / 17) : ℂ) * ζ ^ 14
          + ((41 / 34) : ℂ) * ζ ^ 15
          + ((1 / 17) : ℂ) * ζ ^ 18
          - ((41 / 34) : ℂ) * ζ ^ 19
          - ((11 / 34) : ℂ) * ζ ^ 20
          + ((41 / 34) : ℂ) * ζ ^ 23
          + ((11 / 34) : ℂ) * ζ ^ 24
          - ((11 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((21 / 17) : ℂ)
          - ((21 / 17) : ℂ) * ζ ^ 4
          - (2 : ℂ) * ζ ^ 5
          + ((21 / 17) : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 10
          - (2 : ℂ) * ζ ^ 13
          - ((1 / 17) : ℂ) * ζ ^ 14
          + ((41 / 34) : ℂ) * ζ ^ 15
          + ((1 / 17) : ℂ) * ζ ^ 18
          - ((41 / 34) : ℂ) * ζ ^ 19
          - ((11 / 34) : ℂ) * ζ ^ 20
          + ((41 / 34) : ℂ) * ζ ^ 23
          + ((11 / 34) : ℂ) * ζ ^ 24
          - ((11 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry04_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (4 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (4 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((38 / 17) : ℂ)
          - ((38 / 17) : ℂ) * ζ ^ 4
          + ((38 / 17) : ℂ) * ζ ^ 5
          + ((38 / 17) : ℂ) * ζ ^ 8
          - ((38 / 17) : ℂ) * ζ ^ 9
          - ((8 / 17) : ℂ) * ζ ^ 10
          + ((38 / 17) : ℂ) * ζ ^ 13
          + ((8 / 17) : ℂ) * ζ ^ 14
          + ((21 / 34) : ℂ) * ζ ^ 15
          - ((8 / 17) : ℂ) * ζ ^ 18
          - ((21 / 34) : ℂ) * ζ ^ 19
          - ((13 / 34) : ℂ) * ζ ^ 20
          + ((21 / 34) : ℂ) * ζ ^ 23
          + ((13 / 34) : ℂ) * ζ ^ 24
          - ((13 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((38 / 17) : ℂ)
          - ((38 / 17) : ℂ) * ζ ^ 4
          + ((38 / 17) : ℂ) * ζ ^ 5
          + ((38 / 17) : ℂ) * ζ ^ 8
          - ((38 / 17) : ℂ) * ζ ^ 9
          - ((8 / 17) : ℂ) * ζ ^ 10
          + ((38 / 17) : ℂ) * ζ ^ 13
          + ((8 / 17) : ℂ) * ζ ^ 14
          + ((21 / 34) : ℂ) * ζ ^ 15
          - ((8 / 17) : ℂ) * ζ ^ 18
          - ((21 / 34) : ℂ) * ζ ^ 19
          - ((13 / 34) : ℂ) * ζ ^ 20
          + ((21 / 34) : ℂ) * ζ ^ 23
          + ((13 / 34) : ℂ) * ζ ^ 24
          - ((13 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry04_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (4 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (4 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((111 / 34) : ℂ)
          - ((111 / 34) : ℂ) * ζ ^ 4
          + ((45 / 34) : ℂ) * ζ ^ 5
          + ((111 / 34) : ℂ) * ζ ^ 8
          - ((45 / 34) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 10
          + ((45 / 34) : ℂ) * ζ ^ 13
          + ((7 / 17) : ℂ) * ζ ^ 14
          + ((89 / 34) : ℂ) * ζ ^ 15
          - ((7 / 17) : ℂ) * ζ ^ 18
          - ((89 / 34) : ℂ) * ζ ^ 19
          + ((47 / 34) : ℂ) * ζ ^ 20
          + ((89 / 34) : ℂ) * ζ ^ 23
          - ((47 / 34) : ℂ) * ζ ^ 24
          + ((47 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((111 / 34) : ℂ)
          - ((111 / 34) : ℂ) * ζ ^ 4
          + ((45 / 34) : ℂ) * ζ ^ 5
          + ((111 / 34) : ℂ) * ζ ^ 8
          - ((45 / 34) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 10
          + ((45 / 34) : ℂ) * ζ ^ 13
          + ((7 / 17) : ℂ) * ζ ^ 14
          + ((89 / 34) : ℂ) * ζ ^ 15
          - ((7 / 17) : ℂ) * ζ ^ 18
          - ((89 / 34) : ℂ) * ζ ^ 19
          + ((47 / 34) : ℂ) * ζ ^ 20
          + ((89 / 34) : ℂ) * ζ ^ 23
          - ((47 / 34) : ℂ) * ζ ^ 24
          + ((47 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry04_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (4 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (4 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((13 / 17) : ℂ)
          + ((13 / 17) : ℂ) * ζ ^ 4
          - ((13 / 17) : ℂ) * ζ ^ 8
          + ((18 / 17) : ℂ) * ζ ^ 10
          - ((18 / 17) : ℂ) * ζ ^ 14
          - ((42 / 17) : ℂ) * ζ ^ 15
          + ((18 / 17) : ℂ) * ζ ^ 18
          + ((42 / 17) : ℂ) * ζ ^ 19
          + ((31 / 17) : ℂ) * ζ ^ 20
          - ((42 / 17) : ℂ) * ζ ^ 23
          - ((31 / 17) : ℂ) * ζ ^ 24
          + ((31 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((13 / 17) : ℂ)
          + ((13 / 17) : ℂ) * ζ ^ 4
          - ((13 / 17) : ℂ) * ζ ^ 8
          + ((18 / 17) : ℂ) * ζ ^ 10
          - ((18 / 17) : ℂ) * ζ ^ 14
          - ((42 / 17) : ℂ) * ζ ^ 15
          + ((18 / 17) : ℂ) * ζ ^ 18
          + ((42 / 17) : ℂ) * ζ ^ 19
          + ((31 / 17) : ℂ) * ζ ^ 20
          - ((42 / 17) : ℂ) * ζ ^ 23
          - ((31 / 17) : ℂ) * ζ ^ 24
          + ((31 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry04_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (4 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (4 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((111 / 34) : ℂ)
          + ((111 / 34) : ℂ) * ζ ^ 4
          + ((2 / 17) : ℂ) * ζ ^ 5
          - ((111 / 34) : ℂ) * ζ ^ 8
          - ((2 / 17) : ℂ) * ζ ^ 9
          + ((27 / 34) : ℂ) * ζ ^ 10
          + ((2 / 17) : ℂ) * ζ ^ 13
          - ((27 / 34) : ℂ) * ζ ^ 14
          - ((65 / 17) : ℂ) * ζ ^ 15
          + ((27 / 34) : ℂ) * ζ ^ 18
          + ((65 / 17) : ℂ) * ζ ^ 19
          + ((57 / 34) : ℂ) * ζ ^ 20
          - ((65 / 17) : ℂ) * ζ ^ 23
          - ((57 / 34) : ℂ) * ζ ^ 24
          + ((57 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((111 / 34) : ℂ)
          + ((111 / 34) : ℂ) * ζ ^ 4
          + ((2 / 17) : ℂ) * ζ ^ 5
          - ((111 / 34) : ℂ) * ζ ^ 8
          - ((2 / 17) : ℂ) * ζ ^ 9
          + ((27 / 34) : ℂ) * ζ ^ 10
          + ((2 / 17) : ℂ) * ζ ^ 13
          - ((27 / 34) : ℂ) * ζ ^ 14
          - ((65 / 17) : ℂ) * ζ ^ 15
          + ((27 / 34) : ℂ) * ζ ^ 18
          + ((65 / 17) : ℂ) * ζ ^ 19
          + ((57 / 34) : ℂ) * ζ ^ 20
          - ((65 / 17) : ℂ) * ζ ^ 23
          - ((57 / 34) : ℂ) * ζ ^ 24
          + ((57 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry04_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (4 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (4 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((5 / 2) : ℂ)
          - ((5 / 2) : ℂ) * ζ ^ 4
          + ((53 / 17) : ℂ) * ζ ^ 5
          + ((5 / 2) : ℂ) * ζ ^ 8
          - ((53 / 17) : ℂ) * ζ ^ 9
          - ((43 / 34) : ℂ) * ζ ^ 10
          + ((53 / 17) : ℂ) * ζ ^ 13
          + ((43 / 34) : ℂ) * ζ ^ 14
          + ((67 / 34) : ℂ) * ζ ^ 15
          - ((43 / 34) : ℂ) * ζ ^ 18
          - ((67 / 34) : ℂ) * ζ ^ 19
          - ζ ^ 20
          + ((67 / 34) : ℂ) * ζ ^ 23
          + ζ ^ 24
          - ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((5 / 2) : ℂ)
          - ((5 / 2) : ℂ) * ζ ^ 4
          + ((53 / 17) : ℂ) * ζ ^ 5
          + ((5 / 2) : ℂ) * ζ ^ 8
          - ((53 / 17) : ℂ) * ζ ^ 9
          - ((43 / 34) : ℂ) * ζ ^ 10
          + ((53 / 17) : ℂ) * ζ ^ 13
          + ((43 / 34) : ℂ) * ζ ^ 14
          + ((67 / 34) : ℂ) * ζ ^ 15
          - ((43 / 34) : ℂ) * ζ ^ 18
          - ((67 / 34) : ℂ) * ζ ^ 19
          - ζ ^ 20
          + ((67 / 34) : ℂ) * ζ ^ 23
          + ζ ^ 24
          - ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry04_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (4 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (4 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((10 / 17) : ℂ)
          - ((10 / 17) : ℂ) * ζ ^ 4
          + ((83 / 17) : ℂ) * ζ ^ 5
          + ((10 / 17) : ℂ) * ζ ^ 8
          - ((83 / 17) : ℂ) * ζ ^ 9
          - ((10 / 17) : ℂ) * ζ ^ 10
          + ((83 / 17) : ℂ) * ζ ^ 13
          + ((10 / 17) : ℂ) * ζ ^ 14
          + ((13 / 34) : ℂ) * ζ ^ 15
          - ((10 / 17) : ℂ) * ζ ^ 18
          - ((13 / 34) : ℂ) * ζ ^ 19
          + ((21 / 34) : ℂ) * ζ ^ 20
          + ((13 / 34) : ℂ) * ζ ^ 23
          - ((21 / 34) : ℂ) * ζ ^ 24
          + ((21 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((10 / 17) : ℂ)
          - ((10 / 17) : ℂ) * ζ ^ 4
          + ((83 / 17) : ℂ) * ζ ^ 5
          + ((10 / 17) : ℂ) * ζ ^ 8
          - ((83 / 17) : ℂ) * ζ ^ 9
          - ((10 / 17) : ℂ) * ζ ^ 10
          + ((83 / 17) : ℂ) * ζ ^ 13
          + ((10 / 17) : ℂ) * ζ ^ 14
          + ((13 / 34) : ℂ) * ζ ^ 15
          - ((10 / 17) : ℂ) * ζ ^ 18
          - ((13 / 34) : ℂ) * ζ ^ 19
          + ((21 / 34) : ℂ) * ζ ^ 20
          + ((13 / 34) : ℂ) * ζ ^ 23
          - ((21 / 34) : ℂ) * ζ ^ 24
          + ((21 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry04_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (4 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (4 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((11 / 34) : ℂ)
          + ((11 / 34) : ℂ) * ζ ^ 4
          - ((103 / 34) : ℂ) * ζ ^ 5
          - ((11 / 34) : ℂ) * ζ ^ 8
          + ((103 / 34) : ℂ) * ζ ^ 9
          + ((4 / 17) : ℂ) * ζ ^ 10
          - ((103 / 34) : ℂ) * ζ ^ 13
          - ((4 / 17) : ℂ) * ζ ^ 14
          + ((10 / 17) : ℂ) * ζ ^ 15
          + ((4 / 17) : ℂ) * ζ ^ 18
          - ((10 / 17) : ℂ) * ζ ^ 19
          - ((13 / 17) : ℂ) * ζ ^ 20
          + ((10 / 17) : ℂ) * ζ ^ 23
          + ((13 / 17) : ℂ) * ζ ^ 24
          - ((13 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((11 / 34) : ℂ)
          + ((11 / 34) : ℂ) * ζ ^ 4
          - ((103 / 34) : ℂ) * ζ ^ 5
          - ((11 / 34) : ℂ) * ζ ^ 8
          + ((103 / 34) : ℂ) * ζ ^ 9
          + ((4 / 17) : ℂ) * ζ ^ 10
          - ((103 / 34) : ℂ) * ζ ^ 13
          - ((4 / 17) : ℂ) * ζ ^ 14
          + ((10 / 17) : ℂ) * ζ ^ 15
          + ((4 / 17) : ℂ) * ζ ^ 18
          - ((10 / 17) : ℂ) * ζ ^ 19
          - ((13 / 17) : ℂ) * ζ ^ 20
          + ((10 / 17) : ℂ) * ζ ^ 23
          + ((13 / 17) : ℂ) * ζ ^ 24
          - ((13 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry04_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (4 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (4 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((3 / 17) : ℂ)
          - ((3 / 17) : ℂ) * ζ ^ 4
          + ((37 / 17) : ℂ) * ζ ^ 5
          + ((3 / 17) : ℂ) * ζ ^ 8
          - ((37 / 17) : ℂ) * ζ ^ 9
          + ((11 / 17) : ℂ) * ζ ^ 10
          + ((37 / 17) : ℂ) * ζ ^ 13
          - ((11 / 17) : ℂ) * ζ ^ 14
          - ((47 / 17) : ℂ) * ζ ^ 15
          + ((11 / 17) : ℂ) * ζ ^ 18
          + ((47 / 17) : ℂ) * ζ ^ 19
          + ((49 / 17) : ℂ) * ζ ^ 20
          - ((47 / 17) : ℂ) * ζ ^ 23
          - ((49 / 17) : ℂ) * ζ ^ 24
          + ((49 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((3 / 17) : ℂ)
          - ((3 / 17) : ℂ) * ζ ^ 4
          + ((37 / 17) : ℂ) * ζ ^ 5
          + ((3 / 17) : ℂ) * ζ ^ 8
          - ((37 / 17) : ℂ) * ζ ^ 9
          + ((11 / 17) : ℂ) * ζ ^ 10
          + ((37 / 17) : ℂ) * ζ ^ 13
          - ((11 / 17) : ℂ) * ζ ^ 14
          - ((47 / 17) : ℂ) * ζ ^ 15
          + ((11 / 17) : ℂ) * ζ ^ 18
          + ((47 / 17) : ℂ) * ζ ^ 19
          + ((49 / 17) : ℂ) * ζ ^ 20
          - ((47 / 17) : ℂ) * ζ ^ 23
          - ((49 / 17) : ℂ) * ζ ^ 24
          + ((49 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry04_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (4 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (4 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((45 / 34) : ℂ)
          - ((45 / 34) : ℂ) * ζ ^ 4
          + ((10 / 17) : ℂ) * ζ ^ 5
          + ((45 / 34) : ℂ) * ζ ^ 8
          - ((10 / 17) : ℂ) * ζ ^ 9
          - ((21 / 34) : ℂ) * ζ ^ 10
          + ((10 / 17) : ℂ) * ζ ^ 13
          + ((21 / 34) : ℂ) * ζ ^ 14
          + ((45 / 34) : ℂ) * ζ ^ 15
          - ((21 / 34) : ℂ) * ζ ^ 18
          - ((45 / 34) : ℂ) * ζ ^ 19
          - ((15 / 17) : ℂ) * ζ ^ 20
          + ((45 / 34) : ℂ) * ζ ^ 23
          + ((15 / 17) : ℂ) * ζ ^ 24
          - ((15 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((45 / 34) : ℂ)
          - ((45 / 34) : ℂ) * ζ ^ 4
          + ((10 / 17) : ℂ) * ζ ^ 5
          + ((45 / 34) : ℂ) * ζ ^ 8
          - ((10 / 17) : ℂ) * ζ ^ 9
          - ((21 / 34) : ℂ) * ζ ^ 10
          + ((10 / 17) : ℂ) * ζ ^ 13
          + ((21 / 34) : ℂ) * ζ ^ 14
          + ((45 / 34) : ℂ) * ζ ^ 15
          - ((21 / 34) : ℂ) * ζ ^ 18
          - ((45 / 34) : ℂ) * ζ ^ 19
          - ((15 / 17) : ℂ) * ζ ^ 20
          + ((45 / 34) : ℂ) * ζ ^ 23
          + ((15 / 17) : ℂ) * ζ ^ 24
          - ((15 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry05_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (5 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (5 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((55 / 34) : ℂ)
          - ((55 / 34) : ℂ) * ζ ^ 4
          + ((7 / 17) : ℂ) * ζ ^ 5
          + ((55 / 34) : ℂ) * ζ ^ 8
          - ((7 / 17) : ℂ) * ζ ^ 9
          + ((29 / 34) : ℂ) * ζ ^ 10
          + ((7 / 17) : ℂ) * ζ ^ 13
          - ((29 / 34) : ℂ) * ζ ^ 14
          + ((8 / 17) : ℂ) * ζ ^ 15
          + ((29 / 34) : ℂ) * ζ ^ 18
          - ((8 / 17) : ℂ) * ζ ^ 19
          + ((1 / 34) : ℂ) * ζ ^ 20
          + ((8 / 17) : ℂ) * ζ ^ 23
          - ((1 / 34) : ℂ) * ζ ^ 24
          + ((1 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((55 / 34) : ℂ)
          - ((55 / 34) : ℂ) * ζ ^ 4
          + ((7 / 17) : ℂ) * ζ ^ 5
          + ((55 / 34) : ℂ) * ζ ^ 8
          - ((7 / 17) : ℂ) * ζ ^ 9
          + ((29 / 34) : ℂ) * ζ ^ 10
          + ((7 / 17) : ℂ) * ζ ^ 13
          - ((29 / 34) : ℂ) * ζ ^ 14
          + ((8 / 17) : ℂ) * ζ ^ 15
          + ((29 / 34) : ℂ) * ζ ^ 18
          - ((8 / 17) : ℂ) * ζ ^ 19
          + ((1 / 34) : ℂ) * ζ ^ 20
          + ((8 / 17) : ℂ) * ζ ^ 23
          - ((1 / 34) : ℂ) * ζ ^ 24
          + ((1 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry05_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (5 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (5 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((39 / 17) : ℂ)
          - ((39 / 17) : ℂ) * ζ ^ 4
          + ((63 / 17) : ℂ) * ζ ^ 5
          + ((39 / 17) : ℂ) * ζ ^ 8
          - ((63 / 17) : ℂ) * ζ ^ 9
          + ((55 / 17) : ℂ) * ζ ^ 10
          + ((63 / 17) : ℂ) * ζ ^ 13
          - ((55 / 17) : ℂ) * ζ ^ 14
          + ((103 / 34) : ℂ) * ζ ^ 15
          + ((55 / 17) : ℂ) * ζ ^ 18
          - ((103 / 34) : ℂ) * ζ ^ 19
          + ((55 / 34) : ℂ) * ζ ^ 20
          + ((103 / 34) : ℂ) * ζ ^ 23
          - ((55 / 34) : ℂ) * ζ ^ 24
          + ((55 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((39 / 17) : ℂ)
          - ((39 / 17) : ℂ) * ζ ^ 4
          + ((63 / 17) : ℂ) * ζ ^ 5
          + ((39 / 17) : ℂ) * ζ ^ 8
          - ((63 / 17) : ℂ) * ζ ^ 9
          + ((55 / 17) : ℂ) * ζ ^ 10
          + ((63 / 17) : ℂ) * ζ ^ 13
          - ((55 / 17) : ℂ) * ζ ^ 14
          + ((103 / 34) : ℂ) * ζ ^ 15
          + ((55 / 17) : ℂ) * ζ ^ 18
          - ((103 / 34) : ℂ) * ζ ^ 19
          + ((55 / 34) : ℂ) * ζ ^ 20
          + ((103 / 34) : ℂ) * ζ ^ 23
          - ((55 / 34) : ℂ) * ζ ^ 24
          + ((55 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry05_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (5 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (5 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((19 / 34) : ℂ)
          - ((19 / 34) : ℂ) * ζ ^ 4
          + ((43 / 34) : ℂ) * ζ ^ 5
          + ((19 / 34) : ℂ) * ζ ^ 8
          - ((43 / 34) : ℂ) * ζ ^ 9
          + ((39 / 17) : ℂ) * ζ ^ 10
          + ((43 / 34) : ℂ) * ζ ^ 13
          - ((39 / 17) : ℂ) * ζ ^ 14
          + ((211 / 34) : ℂ) * ζ ^ 15
          + ((39 / 17) : ℂ) * ζ ^ 18
          - ((211 / 34) : ℂ) * ζ ^ 19
          + ((93 / 34) : ℂ) * ζ ^ 20
          + ((211 / 34) : ℂ) * ζ ^ 23
          - ((93 / 34) : ℂ) * ζ ^ 24
          + ((93 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((19 / 34) : ℂ)
          - ((19 / 34) : ℂ) * ζ ^ 4
          + ((43 / 34) : ℂ) * ζ ^ 5
          + ((19 / 34) : ℂ) * ζ ^ 8
          - ((43 / 34) : ℂ) * ζ ^ 9
          + ((39 / 17) : ℂ) * ζ ^ 10
          + ((43 / 34) : ℂ) * ζ ^ 13
          - ((39 / 17) : ℂ) * ζ ^ 14
          + ((211 / 34) : ℂ) * ζ ^ 15
          + ((39 / 17) : ℂ) * ζ ^ 18
          - ((211 / 34) : ℂ) * ζ ^ 19
          + ((93 / 34) : ℂ) * ζ ^ 20
          + ((211 / 34) : ℂ) * ζ ^ 23
          - ((93 / 34) : ℂ) * ζ ^ 24
          + ((93 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry05_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (5 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (5 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((53 / 34) : ℂ)
          + ((53 / 34) : ℂ) * ζ ^ 4
          - ((43 / 17) : ℂ) * ζ ^ 5
          - ((53 / 34) : ℂ) * ζ ^ 8
          + ((43 / 17) : ℂ) * ζ ^ 9
          - ((113 / 34) : ℂ) * ζ ^ 10
          - ((43 / 17) : ℂ) * ζ ^ 13
          + ((113 / 34) : ℂ) * ζ ^ 14
          + ((43 / 34) : ℂ) * ζ ^ 15
          - ((113 / 34) : ℂ) * ζ ^ 18
          - ((43 / 34) : ℂ) * ζ ^ 19
          + ((14 / 17) : ℂ) * ζ ^ 20
          + ((43 / 34) : ℂ) * ζ ^ 23
          - ((14 / 17) : ℂ) * ζ ^ 24
          + ((14 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((53 / 34) : ℂ)
          + ((53 / 34) : ℂ) * ζ ^ 4
          - ((43 / 17) : ℂ) * ζ ^ 5
          - ((53 / 34) : ℂ) * ζ ^ 8
          + ((43 / 17) : ℂ) * ζ ^ 9
          - ((113 / 34) : ℂ) * ζ ^ 10
          - ((43 / 17) : ℂ) * ζ ^ 13
          + ((113 / 34) : ℂ) * ζ ^ 14
          + ((43 / 34) : ℂ) * ζ ^ 15
          - ((113 / 34) : ℂ) * ζ ^ 18
          - ((43 / 34) : ℂ) * ζ ^ 19
          + ((14 / 17) : ℂ) * ζ ^ 20
          + ((43 / 34) : ℂ) * ζ ^ 23
          - ((14 / 17) : ℂ) * ζ ^ 24
          + ((14 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry05_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (5 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (5 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((99 / 34) : ℂ)
          + ((99 / 34) : ℂ) * ζ ^ 4
          - ((55 / 17) : ℂ) * ζ ^ 5
          - ((99 / 34) : ℂ) * ζ ^ 8
          + ((55 / 17) : ℂ) * ζ ^ 9
          - ((215 / 34) : ℂ) * ζ ^ 10
          - ((55 / 17) : ℂ) * ζ ^ 13
          + ((215 / 34) : ℂ) * ζ ^ 14
          - ((62 / 17) : ℂ) * ζ ^ 15
          - ((215 / 34) : ℂ) * ζ ^ 18
          + ((62 / 17) : ℂ) * ζ ^ 19
          + ((1 / 2) : ℂ) * ζ ^ 20
          - ((62 / 17) : ℂ) * ζ ^ 23
          - ((1 / 2) : ℂ) * ζ ^ 24
          + ((1 / 2) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((99 / 34) : ℂ)
          + ((99 / 34) : ℂ) * ζ ^ 4
          - ((55 / 17) : ℂ) * ζ ^ 5
          - ((99 / 34) : ℂ) * ζ ^ 8
          + ((55 / 17) : ℂ) * ζ ^ 9
          - ((215 / 34) : ℂ) * ζ ^ 10
          - ((55 / 17) : ℂ) * ζ ^ 13
          + ((215 / 34) : ℂ) * ζ ^ 14
          - ((62 / 17) : ℂ) * ζ ^ 15
          - ((215 / 34) : ℂ) * ζ ^ 18
          + ((62 / 17) : ℂ) * ζ ^ 19
          + ((1 / 2) : ℂ) * ζ ^ 20
          - ((62 / 17) : ℂ) * ζ ^ 23
          - ((1 / 2) : ℂ) * ζ ^ 24
          + ((1 / 2) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry05_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (5 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (5 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((45 / 17) : ℂ)
          - ((45 / 17) : ℂ) * ζ ^ 4
          + ((90 / 17) : ℂ) * ζ ^ 5
          + ((45 / 17) : ℂ) * ζ ^ 8
          - ((90 / 17) : ℂ) * ζ ^ 9
          + (5 : ℂ) * ζ ^ 10
          + ((90 / 17) : ℂ) * ζ ^ 13
          - (5 : ℂ) * ζ ^ 14
          + ((31 / 17) : ℂ) * ζ ^ 15
          + (5 : ℂ) * ζ ^ 18
          - ((31 / 17) : ℂ) * ζ ^ 19
          + ((45 / 17) : ℂ) * ζ ^ 20
          + ((31 / 17) : ℂ) * ζ ^ 23
          - ((45 / 17) : ℂ) * ζ ^ 24
          + ((45 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((45 / 17) : ℂ)
          - ((45 / 17) : ℂ) * ζ ^ 4
          + ((90 / 17) : ℂ) * ζ ^ 5
          + ((45 / 17) : ℂ) * ζ ^ 8
          - ((90 / 17) : ℂ) * ζ ^ 9
          + (5 : ℂ) * ζ ^ 10
          + ((90 / 17) : ℂ) * ζ ^ 13
          - (5 : ℂ) * ζ ^ 14
          + ((31 / 17) : ℂ) * ζ ^ 15
          + (5 : ℂ) * ζ ^ 18
          - ((31 / 17) : ℂ) * ζ ^ 19
          + ((45 / 17) : ℂ) * ζ ^ 20
          + ((31 / 17) : ℂ) * ζ ^ 23
          - ((45 / 17) : ℂ) * ζ ^ 24
          + ((45 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry05_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (5 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (5 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((5 / 17) : ℂ)
          + ((5 / 17) : ℂ) * ζ ^ 4
          + ((32 / 17) : ℂ) * ζ ^ 5
          - ((5 / 17) : ℂ) * ζ ^ 8
          - ((32 / 17) : ℂ) * ζ ^ 9
          + ((33 / 17) : ℂ) * ζ ^ 10
          + ((32 / 17) : ℂ) * ζ ^ 13
          - ((33 / 17) : ℂ) * ζ ^ 14
          + ((13 / 34) : ℂ) * ζ ^ 15
          + ((33 / 17) : ℂ) * ζ ^ 18
          - ((13 / 34) : ℂ) * ζ ^ 19
          + ((1 / 2) : ℂ) * ζ ^ 20
          + ((13 / 34) : ℂ) * ζ ^ 23
          - ((1 / 2) : ℂ) * ζ ^ 24
          + ((1 / 2) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((5 / 17) : ℂ)
          + ((5 / 17) : ℂ) * ζ ^ 4
          + ((32 / 17) : ℂ) * ζ ^ 5
          - ((5 / 17) : ℂ) * ζ ^ 8
          - ((32 / 17) : ℂ) * ζ ^ 9
          + ((33 / 17) : ℂ) * ζ ^ 10
          + ((32 / 17) : ℂ) * ζ ^ 13
          - ((33 / 17) : ℂ) * ζ ^ 14
          + ((13 / 34) : ℂ) * ζ ^ 15
          + ((33 / 17) : ℂ) * ζ ^ 18
          - ((13 / 34) : ℂ) * ζ ^ 19
          + ((1 / 2) : ℂ) * ζ ^ 20
          + ((13 / 34) : ℂ) * ζ ^ 23
          - ((1 / 2) : ℂ) * ζ ^ 24
          + ((1 / 2) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry05_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (5 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (5 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((7 / 34) : ℂ)
          + ((7 / 34) : ℂ) * ζ ^ 4
          - ((67 / 34) : ℂ) * ζ ^ 5
          - ((7 / 34) : ℂ) * ζ ^ 8
          + ((67 / 34) : ℂ) * ζ ^ 9
          - ((19 / 17) : ℂ) * ζ ^ 10
          - ((67 / 34) : ℂ) * ζ ^ 13
          + ((19 / 17) : ℂ) * ζ ^ 14
          - ((22 / 17) : ℂ) * ζ ^ 15
          - ((19 / 17) : ℂ) * ζ ^ 18
          + ((22 / 17) : ℂ) * ζ ^ 19
          - ((36 / 17) : ℂ) * ζ ^ 20
          - ((22 / 17) : ℂ) * ζ ^ 23
          + ((36 / 17) : ℂ) * ζ ^ 24
          - ((36 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((7 / 34) : ℂ)
          + ((7 / 34) : ℂ) * ζ ^ 4
          - ((67 / 34) : ℂ) * ζ ^ 5
          - ((7 / 34) : ℂ) * ζ ^ 8
          + ((67 / 34) : ℂ) * ζ ^ 9
          - ((19 / 17) : ℂ) * ζ ^ 10
          - ((67 / 34) : ℂ) * ζ ^ 13
          + ((19 / 17) : ℂ) * ζ ^ 14
          - ((22 / 17) : ℂ) * ζ ^ 15
          - ((19 / 17) : ℂ) * ζ ^ 18
          + ((22 / 17) : ℂ) * ζ ^ 19
          - ((36 / 17) : ℂ) * ζ ^ 20
          - ((22 / 17) : ℂ) * ζ ^ 23
          + ((36 / 17) : ℂ) * ζ ^ 24
          - ((36 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry05_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (5 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (5 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((28 / 17) : ℂ)
          - ((28 / 17) : ℂ) * ζ ^ 4
          + ((42 / 17) : ℂ) * ζ ^ 5
          + ((28 / 17) : ℂ) * ζ ^ 8
          - ((42 / 17) : ℂ) * ζ ^ 9
          - ((28 / 17) : ℂ) * ζ ^ 10
          + ((42 / 17) : ℂ) * ζ ^ 13
          + ((28 / 17) : ℂ) * ζ ^ 14
          - ((16 / 17) : ℂ) * ζ ^ 15
          - ((28 / 17) : ℂ) * ζ ^ 18
          + ((16 / 17) : ℂ) * ζ ^ 19
          + ((29 / 17) : ℂ) * ζ ^ 20
          - ((16 / 17) : ℂ) * ζ ^ 23
          - ((29 / 17) : ℂ) * ζ ^ 24
          + ((29 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((28 / 17) : ℂ)
          - ((28 / 17) : ℂ) * ζ ^ 4
          + ((42 / 17) : ℂ) * ζ ^ 5
          + ((28 / 17) : ℂ) * ζ ^ 8
          - ((42 / 17) : ℂ) * ζ ^ 9
          - ((28 / 17) : ℂ) * ζ ^ 10
          + ((42 / 17) : ℂ) * ζ ^ 13
          + ((28 / 17) : ℂ) * ζ ^ 14
          - ((16 / 17) : ℂ) * ζ ^ 15
          - ((28 / 17) : ℂ) * ζ ^ 18
          + ((16 / 17) : ℂ) * ζ ^ 19
          + ((29 / 17) : ℂ) * ζ ^ 20
          - ((16 / 17) : ℂ) * ζ ^ 23
          - ((29 / 17) : ℂ) * ζ ^ 24
          + ((29 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry05_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (5 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (5 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((4 / 17) : ℂ)
          - ((4 / 17) : ℂ) * ζ ^ 4
          + ((15 / 17) : ℂ) * ζ ^ 5
          + ((4 / 17) : ℂ) * ζ ^ 8
          - ((15 / 17) : ℂ) * ζ ^ 9
          + ((65 / 17) : ℂ) * ζ ^ 10
          + ((15 / 17) : ℂ) * ζ ^ 13
          - ((65 / 17) : ℂ) * ζ ^ 14
          + ((55 / 17) : ℂ) * ζ ^ 15
          + ((65 / 17) : ℂ) * ζ ^ 18
          - ((55 / 17) : ℂ) * ζ ^ 19
          + ((3 / 17) : ℂ) * ζ ^ 20
          + ((55 / 17) : ℂ) * ζ ^ 23
          - ((3 / 17) : ℂ) * ζ ^ 24
          + ((3 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((4 / 17) : ℂ)
          - ((4 / 17) : ℂ) * ζ ^ 4
          + ((15 / 17) : ℂ) * ζ ^ 5
          + ((4 / 17) : ℂ) * ζ ^ 8
          - ((15 / 17) : ℂ) * ζ ^ 9
          + ((65 / 17) : ℂ) * ζ ^ 10
          + ((15 / 17) : ℂ) * ζ ^ 13
          - ((65 / 17) : ℂ) * ζ ^ 14
          + ((55 / 17) : ℂ) * ζ ^ 15
          + ((65 / 17) : ℂ) * ζ ^ 18
          - ((55 / 17) : ℂ) * ζ ^ 19
          + ((3 / 17) : ℂ) * ζ ^ 20
          + ((55 / 17) : ℂ) * ζ ^ 23
          - ((3 / 17) : ℂ) * ζ ^ 24
          + ((3 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry06_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (6 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (6 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((3 / 34) : ℂ)
          + ((3 / 34) : ℂ) * ζ ^ 4
          + ((11 / 34) : ℂ) * ζ ^ 5
          - ((3 / 34) : ℂ) * ζ ^ 8
          - ((11 / 34) : ℂ) * ζ ^ 9
          + ((11 / 34) : ℂ) * ζ ^ 13
          + ((7 / 34) : ℂ) * ζ ^ 15
          - ((7 / 34) : ℂ) * ζ ^ 19
          - ((3 / 34) : ℂ) * ζ ^ 20
          + ((7 / 34) : ℂ) * ζ ^ 23
          + ((3 / 34) : ℂ) * ζ ^ 24
          - ((3 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((3 / 34) : ℂ)
          + ((3 / 34) : ℂ) * ζ ^ 4
          + ((11 / 34) : ℂ) * ζ ^ 5
          - ((3 / 34) : ℂ) * ζ ^ 8
          - ((11 / 34) : ℂ) * ζ ^ 9
          + ((11 / 34) : ℂ) * ζ ^ 13
          + ((7 / 34) : ℂ) * ζ ^ 15
          - ((7 / 34) : ℂ) * ζ ^ 19
          - ((3 / 34) : ℂ) * ζ ^ 20
          + ((7 / 34) : ℂ) * ζ ^ 23
          + ((3 / 34) : ℂ) * ζ ^ 24
          - ((3 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry06_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (6 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (6 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((11 / 17) : ℂ)
          + ((11 / 17) : ℂ) * ζ ^ 4
          - ((5 / 17) : ℂ) * ζ ^ 5
          - ((11 / 17) : ℂ) * ζ ^ 8
          + ((5 / 17) : ℂ) * ζ ^ 9
          - ((5 / 17) : ℂ) * ζ ^ 13
          + ((3 / 17) : ℂ) * ζ ^ 15
          - ((3 / 17) : ℂ) * ζ ^ 19
          - ((11 / 17) : ℂ) * ζ ^ 20
          + ((3 / 17) : ℂ) * ζ ^ 23
          + ((11 / 17) : ℂ) * ζ ^ 24
          - ((11 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((11 / 17) : ℂ)
          + ((11 / 17) : ℂ) * ζ ^ 4
          - ((5 / 17) : ℂ) * ζ ^ 5
          - ((11 / 17) : ℂ) * ζ ^ 8
          + ((5 / 17) : ℂ) * ζ ^ 9
          - ((5 / 17) : ℂ) * ζ ^ 13
          + ((3 / 17) : ℂ) * ζ ^ 15
          - ((3 / 17) : ℂ) * ζ ^ 19
          - ((11 / 17) : ℂ) * ζ ^ 20
          + ((3 / 17) : ℂ) * ζ ^ 23
          + ((11 / 17) : ℂ) * ζ ^ 24
          - ((11 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry06_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (6 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (6 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((9 / 17) : ℂ)
          - ((9 / 17) : ℂ) * ζ ^ 4
          + ((1 / 17) : ℂ) * ζ ^ 5
          + ((9 / 17) : ℂ) * ζ ^ 8
          - ((1 / 17) : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 13
          - ((4 / 17) : ℂ) * ζ ^ 15
          + ((4 / 17) : ℂ) * ζ ^ 19
          + ((9 / 17) : ℂ) * ζ ^ 20
          - ((4 / 17) : ℂ) * ζ ^ 23
          - ((9 / 17) : ℂ) * ζ ^ 24
          + ((9 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((9 / 17) : ℂ)
          - ((9 / 17) : ℂ) * ζ ^ 4
          + ((1 / 17) : ℂ) * ζ ^ 5
          + ((9 / 17) : ℂ) * ζ ^ 8
          - ((1 / 17) : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 13
          - ((4 / 17) : ℂ) * ζ ^ 15
          + ((4 / 17) : ℂ) * ζ ^ 19
          + ((9 / 17) : ℂ) * ζ ^ 20
          - ((4 / 17) : ℂ) * ζ ^ 23
          - ((9 / 17) : ℂ) * ζ ^ 24
          + ((9 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry06_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (6 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (6 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((33 / 34) : ℂ)
          - ((33 / 34) : ℂ) * ζ ^ 4
          - ((19 / 34) : ℂ) * ζ ^ 5
          + ((33 / 34) : ℂ) * ζ ^ 8
          + ((19 / 34) : ℂ) * ζ ^ 9
          - ((19 / 34) : ℂ) * ζ ^ 13
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
          - ((19 / 34) : ℂ) * ζ ^ 5
          + ((33 / 34) : ℂ) * ζ ^ 8
          + ((19 / 34) : ℂ) * ζ ^ 9
          - ((19 / 34) : ℂ) * ζ ^ 13
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
private theorem alternatingSixAmbientRow24_longPrefix77_entry06_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (6 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (6 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((10 / 17) : ℂ)
          - ((10 / 17) : ℂ) * ζ ^ 4
          + ((3 / 17) : ℂ) * ζ ^ 5
          + ((10 / 17) : ℂ) * ζ ^ 8
          - ((3 / 17) : ℂ) * ζ ^ 9
          + ((3 / 17) : ℂ) * ζ ^ 13
          - ((12 / 17) : ℂ) * ζ ^ 15
          + ((12 / 17) : ℂ) * ζ ^ 19
          + ((10 / 17) : ℂ) * ζ ^ 20
          - ((12 / 17) : ℂ) * ζ ^ 23
          - ((10 / 17) : ℂ) * ζ ^ 24
          + ((10 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((10 / 17) : ℂ)
          - ((10 / 17) : ℂ) * ζ ^ 4
          + ((3 / 17) : ℂ) * ζ ^ 5
          + ((10 / 17) : ℂ) * ζ ^ 8
          - ((3 / 17) : ℂ) * ζ ^ 9
          + ((3 / 17) : ℂ) * ζ ^ 13
          - ((12 / 17) : ℂ) * ζ ^ 15
          + ((12 / 17) : ℂ) * ζ ^ 19
          + ((10 / 17) : ℂ) * ζ ^ 20
          - ((12 / 17) : ℂ) * ζ ^ 23
          - ((10 / 17) : ℂ) * ζ ^ 24
          + ((10 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry06_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (6 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (6 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((13 / 34) : ℂ)
          + ((13 / 34) : ℂ) * ζ ^ 4
          - ((9 / 34) : ℂ) * ζ ^ 5
          - ((13 / 34) : ℂ) * ζ ^ 8
          + ((9 / 34) : ℂ) * ζ ^ 9
          - ((9 / 34) : ℂ) * ζ ^ 13
          + ((19 / 34) : ℂ) * ζ ^ 15
          - ((19 / 34) : ℂ) * ζ ^ 19
          - ((13 / 34) : ℂ) * ζ ^ 20
          + ((19 / 34) : ℂ) * ζ ^ 23
          + ((13 / 34) : ℂ) * ζ ^ 24
          - ((13 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((13 / 34) : ℂ)
          + ((13 / 34) : ℂ) * ζ ^ 4
          - ((9 / 34) : ℂ) * ζ ^ 5
          - ((13 / 34) : ℂ) * ζ ^ 8
          + ((9 / 34) : ℂ) * ζ ^ 9
          - ((9 / 34) : ℂ) * ζ ^ 13
          + ((19 / 34) : ℂ) * ζ ^ 15
          - ((19 / 34) : ℂ) * ζ ^ 19
          - ((13 / 34) : ℂ) * ζ ^ 20
          + ((19 / 34) : ℂ) * ζ ^ 23
          + ((13 / 34) : ℂ) * ζ ^ 24
          - ((13 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry06_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (6 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (6 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((16 / 17) : ℂ)
          + ((16 / 17) : ℂ) * ζ ^ 4
          - ((15 / 17) : ℂ) * ζ ^ 5
          - ((16 / 17) : ℂ) * ζ ^ 8
          + ((15 / 17) : ℂ) * ζ ^ 9
          - ((15 / 17) : ℂ) * ζ ^ 13
          - ((8 / 17) : ℂ) * ζ ^ 15
          + ((8 / 17) : ℂ) * ζ ^ 19
          - ((16 / 17) : ℂ) * ζ ^ 20
          - ((8 / 17) : ℂ) * ζ ^ 23
          + ((16 / 17) : ℂ) * ζ ^ 24
          - ((16 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((16 / 17) : ℂ)
          + ((16 / 17) : ℂ) * ζ ^ 4
          - ((15 / 17) : ℂ) * ζ ^ 5
          - ((16 / 17) : ℂ) * ζ ^ 8
          + ((15 / 17) : ℂ) * ζ ^ 9
          - ((15 / 17) : ℂ) * ζ ^ 13
          - ((8 / 17) : ℂ) * ζ ^ 15
          + ((8 / 17) : ℂ) * ζ ^ 19
          - ((16 / 17) : ℂ) * ζ ^ 20
          - ((8 / 17) : ℂ) * ζ ^ 23
          + ((16 / 17) : ℂ) * ζ ^ 24
          - ((16 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry06_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (6 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (6 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((3 / 17) : ℂ)
          + ((3 / 17) : ℂ) * ζ ^ 4
          - ((6 / 17) : ℂ) * ζ ^ 5
          - ((3 / 17) : ℂ) * ζ ^ 8
          + ((6 / 17) : ℂ) * ζ ^ 9
          - ((6 / 17) : ℂ) * ζ ^ 13
          + ((7 / 17) : ℂ) * ζ ^ 15
          - ((7 / 17) : ℂ) * ζ ^ 19
          - ((3 / 17) : ℂ) * ζ ^ 20
          + ((7 / 17) : ℂ) * ζ ^ 23
          + ((3 / 17) : ℂ) * ζ ^ 24
          - ((3 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((3 / 17) : ℂ)
          + ((3 / 17) : ℂ) * ζ ^ 4
          - ((6 / 17) : ℂ) * ζ ^ 5
          - ((3 / 17) : ℂ) * ζ ^ 8
          + ((6 / 17) : ℂ) * ζ ^ 9
          - ((6 / 17) : ℂ) * ζ ^ 13
          + ((7 / 17) : ℂ) * ζ ^ 15
          - ((7 / 17) : ℂ) * ζ ^ 19
          - ((3 / 17) : ℂ) * ζ ^ 20
          + ((7 / 17) : ℂ) * ζ ^ 23
          + ((3 / 17) : ℂ) * ζ ^ 24
          - ((3 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry06_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (6 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (6 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
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
private theorem alternatingSixAmbientRow24_longPrefix77_entry06_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (6 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (6 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
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
private theorem alternatingSixAmbientRow24_longPrefix77_entry07_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (7 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (7 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((15 / 34) : ℂ)
          + ((15 / 34) : ℂ) * ζ ^ 4
          + ((21 / 34) : ℂ) * ζ ^ 5
          - ((15 / 34) : ℂ) * ζ ^ 8
          - ((21 / 34) : ℂ) * ζ ^ 9
          + ((21 / 34) : ℂ) * ζ ^ 13
          + ((1 / 34) : ℂ) * ζ ^ 15
          - ((1 / 34) : ℂ) * ζ ^ 19
          - ((15 / 34) : ℂ) * ζ ^ 20
          + ((1 / 34) : ℂ) * ζ ^ 23
          + ((15 / 34) : ℂ) * ζ ^ 24
          - ((15 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((15 / 34) : ℂ)
          + ((15 / 34) : ℂ) * ζ ^ 4
          + ((21 / 34) : ℂ) * ζ ^ 5
          - ((15 / 34) : ℂ) * ζ ^ 8
          - ((21 / 34) : ℂ) * ζ ^ 9
          + ((21 / 34) : ℂ) * ζ ^ 13
          + ((1 / 34) : ℂ) * ζ ^ 15
          - ((1 / 34) : ℂ) * ζ ^ 19
          - ((15 / 34) : ℂ) * ζ ^ 20
          + ((1 / 34) : ℂ) * ζ ^ 23
          + ((15 / 34) : ℂ) * ζ ^ 24
          - ((15 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry07_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (7 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (7 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((4 / 17) : ℂ)
          + ((4 / 17) : ℂ) * ζ ^ 4
          - ((8 / 17) : ℂ) * ζ ^ 5
          - ((4 / 17) : ℂ) * ζ ^ 8
          + ((8 / 17) : ℂ) * ζ ^ 9
          - ((8 / 17) : ℂ) * ζ ^ 13
          - ((2 / 17) : ℂ) * ζ ^ 15
          + ((2 / 17) : ℂ) * ζ ^ 19
          - ((4 / 17) : ℂ) * ζ ^ 20
          - ((2 / 17) : ℂ) * ζ ^ 23
          + ((4 / 17) : ℂ) * ζ ^ 24
          - ((4 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((4 / 17) : ℂ)
          + ((4 / 17) : ℂ) * ζ ^ 4
          - ((8 / 17) : ℂ) * ζ ^ 5
          - ((4 / 17) : ℂ) * ζ ^ 8
          + ((8 / 17) : ℂ) * ζ ^ 9
          - ((8 / 17) : ℂ) * ζ ^ 13
          - ((2 / 17) : ℂ) * ζ ^ 15
          + ((2 / 17) : ℂ) * ζ ^ 19
          - ((4 / 17) : ℂ) * ζ ^ 20
          - ((2 / 17) : ℂ) * ζ ^ 23
          + ((4 / 17) : ℂ) * ζ ^ 24
          - ((4 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry07_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (7 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (7 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((11 / 17) : ℂ)
          - ((11 / 17) : ℂ) * ζ ^ 4
          - ((12 / 17) : ℂ) * ζ ^ 5
          + ((11 / 17) : ℂ) * ζ ^ 8
          + ((12 / 17) : ℂ) * ζ ^ 9
          - ((12 / 17) : ℂ) * ζ ^ 13
          - ((20 / 17) : ℂ) * ζ ^ 15
          + ((20 / 17) : ℂ) * ζ ^ 19
          + ((11 / 17) : ℂ) * ζ ^ 20
          - ((20 / 17) : ℂ) * ζ ^ 23
          - ((11 / 17) : ℂ) * ζ ^ 24
          + ((11 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((11 / 17) : ℂ)
          - ((11 / 17) : ℂ) * ζ ^ 4
          - ((12 / 17) : ℂ) * ζ ^ 5
          + ((11 / 17) : ℂ) * ζ ^ 8
          + ((12 / 17) : ℂ) * ζ ^ 9
          - ((12 / 17) : ℂ) * ζ ^ 13
          - ((20 / 17) : ℂ) * ζ ^ 15
          + ((20 / 17) : ℂ) * ζ ^ 19
          + ((11 / 17) : ℂ) * ζ ^ 20
          - ((20 / 17) : ℂ) * ζ ^ 23
          - ((11 / 17) : ℂ) * ζ ^ 24
          + ((11 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry07_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (7 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (7 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((29 / 34) : ℂ)
          - ((29 / 34) : ℂ) * ζ ^ 4
          + ((7 / 34) : ℂ) * ζ ^ 5
          + ((29 / 34) : ℂ) * ζ ^ 8
          - ((7 / 34) : ℂ) * ζ ^ 9
          + ((7 / 34) : ℂ) * ζ ^ 13
          - ((45 / 34) : ℂ) * ζ ^ 15
          + ((45 / 34) : ℂ) * ζ ^ 19
          + ((29 / 34) : ℂ) * ζ ^ 20
          - ((45 / 34) : ℂ) * ζ ^ 23
          - ((29 / 34) : ℂ) * ζ ^ 24
          + ((29 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((29 / 34) : ℂ)
          - ((29 / 34) : ℂ) * ζ ^ 4
          + ((7 / 34) : ℂ) * ζ ^ 5
          + ((29 / 34) : ℂ) * ζ ^ 8
          - ((7 / 34) : ℂ) * ζ ^ 9
          + ((7 / 34) : ℂ) * ζ ^ 13
          - ((45 / 34) : ℂ) * ζ ^ 15
          + ((45 / 34) : ℂ) * ζ ^ 19
          + ((29 / 34) : ℂ) * ζ ^ 20
          - ((45 / 34) : ℂ) * ζ ^ 23
          - ((29 / 34) : ℂ) * ζ ^ 24
          + ((29 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry07_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (7 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (7 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
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
          - ((1 / 17) : ℂ) * ζ ^ 20
          - ((9 / 17) : ℂ) * ζ ^ 23
          + ((1 / 17) : ℂ) * ζ ^ 24
          - ((1 / 17) : ℂ) * ζ ^ 28
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
private theorem alternatingSixAmbientRow24_longPrefix77_entry07_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (7 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (7 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((31 / 34) : ℂ)
          + ((31 / 34) : ℂ) * ζ ^ 4
          - ((11 / 34) : ℂ) * ζ ^ 5
          - ((31 / 34) : ℂ) * ζ ^ 8
          + ((11 / 34) : ℂ) * ζ ^ 9
          - ((11 / 34) : ℂ) * ζ ^ 13
          + ((27 / 34) : ℂ) * ζ ^ 15
          - ((27 / 34) : ℂ) * ζ ^ 19
          - ((31 / 34) : ℂ) * ζ ^ 20
          + ((27 / 34) : ℂ) * ζ ^ 23
          + ((31 / 34) : ℂ) * ζ ^ 24
          - ((31 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((31 / 34) : ℂ)
          + ((31 / 34) : ℂ) * ζ ^ 4
          - ((11 / 34) : ℂ) * ζ ^ 5
          - ((31 / 34) : ℂ) * ζ ^ 8
          + ((11 / 34) : ℂ) * ζ ^ 9
          - ((11 / 34) : ℂ) * ζ ^ 13
          + ((27 / 34) : ℂ) * ζ ^ 15
          - ((27 / 34) : ℂ) * ζ ^ 19
          - ((31 / 34) : ℂ) * ζ ^ 20
          + ((27 / 34) : ℂ) * ζ ^ 23
          + ((31 / 34) : ℂ) * ζ ^ 24
          - ((31 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry07_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (7 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (7 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((12 / 17) : ℂ)
          + ((12 / 17) : ℂ) * ζ ^ 4
          - ((7 / 17) : ℂ) * ζ ^ 5
          - ((12 / 17) : ℂ) * ζ ^ 8
          + ((7 / 17) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 13
          + ((11 / 17) : ℂ) * ζ ^ 15
          - ((11 / 17) : ℂ) * ζ ^ 19
          - ((12 / 17) : ℂ) * ζ ^ 20
          + ((11 / 17) : ℂ) * ζ ^ 23
          + ((12 / 17) : ℂ) * ζ ^ 24
          - ((12 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((12 / 17) : ℂ)
          + ((12 / 17) : ℂ) * ζ ^ 4
          - ((7 / 17) : ℂ) * ζ ^ 5
          - ((12 / 17) : ℂ) * ζ ^ 8
          + ((7 / 17) : ℂ) * ζ ^ 9
          - ((7 / 17) : ℂ) * ζ ^ 13
          + ((11 / 17) : ℂ) * ζ ^ 15
          - ((11 / 17) : ℂ) * ζ ^ 19
          - ((12 / 17) : ℂ) * ζ ^ 20
          + ((11 / 17) : ℂ) * ζ ^ 23
          + ((12 / 17) : ℂ) * ζ ^ 24
          - ((12 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry07_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (7 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (7 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 17) : ℂ)
          - ((2 / 17) : ℂ) * ζ ^ 4
          + ((4 / 17) : ℂ) * ζ ^ 5
          + ((2 / 17) : ℂ) * ζ ^ 8
          - ((4 / 17) : ℂ) * ζ ^ 9
          + ((4 / 17) : ℂ) * ζ ^ 13
          + ((1 / 17) : ℂ) * ζ ^ 15
          - ((1 / 17) : ℂ) * ζ ^ 19
          + ((2 / 17) : ℂ) * ζ ^ 20
          + ((1 / 17) : ℂ) * ζ ^ 23
          - ((2 / 17) : ℂ) * ζ ^ 24
          + ((2 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 17) : ℂ)
          - ((2 / 17) : ℂ) * ζ ^ 4
          + ((4 / 17) : ℂ) * ζ ^ 5
          + ((2 / 17) : ℂ) * ζ ^ 8
          - ((4 / 17) : ℂ) * ζ ^ 9
          + ((4 / 17) : ℂ) * ζ ^ 13
          + ((1 / 17) : ℂ) * ζ ^ 15
          - ((1 / 17) : ℂ) * ζ ^ 19
          + ((2 / 17) : ℂ) * ζ ^ 20
          + ((1 / 17) : ℂ) * ζ ^ 23
          - ((2 / 17) : ℂ) * ζ ^ 24
          + ((2 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry07_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (7 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (7 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((8 / 17) : ℂ)
          + ((8 / 17) : ℂ) * ζ ^ 4
          + ((18 / 17) : ℂ) * ζ ^ 5
          - ((8 / 17) : ℂ) * ζ ^ 8
          - ((18 / 17) : ℂ) * ζ ^ 9
          + ((18 / 17) : ℂ) * ζ ^ 13
          - ((4 / 17) : ℂ) * ζ ^ 15
          + ((4 / 17) : ℂ) * ζ ^ 19
          - ((8 / 17) : ℂ) * ζ ^ 20
          - ((4 / 17) : ℂ) * ζ ^ 23
          + ((8 / 17) : ℂ) * ζ ^ 24
          - ((8 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((8 / 17) : ℂ)
          + ((8 / 17) : ℂ) * ζ ^ 4
          + ((18 / 17) : ℂ) * ζ ^ 5
          - ((8 / 17) : ℂ) * ζ ^ 8
          - ((18 / 17) : ℂ) * ζ ^ 9
          + ((18 / 17) : ℂ) * ζ ^ 13
          - ((4 / 17) : ℂ) * ζ ^ 15
          + ((4 / 17) : ℂ) * ζ ^ 19
          - ((8 / 17) : ℂ) * ζ ^ 20
          - ((4 / 17) : ℂ) * ζ ^ 23
          + ((8 / 17) : ℂ) * ζ ^ 24
          - ((8 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry07_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (7 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (7 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
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
          - ((1 / 2) : ℂ) * ζ ^ 15
          + ((1 / 2) : ℂ) * ζ ^ 19
          + ((1 / 2) : ℂ) * ζ ^ 20
          - ((1 / 2) : ℂ) * ζ ^ 23
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
          - ((1 / 2) : ℂ) * ζ ^ 15
          + ((1 / 2) : ℂ) * ζ ^ 19
          + ((1 / 2) : ℂ) * ζ ^ 20
          - ((1 / 2) : ℂ) * ζ ^ 23
          - ((1 / 2) : ℂ) * ζ ^ 24
          + ((1 / 2) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry08_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (8 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (8 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((31 / 34) : ℂ)
          - ((31 / 34) : ℂ) * ζ ^ 4
          + ((49 / 17) : ℂ) * ζ ^ 5
          + ((31 / 34) : ℂ) * ζ ^ 8
          - ((49 / 17) : ℂ) * ζ ^ 9
          + ((55 / 34) : ℂ) * ζ ^ 10
          + ((49 / 17) : ℂ) * ζ ^ 13
          - ((55 / 34) : ℂ) * ζ ^ 14
          - ((1 / 34) : ℂ) * ζ ^ 15
          + ((55 / 34) : ℂ) * ζ ^ 18
          + ((1 / 34) : ℂ) * ζ ^ 19
          + ((42 / 17) : ℂ) * ζ ^ 20
          - ((1 / 34) : ℂ) * ζ ^ 23
          - ((42 / 17) : ℂ) * ζ ^ 24
          + ((42 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((31 / 34) : ℂ)
          - ((31 / 34) : ℂ) * ζ ^ 4
          + ((49 / 17) : ℂ) * ζ ^ 5
          + ((31 / 34) : ℂ) * ζ ^ 8
          - ((49 / 17) : ℂ) * ζ ^ 9
          + ((55 / 34) : ℂ) * ζ ^ 10
          + ((49 / 17) : ℂ) * ζ ^ 13
          - ((55 / 34) : ℂ) * ζ ^ 14
          - ((1 / 34) : ℂ) * ζ ^ 15
          + ((55 / 34) : ℂ) * ζ ^ 18
          + ((1 / 34) : ℂ) * ζ ^ 19
          + ((42 / 17) : ℂ) * ζ ^ 20
          - ((1 / 34) : ℂ) * ζ ^ 23
          - ((42 / 17) : ℂ) * ζ ^ 24
          + ((42 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry08_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (8 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (8 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((30 / 17) : ℂ)
          + ((30 / 17) : ℂ) * ζ ^ 4
          - ((40 / 17) : ℂ) * ζ ^ 5
          - ((30 / 17) : ℂ) * ζ ^ 8
          + ((40 / 17) : ℂ) * ζ ^ 9
          + ((6 / 17) : ℂ) * ζ ^ 10
          - ((40 / 17) : ℂ) * ζ ^ 13
          - ((6 / 17) : ℂ) * ζ ^ 14
          - ((37 / 17) : ℂ) * ζ ^ 15
          + ((6 / 17) : ℂ) * ζ ^ 18
          + ((37 / 17) : ℂ) * ζ ^ 19
          + ((4 / 17) : ℂ) * ζ ^ 20
          - ((37 / 17) : ℂ) * ζ ^ 23
          - ((4 / 17) : ℂ) * ζ ^ 24
          + ((4 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((30 / 17) : ℂ)
          + ((30 / 17) : ℂ) * ζ ^ 4
          - ((40 / 17) : ℂ) * ζ ^ 5
          - ((30 / 17) : ℂ) * ζ ^ 8
          + ((40 / 17) : ℂ) * ζ ^ 9
          + ((6 / 17) : ℂ) * ζ ^ 10
          - ((40 / 17) : ℂ) * ζ ^ 13
          - ((6 / 17) : ℂ) * ζ ^ 14
          - ((37 / 17) : ℂ) * ζ ^ 15
          + ((6 / 17) : ℂ) * ζ ^ 18
          + ((37 / 17) : ℂ) * ζ ^ 19
          + ((4 / 17) : ℂ) * ζ ^ 20
          - ((37 / 17) : ℂ) * ζ ^ 23
          - ((4 / 17) : ℂ) * ζ ^ 24
          + ((4 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry08_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (8 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (8 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((61 / 17) : ℂ)
          + ((61 / 17) : ℂ) * ζ ^ 4
          - ((3 / 17) : ℂ) * ζ ^ 5
          - ((61 / 17) : ℂ) * ζ ^ 8
          + ((3 / 17) : ℂ) * ζ ^ 9
          - ((3 / 17) : ℂ) * ζ ^ 13
          - ((52 / 17) : ℂ) * ζ ^ 15
          + ((52 / 17) : ℂ) * ζ ^ 19
          - ((19 / 17) : ℂ) * ζ ^ 20
          - ((52 / 17) : ℂ) * ζ ^ 23
          + ((19 / 17) : ℂ) * ζ ^ 24
          - ((19 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((61 / 17) : ℂ)
          + ((61 / 17) : ℂ) * ζ ^ 4
          - ((3 / 17) : ℂ) * ζ ^ 5
          - ((61 / 17) : ℂ) * ζ ^ 8
          + ((3 / 17) : ℂ) * ζ ^ 9
          - ((3 / 17) : ℂ) * ζ ^ 13
          - ((52 / 17) : ℂ) * ζ ^ 15
          + ((52 / 17) : ℂ) * ζ ^ 19
          - ((19 / 17) : ℂ) * ζ ^ 20
          - ((52 / 17) : ℂ) * ζ ^ 23
          + ((19 / 17) : ℂ) * ζ ^ 24
          - ((19 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry08_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (8 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (8 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((99 / 34) : ℂ)
          + ((99 / 34) : ℂ) * ζ ^ 4
          + ((22 / 17) : ℂ) * ζ ^ 5
          - ((99 / 34) : ℂ) * ζ ^ 8
          - ((22 / 17) : ℂ) * ζ ^ 9
          - ((77 / 34) : ℂ) * ζ ^ 10
          + ((22 / 17) : ℂ) * ζ ^ 13
          + ((77 / 34) : ℂ) * ζ ^ 14
          + ((95 / 34) : ℂ) * ζ ^ 15
          - ((77 / 34) : ℂ) * ζ ^ 18
          - ((95 / 34) : ℂ) * ζ ^ 19
          - ((74 / 17) : ℂ) * ζ ^ 20
          + ((95 / 34) : ℂ) * ζ ^ 23
          + ((74 / 17) : ℂ) * ζ ^ 24
          - ((74 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((99 / 34) : ℂ)
          + ((99 / 34) : ℂ) * ζ ^ 4
          + ((22 / 17) : ℂ) * ζ ^ 5
          - ((99 / 34) : ℂ) * ζ ^ 8
          - ((22 / 17) : ℂ) * ζ ^ 9
          - ((77 / 34) : ℂ) * ζ ^ 10
          + ((22 / 17) : ℂ) * ζ ^ 13
          + ((77 / 34) : ℂ) * ζ ^ 14
          + ((95 / 34) : ℂ) * ζ ^ 15
          - ((77 / 34) : ℂ) * ζ ^ 18
          - ((95 / 34) : ℂ) * ζ ^ 19
          - ((74 / 17) : ℂ) * ζ ^ 20
          + ((95 / 34) : ℂ) * ζ ^ 23
          + ((74 / 17) : ℂ) * ζ ^ 24
          - ((74 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry08_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (8 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (8 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((16 / 17) : ℂ)
          - ((16 / 17) : ℂ) * ζ ^ 4
          + ((12 / 17) : ℂ) * ζ ^ 5
          + ((16 / 17) : ℂ) * ζ ^ 8
          - ((12 / 17) : ℂ) * ζ ^ 9
          - ((40 / 17) : ℂ) * ζ ^ 10
          + ((12 / 17) : ℂ) * ζ ^ 13
          + ((40 / 17) : ℂ) * ζ ^ 14
          + ((84 / 17) : ℂ) * ζ ^ 15
          - ((40 / 17) : ℂ) * ζ ^ 18
          - ((84 / 17) : ℂ) * ζ ^ 19
          - ((63 / 17) : ℂ) * ζ ^ 20
          + ((84 / 17) : ℂ) * ζ ^ 23
          + ((63 / 17) : ℂ) * ζ ^ 24
          - ((63 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((16 / 17) : ℂ)
          - ((16 / 17) : ℂ) * ζ ^ 4
          + ((12 / 17) : ℂ) * ζ ^ 5
          + ((16 / 17) : ℂ) * ζ ^ 8
          - ((12 / 17) : ℂ) * ζ ^ 9
          - ((40 / 17) : ℂ) * ζ ^ 10
          + ((12 / 17) : ℂ) * ζ ^ 13
          + ((40 / 17) : ℂ) * ζ ^ 14
          + ((84 / 17) : ℂ) * ζ ^ 15
          - ((40 / 17) : ℂ) * ζ ^ 18
          - ((84 / 17) : ℂ) * ζ ^ 19
          - ((63 / 17) : ℂ) * ζ ^ 20
          + ((84 / 17) : ℂ) * ζ ^ 23
          + ((63 / 17) : ℂ) * ζ ^ 24
          - ((63 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry08_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (8 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (8 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((5 / 34) : ℂ)
          + ((5 / 34) : ℂ) * ζ ^ 4
          - ((78 / 17) : ℂ) * ζ ^ 5
          - ((5 / 34) : ℂ) * ζ ^ 8
          + ((78 / 17) : ℂ) * ζ ^ 9
          + ((31 / 34) : ℂ) * ζ ^ 10
          - ((78 / 17) : ℂ) * ζ ^ 13
          - ((31 / 34) : ℂ) * ζ ^ 14
          - ((127 / 34) : ℂ) * ζ ^ 15
          + ((31 / 34) : ℂ) * ζ ^ 18
          + ((127 / 34) : ℂ) * ζ ^ 19
          + ((32 / 17) : ℂ) * ζ ^ 20
          - ((127 / 34) : ℂ) * ζ ^ 23
          - ((32 / 17) : ℂ) * ζ ^ 24
          + ((32 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((5 / 34) : ℂ)
          + ((5 / 34) : ℂ) * ζ ^ 4
          - ((78 / 17) : ℂ) * ζ ^ 5
          - ((5 / 34) : ℂ) * ζ ^ 8
          + ((78 / 17) : ℂ) * ζ ^ 9
          + ((31 / 34) : ℂ) * ζ ^ 10
          - ((78 / 17) : ℂ) * ζ ^ 13
          - ((31 / 34) : ℂ) * ζ ^ 14
          - ((127 / 34) : ℂ) * ζ ^ 15
          + ((31 / 34) : ℂ) * ζ ^ 18
          + ((127 / 34) : ℂ) * ζ ^ 19
          + ((32 / 17) : ℂ) * ζ ^ 20
          - ((127 / 34) : ℂ) * ζ ^ 23
          - ((32 / 17) : ℂ) * ζ ^ 24
          + ((32 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry08_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (8 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (8 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((15 / 17) : ℂ)
          + ((15 / 17) : ℂ) * ζ ^ 4
          - ((105 / 17) : ℂ) * ζ ^ 5
          - ((15 / 17) : ℂ) * ζ ^ 8
          + ((105 / 17) : ℂ) * ζ ^ 9
          - ((14 / 17) : ℂ) * ζ ^ 10
          - ((105 / 17) : ℂ) * ζ ^ 13
          + ((14 / 17) : ℂ) * ζ ^ 14
          - ((66 / 17) : ℂ) * ζ ^ 15
          - ((14 / 17) : ℂ) * ζ ^ 18
          + ((66 / 17) : ℂ) * ζ ^ 19
          - ((42 / 17) : ℂ) * ζ ^ 20
          - ((66 / 17) : ℂ) * ζ ^ 23
          + ((42 / 17) : ℂ) * ζ ^ 24
          - ((42 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((15 / 17) : ℂ)
          + ((15 / 17) : ℂ) * ζ ^ 4
          - ((105 / 17) : ℂ) * ζ ^ 5
          - ((15 / 17) : ℂ) * ζ ^ 8
          + ((105 / 17) : ℂ) * ζ ^ 9
          - ((14 / 17) : ℂ) * ζ ^ 10
          - ((105 / 17) : ℂ) * ζ ^ 13
          + ((14 / 17) : ℂ) * ζ ^ 14
          - ((66 / 17) : ℂ) * ζ ^ 15
          - ((14 / 17) : ℂ) * ζ ^ 18
          + ((66 / 17) : ℂ) * ζ ^ 19
          - ((42 / 17) : ℂ) * ζ ^ 20
          - ((66 / 17) : ℂ) * ζ ^ 23
          + ((42 / 17) : ℂ) * ζ ^ 24
          - ((42 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry08_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (8 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (8 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((23 / 17) : ℂ)
          - ((23 / 17) : ℂ) * ζ ^ 4
          + ((70 / 17) : ℂ) * ζ ^ 5
          + ((23 / 17) : ℂ) * ζ ^ 8
          - ((70 / 17) : ℂ) * ζ ^ 9
          + ((14 / 17) : ℂ) * ζ ^ 10
          + ((70 / 17) : ℂ) * ζ ^ 13
          - ((14 / 17) : ℂ) * ζ ^ 14
          + ((14 / 17) : ℂ) * ζ ^ 15
          + ((14 / 17) : ℂ) * ζ ^ 18
          - ((14 / 17) : ℂ) * ζ ^ 19
          + ((40 / 17) : ℂ) * ζ ^ 20
          + ((14 / 17) : ℂ) * ζ ^ 23
          - ((40 / 17) : ℂ) * ζ ^ 24
          + ((40 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((23 / 17) : ℂ)
          - ((23 / 17) : ℂ) * ζ ^ 4
          + ((70 / 17) : ℂ) * ζ ^ 5
          + ((23 / 17) : ℂ) * ζ ^ 8
          - ((70 / 17) : ℂ) * ζ ^ 9
          + ((14 / 17) : ℂ) * ζ ^ 10
          + ((70 / 17) : ℂ) * ζ ^ 13
          - ((14 / 17) : ℂ) * ζ ^ 14
          + ((14 / 17) : ℂ) * ζ ^ 15
          + ((14 / 17) : ℂ) * ζ ^ 18
          - ((14 / 17) : ℂ) * ζ ^ 19
          + ((40 / 17) : ℂ) * ζ ^ 20
          + ((14 / 17) : ℂ) * ζ ^ 23
          - ((40 / 17) : ℂ) * ζ ^ 24
          + ((40 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry08_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (8 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (8 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(1 : ℂ)
          + ζ ^ 4
          - ((54 / 17) : ℂ) * ζ ^ 5
          - ζ ^ 8
          + ((54 / 17) : ℂ) * ζ ^ 9
          - ((40 / 17) : ℂ) * ζ ^ 10
          - ((54 / 17) : ℂ) * ζ ^ 13
          + ((40 / 17) : ℂ) * ζ ^ 14
          + ((62 / 17) : ℂ) * ζ ^ 15
          - ((40 / 17) : ℂ) * ζ ^ 18
          - ((62 / 17) : ℂ) * ζ ^ 19
          - ((90 / 17) : ℂ) * ζ ^ 20
          + ((62 / 17) : ℂ) * ζ ^ 23
          + ((90 / 17) : ℂ) * ζ ^ 24
          - ((90 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(1 : ℂ)
          + ζ ^ 4
          - ((54 / 17) : ℂ) * ζ ^ 5
          - ζ ^ 8
          + ((54 / 17) : ℂ) * ζ ^ 9
          - ((40 / 17) : ℂ) * ζ ^ 10
          - ((54 / 17) : ℂ) * ζ ^ 13
          + ((40 / 17) : ℂ) * ζ ^ 14
          + ((62 / 17) : ℂ) * ζ ^ 15
          - ((40 / 17) : ℂ) * ζ ^ 18
          - ((62 / 17) : ℂ) * ζ ^ 19
          - ((90 / 17) : ℂ) * ζ ^ 20
          + ((62 / 17) : ℂ) * ζ ^ 23
          + ((90 / 17) : ℂ) * ζ ^ 24
          - ((90 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry08_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (8 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (8 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((47 / 34) : ℂ)
          + ((47 / 34) : ℂ) * ζ ^ 4
          - ((1 / 17) : ℂ) * ζ ^ 5
          - ((47 / 34) : ℂ) * ζ ^ 8
          + ((1 / 17) : ℂ) * ζ ^ 9
          + ((31 / 34) : ℂ) * ζ ^ 10
          - ((1 / 17) : ℂ) * ζ ^ 13
          - ((31 / 34) : ℂ) * ζ ^ 14
          - ((115 / 34) : ℂ) * ζ ^ 15
          + ((31 / 34) : ℂ) * ζ ^ 18
          + ((115 / 34) : ℂ) * ζ ^ 19
          + ((10 / 17) : ℂ) * ζ ^ 20
          - ((115 / 34) : ℂ) * ζ ^ 23
          - ((10 / 17) : ℂ) * ζ ^ 24
          + ((10 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((47 / 34) : ℂ)
          + ((47 / 34) : ℂ) * ζ ^ 4
          - ((1 / 17) : ℂ) * ζ ^ 5
          - ((47 / 34) : ℂ) * ζ ^ 8
          + ((1 / 17) : ℂ) * ζ ^ 9
          + ((31 / 34) : ℂ) * ζ ^ 10
          - ((1 / 17) : ℂ) * ζ ^ 13
          - ((31 / 34) : ℂ) * ζ ^ 14
          - ((115 / 34) : ℂ) * ζ ^ 15
          + ((31 / 34) : ℂ) * ζ ^ 18
          + ((115 / 34) : ℂ) * ζ ^ 19
          + ((10 / 17) : ℂ) * ζ ^ 20
          - ((115 / 34) : ℂ) * ζ ^ 23
          - ((10 / 17) : ℂ) * ζ ^ 24
          + ((10 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry09_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (9 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (9 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((31 / 34) : ℂ)
          + ((31 / 34) : ℂ) * ζ ^ 4
          - ((45 / 34) : ℂ) * ζ ^ 5
          - ((31 / 34) : ℂ) * ζ ^ 8
          + ((45 / 34) : ℂ) * ζ ^ 9
          - ((45 / 34) : ℂ) * ζ ^ 13
          - ((7 / 34) : ℂ) * ζ ^ 15
          + ((7 / 34) : ℂ) * ζ ^ 19
          - ((31 / 34) : ℂ) * ζ ^ 20
          - ((7 / 34) : ℂ) * ζ ^ 23
          + ((31 / 34) : ℂ) * ζ ^ 24
          - ((31 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((31 / 34) : ℂ)
          + ((31 / 34) : ℂ) * ζ ^ 4
          - ((45 / 34) : ℂ) * ζ ^ 5
          - ((31 / 34) : ℂ) * ζ ^ 8
          + ((45 / 34) : ℂ) * ζ ^ 9
          - ((45 / 34) : ℂ) * ζ ^ 13
          - ((7 / 34) : ℂ) * ζ ^ 15
          + ((7 / 34) : ℂ) * ζ ^ 19
          - ((31 / 34) : ℂ) * ζ ^ 20
          - ((7 / 34) : ℂ) * ζ ^ 23
          + ((31 / 34) : ℂ) * ζ ^ 24
          - ((31 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry09_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (9 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (9 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((11 / 17) : ℂ)
          - ((11 / 17) : ℂ) * ζ ^ 4
          + ((5 / 17) : ℂ) * ζ ^ 5
          + ((11 / 17) : ℂ) * ζ ^ 8
          - ((5 / 17) : ℂ) * ζ ^ 9
          + ((5 / 17) : ℂ) * ζ ^ 13
          + ((14 / 17) : ℂ) * ζ ^ 15
          - ((14 / 17) : ℂ) * ζ ^ 19
          + ((11 / 17) : ℂ) * ζ ^ 20
          + ((14 / 17) : ℂ) * ζ ^ 23
          - ((11 / 17) : ℂ) * ζ ^ 24
          + ((11 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((11 / 17) : ℂ)
          - ((11 / 17) : ℂ) * ζ ^ 4
          + ((5 / 17) : ℂ) * ζ ^ 5
          + ((11 / 17) : ℂ) * ζ ^ 8
          - ((5 / 17) : ℂ) * ζ ^ 9
          + ((5 / 17) : ℂ) * ζ ^ 13
          + ((14 / 17) : ℂ) * ζ ^ 15
          - ((14 / 17) : ℂ) * ζ ^ 19
          + ((11 / 17) : ℂ) * ζ ^ 20
          + ((14 / 17) : ℂ) * ζ ^ 23
          - ((11 / 17) : ℂ) * ζ ^ 24
          + ((11 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry09_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (9 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (9 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((8 / 17) : ℂ)
          - ((8 / 17) : ℂ) * ζ ^ 4
          - ((18 / 17) : ℂ) * ζ ^ 5
          + ((8 / 17) : ℂ) * ζ ^ 8
          + ((18 / 17) : ℂ) * ζ ^ 9
          - ((18 / 17) : ℂ) * ζ ^ 13
          + ((38 / 17) : ℂ) * ζ ^ 15
          - ((38 / 17) : ℂ) * ζ ^ 19
          + ((8 / 17) : ℂ) * ζ ^ 20
          + ((38 / 17) : ℂ) * ζ ^ 23
          - ((8 / 17) : ℂ) * ζ ^ 24
          + ((8 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((8 / 17) : ℂ)
          - ((8 / 17) : ℂ) * ζ ^ 4
          - ((18 / 17) : ℂ) * ζ ^ 5
          + ((8 / 17) : ℂ) * ζ ^ 8
          + ((18 / 17) : ℂ) * ζ ^ 9
          - ((18 / 17) : ℂ) * ζ ^ 13
          + ((38 / 17) : ℂ) * ζ ^ 15
          - ((38 / 17) : ℂ) * ζ ^ 19
          + ((8 / 17) : ℂ) * ζ ^ 20
          + ((38 / 17) : ℂ) * ζ ^ 23
          - ((8 / 17) : ℂ) * ζ ^ 24
          + ((8 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry09_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (9 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (9 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((35 / 34) : ℂ)
          - ((35 / 34) : ℂ) * ζ ^ 4
          + ((19 / 34) : ℂ) * ζ ^ 5
          + ((35 / 34) : ℂ) * ζ ^ 8
          - ((19 / 34) : ℂ) * ζ ^ 9
          + ((19 / 34) : ℂ) * ζ ^ 13
          - ((25 / 34) : ℂ) * ζ ^ 15
          + ((25 / 34) : ℂ) * ζ ^ 19
          + ((35 / 34) : ℂ) * ζ ^ 20
          - ((25 / 34) : ℂ) * ζ ^ 23
          - ((35 / 34) : ℂ) * ζ ^ 24
          + ((35 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((35 / 34) : ℂ)
          - ((35 / 34) : ℂ) * ζ ^ 4
          + ((19 / 34) : ℂ) * ζ ^ 5
          + ((35 / 34) : ℂ) * ζ ^ 8
          - ((19 / 34) : ℂ) * ζ ^ 9
          + ((19 / 34) : ℂ) * ζ ^ 13
          - ((25 / 34) : ℂ) * ζ ^ 15
          + ((25 / 34) : ℂ) * ζ ^ 19
          + ((35 / 34) : ℂ) * ζ ^ 20
          - ((25 / 34) : ℂ) * ζ ^ 23
          - ((35 / 34) : ℂ) * ζ ^ 24
          + ((35 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry09_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (9 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (9 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
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
          - ((22 / 17) : ℂ) * ζ ^ 15
          + ((22 / 17) : ℂ) * ζ ^ 19
          + ((7 / 17) : ℂ) * ζ ^ 20
          - ((22 / 17) : ℂ) * ζ ^ 23
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
          - ((22 / 17) : ℂ) * ζ ^ 15
          + ((22 / 17) : ℂ) * ζ ^ 19
          + ((7 / 17) : ℂ) * ζ ^ 20
          - ((22 / 17) : ℂ) * ζ ^ 23
          - ((7 / 17) : ℂ) * ζ ^ 24
          + ((7 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry09_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (9 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (9 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((13 / 34) : ℂ)
          - ((13 / 34) : ℂ) * ζ ^ 4
          + ((9 / 34) : ℂ) * ζ ^ 5
          + ((13 / 34) : ℂ) * ζ ^ 8
          - ((9 / 34) : ℂ) * ζ ^ 9
          + ((9 / 34) : ℂ) * ζ ^ 13
          + ((49 / 34) : ℂ) * ζ ^ 15
          - ((49 / 34) : ℂ) * ζ ^ 19
          + ((13 / 34) : ℂ) * ζ ^ 20
          + ((49 / 34) : ℂ) * ζ ^ 23
          - ((13 / 34) : ℂ) * ζ ^ 24
          + ((13 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((13 / 34) : ℂ)
          - ((13 / 34) : ℂ) * ζ ^ 4
          + ((9 / 34) : ℂ) * ζ ^ 5
          + ((13 / 34) : ℂ) * ζ ^ 8
          - ((9 / 34) : ℂ) * ζ ^ 9
          + ((9 / 34) : ℂ) * ζ ^ 13
          + ((49 / 34) : ℂ) * ζ ^ 15
          - ((49 / 34) : ℂ) * ζ ^ 19
          + ((13 / 34) : ℂ) * ζ ^ 20
          + ((49 / 34) : ℂ) * ζ ^ 23
          - ((13 / 34) : ℂ) * ζ ^ 24
          + ((13 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry09_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (9 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (9 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((33 / 17) : ℂ)
          - ((33 / 17) : ℂ) * ζ ^ 4
          + ((32 / 17) : ℂ) * ζ ^ 5
          + ((33 / 17) : ℂ) * ζ ^ 8
          - ((32 / 17) : ℂ) * ζ ^ 9
          + ((32 / 17) : ℂ) * ζ ^ 13
          + ((25 / 17) : ℂ) * ζ ^ 15
          - ((25 / 17) : ℂ) * ζ ^ 19
          + ((33 / 17) : ℂ) * ζ ^ 20
          + ((25 / 17) : ℂ) * ζ ^ 23
          - ((33 / 17) : ℂ) * ζ ^ 24
          + ((33 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((33 / 17) : ℂ)
          - ((33 / 17) : ℂ) * ζ ^ 4
          + ((32 / 17) : ℂ) * ζ ^ 5
          + ((33 / 17) : ℂ) * ζ ^ 8
          - ((32 / 17) : ℂ) * ζ ^ 9
          + ((32 / 17) : ℂ) * ζ ^ 13
          + ((25 / 17) : ℂ) * ζ ^ 15
          - ((25 / 17) : ℂ) * ζ ^ 19
          + ((33 / 17) : ℂ) * ζ ^ 20
          + ((25 / 17) : ℂ) * ζ ^ 23
          - ((33 / 17) : ℂ) * ζ ^ 24
          + ((33 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry09_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (9 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (9 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((14 / 17) : ℂ)
          + ((14 / 17) : ℂ) * ζ ^ 4
          - ((11 / 17) : ℂ) * ζ ^ 5
          - ((14 / 17) : ℂ) * ζ ^ 8
          + ((11 / 17) : ℂ) * ζ ^ 9
          - ((11 / 17) : ℂ) * ζ ^ 13
          - ((7 / 17) : ℂ) * ζ ^ 15
          + ((7 / 17) : ℂ) * ζ ^ 19
          - ((14 / 17) : ℂ) * ζ ^ 20
          - ((7 / 17) : ℂ) * ζ ^ 23
          + ((14 / 17) : ℂ) * ζ ^ 24
          - ((14 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((14 / 17) : ℂ)
          + ((14 / 17) : ℂ) * ζ ^ 4
          - ((11 / 17) : ℂ) * ζ ^ 5
          - ((14 / 17) : ℂ) * ζ ^ 8
          + ((11 / 17) : ℂ) * ζ ^ 9
          - ((11 / 17) : ℂ) * ζ ^ 13
          - ((7 / 17) : ℂ) * ζ ^ 15
          + ((7 / 17) : ℂ) * ζ ^ 19
          - ((14 / 17) : ℂ) * ζ ^ 20
          - ((7 / 17) : ℂ) * ζ ^ 23
          + ((14 / 17) : ℂ) * ζ ^ 24
          - ((14 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry09_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (9 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (9 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((22 / 17) : ℂ)
          - ((22 / 17) : ℂ) * ζ ^ 4
          + ((10 / 17) : ℂ) * ζ ^ 5
          + ((22 / 17) : ℂ) * ζ ^ 8
          - ((10 / 17) : ℂ) * ζ ^ 9
          + ((10 / 17) : ℂ) * ζ ^ 13
          - ((6 / 17) : ℂ) * ζ ^ 15
          + ((6 / 17) : ℂ) * ζ ^ 19
          + ((22 / 17) : ℂ) * ζ ^ 20
          - ((6 / 17) : ℂ) * ζ ^ 23
          - ((22 / 17) : ℂ) * ζ ^ 24
          + ((22 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((22 / 17) : ℂ)
          - ((22 / 17) : ℂ) * ζ ^ 4
          + ((10 / 17) : ℂ) * ζ ^ 5
          + ((22 / 17) : ℂ) * ζ ^ 8
          - ((10 / 17) : ℂ) * ζ ^ 9
          + ((10 / 17) : ℂ) * ζ ^ 13
          - ((6 / 17) : ℂ) * ζ ^ 15
          + ((6 / 17) : ℂ) * ζ ^ 19
          + ((22 / 17) : ℂ) * ζ ^ 20
          - ((6 / 17) : ℂ) * ζ ^ 23
          - ((22 / 17) : ℂ) * ζ ^ 24
          + ((22 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix77_entry09_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABB)
          (9 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix77
        (9 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABB,
    alternatingSixAmbientRow24LongPrefix77,
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
          - ((1 / 2) : ℂ) * ζ ^ 5
          - ((1 / 2) : ℂ) * ζ ^ 8
          + ((1 / 2) : ℂ) * ζ ^ 9
          - ((1 / 2) : ℂ) * ζ ^ 13
          + ((1 / 2) : ℂ) * ζ ^ 15
          - ((1 / 2) : ℂ) * ζ ^ 19
          - ((1 / 2) : ℂ) * ζ ^ 20
          + ((1 / 2) : ℂ) * ζ ^ 23
          + ((1 / 2) : ℂ) * ζ ^ 24
          - ((1 / 2) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

theorem alternatingSixAmbientRow24_longPrefix77_mul :
    alternatingSixAmbientRow24LongMatrixAB *
        alternatingSixAmbientRow24LongMatrixABB =
      alternatingSixAmbientRow24LongPrefix77 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientRow24_longPrefix77_entry00_00
  · exact alternatingSixAmbientRow24_longPrefix77_entry00_01
  · exact alternatingSixAmbientRow24_longPrefix77_entry00_02
  · exact alternatingSixAmbientRow24_longPrefix77_entry00_03
  · exact alternatingSixAmbientRow24_longPrefix77_entry00_04
  · exact alternatingSixAmbientRow24_longPrefix77_entry00_05
  · exact alternatingSixAmbientRow24_longPrefix77_entry00_06
  · exact alternatingSixAmbientRow24_longPrefix77_entry00_07
  · exact alternatingSixAmbientRow24_longPrefix77_entry00_08
  · exact alternatingSixAmbientRow24_longPrefix77_entry00_09
  · exact alternatingSixAmbientRow24_longPrefix77_entry01_00
  · exact alternatingSixAmbientRow24_longPrefix77_entry01_01
  · exact alternatingSixAmbientRow24_longPrefix77_entry01_02
  · exact alternatingSixAmbientRow24_longPrefix77_entry01_03
  · exact alternatingSixAmbientRow24_longPrefix77_entry01_04
  · exact alternatingSixAmbientRow24_longPrefix77_entry01_05
  · exact alternatingSixAmbientRow24_longPrefix77_entry01_06
  · exact alternatingSixAmbientRow24_longPrefix77_entry01_07
  · exact alternatingSixAmbientRow24_longPrefix77_entry01_08
  · exact alternatingSixAmbientRow24_longPrefix77_entry01_09
  · exact alternatingSixAmbientRow24_longPrefix77_entry02_00
  · exact alternatingSixAmbientRow24_longPrefix77_entry02_01
  · exact alternatingSixAmbientRow24_longPrefix77_entry02_02
  · exact alternatingSixAmbientRow24_longPrefix77_entry02_03
  · exact alternatingSixAmbientRow24_longPrefix77_entry02_04
  · exact alternatingSixAmbientRow24_longPrefix77_entry02_05
  · exact alternatingSixAmbientRow24_longPrefix77_entry02_06
  · exact alternatingSixAmbientRow24_longPrefix77_entry02_07
  · exact alternatingSixAmbientRow24_longPrefix77_entry02_08
  · exact alternatingSixAmbientRow24_longPrefix77_entry02_09
  · exact alternatingSixAmbientRow24_longPrefix77_entry03_00
  · exact alternatingSixAmbientRow24_longPrefix77_entry03_01
  · exact alternatingSixAmbientRow24_longPrefix77_entry03_02
  · exact alternatingSixAmbientRow24_longPrefix77_entry03_03
  · exact alternatingSixAmbientRow24_longPrefix77_entry03_04
  · exact alternatingSixAmbientRow24_longPrefix77_entry03_05
  · exact alternatingSixAmbientRow24_longPrefix77_entry03_06
  · exact alternatingSixAmbientRow24_longPrefix77_entry03_07
  · exact alternatingSixAmbientRow24_longPrefix77_entry03_08
  · exact alternatingSixAmbientRow24_longPrefix77_entry03_09
  · exact alternatingSixAmbientRow24_longPrefix77_entry04_00
  · exact alternatingSixAmbientRow24_longPrefix77_entry04_01
  · exact alternatingSixAmbientRow24_longPrefix77_entry04_02
  · exact alternatingSixAmbientRow24_longPrefix77_entry04_03
  · exact alternatingSixAmbientRow24_longPrefix77_entry04_04
  · exact alternatingSixAmbientRow24_longPrefix77_entry04_05
  · exact alternatingSixAmbientRow24_longPrefix77_entry04_06
  · exact alternatingSixAmbientRow24_longPrefix77_entry04_07
  · exact alternatingSixAmbientRow24_longPrefix77_entry04_08
  · exact alternatingSixAmbientRow24_longPrefix77_entry04_09
  · exact alternatingSixAmbientRow24_longPrefix77_entry05_00
  · exact alternatingSixAmbientRow24_longPrefix77_entry05_01
  · exact alternatingSixAmbientRow24_longPrefix77_entry05_02
  · exact alternatingSixAmbientRow24_longPrefix77_entry05_03
  · exact alternatingSixAmbientRow24_longPrefix77_entry05_04
  · exact alternatingSixAmbientRow24_longPrefix77_entry05_05
  · exact alternatingSixAmbientRow24_longPrefix77_entry05_06
  · exact alternatingSixAmbientRow24_longPrefix77_entry05_07
  · exact alternatingSixAmbientRow24_longPrefix77_entry05_08
  · exact alternatingSixAmbientRow24_longPrefix77_entry05_09
  · exact alternatingSixAmbientRow24_longPrefix77_entry06_00
  · exact alternatingSixAmbientRow24_longPrefix77_entry06_01
  · exact alternatingSixAmbientRow24_longPrefix77_entry06_02
  · exact alternatingSixAmbientRow24_longPrefix77_entry06_03
  · exact alternatingSixAmbientRow24_longPrefix77_entry06_04
  · exact alternatingSixAmbientRow24_longPrefix77_entry06_05
  · exact alternatingSixAmbientRow24_longPrefix77_entry06_06
  · exact alternatingSixAmbientRow24_longPrefix77_entry06_07
  · exact alternatingSixAmbientRow24_longPrefix77_entry06_08
  · exact alternatingSixAmbientRow24_longPrefix77_entry06_09
  · exact alternatingSixAmbientRow24_longPrefix77_entry07_00
  · exact alternatingSixAmbientRow24_longPrefix77_entry07_01
  · exact alternatingSixAmbientRow24_longPrefix77_entry07_02
  · exact alternatingSixAmbientRow24_longPrefix77_entry07_03
  · exact alternatingSixAmbientRow24_longPrefix77_entry07_04
  · exact alternatingSixAmbientRow24_longPrefix77_entry07_05
  · exact alternatingSixAmbientRow24_longPrefix77_entry07_06
  · exact alternatingSixAmbientRow24_longPrefix77_entry07_07
  · exact alternatingSixAmbientRow24_longPrefix77_entry07_08
  · exact alternatingSixAmbientRow24_longPrefix77_entry07_09
  · exact alternatingSixAmbientRow24_longPrefix77_entry08_00
  · exact alternatingSixAmbientRow24_longPrefix77_entry08_01
  · exact alternatingSixAmbientRow24_longPrefix77_entry08_02
  · exact alternatingSixAmbientRow24_longPrefix77_entry08_03
  · exact alternatingSixAmbientRow24_longPrefix77_entry08_04
  · exact alternatingSixAmbientRow24_longPrefix77_entry08_05
  · exact alternatingSixAmbientRow24_longPrefix77_entry08_06
  · exact alternatingSixAmbientRow24_longPrefix77_entry08_07
  · exact alternatingSixAmbientRow24_longPrefix77_entry08_08
  · exact alternatingSixAmbientRow24_longPrefix77_entry08_09
  · exact alternatingSixAmbientRow24_longPrefix77_entry09_00
  · exact alternatingSixAmbientRow24_longPrefix77_entry09_01
  · exact alternatingSixAmbientRow24_longPrefix77_entry09_02
  · exact alternatingSixAmbientRow24_longPrefix77_entry09_03
  · exact alternatingSixAmbientRow24_longPrefix77_entry09_04
  · exact alternatingSixAmbientRow24_longPrefix77_entry09_05
  · exact alternatingSixAmbientRow24_longPrefix77_entry09_06
  · exact alternatingSixAmbientRow24_longPrefix77_entry09_07
  · exact alternatingSixAmbientRow24_longPrefix77_entry09_08
  · exact alternatingSixAmbientRow24_longPrefix77_entry09_09

end InductiveMcKay
end McKayConjecture
