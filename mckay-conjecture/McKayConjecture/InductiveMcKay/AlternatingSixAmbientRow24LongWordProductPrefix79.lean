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
private theorem alternatingSixAmbientRow24_longPrefix79_entry00_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (0 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (0 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((35 / 34) : ℂ)
          + ((35 / 34) : ℂ) * ζ ^ 4
          - ((20 / 17) : ℂ) * ζ ^ 5
          - ((35 / 34) : ℂ) * ζ ^ 8
          + ((20 / 17) : ℂ) * ζ ^ 9
          - ((25 / 34) : ℂ) * ζ ^ 10
          - ((20 / 17) : ℂ) * ζ ^ 13
          + ((25 / 34) : ℂ) * ζ ^ 14
          - ((25 / 34) : ℂ) * ζ ^ 18
          - ((19 / 34) : ℂ) * ζ ^ 20
          + ((19 / 34) : ℂ) * ζ ^ 24
          - ((19 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((35 / 34) : ℂ)
          + ((35 / 34) : ℂ) * ζ ^ 4
          - ((20 / 17) : ℂ) * ζ ^ 5
          - ((35 / 34) : ℂ) * ζ ^ 8
          + ((20 / 17) : ℂ) * ζ ^ 9
          - ((25 / 34) : ℂ) * ζ ^ 10
          - ((20 / 17) : ℂ) * ζ ^ 13
          + ((25 / 34) : ℂ) * ζ ^ 14
          - ((25 / 34) : ℂ) * ζ ^ 18
          - ((19 / 34) : ℂ) * ζ ^ 20
          + ((19 / 34) : ℂ) * ζ ^ 24
          - ((19 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry00_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (0 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (0 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((15 / 34) : ℂ)
          + ((15 / 34) : ℂ) * ζ ^ 4
          - ((65 / 34) : ℂ) * ζ ^ 5
          - ((15 / 34) : ℂ) * ζ ^ 8
          + ((65 / 34) : ℂ) * ζ ^ 9
          - ((18 / 17) : ℂ) * ζ ^ 10
          - ((65 / 34) : ℂ) * ζ ^ 13
          + ((18 / 17) : ℂ) * ζ ^ 14
          - ((9 / 17) : ℂ) * ζ ^ 15
          - ((18 / 17) : ℂ) * ζ ^ 18
          + ((9 / 17) : ℂ) * ζ ^ 19
          - ((31 / 17) : ℂ) * ζ ^ 20
          - ((9 / 17) : ℂ) * ζ ^ 23
          + ((31 / 17) : ℂ) * ζ ^ 24
          - ((31 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((15 / 34) : ℂ)
          + ((15 / 34) : ℂ) * ζ ^ 4
          - ((65 / 34) : ℂ) * ζ ^ 5
          - ((15 / 34) : ℂ) * ζ ^ 8
          + ((65 / 34) : ℂ) * ζ ^ 9
          - ((18 / 17) : ℂ) * ζ ^ 10
          - ((65 / 34) : ℂ) * ζ ^ 13
          + ((18 / 17) : ℂ) * ζ ^ 14
          - ((9 / 17) : ℂ) * ζ ^ 15
          - ((18 / 17) : ℂ) * ζ ^ 18
          + ((9 / 17) : ℂ) * ζ ^ 19
          - ((31 / 17) : ℂ) * ζ ^ 20
          - ((9 / 17) : ℂ) * ζ ^ 23
          + ((31 / 17) : ℂ) * ζ ^ 24
          - ((31 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry00_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (0 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (0 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((95 / 34) : ℂ)
          + ((95 / 34) : ℂ) * ζ ^ 4
          - ((117 / 34) : ℂ) * ζ ^ 5
          - ((95 / 34) : ℂ) * ζ ^ 8
          + ((117 / 34) : ℂ) * ζ ^ 9
          - ((63 / 17) : ℂ) * ζ ^ 10
          - ((117 / 34) : ℂ) * ζ ^ 13
          + ((63 / 17) : ℂ) * ζ ^ 14
          - ((105 / 17) : ℂ) * ζ ^ 15
          - ((63 / 17) : ℂ) * ζ ^ 18
          + ((105 / 17) : ℂ) * ζ ^ 19
          - ((43 / 17) : ℂ) * ζ ^ 20
          - ((105 / 17) : ℂ) * ζ ^ 23
          + ((43 / 17) : ℂ) * ζ ^ 24
          - ((43 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((95 / 34) : ℂ)
          + ((95 / 34) : ℂ) * ζ ^ 4
          - ((117 / 34) : ℂ) * ζ ^ 5
          - ((95 / 34) : ℂ) * ζ ^ 8
          + ((117 / 34) : ℂ) * ζ ^ 9
          - ((63 / 17) : ℂ) * ζ ^ 10
          - ((117 / 34) : ℂ) * ζ ^ 13
          + ((63 / 17) : ℂ) * ζ ^ 14
          - ((105 / 17) : ℂ) * ζ ^ 15
          - ((63 / 17) : ℂ) * ζ ^ 18
          + ((105 / 17) : ℂ) * ζ ^ 19
          - ((43 / 17) : ℂ) * ζ ^ 20
          - ((105 / 17) : ℂ) * ζ ^ 23
          + ((43 / 17) : ℂ) * ζ ^ 24
          - ((43 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry00_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (0 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (0 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((53 / 34) : ℂ)
          - ((53 / 34) : ℂ) * ζ ^ 4
          + ((55 / 34) : ℂ) * ζ ^ 5
          + ((53 / 34) : ℂ) * ζ ^ 8
          - ((55 / 34) : ℂ) * ζ ^ 9
          + ζ ^ 10
          + ((55 / 34) : ℂ) * ζ ^ 13
          - ζ ^ 14
          + ((21 / 17) : ℂ) * ζ ^ 15
          + ζ ^ 18
          - ((21 / 17) : ℂ) * ζ ^ 19
          + ((25 / 17) : ℂ) * ζ ^ 20
          + ((21 / 17) : ℂ) * ζ ^ 23
          - ((25 / 17) : ℂ) * ζ ^ 24
          + ((25 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((53 / 34) : ℂ)
          - ((53 / 34) : ℂ) * ζ ^ 4
          + ((55 / 34) : ℂ) * ζ ^ 5
          + ((53 / 34) : ℂ) * ζ ^ 8
          - ((55 / 34) : ℂ) * ζ ^ 9
          + ζ ^ 10
          + ((55 / 34) : ℂ) * ζ ^ 13
          - ζ ^ 14
          + ((21 / 17) : ℂ) * ζ ^ 15
          + ζ ^ 18
          - ((21 / 17) : ℂ) * ζ ^ 19
          + ((25 / 17) : ℂ) * ζ ^ 20
          + ((21 / 17) : ℂ) * ζ ^ 23
          - ((25 / 17) : ℂ) * ζ ^ 24
          + ((25 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry00_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (0 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (0 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((61 / 34) : ℂ)
          - ((61 / 34) : ℂ) * ζ ^ 4
          + ((71 / 17) : ℂ) * ζ ^ 5
          + ((61 / 34) : ℂ) * ζ ^ 8
          - ((71 / 17) : ℂ) * ζ ^ 9
          + ((125 / 34) : ℂ) * ζ ^ 10
          + ((71 / 17) : ℂ) * ζ ^ 13
          - ((125 / 34) : ℂ) * ζ ^ 14
          + ((35 / 17) : ℂ) * ζ ^ 15
          + ((125 / 34) : ℂ) * ζ ^ 18
          - ((35 / 17) : ℂ) * ζ ^ 19
          + ((65 / 34) : ℂ) * ζ ^ 20
          + ((35 / 17) : ℂ) * ζ ^ 23
          - ((65 / 34) : ℂ) * ζ ^ 24
          + ((65 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((61 / 34) : ℂ)
          - ((61 / 34) : ℂ) * ζ ^ 4
          + ((71 / 17) : ℂ) * ζ ^ 5
          + ((61 / 34) : ℂ) * ζ ^ 8
          - ((71 / 17) : ℂ) * ζ ^ 9
          + ((125 / 34) : ℂ) * ζ ^ 10
          + ((71 / 17) : ℂ) * ζ ^ 13
          - ((125 / 34) : ℂ) * ζ ^ 14
          + ((35 / 17) : ℂ) * ζ ^ 15
          + ((125 / 34) : ℂ) * ζ ^ 18
          - ((35 / 17) : ℂ) * ζ ^ 19
          + ((65 / 34) : ℂ) * ζ ^ 20
          + ((35 / 17) : ℂ) * ζ ^ 23
          - ((65 / 34) : ℂ) * ζ ^ 24
          + ((65 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry00_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (0 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (0 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((45 / 34) : ℂ)
          + ((45 / 34) : ℂ) * ζ ^ 4
          - (3 : ℂ) * ζ ^ 5
          - ((45 / 34) : ℂ) * ζ ^ 8
          + (3 : ℂ) * ζ ^ 9
          - ((75 / 34) : ℂ) * ζ ^ 10
          - (3 : ℂ) * ζ ^ 13
          + ((75 / 34) : ℂ) * ζ ^ 14
          - ((43 / 17) : ℂ) * ζ ^ 15
          - ((75 / 34) : ℂ) * ζ ^ 18
          + ((43 / 17) : ℂ) * ζ ^ 19
          - ((93 / 34) : ℂ) * ζ ^ 20
          - ((43 / 17) : ℂ) * ζ ^ 23
          + ((93 / 34) : ℂ) * ζ ^ 24
          - ((93 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((45 / 34) : ℂ)
          + ((45 / 34) : ℂ) * ζ ^ 4
          - (3 : ℂ) * ζ ^ 5
          - ((45 / 34) : ℂ) * ζ ^ 8
          + (3 : ℂ) * ζ ^ 9
          - ((75 / 34) : ℂ) * ζ ^ 10
          - (3 : ℂ) * ζ ^ 13
          + ((75 / 34) : ℂ) * ζ ^ 14
          - ((43 / 17) : ℂ) * ζ ^ 15
          - ((75 / 34) : ℂ) * ζ ^ 18
          + ((43 / 17) : ℂ) * ζ ^ 19
          - ((93 / 34) : ℂ) * ζ ^ 20
          - ((43 / 17) : ℂ) * ζ ^ 23
          + ((93 / 34) : ℂ) * ζ ^ 24
          - ((93 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry00_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (0 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (0 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((27 / 34) : ℂ)
          + ((27 / 34) : ℂ) * ζ ^ 4
          - (2 : ℂ) * ζ ^ 5
          - ((27 / 34) : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 9
          - ((79 / 34) : ℂ) * ζ ^ 10
          - (2 : ℂ) * ζ ^ 13
          + ((79 / 34) : ℂ) * ζ ^ 14
          - ((65 / 34) : ℂ) * ζ ^ 15
          - ((79 / 34) : ℂ) * ζ ^ 18
          + ((65 / 34) : ℂ) * ζ ^ 19
          - ((26 / 17) : ℂ) * ζ ^ 20
          - ((65 / 34) : ℂ) * ζ ^ 23
          + ((26 / 17) : ℂ) * ζ ^ 24
          - ((26 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((27 / 34) : ℂ)
          + ((27 / 34) : ℂ) * ζ ^ 4
          - (2 : ℂ) * ζ ^ 5
          - ((27 / 34) : ℂ) * ζ ^ 8
          + (2 : ℂ) * ζ ^ 9
          - ((79 / 34) : ℂ) * ζ ^ 10
          - (2 : ℂ) * ζ ^ 13
          + ((79 / 34) : ℂ) * ζ ^ 14
          - ((65 / 34) : ℂ) * ζ ^ 15
          - ((79 / 34) : ℂ) * ζ ^ 18
          + ((65 / 34) : ℂ) * ζ ^ 19
          - ((26 / 17) : ℂ) * ζ ^ 20
          - ((65 / 34) : ℂ) * ζ ^ 23
          + ((26 / 17) : ℂ) * ζ ^ 24
          - ((26 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry00_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (0 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (0 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((5 / 34) : ℂ)
          - ((5 / 34) : ℂ) * ζ ^ 4
          + ((18 / 17) : ℂ) * ζ ^ 5
          + ((5 / 34) : ℂ) * ζ ^ 8
          - ((18 / 17) : ℂ) * ζ ^ 9
          + ((1 / 34) : ℂ) * ζ ^ 10
          + ((18 / 17) : ℂ) * ζ ^ 13
          - ((1 / 34) : ℂ) * ζ ^ 14
          + ((35 / 17) : ℂ) * ζ ^ 15
          + ((1 / 34) : ℂ) * ζ ^ 18
          - ((35 / 17) : ℂ) * ζ ^ 19
          + ((3 / 2) : ℂ) * ζ ^ 20
          + ((35 / 17) : ℂ) * ζ ^ 23
          - ((3 / 2) : ℂ) * ζ ^ 24
          + ((3 / 2) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((5 / 34) : ℂ)
          - ((5 / 34) : ℂ) * ζ ^ 4
          + ((18 / 17) : ℂ) * ζ ^ 5
          + ((5 / 34) : ℂ) * ζ ^ 8
          - ((18 / 17) : ℂ) * ζ ^ 9
          + ((1 / 34) : ℂ) * ζ ^ 10
          + ((18 / 17) : ℂ) * ζ ^ 13
          - ((1 / 34) : ℂ) * ζ ^ 14
          + ((35 / 17) : ℂ) * ζ ^ 15
          + ((1 / 34) : ℂ) * ζ ^ 18
          - ((35 / 17) : ℂ) * ζ ^ 19
          + ((3 / 2) : ℂ) * ζ ^ 20
          + ((35 / 17) : ℂ) * ζ ^ 23
          - ((3 / 2) : ℂ) * ζ ^ 24
          + ((3 / 2) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry00_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (0 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (0 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((33 / 34) : ℂ)
          + ((33 / 34) : ℂ) * ζ ^ 4
          - ζ ^ 5
          - ((33 / 34) : ℂ) * ζ ^ 8
          + ζ ^ 9
          + ((13 / 34) : ℂ) * ζ ^ 10
          - ζ ^ 13
          - ((13 / 34) : ℂ) * ζ ^ 14
          - ((5 / 34) : ℂ) * ζ ^ 15
          + ((13 / 34) : ℂ) * ζ ^ 18
          + ((5 / 34) : ℂ) * ζ ^ 19
          - ((14 / 17) : ℂ) * ζ ^ 20
          - ((5 / 34) : ℂ) * ζ ^ 23
          + ((14 / 17) : ℂ) * ζ ^ 24
          - ((14 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((33 / 34) : ℂ)
          + ((33 / 34) : ℂ) * ζ ^ 4
          - ζ ^ 5
          - ((33 / 34) : ℂ) * ζ ^ 8
          + ζ ^ 9
          + ((13 / 34) : ℂ) * ζ ^ 10
          - ζ ^ 13
          - ((13 / 34) : ℂ) * ζ ^ 14
          - ((5 / 34) : ℂ) * ζ ^ 15
          + ((13 / 34) : ℂ) * ζ ^ 18
          + ((5 / 34) : ℂ) * ζ ^ 19
          - ((14 / 17) : ℂ) * ζ ^ 20
          - ((5 / 34) : ℂ) * ζ ^ 23
          + ((14 / 17) : ℂ) * ζ ^ 24
          - ((14 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry00_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (0 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (0 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((9 / 17) : ℂ)
          - ((9 / 17) : ℂ) * ζ ^ 4
          - ((4 / 17) : ℂ) * ζ ^ 5
          + ((9 / 17) : ℂ) * ζ ^ 8
          + ((4 / 17) : ℂ) * ζ ^ 9
          - ((27 / 17) : ℂ) * ζ ^ 10
          - ((4 / 17) : ℂ) * ζ ^ 13
          + ((27 / 17) : ℂ) * ζ ^ 14
          - ((33 / 34) : ℂ) * ζ ^ 15
          - ((27 / 17) : ℂ) * ζ ^ 18
          + ((33 / 34) : ℂ) * ζ ^ 19
          - ((3 / 34) : ℂ) * ζ ^ 20
          - ((33 / 34) : ℂ) * ζ ^ 23
          + ((3 / 34) : ℂ) * ζ ^ 24
          - ((3 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((9 / 17) : ℂ)
          - ((9 / 17) : ℂ) * ζ ^ 4
          - ((4 / 17) : ℂ) * ζ ^ 5
          + ((9 / 17) : ℂ) * ζ ^ 8
          + ((4 / 17) : ℂ) * ζ ^ 9
          - ((27 / 17) : ℂ) * ζ ^ 10
          - ((4 / 17) : ℂ) * ζ ^ 13
          + ((27 / 17) : ℂ) * ζ ^ 14
          - ((33 / 34) : ℂ) * ζ ^ 15
          - ((27 / 17) : ℂ) * ζ ^ 18
          + ((33 / 34) : ℂ) * ζ ^ 19
          - ((3 / 34) : ℂ) * ζ ^ 20
          - ((33 / 34) : ℂ) * ζ ^ 23
          + ((3 / 34) : ℂ) * ζ ^ 24
          - ((3 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry01_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (1 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (1 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((251 / 34) : ℂ)
          - ((251 / 34) : ℂ) * ζ ^ 4
          + ((199 / 17) : ℂ) * ζ ^ 5
          + ((251 / 34) : ℂ) * ζ ^ 8
          - ((199 / 17) : ℂ) * ζ ^ 9
          + ((149 / 34) : ℂ) * ζ ^ 10
          + ((199 / 17) : ℂ) * ζ ^ 13
          - ((149 / 34) : ℂ) * ζ ^ 14
          + ((309 / 34) : ℂ) * ζ ^ 15
          + ((149 / 34) : ℂ) * ζ ^ 18
          - ((309 / 34) : ℂ) * ζ ^ 19
          + ((164 / 17) : ℂ) * ζ ^ 20
          + ((309 / 34) : ℂ) * ζ ^ 23
          - ((164 / 17) : ℂ) * ζ ^ 24
          + ((164 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((251 / 34) : ℂ)
          - ((251 / 34) : ℂ) * ζ ^ 4
          + ((199 / 17) : ℂ) * ζ ^ 5
          + ((251 / 34) : ℂ) * ζ ^ 8
          - ((199 / 17) : ℂ) * ζ ^ 9
          + ((149 / 34) : ℂ) * ζ ^ 10
          + ((199 / 17) : ℂ) * ζ ^ 13
          - ((149 / 34) : ℂ) * ζ ^ 14
          + ((309 / 34) : ℂ) * ζ ^ 15
          + ((149 / 34) : ℂ) * ζ ^ 18
          - ((309 / 34) : ℂ) * ζ ^ 19
          + ((164 / 17) : ℂ) * ζ ^ 20
          + ((309 / 34) : ℂ) * ζ ^ 23
          - ((164 / 17) : ℂ) * ζ ^ 24
          + ((164 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry01_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (1 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (1 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((91 / 17) : ℂ)
          + ((91 / 17) : ℂ) * ζ ^ 4
          - ((76 / 17) : ℂ) * ζ ^ 5
          - ((91 / 17) : ℂ) * ζ ^ 8
          + ((76 / 17) : ℂ) * ζ ^ 9
          - ((60 / 17) : ℂ) * ζ ^ 10
          - ((76 / 17) : ℂ) * ζ ^ 13
          + ((60 / 17) : ℂ) * ζ ^ 14
          - ((81 / 17) : ℂ) * ζ ^ 15
          - ((60 / 17) : ℂ) * ζ ^ 18
          + ((81 / 17) : ℂ) * ζ ^ 19
          - ((24 / 17) : ℂ) * ζ ^ 20
          - ((81 / 17) : ℂ) * ζ ^ 23
          + ((24 / 17) : ℂ) * ζ ^ 24
          - ((24 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((91 / 17) : ℂ)
          + ((91 / 17) : ℂ) * ζ ^ 4
          - ((76 / 17) : ℂ) * ζ ^ 5
          - ((91 / 17) : ℂ) * ζ ^ 8
          + ((76 / 17) : ℂ) * ζ ^ 9
          - ((60 / 17) : ℂ) * ζ ^ 10
          - ((76 / 17) : ℂ) * ζ ^ 13
          + ((60 / 17) : ℂ) * ζ ^ 14
          - ((81 / 17) : ℂ) * ζ ^ 15
          - ((60 / 17) : ℂ) * ζ ^ 18
          + ((81 / 17) : ℂ) * ζ ^ 19
          - ((24 / 17) : ℂ) * ζ ^ 20
          - ((81 / 17) : ℂ) * ζ ^ 23
          + ((24 / 17) : ℂ) * ζ ^ 24
          - ((24 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry01_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (1 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (1 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 17) : ℂ)
          - ((2 / 17) : ℂ) * ζ ^ 4
          + ((47 / 17) : ℂ) * ζ ^ 5
          + ((2 / 17) : ℂ) * ζ ^ 8
          - ((47 / 17) : ℂ) * ζ ^ 9
          + ((86 / 17) : ℂ) * ζ ^ 10
          + ((47 / 17) : ℂ) * ζ ^ 13
          - ((86 / 17) : ℂ) * ζ ^ 14
          + (2 : ℂ) * ζ ^ 15
          + ((86 / 17) : ℂ) * ζ ^ 18
          - (2 : ℂ) * ζ ^ 19
          - ((4 / 17) : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 23
          + ((4 / 17) : ℂ) * ζ ^ 24
          - ((4 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 17) : ℂ)
          - ((2 / 17) : ℂ) * ζ ^ 4
          + ((47 / 17) : ℂ) * ζ ^ 5
          + ((2 / 17) : ℂ) * ζ ^ 8
          - ((47 / 17) : ℂ) * ζ ^ 9
          + ((86 / 17) : ℂ) * ζ ^ 10
          + ((47 / 17) : ℂ) * ζ ^ 13
          - ((86 / 17) : ℂ) * ζ ^ 14
          + (2 : ℂ) * ζ ^ 15
          + ((86 / 17) : ℂ) * ζ ^ 18
          - (2 : ℂ) * ζ ^ 19
          - ((4 / 17) : ℂ) * ζ ^ 20
          + (2 : ℂ) * ζ ^ 23
          + ((4 / 17) : ℂ) * ζ ^ 24
          - ((4 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry01_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (1 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (1 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((133 / 34) : ℂ)
          + ((133 / 34) : ℂ) * ζ ^ 4
          - ((141 / 17) : ℂ) * ζ ^ 5
          - ((133 / 34) : ℂ) * ζ ^ 8
          + ((141 / 17) : ℂ) * ζ ^ 9
          - ((49 / 34) : ℂ) * ζ ^ 10
          - ((141 / 17) : ℂ) * ζ ^ 13
          + ((49 / 34) : ℂ) * ζ ^ 14
          - ((91 / 34) : ℂ) * ζ ^ 15
          - ((49 / 34) : ℂ) * ζ ^ 18
          + ((91 / 34) : ℂ) * ζ ^ 19
          - ((78 / 17) : ℂ) * ζ ^ 20
          - ((91 / 34) : ℂ) * ζ ^ 23
          + ((78 / 17) : ℂ) * ζ ^ 24
          - ((78 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((133 / 34) : ℂ)
          + ((133 / 34) : ℂ) * ζ ^ 4
          - ((141 / 17) : ℂ) * ζ ^ 5
          - ((133 / 34) : ℂ) * ζ ^ 8
          + ((141 / 17) : ℂ) * ζ ^ 9
          - ((49 / 34) : ℂ) * ζ ^ 10
          - ((141 / 17) : ℂ) * ζ ^ 13
          + ((49 / 34) : ℂ) * ζ ^ 14
          - ((91 / 34) : ℂ) * ζ ^ 15
          - ((49 / 34) : ℂ) * ζ ^ 18
          + ((91 / 34) : ℂ) * ζ ^ 19
          - ((78 / 17) : ℂ) * ζ ^ 20
          - ((91 / 34) : ℂ) * ζ ^ 23
          + ((78 / 17) : ℂ) * ζ ^ 24
          - ((78 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry01_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (1 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (1 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((71 / 17) : ℂ)
          + ((71 / 17) : ℂ) * ζ ^ 4
          - ((165 / 17) : ℂ) * ζ ^ 5
          - ((71 / 17) : ℂ) * ζ ^ 8
          + ((165 / 17) : ℂ) * ζ ^ 9
          - ((12 / 17) : ℂ) * ζ ^ 10
          - ((165 / 17) : ℂ) * ζ ^ 13
          + ((12 / 17) : ℂ) * ζ ^ 14
          + ((4 / 17) : ℂ) * ζ ^ 15
          - ((12 / 17) : ℂ) * ζ ^ 18
          - ((4 / 17) : ℂ) * ζ ^ 19
          - ((97 / 17) : ℂ) * ζ ^ 20
          + ((4 / 17) : ℂ) * ζ ^ 23
          + ((97 / 17) : ℂ) * ζ ^ 24
          - ((97 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((71 / 17) : ℂ)
          + ((71 / 17) : ℂ) * ζ ^ 4
          - ((165 / 17) : ℂ) * ζ ^ 5
          - ((71 / 17) : ℂ) * ζ ^ 8
          + ((165 / 17) : ℂ) * ζ ^ 9
          - ((12 / 17) : ℂ) * ζ ^ 10
          - ((165 / 17) : ℂ) * ζ ^ 13
          + ((12 / 17) : ℂ) * ζ ^ 14
          + ((4 / 17) : ℂ) * ζ ^ 15
          - ((12 / 17) : ℂ) * ζ ^ 18
          - ((4 / 17) : ℂ) * ζ ^ 19
          - ((97 / 17) : ℂ) * ζ ^ 20
          + ((4 / 17) : ℂ) * ζ ^ 23
          + ((97 / 17) : ℂ) * ζ ^ 24
          - ((97 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry01_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (1 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (1 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((71 / 34) : ℂ)
          + ((71 / 34) : ℂ) * ζ ^ 4
          - ((4 / 17) : ℂ) * ζ ^ 5
          - ((71 / 34) : ℂ) * ζ ^ 8
          + ((4 / 17) : ℂ) * ζ ^ 9
          - ((89 / 34) : ℂ) * ζ ^ 10
          - ((4 / 17) : ℂ) * ζ ^ 13
          + ((89 / 34) : ℂ) * ζ ^ 14
          - ((137 / 34) : ℂ) * ζ ^ 15
          - ((89 / 34) : ℂ) * ζ ^ 18
          + ((137 / 34) : ℂ) * ζ ^ 19
          - ((44 / 17) : ℂ) * ζ ^ 20
          - ((137 / 34) : ℂ) * ζ ^ 23
          + ((44 / 17) : ℂ) * ζ ^ 24
          - ((44 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((71 / 34) : ℂ)
          + ((71 / 34) : ℂ) * ζ ^ 4
          - ((4 / 17) : ℂ) * ζ ^ 5
          - ((71 / 34) : ℂ) * ζ ^ 8
          + ((4 / 17) : ℂ) * ζ ^ 9
          - ((89 / 34) : ℂ) * ζ ^ 10
          - ((4 / 17) : ℂ) * ζ ^ 13
          + ((89 / 34) : ℂ) * ζ ^ 14
          - ((137 / 34) : ℂ) * ζ ^ 15
          - ((89 / 34) : ℂ) * ζ ^ 18
          + ((137 / 34) : ℂ) * ζ ^ 19
          - ((44 / 17) : ℂ) * ζ ^ 20
          - ((137 / 34) : ℂ) * ζ ^ 23
          + ((44 / 17) : ℂ) * ζ ^ 24
          - ((44 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry01_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (1 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (1 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((232 / 17) : ℂ)
          + ((232 / 17) : ℂ) * ζ ^ 4
          - ((274 / 17) : ℂ) * ζ ^ 5
          - ((232 / 17) : ℂ) * ζ ^ 8
          + ((274 / 17) : ℂ) * ζ ^ 9
          - ((215 / 17) : ℂ) * ζ ^ 10
          - ((274 / 17) : ℂ) * ζ ^ 13
          + ((215 / 17) : ℂ) * ζ ^ 14
          - ((371 / 17) : ℂ) * ζ ^ 15
          - ((215 / 17) : ℂ) * ζ ^ 18
          + ((371 / 17) : ℂ) * ζ ^ 19
          - ((256 / 17) : ℂ) * ζ ^ 20
          - ((371 / 17) : ℂ) * ζ ^ 23
          + ((256 / 17) : ℂ) * ζ ^ 24
          - ((256 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((232 / 17) : ℂ)
          + ((232 / 17) : ℂ) * ζ ^ 4
          - ((274 / 17) : ℂ) * ζ ^ 5
          - ((232 / 17) : ℂ) * ζ ^ 8
          + ((274 / 17) : ℂ) * ζ ^ 9
          - ((215 / 17) : ℂ) * ζ ^ 10
          - ((274 / 17) : ℂ) * ζ ^ 13
          + ((215 / 17) : ℂ) * ζ ^ 14
          - ((371 / 17) : ℂ) * ζ ^ 15
          - ((215 / 17) : ℂ) * ζ ^ 18
          + ((371 / 17) : ℂ) * ζ ^ 19
          - ((256 / 17) : ℂ) * ζ ^ 20
          - ((371 / 17) : ℂ) * ζ ^ 23
          + ((256 / 17) : ℂ) * ζ ^ 24
          - ((256 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry01_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (1 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (1 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((96 / 17) : ℂ)
          - ((96 / 17) : ℂ) * ζ ^ 4
          + ((156 / 17) : ℂ) * ζ ^ 5
          + ((96 / 17) : ℂ) * ζ ^ 8
          - ((156 / 17) : ℂ) * ζ ^ 9
          + ((81 / 17) : ℂ) * ζ ^ 10
          + ((156 / 17) : ℂ) * ζ ^ 13
          - ((81 / 17) : ℂ) * ζ ^ 14
          + (5 : ℂ) * ζ ^ 15
          + ((81 / 17) : ℂ) * ζ ^ 18
          - (5 : ℂ) * ζ ^ 19
          + ((84 / 17) : ℂ) * ζ ^ 20
          + (5 : ℂ) * ζ ^ 23
          - ((84 / 17) : ℂ) * ζ ^ 24
          + ((84 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((96 / 17) : ℂ)
          - ((96 / 17) : ℂ) * ζ ^ 4
          + ((156 / 17) : ℂ) * ζ ^ 5
          + ((96 / 17) : ℂ) * ζ ^ 8
          - ((156 / 17) : ℂ) * ζ ^ 9
          + ((81 / 17) : ℂ) * ζ ^ 10
          + ((156 / 17) : ℂ) * ζ ^ 13
          - ((81 / 17) : ℂ) * ζ ^ 14
          + (5 : ℂ) * ζ ^ 15
          + ((81 / 17) : ℂ) * ζ ^ 18
          - (5 : ℂ) * ζ ^ 19
          + ((84 / 17) : ℂ) * ζ ^ 20
          + (5 : ℂ) * ζ ^ 23
          - ((84 / 17) : ℂ) * ζ ^ 24
          + ((84 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry01_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (1 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (1 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((84 / 17) : ℂ)
          + ((84 / 17) : ℂ) * ζ ^ 4
          - ((160 / 17) : ℂ) * ζ ^ 5
          - ((84 / 17) : ℂ) * ζ ^ 8
          + ((160 / 17) : ℂ) * ζ ^ 9
          - ((103 / 17) : ℂ) * ζ ^ 10
          - ((160 / 17) : ℂ) * ζ ^ 13
          + ((103 / 17) : ℂ) * ζ ^ 14
          - ((115 / 17) : ℂ) * ζ ^ 15
          - ((103 / 17) : ℂ) * ζ ^ 18
          + ((115 / 17) : ℂ) * ζ ^ 19
          - ((73 / 17) : ℂ) * ζ ^ 20
          - ((115 / 17) : ℂ) * ζ ^ 23
          + ((73 / 17) : ℂ) * ζ ^ 24
          - ((73 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((84 / 17) : ℂ)
          + ((84 / 17) : ℂ) * ζ ^ 4
          - ((160 / 17) : ℂ) * ζ ^ 5
          - ((84 / 17) : ℂ) * ζ ^ 8
          + ((160 / 17) : ℂ) * ζ ^ 9
          - ((103 / 17) : ℂ) * ζ ^ 10
          - ((160 / 17) : ℂ) * ζ ^ 13
          + ((103 / 17) : ℂ) * ζ ^ 14
          - ((115 / 17) : ℂ) * ζ ^ 15
          - ((103 / 17) : ℂ) * ζ ^ 18
          + ((115 / 17) : ℂ) * ζ ^ 19
          - ((73 / 17) : ℂ) * ζ ^ 20
          - ((115 / 17) : ℂ) * ζ ^ 23
          + ((73 / 17) : ℂ) * ζ ^ 24
          - ((73 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry01_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (1 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (1 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((3 / 34) : ℂ)
          + ((3 / 34) : ℂ) * ζ ^ 4
          + ((80 / 17) : ℂ) * ζ ^ 5
          - ((3 / 34) : ℂ) * ζ ^ 8
          - ((80 / 17) : ℂ) * ζ ^ 9
          + ((111 / 34) : ℂ) * ζ ^ 10
          + ((80 / 17) : ℂ) * ζ ^ 13
          - ((111 / 34) : ℂ) * ζ ^ 14
          + ((65 / 34) : ℂ) * ζ ^ 15
          + ((111 / 34) : ℂ) * ζ ^ 18
          - ((65 / 34) : ℂ) * ζ ^ 19
          + ((30 / 17) : ℂ) * ζ ^ 20
          + ((65 / 34) : ℂ) * ζ ^ 23
          - ((30 / 17) : ℂ) * ζ ^ 24
          + ((30 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((3 / 34) : ℂ)
          + ((3 / 34) : ℂ) * ζ ^ 4
          + ((80 / 17) : ℂ) * ζ ^ 5
          - ((3 / 34) : ℂ) * ζ ^ 8
          - ((80 / 17) : ℂ) * ζ ^ 9
          + ((111 / 34) : ℂ) * ζ ^ 10
          + ((80 / 17) : ℂ) * ζ ^ 13
          - ((111 / 34) : ℂ) * ζ ^ 14
          + ((65 / 34) : ℂ) * ζ ^ 15
          + ((111 / 34) : ℂ) * ζ ^ 18
          - ((65 / 34) : ℂ) * ζ ^ 19
          + ((30 / 17) : ℂ) * ζ ^ 20
          + ((65 / 34) : ℂ) * ζ ^ 23
          - ((30 / 17) : ℂ) * ζ ^ 24
          + ((30 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry02_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (2 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (2 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((105 / 34) : ℂ)
          - ((105 / 34) : ℂ) * ζ ^ 4
          + ((167 / 34) : ℂ) * ζ ^ 5
          + ((105 / 34) : ℂ) * ζ ^ 8
          - ((167 / 34) : ℂ) * ζ ^ 9
          + ((59 / 17) : ℂ) * ζ ^ 10
          + ((167 / 34) : ℂ) * ζ ^ 13
          - ((59 / 17) : ℂ) * ζ ^ 14
          + ((55 / 17) : ℂ) * ζ ^ 15
          + ((59 / 17) : ℂ) * ζ ^ 18
          - ((55 / 17) : ℂ) * ζ ^ 19
          + ((78 / 17) : ℂ) * ζ ^ 20
          + ((55 / 17) : ℂ) * ζ ^ 23
          - ((78 / 17) : ℂ) * ζ ^ 24
          + ((78 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((105 / 34) : ℂ)
          - ((105 / 34) : ℂ) * ζ ^ 4
          + ((167 / 34) : ℂ) * ζ ^ 5
          + ((105 / 34) : ℂ) * ζ ^ 8
          - ((167 / 34) : ℂ) * ζ ^ 9
          + ((59 / 17) : ℂ) * ζ ^ 10
          + ((167 / 34) : ℂ) * ζ ^ 13
          - ((59 / 17) : ℂ) * ζ ^ 14
          + ((55 / 17) : ℂ) * ζ ^ 15
          + ((59 / 17) : ℂ) * ζ ^ 18
          - ((55 / 17) : ℂ) * ζ ^ 19
          + ((78 / 17) : ℂ) * ζ ^ 20
          + ((55 / 17) : ℂ) * ζ ^ 23
          - ((78 / 17) : ℂ) * ζ ^ 24
          + ((78 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry02_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (2 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (2 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((79 / 34) : ℂ)
          + ((79 / 34) : ℂ) * ζ ^ 4
          - ((71 / 34) : ℂ) * ζ ^ 5
          - ((79 / 34) : ℂ) * ζ ^ 8
          + ((71 / 34) : ℂ) * ζ ^ 9
          - ((32 / 17) : ℂ) * ζ ^ 10
          - ((71 / 34) : ℂ) * ζ ^ 13
          + ((32 / 17) : ℂ) * ζ ^ 14
          - ((37 / 17) : ℂ) * ζ ^ 15
          - ((32 / 17) : ℂ) * ζ ^ 18
          + ((37 / 17) : ℂ) * ζ ^ 19
          - ((14 / 17) : ℂ) * ζ ^ 20
          - ((37 / 17) : ℂ) * ζ ^ 23
          + ((14 / 17) : ℂ) * ζ ^ 24
          - ((14 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((79 / 34) : ℂ)
          + ((79 / 34) : ℂ) * ζ ^ 4
          - ((71 / 34) : ℂ) * ζ ^ 5
          - ((79 / 34) : ℂ) * ζ ^ 8
          + ((71 / 34) : ℂ) * ζ ^ 9
          - ((32 / 17) : ℂ) * ζ ^ 10
          - ((71 / 34) : ℂ) * ζ ^ 13
          + ((32 / 17) : ℂ) * ζ ^ 14
          - ((37 / 17) : ℂ) * ζ ^ 15
          - ((32 / 17) : ℂ) * ζ ^ 18
          + ((37 / 17) : ℂ) * ζ ^ 19
          - ((14 / 17) : ℂ) * ζ ^ 20
          - ((37 / 17) : ℂ) * ζ ^ 23
          + ((14 / 17) : ℂ) * ζ ^ 24
          - ((14 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry02_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (2 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (2 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((27 / 34) : ℂ)
          + ((27 / 34) : ℂ) * ζ ^ 4
          + ((69 / 34) : ℂ) * ζ ^ 5
          - ((27 / 34) : ℂ) * ζ ^ 8
          - ((69 / 34) : ℂ) * ζ ^ 9
          + ((38 / 17) : ℂ) * ζ ^ 10
          + ((69 / 34) : ℂ) * ζ ^ 13
          - ((38 / 17) : ℂ) * ζ ^ 14
          + ((71 / 17) : ℂ) * ζ ^ 15
          + ((38 / 17) : ℂ) * ζ ^ 18
          - ((71 / 17) : ℂ) * ζ ^ 19
          - ((27 / 17) : ℂ) * ζ ^ 20
          + ((71 / 17) : ℂ) * ζ ^ 23
          + ((27 / 17) : ℂ) * ζ ^ 24
          - ((27 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((27 / 34) : ℂ)
          + ((27 / 34) : ℂ) * ζ ^ 4
          + ((69 / 34) : ℂ) * ζ ^ 5
          - ((27 / 34) : ℂ) * ζ ^ 8
          - ((69 / 34) : ℂ) * ζ ^ 9
          + ((38 / 17) : ℂ) * ζ ^ 10
          + ((69 / 34) : ℂ) * ζ ^ 13
          - ((38 / 17) : ℂ) * ζ ^ 14
          + ((71 / 17) : ℂ) * ζ ^ 15
          + ((38 / 17) : ℂ) * ζ ^ 18
          - ((71 / 17) : ℂ) * ζ ^ 19
          - ((27 / 17) : ℂ) * ζ ^ 20
          + ((71 / 17) : ℂ) * ζ ^ 23
          + ((27 / 17) : ℂ) * ζ ^ 24
          - ((27 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry02_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (2 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (2 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((71 / 34) : ℂ)
          + ((71 / 34) : ℂ) * ζ ^ 4
          - ((53 / 17) : ℂ) * ζ ^ 5
          - ((71 / 34) : ℂ) * ζ ^ 8
          + ((53 / 17) : ℂ) * ζ ^ 9
          - ((81 / 34) : ℂ) * ζ ^ 10
          - ((53 / 17) : ℂ) * ζ ^ 13
          + ((81 / 34) : ℂ) * ζ ^ 14
          + ((5 / 17) : ℂ) * ζ ^ 15
          - ((81 / 34) : ℂ) * ζ ^ 18
          - ((5 / 17) : ℂ) * ζ ^ 19
          - ((81 / 34) : ℂ) * ζ ^ 20
          + ((5 / 17) : ℂ) * ζ ^ 23
          + ((81 / 34) : ℂ) * ζ ^ 24
          - ((81 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((71 / 34) : ℂ)
          + ((71 / 34) : ℂ) * ζ ^ 4
          - ((53 / 17) : ℂ) * ζ ^ 5
          - ((71 / 34) : ℂ) * ζ ^ 8
          + ((53 / 17) : ℂ) * ζ ^ 9
          - ((81 / 34) : ℂ) * ζ ^ 10
          - ((53 / 17) : ℂ) * ζ ^ 13
          + ((81 / 34) : ℂ) * ζ ^ 14
          + ((5 / 17) : ℂ) * ζ ^ 15
          - ((81 / 34) : ℂ) * ζ ^ 18
          - ((5 / 17) : ℂ) * ζ ^ 19
          - ((81 / 34) : ℂ) * ζ ^ 20
          + ((5 / 17) : ℂ) * ζ ^ 23
          + ((81 / 34) : ℂ) * ζ ^ 24
          - ((81 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry02_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (2 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (2 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((67 / 34) : ℂ)
          + ((67 / 34) : ℂ) * ζ ^ 4
          - ((75 / 17) : ℂ) * ζ ^ 5
          - ((67 / 34) : ℂ) * ζ ^ 8
          + ((75 / 17) : ℂ) * ζ ^ 9
          - ((83 / 34) : ℂ) * ζ ^ 10
          - ((75 / 17) : ℂ) * ζ ^ 13
          + ((83 / 34) : ℂ) * ζ ^ 14
          + ((4 / 17) : ℂ) * ζ ^ 15
          - ((83 / 34) : ℂ) * ζ ^ 18
          - ((4 / 17) : ℂ) * ζ ^ 19
          - ((77 / 34) : ℂ) * ζ ^ 20
          + ((4 / 17) : ℂ) * ζ ^ 23
          + ((77 / 34) : ℂ) * ζ ^ 24
          - ((77 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((67 / 34) : ℂ)
          + ((67 / 34) : ℂ) * ζ ^ 4
          - ((75 / 17) : ℂ) * ζ ^ 5
          - ((67 / 34) : ℂ) * ζ ^ 8
          + ((75 / 17) : ℂ) * ζ ^ 9
          - ((83 / 34) : ℂ) * ζ ^ 10
          - ((75 / 17) : ℂ) * ζ ^ 13
          + ((83 / 34) : ℂ) * ζ ^ 14
          + ((4 / 17) : ℂ) * ζ ^ 15
          - ((83 / 34) : ℂ) * ζ ^ 18
          - ((4 / 17) : ℂ) * ζ ^ 19
          - ((77 / 34) : ℂ) * ζ ^ 20
          + ((4 / 17) : ℂ) * ζ ^ 23
          + ((77 / 34) : ℂ) * ζ ^ 24
          - ((77 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry02_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (2 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (2 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((29 / 34) : ℂ)
          + ((29 / 34) : ℂ) * ζ ^ 4
          - ((9 / 34) : ℂ) * ζ ^ 5
          - ((29 / 34) : ℂ) * ζ ^ 8
          + ((9 / 34) : ℂ) * ζ ^ 9
          - ((2 / 17) : ℂ) * ζ ^ 10
          - ((9 / 34) : ℂ) * ζ ^ 13
          + ((2 / 17) : ℂ) * ζ ^ 14
          - ((32 / 17) : ℂ) * ζ ^ 15
          - ((2 / 17) : ℂ) * ζ ^ 18
          + ((32 / 17) : ℂ) * ζ ^ 19
          - ((22 / 17) : ℂ) * ζ ^ 20
          - ((32 / 17) : ℂ) * ζ ^ 23
          + ((22 / 17) : ℂ) * ζ ^ 24
          - ((22 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((29 / 34) : ℂ)
          + ((29 / 34) : ℂ) * ζ ^ 4
          - ((9 / 34) : ℂ) * ζ ^ 5
          - ((29 / 34) : ℂ) * ζ ^ 8
          + ((9 / 34) : ℂ) * ζ ^ 9
          - ((2 / 17) : ℂ) * ζ ^ 10
          - ((9 / 34) : ℂ) * ζ ^ 13
          + ((2 / 17) : ℂ) * ζ ^ 14
          - ((32 / 17) : ℂ) * ζ ^ 15
          - ((2 / 17) : ℂ) * ζ ^ 18
          + ((32 / 17) : ℂ) * ζ ^ 19
          - ((22 / 17) : ℂ) * ζ ^ 20
          - ((32 / 17) : ℂ) * ζ ^ 23
          + ((22 / 17) : ℂ) * ζ ^ 24
          - ((22 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry02_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (2 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (2 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((195 / 34) : ℂ)
          + ((195 / 34) : ℂ) * ζ ^ 4
          - ((134 / 17) : ℂ) * ζ ^ 5
          - ((195 / 34) : ℂ) * ζ ^ 8
          + ((134 / 17) : ℂ) * ζ ^ 9
          - ((249 / 34) : ℂ) * ζ ^ 10
          - ((134 / 17) : ℂ) * ζ ^ 13
          + ((249 / 34) : ℂ) * ζ ^ 14
          - ((327 / 34) : ℂ) * ζ ^ 15
          - ((249 / 34) : ℂ) * ζ ^ 18
          + ((327 / 34) : ℂ) * ζ ^ 19
          - ((118 / 17) : ℂ) * ζ ^ 20
          - ((327 / 34) : ℂ) * ζ ^ 23
          + ((118 / 17) : ℂ) * ζ ^ 24
          - ((118 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((195 / 34) : ℂ)
          + ((195 / 34) : ℂ) * ζ ^ 4
          - ((134 / 17) : ℂ) * ζ ^ 5
          - ((195 / 34) : ℂ) * ζ ^ 8
          + ((134 / 17) : ℂ) * ζ ^ 9
          - ((249 / 34) : ℂ) * ζ ^ 10
          - ((134 / 17) : ℂ) * ζ ^ 13
          + ((249 / 34) : ℂ) * ζ ^ 14
          - ((327 / 34) : ℂ) * ζ ^ 15
          - ((249 / 34) : ℂ) * ζ ^ 18
          + ((327 / 34) : ℂ) * ζ ^ 19
          - ((118 / 17) : ℂ) * ζ ^ 20
          - ((327 / 34) : ℂ) * ζ ^ 23
          + ((118 / 17) : ℂ) * ζ ^ 24
          - ((118 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry02_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (2 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (2 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((79 / 34) : ℂ)
          - ((79 / 34) : ℂ) * ζ ^ 4
          + ((70 / 17) : ℂ) * ζ ^ 5
          + ((79 / 34) : ℂ) * ζ ^ 8
          - ((70 / 17) : ℂ) * ζ ^ 9
          + ((117 / 34) : ℂ) * ζ ^ 10
          + ((70 / 17) : ℂ) * ζ ^ 13
          - ((117 / 34) : ℂ) * ζ ^ 14
          + ((16 / 17) : ℂ) * ζ ^ 15
          + ((117 / 34) : ℂ) * ζ ^ 18
          - ((16 / 17) : ℂ) * ζ ^ 19
          + ((89 / 34) : ℂ) * ζ ^ 20
          + ((16 / 17) : ℂ) * ζ ^ 23
          - ((89 / 34) : ℂ) * ζ ^ 24
          + ((89 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((79 / 34) : ℂ)
          - ((79 / 34) : ℂ) * ζ ^ 4
          + ((70 / 17) : ℂ) * ζ ^ 5
          + ((79 / 34) : ℂ) * ζ ^ 8
          - ((70 / 17) : ℂ) * ζ ^ 9
          + ((117 / 34) : ℂ) * ζ ^ 10
          + ((70 / 17) : ℂ) * ζ ^ 13
          - ((117 / 34) : ℂ) * ζ ^ 14
          + ((16 / 17) : ℂ) * ζ ^ 15
          + ((117 / 34) : ℂ) * ζ ^ 18
          - ((16 / 17) : ℂ) * ζ ^ 19
          + ((89 / 34) : ℂ) * ζ ^ 20
          + ((16 / 17) : ℂ) * ζ ^ 23
          - ((89 / 34) : ℂ) * ζ ^ 24
          + ((89 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry02_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (2 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (2 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((29 / 34) : ℂ)
          + ((29 / 34) : ℂ) * ζ ^ 4
          - ((78 / 17) : ℂ) * ζ ^ 5
          - ((29 / 34) : ℂ) * ζ ^ 8
          + ((78 / 17) : ℂ) * ζ ^ 9
          - ((111 / 34) : ℂ) * ζ ^ 10
          - ((78 / 17) : ℂ) * ζ ^ 13
          + ((111 / 34) : ℂ) * ζ ^ 14
          - ((121 / 34) : ℂ) * ζ ^ 15
          - ((111 / 34) : ℂ) * ζ ^ 18
          + ((121 / 34) : ℂ) * ζ ^ 19
          - ((18 / 17) : ℂ) * ζ ^ 20
          - ((121 / 34) : ℂ) * ζ ^ 23
          + ((18 / 17) : ℂ) * ζ ^ 24
          - ((18 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((29 / 34) : ℂ)
          + ((29 / 34) : ℂ) * ζ ^ 4
          - ((78 / 17) : ℂ) * ζ ^ 5
          - ((29 / 34) : ℂ) * ζ ^ 8
          + ((78 / 17) : ℂ) * ζ ^ 9
          - ((111 / 34) : ℂ) * ζ ^ 10
          - ((78 / 17) : ℂ) * ζ ^ 13
          + ((111 / 34) : ℂ) * ζ ^ 14
          - ((121 / 34) : ℂ) * ζ ^ 15
          - ((111 / 34) : ℂ) * ζ ^ 18
          + ((121 / 34) : ℂ) * ζ ^ 19
          - ((18 / 17) : ℂ) * ζ ^ 20
          - ((121 / 34) : ℂ) * ζ ^ 23
          + ((18 / 17) : ℂ) * ζ ^ 24
          - ((18 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry02_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (2 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (2 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((13 / 17) : ℂ)
          + ((13 / 17) : ℂ) * ζ ^ 4
          + ((89 / 34) : ℂ) * ζ ^ 5
          - ((13 / 17) : ℂ) * ζ ^ 8
          - ((89 / 34) : ℂ) * ζ ^ 9
          + ((61 / 34) : ℂ) * ζ ^ 10
          + ((89 / 34) : ℂ) * ζ ^ 13
          - ((61 / 34) : ℂ) * ζ ^ 14
          + ((59 / 34) : ℂ) * ζ ^ 15
          + ((61 / 34) : ℂ) * ζ ^ 18
          - ((59 / 34) : ℂ) * ζ ^ 19
          + ((5 / 17) : ℂ) * ζ ^ 20
          + ((59 / 34) : ℂ) * ζ ^ 23
          - ((5 / 17) : ℂ) * ζ ^ 24
          + ((5 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((13 / 17) : ℂ)
          + ((13 / 17) : ℂ) * ζ ^ 4
          + ((89 / 34) : ℂ) * ζ ^ 5
          - ((13 / 17) : ℂ) * ζ ^ 8
          - ((89 / 34) : ℂ) * ζ ^ 9
          + ((61 / 34) : ℂ) * ζ ^ 10
          + ((89 / 34) : ℂ) * ζ ^ 13
          - ((61 / 34) : ℂ) * ζ ^ 14
          + ((59 / 34) : ℂ) * ζ ^ 15
          + ((61 / 34) : ℂ) * ζ ^ 18
          - ((59 / 34) : ℂ) * ζ ^ 19
          + ((5 / 17) : ℂ) * ζ ^ 20
          + ((59 / 34) : ℂ) * ζ ^ 23
          - ((5 / 17) : ℂ) * ζ ^ 24
          + ((5 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry03_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (3 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (3 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((23 / 17) : ℂ)
          - ((23 / 17) : ℂ) * ζ ^ 4
          + ((88 / 17) : ℂ) * ζ ^ 5
          + ((23 / 17) : ℂ) * ζ ^ 8
          - ((88 / 17) : ℂ) * ζ ^ 9
          + ((16 / 17) : ℂ) * ζ ^ 10
          + ((88 / 17) : ℂ) * ζ ^ 13
          - ((16 / 17) : ℂ) * ζ ^ 14
          + ((13 / 17) : ℂ) * ζ ^ 15
          + ((16 / 17) : ℂ) * ζ ^ 18
          - ((13 / 17) : ℂ) * ζ ^ 19
          + ((64 / 17) : ℂ) * ζ ^ 20
          + ((13 / 17) : ℂ) * ζ ^ 23
          - ((64 / 17) : ℂ) * ζ ^ 24
          + ((64 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((23 / 17) : ℂ)
          - ((23 / 17) : ℂ) * ζ ^ 4
          + ((88 / 17) : ℂ) * ζ ^ 5
          + ((23 / 17) : ℂ) * ζ ^ 8
          - ((88 / 17) : ℂ) * ζ ^ 9
          + ((16 / 17) : ℂ) * ζ ^ 10
          + ((88 / 17) : ℂ) * ζ ^ 13
          - ((16 / 17) : ℂ) * ζ ^ 14
          + ((13 / 17) : ℂ) * ζ ^ 15
          + ((16 / 17) : ℂ) * ζ ^ 18
          - ((13 / 17) : ℂ) * ζ ^ 19
          + ((64 / 17) : ℂ) * ζ ^ 20
          + ((13 / 17) : ℂ) * ζ ^ 23
          - ((64 / 17) : ℂ) * ζ ^ 24
          + ((64 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry03_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (3 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (3 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((32 / 17) : ℂ)
          - ((32 / 17) : ℂ) * ζ ^ 4
          + ((66 / 17) : ℂ) * ζ ^ 5
          + ((32 / 17) : ℂ) * ζ ^ 8
          - ((66 / 17) : ℂ) * ζ ^ 9
          + ((89 / 17) : ℂ) * ζ ^ 10
          + ((66 / 17) : ℂ) * ζ ^ 13
          - ((89 / 17) : ℂ) * ζ ^ 14
          + ((44 / 17) : ℂ) * ζ ^ 15
          + ((89 / 17) : ℂ) * ζ ^ 18
          - ((44 / 17) : ℂ) * ζ ^ 19
          + ((55 / 17) : ℂ) * ζ ^ 20
          + ((44 / 17) : ℂ) * ζ ^ 23
          - ((55 / 17) : ℂ) * ζ ^ 24
          + ((55 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((32 / 17) : ℂ)
          - ((32 / 17) : ℂ) * ζ ^ 4
          + ((66 / 17) : ℂ) * ζ ^ 5
          + ((32 / 17) : ℂ) * ζ ^ 8
          - ((66 / 17) : ℂ) * ζ ^ 9
          + ((89 / 17) : ℂ) * ζ ^ 10
          + ((66 / 17) : ℂ) * ζ ^ 13
          - ((89 / 17) : ℂ) * ζ ^ 14
          + ((44 / 17) : ℂ) * ζ ^ 15
          + ((89 / 17) : ℂ) * ζ ^ 18
          - ((44 / 17) : ℂ) * ζ ^ 19
          + ((55 / 17) : ℂ) * ζ ^ 20
          + ((44 / 17) : ℂ) * ζ ^ 23
          - ((55 / 17) : ℂ) * ζ ^ 24
          + ((55 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry03_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (3 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (3 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((106 / 17) : ℂ)
          - ((106 / 17) : ℂ) * ζ ^ 4
          + ((118 / 17) : ℂ) * ζ ^ 5
          + ((106 / 17) : ℂ) * ζ ^ 8
          - ((118 / 17) : ℂ) * ζ ^ 9
          + ((135 / 17) : ℂ) * ζ ^ 10
          + ((118 / 17) : ℂ) * ζ ^ 13
          - ((135 / 17) : ℂ) * ζ ^ 14
          + ((158 / 17) : ℂ) * ζ ^ 15
          + ((135 / 17) : ℂ) * ζ ^ 18
          - ((158 / 17) : ℂ) * ζ ^ 19
          + ((133 / 17) : ℂ) * ζ ^ 20
          + ((158 / 17) : ℂ) * ζ ^ 23
          - ((133 / 17) : ℂ) * ζ ^ 24
          + ((133 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((106 / 17) : ℂ)
          - ((106 / 17) : ℂ) * ζ ^ 4
          + ((118 / 17) : ℂ) * ζ ^ 5
          + ((106 / 17) : ℂ) * ζ ^ 8
          - ((118 / 17) : ℂ) * ζ ^ 9
          + ((135 / 17) : ℂ) * ζ ^ 10
          + ((118 / 17) : ℂ) * ζ ^ 13
          - ((135 / 17) : ℂ) * ζ ^ 14
          + ((158 / 17) : ℂ) * ζ ^ 15
          + ((135 / 17) : ℂ) * ζ ^ 18
          - ((158 / 17) : ℂ) * ζ ^ 19
          + ((133 / 17) : ℂ) * ζ ^ 20
          + ((158 / 17) : ℂ) * ζ ^ 23
          - ((133 / 17) : ℂ) * ζ ^ 24
          + ((133 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry03_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (3 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (3 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((18 / 17) : ℂ)
          + ((18 / 17) : ℂ) * ζ ^ 4
          - ((116 / 17) : ℂ) * ζ ^ 5
          - ((18 / 17) : ℂ) * ζ ^ 8
          + ((116 / 17) : ℂ) * ζ ^ 9
          - ((41 / 17) : ℂ) * ζ ^ 10
          - ((116 / 17) : ℂ) * ζ ^ 13
          + ((41 / 17) : ℂ) * ζ ^ 14
          - ((27 / 17) : ℂ) * ζ ^ 15
          - ((41 / 17) : ℂ) * ζ ^ 18
          + ((27 / 17) : ℂ) * ζ ^ 19
          - ((60 / 17) : ℂ) * ζ ^ 20
          - ((27 / 17) : ℂ) * ζ ^ 23
          + ((60 / 17) : ℂ) * ζ ^ 24
          - ((60 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((18 / 17) : ℂ)
          + ((18 / 17) : ℂ) * ζ ^ 4
          - ((116 / 17) : ℂ) * ζ ^ 5
          - ((18 / 17) : ℂ) * ζ ^ 8
          + ((116 / 17) : ℂ) * ζ ^ 9
          - ((41 / 17) : ℂ) * ζ ^ 10
          - ((116 / 17) : ℂ) * ζ ^ 13
          + ((41 / 17) : ℂ) * ζ ^ 14
          - ((27 / 17) : ℂ) * ζ ^ 15
          - ((41 / 17) : ℂ) * ζ ^ 18
          + ((27 / 17) : ℂ) * ζ ^ 19
          - ((60 / 17) : ℂ) * ζ ^ 20
          - ((27 / 17) : ℂ) * ζ ^ 23
          + ((60 / 17) : ℂ) * ζ ^ 24
          - ((60 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry03_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (3 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (3 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((37 / 17) : ℂ)
          + ((37 / 17) : ℂ) * ζ ^ 4
          - ((190 / 17) : ℂ) * ζ ^ 5
          - ((37 / 17) : ℂ) * ζ ^ 8
          + ((190 / 17) : ℂ) * ζ ^ 9
          - ((113 / 17) : ℂ) * ζ ^ 10
          - ((190 / 17) : ℂ) * ζ ^ 13
          + ((113 / 17) : ℂ) * ζ ^ 14
          - ((69 / 17) : ℂ) * ζ ^ 15
          - ((113 / 17) : ℂ) * ζ ^ 18
          + ((69 / 17) : ℂ) * ζ ^ 19
          - ((111 / 17) : ℂ) * ζ ^ 20
          - ((69 / 17) : ℂ) * ζ ^ 23
          + ((111 / 17) : ℂ) * ζ ^ 24
          - ((111 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((37 / 17) : ℂ)
          + ((37 / 17) : ℂ) * ζ ^ 4
          - ((190 / 17) : ℂ) * ζ ^ 5
          - ((37 / 17) : ℂ) * ζ ^ 8
          + ((190 / 17) : ℂ) * ζ ^ 9
          - ((113 / 17) : ℂ) * ζ ^ 10
          - ((190 / 17) : ℂ) * ζ ^ 13
          + ((113 / 17) : ℂ) * ζ ^ 14
          - ((69 / 17) : ℂ) * ζ ^ 15
          - ((113 / 17) : ℂ) * ζ ^ 18
          + ((69 / 17) : ℂ) * ζ ^ 19
          - ((111 / 17) : ℂ) * ζ ^ 20
          - ((69 / 17) : ℂ) * ζ ^ 23
          + ((111 / 17) : ℂ) * ζ ^ 24
          - ((111 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry03_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (3 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (3 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((20 / 17) : ℂ)
          - ((20 / 17) : ℂ) * ζ ^ 4
          + ((118 / 17) : ℂ) * ζ ^ 5
          + ((20 / 17) : ℂ) * ζ ^ 8
          - ((118 / 17) : ℂ) * ζ ^ 9
          + ((105 / 17) : ℂ) * ζ ^ 10
          + ((118 / 17) : ℂ) * ζ ^ 13
          - ((105 / 17) : ℂ) * ζ ^ 14
          + ((90 / 17) : ℂ) * ζ ^ 15
          + ((105 / 17) : ℂ) * ζ ^ 18
          - ((90 / 17) : ℂ) * ζ ^ 19
          + ((100 / 17) : ℂ) * ζ ^ 20
          + ((90 / 17) : ℂ) * ζ ^ 23
          - ((100 / 17) : ℂ) * ζ ^ 24
          + ((100 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((20 / 17) : ℂ)
          - ((20 / 17) : ℂ) * ζ ^ 4
          + ((118 / 17) : ℂ) * ζ ^ 5
          + ((20 / 17) : ℂ) * ζ ^ 8
          - ((118 / 17) : ℂ) * ζ ^ 9
          + ((105 / 17) : ℂ) * ζ ^ 10
          + ((118 / 17) : ℂ) * ζ ^ 13
          - ((105 / 17) : ℂ) * ζ ^ 14
          + ((90 / 17) : ℂ) * ζ ^ 15
          + ((105 / 17) : ℂ) * ζ ^ 18
          - ((90 / 17) : ℂ) * ζ ^ 19
          + ((100 / 17) : ℂ) * ζ ^ 20
          + ((90 / 17) : ℂ) * ζ ^ 23
          - ((100 / 17) : ℂ) * ζ ^ 24
          + ((100 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry03_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (3 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (3 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(1 : ℂ)
          + ζ ^ 4
          + ((42 / 17) : ℂ) * ζ ^ 5
          - ζ ^ 8
          - ((42 / 17) : ℂ) * ζ ^ 9
          + ((101 / 17) : ℂ) * ζ ^ 10
          + ((42 / 17) : ℂ) * ζ ^ 13
          - ((101 / 17) : ℂ) * ζ ^ 14
          + ((32 / 17) : ℂ) * ζ ^ 15
          + ((101 / 17) : ℂ) * ζ ^ 18
          - ((32 / 17) : ℂ) * ζ ^ 19
          + ((32 / 17) : ℂ) * ζ ^ 23
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(1 : ℂ)
          + ζ ^ 4
          + ((42 / 17) : ℂ) * ζ ^ 5
          - ζ ^ 8
          - ((42 / 17) : ℂ) * ζ ^ 9
          + ((101 / 17) : ℂ) * ζ ^ 10
          + ((42 / 17) : ℂ) * ζ ^ 13
          - ((101 / 17) : ℂ) * ζ ^ 14
          + ((32 / 17) : ℂ) * ζ ^ 15
          + ((101 / 17) : ℂ) * ζ ^ 18
          - ((32 / 17) : ℂ) * ζ ^ 19
          + ((32 / 17) : ℂ) * ζ ^ 23
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry03_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (3 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (3 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((31 / 17) : ℂ)
          + ((31 / 17) : ℂ) * ζ ^ 4
          - ((12 / 17) : ℂ) * ζ ^ 5
          - ((31 / 17) : ℂ) * ζ ^ 8
          + ((12 / 17) : ℂ) * ζ ^ 9
          - ((36 / 17) : ℂ) * ζ ^ 10
          - ((12 / 17) : ℂ) * ζ ^ 13
          + ((36 / 17) : ℂ) * ζ ^ 14
          - ((30 / 17) : ℂ) * ζ ^ 15
          - ((36 / 17) : ℂ) * ζ ^ 18
          + ((30 / 17) : ℂ) * ζ ^ 19
          - ((35 / 17) : ℂ) * ζ ^ 20
          - ((30 / 17) : ℂ) * ζ ^ 23
          + ((35 / 17) : ℂ) * ζ ^ 24
          - ((35 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((31 / 17) : ℂ)
          + ((31 / 17) : ℂ) * ζ ^ 4
          - ((12 / 17) : ℂ) * ζ ^ 5
          - ((31 / 17) : ℂ) * ζ ^ 8
          + ((12 / 17) : ℂ) * ζ ^ 9
          - ((36 / 17) : ℂ) * ζ ^ 10
          - ((12 / 17) : ℂ) * ζ ^ 13
          + ((36 / 17) : ℂ) * ζ ^ 14
          - ((30 / 17) : ℂ) * ζ ^ 15
          - ((36 / 17) : ℂ) * ζ ^ 18
          + ((30 / 17) : ℂ) * ζ ^ 19
          - ((35 / 17) : ℂ) * ζ ^ 20
          - ((30 / 17) : ℂ) * ζ ^ 23
          + ((35 / 17) : ℂ) * ζ ^ 24
          - ((35 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry03_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (3 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (3 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((12 / 17) : ℂ)
          - ((12 / 17) : ℂ) * ζ ^ 4
          + ((45 / 17) : ℂ) * ζ ^ 5
          + ((12 / 17) : ℂ) * ζ ^ 8
          - ((45 / 17) : ℂ) * ζ ^ 9
          + ((8 / 17) : ℂ) * ζ ^ 10
          + ((45 / 17) : ℂ) * ζ ^ 13
          - ((8 / 17) : ℂ) * ζ ^ 14
          + ((19 / 17) : ℂ) * ζ ^ 15
          + ((8 / 17) : ℂ) * ζ ^ 18
          - ((19 / 17) : ℂ) * ζ ^ 19
          - ((11 / 17) : ℂ) * ζ ^ 20
          + ((19 / 17) : ℂ) * ζ ^ 23
          + ((11 / 17) : ℂ) * ζ ^ 24
          - ((11 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((12 / 17) : ℂ)
          - ((12 / 17) : ℂ) * ζ ^ 4
          + ((45 / 17) : ℂ) * ζ ^ 5
          + ((12 / 17) : ℂ) * ζ ^ 8
          - ((45 / 17) : ℂ) * ζ ^ 9
          + ((8 / 17) : ℂ) * ζ ^ 10
          + ((45 / 17) : ℂ) * ζ ^ 13
          - ((8 / 17) : ℂ) * ζ ^ 14
          + ((19 / 17) : ℂ) * ζ ^ 15
          + ((8 / 17) : ℂ) * ζ ^ 18
          - ((19 / 17) : ℂ) * ζ ^ 19
          - ((11 / 17) : ℂ) * ζ ^ 20
          + ((19 / 17) : ℂ) * ζ ^ 23
          + ((11 / 17) : ℂ) * ζ ^ 24
          - ((11 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry03_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (3 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (3 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((6 / 17) : ℂ)
          - ((6 / 17) : ℂ) * ζ ^ 4
          + ((3 / 17) : ℂ) * ζ ^ 5
          + ((6 / 17) : ℂ) * ζ ^ 8
          - ((3 / 17) : ℂ) * ζ ^ 9
          + ((50 / 17) : ℂ) * ζ ^ 10
          + ((3 / 17) : ℂ) * ζ ^ 13
          - ((50 / 17) : ℂ) * ζ ^ 14
          + ((23 / 17) : ℂ) * ζ ^ 15
          + ((50 / 17) : ℂ) * ζ ^ 18
          - ((23 / 17) : ℂ) * ζ ^ 19
          + ((33 / 17) : ℂ) * ζ ^ 20
          + ((23 / 17) : ℂ) * ζ ^ 23
          - ((33 / 17) : ℂ) * ζ ^ 24
          + ((33 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((6 / 17) : ℂ)
          - ((6 / 17) : ℂ) * ζ ^ 4
          + ((3 / 17) : ℂ) * ζ ^ 5
          + ((6 / 17) : ℂ) * ζ ^ 8
          - ((3 / 17) : ℂ) * ζ ^ 9
          + ((50 / 17) : ℂ) * ζ ^ 10
          + ((3 / 17) : ℂ) * ζ ^ 13
          - ((50 / 17) : ℂ) * ζ ^ 14
          + ((23 / 17) : ℂ) * ζ ^ 15
          + ((50 / 17) : ℂ) * ζ ^ 18
          - ((23 / 17) : ℂ) * ζ ^ 19
          + ((33 / 17) : ℂ) * ζ ^ 20
          + ((23 / 17) : ℂ) * ζ ^ 23
          - ((33 / 17) : ℂ) * ζ ^ 24
          + ((33 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry04_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (4 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (4 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((21 / 17) : ℂ)
          + ((21 / 17) : ℂ) * ζ ^ 4
          - ((36 / 17) : ℂ) * ζ ^ 5
          - ((21 / 17) : ℂ) * ζ ^ 8
          + ((36 / 17) : ℂ) * ζ ^ 9
          + ((12 / 17) : ℂ) * ζ ^ 10
          - ((36 / 17) : ℂ) * ζ ^ 13
          - ((12 / 17) : ℂ) * ζ ^ 14
          - ((7 / 17) : ℂ) * ζ ^ 15
          + ((12 / 17) : ℂ) * ζ ^ 18
          + ((7 / 17) : ℂ) * ζ ^ 19
          + ((23 / 17) : ℂ) * ζ ^ 20
          - ((7 / 17) : ℂ) * ζ ^ 23
          - ((23 / 17) : ℂ) * ζ ^ 24
          + ((23 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((21 / 17) : ℂ)
          + ((21 / 17) : ℂ) * ζ ^ 4
          - ((36 / 17) : ℂ) * ζ ^ 5
          - ((21 / 17) : ℂ) * ζ ^ 8
          + ((36 / 17) : ℂ) * ζ ^ 9
          + ((12 / 17) : ℂ) * ζ ^ 10
          - ((36 / 17) : ℂ) * ζ ^ 13
          - ((12 / 17) : ℂ) * ζ ^ 14
          - ((7 / 17) : ℂ) * ζ ^ 15
          + ((12 / 17) : ℂ) * ζ ^ 18
          + ((7 / 17) : ℂ) * ζ ^ 19
          + ((23 / 17) : ℂ) * ζ ^ 20
          - ((7 / 17) : ℂ) * ζ ^ 23
          - ((23 / 17) : ℂ) * ζ ^ 24
          + ((23 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry04_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (4 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (4 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((3 / 34) : ℂ)
          - ((3 / 34) : ℂ) * ζ ^ 4
          - ((25 / 34) : ℂ) * ζ ^ 5
          + ((3 / 34) : ℂ) * ζ ^ 8
          + ((25 / 34) : ℂ) * ζ ^ 9
          + ((3 / 17) : ℂ) * ζ ^ 10
          - ((25 / 34) : ℂ) * ζ ^ 13
          - ((3 / 17) : ℂ) * ζ ^ 14
          - ((43 / 17) : ℂ) * ζ ^ 15
          + ((3 / 17) : ℂ) * ζ ^ 18
          + ((43 / 17) : ℂ) * ζ ^ 19
          - ((30 / 17) : ℂ) * ζ ^ 20
          - ((43 / 17) : ℂ) * ζ ^ 23
          + ((30 / 17) : ℂ) * ζ ^ 24
          - ((30 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((3 / 34) : ℂ)
          - ((3 / 34) : ℂ) * ζ ^ 4
          - ((25 / 34) : ℂ) * ζ ^ 5
          + ((3 / 34) : ℂ) * ζ ^ 8
          + ((25 / 34) : ℂ) * ζ ^ 9
          + ((3 / 17) : ℂ) * ζ ^ 10
          - ((25 / 34) : ℂ) * ζ ^ 13
          - ((3 / 17) : ℂ) * ζ ^ 14
          - ((43 / 17) : ℂ) * ζ ^ 15
          + ((3 / 17) : ℂ) * ζ ^ 18
          + ((43 / 17) : ℂ) * ζ ^ 19
          - ((30 / 17) : ℂ) * ζ ^ 20
          - ((43 / 17) : ℂ) * ζ ^ 23
          + ((30 / 17) : ℂ) * ζ ^ 24
          - ((30 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry04_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (4 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (4 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((3 / 34) : ℂ)
          - ((3 / 34) : ℂ) * ζ ^ 4
          - ((95 / 34) : ℂ) * ζ ^ 5
          + ((3 / 34) : ℂ) * ζ ^ 8
          + ((95 / 34) : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 10
          - ((95 / 34) : ℂ) * ζ ^ 13
          - ((1 / 17) : ℂ) * ζ ^ 14
          - ((44 / 17) : ℂ) * ζ ^ 15
          + ((1 / 17) : ℂ) * ζ ^ 18
          + ((44 / 17) : ℂ) * ζ ^ 19
          + ((10 / 17) : ℂ) * ζ ^ 20
          - ((44 / 17) : ℂ) * ζ ^ 23
          - ((10 / 17) : ℂ) * ζ ^ 24
          + ((10 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((3 / 34) : ℂ)
          - ((3 / 34) : ℂ) * ζ ^ 4
          - ((95 / 34) : ℂ) * ζ ^ 5
          + ((3 / 34) : ℂ) * ζ ^ 8
          + ((95 / 34) : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 10
          - ((95 / 34) : ℂ) * ζ ^ 13
          - ((1 / 17) : ℂ) * ζ ^ 14
          - ((44 / 17) : ℂ) * ζ ^ 15
          + ((1 / 17) : ℂ) * ζ ^ 18
          + ((44 / 17) : ℂ) * ζ ^ 19
          + ((10 / 17) : ℂ) * ζ ^ 20
          - ((44 / 17) : ℂ) * ζ ^ 23
          - ((10 / 17) : ℂ) * ζ ^ 24
          + ((10 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry04_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (4 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (4 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((97 / 34) : ℂ) * ζ ^ 5
          - ((97 / 34) : ℂ) * ζ ^ 9
          - ((27 / 34) : ℂ) * ζ ^ 10
          + ((97 / 34) : ℂ) * ζ ^ 13
          + ((27 / 34) : ℂ) * ζ ^ 14
          + ((16 / 17) : ℂ) * ζ ^ 15
          - ((27 / 34) : ℂ) * ζ ^ 18
          - ((16 / 17) : ℂ) * ζ ^ 19
          - ((49 / 34) : ℂ) * ζ ^ 20
          + ((16 / 17) : ℂ) * ζ ^ 23
          + ((49 / 34) : ℂ) * ζ ^ 24
          - ((49 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((97 / 34) : ℂ) * ζ ^ 5
          - ((97 / 34) : ℂ) * ζ ^ 9
          - ((27 / 34) : ℂ) * ζ ^ 10
          + ((97 / 34) : ℂ) * ζ ^ 13
          + ((27 / 34) : ℂ) * ζ ^ 14
          + ((16 / 17) : ℂ) * ζ ^ 15
          - ((27 / 34) : ℂ) * ζ ^ 18
          - ((16 / 17) : ℂ) * ζ ^ 19
          - ((49 / 34) : ℂ) * ζ ^ 20
          + ((16 / 17) : ℂ) * ζ ^ 23
          + ((49 / 34) : ℂ) * ζ ^ 24
          - ((49 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry04_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (4 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (4 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((23 / 34) : ℂ)
          + ((23 / 34) : ℂ) * ζ ^ 4
          + ((87 / 17) : ℂ) * ζ ^ 5
          - ((23 / 34) : ℂ) * ζ ^ 8
          - ((87 / 17) : ℂ) * ζ ^ 9
          - ((53 / 34) : ℂ) * ζ ^ 10
          + ((87 / 17) : ℂ) * ζ ^ 13
          + ((53 / 34) : ℂ) * ζ ^ 14
          + ((30 / 17) : ℂ) * ζ ^ 15
          - ((53 / 34) : ℂ) * ζ ^ 18
          - ((30 / 17) : ℂ) * ζ ^ 19
          - ((25 / 34) : ℂ) * ζ ^ 20
          + ((30 / 17) : ℂ) * ζ ^ 23
          + ((25 / 34) : ℂ) * ζ ^ 24
          - ((25 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((23 / 34) : ℂ)
          + ((23 / 34) : ℂ) * ζ ^ 4
          + ((87 / 17) : ℂ) * ζ ^ 5
          - ((23 / 34) : ℂ) * ζ ^ 8
          - ((87 / 17) : ℂ) * ζ ^ 9
          - ((53 / 34) : ℂ) * ζ ^ 10
          + ((87 / 17) : ℂ) * ζ ^ 13
          + ((53 / 34) : ℂ) * ζ ^ 14
          + ((30 / 17) : ℂ) * ζ ^ 15
          - ((53 / 34) : ℂ) * ζ ^ 18
          - ((30 / 17) : ℂ) * ζ ^ 19
          - ((25 / 34) : ℂ) * ζ ^ 20
          + ((30 / 17) : ℂ) * ζ ^ 23
          + ((25 / 34) : ℂ) * ζ ^ 24
          - ((25 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry04_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (4 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (4 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((8 / 17) : ℂ)
          - ((8 / 17) : ℂ) * ζ ^ 4
          - ((44 / 17) : ℂ) * ζ ^ 5
          + ((8 / 17) : ℂ) * ζ ^ 8
          + ((44 / 17) : ℂ) * ζ ^ 9
          + ((16 / 17) : ℂ) * ζ ^ 10
          - ((44 / 17) : ℂ) * ζ ^ 13
          - ((16 / 17) : ℂ) * ζ ^ 14
          - ((39 / 17) : ℂ) * ζ ^ 15
          + ((16 / 17) : ℂ) * ζ ^ 18
          + ((39 / 17) : ℂ) * ζ ^ 19
          - ((23 / 17) : ℂ) * ζ ^ 20
          - ((39 / 17) : ℂ) * ζ ^ 23
          + ((23 / 17) : ℂ) * ζ ^ 24
          - ((23 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((8 / 17) : ℂ)
          - ((8 / 17) : ℂ) * ζ ^ 4
          - ((44 / 17) : ℂ) * ζ ^ 5
          + ((8 / 17) : ℂ) * ζ ^ 8
          + ((44 / 17) : ℂ) * ζ ^ 9
          + ((16 / 17) : ℂ) * ζ ^ 10
          - ((44 / 17) : ℂ) * ζ ^ 13
          - ((16 / 17) : ℂ) * ζ ^ 14
          - ((39 / 17) : ℂ) * ζ ^ 15
          + ((16 / 17) : ℂ) * ζ ^ 18
          + ((39 / 17) : ℂ) * ζ ^ 19
          - ((23 / 17) : ℂ) * ζ ^ 20
          - ((39 / 17) : ℂ) * ζ ^ 23
          + ((23 / 17) : ℂ) * ζ ^ 24
          - ((23 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry04_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (4 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (4 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((117 / 34) : ℂ)
          - ((117 / 34) : ℂ) * ζ ^ 4
          - ((5 / 17) : ℂ) * ζ ^ 5
          + ((117 / 34) : ℂ) * ζ ^ 8
          + ((5 / 17) : ℂ) * ζ ^ 9
          - ((29 / 34) : ℂ) * ζ ^ 10
          - ((5 / 17) : ℂ) * ζ ^ 13
          + ((29 / 34) : ℂ) * ζ ^ 14
          - ((69 / 34) : ℂ) * ζ ^ 15
          - ((29 / 34) : ℂ) * ζ ^ 18
          + ((69 / 34) : ℂ) * ζ ^ 19
          - ((45 / 17) : ℂ) * ζ ^ 20
          - ((69 / 34) : ℂ) * ζ ^ 23
          + ((45 / 17) : ℂ) * ζ ^ 24
          - ((45 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((117 / 34) : ℂ)
          - ((117 / 34) : ℂ) * ζ ^ 4
          - ((5 / 17) : ℂ) * ζ ^ 5
          + ((117 / 34) : ℂ) * ζ ^ 8
          + ((5 / 17) : ℂ) * ζ ^ 9
          - ((29 / 34) : ℂ) * ζ ^ 10
          - ((5 / 17) : ℂ) * ζ ^ 13
          + ((29 / 34) : ℂ) * ζ ^ 14
          - ((69 / 34) : ℂ) * ζ ^ 15
          - ((29 / 34) : ℂ) * ζ ^ 18
          + ((69 / 34) : ℂ) * ζ ^ 19
          - ((45 / 17) : ℂ) * ζ ^ 20
          - ((69 / 34) : ℂ) * ζ ^ 23
          + ((45 / 17) : ℂ) * ζ ^ 24
          - ((45 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry04_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (4 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (4 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((25 / 34) : ℂ)
          + ((25 / 34) : ℂ) * ζ ^ 4
          - ((13 / 17) : ℂ) * ζ ^ 5
          - ((25 / 34) : ℂ) * ζ ^ 8
          + ((13 / 17) : ℂ) * ζ ^ 9
          + ((31 / 34) : ℂ) * ζ ^ 10
          - ((13 / 17) : ℂ) * ζ ^ 13
          - ((31 / 34) : ℂ) * ζ ^ 14
          + ((9 / 17) : ℂ) * ζ ^ 15
          + ((31 / 34) : ℂ) * ζ ^ 18
          - ((9 / 17) : ℂ) * ζ ^ 19
          + ((65 / 34) : ℂ) * ζ ^ 20
          + ((9 / 17) : ℂ) * ζ ^ 23
          - ((65 / 34) : ℂ) * ζ ^ 24
          + ((65 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((25 / 34) : ℂ)
          + ((25 / 34) : ℂ) * ζ ^ 4
          - ((13 / 17) : ℂ) * ζ ^ 5
          - ((25 / 34) : ℂ) * ζ ^ 8
          + ((13 / 17) : ℂ) * ζ ^ 9
          + ((31 / 34) : ℂ) * ζ ^ 10
          - ((13 / 17) : ℂ) * ζ ^ 13
          - ((31 / 34) : ℂ) * ζ ^ 14
          + ((9 / 17) : ℂ) * ζ ^ 15
          + ((31 / 34) : ℂ) * ζ ^ 18
          - ((9 / 17) : ℂ) * ζ ^ 19
          + ((65 / 34) : ℂ) * ζ ^ 20
          + ((9 / 17) : ℂ) * ζ ^ 23
          - ((65 / 34) : ℂ) * ζ ^ 24
          + ((65 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry04_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (4 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (4 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((5 / 34) : ℂ)
          - ((5 / 34) : ℂ) * ζ ^ 4
          + ((25 / 17) : ℂ) * ζ ^ 5
          + ((5 / 34) : ℂ) * ζ ^ 8
          - ((25 / 17) : ℂ) * ζ ^ 9
          - ((39 / 34) : ℂ) * ζ ^ 10
          + ((25 / 17) : ℂ) * ζ ^ 13
          + ((39 / 34) : ℂ) * ζ ^ 14
          - ((3 / 34) : ℂ) * ζ ^ 15
          - ((39 / 34) : ℂ) * ζ ^ 18
          + ((3 / 34) : ℂ) * ζ ^ 19
          - ((44 / 17) : ℂ) * ζ ^ 20
          - ((3 / 34) : ℂ) * ζ ^ 23
          + ((44 / 17) : ℂ) * ζ ^ 24
          - ((44 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((5 / 34) : ℂ)
          - ((5 / 34) : ℂ) * ζ ^ 4
          + ((25 / 17) : ℂ) * ζ ^ 5
          + ((5 / 34) : ℂ) * ζ ^ 8
          - ((25 / 17) : ℂ) * ζ ^ 9
          - ((39 / 34) : ℂ) * ζ ^ 10
          + ((25 / 17) : ℂ) * ζ ^ 13
          + ((39 / 34) : ℂ) * ζ ^ 14
          - ((3 / 34) : ℂ) * ζ ^ 15
          - ((39 / 34) : ℂ) * ζ ^ 18
          + ((3 / 34) : ℂ) * ζ ^ 19
          - ((44 / 17) : ℂ) * ζ ^ 20
          - ((3 / 34) : ℂ) * ζ ^ 23
          + ((44 / 17) : ℂ) * ζ ^ 24
          - ((44 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry04_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (4 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (4 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((11 / 34) : ℂ)
          + ((11 / 34) : ℂ) * ζ ^ 4
          - ((24 / 17) : ℂ) * ζ ^ 5
          - ((11 / 34) : ℂ) * ζ ^ 8
          + ((24 / 17) : ℂ) * ζ ^ 9
          + ((33 / 34) : ℂ) * ζ ^ 10
          - ((24 / 17) : ℂ) * ζ ^ 13
          - ((33 / 34) : ℂ) * ζ ^ 14
          - ((45 / 34) : ℂ) * ζ ^ 15
          + ((33 / 34) : ℂ) * ζ ^ 18
          + ((45 / 34) : ℂ) * ζ ^ 19
          + ((25 / 17) : ℂ) * ζ ^ 20
          - ((45 / 34) : ℂ) * ζ ^ 23
          - ((25 / 17) : ℂ) * ζ ^ 24
          + ((25 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((11 / 34) : ℂ)
          + ((11 / 34) : ℂ) * ζ ^ 4
          - ((24 / 17) : ℂ) * ζ ^ 5
          - ((11 / 34) : ℂ) * ζ ^ 8
          + ((24 / 17) : ℂ) * ζ ^ 9
          + ((33 / 34) : ℂ) * ζ ^ 10
          - ((24 / 17) : ℂ) * ζ ^ 13
          - ((33 / 34) : ℂ) * ζ ^ 14
          - ((45 / 34) : ℂ) * ζ ^ 15
          + ((33 / 34) : ℂ) * ζ ^ 18
          + ((45 / 34) : ℂ) * ζ ^ 19
          + ((25 / 17) : ℂ) * ζ ^ 20
          - ((45 / 34) : ℂ) * ζ ^ 23
          - ((25 / 17) : ℂ) * ζ ^ 24
          + ((25 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry05_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (5 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (5 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((58 / 17) : ℂ)
          + ((58 / 17) : ℂ) * ζ ^ 4
          - ((179 / 34) : ℂ) * ζ ^ 5
          - ((58 / 17) : ℂ) * ζ ^ 8
          + ((179 / 34) : ℂ) * ζ ^ 9
          - ((183 / 34) : ℂ) * ζ ^ 10
          - ((179 / 34) : ℂ) * ζ ^ 13
          + ((183 / 34) : ℂ) * ζ ^ 14
          - ((78 / 17) : ℂ) * ζ ^ 15
          - ((183 / 34) : ℂ) * ζ ^ 18
          + ((78 / 17) : ℂ) * ζ ^ 19
          - ((73 / 34) : ℂ) * ζ ^ 20
          - ((78 / 17) : ℂ) * ζ ^ 23
          + ((73 / 34) : ℂ) * ζ ^ 24
          - ((73 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((58 / 17) : ℂ)
          + ((58 / 17) : ℂ) * ζ ^ 4
          - ((179 / 34) : ℂ) * ζ ^ 5
          - ((58 / 17) : ℂ) * ζ ^ 8
          + ((179 / 34) : ℂ) * ζ ^ 9
          - ((183 / 34) : ℂ) * ζ ^ 10
          - ((179 / 34) : ℂ) * ζ ^ 13
          + ((183 / 34) : ℂ) * ζ ^ 14
          - ((78 / 17) : ℂ) * ζ ^ 15
          - ((183 / 34) : ℂ) * ζ ^ 18
          + ((78 / 17) : ℂ) * ζ ^ 19
          - ((73 / 34) : ℂ) * ζ ^ 20
          - ((78 / 17) : ℂ) * ζ ^ 23
          + ((73 / 34) : ℂ) * ζ ^ 24
          - ((73 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry05_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (5 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (5 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((55 / 34) : ℂ)
          - ((55 / 34) : ℂ) * ζ ^ 4
          + ((5 / 2) : ℂ) * ζ ^ 5
          + ((55 / 34) : ℂ) * ζ ^ 8
          - ((5 / 2) : ℂ) * ζ ^ 9
          + ((60 / 17) : ℂ) * ζ ^ 10
          + ((5 / 2) : ℂ) * ζ ^ 13
          - ((60 / 17) : ℂ) * ζ ^ 14
          + ((10 / 17) : ℂ) * ζ ^ 15
          + ((60 / 17) : ℂ) * ζ ^ 18
          - ((10 / 17) : ℂ) * ζ ^ 19
          + ((1 / 17) : ℂ) * ζ ^ 20
          + ((10 / 17) : ℂ) * ζ ^ 23
          - ((1 / 17) : ℂ) * ζ ^ 24
          + ((1 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((55 / 34) : ℂ)
          - ((55 / 34) : ℂ) * ζ ^ 4
          + ((5 / 2) : ℂ) * ζ ^ 5
          + ((55 / 34) : ℂ) * ζ ^ 8
          - ((5 / 2) : ℂ) * ζ ^ 9
          + ((60 / 17) : ℂ) * ζ ^ 10
          + ((5 / 2) : ℂ) * ζ ^ 13
          - ((60 / 17) : ℂ) * ζ ^ 14
          + ((10 / 17) : ℂ) * ζ ^ 15
          + ((60 / 17) : ℂ) * ζ ^ 18
          - ((10 / 17) : ℂ) * ζ ^ 19
          + ((1 / 17) : ℂ) * ζ ^ 20
          + ((10 / 17) : ℂ) * ζ ^ 23
          - ((1 / 17) : ℂ) * ζ ^ 24
          + ((1 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry05_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (5 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (5 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((77 / 34) : ℂ)
          + ((77 / 34) : ℂ) * ζ ^ 4
          - ((31 / 34) : ℂ) * ζ ^ 5
          - ((77 / 34) : ℂ) * ζ ^ 8
          + ((31 / 34) : ℂ) * ζ ^ 9
          - ((30 / 17) : ℂ) * ζ ^ 10
          - ((31 / 34) : ℂ) * ζ ^ 13
          + ((30 / 17) : ℂ) * ζ ^ 14
          - ((103 / 17) : ℂ) * ζ ^ 15
          - ((30 / 17) : ℂ) * ζ ^ 18
          + ((103 / 17) : ℂ) * ζ ^ 19
          + ((33 / 17) : ℂ) * ζ ^ 20
          - ((103 / 17) : ℂ) * ζ ^ 23
          - ((33 / 17) : ℂ) * ζ ^ 24
          + ((33 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((77 / 34) : ℂ)
          + ((77 / 34) : ℂ) * ζ ^ 4
          - ((31 / 34) : ℂ) * ζ ^ 5
          - ((77 / 34) : ℂ) * ζ ^ 8
          + ((31 / 34) : ℂ) * ζ ^ 9
          - ((30 / 17) : ℂ) * ζ ^ 10
          - ((31 / 34) : ℂ) * ζ ^ 13
          + ((30 / 17) : ℂ) * ζ ^ 14
          - ((103 / 17) : ℂ) * ζ ^ 15
          - ((30 / 17) : ℂ) * ζ ^ 18
          + ((103 / 17) : ℂ) * ζ ^ 19
          + ((33 / 17) : ℂ) * ζ ^ 20
          - ((103 / 17) : ℂ) * ζ ^ 23
          - ((33 / 17) : ℂ) * ζ ^ 24
          + ((33 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry05_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (5 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (5 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((28 / 17) : ℂ)
          - ((28 / 17) : ℂ) * ζ ^ 4
          + (3 : ℂ) * ζ ^ 5
          + ((28 / 17) : ℂ) * ζ ^ 8
          - (3 : ℂ) * ζ ^ 9
          + ((58 / 17) : ℂ) * ζ ^ 10
          + (3 : ℂ) * ζ ^ 13
          - ((58 / 17) : ℂ) * ζ ^ 14
          + ((44 / 17) : ℂ) * ζ ^ 15
          + ((58 / 17) : ℂ) * ζ ^ 18
          - ((44 / 17) : ℂ) * ζ ^ 19
          + ((9 / 17) : ℂ) * ζ ^ 20
          + ((44 / 17) : ℂ) * ζ ^ 23
          - ((9 / 17) : ℂ) * ζ ^ 24
          + ((9 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((28 / 17) : ℂ)
          - ((28 / 17) : ℂ) * ζ ^ 4
          + (3 : ℂ) * ζ ^ 5
          + ((28 / 17) : ℂ) * ζ ^ 8
          - (3 : ℂ) * ζ ^ 9
          + ((58 / 17) : ℂ) * ζ ^ 10
          + (3 : ℂ) * ζ ^ 13
          - ((58 / 17) : ℂ) * ζ ^ 14
          + ((44 / 17) : ℂ) * ζ ^ 15
          + ((58 / 17) : ℂ) * ζ ^ 18
          - ((44 / 17) : ℂ) * ζ ^ 19
          + ((9 / 17) : ℂ) * ζ ^ 20
          + ((44 / 17) : ℂ) * ζ ^ 23
          - ((9 / 17) : ℂ) * ζ ^ 24
          + ((9 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry05_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (5 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (5 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((95 / 34) : ℂ)
          - ((95 / 34) : ℂ) * ζ ^ 4
          + ((64 / 17) : ℂ) * ζ ^ 5
          + ((95 / 34) : ℂ) * ζ ^ 8
          - ((64 / 17) : ℂ) * ζ ^ 9
          + ((97 / 34) : ℂ) * ζ ^ 10
          + ((64 / 17) : ℂ) * ζ ^ 13
          - ((97 / 34) : ℂ) * ζ ^ 14
          + ((36 / 17) : ℂ) * ζ ^ 15
          + ((97 / 34) : ℂ) * ζ ^ 18
          - ((36 / 17) : ℂ) * ζ ^ 19
          + ((45 / 34) : ℂ) * ζ ^ 20
          + ((36 / 17) : ℂ) * ζ ^ 23
          - ((45 / 34) : ℂ) * ζ ^ 24
          + ((45 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((95 / 34) : ℂ)
          - ((95 / 34) : ℂ) * ζ ^ 4
          + ((64 / 17) : ℂ) * ζ ^ 5
          + ((95 / 34) : ℂ) * ζ ^ 8
          - ((64 / 17) : ℂ) * ζ ^ 9
          + ((97 / 34) : ℂ) * ζ ^ 10
          + ((64 / 17) : ℂ) * ζ ^ 13
          - ((97 / 34) : ℂ) * ζ ^ 14
          + ((36 / 17) : ℂ) * ζ ^ 15
          + ((97 / 34) : ℂ) * ζ ^ 18
          - ((36 / 17) : ℂ) * ζ ^ 19
          + ((45 / 34) : ℂ) * ζ ^ 20
          + ((36 / 17) : ℂ) * ζ ^ 23
          - ((45 / 34) : ℂ) * ζ ^ 24
          + ((45 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry05_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (5 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (5 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((2 / 17) : ℂ)
          - ((2 / 17) : ℂ) * ζ ^ 4
          + ((25 / 34) : ℂ) * ζ ^ 5
          + ((2 / 17) : ℂ) * ζ ^ 8
          - ((25 / 34) : ℂ) * ζ ^ 9
          + ((3 / 2) : ℂ) * ζ ^ 10
          + ((25 / 34) : ℂ) * ζ ^ 13
          - ((3 / 2) : ℂ) * ζ ^ 14
          - ((11 / 17) : ℂ) * ζ ^ 15
          + ((3 / 2) : ℂ) * ζ ^ 18
          + ((11 / 17) : ℂ) * ζ ^ 19
          + ((41 / 34) : ℂ) * ζ ^ 20
          - ((11 / 17) : ℂ) * ζ ^ 23
          - ((41 / 34) : ℂ) * ζ ^ 24
          + ((41 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((2 / 17) : ℂ)
          - ((2 / 17) : ℂ) * ζ ^ 4
          + ((25 / 34) : ℂ) * ζ ^ 5
          + ((2 / 17) : ℂ) * ζ ^ 8
          - ((25 / 34) : ℂ) * ζ ^ 9
          + ((3 / 2) : ℂ) * ζ ^ 10
          + ((25 / 34) : ℂ) * ζ ^ 13
          - ((3 / 2) : ℂ) * ζ ^ 14
          - ((11 / 17) : ℂ) * ζ ^ 15
          + ((3 / 2) : ℂ) * ζ ^ 18
          + ((11 / 17) : ℂ) * ζ ^ 19
          + ((41 / 34) : ℂ) * ζ ^ 20
          - ((11 / 17) : ℂ) * ζ ^ 23
          - ((41 / 34) : ℂ) * ζ ^ 24
          + ((41 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry05_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (5 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (5 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((191 / 34) : ℂ)
          - ((191 / 34) : ℂ) * ζ ^ 4
          + ((138 / 17) : ℂ) * ζ ^ 5
          + ((191 / 34) : ℂ) * ζ ^ 8
          - ((138 / 17) : ℂ) * ζ ^ 9
          + ((315 / 34) : ℂ) * ζ ^ 10
          + ((138 / 17) : ℂ) * ζ ^ 13
          - ((315 / 34) : ℂ) * ζ ^ 14
          + ((267 / 34) : ℂ) * ζ ^ 15
          + ((315 / 34) : ℂ) * ζ ^ 18
          - ((267 / 34) : ℂ) * ζ ^ 19
          + ((79 / 17) : ℂ) * ζ ^ 20
          + ((267 / 34) : ℂ) * ζ ^ 23
          - ((79 / 17) : ℂ) * ζ ^ 24
          + ((79 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((191 / 34) : ℂ)
          - ((191 / 34) : ℂ) * ζ ^ 4
          + ((138 / 17) : ℂ) * ζ ^ 5
          + ((191 / 34) : ℂ) * ζ ^ 8
          - ((138 / 17) : ℂ) * ζ ^ 9
          + ((315 / 34) : ℂ) * ζ ^ 10
          + ((138 / 17) : ℂ) * ζ ^ 13
          - ((315 / 34) : ℂ) * ζ ^ 14
          + ((267 / 34) : ℂ) * ζ ^ 15
          + ((315 / 34) : ℂ) * ζ ^ 18
          - ((267 / 34) : ℂ) * ζ ^ 19
          + ((79 / 17) : ℂ) * ζ ^ 20
          + ((267 / 34) : ℂ) * ζ ^ 23
          - ((79 / 17) : ℂ) * ζ ^ 24
          + ((79 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry05_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (5 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (5 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((67 / 34) : ℂ)
          + ((67 / 34) : ℂ) * ζ ^ 4
          - ((65 / 17) : ℂ) * ζ ^ 5
          - ((67 / 34) : ℂ) * ζ ^ 8
          + ((65 / 17) : ℂ) * ζ ^ 9
          - ((145 / 34) : ℂ) * ζ ^ 10
          - ((65 / 17) : ℂ) * ζ ^ 13
          + ((145 / 34) : ℂ) * ζ ^ 14
          - ((11 / 17) : ℂ) * ζ ^ 15
          - ((145 / 34) : ℂ) * ζ ^ 18
          + ((11 / 17) : ℂ) * ζ ^ 19
          - ((59 / 34) : ℂ) * ζ ^ 20
          - ((11 / 17) : ℂ) * ζ ^ 23
          + ((59 / 34) : ℂ) * ζ ^ 24
          - ((59 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((67 / 34) : ℂ)
          + ((67 / 34) : ℂ) * ζ ^ 4
          - ((65 / 17) : ℂ) * ζ ^ 5
          - ((67 / 34) : ℂ) * ζ ^ 8
          + ((65 / 17) : ℂ) * ζ ^ 9
          - ((145 / 34) : ℂ) * ζ ^ 10
          - ((65 / 17) : ℂ) * ζ ^ 13
          + ((145 / 34) : ℂ) * ζ ^ 14
          - ((11 / 17) : ℂ) * ζ ^ 15
          - ((145 / 34) : ℂ) * ζ ^ 18
          + ((11 / 17) : ℂ) * ζ ^ 19
          - ((59 / 34) : ℂ) * ζ ^ 20
          - ((11 / 17) : ℂ) * ζ ^ 23
          + ((59 / 34) : ℂ) * ζ ^ 24
          - ((59 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry05_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (5 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (5 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((49 / 34) : ℂ)
          - ((49 / 34) : ℂ) * ζ ^ 4
          + ((58 / 17) : ℂ) * ζ ^ 5
          + ((49 / 34) : ℂ) * ζ ^ 8
          - ((58 / 17) : ℂ) * ζ ^ 9
          + ((121 / 34) : ℂ) * ζ ^ 10
          + ((58 / 17) : ℂ) * ζ ^ 13
          - ((121 / 34) : ℂ) * ζ ^ 14
          + ((115 / 34) : ℂ) * ζ ^ 15
          + ((121 / 34) : ℂ) * ζ ^ 18
          - ((115 / 34) : ℂ) * ζ ^ 19
          + ((9 / 17) : ℂ) * ζ ^ 20
          + ((115 / 34) : ℂ) * ζ ^ 23
          - ((9 / 17) : ℂ) * ζ ^ 24
          + ((9 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((49 / 34) : ℂ)
          - ((49 / 34) : ℂ) * ζ ^ 4
          + ((58 / 17) : ℂ) * ζ ^ 5
          + ((49 / 34) : ℂ) * ζ ^ 8
          - ((58 / 17) : ℂ) * ζ ^ 9
          + ((121 / 34) : ℂ) * ζ ^ 10
          + ((58 / 17) : ℂ) * ζ ^ 13
          - ((121 / 34) : ℂ) * ζ ^ 14
          + ((115 / 34) : ℂ) * ζ ^ 15
          + ((121 / 34) : ℂ) * ζ ^ 18
          - ((115 / 34) : ℂ) * ζ ^ 19
          + ((9 / 17) : ℂ) * ζ ^ 20
          + ((115 / 34) : ℂ) * ζ ^ 23
          - ((9 / 17) : ℂ) * ζ ^ 24
          + ((9 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry05_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (5 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (5 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((25 / 34) : ℂ)
          + ((25 / 34) : ℂ) * ζ ^ 4
          - ((55 / 34) : ℂ) * ζ ^ 5
          - ((25 / 34) : ℂ) * ζ ^ 8
          + ((55 / 34) : ℂ) * ζ ^ 9
          - ((22 / 17) : ℂ) * ζ ^ 10
          - ((55 / 34) : ℂ) * ζ ^ 13
          + ((22 / 17) : ℂ) * ζ ^ 14
          - ((93 / 34) : ℂ) * ζ ^ 15
          - ((22 / 17) : ℂ) * ζ ^ 18
          + ((93 / 34) : ℂ) * ζ ^ 19
          + ((7 / 34) : ℂ) * ζ ^ 20
          - ((93 / 34) : ℂ) * ζ ^ 23
          - ((7 / 34) : ℂ) * ζ ^ 24
          + ((7 / 34) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((25 / 34) : ℂ)
          + ((25 / 34) : ℂ) * ζ ^ 4
          - ((55 / 34) : ℂ) * ζ ^ 5
          - ((25 / 34) : ℂ) * ζ ^ 8
          + ((55 / 34) : ℂ) * ζ ^ 9
          - ((22 / 17) : ℂ) * ζ ^ 10
          - ((55 / 34) : ℂ) * ζ ^ 13
          + ((22 / 17) : ℂ) * ζ ^ 14
          - ((93 / 34) : ℂ) * ζ ^ 15
          - ((22 / 17) : ℂ) * ζ ^ 18
          + ((93 / 34) : ℂ) * ζ ^ 19
          + ((7 / 34) : ℂ) * ζ ^ 20
          - ((93 / 34) : ℂ) * ζ ^ 23
          - ((7 / 34) : ℂ) * ζ ^ 24
          + ((7 / 34) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry06_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (6 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (6 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((20 / 17) : ℂ)
          + ((20 / 17) : ℂ) * ζ ^ 4
          - ((23 / 17) : ℂ) * ζ ^ 5
          - ((20 / 17) : ℂ) * ζ ^ 8
          + ((23 / 17) : ℂ) * ζ ^ 9
          - ((23 / 17) : ℂ) * ζ ^ 13
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
          - ((23 / 17) : ℂ) * ζ ^ 5
          - ((20 / 17) : ℂ) * ζ ^ 8
          + ((23 / 17) : ℂ) * ζ ^ 9
          - ((23 / 17) : ℂ) * ζ ^ 13
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
private theorem alternatingSixAmbientRow24_longPrefix79_entry06_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (6 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (6 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((12 / 17) : ℂ)
          - ((12 / 17) : ℂ) * ζ ^ 4
          - ((10 / 17) : ℂ) * ζ ^ 5
          + ((12 / 17) : ℂ) * ζ ^ 8
          + ((10 / 17) : ℂ) * ζ ^ 9
          - ((10 / 17) : ℂ) * ζ ^ 13
          + ((23 / 17) : ℂ) * ζ ^ 15
          - ((23 / 17) : ℂ) * ζ ^ 19
          + ((12 / 17) : ℂ) * ζ ^ 20
          + ((23 / 17) : ℂ) * ζ ^ 23
          - ((12 / 17) : ℂ) * ζ ^ 24
          + ((12 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((12 / 17) : ℂ)
          - ((12 / 17) : ℂ) * ζ ^ 4
          - ((10 / 17) : ℂ) * ζ ^ 5
          + ((12 / 17) : ℂ) * ζ ^ 8
          + ((10 / 17) : ℂ) * ζ ^ 9
          - ((10 / 17) : ℂ) * ζ ^ 13
          + ((23 / 17) : ℂ) * ζ ^ 15
          - ((23 / 17) : ℂ) * ζ ^ 19
          + ((12 / 17) : ℂ) * ζ ^ 20
          + ((23 / 17) : ℂ) * ζ ^ 23
          - ((12 / 17) : ℂ) * ζ ^ 24
          + ((12 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry06_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (6 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (6 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((16 / 17) : ℂ)
          + ((16 / 17) : ℂ) * ζ ^ 4
          - ((32 / 17) : ℂ) * ζ ^ 5
          - ((16 / 17) : ℂ) * ζ ^ 8
          + ((32 / 17) : ℂ) * ζ ^ 9
          - ((32 / 17) : ℂ) * ζ ^ 13
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
          - ((32 / 17) : ℂ) * ζ ^ 5
          - ((16 / 17) : ℂ) * ζ ^ 8
          + ((32 / 17) : ℂ) * ζ ^ 9
          - ((32 / 17) : ℂ) * ζ ^ 13
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
private theorem alternatingSixAmbientRow24_longPrefix79_entry06_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (6 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (6 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((16 / 17) : ℂ)
          - ((16 / 17) : ℂ) * ζ ^ 4
          + ((32 / 17) : ℂ) * ζ ^ 5
          + ((16 / 17) : ℂ) * ζ ^ 8
          - ((32 / 17) : ℂ) * ζ ^ 9
          + ((32 / 17) : ℂ) * ζ ^ 13
          + ((8 / 17) : ℂ) * ζ ^ 15
          - ((8 / 17) : ℂ) * ζ ^ 19
          + ((16 / 17) : ℂ) * ζ ^ 20
          + ((8 / 17) : ℂ) * ζ ^ 23
          - ((16 / 17) : ℂ) * ζ ^ 24
          + ((16 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((16 / 17) : ℂ)
          - ((16 / 17) : ℂ) * ζ ^ 4
          + ((32 / 17) : ℂ) * ζ ^ 5
          + ((16 / 17) : ℂ) * ζ ^ 8
          - ((32 / 17) : ℂ) * ζ ^ 9
          + ((32 / 17) : ℂ) * ζ ^ 13
          + ((8 / 17) : ℂ) * ζ ^ 15
          - ((8 / 17) : ℂ) * ζ ^ 19
          + ((16 / 17) : ℂ) * ζ ^ 20
          + ((8 / 17) : ℂ) * ζ ^ 23
          - ((16 / 17) : ℂ) * ζ ^ 24
          + ((16 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry06_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (6 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (6 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((3 / 17) : ℂ)
          - ((3 / 17) : ℂ) * ζ ^ 4
          + ((40 / 17) : ℂ) * ζ ^ 5
          + ((3 / 17) : ℂ) * ζ ^ 8
          - ((40 / 17) : ℂ) * ζ ^ 9
          + ((40 / 17) : ℂ) * ζ ^ 13
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
          + ((40 / 17) : ℂ) * ζ ^ 5
          + ((3 / 17) : ℂ) * ζ ^ 8
          - ((40 / 17) : ℂ) * ζ ^ 9
          + ((40 / 17) : ℂ) * ζ ^ 13
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
private theorem alternatingSixAmbientRow24_longPrefix79_entry06_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (6 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (6 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((4 / 17) : ℂ)
          - ((4 / 17) : ℂ) * ζ ^ 4
          - ((26 / 17) : ℂ) * ζ ^ 5
          + ((4 / 17) : ℂ) * ζ ^ 8
          + ((26 / 17) : ℂ) * ζ ^ 9
          - ((26 / 17) : ℂ) * ζ ^ 13
          + ((19 / 17) : ℂ) * ζ ^ 15
          - ((19 / 17) : ℂ) * ζ ^ 19
          + ((4 / 17) : ℂ) * ζ ^ 20
          + ((19 / 17) : ℂ) * ζ ^ 23
          - ((4 / 17) : ℂ) * ζ ^ 24
          + ((4 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((4 / 17) : ℂ)
          - ((4 / 17) : ℂ) * ζ ^ 4
          - ((26 / 17) : ℂ) * ζ ^ 5
          + ((4 / 17) : ℂ) * ζ ^ 8
          + ((26 / 17) : ℂ) * ζ ^ 9
          - ((26 / 17) : ℂ) * ζ ^ 13
          + ((19 / 17) : ℂ) * ζ ^ 15
          - ((19 / 17) : ℂ) * ζ ^ 19
          + ((4 / 17) : ℂ) * ζ ^ 20
          + ((19 / 17) : ℂ) * ζ ^ 23
          - ((4 / 17) : ℂ) * ζ ^ 24
          + ((4 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry06_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (6 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (6 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((36 / 17) : ℂ)
          - ((36 / 17) : ℂ) * ζ ^ 4
          + ((4 / 17) : ℂ) * ζ ^ 5
          + ((36 / 17) : ℂ) * ζ ^ 8
          - ((4 / 17) : ℂ) * ζ ^ 9
          + ((4 / 17) : ℂ) * ζ ^ 13
          + ((35 / 17) : ℂ) * ζ ^ 15
          - ((35 / 17) : ℂ) * ζ ^ 19
          + ((36 / 17) : ℂ) * ζ ^ 20
          + ((35 / 17) : ℂ) * ζ ^ 23
          - ((36 / 17) : ℂ) * ζ ^ 24
          + ((36 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((36 / 17) : ℂ)
          - ((36 / 17) : ℂ) * ζ ^ 4
          + ((4 / 17) : ℂ) * ζ ^ 5
          + ((36 / 17) : ℂ) * ζ ^ 8
          - ((4 / 17) : ℂ) * ζ ^ 9
          + ((4 / 17) : ℂ) * ζ ^ 13
          + ((35 / 17) : ℂ) * ζ ^ 15
          - ((35 / 17) : ℂ) * ζ ^ 19
          + ((36 / 17) : ℂ) * ζ ^ 20
          + ((35 / 17) : ℂ) * ζ ^ 23
          - ((36 / 17) : ℂ) * ζ ^ 24
          + ((36 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry06_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (6 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (6 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((6 / 17) : ℂ)
          + ((6 / 17) : ℂ) * ζ ^ 4
          - ((12 / 17) : ℂ) * ζ ^ 5
          - ((6 / 17) : ℂ) * ζ ^ 8
          + ((12 / 17) : ℂ) * ζ ^ 9
          - ((12 / 17) : ℂ) * ζ ^ 13
          - ((20 / 17) : ℂ) * ζ ^ 15
          + ((20 / 17) : ℂ) * ζ ^ 19
          - ((6 / 17) : ℂ) * ζ ^ 20
          - ((20 / 17) : ℂ) * ζ ^ 23
          + ((6 / 17) : ℂ) * ζ ^ 24
          - ((6 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((6 / 17) : ℂ)
          + ((6 / 17) : ℂ) * ζ ^ 4
          - ((12 / 17) : ℂ) * ζ ^ 5
          - ((6 / 17) : ℂ) * ζ ^ 8
          + ((12 / 17) : ℂ) * ζ ^ 9
          - ((12 / 17) : ℂ) * ζ ^ 13
          - ((20 / 17) : ℂ) * ζ ^ 15
          + ((20 / 17) : ℂ) * ζ ^ 19
          - ((6 / 17) : ℂ) * ζ ^ 20
          - ((20 / 17) : ℂ) * ζ ^ 23
          + ((6 / 17) : ℂ) * ζ ^ 24
          - ((6 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry06_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (6 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (6 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
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
          + ((29 / 17) : ℂ) * ζ ^ 15
          - ((29 / 17) : ℂ) * ζ ^ 19
          + ((7 / 17) : ℂ) * ζ ^ 20
          + ((29 / 17) : ℂ) * ζ ^ 23
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
          + ((29 / 17) : ℂ) * ζ ^ 15
          - ((29 / 17) : ℂ) * ζ ^ 19
          + ((7 / 17) : ℂ) * ζ ^ 20
          + ((29 / 17) : ℂ) * ζ ^ 23
          - ((7 / 17) : ℂ) * ζ ^ 24
          + ((7 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry06_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (6 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (6 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (-ζ ^ 15 + ζ ^ 19 - ζ ^ 23) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(-ζ ^ 15 + ζ ^ 19 - ζ ^ 23)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry07_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (7 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (7 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry07_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (7 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (7 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry07_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (7 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (7 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry07_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (7 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (7 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry07_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (7 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (7 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry07_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (7 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (7 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry07_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (7 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (7 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry07_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (7 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (7 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry07_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (7 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (7 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 + ζ ^ 20 - ζ ^ 24 + ζ ^ 28) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-((1 : ℂ) - ζ ^ 4 + ζ ^ 8 + ζ ^ 20 - ζ ^ 24 + ζ ^ 28)) *
        alternatingSixComplexCyclotomicRoot_relation

-- `simp` may close before the zero-goal-safe `all_goals ring` fallback runs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry07_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (7 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (7 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  all_goals ring

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry08_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (8 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (8 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((3 / 34) : ℂ)
          + ((3 / 34) : ℂ) * ζ ^ 4
          + ((62 / 17) : ℂ) * ζ ^ 5
          - ((3 / 34) : ℂ) * ζ ^ 8
          - ((62 / 17) : ℂ) * ζ ^ 9
          + ((5 / 34) : ℂ) * ζ ^ 10
          + ((62 / 17) : ℂ) * ζ ^ 13
          - ((5 / 34) : ℂ) * ζ ^ 14
          - ((13 / 34) : ℂ) * ζ ^ 15
          + ((5 / 34) : ℂ) * ζ ^ 18
          + ((13 / 34) : ℂ) * ζ ^ 19
          - ((23 / 17) : ℂ) * ζ ^ 20
          - ((13 / 34) : ℂ) * ζ ^ 23
          + ((23 / 17) : ℂ) * ζ ^ 24
          - ((23 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((3 / 34) : ℂ)
          + ((3 / 34) : ℂ) * ζ ^ 4
          + ((62 / 17) : ℂ) * ζ ^ 5
          - ((3 / 34) : ℂ) * ζ ^ 8
          - ((62 / 17) : ℂ) * ζ ^ 9
          + ((5 / 34) : ℂ) * ζ ^ 10
          + ((62 / 17) : ℂ) * ζ ^ 13
          - ((5 / 34) : ℂ) * ζ ^ 14
          - ((13 / 34) : ℂ) * ζ ^ 15
          + ((5 / 34) : ℂ) * ζ ^ 18
          + ((13 / 34) : ℂ) * ζ ^ 19
          - ((23 / 17) : ℂ) * ζ ^ 20
          - ((13 / 34) : ℂ) * ζ ^ 23
          + ((23 / 17) : ℂ) * ζ ^ 24
          - ((23 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry08_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (8 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (8 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((24 / 17) : ℂ)
          + ((24 / 17) : ℂ) * ζ ^ 4
          - ((19 / 17) : ℂ) * ζ ^ 5
          - ((24 / 17) : ℂ) * ζ ^ 8
          + ((19 / 17) : ℂ) * ζ ^ 9
          + ((7 / 17) : ℂ) * ζ ^ 10
          - ((19 / 17) : ℂ) * ζ ^ 13
          - ((7 / 17) : ℂ) * ζ ^ 14
          + ((28 / 17) : ℂ) * ζ ^ 15
          + ((7 / 17) : ℂ) * ζ ^ 18
          - ((28 / 17) : ℂ) * ζ ^ 19
          + ((11 / 17) : ℂ) * ζ ^ 20
          + ((28 / 17) : ℂ) * ζ ^ 23
          - ((11 / 17) : ℂ) * ζ ^ 24
          + ((11 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((24 / 17) : ℂ)
          + ((24 / 17) : ℂ) * ζ ^ 4
          - ((19 / 17) : ℂ) * ζ ^ 5
          - ((24 / 17) : ℂ) * ζ ^ 8
          + ((19 / 17) : ℂ) * ζ ^ 9
          + ((7 / 17) : ℂ) * ζ ^ 10
          - ((19 / 17) : ℂ) * ζ ^ 13
          - ((7 / 17) : ℂ) * ζ ^ 14
          + ((28 / 17) : ℂ) * ζ ^ 15
          + ((7 / 17) : ℂ) * ζ ^ 18
          - ((28 / 17) : ℂ) * ζ ^ 19
          + ((11 / 17) : ℂ) * ζ ^ 20
          + ((28 / 17) : ℂ) * ζ ^ 23
          - ((11 / 17) : ℂ) * ζ ^ 24
          + ((11 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry08_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (8 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (8 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((7 / 17) : ℂ)
          - ((7 / 17) : ℂ) * ζ ^ 4
          + ((36 / 17) : ℂ) * ζ ^ 5
          + ((7 / 17) : ℂ) * ζ ^ 8
          - ((36 / 17) : ℂ) * ζ ^ 9
          + ((10 / 17) : ℂ) * ζ ^ 10
          + ((36 / 17) : ℂ) * ζ ^ 13
          - ((10 / 17) : ℂ) * ζ ^ 14
          + (5 : ℂ) * ζ ^ 15
          + ((10 / 17) : ℂ) * ζ ^ 18
          - (5 : ℂ) * ζ ^ 19
          + ((28 / 17) : ℂ) * ζ ^ 20
          + (5 : ℂ) * ζ ^ 23
          - ((28 / 17) : ℂ) * ζ ^ 24
          + ((28 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((7 / 17) : ℂ)
          - ((7 / 17) : ℂ) * ζ ^ 4
          + ((36 / 17) : ℂ) * ζ ^ 5
          + ((7 / 17) : ℂ) * ζ ^ 8
          - ((36 / 17) : ℂ) * ζ ^ 9
          + ((10 / 17) : ℂ) * ζ ^ 10
          + ((36 / 17) : ℂ) * ζ ^ 13
          - ((10 / 17) : ℂ) * ζ ^ 14
          + (5 : ℂ) * ζ ^ 15
          + ((10 / 17) : ℂ) * ζ ^ 18
          - (5 : ℂ) * ζ ^ 19
          + ((28 / 17) : ℂ) * ζ ^ 20
          + (5 : ℂ) * ζ ^ 23
          - ((28 / 17) : ℂ) * ζ ^ 24
          + ((28 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry08_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (8 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (8 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((69 / 34) : ℂ)
          - ((69 / 34) : ℂ) * ζ ^ 4
          - ((82 / 17) : ℂ) * ζ ^ 5
          + ((69 / 34) : ℂ) * ζ ^ 8
          + ((82 / 17) : ℂ) * ζ ^ 9
          - ((43 / 34) : ℂ) * ζ ^ 10
          - ((82 / 17) : ℂ) * ζ ^ 13
          + ((43 / 34) : ℂ) * ζ ^ 14
          - ((25 / 34) : ℂ) * ζ ^ 15
          - ((43 / 34) : ℂ) * ζ ^ 18
          + ((25 / 34) : ℂ) * ζ ^ 19
          + ((44 / 17) : ℂ) * ζ ^ 20
          - ((25 / 34) : ℂ) * ζ ^ 23
          - ((44 / 17) : ℂ) * ζ ^ 24
          + ((44 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((69 / 34) : ℂ)
          - ((69 / 34) : ℂ) * ζ ^ 4
          - ((82 / 17) : ℂ) * ζ ^ 5
          + ((69 / 34) : ℂ) * ζ ^ 8
          + ((82 / 17) : ℂ) * ζ ^ 9
          - ((43 / 34) : ℂ) * ζ ^ 10
          - ((82 / 17) : ℂ) * ζ ^ 13
          + ((43 / 34) : ℂ) * ζ ^ 14
          - ((25 / 34) : ℂ) * ζ ^ 15
          - ((43 / 34) : ℂ) * ζ ^ 18
          + ((25 / 34) : ℂ) * ζ ^ 19
          + ((44 / 17) : ℂ) * ζ ^ 20
          - ((25 / 34) : ℂ) * ζ ^ 23
          - ((44 / 17) : ℂ) * ζ ^ 24
          + ((44 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry08_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (8 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (8 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((60 / 17) : ℂ)
          - ((60 / 17) : ℂ) * ζ ^ 4
          - ((113 / 17) : ℂ) * ζ ^ 5
          + ((60 / 17) : ℂ) * ζ ^ 8
          + ((113 / 17) : ℂ) * ζ ^ 9
          - ((24 / 17) : ℂ) * ζ ^ 10
          - ((113 / 17) : ℂ) * ζ ^ 13
          + ((24 / 17) : ℂ) * ζ ^ 14
          - ((57 / 17) : ℂ) * ζ ^ 15
          - ((24 / 17) : ℂ) * ζ ^ 18
          + ((57 / 17) : ℂ) * ζ ^ 19
          + ((33 / 17) : ℂ) * ζ ^ 20
          - ((57 / 17) : ℂ) * ζ ^ 23
          - ((33 / 17) : ℂ) * ζ ^ 24
          + ((33 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((60 / 17) : ℂ)
          - ((60 / 17) : ℂ) * ζ ^ 4
          - ((113 / 17) : ℂ) * ζ ^ 5
          + ((60 / 17) : ℂ) * ζ ^ 8
          + ((113 / 17) : ℂ) * ζ ^ 9
          - ((24 / 17) : ℂ) * ζ ^ 10
          - ((113 / 17) : ℂ) * ζ ^ 13
          + ((24 / 17) : ℂ) * ζ ^ 14
          - ((57 / 17) : ℂ) * ζ ^ 15
          - ((24 / 17) : ℂ) * ζ ^ 18
          + ((57 / 17) : ℂ) * ζ ^ 19
          + ((33 / 17) : ℂ) * ζ ^ 20
          - ((57 / 17) : ℂ) * ζ ^ 23
          - ((33 / 17) : ℂ) * ζ ^ 24
          + ((33 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry08_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (8 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (8 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((77 / 34) : ℂ)
          + ((77 / 34) : ℂ) * ζ ^ 4
          + ((24 / 17) : ℂ) * ζ ^ 5
          - ((77 / 34) : ℂ) * ζ ^ 8
          - ((24 / 17) : ℂ) * ζ ^ 9
          + ((13 / 34) : ℂ) * ζ ^ 10
          + ((24 / 17) : ℂ) * ζ ^ 13
          - ((13 / 34) : ℂ) * ζ ^ 14
          + ((129 / 34) : ℂ) * ζ ^ 15
          + ((13 / 34) : ℂ) * ζ ^ 18
          - ((129 / 34) : ℂ) * ζ ^ 19
          + ((18 / 17) : ℂ) * ζ ^ 20
          + ((129 / 34) : ℂ) * ζ ^ 23
          - ((18 / 17) : ℂ) * ζ ^ 24
          + ((18 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((77 / 34) : ℂ)
          + ((77 / 34) : ℂ) * ζ ^ 4
          + ((24 / 17) : ℂ) * ζ ^ 5
          - ((77 / 34) : ℂ) * ζ ^ 8
          - ((24 / 17) : ℂ) * ζ ^ 9
          + ((13 / 34) : ℂ) * ζ ^ 10
          + ((24 / 17) : ℂ) * ζ ^ 13
          - ((13 / 34) : ℂ) * ζ ^ 14
          + ((129 / 34) : ℂ) * ζ ^ 15
          + ((13 / 34) : ℂ) * ζ ^ 18
          - ((129 / 34) : ℂ) * ζ ^ 19
          + ((18 / 17) : ℂ) * ζ ^ 20
          + ((129 / 34) : ℂ) * ζ ^ 23
          - ((18 / 17) : ℂ) * ζ ^ 24
          + ((18 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry08_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (8 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (8 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((74 / 17) : ℂ)
          + ((74 / 17) : ℂ) * ζ ^ 4
          - ((22 / 17) : ℂ) * ζ ^ 5
          - ((74 / 17) : ℂ) * ζ ^ 8
          + ((22 / 17) : ℂ) * ζ ^ 9
          + ((31 / 17) : ℂ) * ζ ^ 10
          - ((22 / 17) : ℂ) * ζ ^ 13
          - ((31 / 17) : ℂ) * ζ ^ 14
          + ((55 / 17) : ℂ) * ζ ^ 15
          + ((31 / 17) : ℂ) * ζ ^ 18
          - ((55 / 17) : ℂ) * ζ ^ 19
          + ((37 / 17) : ℂ) * ζ ^ 20
          + ((55 / 17) : ℂ) * ζ ^ 23
          - ((37 / 17) : ℂ) * ζ ^ 24
          + ((37 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((74 / 17) : ℂ)
          + ((74 / 17) : ℂ) * ζ ^ 4
          - ((22 / 17) : ℂ) * ζ ^ 5
          - ((74 / 17) : ℂ) * ζ ^ 8
          + ((22 / 17) : ℂ) * ζ ^ 9
          + ((31 / 17) : ℂ) * ζ ^ 10
          - ((22 / 17) : ℂ) * ζ ^ 13
          - ((31 / 17) : ℂ) * ζ ^ 14
          + ((55 / 17) : ℂ) * ζ ^ 15
          + ((31 / 17) : ℂ) * ζ ^ 18
          - ((55 / 17) : ℂ) * ζ ^ 19
          + ((37 / 17) : ℂ) * ζ ^ 20
          + ((55 / 17) : ℂ) * ζ ^ 23
          - ((37 / 17) : ℂ) * ζ ^ 24
          + ((37 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry08_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (8 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (8 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -(1 : ℂ)
          + ζ ^ 4
          + ((28 / 17) : ℂ) * ζ ^ 5
          - ζ ^ 8
          - ((28 / 17) : ℂ) * ζ ^ 9
          - ((12 / 17) : ℂ) * ζ ^ 10
          + ((28 / 17) : ℂ) * ζ ^ 13
          + ((12 / 17) : ℂ) * ζ ^ 14
          - ((12 / 17) : ℂ) * ζ ^ 18
          - ((54 / 17) : ℂ) * ζ ^ 20
          + ((54 / 17) : ℂ) * ζ ^ 24
          - ((54 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -(1 : ℂ)
          + ζ ^ 4
          + ((28 / 17) : ℂ) * ζ ^ 5
          - ζ ^ 8
          - ((28 / 17) : ℂ) * ζ ^ 9
          - ((12 / 17) : ℂ) * ζ ^ 10
          + ((28 / 17) : ℂ) * ζ ^ 13
          + ((12 / 17) : ℂ) * ζ ^ 14
          - ((12 / 17) : ℂ) * ζ ^ 18
          - ((54 / 17) : ℂ) * ζ ^ 20
          + ((54 / 17) : ℂ) * ζ ^ 24
          - ((54 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry08_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (8 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (8 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((26 / 17) : ℂ)
          - ((26 / 17) : ℂ) * ζ ^ 4
          - ((9 / 17) : ℂ) * ζ ^ 5
          + ((26 / 17) : ℂ) * ζ ^ 8
          + ((9 / 17) : ℂ) * ζ ^ 9
          + ((14 / 17) : ℂ) * ζ ^ 10
          - ((9 / 17) : ℂ) * ζ ^ 13
          - ((14 / 17) : ℂ) * ζ ^ 14
          - ((6 / 17) : ℂ) * ζ ^ 15
          + ((14 / 17) : ℂ) * ζ ^ 18
          + ((6 / 17) : ℂ) * ζ ^ 19
          + (3 : ℂ) * ζ ^ 20
          - ((6 / 17) : ℂ) * ζ ^ 23
          - (3 : ℂ) * ζ ^ 24
          + (3 : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((26 / 17) : ℂ)
          - ((26 / 17) : ℂ) * ζ ^ 4
          - ((9 / 17) : ℂ) * ζ ^ 5
          + ((26 / 17) : ℂ) * ζ ^ 8
          + ((9 / 17) : ℂ) * ζ ^ 9
          + ((14 / 17) : ℂ) * ζ ^ 10
          - ((9 / 17) : ℂ) * ζ ^ 13
          - ((14 / 17) : ℂ) * ζ ^ 14
          - ((6 / 17) : ℂ) * ζ ^ 15
          + ((14 / 17) : ℂ) * ζ ^ 18
          + ((6 / 17) : ℂ) * ζ ^ 19
          + (3 : ℂ) * ζ ^ 20
          - ((6 / 17) : ℂ) * ζ ^ 23
          - (3 : ℂ) * ζ ^ 24
          + (3 : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry08_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (8 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (8 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((21 / 34) : ℂ)
          + ((21 / 34) : ℂ) * ζ ^ 4
          - ((1 / 17) : ℂ) * ζ ^ 5
          - ((21 / 34) : ℂ) * ζ ^ 8
          + ((1 / 17) : ℂ) * ζ ^ 9
          - ((5 / 34) : ℂ) * ζ ^ 10
          - ((1 / 17) : ℂ) * ζ ^ 13
          + ((5 / 34) : ℂ) * ζ ^ 14
          + ((81 / 34) : ℂ) * ζ ^ 15
          - ((5 / 34) : ℂ) * ζ ^ 18
          - ((81 / 34) : ℂ) * ζ ^ 19
          - ((11 / 17) : ℂ) * ζ ^ 20
          + ((81 / 34) : ℂ) * ζ ^ 23
          + ((11 / 17) : ℂ) * ζ ^ 24
          - ((11 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((21 / 34) : ℂ)
          + ((21 / 34) : ℂ) * ζ ^ 4
          - ((1 / 17) : ℂ) * ζ ^ 5
          - ((21 / 34) : ℂ) * ζ ^ 8
          + ((1 / 17) : ℂ) * ζ ^ 9
          - ((5 / 34) : ℂ) * ζ ^ 10
          - ((1 / 17) : ℂ) * ζ ^ 13
          + ((5 / 34) : ℂ) * ζ ^ 14
          + ((81 / 34) : ℂ) * ζ ^ 15
          - ((5 / 34) : ℂ) * ζ ^ 18
          - ((81 / 34) : ℂ) * ζ ^ 19
          - ((11 / 17) : ℂ) * ζ ^ 20
          + ((81 / 34) : ℂ) * ζ ^ 23
          + ((11 / 17) : ℂ) * ζ ^ 24
          - ((11 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry09_00 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (9 : Fin 10) (0 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (9 : Fin 10) (0 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((30 / 17) : ℂ)
          - ((30 / 17) : ℂ) * ζ ^ 4
          + ((26 / 17) : ℂ) * ζ ^ 5
          + ((30 / 17) : ℂ) * ζ ^ 8
          - ((26 / 17) : ℂ) * ζ ^ 9
          + ((26 / 17) : ℂ) * ζ ^ 13
          - ((2 / 17) : ℂ) * ζ ^ 15
          + ((2 / 17) : ℂ) * ζ ^ 19
          + ((30 / 17) : ℂ) * ζ ^ 20
          - ((2 / 17) : ℂ) * ζ ^ 23
          - ((30 / 17) : ℂ) * ζ ^ 24
          + ((30 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        ((30 / 17) : ℂ)
          - ((30 / 17) : ℂ) * ζ ^ 4
          + ((26 / 17) : ℂ) * ζ ^ 5
          + ((30 / 17) : ℂ) * ζ ^ 8
          - ((26 / 17) : ℂ) * ζ ^ 9
          + ((26 / 17) : ℂ) * ζ ^ 13
          - ((2 / 17) : ℂ) * ζ ^ 15
          + ((2 / 17) : ℂ) * ζ ^ 19
          + ((30 / 17) : ℂ) * ζ ^ 20
          - ((2 / 17) : ℂ) * ζ ^ 23
          - ((30 / 17) : ℂ) * ζ ^ 24
          + ((30 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry09_01 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (9 : Fin 10) (1 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (9 : Fin 10) (1 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((18 / 17) : ℂ)
          + ((18 / 17) : ℂ) * ζ ^ 4
          - ((2 / 17) : ℂ) * ζ ^ 5
          - ((18 / 17) : ℂ) * ζ ^ 8
          + ((2 / 17) : ℂ) * ζ ^ 9
          - ((2 / 17) : ℂ) * ζ ^ 13
          - ((26 / 17) : ℂ) * ζ ^ 15
          + ((26 / 17) : ℂ) * ζ ^ 19
          - ((18 / 17) : ℂ) * ζ ^ 20
          - ((26 / 17) : ℂ) * ζ ^ 23
          + ((18 / 17) : ℂ) * ζ ^ 24
          - ((18 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((18 / 17) : ℂ)
          + ((18 / 17) : ℂ) * ζ ^ 4
          - ((2 / 17) : ℂ) * ζ ^ 5
          - ((18 / 17) : ℂ) * ζ ^ 8
          + ((2 / 17) : ℂ) * ζ ^ 9
          - ((2 / 17) : ℂ) * ζ ^ 13
          - ((26 / 17) : ℂ) * ζ ^ 15
          + ((26 / 17) : ℂ) * ζ ^ 19
          - ((18 / 17) : ℂ) * ζ ^ 20
          - ((26 / 17) : ℂ) * ζ ^ 23
          + ((18 / 17) : ℂ) * ζ ^ 24
          - ((18 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry09_02 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (9 : Fin 10) (2 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (9 : Fin 10) (2 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((10 / 17) : ℂ)
          + ((10 / 17) : ℂ) * ζ ^ 4
          + ((31 / 17) : ℂ) * ζ ^ 5
          - ((10 / 17) : ℂ) * ζ ^ 8
          - ((31 / 17) : ℂ) * ζ ^ 9
          + ((31 / 17) : ℂ) * ζ ^ 13
          - ((22 / 17) : ℂ) * ζ ^ 15
          + ((22 / 17) : ℂ) * ζ ^ 19
          - ((10 / 17) : ℂ) * ζ ^ 20
          - ((22 / 17) : ℂ) * ζ ^ 23
          + ((10 / 17) : ℂ) * ζ ^ 24
          - ((10 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((10 / 17) : ℂ)
          + ((10 / 17) : ℂ) * ζ ^ 4
          + ((31 / 17) : ℂ) * ζ ^ 5
          - ((10 / 17) : ℂ) * ζ ^ 8
          - ((31 / 17) : ℂ) * ζ ^ 9
          + ((31 / 17) : ℂ) * ζ ^ 13
          - ((22 / 17) : ℂ) * ζ ^ 15
          + ((22 / 17) : ℂ) * ζ ^ 19
          - ((10 / 17) : ℂ) * ζ ^ 20
          - ((22 / 17) : ℂ) * ζ ^ 23
          + ((10 / 17) : ℂ) * ζ ^ 24
          - ((10 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry09_03 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (9 : Fin 10) (3 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (9 : Fin 10) (3 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((24 / 17) : ℂ)
          + ((24 / 17) : ℂ) * ζ ^ 4
          - ((14 / 17) : ℂ) * ζ ^ 5
          - ((24 / 17) : ℂ) * ζ ^ 8
          + ((14 / 17) : ℂ) * ζ ^ 9
          - ((14 / 17) : ℂ) * ζ ^ 13
          + ((22 / 17) : ℂ) * ζ ^ 15
          - ((22 / 17) : ℂ) * ζ ^ 19
          - ((24 / 17) : ℂ) * ζ ^ 20
          + ((22 / 17) : ℂ) * ζ ^ 23
          + ((24 / 17) : ℂ) * ζ ^ 24
          - ((24 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((24 / 17) : ℂ)
          + ((24 / 17) : ℂ) * ζ ^ 4
          - ((14 / 17) : ℂ) * ζ ^ 5
          - ((24 / 17) : ℂ) * ζ ^ 8
          + ((14 / 17) : ℂ) * ζ ^ 9
          - ((14 / 17) : ℂ) * ζ ^ 13
          + ((22 / 17) : ℂ) * ζ ^ 15
          - ((22 / 17) : ℂ) * ζ ^ 19
          - ((24 / 17) : ℂ) * ζ ^ 20
          + ((22 / 17) : ℂ) * ζ ^ 23
          + ((24 / 17) : ℂ) * ζ ^ 24
          - ((24 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry09_04 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (9 : Fin 10) (4 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (9 : Fin 10) (4 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((13 / 17) : ℂ)
          + ((13 / 17) : ℂ) * ζ ^ 4
          - ((9 / 17) : ℂ) * ζ ^ 5
          - ((13 / 17) : ℂ) * ζ ^ 8
          + ((9 / 17) : ℂ) * ζ ^ 9
          - ((9 / 17) : ℂ) * ζ ^ 13
          + ((36 / 17) : ℂ) * ζ ^ 15
          - ((36 / 17) : ℂ) * ζ ^ 19
          - ((13 / 17) : ℂ) * ζ ^ 20
          + ((36 / 17) : ℂ) * ζ ^ 23
          + ((13 / 17) : ℂ) * ζ ^ 24
          - ((13 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((13 / 17) : ℂ)
          + ((13 / 17) : ℂ) * ζ ^ 4
          - ((9 / 17) : ℂ) * ζ ^ 5
          - ((13 / 17) : ℂ) * ζ ^ 8
          + ((9 / 17) : ℂ) * ζ ^ 9
          - ((9 / 17) : ℂ) * ζ ^ 13
          + ((36 / 17) : ℂ) * ζ ^ 15
          - ((36 / 17) : ℂ) * ζ ^ 19
          - ((13 / 17) : ℂ) * ζ ^ 20
          + ((36 / 17) : ℂ) * ζ ^ 23
          + ((13 / 17) : ℂ) * ζ ^ 24
          - ((13 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry09_05 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (9 : Fin 10) (5 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (9 : Fin 10) (5 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((6 / 17) : ℂ)
          + ((6 / 17) : ℂ) * ζ ^ 4
          + ((5 / 17) : ℂ) * ζ ^ 5
          - ((6 / 17) : ℂ) * ζ ^ 8
          - ((5 / 17) : ℂ) * ζ ^ 9
          + ((5 / 17) : ℂ) * ζ ^ 13
          - ((37 / 17) : ℂ) * ζ ^ 15
          + ((37 / 17) : ℂ) * ζ ^ 19
          - ((6 / 17) : ℂ) * ζ ^ 20
          - ((37 / 17) : ℂ) * ζ ^ 23
          + ((6 / 17) : ℂ) * ζ ^ 24
          - ((6 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((6 / 17) : ℂ)
          + ((6 / 17) : ℂ) * ζ ^ 4
          + ((5 / 17) : ℂ) * ζ ^ 5
          - ((6 / 17) : ℂ) * ζ ^ 8
          - ((5 / 17) : ℂ) * ζ ^ 9
          + ((5 / 17) : ℂ) * ζ ^ 13
          - ((37 / 17) : ℂ) * ζ ^ 15
          + ((37 / 17) : ℂ) * ζ ^ 19
          - ((6 / 17) : ℂ) * ζ ^ 20
          - ((37 / 17) : ℂ) * ζ ^ 23
          + ((6 / 17) : ℂ) * ζ ^ 24
          - ((6 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry09_06 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (9 : Fin 10) (6 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (9 : Fin 10) (6 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((37 / 17) : ℂ)
          + ((37 / 17) : ℂ) * ζ ^ 4
          - ((23 / 17) : ℂ) * ζ ^ 5
          - ((37 / 17) : ℂ) * ζ ^ 8
          + ((23 / 17) : ℂ) * ζ ^ 9
          - ((23 / 17) : ℂ) * ζ ^ 13
          - ((27 / 17) : ℂ) * ζ ^ 15
          + ((27 / 17) : ℂ) * ζ ^ 19
          - ((37 / 17) : ℂ) * ζ ^ 20
          - ((27 / 17) : ℂ) * ζ ^ 23
          + ((37 / 17) : ℂ) * ζ ^ 24
          - ((37 / 17) : ℂ) * ζ ^ 28
      ) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(
        -((37 / 17) : ℂ)
          + ((37 / 17) : ℂ) * ζ ^ 4
          - ((23 / 17) : ℂ) * ζ ^ 5
          - ((37 / 17) : ℂ) * ζ ^ 8
          + ((23 / 17) : ℂ) * ζ ^ 9
          - ((23 / 17) : ℂ) * ζ ^ 13
          - ((27 / 17) : ℂ) * ζ ^ 15
          + ((27 / 17) : ℂ) * ζ ^ 19
          - ((37 / 17) : ℂ) * ζ ^ 20
          - ((27 / 17) : ℂ) * ζ ^ 23
          + ((37 / 17) : ℂ) * ζ ^ 24
          - ((37 / 17) : ℂ) * ζ ^ 28
      )) *
        alternatingSixComplexCyclotomicRoot_relation

-- Cyclotomic reduction uses a generated fallback with the opposite sign.
set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem alternatingSixAmbientRow24_longPrefix79_entry09_07 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (9 : Fin 10) (7 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (9 : Fin 10) (7 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        ((26 / 17) : ℂ)
          - ((26 / 17) : ℂ) * ζ ^ 4
          + ((1 / 17) : ℂ) * ζ ^ 5
          + ((26 / 17) : ℂ) * ζ ^ 8
          - ((1 / 17) : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 13
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
          + ((1 / 17) : ℂ) * ζ ^ 5
          + ((26 / 17) : ℂ) * ζ ^ 8
          - ((1 / 17) : ℂ) * ζ ^ 9
          + ((1 / 17) : ℂ) * ζ ^ 13
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
private theorem alternatingSixAmbientRow24_longPrefix79_entry09_08 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (9 : Fin 10) (8 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (9 : Fin 10) (8 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (
        -((19 / 17) : ℂ)
          + ((19 / 17) : ℂ) * ζ ^ 4
          - ((21 / 17) : ℂ) * ζ ^ 5
          - ((19 / 17) : ℂ) * ζ ^ 8
          + ((21 / 17) : ℂ) * ζ ^ 9
          - ((21 / 17) : ℂ) * ζ ^ 13
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
          - ((21 / 17) : ℂ) * ζ ^ 5
          - ((19 / 17) : ℂ) * ζ ^ 8
          + ((21 / 17) : ℂ) * ζ ^ 9
          - ((21 / 17) : ℂ) * ζ ^ 13
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
private theorem alternatingSixAmbientRow24_longPrefix79_entry09_09 :
    (alternatingSixAmbientRow24LongMatrixAB
        * alternatingSixAmbientRow24LongMatrixABBB)
          (9 : Fin 10) (9 : Fin 10) =
      alternatingSixAmbientRow24LongPrefix79
        (9 : Fin 10) (9 : Fin 10) := by
  rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow24LongMatrixAB,
    alternatingSixAmbientRow24LongMatrixABBB,
    alternatingSixAmbientRow24LongPrefix79,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ
  ]
  first
  | linear_combination
      (ζ ^ 5 - ζ ^ 9 + ζ ^ 13 - ζ ^ 15 + ζ ^ 19 - ζ ^ 23) *
        alternatingSixComplexCyclotomicRoot_relation
  | linear_combination
      (-(ζ ^ 5 - ζ ^ 9 + ζ ^ 13 - ζ ^ 15 + ζ ^ 19 - ζ ^ 23)) *
        alternatingSixComplexCyclotomicRoot_relation

theorem alternatingSixAmbientRow24_longPrefix79_mul :
    alternatingSixAmbientRow24LongMatrixAB *
        alternatingSixAmbientRow24LongMatrixABBB =
      alternatingSixAmbientRow24LongPrefix79 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact alternatingSixAmbientRow24_longPrefix79_entry00_00
  · exact alternatingSixAmbientRow24_longPrefix79_entry00_01
  · exact alternatingSixAmbientRow24_longPrefix79_entry00_02
  · exact alternatingSixAmbientRow24_longPrefix79_entry00_03
  · exact alternatingSixAmbientRow24_longPrefix79_entry00_04
  · exact alternatingSixAmbientRow24_longPrefix79_entry00_05
  · exact alternatingSixAmbientRow24_longPrefix79_entry00_06
  · exact alternatingSixAmbientRow24_longPrefix79_entry00_07
  · exact alternatingSixAmbientRow24_longPrefix79_entry00_08
  · exact alternatingSixAmbientRow24_longPrefix79_entry00_09
  · exact alternatingSixAmbientRow24_longPrefix79_entry01_00
  · exact alternatingSixAmbientRow24_longPrefix79_entry01_01
  · exact alternatingSixAmbientRow24_longPrefix79_entry01_02
  · exact alternatingSixAmbientRow24_longPrefix79_entry01_03
  · exact alternatingSixAmbientRow24_longPrefix79_entry01_04
  · exact alternatingSixAmbientRow24_longPrefix79_entry01_05
  · exact alternatingSixAmbientRow24_longPrefix79_entry01_06
  · exact alternatingSixAmbientRow24_longPrefix79_entry01_07
  · exact alternatingSixAmbientRow24_longPrefix79_entry01_08
  · exact alternatingSixAmbientRow24_longPrefix79_entry01_09
  · exact alternatingSixAmbientRow24_longPrefix79_entry02_00
  · exact alternatingSixAmbientRow24_longPrefix79_entry02_01
  · exact alternatingSixAmbientRow24_longPrefix79_entry02_02
  · exact alternatingSixAmbientRow24_longPrefix79_entry02_03
  · exact alternatingSixAmbientRow24_longPrefix79_entry02_04
  · exact alternatingSixAmbientRow24_longPrefix79_entry02_05
  · exact alternatingSixAmbientRow24_longPrefix79_entry02_06
  · exact alternatingSixAmbientRow24_longPrefix79_entry02_07
  · exact alternatingSixAmbientRow24_longPrefix79_entry02_08
  · exact alternatingSixAmbientRow24_longPrefix79_entry02_09
  · exact alternatingSixAmbientRow24_longPrefix79_entry03_00
  · exact alternatingSixAmbientRow24_longPrefix79_entry03_01
  · exact alternatingSixAmbientRow24_longPrefix79_entry03_02
  · exact alternatingSixAmbientRow24_longPrefix79_entry03_03
  · exact alternatingSixAmbientRow24_longPrefix79_entry03_04
  · exact alternatingSixAmbientRow24_longPrefix79_entry03_05
  · exact alternatingSixAmbientRow24_longPrefix79_entry03_06
  · exact alternatingSixAmbientRow24_longPrefix79_entry03_07
  · exact alternatingSixAmbientRow24_longPrefix79_entry03_08
  · exact alternatingSixAmbientRow24_longPrefix79_entry03_09
  · exact alternatingSixAmbientRow24_longPrefix79_entry04_00
  · exact alternatingSixAmbientRow24_longPrefix79_entry04_01
  · exact alternatingSixAmbientRow24_longPrefix79_entry04_02
  · exact alternatingSixAmbientRow24_longPrefix79_entry04_03
  · exact alternatingSixAmbientRow24_longPrefix79_entry04_04
  · exact alternatingSixAmbientRow24_longPrefix79_entry04_05
  · exact alternatingSixAmbientRow24_longPrefix79_entry04_06
  · exact alternatingSixAmbientRow24_longPrefix79_entry04_07
  · exact alternatingSixAmbientRow24_longPrefix79_entry04_08
  · exact alternatingSixAmbientRow24_longPrefix79_entry04_09
  · exact alternatingSixAmbientRow24_longPrefix79_entry05_00
  · exact alternatingSixAmbientRow24_longPrefix79_entry05_01
  · exact alternatingSixAmbientRow24_longPrefix79_entry05_02
  · exact alternatingSixAmbientRow24_longPrefix79_entry05_03
  · exact alternatingSixAmbientRow24_longPrefix79_entry05_04
  · exact alternatingSixAmbientRow24_longPrefix79_entry05_05
  · exact alternatingSixAmbientRow24_longPrefix79_entry05_06
  · exact alternatingSixAmbientRow24_longPrefix79_entry05_07
  · exact alternatingSixAmbientRow24_longPrefix79_entry05_08
  · exact alternatingSixAmbientRow24_longPrefix79_entry05_09
  · exact alternatingSixAmbientRow24_longPrefix79_entry06_00
  · exact alternatingSixAmbientRow24_longPrefix79_entry06_01
  · exact alternatingSixAmbientRow24_longPrefix79_entry06_02
  · exact alternatingSixAmbientRow24_longPrefix79_entry06_03
  · exact alternatingSixAmbientRow24_longPrefix79_entry06_04
  · exact alternatingSixAmbientRow24_longPrefix79_entry06_05
  · exact alternatingSixAmbientRow24_longPrefix79_entry06_06
  · exact alternatingSixAmbientRow24_longPrefix79_entry06_07
  · exact alternatingSixAmbientRow24_longPrefix79_entry06_08
  · exact alternatingSixAmbientRow24_longPrefix79_entry06_09
  · exact alternatingSixAmbientRow24_longPrefix79_entry07_00
  · exact alternatingSixAmbientRow24_longPrefix79_entry07_01
  · exact alternatingSixAmbientRow24_longPrefix79_entry07_02
  · exact alternatingSixAmbientRow24_longPrefix79_entry07_03
  · exact alternatingSixAmbientRow24_longPrefix79_entry07_04
  · exact alternatingSixAmbientRow24_longPrefix79_entry07_05
  · exact alternatingSixAmbientRow24_longPrefix79_entry07_06
  · exact alternatingSixAmbientRow24_longPrefix79_entry07_07
  · exact alternatingSixAmbientRow24_longPrefix79_entry07_08
  · exact alternatingSixAmbientRow24_longPrefix79_entry07_09
  · exact alternatingSixAmbientRow24_longPrefix79_entry08_00
  · exact alternatingSixAmbientRow24_longPrefix79_entry08_01
  · exact alternatingSixAmbientRow24_longPrefix79_entry08_02
  · exact alternatingSixAmbientRow24_longPrefix79_entry08_03
  · exact alternatingSixAmbientRow24_longPrefix79_entry08_04
  · exact alternatingSixAmbientRow24_longPrefix79_entry08_05
  · exact alternatingSixAmbientRow24_longPrefix79_entry08_06
  · exact alternatingSixAmbientRow24_longPrefix79_entry08_07
  · exact alternatingSixAmbientRow24_longPrefix79_entry08_08
  · exact alternatingSixAmbientRow24_longPrefix79_entry08_09
  · exact alternatingSixAmbientRow24_longPrefix79_entry09_00
  · exact alternatingSixAmbientRow24_longPrefix79_entry09_01
  · exact alternatingSixAmbientRow24_longPrefix79_entry09_02
  · exact alternatingSixAmbientRow24_longPrefix79_entry09_03
  · exact alternatingSixAmbientRow24_longPrefix79_entry09_04
  · exact alternatingSixAmbientRow24_longPrefix79_entry09_05
  · exact alternatingSixAmbientRow24_longPrefix79_entry09_06
  · exact alternatingSixAmbientRow24_longPrefix79_entry09_07
  · exact alternatingSixAmbientRow24_longPrefix79_entry09_08
  · exact alternatingSixAmbientRow24_longPrefix79_entry09_09

end InductiveMcKay
end McKayConjecture
