/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixDegreeFourSixEigenvalues
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixDataDegreeFourSix

/-!
# Checked diagonal data for ambient row 07

This generated module records an exact eigenbasis for the second generator
and the first generator in that basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenvalue block labels for row 07. -/
def alternatingSixAmbientRow07EigenvalueLabel :
    Fin 4 → Fin 4 :=
  ![0, 1, 2, 3]

/-- Second-generator eigenvalues, including their multiplicities. -/
def alternatingSixAmbientRow07GeneratorBEigenvalue :
    Fin 4 → ℂ :=
  fun i ↦
    alternatingSixOrderEightOddEigenvalue
      (alternatingSixAmbientRow07EigenvalueLabel i)

/-- Diagonal form of the row 07 second generator. -/
def alternatingSixAmbientRow07GeneratorBDiagonal :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal
    alternatingSixAmbientRow07GeneratorBEigenvalue

/-- Checked eigenbasis for the row 07 second generator. -/
def alternatingSixAmbientRow07Eigenbasis :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [(1, 0), (-1, 3), (1, 5), (-1, 7), (-1, 15), (1, 19), (-1, 20), (1, 23), (1, 30), (-1, 31)],
      alternatingSixCyclotomicValue [(1, 0), (1, 3), (1, 5), (1, 7), (-1, 15), (-1, 19), (-1, 20), (-1, 23), (-2, 25), (-1, 30), (1, 31)],
      alternatingSixCyclotomicValue [(1, 0), (1, 3), (-1, 5), (1, 7), (1, 15), (-1, 19), (-1, 20), (-1, 23), (1, 30), (1, 31)],
      alternatingSixCyclotomicValue [(1, 0), (-1, 3), (-1, 5), (-1, 7), (1, 15), (1, 19), (-1, 20), (1, 23), (2, 25), (-1, 30), (-1, 31)]],
    ![alternatingSixCyclotomicValue [(-1, 0), (1, 10), (1, 20), (-1, 25), (-1, 30)],
      alternatingSixCyclotomicValue [(-1, 0), (-1, 3), (-1, 7), (-1, 10), (1, 19), (1, 20), (1, 23), (1, 30), (-1, 31)],
      alternatingSixCyclotomicValue [(-1, 0), (1, 10), (1, 20), (1, 25), (-1, 30)],
      alternatingSixCyclotomicValue [(-1, 0), (1, 3), (1, 7), (-1, 10), (-1, 19), (1, 20), (-1, 23), (1, 30), (1, 31)]],
    ![alternatingSixCyclotomicValue [(-1, 0), (1, 15), (1, 20), (-1, 25)],
      alternatingSixCyclotomicValue [(-1, 0), (-1, 3), (-1, 5), (-1, 7), (1, 19), (1, 20), (1, 23), (1, 25), (-1, 31)],
      alternatingSixCyclotomicValue [(-1, 0), (-1, 15), (1, 20), (1, 25)],
      alternatingSixCyclotomicValue [(-1, 0), (1, 3), (1, 5), (1, 7), (-1, 19), (1, 20), (-1, 23), (-1, 25), (1, 31)]],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)]]
  ]

/-- Checked inverse of the row 07 eigenbasis. -/
def alternatingSixAmbientRow07EigenbasisInverse :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((-1 / 6), 3), ((-1 / 6), 5), ((-1 / 6), 7), ((-1 / 12), 10), ((1 / 12), 15), ((1 / 6), 19), ((1 / 6), 23), ((1 / 12), 25), ((-1 / 12), 30), ((-1 / 6), 31)],
      alternatingSixCyclotomicValue [((-1 / 12), 3), ((-1 / 12), 5), ((-1 / 12), 7), ((1 / 12), 10), ((1 / 6), 15), ((1 / 12), 19), ((1 / 12), 23), ((1 / 6), 25), ((1 / 12), 30), ((-1 / 12), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 3), ((-1 / 4), 7), ((-1 / 4), 10), ((1 / 4), 15), ((1 / 4), 19), ((1 / 4), 23), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 6), 3), ((1 / 6), 5), ((1 / 6), 7), ((1 / 12), 10), ((1 / 6), 15), ((-1 / 6), 19), ((-1 / 6), 23), ((-1 / 12), 25), ((1 / 12), 30), ((1 / 6), 31)]],
    ![alternatingSixCyclotomicValue [((-1 / 12), 3), ((-1 / 12), 5), ((-1 / 12), 7), ((1 / 12), 10), ((1 / 6), 15), ((1 / 12), 19), ((1 / 12), 23), ((-1 / 12), 25), ((1 / 12), 30), ((-1 / 12), 31)],
      alternatingSixCyclotomicValue [((1 / 12), 3), ((-1 / 6), 5), ((1 / 12), 7), ((-1 / 12), 10), ((1 / 12), 15), ((-1 / 12), 19), ((-1 / 12), 23), ((1 / 12), 25), ((-1 / 12), 30), ((1 / 12), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 5), ((1 / 4), 10)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 12), 3), ((-1 / 6), 5), ((1 / 12), 7), ((-1 / 12), 10), ((-1 / 6), 15), ((-1 / 12), 19), ((-1 / 12), 23), ((1 / 3), 25), ((-1 / 12), 30), ((1 / 12), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 6), 3), ((1 / 6), 5), ((1 / 6), 7), ((-1 / 12), 10), ((-1 / 12), 15), ((-1 / 6), 19), ((-1 / 6), 23), ((-1 / 12), 25), ((-1 / 12), 30), ((1 / 6), 31)],
      alternatingSixCyclotomicValue [((1 / 12), 3), ((1 / 12), 5), ((1 / 12), 7), ((1 / 12), 10), ((-1 / 6), 15), ((-1 / 12), 19), ((-1 / 12), 23), ((-1 / 6), 25), ((1 / 12), 30), ((1 / 12), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 3), ((1 / 4), 7), ((-1 / 4), 10), ((-1 / 4), 15), ((-1 / 4), 19), ((-1 / 4), 23), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 6), 3), ((-1 / 6), 5), ((-1 / 6), 7), ((1 / 12), 10), ((-1 / 6), 15), ((1 / 6), 19), ((1 / 6), 23), ((1 / 12), 25), ((1 / 12), 30), ((-1 / 6), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 12), 3), ((1 / 12), 5), ((1 / 12), 7), ((1 / 12), 10), ((-1 / 6), 15), ((-1 / 12), 19), ((-1 / 12), 23), ((1 / 12), 25), ((1 / 12), 30), ((1 / 12), 31)],
      alternatingSixCyclotomicValue [((-1 / 12), 3), ((1 / 6), 5), ((-1 / 12), 7), ((-1 / 12), 10), ((-1 / 12), 15), ((1 / 12), 19), ((1 / 12), 23), ((-1 / 12), 25), ((-1 / 12), 30), ((-1 / 12), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 5), ((1 / 4), 10)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 12), 3), ((1 / 6), 5), ((-1 / 12), 7), ((-1 / 12), 10), ((1 / 6), 15), ((1 / 12), 19), ((1 / 12), 23), ((-1 / 3), 25), ((-1 / 12), 30), ((-1 / 12), 31)]]
  ]

/-- The row 07 first generator in the checked diagonal basis. -/
def alternatingSixAmbientRow07TransformedGeneratorA :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((1 / 4), 5), ((-1 / 4), 15), ((-1 / 4), 25), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 3), ((-3 / 4), 5), ((-1 / 2), 7), ((-1 / 4), 10), ((1 / 4), 15), ((1 / 2), 19), ((1 / 4), 20), ((1 / 2), 23), ((3 / 4), 25), ((1 / 2), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 3), ((-1 / 4), 5), ((-1 / 2), 7), ((-1 / 2), 10), ((1 / 4), 15), ((1 / 2), 19), ((1 / 2), 23), ((-1 / 4), 25), ((1 / 4), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 4), 5), ((-1 / 4), 10), ((-1 / 4), 15), ((3 / 4), 20), ((-1 / 4), 25), ((1 / 2), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 4), 5), ((1 / 4), 10), ((3 / 4), 15), ((1 / 4), 20), ((-1 / 4), 25), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 5), ((-1 / 4), 15), ((-1 / 4), 25), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 3), ((1 / 4), 5), ((-1 / 2), 7), ((1 / 4), 10), ((1 / 4), 15), ((1 / 2), 19), ((3 / 4), 20), ((1 / 2), 23), ((-1 / 4), 25), ((-1 / 2), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 3), ((-1 / 4), 5), ((-1 / 2), 7), ((1 / 2), 10), ((1 / 4), 15), ((1 / 2), 19), ((1 / 2), 23), ((-1 / 4), 25), ((-1 / 4), 30), ((-1 / 2), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 3), ((1 / 4), 5), ((1 / 2), 7), ((-1 / 2), 10), ((-1 / 4), 15), ((-1 / 2), 19), ((-1 / 2), 23), ((1 / 4), 25), ((1 / 4), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 4), 5), ((-1 / 4), 10), ((1 / 4), 15), ((3 / 4), 20), ((1 / 4), 25), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 5), ((1 / 4), 15), ((1 / 4), 25), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 3), ((3 / 4), 5), ((1 / 2), 7), ((-1 / 4), 10), ((-1 / 4), 15), ((-1 / 2), 19), ((1 / 4), 20), ((-1 / 2), 23), ((-3 / 4), 25), ((1 / 2), 30), ((1 / 2), 31)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 3), ((-1 / 4), 5), ((1 / 2), 7), ((1 / 4), 10), ((-1 / 4), 15), ((-1 / 2), 19), ((3 / 4), 20), ((-1 / 2), 23), ((1 / 4), 25), ((-1 / 2), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((1 / 2), 3), ((1 / 4), 5), ((1 / 2), 7), ((1 / 2), 10), ((-1 / 4), 15), ((-1 / 2), 19), ((-1 / 2), 23), ((1 / 4), 25), ((-1 / 4), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 4), 5), ((1 / 4), 10), ((-3 / 4), 15), ((1 / 4), 20), ((1 / 4), 25), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 5), ((1 / 4), 15), ((1 / 4), 25), ((1 / 4), 30)]]
  ]

macro "close_cyclotomic_row07" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)


private theorem row07_eigenbasisInverse_mul_0_0 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        0 0 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        0 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((3 / 4) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 3 + ((3 / 4) : ℂ) * ζ ^ 4 + ((1 / 12) : ℂ) * ζ ^ 5 + ((1 / 6) : ℂ) * ζ ^ 6 - ((3 / 4) : ℂ) * ζ ^ 8 - ((1 / 12) : ℂ) * ζ ^ 9 + ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 12) : ℂ) * ζ ^ 13 - ((5 / 12) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 6) : ℂ) * ζ ^ 23 + ((5 / 12) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 26 - ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 6) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_0_1 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        0 1 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        0 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 4) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 12) : ℂ) * ζ ^ 5 + ((1 / 6) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 12) : ℂ) * ζ ^ 9 + ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 13 + ((5 / 12) : ℂ) * ζ ^ 15 - ((5 / 12) : ℂ) * ζ ^ 19 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 25 - ((1 / 6) : ℂ) * ζ ^ 26 + ((1 / 6) : ℂ) * ζ ^ 28 - ((1 / 12) : ℂ) * ζ ^ 29 + ((1 / 6) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_0_2 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        0 2 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        0 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 4) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 12) : ℂ) * ζ ^ 5 - ((1 / 6) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 12) : ℂ) * ζ ^ 9 + ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 12) : ℂ) * ζ ^ 13 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 15 + ((1 / 3) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 19 + ((1 / 12) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 12) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 25 + ((1 / 6) : ℂ) * ζ ^ 26 - ((1 / 6) : ℂ) * ζ ^ 28 - ((1 / 6) : ℂ) * ζ ^ 29 - ((1 / 6) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_0_3 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        0 3 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        0 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 4) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 12) : ℂ) * ζ ^ 5 - ((1 / 6) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 12) : ℂ) * ζ ^ 9 + ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 12) : ℂ) * ζ ^ 13 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 12) : ℂ) * ζ ^ 15 + ((1 / 3) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 19 + ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 12) : ℂ) * ζ ^ 23 - ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 25 + ((1 / 6) : ℂ) * ζ ^ 26 + ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 29 - ((1 / 6) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_1_0 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        1 0 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        1 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 4) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 5 + ((1 / 12) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 9 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 13 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 19 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 22 - ((1 / 12) : ℂ) * ζ ^ 23 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 25 - ((1 / 12) : ℂ) * ζ ^ 26 + ((1 / 6) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 29 + ((1 / 12) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_1_1 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        1 1 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        1 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((3 / 4) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 3 + ((3 / 4) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 5 - ((1 / 6) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 9 - ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 15 + ((1 / 6) : ℂ) * ζ ^ 19 - ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 25 + ((1 / 6) : ℂ) * ζ ^ 26 - ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 29 - ((1 / 6) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_1_2 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        1 2 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        1 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 4) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 5 - ((1 / 12) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 9 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 13 + ((1 / 12) : ℂ) * ζ ^ 14 - ((5 / 12) : ℂ) * ζ ^ 15 - ((1 / 12) : ℂ) * ζ ^ 18 + ((5 / 12) : ℂ) * ζ ^ 19 + ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 12) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 25 + ((1 / 12) : ℂ) * ζ ^ 26 + ((1 / 6) : ℂ) * ζ ^ 28 - ((1 / 12) : ℂ) * ζ ^ 29 - ((1 / 12) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_1_3 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        1 3 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        1 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 4) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 5 + ((1 / 6) : ℂ) * ζ ^ 6 - ((1 / 6) : ℂ) * ζ ^ 9 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 13 + ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 15 - ((1 / 3) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 19 - ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 23 + ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 26 - ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 6) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_2_0 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        2 0 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        2 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 4) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 12) : ℂ) * ζ ^ 5 - ((1 / 6) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 9 + ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 12) : ℂ) * ζ ^ 13 - ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 15 + ((1 / 3) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 19 + ((1 / 12) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 12) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 25 + ((1 / 6) : ℂ) * ζ ^ 26 - ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 6) : ℂ) * ζ ^ 29 - ((1 / 6) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_2_1 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        2 1 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        2 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 4) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 12) : ℂ) * ζ ^ 5 - ((1 / 6) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 9 + ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 12) : ℂ) * ζ ^ 13 - ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 12) : ℂ) * ζ ^ 15 + ((1 / 3) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 19 + ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 12) : ℂ) * ζ ^ 23 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 25 + ((1 / 6) : ℂ) * ζ ^ 26 + ((1 / 6) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 29 - ((1 / 6) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_2_2 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        2 2 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        2 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((3 / 4) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 3 + ((3 / 4) : ℂ) * ζ ^ 4 - ((1 / 12) : ℂ) * ζ ^ 5 + ((1 / 6) : ℂ) * ζ ^ 6 - ((3 / 4) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 9 + ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 12) : ℂ) * ζ ^ 13 - ((5 / 12) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 6) : ℂ) * ζ ^ 23 + ((5 / 12) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 26 - ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 6) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_2_3 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        2 3 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        2 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 4) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 12) : ℂ) * ζ ^ 5 + ((1 / 6) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 9 + ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 13 - ((5 / 12) : ℂ) * ζ ^ 15 + ((5 / 12) : ℂ) * ζ ^ 19 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 12) : ℂ) * ζ ^ 25 - ((1 / 6) : ℂ) * ζ ^ 26 + ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 12) : ℂ) * ζ ^ 29 + ((1 / 6) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_3_0 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        3 0 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        3 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 4) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 5 - ((1 / 12) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 9 - ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 13 + ((1 / 12) : ℂ) * ζ ^ 14 + ((5 / 12) : ℂ) * ζ ^ 15 - ((1 / 12) : ℂ) * ζ ^ 18 - ((5 / 12) : ℂ) * ζ ^ 19 + ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 12) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 12) : ℂ) * ζ ^ 25 + ((1 / 12) : ℂ) * ζ ^ 26 + ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 12) : ℂ) * ζ ^ 29 - ((1 / 12) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_3_1 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        3 1 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        3 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 4) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 5 + ((1 / 6) : ℂ) * ζ ^ 6 + ((1 / 6) : ℂ) * ζ ^ 9 - ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 13 + ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 15 - ((1 / 3) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 19 - ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 23 + ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 26 - ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 6) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_3_2 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        3 2 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        3 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 4) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 5 + ((1 / 12) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 9 - ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 13 + ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 19 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 22 + ((1 / 12) : ℂ) * ζ ^ 23 - ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 25 - ((1 / 12) : ℂ) * ζ ^ 26 + ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 29 + ((1 / 12) : ℂ) * ζ ^ 30)
private theorem row07_eigenbasisInverse_mul_3_3 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis)
        3 3 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        3 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((3 / 4) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 3 + ((3 / 4) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 5 - ((1 / 6) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 9 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 15 - ((1 / 6) : ℂ) * ζ ^ 19 - ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 25 + ((1 / 6) : ℂ) * ζ ^ 26 - ((1 / 6) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 29 - ((1 / 6) : ℂ) * ζ ^ 30)
/-- The displayed row 07 matrix is a left inverse of its
eigenbasis. -/
theorem alternatingSixAmbientRow07EigenbasisInverse_mul :
    alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixAmbientRow07Eigenbasis =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row07_eigenbasisInverse_mul_0_0
  · exact row07_eigenbasisInverse_mul_0_1
  · exact row07_eigenbasisInverse_mul_0_2
  · exact row07_eigenbasisInverse_mul_0_3
  · exact row07_eigenbasisInverse_mul_1_0
  · exact row07_eigenbasisInverse_mul_1_1
  · exact row07_eigenbasisInverse_mul_1_2
  · exact row07_eigenbasisInverse_mul_1_3
  · exact row07_eigenbasisInverse_mul_2_0
  · exact row07_eigenbasisInverse_mul_2_1
  · exact row07_eigenbasisInverse_mul_2_2
  · exact row07_eigenbasisInverse_mul_2_3
  · exact row07_eigenbasisInverse_mul_3_0
  · exact row07_eigenbasisInverse_mul_3_1
  · exact row07_eigenbasisInverse_mul_3_2
  · exact row07_eigenbasisInverse_mul_3_3

/-- The displayed row 07 inverse is also a right inverse. -/
theorem alternatingSixAmbientRow07Eigenbasis_mul_inverse :
    alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow07EigenbasisInverse_mul


private theorem row07_generatorB_mul_eigenbasis_0_0 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        0 0 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        0 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((1 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 3 + ((1 / 3) : ℂ) * ζ ^ 4 - ((4 / 3) : ℂ) * ζ ^ 5 - ((1 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 9 + ((1 / 3) : ℂ) * ζ ^ 10 - ((4 / 3) : ℂ) * ζ ^ 13 - ((1 / 3) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 15 + ((4 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 19)
private theorem row07_generatorB_mul_eigenbasis_0_1 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        0 1 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        0 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((1 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 3 + ((1 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 5 - ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 9 - ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 13 + ((1 / 3) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 15 - ((1 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 19 + ζ ^ 20 + ζ ^ 23 - ζ ^ 24 + ζ ^ 25 + ζ ^ 28 - ζ ^ 29 + (2 : ℂ) * ζ ^ 30 + ζ ^ 33 - (2 : ℂ) * ζ ^ 34 + ζ ^ 35 + (2 : ℂ) * ζ ^ 38 - ζ ^ 39 + ζ ^ 40 + ζ ^ 43 - ζ ^ 44)
private theorem row07_generatorB_mul_eigenbasis_0_2 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        0 2 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        0 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((1 / 3) : ℂ) - ((4 / 3) : ℂ) * ζ ^ 3 + ((1 / 3) : ℂ) * ζ ^ 4 + ((4 / 3) : ℂ) * ζ ^ 5 - ((1 / 3) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 9 + ((1 / 3) : ℂ) * ζ ^ 10 + ((4 / 3) : ℂ) * ζ ^ 13 - ((1 / 3) : ℂ) * ζ ^ 14 - ((5 / 3) : ℂ) * ζ ^ 15 + ((1 / 3) : ℂ) * ζ ^ 18 + ((5 / 3) : ℂ) * ζ ^ 19 + ζ ^ 20 - ζ ^ 23 - ζ ^ 24 + ζ ^ 28 - (2 : ℂ) * ζ ^ 30 + (2 : ℂ) * ζ ^ 34 - (2 : ℂ) * ζ ^ 38 + ζ ^ 40 - ζ ^ 44 - ζ ^ 45 + ζ ^ 48 + ζ ^ 49 - ζ ^ 50 - ζ ^ 53 + ζ ^ 54 + ζ ^ 55 - ζ ^ 58 - ζ ^ 59 + ζ ^ 63 - ζ ^ 65 + ζ ^ 69 + ζ ^ 70 - ζ ^ 73 - ζ ^ 74)
private theorem row07_generatorB_mul_eigenbasis_0_3 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        0 3 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        0 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((1 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 3 + ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 5 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 9 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 13 + ((1 / 3) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 15 - ((1 / 3) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 19 + ζ ^ 20 - ζ ^ 23 - ζ ^ 24 - ζ ^ 25 + ζ ^ 28 + ζ ^ 29 + (2 : ℂ) * ζ ^ 30 - ζ ^ 33 - (2 : ℂ) * ζ ^ 34 - ζ ^ 35 + (2 : ℂ) * ζ ^ 38 + ζ ^ 39 + ζ ^ 40 - ζ ^ 43 - ζ ^ 44 - ζ ^ 45 + ζ ^ 48 + ζ ^ 49 + ζ ^ 50 - ζ ^ 53 - ζ ^ 54 + ζ ^ 58 - ζ ^ 70 + ζ ^ 74 + ζ ^ 75 - ζ ^ 78 - ζ ^ 79 - ζ ^ 80 + ζ ^ 83 + ζ ^ 84 + ζ ^ 85 - ζ ^ 88 - ζ ^ 89 - (2 : ℂ) * ζ ^ 90 + ζ ^ 93 + (2 : ℂ) * ζ ^ 94 + ζ ^ 95 - (2 : ℂ) * ζ ^ 98 - ζ ^ 99 - ζ ^ 100 + ζ ^ 103 + ζ ^ 104)
private theorem row07_generatorB_mul_eigenbasis_1_0 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        1 0 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        1 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 ((2 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8)
private theorem row07_generatorB_mul_eigenbasis_1_1 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        1 1 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        1 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 ((2 : ℂ) + ζ ^ 3 - (2 : ℂ) * ζ ^ 4 + ζ ^ 5 + (2 : ℂ) * ζ ^ 8 - ζ ^ 9 + ζ ^ 13 + ζ ^ 15 - ζ ^ 19 - ζ ^ 25 + ζ ^ 29 - ζ ^ 33 - ζ ^ 35 + ζ ^ 39 - ζ ^ 40 - ζ ^ 43 + ζ ^ 44)
private theorem row07_generatorB_mul_eigenbasis_1_2 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        1 2 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        1 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 ((2 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8 + ζ ^ 15 - ζ ^ 19 + ζ ^ 23 - ζ ^ 25 + ζ ^ 29 - ζ ^ 33 - ζ ^ 40 + ζ ^ 44 - ζ ^ 48 - ζ ^ 55 + ζ ^ 59 - ζ ^ 60 - ζ ^ 63 + ζ ^ 64 + ζ ^ 65 - ζ ^ 68 - ζ ^ 69 + ζ ^ 73)
private theorem row07_generatorB_mul_eigenbasis_1_3 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        1 3 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        1 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 ((2 : ℂ) - ζ ^ 3 - (2 : ℂ) * ζ ^ 4 - ζ ^ 5 + (2 : ℂ) * ζ ^ 8 + ζ ^ 9 - ζ ^ 13 - ζ ^ 15 + ζ ^ 19 + ζ ^ 25 - ζ ^ 29 + ζ ^ 33 + ζ ^ 35 - ζ ^ 39 - ζ ^ 40 + ζ ^ 43 + ζ ^ 44 + ζ ^ 45 - ζ ^ 48 - ζ ^ 49 + ζ ^ 53 + ζ ^ 55 - ζ ^ 59 - ζ ^ 60 + ζ ^ 63 + ζ ^ 64 - ζ ^ 68 - ζ ^ 85 + ζ ^ 89 - ζ ^ 93 - ζ ^ 95 + ζ ^ 99 + ζ ^ 100 - ζ ^ 103 - ζ ^ 104)
private theorem row07_generatorB_mul_eigenbasis_2_0 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        2 0 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        2 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 3) : ℂ) - ((4 / 3) : ℂ) * ζ ^ 3 - ((1 / 3) : ℂ) * ζ ^ 4 + ((4 / 3) : ℂ) * ζ ^ 5 + ((1 / 3) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 9 - ((1 / 3) : ℂ) * ζ ^ 10 + ((4 / 3) : ℂ) * ζ ^ 13 + ((1 / 3) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 15 - ((1 / 3) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 19)
private theorem row07_generatorB_mul_eigenbasis_2_1 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        2 1 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        2 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 3 - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 5 + ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 9 + ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 13 - ((1 / 3) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 15 + ((1 / 3) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 19 - ζ ^ 25 + ζ ^ 29 - ζ ^ 30 - ζ ^ 33 + ζ ^ 34 - ζ ^ 38 - ζ ^ 40 + ζ ^ 44)
private theorem row07_generatorB_mul_eigenbasis_2_2 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        2 2 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        2 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 3 - ((1 / 3) : ℂ) * ζ ^ 4 - ((4 / 3) : ℂ) * ζ ^ 5 + ((1 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 9 - ((1 / 3) : ℂ) * ζ ^ 10 - ((4 / 3) : ℂ) * ζ ^ 13 + ((1 / 3) : ℂ) * ζ ^ 14 + ((5 / 3) : ℂ) * ζ ^ 15 - ((1 / 3) : ℂ) * ζ ^ 18 - ((5 / 3) : ℂ) * ζ ^ 19 + ζ ^ 23 + ζ ^ 30 - ζ ^ 34 + ζ ^ 38 - ζ ^ 40 + ζ ^ 44 - ζ ^ 48 + ζ ^ 50 - ζ ^ 54 - ζ ^ 55 + ζ ^ 58 + ζ ^ 59 - ζ ^ 60 - ζ ^ 63 + ζ ^ 64 - ζ ^ 68)
private theorem row07_generatorB_mul_eigenbasis_2_3 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        2 3 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        2 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((1 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 3 - ((1 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 5 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 9 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 13 - ((1 / 3) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 15 + ((1 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 19 + ζ ^ 25 - ζ ^ 29 - ζ ^ 30 + ζ ^ 33 + ζ ^ 34 - ζ ^ 38 - ζ ^ 40 + ζ ^ 44 + ζ ^ 45 - ζ ^ 48 - ζ ^ 49 - ζ ^ 50 + ζ ^ 53 + ζ ^ 54 - ζ ^ 58 - ζ ^ 60 + ζ ^ 64 - ζ ^ 68 - ζ ^ 85 + ζ ^ 89 + ζ ^ 90 - ζ ^ 93 - ζ ^ 94 + ζ ^ 98 + ζ ^ 100 - ζ ^ 104)
private theorem row07_generatorB_mul_eigenbasis_3_0 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        3 0 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        3 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((2 / 3) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 3 - ((2 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 5 + ((2 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 9 - ((2 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 13 + ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 15 - ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 19)
private theorem row07_generatorB_mul_eigenbasis_3_1 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        3 1 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        3 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((2 / 3) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 3 - ((2 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 5 + ((2 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 9 + ((2 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 13 - ((2 / 3) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 15 + ((2 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 19)
private theorem row07_generatorB_mul_eigenbasis_3_2 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        3 2 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        3 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((2 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 3 - ((2 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 5 + ((2 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 9 - ((2 / 3) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 13 + ((2 / 3) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 15 - ((2 / 3) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 19 - ζ ^ 23 - ζ ^ 35 + ζ ^ 39 - ζ ^ 43)
private theorem row07_generatorB_mul_eigenbasis_3_3 :
    (alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis)
        3 3 =
      (alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal)
        3 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07GeneratorBDiagonal,
      alternatingSixAmbientRow07GeneratorBEigenvalue,
      alternatingSixAmbientRow07EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((2 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 3 - ((2 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 5 + ((2 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 9 + ((2 / 3) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 13 - ((2 / 3) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 15 + ((2 / 3) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 19 - ζ ^ 45 + ζ ^ 49 - ζ ^ 53 - ζ ^ 65 + ζ ^ 69 - ζ ^ 73)
/-- The checked row 07 basis diagonalizes the second
generator. -/
theorem alternatingSixAmbientRow07GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row07_matrixB *
        alternatingSixAmbientRow07Eigenbasis =
      alternatingSixAmbientRow07Eigenbasis *
        alternatingSixAmbientRow07GeneratorBDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row07_generatorB_mul_eigenbasis_0_0
  · exact row07_generatorB_mul_eigenbasis_0_1
  · exact row07_generatorB_mul_eigenbasis_0_2
  · exact row07_generatorB_mul_eigenbasis_0_3
  · exact row07_generatorB_mul_eigenbasis_1_0
  · exact row07_generatorB_mul_eigenbasis_1_1
  · exact row07_generatorB_mul_eigenbasis_1_2
  · exact row07_generatorB_mul_eigenbasis_1_3
  · exact row07_generatorB_mul_eigenbasis_2_0
  · exact row07_generatorB_mul_eigenbasis_2_1
  · exact row07_generatorB_mul_eigenbasis_2_2
  · exact row07_generatorB_mul_eigenbasis_2_3
  · exact row07_generatorB_mul_eigenbasis_3_0
  · exact row07_generatorB_mul_eigenbasis_3_1
  · exact row07_generatorB_mul_eigenbasis_3_2
  · exact row07_generatorB_mul_eigenbasis_3_3


private theorem row07_transformedGeneratorA_0_0 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        0 0 =
      alternatingSixAmbientRow07TransformedGeneratorA
        0 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((1 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 3 + ((1 / 12) : ℂ) * ζ ^ 4 - ((5 / 12) : ℂ) * ζ ^ 5 + ((1 / 6) : ℂ) * ζ ^ 6 + ((5 / 12) : ℂ) * ζ ^ 9 - ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 13 + ((2 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 15 + ((1 / 12) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 19 - ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 26 - ((1 / 6) : ℂ) * ζ ^ 28 + ((3 / 4) : ℂ) * ζ ^ 30 - ((1 / 6) : ℂ) * ζ ^ 33 - ((11 / 12) : ℂ) * ζ ^ 34 + ((5 / 12) : ℂ) * ζ ^ 38 + ((1 / 12) : ℂ) * ζ ^ 40 + ((1 / 3) : ℂ) * ζ ^ 42 - ((1 / 6) : ℂ) * ζ ^ 43 - ((1 / 12) : ℂ) * ζ ^ 44 - ((1 / 6) : ℂ) * ζ ^ 45 + ((1 / 3) : ℂ) * ζ ^ 46 + ((1 / 12) : ℂ) * ζ ^ 48 + ((1 / 6) : ℂ) * ζ ^ 49 - ((1 / 3) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_0_1 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        0 1 =
      alternatingSixAmbientRow07TransformedGeneratorA
        0 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((5 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 3 - ((5 / 12) : ℂ) * ζ ^ 4 + ((5 / 6) : ℂ) * ζ ^ 5 - ((1 / 3) : ℂ) * ζ ^ 6 + ((1 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 9 - ((3 / 4) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 13 + ((5 / 12) : ℂ) * ζ ^ 14 + ((1 / 12) : ℂ) * ζ ^ 15 - ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 19 + ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 6) : ℂ) * ζ ^ 24 - ((7 / 12) : ℂ) * ζ ^ 25 + ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28 + ((7 / 12) : ℂ) * ζ ^ 29 + ((2 / 3) : ℂ) * ζ ^ 30 - ((1 / 6) : ℂ) * ζ ^ 33 - ((5 / 6) : ℂ) * ζ ^ 34 + ((1 / 6) : ℂ) * ζ ^ 35 + ((1 / 4) : ℂ) * ζ ^ 38 - ((1 / 6) : ℂ) * ζ ^ 39 + ((1 / 3) : ℂ) * ζ ^ 40 - ((1 / 6) : ℂ) * ζ ^ 42 - ((1 / 3) : ℂ) * ζ ^ 44 + ((1 / 3) : ℂ) * ζ ^ 45 - ((1 / 6) : ℂ) * ζ ^ 46 - ((1 / 12) : ℂ) * ζ ^ 48 - ((1 / 3) : ℂ) * ζ ^ 49 + ((1 / 6) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_0_2 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        0 2 =
      alternatingSixAmbientRow07TransformedGeneratorA
        0 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((1 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 3 + ((1 / 12) : ℂ) * ζ ^ 4 + ((3 / 4) : ℂ) * ζ ^ 5 - ((1 / 6) : ℂ) * ζ ^ 6 - ((1 / 6) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 9 + ((1 / 6) : ℂ) * ζ ^ 10 + ((3 / 4) : ℂ) * ζ ^ 13 - ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 15 - ((5 / 12) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 19 + ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 6) : ℂ) * ζ ^ 23 - ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 25 + ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28 + ((1 / 6) : ℂ) * ζ ^ 29 - ((7 / 12) : ℂ) * ζ ^ 30 - ((1 / 3) : ℂ) * ζ ^ 33 + ((3 / 4) : ℂ) * ζ ^ 34 + ((1 / 3) : ℂ) * ζ ^ 35 - ((1 / 4) : ℂ) * ζ ^ 38 - ((1 / 3) : ℂ) * ζ ^ 39 + ((1 / 12) : ℂ) * ζ ^ 40 - ((1 / 3) : ℂ) * ζ ^ 42 + ((1 / 6) : ℂ) * ζ ^ 43 - ((1 / 12) : ℂ) * ζ ^ 44 - ((1 / 3) : ℂ) * ζ ^ 45 - ((1 / 3) : ℂ) * ζ ^ 46 + ((1 / 12) : ℂ) * ζ ^ 48 + ((1 / 3) : ℂ) * ζ ^ 49 + ((1 / 3) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_0_3 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        0 3 =
      alternatingSixAmbientRow07TransformedGeneratorA
        0 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((5 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 3 - ((5 / 12) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 5 + ((1 / 3) : ℂ) * ζ ^ 6 + ((2 / 3) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 9 + ((1 / 12) : ℂ) * ζ ^ 10 + ((5 / 6) : ℂ) * ζ ^ 13 + ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 6) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 22 + ((3 / 4) : ℂ) * ζ ^ 23 + ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 25 - ((1 / 2) : ℂ) * ζ ^ 26 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 12) : ℂ) * ζ ^ 29 - ((1 / 2) : ℂ) * ζ ^ 30 + ((2 / 3) : ℂ) * ζ ^ 34 + ((1 / 6) : ℂ) * ζ ^ 35 - ((1 / 12) : ℂ) * ζ ^ 38 - ((1 / 6) : ℂ) * ζ ^ 39 - ((1 / 2) : ℂ) * ζ ^ 40 + ((1 / 6) : ℂ) * ζ ^ 42 + ((1 / 2) : ℂ) * ζ ^ 44 + ((1 / 6) : ℂ) * ζ ^ 45 + ((1 / 6) : ℂ) * ζ ^ 46 - ((1 / 12) : ℂ) * ζ ^ 48 - ((1 / 6) : ℂ) * ζ ^ 49 - ((1 / 6) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_1_0 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        1 0 =
      alternatingSixAmbientRow07TransformedGeneratorA
        1 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((5 / 12) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 3 - ((5 / 12) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 5 + ((1 / 6) : ℂ) * ζ ^ 6 - ((1 / 12) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 9 + ((5 / 6) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 13 - ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 15 + ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 19 - ((1 / 12) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 23 + ((1 / 12) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 29 - ((3 / 4) : ℂ) * ζ ^ 30 + ((1 / 12) : ℂ) * ζ ^ 33 + ((5 / 6) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 35 - ((7 / 12) : ℂ) * ζ ^ 38 - ((1 / 4) : ℂ) * ζ ^ 39 + ((1 / 3) : ℂ) * ζ ^ 40 + ((1 / 12) : ℂ) * ζ ^ 42 + ((1 / 3) : ℂ) * ζ ^ 43 - ((1 / 3) : ℂ) * ζ ^ 44 - ((1 / 6) : ℂ) * ζ ^ 45 + ((1 / 12) : ℂ) * ζ ^ 46 - ((1 / 12) : ℂ) * ζ ^ 48 + ((1 / 6) : ℂ) * ζ ^ 49 - ((1 / 12) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_1_1 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        1 1 =
      alternatingSixAmbientRow07TransformedGeneratorA
        1 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((1 / 12) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 3 + ((1 / 12) : ℂ) * ζ ^ 4 - ((5 / 12) : ℂ) * ζ ^ 5 - ((1 / 12) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 8 + ((5 / 12) : ℂ) * ζ ^ 9 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((5 / 12) : ℂ) * ζ ^ 15 + ((5 / 12) : ℂ) * ζ ^ 18 - ((5 / 12) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 12) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 23 + ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 25 + ((1 / 12) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 29 - ((5 / 12) : ℂ) * ζ ^ 30 + ((5 / 12) : ℂ) * ζ ^ 33 + ((1 / 4) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 35 - ((1 / 6) : ℂ) * ζ ^ 38 + ((1 / 4) : ℂ) * ζ ^ 39 + ((1 / 3) : ℂ) * ζ ^ 40 + ((1 / 12) : ℂ) * ζ ^ 42 - ((1 / 6) : ℂ) * ζ ^ 43 - ((1 / 3) : ℂ) * ζ ^ 44 + ((1 / 12) : ℂ) * ζ ^ 46 + ((1 / 12) : ℂ) * ζ ^ 48 - ((1 / 12) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_1_2 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        1 2 =
      alternatingSixAmbientRow07TransformedGeneratorA
        1 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((5 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 3 - ((5 / 12) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 6 + ((11 / 12) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 12) : ℂ) * ζ ^ 13 - ((1 / 2) : ℂ) * ζ ^ 15 + ((1 / 2) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 23 + ((1 / 4) : ℂ) * ζ ^ 24 + ((5 / 12) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 26 - ((5 / 6) : ℂ) * ζ ^ 28 - ((5 / 12) : ℂ) * ζ ^ 29 + ((7 / 12) : ℂ) * ζ ^ 30 + ((1 / 4) : ℂ) * ζ ^ 33 - ((2 / 3) : ℂ) * ζ ^ 34 - ((1 / 12) : ℂ) * ζ ^ 35 + ((5 / 12) : ℂ) * ζ ^ 38 + ((1 / 12) : ℂ) * ζ ^ 39 - ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 12) : ℂ) * ζ ^ 42 + ((1 / 2) : ℂ) * ζ ^ 44 - ((1 / 12) : ℂ) * ζ ^ 46 - ((1 / 12) : ℂ) * ζ ^ 48 + ((1 / 12) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_1_3 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        1 3 =
      alternatingSixAmbientRow07TransformedGeneratorA
        1 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((1 / 12) : ℂ) + ((7 / 12) : ℂ) * ζ ^ 3 + ((1 / 12) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 5 + ((1 / 12) : ℂ) * ζ ^ 6 + ((1 / 12) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 9 + ((1 / 12) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 13 - ((5 / 12) : ℂ) * ζ ^ 15 - ((1 / 12) : ℂ) * ζ ^ 18 + ((5 / 12) : ℂ) * ζ ^ 19 + ((7 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 23 - ((7 / 12) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 28 + ((1 / 6) : ℂ) * ζ ^ 29 + ((1 / 4) : ℂ) * ζ ^ 30 + ((1 / 4) : ℂ) * ζ ^ 33 - ((1 / 12) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 35 + ((1 / 4) : ℂ) * ζ ^ 39 - ((1 / 6) : ℂ) * ζ ^ 40 - ((1 / 12) : ℂ) * ζ ^ 42 - ((1 / 6) : ℂ) * ζ ^ 43 + ((1 / 6) : ℂ) * ζ ^ 44 + ((1 / 6) : ℂ) * ζ ^ 45 - ((1 / 12) : ℂ) * ζ ^ 46 + ((1 / 12) : ℂ) * ζ ^ 48 - ((1 / 6) : ℂ) * ζ ^ 49 + ((1 / 12) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_2_0 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        2 0 =
      alternatingSixAmbientRow07TransformedGeneratorA
        2 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((1 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 3 + ((1 / 12) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 5 - ((1 / 6) : ℂ) * ζ ^ 6 - ((1 / 6) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 9 + ((1 / 6) : ℂ) * ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 13 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 15 - ((5 / 12) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 19 + ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 6) : ℂ) * ζ ^ 23 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 25 + ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28 - ((1 / 6) : ℂ) * ζ ^ 29 - ((7 / 12) : ℂ) * ζ ^ 30 + ((1 / 3) : ℂ) * ζ ^ 33 + ((3 / 4) : ℂ) * ζ ^ 34 - ((1 / 3) : ℂ) * ζ ^ 35 - ((1 / 4) : ℂ) * ζ ^ 38 + ((1 / 3) : ℂ) * ζ ^ 39 + ((1 / 12) : ℂ) * ζ ^ 40 - ((1 / 3) : ℂ) * ζ ^ 42 - ((1 / 6) : ℂ) * ζ ^ 43 - ((1 / 12) : ℂ) * ζ ^ 44 + ((1 / 3) : ℂ) * ζ ^ 45 - ((1 / 3) : ℂ) * ζ ^ 46 + ((1 / 12) : ℂ) * ζ ^ 48 - ((1 / 3) : ℂ) * ζ ^ 49 + ((1 / 3) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_2_1 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        2 1 =
      alternatingSixAmbientRow07TransformedGeneratorA
        2 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((5 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 3 - ((5 / 12) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 5 + ((1 / 3) : ℂ) * ζ ^ 6 + ((2 / 3) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 9 + ((1 / 12) : ℂ) * ζ ^ 10 - ((5 / 6) : ℂ) * ζ ^ 13 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 6) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 22 - ((3 / 4) : ℂ) * ζ ^ 23 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 12) : ℂ) * ζ ^ 25 - ((1 / 2) : ℂ) * ζ ^ 26 - ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 12) : ℂ) * ζ ^ 29 - ((1 / 2) : ℂ) * ζ ^ 30 + ((2 / 3) : ℂ) * ζ ^ 34 - ((1 / 6) : ℂ) * ζ ^ 35 - ((1 / 12) : ℂ) * ζ ^ 38 + ((1 / 6) : ℂ) * ζ ^ 39 - ((1 / 2) : ℂ) * ζ ^ 40 + ((1 / 6) : ℂ) * ζ ^ 42 + ((1 / 2) : ℂ) * ζ ^ 44 - ((1 / 6) : ℂ) * ζ ^ 45 + ((1 / 6) : ℂ) * ζ ^ 46 - ((1 / 12) : ℂ) * ζ ^ 48 + ((1 / 6) : ℂ) * ζ ^ 49 - ((1 / 6) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_2_2 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        2 2 =
      alternatingSixAmbientRow07TransformedGeneratorA
        2 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((1 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 3 + ((1 / 12) : ℂ) * ζ ^ 4 + ((5 / 12) : ℂ) * ζ ^ 5 + ((1 / 6) : ℂ) * ζ ^ 6 - ((5 / 12) : ℂ) * ζ ^ 9 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 13 + ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 15 + ((1 / 12) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 19 - ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 26 - ((1 / 6) : ℂ) * ζ ^ 28 + ((3 / 4) : ℂ) * ζ ^ 30 + ((1 / 6) : ℂ) * ζ ^ 33 - ((11 / 12) : ℂ) * ζ ^ 34 + ((5 / 12) : ℂ) * ζ ^ 38 + ((1 / 12) : ℂ) * ζ ^ 40 + ((1 / 3) : ℂ) * ζ ^ 42 + ((1 / 6) : ℂ) * ζ ^ 43 - ((1 / 12) : ℂ) * ζ ^ 44 + ((1 / 6) : ℂ) * ζ ^ 45 + ((1 / 3) : ℂ) * ζ ^ 46 + ((1 / 12) : ℂ) * ζ ^ 48 - ((1 / 6) : ℂ) * ζ ^ 49 - ((1 / 3) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_2_3 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        2 3 =
      alternatingSixAmbientRow07TransformedGeneratorA
        2 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((5 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 3 - ((5 / 12) : ℂ) * ζ ^ 4 - ((5 / 6) : ℂ) * ζ ^ 5 - ((1 / 3) : ℂ) * ζ ^ 6 + ((1 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 9 - ((3 / 4) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 13 + ((5 / 12) : ℂ) * ζ ^ 14 - ((1 / 12) : ℂ) * ζ ^ 15 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 19 + ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 6) : ℂ) * ζ ^ 24 + ((7 / 12) : ℂ) * ζ ^ 25 + ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28 - ((7 / 12) : ℂ) * ζ ^ 29 + ((2 / 3) : ℂ) * ζ ^ 30 + ((1 / 6) : ℂ) * ζ ^ 33 - ((5 / 6) : ℂ) * ζ ^ 34 - ((1 / 6) : ℂ) * ζ ^ 35 + ((1 / 4) : ℂ) * ζ ^ 38 + ((1 / 6) : ℂ) * ζ ^ 39 + ((1 / 3) : ℂ) * ζ ^ 40 - ((1 / 6) : ℂ) * ζ ^ 42 - ((1 / 3) : ℂ) * ζ ^ 44 - ((1 / 3) : ℂ) * ζ ^ 45 - ((1 / 6) : ℂ) * ζ ^ 46 - ((1 / 12) : ℂ) * ζ ^ 48 + ((1 / 3) : ℂ) * ζ ^ 49 + ((1 / 6) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_3_0 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        3 0 =
      alternatingSixAmbientRow07TransformedGeneratorA
        3 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((5 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 3 - ((5 / 12) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 6 + ((11 / 12) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 12) : ℂ) * ζ ^ 13 + ((1 / 2) : ℂ) * ζ ^ 15 - ((1 / 2) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 23 + ((1 / 4) : ℂ) * ζ ^ 24 - ((5 / 12) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 26 - ((5 / 6) : ℂ) * ζ ^ 28 + ((5 / 12) : ℂ) * ζ ^ 29 + ((7 / 12) : ℂ) * ζ ^ 30 - ((1 / 4) : ℂ) * ζ ^ 33 - ((2 / 3) : ℂ) * ζ ^ 34 + ((1 / 12) : ℂ) * ζ ^ 35 + ((5 / 12) : ℂ) * ζ ^ 38 - ((1 / 12) : ℂ) * ζ ^ 39 - ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 12) : ℂ) * ζ ^ 42 + ((1 / 2) : ℂ) * ζ ^ 44 - ((1 / 12) : ℂ) * ζ ^ 46 - ((1 / 12) : ℂ) * ζ ^ 48 + ((1 / 12) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_3_1 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        3 1 =
      alternatingSixAmbientRow07TransformedGeneratorA
        3 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((1 / 12) : ℂ) - ((7 / 12) : ℂ) * ζ ^ 3 + ((1 / 12) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 5 + ((1 / 12) : ℂ) * ζ ^ 6 + ((1 / 12) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 9 + ((1 / 12) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 13 + ((5 / 12) : ℂ) * ζ ^ 15 - ((1 / 12) : ℂ) * ζ ^ 18 - ((5 / 12) : ℂ) * ζ ^ 19 + ((7 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 23 - ((7 / 12) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 28 - ((1 / 6) : ℂ) * ζ ^ 29 + ((1 / 4) : ℂ) * ζ ^ 30 - ((1 / 4) : ℂ) * ζ ^ 33 - ((1 / 12) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 35 - ((1 / 4) : ℂ) * ζ ^ 39 - ((1 / 6) : ℂ) * ζ ^ 40 - ((1 / 12) : ℂ) * ζ ^ 42 + ((1 / 6) : ℂ) * ζ ^ 43 + ((1 / 6) : ℂ) * ζ ^ 44 - ((1 / 6) : ℂ) * ζ ^ 45 - ((1 / 12) : ℂ) * ζ ^ 46 + ((1 / 12) : ℂ) * ζ ^ 48 + ((1 / 6) : ℂ) * ζ ^ 49 + ((1 / 12) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_3_2 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        3 2 =
      alternatingSixAmbientRow07TransformedGeneratorA
        3 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (((5 / 12) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 3 - ((5 / 12) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 5 + ((1 / 6) : ℂ) * ζ ^ 6 - ((1 / 12) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 9 + ((5 / 6) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 13 - ((2 / 3) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 15 + ((2 / 3) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 19 - ((1 / 12) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 23 + ((1 / 12) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 29 - ((3 / 4) : ℂ) * ζ ^ 30 - ((1 / 12) : ℂ) * ζ ^ 33 + ((5 / 6) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 35 - ((7 / 12) : ℂ) * ζ ^ 38 + ((1 / 4) : ℂ) * ζ ^ 39 + ((1 / 3) : ℂ) * ζ ^ 40 + ((1 / 12) : ℂ) * ζ ^ 42 - ((1 / 3) : ℂ) * ζ ^ 43 - ((1 / 3) : ℂ) * ζ ^ 44 + ((1 / 6) : ℂ) * ζ ^ 45 + ((1 / 12) : ℂ) * ζ ^ 46 - ((1 / 12) : ℂ) * ζ ^ 48 - ((1 / 6) : ℂ) * ζ ^ 49 - ((1 / 12) : ℂ) * ζ ^ 50)
private theorem row07_transformedGeneratorA_3_3 :
    (alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis)
        3 3 =
      alternatingSixAmbientRow07TransformedGeneratorA
        3 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow07Eigenbasis,
      alternatingSixAmbientRow07EigenbasisInverse,
      alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row07 (-((1 / 12) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 3 + ((1 / 12) : ℂ) * ζ ^ 4 + ((5 / 12) : ℂ) * ζ ^ 5 - ((1 / 12) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 8 - ((5 / 12) : ℂ) * ζ ^ 9 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 - ((5 / 12) : ℂ) * ζ ^ 15 + ((5 / 12) : ℂ) * ζ ^ 18 + ((5 / 12) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 12) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 23 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 25 + ((1 / 12) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 29 - ((5 / 12) : ℂ) * ζ ^ 30 - ((5 / 12) : ℂ) * ζ ^ 33 + ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 35 - ((1 / 6) : ℂ) * ζ ^ 38 - ((1 / 4) : ℂ) * ζ ^ 39 + ((1 / 3) : ℂ) * ζ ^ 40 + ((1 / 12) : ℂ) * ζ ^ 42 + ((1 / 6) : ℂ) * ζ ^ 43 - ((1 / 3) : ℂ) * ζ ^ 44 + ((1 / 12) : ℂ) * ζ ^ 46 + ((1 / 12) : ℂ) * ζ ^ 48 - ((1 / 12) : ℂ) * ζ ^ 50)
/-- Exact conjugation formula for the row 07 first
generator. -/
theorem alternatingSixAmbientRow07TransformedGeneratorA_eq :
    alternatingSixAmbientRow07EigenbasisInverse *
        alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixAmbientRow07Eigenbasis =
      alternatingSixAmbientRow07TransformedGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row07_transformedGeneratorA_0_0
  · exact row07_transformedGeneratorA_0_1
  · exact row07_transformedGeneratorA_0_2
  · exact row07_transformedGeneratorA_0_3
  · exact row07_transformedGeneratorA_1_0
  · exact row07_transformedGeneratorA_1_1
  · exact row07_transformedGeneratorA_1_2
  · exact row07_transformedGeneratorA_1_3
  · exact row07_transformedGeneratorA_2_0
  · exact row07_transformedGeneratorA_2_1
  · exact row07_transformedGeneratorA_2_2
  · exact row07_transformedGeneratorA_2_3
  · exact row07_transformedGeneratorA_3_0
  · exact row07_transformedGeneratorA_3_1
  · exact row07_transformedGeneratorA_3_2
  · exact row07_transformedGeneratorA_3_3


end InductiveMcKay
end McKayConjecture
