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
# Checked diagonal data for ambient row 06

This generated module records an exact eigenbasis for the second generator
and the first generator in that basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenvalue block labels for row 06. -/
def alternatingSixAmbientRow06EigenvalueLabel :
    Fin 4 → Fin 4 :=
  ![0, 1, 2, 3]

/-- Second-generator eigenvalues, including their multiplicities. -/
def alternatingSixAmbientRow06GeneratorBEigenvalue :
    Fin 4 → ℂ :=
  fun i ↦
    alternatingSixOrderEightOddEigenvalue
      (alternatingSixAmbientRow06EigenvalueLabel i)

/-- Diagonal form of the row 06 second generator. -/
def alternatingSixAmbientRow06GeneratorBDiagonal :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal
    alternatingSixAmbientRow06GeneratorBEigenvalue

/-- Checked eigenbasis for the row 06 second generator. -/
def alternatingSixAmbientRow06Eigenbasis :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [(1, 5), (-1, 10), (-1, 20), (1, 30)],
      alternatingSixCyclotomicValue [(1, 3), (1, 7), (1, 10), (-1, 15), (-1, 19), (-1, 20), (-1, 23), (-1, 30), (1, 31)],
      alternatingSixCyclotomicValue [(-1, 5), (-1, 10), (-1, 20), (1, 30)],
      alternatingSixCyclotomicValue [(-1, 3), (-1, 7), (1, 10), (1, 15), (1, 19), (-1, 20), (1, 23), (-1, 30), (-1, 31)]],
    ![alternatingSixCyclotomicValue [(1, 0), (-1, 10)],
      alternatingSixCyclotomicValue [(1, 0), (1, 10)],
      alternatingSixCyclotomicValue [(1, 0), (-1, 10)],
      alternatingSixCyclotomicValue [(1, 0), (1, 10)]],
    ![alternatingSixCyclotomicValue [(1, 0), (-1, 3), (1, 5), (-1, 7), (1, 19), (-1, 20), (1, 23), (1, 30), (-1, 31)],
      alternatingSixCyclotomicValue [(1, 0), (1, 3), (1, 7), (-1, 15), (-1, 19), (-1, 20), (-1, 23), (-1, 25), (-1, 30), (1, 31)],
      alternatingSixCyclotomicValue [(1, 0), (1, 3), (-1, 5), (1, 7), (-1, 19), (-1, 20), (-1, 23), (1, 30), (1, 31)],
      alternatingSixCyclotomicValue [(1, 0), (-1, 3), (-1, 7), (1, 15), (1, 19), (-1, 20), (1, 23), (1, 25), (-1, 30), (-1, 31)]],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)]]
  ]

/-- Checked inverse of the row 06 eigenbasis. -/
def alternatingSixAmbientRow06EigenbasisInverse :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((1 / 4), 3), ((1 / 4), 5), ((1 / 4), 7), ((-1 / 4), 19), ((-1 / 4), 23), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 3), ((-1 / 4), 5), ((-1 / 4), 7), ((-1 / 4), 10), ((1 / 4), 15), ((1 / 4), 19), ((1 / 4), 23), ((1 / 4), 30), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 5)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 3), ((1 / 2), 5), ((1 / 4), 7), ((1 / 4), 10), ((-1 / 4), 19), ((-1 / 4), 23), ((-1 / 4), 30), ((1 / 4), 31)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 3), ((1 / 4), 7), ((-1 / 4), 15), ((-1 / 4), 19), ((-1 / 4), 23), ((1 / 4), 25), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 3), ((-1 / 4), 5), ((-1 / 4), 7), ((1 / 4), 10), ((1 / 4), 15), ((1 / 4), 19), ((1 / 4), 23), ((-1 / 4), 30), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 3), ((-1 / 4), 7), ((1 / 4), 15), ((1 / 4), 19), ((1 / 4), 23), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 2), 3), ((1 / 2), 7), ((-1 / 4), 10), ((-1 / 2), 15), ((-1 / 2), 19), ((-1 / 2), 23), ((1 / 4), 25), ((1 / 4), 30), ((1 / 2), 31)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 3), ((-1 / 4), 5), ((-1 / 4), 7), ((1 / 4), 19), ((1 / 4), 23), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 3), ((1 / 4), 5), ((1 / 4), 7), ((-1 / 4), 10), ((-1 / 4), 15), ((-1 / 4), 19), ((-1 / 4), 23), ((1 / 4), 30), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 5)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 3), ((-1 / 2), 5), ((-1 / 4), 7), ((1 / 4), 10), ((1 / 4), 19), ((1 / 4), 23), ((-1 / 4), 30), ((-1 / 4), 31)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 3), ((-1 / 4), 7), ((1 / 4), 15), ((1 / 4), 19), ((1 / 4), 23), ((-1 / 4), 25), ((-1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 3), ((1 / 4), 5), ((1 / 4), 7), ((1 / 4), 10), ((-1 / 4), 15), ((-1 / 4), 19), ((-1 / 4), 23), ((-1 / 4), 30), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 3), ((1 / 4), 7), ((-1 / 4), 15), ((-1 / 4), 19), ((-1 / 4), 23), ((1 / 4), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 2), 3), ((-1 / 2), 7), ((-1 / 4), 10), ((1 / 2), 15), ((1 / 2), 19), ((1 / 2), 23), ((-1 / 4), 25), ((1 / 4), 30), ((-1 / 2), 31)]]
  ]

/-- The row 06 first generator in the checked diagonal basis. -/
def alternatingSixAmbientRow06TransformedGeneratorA :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((1 / 4), 5), ((-1 / 4), 15), ((-1 / 4), 25), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 5), ((-1 / 4), 10), ((-3 / 4), 15), ((-1 / 4), 20), ((-1 / 4), 25), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 3), ((1 / 4), 5), ((1 / 2), 7), ((1 / 2), 10), ((-1 / 4), 15), ((-1 / 2), 19), ((-1 / 2), 23), ((1 / 4), 25), ((-1 / 4), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 2), 3), ((-1 / 4), 5), ((-1 / 2), 7), ((-1 / 4), 10), ((1 / 4), 15), ((1 / 2), 19), ((-3 / 4), 20), ((1 / 2), 23), ((1 / 4), 25), ((-1 / 4), 30), ((-1 / 2), 31)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 2), 3), ((3 / 4), 5), ((-1 / 2), 7), ((1 / 4), 10), ((1 / 4), 15), ((1 / 2), 19), ((-1 / 4), 20), ((1 / 2), 23), ((-3 / 4), 25), ((1 / 4), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 5), ((-1 / 4), 15), ((-1 / 4), 25), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 5), ((1 / 4), 10), ((1 / 4), 15), ((-3 / 4), 20), ((-1 / 4), 25), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 3), ((1 / 4), 5), ((1 / 2), 7), ((-1 / 2), 10), ((-1 / 4), 15), ((-1 / 2), 19), ((-1 / 2), 23), ((1 / 4), 25), ((1 / 4), 30), ((1 / 2), 31)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 3), ((-1 / 4), 5), ((-1 / 2), 7), ((1 / 2), 10), ((1 / 4), 15), ((1 / 2), 19), ((1 / 2), 23), ((-1 / 4), 25), ((-1 / 4), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 2), 3), ((1 / 4), 5), ((1 / 2), 7), ((-1 / 4), 10), ((-1 / 4), 15), ((-1 / 2), 19), ((-3 / 4), 20), ((-1 / 2), 23), ((-1 / 4), 25), ((-1 / 4), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 5), ((1 / 4), 15), ((1 / 4), 25), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 5), ((-1 / 4), 10), ((3 / 4), 15), ((-1 / 4), 20), ((1 / 4), 25), ((-1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 5), ((1 / 4), 10), ((-1 / 4), 15), ((-3 / 4), 20), ((1 / 4), 25), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 3), ((-1 / 4), 5), ((-1 / 2), 7), ((-1 / 2), 10), ((1 / 4), 15), ((1 / 2), 19), ((1 / 2), 23), ((-1 / 4), 25), ((1 / 4), 30), ((-1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 2), 3), ((-3 / 4), 5), ((1 / 2), 7), ((1 / 4), 10), ((-1 / 4), 15), ((-1 / 2), 19), ((-1 / 4), 20), ((-1 / 2), 23), ((3 / 4), 25), ((1 / 4), 30), ((1 / 2), 31)],
      alternatingSixCyclotomicValue [((-1 / 4), 5), ((1 / 4), 15), ((1 / 4), 25), ((1 / 4), 30)]]
  ]

macro "close_cyclotomic_row06" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)


private theorem row06_eigenbasisInverse_mul_0_0 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        0 0 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        0 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 29)
private theorem row06_eigenbasisInverse_mul_0_1 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        0 1 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        0 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 29 + ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row06_eigenbasisInverse_mul_0_2 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        0 2 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        0 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 29)
private theorem row06_eigenbasisInverse_mul_0_3 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        0 3 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        0 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 19 + ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 29 - ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row06_eigenbasisInverse_mul_1_0 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        1 0 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        1 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 5 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 9 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 13 + ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 4) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row06_eigenbasisInverse_mul_1_1 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        1 1 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        1 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 5 - ((3 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 9 - ((1 / 4) : ℂ) * ζ ^ 13 - ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 23 + ((1 / 2) : ℂ) * ζ ^ 24)
private theorem row06_eigenbasisInverse_mul_1_2 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        1 2 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        1 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 5 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 9 - ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 13 + ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 19 + ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 23 + ((1 / 4) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row06_eigenbasisInverse_mul_1_3 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        1 3 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        1 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 5 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 9 - ((1 / 4) : ℂ) * ζ ^ 13 - ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 24)
private theorem row06_eigenbasisInverse_mul_2_0 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        2 0 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        2 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 + ((1 / 4) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 29)
private theorem row06_eigenbasisInverse_mul_2_1 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        2 1 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        2 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 + ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 29 - ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row06_eigenbasisInverse_mul_2_2 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        2 2 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        2 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 + ((1 / 4) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 29)
private theorem row06_eigenbasisInverse_mul_2_3 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        2 3 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        2 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 29 + ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row06_eigenbasisInverse_mul_3_0 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        3 0 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        3 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 5 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 9 - ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 13 - ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 + ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 23 + ((1 / 4) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row06_eigenbasisInverse_mul_3_1 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        3 1 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        3 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 5 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 9 + ((1 / 4) : ℂ) * ζ ^ 13 + ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 19 + ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 24)
private theorem row06_eigenbasisInverse_mul_3_2 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        3 2 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        3 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 5 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 9 + ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 13 - ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 4) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 30)
private theorem row06_eigenbasisInverse_mul_3_3 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis)
        3 3 =
      (1 : Matrix (Fin 4) (Fin 4) ℂ)
        3 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 5 - ((3 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 9 + ((1 / 4) : ℂ) * ζ ^ 13 + ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 23 + ((1 / 2) : ℂ) * ζ ^ 24)
/-- The displayed row 06 matrix is a left inverse of its
eigenbasis. -/
theorem alternatingSixAmbientRow06EigenbasisInverse_mul :
    alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixAmbientRow06Eigenbasis =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row06_eigenbasisInverse_mul_0_0
  · exact row06_eigenbasisInverse_mul_0_1
  · exact row06_eigenbasisInverse_mul_0_2
  · exact row06_eigenbasisInverse_mul_0_3
  · exact row06_eigenbasisInverse_mul_1_0
  · exact row06_eigenbasisInverse_mul_1_1
  · exact row06_eigenbasisInverse_mul_1_2
  · exact row06_eigenbasisInverse_mul_1_3
  · exact row06_eigenbasisInverse_mul_2_0
  · exact row06_eigenbasisInverse_mul_2_1
  · exact row06_eigenbasisInverse_mul_2_2
  · exact row06_eigenbasisInverse_mul_2_3
  · exact row06_eigenbasisInverse_mul_3_0
  · exact row06_eigenbasisInverse_mul_3_1
  · exact row06_eigenbasisInverse_mul_3_2
  · exact row06_eigenbasisInverse_mul_3_3

/-- The displayed row 06 inverse is also a right inverse. -/
theorem alternatingSixAmbientRow06Eigenbasis_mul_inverse :
    alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow06EigenbasisInverse_mul


private theorem row06_generatorB_mul_eigenbasis_0_0 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        0 0 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        0 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (ζ ^ 3 - ζ ^ 5 + ζ ^ 9 - ζ ^ 13 + ζ ^ 15 - ζ ^ 19)
private theorem row06_generatorB_mul_eigenbasis_0_1 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        0 1 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        0 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-ζ ^ 3 + ζ ^ 20 - ζ ^ 24 + ζ ^ 25 + ζ ^ 28 - ζ ^ 29 + ζ ^ 33 + ζ ^ 35 - ζ ^ 39 + ζ ^ 40 + ζ ^ 43 - ζ ^ 44)
private theorem row06_generatorB_mul_eigenbasis_0_2 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        0 2 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        0 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-ζ ^ 3 + ζ ^ 5 - ζ ^ 9 + ζ ^ 13 - ζ ^ 15 + ζ ^ 19 + ζ ^ 20 - ζ ^ 24 + ζ ^ 25 + ζ ^ 28 - ζ ^ 29 + ζ ^ 33 + ζ ^ 35 - ζ ^ 39 + ζ ^ 40 + ζ ^ 43 - ζ ^ 44 + ζ ^ 48 + ζ ^ 55 - ζ ^ 59 + ζ ^ 63 - ζ ^ 65 + ζ ^ 69 - ζ ^ 73)
private theorem row06_generatorB_mul_eigenbasis_0_3 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        0 3 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        0 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (ζ ^ 3 + ζ ^ 20 - ζ ^ 24 - ζ ^ 25 + ζ ^ 28 + ζ ^ 29 - ζ ^ 33 - ζ ^ 35 + ζ ^ 39 + ζ ^ 40 - ζ ^ 43 - ζ ^ 44 + ζ ^ 48 - ζ ^ 55 + ζ ^ 59 - ζ ^ 63 + ζ ^ 65 - ζ ^ 69 + ζ ^ 73 - ζ ^ 80 + ζ ^ 84 + ζ ^ 85 - ζ ^ 88 - ζ ^ 89 + ζ ^ 93 + ζ ^ 95 - ζ ^ 99 - ζ ^ 100 + ζ ^ 103 + ζ ^ 104)
private theorem row06_generatorB_mul_eigenbasis_1_0 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        1 0 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        1 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 15 - ζ ^ 18 + ζ ^ 19)
private theorem row06_generatorB_mul_eigenbasis_1_1 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        1 1 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        1 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 - ζ ^ 23)
private theorem row06_generatorB_mul_eigenbasis_1_2 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        1 2 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        1 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 - ζ ^ 23 + ζ ^ 25 - ζ ^ 29 + ζ ^ 33 - ζ ^ 35 + ζ ^ 39 - ζ ^ 43 + ζ ^ 45 - ζ ^ 49 + ζ ^ 53)
private theorem row06_generatorB_mul_eigenbasis_1_3 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        1 3 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        1 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 + ζ ^ 23 - ζ ^ 45 + ζ ^ 49 - ζ ^ 53 - ζ ^ 55 + ζ ^ 59 - ζ ^ 63 - ζ ^ 65 + ζ ^ 69 - ζ ^ 73 - ζ ^ 75 + ζ ^ 79 - ζ ^ 83)
private theorem row06_generatorB_mul_eigenbasis_2_0 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        2 0 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        2 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-(1 : ℂ) + ζ ^ 3 + ζ ^ 4 - ζ ^ 5 - ζ ^ 8 + ζ ^ 9 - ζ ^ 13 + ζ ^ 18)
private theorem row06_generatorB_mul_eigenbasis_2_1 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        2 1 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        2 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-(1 : ℂ) - ζ ^ 3 + ζ ^ 4 - ζ ^ 8 + ζ ^ 20 + ζ ^ 23 - ζ ^ 24 + ζ ^ 25 + ζ ^ 28 - ζ ^ 29 + ζ ^ 30 + ζ ^ 33 - ζ ^ 34 + ζ ^ 35 + ζ ^ 38 - ζ ^ 39 + ζ ^ 40 + ζ ^ 43 - ζ ^ 44)
private theorem row06_generatorB_mul_eigenbasis_2_2 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        2 2 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        2 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-(1 : ℂ) - ζ ^ 3 + ζ ^ 4 + ζ ^ 5 - ζ ^ 8 - ζ ^ 9 + ζ ^ 13 - ζ ^ 15 + ζ ^ 19 + ζ ^ 20 - ζ ^ 23 - ζ ^ 24 + ζ ^ 28 - ζ ^ 30 + ζ ^ 34 - ζ ^ 38 + ζ ^ 40 - ζ ^ 44 - ζ ^ 45 + ζ ^ 48 + ζ ^ 49 - ζ ^ 53 + ζ ^ 55 - ζ ^ 59 + ζ ^ 63 - ζ ^ 65 + ζ ^ 69 + ζ ^ 70 - ζ ^ 73 - ζ ^ 74)
private theorem row06_generatorB_mul_eigenbasis_2_3 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        2 3 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        2 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-(1 : ℂ) + ζ ^ 3 + ζ ^ 4 - ζ ^ 8 + ζ ^ 20 - ζ ^ 23 - ζ ^ 24 - ζ ^ 25 + ζ ^ 28 + ζ ^ 29 + ζ ^ 30 - ζ ^ 33 - ζ ^ 34 - ζ ^ 35 + ζ ^ 38 + ζ ^ 39 + ζ ^ 40 - ζ ^ 43 - ζ ^ 44 - ζ ^ 45 + ζ ^ 48 + ζ ^ 49 - ζ ^ 53 - ζ ^ 70 + ζ ^ 74 + ζ ^ 75 - ζ ^ 78 - ζ ^ 79 - ζ ^ 80 + ζ ^ 83 + ζ ^ 84 + ζ ^ 85 - ζ ^ 88 - ζ ^ 89 - ζ ^ 90 + ζ ^ 93 + ζ ^ 94 + ζ ^ 95 - ζ ^ 98 - ζ ^ 99 - ζ ^ 100 + ζ ^ 103 + ζ ^ 104)
private theorem row06_generatorB_mul_eigenbasis_3_0 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        3 0 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        3 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-ζ ^ 15 + ζ ^ 19)
private theorem row06_generatorB_mul_eigenbasis_3_1 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        3 1 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        3 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 0
private theorem row06_generatorB_mul_eigenbasis_3_2 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        3 2 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        3 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-ζ ^ 23 - ζ ^ 35 + ζ ^ 39 - ζ ^ 43)
private theorem row06_generatorB_mul_eigenbasis_3_3 :
    (alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis)
        3 3 =
      (alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal)
        3 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06GeneratorBDiagonal,
      alternatingSixAmbientRow06GeneratorBEigenvalue,
      alternatingSixAmbientRow06EigenvalueLabel,
      alternatingSixOrderEightOddEigenvalue,
      alternatingSixOrderEightOddEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-ζ ^ 45 + ζ ^ 49 - ζ ^ 53 - ζ ^ 65 + ζ ^ 69 - ζ ^ 73)
/-- The checked row 06 basis diagonalizes the second
generator. -/
theorem alternatingSixAmbientRow06GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row06_matrixB *
        alternatingSixAmbientRow06Eigenbasis =
      alternatingSixAmbientRow06Eigenbasis *
        alternatingSixAmbientRow06GeneratorBDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row06_generatorB_mul_eigenbasis_0_0
  · exact row06_generatorB_mul_eigenbasis_0_1
  · exact row06_generatorB_mul_eigenbasis_0_2
  · exact row06_generatorB_mul_eigenbasis_0_3
  · exact row06_generatorB_mul_eigenbasis_1_0
  · exact row06_generatorB_mul_eigenbasis_1_1
  · exact row06_generatorB_mul_eigenbasis_1_2
  · exact row06_generatorB_mul_eigenbasis_1_3
  · exact row06_generatorB_mul_eigenbasis_2_0
  · exact row06_generatorB_mul_eigenbasis_2_1
  · exact row06_generatorB_mul_eigenbasis_2_2
  · exact row06_generatorB_mul_eigenbasis_2_3
  · exact row06_generatorB_mul_eigenbasis_3_0
  · exact row06_generatorB_mul_eigenbasis_3_1
  · exact row06_generatorB_mul_eigenbasis_3_2
  · exact row06_generatorB_mul_eigenbasis_3_3


private theorem row06_transformedGeneratorA_0_0 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        0 0 =
      alternatingSixAmbientRow06TransformedGeneratorA
        0 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 23 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 33 + ((1 / 4) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 45 + ((1 / 4) : ℂ) * ζ ^ 49)
private theorem row06_transformedGeneratorA_0_1 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        0 1 =
      alternatingSixAmbientRow06TransformedGeneratorA
        0 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 2) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 5 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 9 + ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 13 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 15 + ((3 / 4) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 19 + ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 29 + ((1 / 4) : ℂ) * ζ ^ 33 - ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 35 - ((1 / 4) : ℂ) * ζ ^ 39 + ((1 / 4) : ℂ) * ζ ^ 43)
private theorem row06_transformedGeneratorA_0_2 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        0 2 =
      alternatingSixAmbientRow06TransformedGeneratorA
        0 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 5 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 9 - ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 13 + ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 23 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 29 - ((1 / 4) : ℂ) * ζ ^ 33 - ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 45 - ((1 / 4) : ℂ) * ζ ^ 49)
private theorem row06_transformedGeneratorA_0_3 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        0 3 =
      alternatingSixAmbientRow06TransformedGeneratorA
        0 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) * ζ ^ 3 + ((1 / 4) : ℂ) * ζ ^ 5 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 9 + ((3 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 13 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 29 + ((1 / 4) : ℂ) * ζ ^ 33 + ((1 / 4) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 35 + ((1 / 4) : ℂ) * ζ ^ 39 - ((1 / 4) : ℂ) * ζ ^ 43)
private theorem row06_transformedGeneratorA_1_0 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        1 0 =
      alternatingSixAmbientRow06TransformedGeneratorA
        1 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 2) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 5 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 9 - ((3 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 13 + ((3 / 4) : ℂ) * ζ ^ 14 - ((3 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 29 + ((1 / 4) : ℂ) * ζ ^ 33 - ((1 / 4) : ℂ) * ζ ^ 35 + ((1 / 4) : ℂ) * ζ ^ 39 - ((1 / 4) : ℂ) * ζ ^ 40 - ((1 / 4) : ℂ) * ζ ^ 43 + ((1 / 4) : ℂ) * ζ ^ 44 + ((1 / 4) : ℂ) * ζ ^ 45 - ((1 / 4) : ℂ) * ζ ^ 49)
private theorem row06_transformedGeneratorA_1_1 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        1 1 =
      alternatingSixAmbientRow06TransformedGeneratorA
        1 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 5 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 9 - ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 13 + ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 33 - ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 38 + ((1 / 4) : ℂ) * ζ ^ 40 - ((1 / 4) : ℂ) * ζ ^ 44)
private theorem row06_transformedGeneratorA_1_2 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        1 2 =
      alternatingSixAmbientRow06TransformedGeneratorA
        1 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 13 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 28 - ((3 / 4) : ℂ) * ζ ^ 29 + ((1 / 4) : ℂ) * ζ ^ 33 - ((1 / 4) : ℂ) * ζ ^ 35 + ((1 / 4) : ℂ) * ζ ^ 39 + ((1 / 4) : ℂ) * ζ ^ 40 - ((1 / 4) : ℂ) * ζ ^ 43 - ((1 / 4) : ℂ) * ζ ^ 44 - ((1 / 4) : ℂ) * ζ ^ 45 + ((1 / 4) : ℂ) * ζ ^ 49)
private theorem row06_transformedGeneratorA_1_3 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        1 3 =
      alternatingSixAmbientRow06TransformedGeneratorA
        1 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 5 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 9 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 13 - ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 26 - ((1 / 2) : ℂ) * ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 33 + ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 2) : ℂ) * ζ ^ 35 - ((1 / 4) : ℂ) * ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 39 - ((1 / 4) : ℂ) * ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 43 + ((1 / 4) : ℂ) * ζ ^ 44)
private theorem row06_transformedGeneratorA_2_0 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        2 0 =
      alternatingSixAmbientRow06TransformedGeneratorA
        2 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 5 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 9 - ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 13 - ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 23 + ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 29 + ((1 / 4) : ℂ) * ζ ^ 33 - ((1 / 4) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 45 + ((1 / 4) : ℂ) * ζ ^ 49)
private theorem row06_transformedGeneratorA_2_1 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        2 1 =
      alternatingSixAmbientRow06TransformedGeneratorA
        2 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 5 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 9 + ((3 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 13 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 29 - ((1 / 4) : ℂ) * ζ ^ 33 + ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 35 - ((1 / 4) : ℂ) * ζ ^ 39 + ((1 / 4) : ℂ) * ζ ^ 43)
private theorem row06_transformedGeneratorA_2_2 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        2 2 =
      alternatingSixAmbientRow06TransformedGeneratorA
        2 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 23 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 33 + ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 45 - ((1 / 4) : ℂ) * ζ ^ 49)
private theorem row06_transformedGeneratorA_2_3 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        2 3 =
      alternatingSixAmbientRow06TransformedGeneratorA
        2 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 2) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 5 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 9 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 13 - ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 15 + ((3 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 19 + ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 29 - ((1 / 4) : ℂ) * ζ ^ 33 - ((1 / 4) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 35 + ((1 / 4) : ℂ) * ζ ^ 39 - ((1 / 4) : ℂ) * ζ ^ 43)
private theorem row06_transformedGeneratorA_3_0 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        3 0 =
      alternatingSixAmbientRow06TransformedGeneratorA
        3 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (-((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 13 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 28 + ((3 / 4) : ℂ) * ζ ^ 29 - ((1 / 4) : ℂ) * ζ ^ 33 + ((1 / 4) : ℂ) * ζ ^ 35 - ((1 / 4) : ℂ) * ζ ^ 39 + ((1 / 4) : ℂ) * ζ ^ 40 + ((1 / 4) : ℂ) * ζ ^ 43 - ((1 / 4) : ℂ) * ζ ^ 44 + ((1 / 4) : ℂ) * ζ ^ 45 - ((1 / 4) : ℂ) * ζ ^ 49)
private theorem row06_transformedGeneratorA_3_1 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        3 1 =
      alternatingSixAmbientRow06TransformedGeneratorA
        3 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 5 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 9 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 13 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 26 - ((1 / 2) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 33 + ((1 / 4) : ℂ) * ζ ^ 34 - ((1 / 2) : ℂ) * ζ ^ 35 - ((1 / 4) : ℂ) * ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 39 - ((1 / 4) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 43 + ((1 / 4) : ℂ) * ζ ^ 44)
private theorem row06_transformedGeneratorA_3_2 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        3 2 =
      alternatingSixAmbientRow06TransformedGeneratorA
        3 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 2) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 5 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 9 - ((3 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 13 + ((3 / 4) : ℂ) * ζ ^ 14 - ((3 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 25 + ((1 / 4) : ℂ) * ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 29 - ((1 / 4) : ℂ) * ζ ^ 33 + ((1 / 4) : ℂ) * ζ ^ 35 - ((1 / 4) : ℂ) * ζ ^ 39 - ((1 / 4) : ℂ) * ζ ^ 40 + ((1 / 4) : ℂ) * ζ ^ 43 + ((1 / 4) : ℂ) * ζ ^ 44 - ((1 / 4) : ℂ) * ζ ^ 45 + ((1 / 4) : ℂ) * ζ ^ 49)
private theorem row06_transformedGeneratorA_3_3 :
    (alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis)
        3 3 =
      alternatingSixAmbientRow06TransformedGeneratorA
        3 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow06Eigenbasis,
      alternatingSixAmbientRow06EigenbasisInverse,
      alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixAmbientRow06TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row06 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 5 - ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 9 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 13 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 33 - ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 38 + ((1 / 4) : ℂ) * ζ ^ 40 - ((1 / 4) : ℂ) * ζ ^ 44)
/-- Exact conjugation formula for the row 06 first
generator. -/
theorem alternatingSixAmbientRow06TransformedGeneratorA_eq :
    alternatingSixAmbientRow06EigenbasisInverse *
        alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixAmbientRow06Eigenbasis =
      alternatingSixAmbientRow06TransformedGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row06_transformedGeneratorA_0_0
  · exact row06_transformedGeneratorA_0_1
  · exact row06_transformedGeneratorA_0_2
  · exact row06_transformedGeneratorA_0_3
  · exact row06_transformedGeneratorA_1_0
  · exact row06_transformedGeneratorA_1_1
  · exact row06_transformedGeneratorA_1_2
  · exact row06_transformedGeneratorA_1_3
  · exact row06_transformedGeneratorA_2_0
  · exact row06_transformedGeneratorA_2_1
  · exact row06_transformedGeneratorA_2_2
  · exact row06_transformedGeneratorA_2_3
  · exact row06_transformedGeneratorA_3_0
  · exact row06_transformedGeneratorA_3_1
  · exact row06_transformedGeneratorA_3_2
  · exact row06_transformedGeneratorA_3_3


end InductiveMcKay
end McKayConjecture
