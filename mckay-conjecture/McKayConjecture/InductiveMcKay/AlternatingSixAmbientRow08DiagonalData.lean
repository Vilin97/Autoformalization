/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixDegreeFourSixEigenvalues
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixDataDegreeFiveTenFifteen

/-!
# Checked diagonal data for ambient row 08

This generated module records an exact eigenbasis for the second generator
and the first generator in that basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenvalue block labels for row 08. -/
def alternatingSixAmbientRow08EigenvalueLabel :
    Fin 5 → Fin 4 :=
  ![0, 1, 2, 2, 3]

/-- Second-generator eigenvalues, including their multiplicities. -/
def alternatingSixAmbientRow08GeneratorBEigenvalue :
    Fin 5 → ℂ :=
  fun i ↦
    alternatingSixOrderFourEigenvalue
      (alternatingSixAmbientRow08EigenvalueLabel i)

/-- Diagonal form of the row 08 second generator. -/
def alternatingSixAmbientRow08GeneratorBDiagonal :
    Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal
    alternatingSixAmbientRow08GeneratorBEigenvalue

/-- Checked eigenbasis for the row 08 second generator. -/
def alternatingSixAmbientRow08Eigenbasis :
    Matrix (Fin 5) (Fin 5) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 30)],
      alternatingSixCyclotomicValue [(-1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(-1, 30)]],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0)],
      alternatingSixCyclotomicValue [((-1 / 2), 0)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 2), 30)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 30)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(-1, 30)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue []]
  ]

/-- Checked inverse of the row 08 eigenbasis. -/
def alternatingSixAmbientRow08EigenbasisInverse :
    Matrix (Fin 5) (Fin 5) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((-1 / 4), 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [((3 / 4), 0)],
      alternatingSixCyclotomicValue [((-1 / 2), 0)],
      alternatingSixCyclotomicValue [((1 / 2), 0)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0)],
      alternatingSixCyclotomicValue []],
    ![alternatingSixCyclotomicValue [((-1 / 2), 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [((1 / 2), 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue []],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0)],
      alternatingSixCyclotomicValue []]
  ]

/-- The row 08 first generator in the checked diagonal basis. -/
def alternatingSixAmbientRow08TransformedGeneratorA :
    Matrix (Fin 5) (Fin 5) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((1 / 4), 0)],
      alternatingSixCyclotomicValue [((-3 / 8), 0), ((3 / 8), 30)],
      alternatingSixCyclotomicValue [((-9 / 8), 0)],
      alternatingSixCyclotomicValue [((-3 / 8), 0)],
      alternatingSixCyclotomicValue [((-3 / 8), 0), ((-3 / 8), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((-3 / 8), 30)],
      alternatingSixCyclotomicValue [((3 / 8), 0), ((-1 / 8), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 0)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0)],
      alternatingSixCyclotomicValue [((-1 / 4), 0)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(-1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((3 / 8), 30)],
      alternatingSixCyclotomicValue [((3 / 8), 0), ((1 / 8), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0)]]
  ]

macro "close_cyclotomic_row08" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)


private theorem row08_eigenbasisInverse_mul_0_0 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        0 0 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        0 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_0_1 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        0 1 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        0 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_0_2 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        0 2 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        0 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_0_3 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        0 3 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        0 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_0_4 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        0 4 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        0 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_1_0 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        1 0 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        1 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_1_1 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        1 1 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        1 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row08_eigenbasisInverse_mul_1_2 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        1 2 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        1 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_1_3 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        1 3 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        1 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_1_4 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        1 4 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        1 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row08_eigenbasisInverse_mul_2_0 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        2 0 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        2 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_2_1 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        2 1 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        2 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_2_2 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        2 2 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        2 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_2_3 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        2 3 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        2 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_2_4 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        2 4 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        2 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_3_0 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        3 0 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        3 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_3_1 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        3 1 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        3 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_3_2 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        3 2 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        3 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_3_3 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        3 3 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        3 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_3_4 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        3 4 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        3 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_4_0 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        4 0 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        4 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_4_1 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        4 1 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        4 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row08_eigenbasisInverse_mul_4_2 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        4 2 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        4 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_4_3 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        4 3 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        4 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_eigenbasisInverse_mul_4_4 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis)
        4 4 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        4 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28)
/-- The displayed row 08 matrix is a left inverse of its
eigenbasis. -/
theorem alternatingSixAmbientRow08EigenbasisInverse_mul :
    alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixAmbientRow08Eigenbasis =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row08_eigenbasisInverse_mul_0_0
  · exact row08_eigenbasisInverse_mul_0_1
  · exact row08_eigenbasisInverse_mul_0_2
  · exact row08_eigenbasisInverse_mul_0_3
  · exact row08_eigenbasisInverse_mul_0_4
  · exact row08_eigenbasisInverse_mul_1_0
  · exact row08_eigenbasisInverse_mul_1_1
  · exact row08_eigenbasisInverse_mul_1_2
  · exact row08_eigenbasisInverse_mul_1_3
  · exact row08_eigenbasisInverse_mul_1_4
  · exact row08_eigenbasisInverse_mul_2_0
  · exact row08_eigenbasisInverse_mul_2_1
  · exact row08_eigenbasisInverse_mul_2_2
  · exact row08_eigenbasisInverse_mul_2_3
  · exact row08_eigenbasisInverse_mul_2_4
  · exact row08_eigenbasisInverse_mul_3_0
  · exact row08_eigenbasisInverse_mul_3_1
  · exact row08_eigenbasisInverse_mul_3_2
  · exact row08_eigenbasisInverse_mul_3_3
  · exact row08_eigenbasisInverse_mul_3_4
  · exact row08_eigenbasisInverse_mul_4_0
  · exact row08_eigenbasisInverse_mul_4_1
  · exact row08_eigenbasisInverse_mul_4_2
  · exact row08_eigenbasisInverse_mul_4_3
  · exact row08_eigenbasisInverse_mul_4_4

/-- The displayed row 08 inverse is also a right inverse. -/
theorem alternatingSixAmbientRow08Eigenbasis_mul_inverse :
    alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow08EigenbasisInverse_mul


private theorem row08_generatorB_mul_eigenbasis_0_0 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        0 0 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        0 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_generatorB_mul_eigenbasis_0_1 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        0 1 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        0 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)
private theorem row08_generatorB_mul_eigenbasis_0_2 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        0 2 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        0 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 + ζ ^ 20 - ζ ^ 24 + ζ ^ 28)
private theorem row08_generatorB_mul_eigenbasis_0_3 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        0 3 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        0 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_generatorB_mul_eigenbasis_0_4 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        0 4 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        0 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28 + ζ ^ 60 - ζ ^ 64 + ζ ^ 68 + ζ ^ 80 - ζ ^ 84 + ζ ^ 88)
private theorem row08_generatorB_mul_eigenbasis_1_0 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        1 0 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        1 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_generatorB_mul_eigenbasis_1_1 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        1 1 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        1 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row08_generatorB_mul_eigenbasis_1_2 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        1 2 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        1 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row08_generatorB_mul_eigenbasis_1_3 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        1 3 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        1 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row08_generatorB_mul_eigenbasis_1_4 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        1 4 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        1 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30 + ((1 / 2) : ℂ) * ζ ^ 34 - ((1 / 2) : ℂ) * ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 58 - ((1 / 2) : ℂ) * ζ ^ 60 + ((1 / 2) : ℂ) * ζ ^ 64 - ((1 / 2) : ℂ) * ζ ^ 68 - ((1 / 2) : ℂ) * ζ ^ 80 + ((1 / 2) : ℂ) * ζ ^ 84 - ((1 / 2) : ℂ) * ζ ^ 88)
private theorem row08_generatorB_mul_eigenbasis_2_0 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        2 0 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        2 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_generatorB_mul_eigenbasis_2_1 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        2 1 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        2 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)
private theorem row08_generatorB_mul_eigenbasis_2_2 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        2 2 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        2 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)
private theorem row08_generatorB_mul_eigenbasis_2_3 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        2 3 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        2 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_generatorB_mul_eigenbasis_2_4 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        2 4 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        2 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28 + ζ ^ 60 - ζ ^ 64 + ζ ^ 68 + ζ ^ 80 - ζ ^ 84 + ζ ^ 88)
private theorem row08_generatorB_mul_eigenbasis_3_0 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        3 0 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        3 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_generatorB_mul_eigenbasis_3_1 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        3 1 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        3 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_generatorB_mul_eigenbasis_3_2 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        3 2 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        3 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)
private theorem row08_generatorB_mul_eigenbasis_3_3 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        3 3 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        3 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_generatorB_mul_eigenbasis_3_4 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        3 4 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        3 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (-ζ ^ 30 + ζ ^ 34 - ζ ^ 38 - ζ ^ 50 + ζ ^ 54 - ζ ^ 58)
private theorem row08_generatorB_mul_eigenbasis_4_0 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        4 0 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        4 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_generatorB_mul_eigenbasis_4_1 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        4 1 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        4 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_generatorB_mul_eigenbasis_4_2 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        4 2 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        4 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_generatorB_mul_eigenbasis_4_3 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        4 3 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        4 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)
private theorem row08_generatorB_mul_eigenbasis_4_4 :
    (alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis)
        4 4 =
      (alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal)
        4 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row08_matrixB,
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08GeneratorBDiagonal,
      alternatingSixAmbientRow08GeneratorBEigenvalue,
      alternatingSixAmbientRow08EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
/-- The checked row 08 basis diagonalizes the second
generator. -/
theorem alternatingSixAmbientRow08GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row08_matrixB *
        alternatingSixAmbientRow08Eigenbasis =
      alternatingSixAmbientRow08Eigenbasis *
        alternatingSixAmbientRow08GeneratorBDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row08_generatorB_mul_eigenbasis_0_0
  · exact row08_generatorB_mul_eigenbasis_0_1
  · exact row08_generatorB_mul_eigenbasis_0_2
  · exact row08_generatorB_mul_eigenbasis_0_3
  · exact row08_generatorB_mul_eigenbasis_0_4
  · exact row08_generatorB_mul_eigenbasis_1_0
  · exact row08_generatorB_mul_eigenbasis_1_1
  · exact row08_generatorB_mul_eigenbasis_1_2
  · exact row08_generatorB_mul_eigenbasis_1_3
  · exact row08_generatorB_mul_eigenbasis_1_4
  · exact row08_generatorB_mul_eigenbasis_2_0
  · exact row08_generatorB_mul_eigenbasis_2_1
  · exact row08_generatorB_mul_eigenbasis_2_2
  · exact row08_generatorB_mul_eigenbasis_2_3
  · exact row08_generatorB_mul_eigenbasis_2_4
  · exact row08_generatorB_mul_eigenbasis_3_0
  · exact row08_generatorB_mul_eigenbasis_3_1
  · exact row08_generatorB_mul_eigenbasis_3_2
  · exact row08_generatorB_mul_eigenbasis_3_3
  · exact row08_generatorB_mul_eigenbasis_3_4
  · exact row08_generatorB_mul_eigenbasis_4_0
  · exact row08_generatorB_mul_eigenbasis_4_1
  · exact row08_generatorB_mul_eigenbasis_4_2
  · exact row08_generatorB_mul_eigenbasis_4_3
  · exact row08_generatorB_mul_eigenbasis_4_4


private theorem row08_transformedGeneratorA_0_0 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        0 0 =
      alternatingSixAmbientRow08TransformedGeneratorA
        0 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_0_1 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        0 1 =
      alternatingSixAmbientRow08TransformedGeneratorA
        0 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_0_2 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        0 2 =
      alternatingSixAmbientRow08TransformedGeneratorA
        0 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_0_3 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        0 3 =
      alternatingSixAmbientRow08TransformedGeneratorA
        0 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_0_4 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        0 4 =
      alternatingSixAmbientRow08TransformedGeneratorA
        0 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_1_0 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        1 0 =
      alternatingSixAmbientRow08TransformedGeneratorA
        1 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_1_1 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        1 1 =
      alternatingSixAmbientRow08TransformedGeneratorA
        1 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (-((3 / 8) : ℂ) + ((3 / 8) : ℂ) * ζ ^ 4 - ((3 / 8) : ℂ) * ζ ^ 8 - ((3 / 8) : ℂ) * ζ ^ 20 + ((3 / 8) : ℂ) * ζ ^ 24 - ((3 / 8) : ℂ) * ζ ^ 28)
private theorem row08_transformedGeneratorA_1_2 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        1 2 =
      alternatingSixAmbientRow08TransformedGeneratorA
        1 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_1_3 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        1 3 =
      alternatingSixAmbientRow08TransformedGeneratorA
        1 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_1_4 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        1 4 =
      alternatingSixAmbientRow08TransformedGeneratorA
        1 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (((3 / 8) : ℂ) - ((3 / 8) : ℂ) * ζ ^ 4 + ((3 / 8) : ℂ) * ζ ^ 8 + ((3 / 8) : ℂ) * ζ ^ 20 - ((3 / 8) : ℂ) * ζ ^ 24 + ((3 / 8) : ℂ) * ζ ^ 28)
private theorem row08_transformedGeneratorA_2_0 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        2 0 =
      alternatingSixAmbientRow08TransformedGeneratorA
        2 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_2_1 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        2 1 =
      alternatingSixAmbientRow08TransformedGeneratorA
        2 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_2_2 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        2 2 =
      alternatingSixAmbientRow08TransformedGeneratorA
        2 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_2_3 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        2 3 =
      alternatingSixAmbientRow08TransformedGeneratorA
        2 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_2_4 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        2 4 =
      alternatingSixAmbientRow08TransformedGeneratorA
        2 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_3_0 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        3 0 =
      alternatingSixAmbientRow08TransformedGeneratorA
        3 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_3_1 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        3 1 =
      alternatingSixAmbientRow08TransformedGeneratorA
        3 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_3_2 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        3 2 =
      alternatingSixAmbientRow08TransformedGeneratorA
        3 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_3_3 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        3 3 =
      alternatingSixAmbientRow08TransformedGeneratorA
        3 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_3_4 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        3 4 =
      alternatingSixAmbientRow08TransformedGeneratorA
        3 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_4_0 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        4 0 =
      alternatingSixAmbientRow08TransformedGeneratorA
        4 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_4_1 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        4 1 =
      alternatingSixAmbientRow08TransformedGeneratorA
        4 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (((3 / 8) : ℂ) - ((3 / 8) : ℂ) * ζ ^ 4 + ((3 / 8) : ℂ) * ζ ^ 8 + ((3 / 8) : ℂ) * ζ ^ 20 - ((3 / 8) : ℂ) * ζ ^ 24 + ((3 / 8) : ℂ) * ζ ^ 28)
private theorem row08_transformedGeneratorA_4_2 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        4 2 =
      alternatingSixAmbientRow08TransformedGeneratorA
        4 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_4_3 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        4 3 =
      alternatingSixAmbientRow08TransformedGeneratorA
        4 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 0
private theorem row08_transformedGeneratorA_4_4 :
    (alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis)
        4 4 =
      alternatingSixAmbientRow08TransformedGeneratorA
        4 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow08Eigenbasis,
      alternatingSixAmbientRow08EigenbasisInverse,
      alternatingSixFiveAmbient_row08_matrixA,
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row08 (-((3 / 8) : ℂ) + ((3 / 8) : ℂ) * ζ ^ 4 - ((3 / 8) : ℂ) * ζ ^ 8 - ((3 / 8) : ℂ) * ζ ^ 20 + ((3 / 8) : ℂ) * ζ ^ 24 - ((3 / 8) : ℂ) * ζ ^ 28)
/-- Exact conjugation formula for the row 08 first
generator. -/
theorem alternatingSixAmbientRow08TransformedGeneratorA_eq :
    alternatingSixAmbientRow08EigenbasisInverse *
        alternatingSixFiveAmbient_row08_matrixA *
        alternatingSixAmbientRow08Eigenbasis =
      alternatingSixAmbientRow08TransformedGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row08_transformedGeneratorA_0_0
  · exact row08_transformedGeneratorA_0_1
  · exact row08_transformedGeneratorA_0_2
  · exact row08_transformedGeneratorA_0_3
  · exact row08_transformedGeneratorA_0_4
  · exact row08_transformedGeneratorA_1_0
  · exact row08_transformedGeneratorA_1_1
  · exact row08_transformedGeneratorA_1_2
  · exact row08_transformedGeneratorA_1_3
  · exact row08_transformedGeneratorA_1_4
  · exact row08_transformedGeneratorA_2_0
  · exact row08_transformedGeneratorA_2_1
  · exact row08_transformedGeneratorA_2_2
  · exact row08_transformedGeneratorA_2_3
  · exact row08_transformedGeneratorA_2_4
  · exact row08_transformedGeneratorA_3_0
  · exact row08_transformedGeneratorA_3_1
  · exact row08_transformedGeneratorA_3_2
  · exact row08_transformedGeneratorA_3_3
  · exact row08_transformedGeneratorA_3_4
  · exact row08_transformedGeneratorA_4_0
  · exact row08_transformedGeneratorA_4_1
  · exact row08_transformedGeneratorA_4_2
  · exact row08_transformedGeneratorA_4_3
  · exact row08_transformedGeneratorA_4_4


end InductiveMcKay
end McKayConjecture
