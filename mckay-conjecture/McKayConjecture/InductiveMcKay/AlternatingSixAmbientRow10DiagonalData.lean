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
# Checked diagonal data for ambient row 10

This generated module records an exact eigenbasis for the second generator
and the first generator in that basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenvalue block labels for row 10. -/
def alternatingSixAmbientRow10EigenvalueLabel :
    Fin 6 → Fin 4 :=
  ![0, 0, 1, 2, 2, 3]

/-- Second-generator eigenvalues, including their multiplicities. -/
def alternatingSixAmbientRow10GeneratorBEigenvalue :
    Fin 6 → ℂ :=
  fun i ↦
    alternatingSixOrderFourEigenvalue
      (alternatingSixAmbientRow10EigenvalueLabel i)

/-- Diagonal form of the row 10 second generator. -/
def alternatingSixAmbientRow10GeneratorBDiagonal :
    Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal
    alternatingSixAmbientRow10GeneratorBEigenvalue

/-- Checked eigenbasis for the row 10 second generator. -/
def alternatingSixAmbientRow10Eigenbasis :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [(2, 0), (-1, 10), (-2, 20), (2, 30)],
      alternatingSixCyclotomicValue [(-1, 10), (1, 20)],
      alternatingSixCyclotomicValue [(1, 10), (1, 20), (-1, 30)],
      alternatingSixCyclotomicValue [((3 / 4), 0), ((1 / 4), 10), ((-1 / 4), 20)],
      alternatingSixCyclotomicValue [(1, 0), ((1 / 2), 10), ((-1 / 2), 20), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue []],
    ![alternatingSixCyclotomicValue [(-1, 0), (1, 20)],
      alternatingSixCyclotomicValue [(-1, 20)],
      alternatingSixCyclotomicValue [(-1, 10)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 10), ((3 / 4), 20)],
      alternatingSixCyclotomicValue [((-1 / 2), 10), ((1 / 2), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [(-1, 20), (1, 30)]],
    ![alternatingSixCyclotomicValue [(1, 0), (-2, 10), (1, 20)],
      alternatingSixCyclotomicValue [(-1, 0), (1, 10), (1, 20), (-1, 30)],
      alternatingSixCyclotomicValue [(1, 10), (1, 20), (-1, 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 10), ((1 / 4), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 10), ((1 / 2), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue []],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(-1, 20)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 2), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 10), ((1 / 2), 20)],
      alternatingSixCyclotomicValue [(-1, 0), (1, 10)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(-1, 0), (-1, 10), (1, 20)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(-1, 0), (1, 10), (1, 20)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)]]
  ]

/-- Checked inverse of the row 10 eigenbasis. -/
def alternatingSixAmbientRow10EigenbasisInverse :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 2), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 10), ((1 / 4), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 10), ((-1 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 10), ((1 / 4), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 20)],
      alternatingSixCyclotomicValue [((-1 / 4), 10), ((-1 / 4), 20), ((1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((-3 / 4), 0), ((-1 / 2), 10), ((1 / 2), 20), ((3 / 4), 30)],
      alternatingSixCyclotomicValue [(-1, 0), ((-1 / 2), 10), ((1 / 4), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 2), 20), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 2), 10), ((1 / 2), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 2), 10), ((1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 2), 10), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 10), ((1 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 20)],
      alternatingSixCyclotomicValue []],
    ![alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 10), ((1 / 2), 20)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 10)],
      alternatingSixCyclotomicValue [((1 / 2), 0), (1, 10), ((-1 / 2), 20), (-1, 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 20)],
      alternatingSixCyclotomicValue [(1, 0), ((-1 / 2), 20)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 10), ((-1 / 2), 20)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 4), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 2), 10)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 2), 20)],
      alternatingSixCyclotomicValue [((-3 / 4), 0), ((1 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 2), 20), ((1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 2), 20), ((-3 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 2), 10), ((-1 / 4), 20), ((-3 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 10), ((1 / 2), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 10), ((-1 / 4), 20), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 2), 10), ((-1 / 2), 20), ((-1 / 2), 30)]]
  ]

/-- The row 10 first generator in the checked diagonal basis. -/
def alternatingSixAmbientRow10TransformedGeneratorA :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 10), ((1 / 4), 20), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 2), 10), ((-1 / 2), 20), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 8), 10), ((1 / 4), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 2), 10), ((1 / 4), 20), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 2), 20), ((-3 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 0), ((3 / 4), 10), ((-1 / 4), 20)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 10), ((1 / 4), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 4), 10), ((-1 / 4), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 8), 10), ((-1 / 2), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 10), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 4), 10), ((1 / 4), 20), ((1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((3 / 4), 0), ((-3 / 4), 10), ((-1 / 4), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 10), ((1 / 4), 20), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 10), ((1 / 4), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 8), 20), ((1 / 8), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 10), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 10), ((1 / 4), 20)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 10), ((-1 / 2), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [(1, 0), ((-1 / 2), 10), ((-1 / 2), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 4), 10), ((1 / 2), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 30)]],
    ![alternatingSixCyclotomicValue [((-3 / 4), 0), ((3 / 4), 10), ((-1 / 4), 20), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 10), ((-3 / 4), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 10), ((-1 / 4), 20), ((-3 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 8), 10), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 4), 10), ((1 / 2), 20), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 10), ((1 / 4), 20), ((1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 10), ((-1 / 4), 20)],
      alternatingSixCyclotomicValue [((-1 / 4), 10), ((1 / 4), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 10), ((1 / 4), 20)],
      alternatingSixCyclotomicValue [((-1 / 4), 10), ((1 / 8), 20), ((1 / 8), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 10), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 10), ((1 / 4), 20), ((-1 / 2), 30)]]
  ]

macro "close_cyclotomic_row10" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)


private theorem row10_eigenbasisInverse_mul_0_0 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        0 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 14 + ((3 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_0_1 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        0 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18)
private theorem row10_eigenbasisInverse_mul_0_2 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        0 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_0_3 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        0 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 8) : ℂ) - ((1 / 8) : ℂ) * ζ ^ 4 + ((1 / 8) : ℂ) * ζ ^ 8 + ((3 / 16) : ℂ) * ζ ^ 10 - ((3 / 16) : ℂ) * ζ ^ 14 + ((3 / 16) : ℂ) * ζ ^ 18 + ((1 / 16) : ℂ) * ζ ^ 20 - ((1 / 16) : ℂ) * ζ ^ 24 + ((1 / 16) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_0_4 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        0 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((3 / 8) : ℂ) + ((3 / 8) : ℂ) * ζ ^ 4 - ((3 / 8) : ℂ) * ζ ^ 8 - ((1 / 8) : ℂ) * ζ ^ 10 + ((1 / 8) : ℂ) * ζ ^ 14 - ((1 / 8) : ℂ) * ζ ^ 18)
private theorem row10_eigenbasisInverse_mul_0_5 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        0 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_1_0 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        1 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 10 + ((3 / 4) : ℂ) * ζ ^ 14 - ((3 / 4) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 24 + ((3 / 2) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_1_1 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        1 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_1_2 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        1 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_1_3 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        1 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 16) : ℂ) + ((1 / 16) : ℂ) * ζ ^ 4 - ((1 / 16) : ℂ) * ζ ^ 8 - ((1 / 8) : ℂ) * ζ ^ 20 + ((1 / 8) : ℂ) * ζ ^ 24 - ((1 / 8) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_1_4 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        1 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((3 / 8) : ℂ) + ((3 / 8) : ℂ) * ζ ^ 4 - ((3 / 8) : ℂ) * ζ ^ 8 - ((5 / 8) : ℂ) * ζ ^ 10 + ((5 / 8) : ℂ) * ζ ^ 14 - ((5 / 8) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_1_5 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        1 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_2_0 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        2 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_2_1 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        2 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_2_2 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        2 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((5 / 4) : ℂ) + ((5 / 4) : ℂ) * ζ ^ 4 - ((5 / 4) : ℂ) * ζ ^ 8)
private theorem row10_eigenbasisInverse_mul_2_3 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        2 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((7 / 16) : ℂ) - ((7 / 16) : ℂ) * ζ ^ 4 + ((7 / 16) : ℂ) * ζ ^ 8 + ((3 / 8) : ℂ) * ζ ^ 10 - ((3 / 8) : ℂ) * ζ ^ 14 + ((3 / 8) : ℂ) * ζ ^ 18 + ((1 / 8) : ℂ) * ζ ^ 20 - ((1 / 8) : ℂ) * ζ ^ 24 + ((1 / 8) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_2_4 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        2 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 + ((3 / 8) : ℂ) * ζ ^ 20 - ((3 / 8) : ℂ) * ζ ^ 24 + ((3 / 8) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_2_5 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        2 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_3_0 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        3 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8)
private theorem row10_eigenbasisInverse_mul_3_1 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        3 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 + ζ ^ 20 - ζ ^ 24 + ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_3_2 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        3 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((3 / 2) : ℂ) + ((3 / 2) : ℂ) * ζ ^ 4 - ((3 / 2) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + ζ ^ 20 - ζ ^ 24 + ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_3_3 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        3 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 - ((3 / 8) : ℂ) * ζ ^ 10 + ((3 / 8) : ℂ) * ζ ^ 14 - ((3 / 8) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_3_4 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        3 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_3_5 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        3 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)
private theorem row10_eigenbasisInverse_mul_4_0 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        4 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_4_1 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        4 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8)
private theorem row10_eigenbasisInverse_mul_4_2 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        4 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_4_3 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        4 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((11 / 16) : ℂ) + ((11 / 16) : ℂ) * ζ ^ 4 - ((11 / 16) : ℂ) * ζ ^ 8)
private theorem row10_eigenbasisInverse_mul_4_4 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        4 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((5 / 8) : ℂ) + ((5 / 8) : ℂ) * ζ ^ 4 - ((5 / 8) : ℂ) * ζ ^ 8 - ((1 / 8) : ℂ) * ζ ^ 10 + ((1 / 8) : ℂ) * ζ ^ 14 - ((1 / 8) : ℂ) * ζ ^ 18)
private theorem row10_eigenbasisInverse_mul_4_5 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        4 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((3 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 4 + ((3 / 4) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_5_0 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        5 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((3 / 2) : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 24 - ((3 / 2) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_5_1 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        5 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_5_2 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        5 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_5_3 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        5 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((5 / 16) : ℂ) - ((5 / 16) : ℂ) * ζ ^ 4 + ((5 / 16) : ℂ) * ζ ^ 8 - ((3 / 8) : ℂ) * ζ ^ 10 + ((3 / 8) : ℂ) * ζ ^ 14 - ((3 / 8) : ℂ) * ζ ^ 18)
private theorem row10_eigenbasisInverse_mul_5_4 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        5 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((3 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 4 + ((3 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 8) : ℂ) * ζ ^ 20 - ((1 / 8) : ℂ) * ζ ^ 24 + ((1 / 8) : ℂ) * ζ ^ 28)
private theorem row10_eigenbasisInverse_mul_5_5 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis)
        5 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 20 + ((3 / 4) : ℂ) * ζ ^ 24 - ((3 / 4) : ℂ) * ζ ^ 28)
/-- The displayed row 10 matrix is a left inverse of its
eigenbasis. -/
theorem alternatingSixAmbientRow10EigenbasisInverse_mul :
    alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixAmbientRow10Eigenbasis =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row10_eigenbasisInverse_mul_0_0
  · exact row10_eigenbasisInverse_mul_0_1
  · exact row10_eigenbasisInverse_mul_0_2
  · exact row10_eigenbasisInverse_mul_0_3
  · exact row10_eigenbasisInverse_mul_0_4
  · exact row10_eigenbasisInverse_mul_0_5
  · exact row10_eigenbasisInverse_mul_1_0
  · exact row10_eigenbasisInverse_mul_1_1
  · exact row10_eigenbasisInverse_mul_1_2
  · exact row10_eigenbasisInverse_mul_1_3
  · exact row10_eigenbasisInverse_mul_1_4
  · exact row10_eigenbasisInverse_mul_1_5
  · exact row10_eigenbasisInverse_mul_2_0
  · exact row10_eigenbasisInverse_mul_2_1
  · exact row10_eigenbasisInverse_mul_2_2
  · exact row10_eigenbasisInverse_mul_2_3
  · exact row10_eigenbasisInverse_mul_2_4
  · exact row10_eigenbasisInverse_mul_2_5
  · exact row10_eigenbasisInverse_mul_3_0
  · exact row10_eigenbasisInverse_mul_3_1
  · exact row10_eigenbasisInverse_mul_3_2
  · exact row10_eigenbasisInverse_mul_3_3
  · exact row10_eigenbasisInverse_mul_3_4
  · exact row10_eigenbasisInverse_mul_3_5
  · exact row10_eigenbasisInverse_mul_4_0
  · exact row10_eigenbasisInverse_mul_4_1
  · exact row10_eigenbasisInverse_mul_4_2
  · exact row10_eigenbasisInverse_mul_4_3
  · exact row10_eigenbasisInverse_mul_4_4
  · exact row10_eigenbasisInverse_mul_4_5
  · exact row10_eigenbasisInverse_mul_5_0
  · exact row10_eigenbasisInverse_mul_5_1
  · exact row10_eigenbasisInverse_mul_5_2
  · exact row10_eigenbasisInverse_mul_5_3
  · exact row10_eigenbasisInverse_mul_5_4
  · exact row10_eigenbasisInverse_mul_5_5

/-- The displayed row 10 inverse is also a right inverse. -/
theorem alternatingSixAmbientRow10Eigenbasis_mul_inverse :
    alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow10EigenbasisInverse_mul


private theorem row10_generatorB_mul_eigenbasis_0_0 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        0 0 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        0 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-(2 : ℂ) + (2 : ℂ) * ζ ^ 4 - (2 : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18)
private theorem row10_generatorB_mul_eigenbasis_0_1 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        0 1 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        0 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (ζ ^ 10 - ζ ^ 14 + ζ ^ 18 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_0_2 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        0 2 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        0 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 0
private theorem row10_generatorB_mul_eigenbasis_0_3 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        0 3 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        0 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 4) : ℂ) * ζ ^ 30 + ((1 / 4) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 38 + ((1 / 4) : ℂ) * ζ ^ 40 - ((1 / 4) : ℂ) * ζ ^ 44 + ((1 / 4) : ℂ) * ζ ^ 48)
private theorem row10_generatorB_mul_eigenbasis_0_4 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        0 4 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        0 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 48 + ((1 / 2) : ℂ) * ζ ^ 50 - ((1 / 2) : ℂ) * ζ ^ 54 + ((1 / 2) : ℂ) * ζ ^ 58)
private theorem row10_generatorB_mul_eigenbasis_0_5 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        0 5 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        0 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 0
private theorem row10_generatorB_mul_eigenbasis_1_0 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        1 0 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        1 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((3 / 2) : ℂ) - ((3 / 2) : ℂ) * ζ ^ 4 + ((3 / 2) : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 10 - (2 : ℂ) * ζ ^ 14 + (2 : ℂ) * ζ ^ 18 - (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_1_1 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        1 1 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        1 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_1_2 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        1 2 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        1 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_1_3 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        1 3 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        1 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((11 / 8) : ℂ) - ((11 / 8) : ℂ) * ζ ^ 4 + ((11 / 8) : ℂ) * ζ ^ 8 + ((3 / 8) : ℂ) * ζ ^ 10 - ((3 / 8) : ℂ) * ζ ^ 14 + ((3 / 8) : ℂ) * ζ ^ 18 - ((3 / 8) : ℂ) * ζ ^ 20 + ((3 / 8) : ℂ) * ζ ^ 24 - ((3 / 8) : ℂ) * ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 30 - ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 38 - ((3 / 4) : ℂ) * ζ ^ 40 + ((3 / 4) : ℂ) * ζ ^ 44 - ((3 / 4) : ℂ) * ζ ^ 48)
private theorem row10_generatorB_mul_eigenbasis_1_4 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        1 4 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        1 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 + ((3 / 2) : ℂ) * ζ ^ 10 - ((3 / 2) : ℂ) * ζ ^ 14 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 44 - ((1 / 2) : ℂ) * ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 58)
private theorem row10_generatorB_mul_eigenbasis_1_5 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        1 5 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        1 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28 + ζ ^ 50 - ζ ^ 54 + ζ ^ 58 - ζ ^ 60 + ζ ^ 64 - ζ ^ 68 + ζ ^ 70 - ζ ^ 74 + ζ ^ 78 - ζ ^ 80 + ζ ^ 84 - ζ ^ 88)
private theorem row10_generatorB_mul_eigenbasis_2_0 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        2 0 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        2 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((7 / 2) : ℂ) + ((7 / 2) : ℂ) * ζ ^ 4 - ((7 / 2) : ℂ) * ζ ^ 8 + (3 : ℂ) * ζ ^ 10 - (3 : ℂ) * ζ ^ 14 + (3 : ℂ) * ζ ^ 18)
private theorem row10_generatorB_mul_eigenbasis_2_1 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        2 1 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        2 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_2_2 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        2 2 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        2 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_2_3 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        2 3 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        2 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 8) : ℂ) - ((1 / 8) : ℂ) * ζ ^ 4 + ((1 / 8) : ℂ) * ζ ^ 8 + ((3 / 8) : ℂ) * ζ ^ 10 - ((3 / 8) : ℂ) * ζ ^ 14 + ((3 / 8) : ℂ) * ζ ^ 18 + ((3 / 8) : ℂ) * ζ ^ 20 - ((3 / 8) : ℂ) * ζ ^ 24 + ((3 / 8) : ℂ) * ζ ^ 28 - ((3 / 4) : ℂ) * ζ ^ 30 + ((3 / 4) : ℂ) * ζ ^ 34 - ((3 / 4) : ℂ) * ζ ^ 38 - ((1 / 4) : ℂ) * ζ ^ 40 + ((1 / 4) : ℂ) * ζ ^ 44 - ((1 / 4) : ℂ) * ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 58)
private theorem row10_generatorB_mul_eigenbasis_2_4 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        2 4 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        2 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 - ζ ^ 30 + ζ ^ 34 - ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 44 - ((1 / 2) : ℂ) * ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 58)
private theorem row10_generatorB_mul_eigenbasis_2_5 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        2 5 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        2 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_3_0 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        3 0 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        3 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18)
private theorem row10_generatorB_mul_eigenbasis_3_1 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        3 1 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        3 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18)
private theorem row10_generatorB_mul_eigenbasis_3_2 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        3 2 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        3 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 0
private theorem row10_generatorB_mul_eigenbasis_3_3 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        3 3 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        3 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((3 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 4 + ((3 / 4) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 14 + ((3 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 30 + ((1 / 4) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 44 - ((1 / 2) : ℂ) * ζ ^ 48 - ((1 / 4) : ℂ) * ζ ^ 50 + ((1 / 4) : ℂ) * ζ ^ 54 - ((1 / 4) : ℂ) * ζ ^ 58)
private theorem row10_generatorB_mul_eigenbasis_3_4 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        3 4 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        3 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((3 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 4 + ((3 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30 + ((1 / 2) : ℂ) * ζ ^ 34 - ((1 / 2) : ℂ) * ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 44 - ((1 / 2) : ℂ) * ζ ^ 48)
private theorem row10_generatorB_mul_eigenbasis_3_5 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        3 5 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        3 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28 + ζ ^ 30 - ζ ^ 34 + ζ ^ 38 - ζ ^ 40 + ζ ^ 44 - ζ ^ 48 + ζ ^ 50 - ζ ^ 54 + ζ ^ 58 - ζ ^ 60 + ζ ^ 64 - ζ ^ 68)
private theorem row10_generatorB_mul_eigenbasis_4_0 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        4 0 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        4 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 - (2 : ℂ) * ζ ^ 10 + (2 : ℂ) * ζ ^ 14 - (2 : ℂ) * ζ ^ 18 - (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_4_1 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        4 1 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        4 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_4_2 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        4 2 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        4 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 ((2 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18)
private theorem row10_generatorB_mul_eigenbasis_4_3 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        4 3 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        4 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 20 + ((3 / 4) : ℂ) * ζ ^ 24 - ((3 / 4) : ℂ) * ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_4_4 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        4 4 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        4 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((3 / 2) : ℂ) - ((3 / 2) : ℂ) * ζ ^ 4 + ((3 / 2) : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_4_5 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        4 5 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        4 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28 + ζ ^ 30 - ζ ^ 34 + ζ ^ 38 - ζ ^ 40 + ζ ^ 44 - ζ ^ 48 - ζ ^ 60 + ζ ^ 64 - ζ ^ 68 - ζ ^ 70 + ζ ^ 74 - ζ ^ 78)
private theorem row10_generatorB_mul_eigenbasis_5_0 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        5 0 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        5 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-(2 : ℂ) + (2 : ℂ) * ζ ^ 4 - (2 : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 24 + (2 : ℂ) * ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_5_1 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        5 1 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        5 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-(2 : ℂ) + (2 : ℂ) * ζ ^ 4 - (2 : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 + ζ ^ 20 - ζ ^ 24 + ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_5_2 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        5 2 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        5 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18)
private theorem row10_generatorB_mul_eigenbasis_5_3 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        5 3 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        5 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_5_4 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        5 4 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        5 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((3 / 2) : ℂ) + ((3 / 2) : ℂ) * ζ ^ 4 - ((3 / 2) : ℂ) * ζ ^ 8 - ((3 / 2) : ℂ) * ζ ^ 10 + ((3 / 2) : ℂ) * ζ ^ 14 - ((3 / 2) : ℂ) * ζ ^ 18 - (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 28)
private theorem row10_generatorB_mul_eigenbasis_5_5 :
    (alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis)
        5 5 =
      (alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal)
        5 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row10_matrixB,
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10GeneratorBDiagonal,
      alternatingSixAmbientRow10GeneratorBEigenvalue,
      alternatingSixAmbientRow10EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-ζ ^ 30 + ζ ^ 34 - ζ ^ 38 - ζ ^ 50 + ζ ^ 54 - ζ ^ 58)
/-- The checked row 10 basis diagonalizes the second
generator. -/
theorem alternatingSixAmbientRow10GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row10_matrixB *
        alternatingSixAmbientRow10Eigenbasis =
      alternatingSixAmbientRow10Eigenbasis *
        alternatingSixAmbientRow10GeneratorBDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row10_generatorB_mul_eigenbasis_0_0
  · exact row10_generatorB_mul_eigenbasis_0_1
  · exact row10_generatorB_mul_eigenbasis_0_2
  · exact row10_generatorB_mul_eigenbasis_0_3
  · exact row10_generatorB_mul_eigenbasis_0_4
  · exact row10_generatorB_mul_eigenbasis_0_5
  · exact row10_generatorB_mul_eigenbasis_1_0
  · exact row10_generatorB_mul_eigenbasis_1_1
  · exact row10_generatorB_mul_eigenbasis_1_2
  · exact row10_generatorB_mul_eigenbasis_1_3
  · exact row10_generatorB_mul_eigenbasis_1_4
  · exact row10_generatorB_mul_eigenbasis_1_5
  · exact row10_generatorB_mul_eigenbasis_2_0
  · exact row10_generatorB_mul_eigenbasis_2_1
  · exact row10_generatorB_mul_eigenbasis_2_2
  · exact row10_generatorB_mul_eigenbasis_2_3
  · exact row10_generatorB_mul_eigenbasis_2_4
  · exact row10_generatorB_mul_eigenbasis_2_5
  · exact row10_generatorB_mul_eigenbasis_3_0
  · exact row10_generatorB_mul_eigenbasis_3_1
  · exact row10_generatorB_mul_eigenbasis_3_2
  · exact row10_generatorB_mul_eigenbasis_3_3
  · exact row10_generatorB_mul_eigenbasis_3_4
  · exact row10_generatorB_mul_eigenbasis_3_5
  · exact row10_generatorB_mul_eigenbasis_4_0
  · exact row10_generatorB_mul_eigenbasis_4_1
  · exact row10_generatorB_mul_eigenbasis_4_2
  · exact row10_generatorB_mul_eigenbasis_4_3
  · exact row10_generatorB_mul_eigenbasis_4_4
  · exact row10_generatorB_mul_eigenbasis_4_5
  · exact row10_generatorB_mul_eigenbasis_5_0
  · exact row10_generatorB_mul_eigenbasis_5_1
  · exact row10_generatorB_mul_eigenbasis_5_2
  · exact row10_generatorB_mul_eigenbasis_5_3
  · exact row10_generatorB_mul_eigenbasis_5_4
  · exact row10_generatorB_mul_eigenbasis_5_5


private theorem row10_transformedGeneratorA_0_0 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        0 0 =
      alternatingSixAmbientRow10TransformedGeneratorA
        0 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 - ((15 / 8) : ℂ) * ζ ^ 10 + ((15 / 8) : ℂ) * ζ ^ 14 - ((15 / 8) : ℂ) * ζ ^ 18 - ((13 / 8) : ℂ) * ζ ^ 20 + ((13 / 8) : ℂ) * ζ ^ 24 - ((13 / 8) : ℂ) * ζ ^ 28 + ((9 / 8) : ℂ) * ζ ^ 30 - ((9 / 8) : ℂ) * ζ ^ 34 + ((9 / 8) : ℂ) * ζ ^ 38 + ((1 / 4) : ℂ) * ζ ^ 40 - ((1 / 4) : ℂ) * ζ ^ 44 + ((1 / 4) : ℂ) * ζ ^ 48 - ζ ^ 50 + ζ ^ 54 - ζ ^ 58)
private theorem row10_transformedGeneratorA_0_1 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        0 1 =
      alternatingSixAmbientRow10TransformedGeneratorA
        0 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((5 / 8) : ℂ) + ((5 / 8) : ℂ) * ζ ^ 4 - ((5 / 8) : ℂ) * ζ ^ 8 - ((3 / 8) : ℂ) * ζ ^ 10 + ((3 / 8) : ℂ) * ζ ^ 14 - ((3 / 8) : ℂ) * ζ ^ 18 + ((9 / 8) : ℂ) * ζ ^ 20 - ((9 / 8) : ℂ) * ζ ^ 24 + ((9 / 8) : ℂ) * ζ ^ 28 + ((5 / 4) : ℂ) * ζ ^ 30 - ((5 / 4) : ℂ) * ζ ^ 34 + ((5 / 4) : ℂ) * ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 44 - ((1 / 2) : ℂ) * ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_0_2 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        0 2 =
      alternatingSixAmbientRow10TransformedGeneratorA
        0 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 14 + ((3 / 4) : ℂ) * ζ ^ 18 + ζ ^ 20 - ζ ^ 24 + ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 30 - ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 48)
private theorem row10_transformedGeneratorA_0_3 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        0 3 =
      alternatingSixAmbientRow10TransformedGeneratorA
        0 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((9 / 16) : ℂ) + ((9 / 16) : ℂ) * ζ ^ 4 - ((9 / 16) : ℂ) * ζ ^ 8 - ((5 / 4) : ℂ) * ζ ^ 10 + ((5 / 4) : ℂ) * ζ ^ 14 - ((5 / 4) : ℂ) * ζ ^ 18 - ((5 / 16) : ℂ) * ζ ^ 20 + ((5 / 16) : ℂ) * ζ ^ 24 - ((5 / 16) : ℂ) * ζ ^ 28 + ((1 / 8) : ℂ) * ζ ^ 30 - ((1 / 8) : ℂ) * ζ ^ 34 + ((1 / 8) : ℂ) * ζ ^ 38 + ((1 / 8) : ℂ) * ζ ^ 40 - ((1 / 8) : ℂ) * ζ ^ 44 + ((1 / 8) : ℂ) * ζ ^ 48 + ((1 / 8) : ℂ) * ζ ^ 50 - ((1 / 8) : ℂ) * ζ ^ 54 + ((1 / 8) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_0_4 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        0 4 =
      alternatingSixAmbientRow10TransformedGeneratorA
        0 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((11 / 16) : ℂ) + ((11 / 16) : ℂ) * ζ ^ 4 - ((11 / 16) : ℂ) * ζ ^ 8 - ((9 / 8) : ℂ) * ζ ^ 10 + ((9 / 8) : ℂ) * ζ ^ 14 - ((9 / 8) : ℂ) * ζ ^ 18 - ((11 / 16) : ℂ) * ζ ^ 20 + ((11 / 16) : ℂ) * ζ ^ 24 - ((11 / 16) : ℂ) * ζ ^ 28 + ((3 / 8) : ℂ) * ζ ^ 30 - ((3 / 8) : ℂ) * ζ ^ 34 + ((3 / 8) : ℂ) * ζ ^ 38 + ((11 / 16) : ℂ) * ζ ^ 40 - ((11 / 16) : ℂ) * ζ ^ 44 + ((11 / 16) : ℂ) * ζ ^ 48 + ((3 / 8) : ℂ) * ζ ^ 50 - ((3 / 8) : ℂ) * ζ ^ 54 + ((3 / 8) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_0_5 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        0 5 =
      alternatingSixAmbientRow10TransformedGeneratorA
        0 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((3 / 8) : ℂ) - ((3 / 8) : ℂ) * ζ ^ 4 + ((3 / 8) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18 - ((5 / 8) : ℂ) * ζ ^ 20 + ((5 / 8) : ℂ) * ζ ^ 24 - ((5 / 8) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 30 + ((1 / 4) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 38 + ((3 / 8) : ℂ) * ζ ^ 40 - ((3 / 8) : ℂ) * ζ ^ 44 + ((3 / 8) : ℂ) * ζ ^ 48 - ((1 / 4) : ℂ) * ζ ^ 50 + ((1 / 4) : ℂ) * ζ ^ 54 - ((1 / 4) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_1_0 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        1 0 =
      alternatingSixAmbientRow10TransformedGeneratorA
        1 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 10 + ((5 / 2) : ℂ) * ζ ^ 14 - ((5 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28 + ((3 / 2) : ℂ) * ζ ^ 30 - ((3 / 2) : ℂ) * ζ ^ 34 + ((3 / 2) : ℂ) * ζ ^ 38 - ((5 / 2) : ℂ) * ζ ^ 40 + ((5 / 2) : ℂ) * ζ ^ 44 - ((5 / 2) : ℂ) * ζ ^ 48 - (2 : ℂ) * ζ ^ 50 + (2 : ℂ) * ζ ^ 54 - (2 : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_1_1 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        1 1 =
      alternatingSixAmbientRow10TransformedGeneratorA
        1 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ((3 / 2) : ℂ) * ζ ^ 10 + ((3 / 2) : ℂ) * ζ ^ 14 - ((3 / 2) : ℂ) * ζ ^ 18 + (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 24 + (2 : ℂ) * ζ ^ 28 + (2 : ℂ) * ζ ^ 30 - (2 : ℂ) * ζ ^ 34 + (2 : ℂ) * ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 44 - ((1 / 2) : ℂ) * ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_1_2 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        1 2 =
      alternatingSixAmbientRow10TransformedGeneratorA
        1 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28 + (2 : ℂ) * ζ ^ 30 - (2 : ℂ) * ζ ^ 34 + (2 : ℂ) * ζ ^ 38 + ((5 / 4) : ℂ) * ζ ^ 40 - ((5 / 4) : ℂ) * ζ ^ 44 + ((5 / 4) : ℂ) * ζ ^ 48 + ((1 / 2) : ℂ) * ζ ^ 50 - ((1 / 2) : ℂ) * ζ ^ 54 + ((1 / 2) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_1_3 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        1 3 =
      alternatingSixAmbientRow10TransformedGeneratorA
        1 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((21 / 16) : ℂ) + ((21 / 16) : ℂ) * ζ ^ 4 - ((21 / 16) : ℂ) * ζ ^ 8 - ((9 / 16) : ℂ) * ζ ^ 10 + ((9 / 16) : ℂ) * ζ ^ 14 - ((9 / 16) : ℂ) * ζ ^ 18 + ((13 / 16) : ℂ) * ζ ^ 20 - ((13 / 16) : ℂ) * ζ ^ 24 + ((13 / 16) : ℂ) * ζ ^ 28 - ((3 / 8) : ℂ) * ζ ^ 30 + ((3 / 8) : ℂ) * ζ ^ 34 - ((3 / 8) : ℂ) * ζ ^ 38 - ((13 / 16) : ℂ) * ζ ^ 40 + ((13 / 16) : ℂ) * ζ ^ 44 - ((13 / 16) : ℂ) * ζ ^ 48)
private theorem row10_transformedGeneratorA_1_4 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        1 4 =
      alternatingSixAmbientRow10TransformedGeneratorA
        1 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((5 / 4) : ℂ) + ((5 / 4) : ℂ) * ζ ^ 4 - ((5 / 4) : ℂ) * ζ ^ 8 - ((19 / 8) : ℂ) * ζ ^ 10 + ((19 / 8) : ℂ) * ζ ^ 14 - ((19 / 8) : ℂ) * ζ ^ 18 - ((1 / 8) : ℂ) * ζ ^ 20 + ((1 / 8) : ℂ) * ζ ^ 24 - ((1 / 8) : ℂ) * ζ ^ 28 + ((9 / 8) : ℂ) * ζ ^ 30 - ((9 / 8) : ℂ) * ζ ^ 34 + ((9 / 8) : ℂ) * ζ ^ 38 + ((3 / 8) : ℂ) * ζ ^ 40 - ((3 / 8) : ℂ) * ζ ^ 44 + ((3 / 8) : ℂ) * ζ ^ 48)
private theorem row10_transformedGeneratorA_1_5 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        1 5 =
      alternatingSixAmbientRow10TransformedGeneratorA
        1 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 - ((5 / 4) : ℂ) * ζ ^ 10 + ((5 / 4) : ℂ) * ζ ^ 14 - ((5 / 4) : ℂ) * ζ ^ 18 - ((5 / 4) : ℂ) * ζ ^ 20 + ((5 / 4) : ℂ) * ζ ^ 24 - ((5 / 4) : ℂ) * ζ ^ 28 + ((5 / 4) : ℂ) * ζ ^ 30 - ((5 / 4) : ℂ) * ζ ^ 34 + ((5 / 4) : ℂ) * ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 48 - ((3 / 2) : ℂ) * ζ ^ 50 + ((3 / 2) : ℂ) * ζ ^ 54 - ((3 / 2) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_2_0 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        2 0 =
      alternatingSixAmbientRow10TransformedGeneratorA
        2 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 8 + ((11 / 8) : ℂ) * ζ ^ 10 - ((11 / 8) : ℂ) * ζ ^ 14 + ((11 / 8) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 20 - ((3 / 4) : ℂ) * ζ ^ 24 + ((3 / 4) : ℂ) * ζ ^ 28 - ζ ^ 30 + ζ ^ 34 - ζ ^ 38 + ((9 / 8) : ℂ) * ζ ^ 40 - ((9 / 8) : ℂ) * ζ ^ 44 + ((9 / 8) : ℂ) * ζ ^ 48 + ((1 / 2) : ℂ) * ζ ^ 50 - ((1 / 2) : ℂ) * ζ ^ 54 + ((1 / 2) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_2_1 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        2 1 =
      alternatingSixAmbientRow10TransformedGeneratorA
        2 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((5 / 8) : ℂ) - ((5 / 8) : ℂ) * ζ ^ 4 + ((5 / 8) : ℂ) * ζ ^ 8 + ((5 / 4) : ℂ) * ζ ^ 10 - ((5 / 4) : ℂ) * ζ ^ 14 + ((5 / 4) : ℂ) * ζ ^ 18 - ((5 / 4) : ℂ) * ζ ^ 20 + ((5 / 4) : ℂ) * ζ ^ 24 - ((5 / 4) : ℂ) * ζ ^ 28 - ((7 / 8) : ℂ) * ζ ^ 30 + ((7 / 8) : ℂ) * ζ ^ 34 - ((7 / 8) : ℂ) * ζ ^ 38)
private theorem row10_transformedGeneratorA_2_2 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        2 2 =
      alternatingSixAmbientRow10TransformedGeneratorA
        2 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 - ((5 / 4) : ℂ) * ζ ^ 30 + ((5 / 4) : ℂ) * ζ ^ 34 - ((5 / 4) : ℂ) * ζ ^ 38 - ((1 / 4) : ℂ) * ζ ^ 40 + ((1 / 4) : ℂ) * ζ ^ 44 - ((1 / 4) : ℂ) * ζ ^ 48 - ((1 / 4) : ℂ) * ζ ^ 50 + ((1 / 4) : ℂ) * ζ ^ 54 - ((1 / 4) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_2_3 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        2 3 =
      alternatingSixAmbientRow10TransformedGeneratorA
        2 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((3 / 16) : ℂ) - ((3 / 16) : ℂ) * ζ ^ 4 + ((3 / 16) : ℂ) * ζ ^ 8 + ((1 / 8) : ℂ) * ζ ^ 20 - ((1 / 8) : ℂ) * ζ ^ 24 + ((1 / 8) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30 - ((1 / 2) : ℂ) * ζ ^ 34 + ((1 / 2) : ℂ) * ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 48 + ((1 / 16) : ℂ) * ζ ^ 50 - ((1 / 16) : ℂ) * ζ ^ 54 + ((1 / 16) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_2_4 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        2 4 =
      alternatingSixAmbientRow10TransformedGeneratorA
        2 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((7 / 16) : ℂ) - ((7 / 16) : ℂ) * ζ ^ 4 + ((7 / 16) : ℂ) * ζ ^ 8 + ((15 / 16) : ℂ) * ζ ^ 10 - ((15 / 16) : ℂ) * ζ ^ 14 + ((15 / 16) : ℂ) * ζ ^ 18 + ((13 / 16) : ℂ) * ζ ^ 20 - ((13 / 16) : ℂ) * ζ ^ 24 + ((13 / 16) : ℂ) * ζ ^ 28 + ((5 / 16) : ℂ) * ζ ^ 30 - ((5 / 16) : ℂ) * ζ ^ 34 + ((5 / 16) : ℂ) * ζ ^ 38 + ((3 / 16) : ℂ) * ζ ^ 40 - ((3 / 16) : ℂ) * ζ ^ 44 + ((3 / 16) : ℂ) * ζ ^ 48 + ((3 / 16) : ℂ) * ζ ^ 50 - ((3 / 16) : ℂ) * ζ ^ 54 + ((3 / 16) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_2_5 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        2 5 =
      alternatingSixAmbientRow10TransformedGeneratorA
        2 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((3 / 8) : ℂ) - ((3 / 8) : ℂ) * ζ ^ 4 + ((3 / 8) : ℂ) * ζ ^ 8 + ((5 / 8) : ℂ) * ζ ^ 10 - ((5 / 8) : ℂ) * ζ ^ 14 + ((5 / 8) : ℂ) * ζ ^ 18 + ((1 / 8) : ℂ) * ζ ^ 20 - ((1 / 8) : ℂ) * ζ ^ 24 + ((1 / 8) : ℂ) * ζ ^ 28 - ((5 / 8) : ℂ) * ζ ^ 30 + ((5 / 8) : ℂ) * ζ ^ 34 - ((5 / 8) : ℂ) * ζ ^ 38 - ((1 / 8) : ℂ) * ζ ^ 40 + ((1 / 8) : ℂ) * ζ ^ 44 - ((1 / 8) : ℂ) * ζ ^ 48 + ((5 / 8) : ℂ) * ζ ^ 50 - ((5 / 8) : ℂ) * ζ ^ 54 + ((5 / 8) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_3_0 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        3 0 =
      alternatingSixAmbientRow10TransformedGeneratorA
        3 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((5 / 2) : ℂ) + ((5 / 2) : ℂ) * ζ ^ 4 - ((5 / 2) : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 10 + (2 : ℂ) * ζ ^ 14 - (2 : ℂ) * ζ ^ 18 + ((17 / 2) : ℂ) * ζ ^ 20 - ((17 / 2) : ℂ) * ζ ^ 24 + ((17 / 2) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30 + ((1 / 2) : ℂ) * ζ ^ 34 - ((1 / 2) : ℂ) * ζ ^ 38 - (7 : ℂ) * ζ ^ 40 + (7 : ℂ) * ζ ^ 44 - (7 : ℂ) * ζ ^ 48)
private theorem row10_transformedGeneratorA_3_1 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        3 1 =
      alternatingSixAmbientRow10TransformedGeneratorA
        3 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((5 / 2) : ℂ) + ((5 / 2) : ℂ) * ζ ^ 4 - ((5 / 2) : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 + ζ ^ 20 - ζ ^ 24 + ζ ^ 28 - ((3 / 2) : ℂ) * ζ ^ 30 + ((3 / 2) : ℂ) * ζ ^ 34 - ((3 / 2) : ℂ) * ζ ^ 38 + ((3 / 2) : ℂ) * ζ ^ 40 - ((3 / 2) : ℂ) * ζ ^ 44 + ((3 / 2) : ℂ) * ζ ^ 48 + ζ ^ 50 - ζ ^ 54 + ζ ^ 58)
private theorem row10_transformedGeneratorA_3_2 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        3 2 =
      alternatingSixAmbientRow10TransformedGeneratorA
        3 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((3 / 2) : ℂ) + ((3 / 2) : ℂ) * ζ ^ 4 - ((3 / 2) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 10 + ((5 / 2) : ℂ) * ζ ^ 14 - ((5 / 2) : ℂ) * ζ ^ 18 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28 + ((3 / 2) : ℂ) * ζ ^ 40 - ((3 / 2) : ℂ) * ζ ^ 44 + ((3 / 2) : ℂ) * ζ ^ 48 + ζ ^ 50 - ζ ^ 54 + ζ ^ 58)
private theorem row10_transformedGeneratorA_3_3 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        3 3 =
      alternatingSixAmbientRow10TransformedGeneratorA
        3 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 + ((3 / 8) : ℂ) * ζ ^ 10 - ((3 / 8) : ℂ) * ζ ^ 14 + ((3 / 8) : ℂ) * ζ ^ 18 + ζ ^ 20 - ζ ^ 24 + ζ ^ 28 - ((15 / 8) : ℂ) * ζ ^ 30 + ((15 / 8) : ℂ) * ζ ^ 34 - ((15 / 8) : ℂ) * ζ ^ 38 - ((9 / 4) : ℂ) * ζ ^ 40 + ((9 / 4) : ℂ) * ζ ^ 44 - ((9 / 4) : ℂ) * ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_3_4 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        3 4 =
      alternatingSixAmbientRow10TransformedGeneratorA
        3 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-(2 : ℂ) + (2 : ℂ) * ζ ^ 4 - (2 : ℂ) * ζ ^ 8 - (4 : ℂ) * ζ ^ 10 + (4 : ℂ) * ζ ^ 14 - (4 : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 30 - ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 38 - ((9 / 4) : ℂ) * ζ ^ 40 + ((9 / 4) : ℂ) * ζ ^ 44 - ((9 / 4) : ℂ) * ζ ^ 48 - ((3 / 2) : ℂ) * ζ ^ 50 + ((3 / 2) : ℂ) * ζ ^ 54 - ((3 / 2) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_3_5 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        3 5 =
      alternatingSixAmbientRow10TransformedGeneratorA
        3 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 10 + ((5 / 2) : ℂ) * ζ ^ 14 - ((5 / 2) : ℂ) * ζ ^ 18 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28 + ((5 / 2) : ℂ) * ζ ^ 30 - ((5 / 2) : ℂ) * ζ ^ 34 + ((5 / 2) : ℂ) * ζ ^ 38 - ζ ^ 40 + ζ ^ 44 - ζ ^ 48 - (2 : ℂ) * ζ ^ 50 + (2 : ℂ) * ζ ^ 54 - (2 : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_4_0 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        4 0 =
      alternatingSixAmbientRow10TransformedGeneratorA
        4 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((9 / 4) : ℂ) - ((9 / 4) : ℂ) * ζ ^ 4 + ((9 / 4) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 - ((7 / 2) : ℂ) * ζ ^ 20 + ((7 / 2) : ℂ) * ζ ^ 24 - ((7 / 2) : ℂ) * ζ ^ 28 + ((3 / 2) : ℂ) * ζ ^ 30 - ((3 / 2) : ℂ) * ζ ^ 34 + ((3 / 2) : ℂ) * ζ ^ 38 - ((1 / 4) : ℂ) * ζ ^ 40 + ((1 / 4) : ℂ) * ζ ^ 44 - ((1 / 4) : ℂ) * ζ ^ 48 - ζ ^ 50 + ζ ^ 54 - ζ ^ 58)
private theorem row10_transformedGeneratorA_4_1 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        4 1 =
      alternatingSixAmbientRow10TransformedGeneratorA
        4 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 24 + ((3 / 2) : ℂ) * ζ ^ 28 + ((3 / 4) : ℂ) * ζ ^ 30 - ((3 / 4) : ℂ) * ζ ^ 34 + ((3 / 4) : ℂ) * ζ ^ 38 - ζ ^ 40 + ζ ^ 44 - ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_4_2 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        4 2 =
      alternatingSixAmbientRow10TransformedGeneratorA
        4 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 + ζ ^ 20 - ζ ^ 24 + ζ ^ 28 + ζ ^ 30 - ζ ^ 34 + ζ ^ 38 + ((1 / 4) : ℂ) * ζ ^ 40 - ((1 / 4) : ℂ) * ζ ^ 44 + ((1 / 4) : ℂ) * ζ ^ 48)
private theorem row10_transformedGeneratorA_4_3 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        4 3 =
      alternatingSixAmbientRow10TransformedGeneratorA
        4 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((11 / 16) : ℂ) - ((11 / 16) : ℂ) * ζ ^ 4 + ((11 / 16) : ℂ) * ζ ^ 8 - ((11 / 16) : ℂ) * ζ ^ 10 + ((11 / 16) : ℂ) * ζ ^ 14 - ((11 / 16) : ℂ) * ζ ^ 18 - ((5 / 16) : ℂ) * ζ ^ 20 + ((5 / 16) : ℂ) * ζ ^ 24 - ((5 / 16) : ℂ) * ζ ^ 28 + ((5 / 8) : ℂ) * ζ ^ 30 - ((5 / 8) : ℂ) * ζ ^ 34 + ((5 / 8) : ℂ) * ζ ^ 38 + ((5 / 16) : ℂ) * ζ ^ 40 - ((5 / 16) : ℂ) * ζ ^ 44 + ((5 / 16) : ℂ) * ζ ^ 48 + ((1 / 8) : ℂ) * ζ ^ 50 - ((1 / 8) : ℂ) * ζ ^ 54 + ((1 / 8) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_4_4 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        4 4 =
      alternatingSixAmbientRow10TransformedGeneratorA
        4 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((3 / 2) : ℂ) - ((3 / 2) : ℂ) * ζ ^ 4 + ((3 / 2) : ℂ) * ζ ^ 8 + ((9 / 8) : ℂ) * ζ ^ 10 - ((9 / 8) : ℂ) * ζ ^ 14 + ((9 / 8) : ℂ) * ζ ^ 18 + ((1 / 8) : ℂ) * ζ ^ 20 - ((1 / 8) : ℂ) * ζ ^ 24 + ((1 / 8) : ℂ) * ζ ^ 28 + ζ ^ 30 - ζ ^ 34 + ζ ^ 38 + ((5 / 4) : ℂ) * ζ ^ 40 - ((5 / 4) : ℂ) * ζ ^ 44 + ((5 / 4) : ℂ) * ζ ^ 48 + ((3 / 8) : ℂ) * ζ ^ 50 - ((3 / 8) : ℂ) * ζ ^ 54 + ((3 / 8) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_4_5 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        4 5 =
      alternatingSixAmbientRow10TransformedGeneratorA
        4 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 + ((7 / 4) : ℂ) * ζ ^ 10 - ((7 / 4) : ℂ) * ζ ^ 14 + ((7 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28 - ζ ^ 30 + ζ ^ 34 - ζ ^ 38 + ((3 / 4) : ℂ) * ζ ^ 40 - ((3 / 4) : ℂ) * ζ ^ 44 + ((3 / 4) : ℂ) * ζ ^ 48 - ((1 / 4) : ℂ) * ζ ^ 50 + ((1 / 4) : ℂ) * ζ ^ 54 - ((1 / 4) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_5_0 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        5 0 =
      alternatingSixAmbientRow10TransformedGeneratorA
        5 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((7 / 4) : ℂ) - ((7 / 4) : ℂ) * ζ ^ 4 + ((7 / 4) : ℂ) * ζ ^ 8 + ((21 / 8) : ℂ) * ζ ^ 10 - ((21 / 8) : ℂ) * ζ ^ 14 + ((21 / 8) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 30 + (2 : ℂ) * ζ ^ 34 - (2 : ℂ) * ζ ^ 38 + ((13 / 8) : ℂ) * ζ ^ 40 - ((13 / 8) : ℂ) * ζ ^ 44 + ((13 / 8) : ℂ) * ζ ^ 48 + ((5 / 2) : ℂ) * ζ ^ 50 - ((5 / 2) : ℂ) * ζ ^ 54 + ((5 / 2) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_5_1 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        5 1 =
      alternatingSixAmbientRow10TransformedGeneratorA
        5 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((11 / 8) : ℂ) - ((11 / 8) : ℂ) * ζ ^ 4 + ((11 / 8) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18 - ((13 / 4) : ℂ) * ζ ^ 20 + ((13 / 4) : ℂ) * ζ ^ 24 - ((13 / 4) : ℂ) * ζ ^ 28 - ((15 / 8) : ℂ) * ζ ^ 30 + ((15 / 8) : ℂ) * ζ ^ 34 - ((15 / 8) : ℂ) * ζ ^ 38 + ((3 / 2) : ℂ) * ζ ^ 40 - ((3 / 2) : ℂ) * ζ ^ 44 + ((3 / 2) : ℂ) * ζ ^ 48 + ζ ^ 50 - ζ ^ 54 + ζ ^ 58)
private theorem row10_transformedGeneratorA_5_2 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        5 2 =
      alternatingSixAmbientRow10TransformedGeneratorA
        5 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28 - ((7 / 4) : ℂ) * ζ ^ 30 + ((7 / 4) : ℂ) * ζ ^ 34 - ((7 / 4) : ℂ) * ζ ^ 38 - ((5 / 4) : ℂ) * ζ ^ 40 + ((5 / 4) : ℂ) * ζ ^ 44 - ((5 / 4) : ℂ) * ζ ^ 48 - ((1 / 4) : ℂ) * ζ ^ 50 + ((1 / 4) : ℂ) * ζ ^ 54 - ((1 / 4) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_5_3 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        5 3 =
      alternatingSixAmbientRow10TransformedGeneratorA
        5 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((23 / 16) : ℂ) - ((23 / 16) : ℂ) * ζ ^ 4 + ((23 / 16) : ℂ) * ζ ^ 8 + ((3 / 2) : ℂ) * ζ ^ 10 - ((3 / 2) : ℂ) * ζ ^ 14 + ((3 / 2) : ℂ) * ζ ^ 18 - ((3 / 8) : ℂ) * ζ ^ 20 + ((3 / 8) : ℂ) * ζ ^ 24 - ((3 / 8) : ℂ) * ζ ^ 28 - ((3 / 4) : ℂ) * ζ ^ 30 + ((3 / 4) : ℂ) * ζ ^ 34 - ((3 / 4) : ℂ) * ζ ^ 38 - ((3 / 16) : ℂ) * ζ ^ 50 + ((3 / 16) : ℂ) * ζ ^ 54 - ((3 / 16) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_5_4 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        5 4 =
      alternatingSixAmbientRow10TransformedGeneratorA
        5 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (((17 / 16) : ℂ) - ((17 / 16) : ℂ) * ζ ^ 4 + ((17 / 16) : ℂ) * ζ ^ 8 + ((33 / 16) : ℂ) * ζ ^ 10 - ((33 / 16) : ℂ) * ζ ^ 14 + ((33 / 16) : ℂ) * ζ ^ 18 - ((1 / 16) : ℂ) * ζ ^ 20 + ((1 / 16) : ℂ) * ζ ^ 24 - ((1 / 16) : ℂ) * ζ ^ 28 - ((39 / 16) : ℂ) * ζ ^ 30 + ((39 / 16) : ℂ) * ζ ^ 34 - ((39 / 16) : ℂ) * ζ ^ 38 - ((29 / 16) : ℂ) * ζ ^ 40 + ((29 / 16) : ℂ) * ζ ^ 44 - ((29 / 16) : ℂ) * ζ ^ 48 - ((9 / 16) : ℂ) * ζ ^ 50 + ((9 / 16) : ℂ) * ζ ^ 54 - ((9 / 16) : ℂ) * ζ ^ 58)
private theorem row10_transformedGeneratorA_5_5 :
    (alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis)
        5 5 =
      alternatingSixAmbientRow10TransformedGeneratorA
        5 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow10Eigenbasis,
      alternatingSixAmbientRow10EigenbasisInverse,
      alternatingSixFiveAmbient_row10_matrixA,
      alternatingSixAmbientRow10TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row10 (-((7 / 8) : ℂ) + ((7 / 8) : ℂ) * ζ ^ 4 - ((7 / 8) : ℂ) * ζ ^ 8 + ((3 / 8) : ℂ) * ζ ^ 10 - ((3 / 8) : ℂ) * ζ ^ 14 + ((3 / 8) : ℂ) * ζ ^ 18 + ((7 / 8) : ℂ) * ζ ^ 20 - ((7 / 8) : ℂ) * ζ ^ 24 + ((7 / 8) : ℂ) * ζ ^ 28 + ((3 / 8) : ℂ) * ζ ^ 30 - ((3 / 8) : ℂ) * ζ ^ 34 + ((3 / 8) : ℂ) * ζ ^ 38 - ((9 / 8) : ℂ) * ζ ^ 40 + ((9 / 8) : ℂ) * ζ ^ 44 - ((9 / 8) : ℂ) * ζ ^ 48 + ((9 / 8) : ℂ) * ζ ^ 50 - ((9 / 8) : ℂ) * ζ ^ 54 + ((9 / 8) : ℂ) * ζ ^ 58)
/-- Exact conjugation formula for the row 10 first
generator. -/
theorem alternatingSixAmbientRow10TransformedGeneratorA_eq :
    alternatingSixAmbientRow10EigenbasisInverse *
        alternatingSixFiveAmbient_row10_matrixA *
        alternatingSixAmbientRow10Eigenbasis =
      alternatingSixAmbientRow10TransformedGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row10_transformedGeneratorA_0_0
  · exact row10_transformedGeneratorA_0_1
  · exact row10_transformedGeneratorA_0_2
  · exact row10_transformedGeneratorA_0_3
  · exact row10_transformedGeneratorA_0_4
  · exact row10_transformedGeneratorA_0_5
  · exact row10_transformedGeneratorA_1_0
  · exact row10_transformedGeneratorA_1_1
  · exact row10_transformedGeneratorA_1_2
  · exact row10_transformedGeneratorA_1_3
  · exact row10_transformedGeneratorA_1_4
  · exact row10_transformedGeneratorA_1_5
  · exact row10_transformedGeneratorA_2_0
  · exact row10_transformedGeneratorA_2_1
  · exact row10_transformedGeneratorA_2_2
  · exact row10_transformedGeneratorA_2_3
  · exact row10_transformedGeneratorA_2_4
  · exact row10_transformedGeneratorA_2_5
  · exact row10_transformedGeneratorA_3_0
  · exact row10_transformedGeneratorA_3_1
  · exact row10_transformedGeneratorA_3_2
  · exact row10_transformedGeneratorA_3_3
  · exact row10_transformedGeneratorA_3_4
  · exact row10_transformedGeneratorA_3_5
  · exact row10_transformedGeneratorA_4_0
  · exact row10_transformedGeneratorA_4_1
  · exact row10_transformedGeneratorA_4_2
  · exact row10_transformedGeneratorA_4_3
  · exact row10_transformedGeneratorA_4_4
  · exact row10_transformedGeneratorA_4_5
  · exact row10_transformedGeneratorA_5_0
  · exact row10_transformedGeneratorA_5_1
  · exact row10_transformedGeneratorA_5_2
  · exact row10_transformedGeneratorA_5_3
  · exact row10_transformedGeneratorA_5_4
  · exact row10_transformedGeneratorA_5_5


end InductiveMcKay
end McKayConjecture
