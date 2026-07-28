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
# Checked diagonal data for ambient row 09

This generated module records an exact eigenbasis for the second generator
and the first generator in that basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenvalue block labels for row 09. -/
def alternatingSixAmbientRow09EigenvalueLabel :
    Fin 5 → Fin 4 :=
  ![0, 1, 2, 2, 3]

/-- Second-generator eigenvalues, including their multiplicities. -/
def alternatingSixAmbientRow09GeneratorBEigenvalue :
    Fin 5 → ℂ :=
  fun i ↦
    alternatingSixOrderFourEigenvalue
      (alternatingSixAmbientRow09EigenvalueLabel i)

/-- Diagonal form of the row 09 second generator. -/
def alternatingSixAmbientRow09GeneratorBDiagonal :
    Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal
    alternatingSixAmbientRow09GeneratorBEigenvalue

/-- Checked eigenbasis for the row 09 second generator. -/
def alternatingSixAmbientRow09Eigenbasis :
    Matrix (Fin 5) (Fin 5) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [(-1, 0), (1, 20)],
      alternatingSixCyclotomicValue [(1, 10)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0), (-1, 20)],
      alternatingSixCyclotomicValue [(-1, 10)]],
    ![alternatingSixCyclotomicValue [(-1, 20)],
      alternatingSixCyclotomicValue [(-1, 20)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(-1, 20)]],
    ![alternatingSixCyclotomicValue [(1, 20)],
      alternatingSixCyclotomicValue [((-1 / 3), 10), ((-1 / 3), 30)],
      alternatingSixCyclotomicValue [(1, 20)],
      alternatingSixCyclotomicValue [(-1, 0), (1, 20)],
      alternatingSixCyclotomicValue [((1 / 3), 10), ((1 / 3), 30)]],
    ![alternatingSixCyclotomicValue [(-1, 0), (1, 20)],
      alternatingSixCyclotomicValue [((1 / 3), 0), ((1 / 3), 10), ((-2 / 3), 20), ((1 / 3), 30)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [((1 / 3), 0), ((-1 / 3), 10), ((-2 / 3), 20), ((-1 / 3), 30)]],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)]]
  ]

/-- Checked inverse of the row 09 eigenbasis. -/
def alternatingSixAmbientRow09EigenbasisInverse :
    Matrix (Fin 5) (Fin 5) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((1 / 2), 0)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 4), 20)],
      alternatingSixCyclotomicValue [((3 / 4), 0), ((-3 / 4), 20)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 20)],
      alternatingSixCyclotomicValue [((-1 / 2), 20)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 4), 10), ((-1 / 4), 20), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 10), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 10), ((1 / 4), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 10), ((1 / 4), 20), ((1 / 2), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 0), (-1, 20)],
      alternatingSixCyclotomicValue [((1 / 4), 0)],
      alternatingSixCyclotomicValue [((-3 / 4), 20)],
      alternatingSixCyclotomicValue [((3 / 4), 20)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 20)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 20)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 20)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 2), 0)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 10), ((-1 / 4), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 10), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 10), ((1 / 4), 20), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 10), ((1 / 4), 20), ((-1 / 2), 30)]]
  ]

/-- The row 09 first generator in the checked diagonal basis. -/
def alternatingSixAmbientRow09TransformedGeneratorA :
    Matrix (Fin 5) (Fin 5) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((1 / 4), 0)],
      alternatingSixCyclotomicValue [((-1 / 2), 10), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-3 / 4), 0), ((3 / 4), 20)],
      alternatingSixCyclotomicValue [((-3 / 4), 0), ((3 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 2), 10), ((-1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 10), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 2), 10), ((-1 / 4), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 2), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 0), ((-3 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((5 / 12), 10), ((-1 / 2), 20), ((-1 / 3), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 4), 20)],
      alternatingSixCyclotomicValue [(-1, 0), ((3 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-5 / 12), 10), ((-1 / 2), 20), ((1 / 3), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 0)],
      alternatingSixCyclotomicValue [((-1 / 6), 0), ((-1 / 2), 10), ((1 / 3), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 20)],
      alternatingSixCyclotomicValue [((3 / 4), 0), ((-1 / 4), 20)],
      alternatingSixCyclotomicValue [((-1 / 6), 0), ((1 / 2), 10), ((1 / 3), 20), ((-1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 10), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 2), 10), ((-1 / 4), 20), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0)]]
  ]

macro "close_cyclotomic_row09" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)


private theorem row09_eigenbasisInverse_mul_0_0 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        0 0 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        0 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((5 / 4) : ℂ) + ((5 / 4) : ℂ) * ζ ^ 4 - ((5 / 4) : ℂ) * ζ ^ 8)
private theorem row09_eigenbasisInverse_mul_0_1 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        0 1 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        0 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((1 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 4 - ((1 / 12) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 18)
private theorem row09_eigenbasisInverse_mul_0_2 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        0 2 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        0 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 8)
private theorem row09_eigenbasisInverse_mul_0_3 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        0 3 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        0 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 8)
private theorem row09_eigenbasisInverse_mul_0_4 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        0 4 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        0 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((1 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 4 - ((1 / 12) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 18)
private theorem row09_eigenbasisInverse_mul_1_0 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        1 0 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        1 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18)
private theorem row09_eigenbasisInverse_mul_1_1 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        1 1 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        1 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((2 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 4 - ((2 / 3) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 20 + ((1 / 12) : ℂ) * ζ ^ 24 - ((1 / 12) : ℂ) * ζ ^ 28)
private theorem row09_eigenbasisInverse_mul_1_2 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        1 2 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        1 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18)
private theorem row09_eigenbasisInverse_mul_1_3 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        1 3 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        1 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 14 + ((3 / 4) : ℂ) * ζ ^ 18)
private theorem row09_eigenbasisInverse_mul_1_4 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        1 4 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        1 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 28)
private theorem row09_eigenbasisInverse_mul_2_0 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        2 0 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        2 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)
private theorem row09_eigenbasisInverse_mul_2_1 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        2 1 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        2 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18)
private theorem row09_eigenbasisInverse_mul_2_2 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        2 2 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        2 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 8)
private theorem row09_eigenbasisInverse_mul_2_3 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        2 3 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        2 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8)
private theorem row09_eigenbasisInverse_mul_2_4 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        2 4 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        2 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18)
private theorem row09_eigenbasisInverse_mul_3_0 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        3 0 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        3 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((3 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 4 + ((3 / 4) : ℂ) * ζ ^ 8)
private theorem row09_eigenbasisInverse_mul_3_1 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        3 1 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        3 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((5 / 12) : ℂ) - ((5 / 12) : ℂ) * ζ ^ 4 + ((5 / 12) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 18)
private theorem row09_eigenbasisInverse_mul_3_2 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        3 2 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        3 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8)
private theorem row09_eigenbasisInverse_mul_3_3 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        3 3 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        3 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8)
private theorem row09_eigenbasisInverse_mul_3_4 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        3 4 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        3 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((5 / 12) : ℂ) - ((5 / 12) : ℂ) * ζ ^ 4 + ((5 / 12) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 18)
private theorem row09_eigenbasisInverse_mul_4_0 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        4 0 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        4 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18)
private theorem row09_eigenbasisInverse_mul_4_1 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        4 1 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        4 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 28)
private theorem row09_eigenbasisInverse_mul_4_2 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        4 2 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        4 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18)
private theorem row09_eigenbasisInverse_mul_4_3 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        4 3 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        4 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 10 + ((3 / 4) : ℂ) * ζ ^ 14 - ((3 / 4) : ℂ) * ζ ^ 18)
private theorem row09_eigenbasisInverse_mul_4_4 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis)
        4 4 =
      (1 : Matrix (Fin 5) (Fin 5) ℂ)
        4 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((2 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 4 - ((2 / 3) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 20 + ((1 / 12) : ℂ) * ζ ^ 24 - ((1 / 12) : ℂ) * ζ ^ 28)
/-- The displayed row 09 matrix is a left inverse of its
eigenbasis. -/
theorem alternatingSixAmbientRow09EigenbasisInverse_mul :
    alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixAmbientRow09Eigenbasis =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row09_eigenbasisInverse_mul_0_0
  · exact row09_eigenbasisInverse_mul_0_1
  · exact row09_eigenbasisInverse_mul_0_2
  · exact row09_eigenbasisInverse_mul_0_3
  · exact row09_eigenbasisInverse_mul_0_4
  · exact row09_eigenbasisInverse_mul_1_0
  · exact row09_eigenbasisInverse_mul_1_1
  · exact row09_eigenbasisInverse_mul_1_2
  · exact row09_eigenbasisInverse_mul_1_3
  · exact row09_eigenbasisInverse_mul_1_4
  · exact row09_eigenbasisInverse_mul_2_0
  · exact row09_eigenbasisInverse_mul_2_1
  · exact row09_eigenbasisInverse_mul_2_2
  · exact row09_eigenbasisInverse_mul_2_3
  · exact row09_eigenbasisInverse_mul_2_4
  · exact row09_eigenbasisInverse_mul_3_0
  · exact row09_eigenbasisInverse_mul_3_1
  · exact row09_eigenbasisInverse_mul_3_2
  · exact row09_eigenbasisInverse_mul_3_3
  · exact row09_eigenbasisInverse_mul_3_4
  · exact row09_eigenbasisInverse_mul_4_0
  · exact row09_eigenbasisInverse_mul_4_1
  · exact row09_eigenbasisInverse_mul_4_2
  · exact row09_eigenbasisInverse_mul_4_3
  · exact row09_eigenbasisInverse_mul_4_4

/-- The displayed row 09 inverse is also a right inverse. -/
theorem alternatingSixAmbientRow09Eigenbasis_mul_inverse :
    alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow09EigenbasisInverse_mul


private theorem row09_generatorB_mul_eigenbasis_0_0 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        0 0 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        0 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 0
private theorem row09_generatorB_mul_eigenbasis_0_1 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        0 1 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        0 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)
private theorem row09_generatorB_mul_eigenbasis_0_2 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        0 2 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        0 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 0
private theorem row09_generatorB_mul_eigenbasis_0_3 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        0 3 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        0 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 + ζ ^ 40 - ζ ^ 44 + ζ ^ 48)
private theorem row09_generatorB_mul_eigenbasis_0_4 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        0 4 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        0 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 + ζ ^ 40 - ζ ^ 44 + ζ ^ 48 + ζ ^ 60 - ζ ^ 64 + ζ ^ 68)
private theorem row09_generatorB_mul_eigenbasis_1_0 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        1 0 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        1 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)
private theorem row09_generatorB_mul_eigenbasis_1_1 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        1 1 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        1 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 18)
private theorem row09_generatorB_mul_eigenbasis_1_2 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        1 2 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        1 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-ζ ^ 20 + ζ ^ 24 - ζ ^ 28)
private theorem row09_generatorB_mul_eigenbasis_1_3 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        1 3 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        1 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)
private theorem row09_generatorB_mul_eigenbasis_1_4 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        1 4 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        1 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 18 + ζ ^ 50 - ζ ^ 54 + ζ ^ 58 + ζ ^ 70 - ζ ^ 74 + ζ ^ 78)
private theorem row09_generatorB_mul_eigenbasis_2_0 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        2 0 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        2 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 ((2 : ℂ) - (2 : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 8)
private theorem row09_generatorB_mul_eigenbasis_2_1 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        2 1 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        2 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((7 / 3) : ℂ) - ((7 / 3) : ℂ) * ζ ^ 4 + ((7 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28)
private theorem row09_generatorB_mul_eigenbasis_2_2 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        2 2 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        2 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28 - ζ ^ 40 + ζ ^ 44 - ζ ^ 48)
private theorem row09_generatorB_mul_eigenbasis_2_3 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        2 3 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        2 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 - ζ ^ 40 + ζ ^ 44 - ζ ^ 48)
private theorem row09_generatorB_mul_eigenbasis_2_4 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        2 4 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        2 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((7 / 3) : ℂ) - ((7 / 3) : ℂ) * ζ ^ 4 + ((7 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 40 + ((1 / 3) : ℂ) * ζ ^ 44 - ((1 / 3) : ℂ) * ζ ^ 48 - ((2 / 3) : ℂ) * ζ ^ 60 + ((2 / 3) : ℂ) * ζ ^ 64 - ((2 / 3) : ℂ) * ζ ^ 68 - ((1 / 3) : ℂ) * ζ ^ 80 + ((1 / 3) : ℂ) * ζ ^ 84 - ((1 / 3) : ℂ) * ζ ^ 88)
private theorem row09_generatorB_mul_eigenbasis_3_0 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        3 0 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        3 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8)
private theorem row09_generatorB_mul_eigenbasis_3_1 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        3 1 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        3 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28)
private theorem row09_generatorB_mul_eigenbasis_3_2 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        3 2 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        3 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-ζ ^ 20 + ζ ^ 24 - ζ ^ 28)
private theorem row09_generatorB_mul_eigenbasis_3_3 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        3 3 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        3 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 0
private theorem row09_generatorB_mul_eigenbasis_3_4 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        3 4 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        3 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 30 + ((1 / 3) : ℂ) * ζ ^ 34 - ((1 / 3) : ℂ) * ζ ^ 38 + ((1 / 3) : ℂ) * ζ ^ 40 - ((1 / 3) : ℂ) * ζ ^ 44 + ((1 / 3) : ℂ) * ζ ^ 48 + ((1 / 3) : ℂ) * ζ ^ 50 - ((1 / 3) : ℂ) * ζ ^ 54 + ((1 / 3) : ℂ) * ζ ^ 58 + ((2 / 3) : ℂ) * ζ ^ 60 - ((2 / 3) : ℂ) * ζ ^ 64 + ((2 / 3) : ℂ) * ζ ^ 68 + ((2 / 3) : ℂ) * ζ ^ 70 - ((2 / 3) : ℂ) * ζ ^ 74 + ((2 / 3) : ℂ) * ζ ^ 78 + ((1 / 3) : ℂ) * ζ ^ 80 - ((1 / 3) : ℂ) * ζ ^ 84 + ((1 / 3) : ℂ) * ζ ^ 88)
private theorem row09_generatorB_mul_eigenbasis_4_0 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        4 0 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        4 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-(3 : ℂ) + (3 : ℂ) * ζ ^ 4 - (3 : ℂ) * ζ ^ 8)
private theorem row09_generatorB_mul_eigenbasis_4_1 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        4 1 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        4 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 18)
private theorem row09_generatorB_mul_eigenbasis_4_2 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        4 2 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        4 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-(2 : ℂ) + (2 : ℂ) * ζ ^ 4 - (2 : ℂ) * ζ ^ 8)
private theorem row09_generatorB_mul_eigenbasis_4_3 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        4 3 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        4 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-(3 : ℂ) + (3 : ℂ) * ζ ^ 4 - (3 : ℂ) * ζ ^ 8 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)
private theorem row09_generatorB_mul_eigenbasis_4_4 :
    (alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis)
        4 4 =
      (alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal)
        4 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09GeneratorBDiagonal,
      alternatingSixAmbientRow09GeneratorBEigenvalue,
      alternatingSixAmbientRow09EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 18 - ζ ^ 30 + ζ ^ 34 - ζ ^ 38 - ζ ^ 50 + ζ ^ 54 - ζ ^ 58)
/-- The checked row 09 basis diagonalizes the second
generator. -/
theorem alternatingSixAmbientRow09GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row09_matrixB *
        alternatingSixAmbientRow09Eigenbasis =
      alternatingSixAmbientRow09Eigenbasis *
        alternatingSixAmbientRow09GeneratorBDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row09_generatorB_mul_eigenbasis_0_0
  · exact row09_generatorB_mul_eigenbasis_0_1
  · exact row09_generatorB_mul_eigenbasis_0_2
  · exact row09_generatorB_mul_eigenbasis_0_3
  · exact row09_generatorB_mul_eigenbasis_0_4
  · exact row09_generatorB_mul_eigenbasis_1_0
  · exact row09_generatorB_mul_eigenbasis_1_1
  · exact row09_generatorB_mul_eigenbasis_1_2
  · exact row09_generatorB_mul_eigenbasis_1_3
  · exact row09_generatorB_mul_eigenbasis_1_4
  · exact row09_generatorB_mul_eigenbasis_2_0
  · exact row09_generatorB_mul_eigenbasis_2_1
  · exact row09_generatorB_mul_eigenbasis_2_2
  · exact row09_generatorB_mul_eigenbasis_2_3
  · exact row09_generatorB_mul_eigenbasis_2_4
  · exact row09_generatorB_mul_eigenbasis_3_0
  · exact row09_generatorB_mul_eigenbasis_3_1
  · exact row09_generatorB_mul_eigenbasis_3_2
  · exact row09_generatorB_mul_eigenbasis_3_3
  · exact row09_generatorB_mul_eigenbasis_3_4
  · exact row09_generatorB_mul_eigenbasis_4_0
  · exact row09_generatorB_mul_eigenbasis_4_1
  · exact row09_generatorB_mul_eigenbasis_4_2
  · exact row09_generatorB_mul_eigenbasis_4_3
  · exact row09_generatorB_mul_eigenbasis_4_4


private theorem row09_transformedGeneratorA_0_0 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        0 0 =
      alternatingSixAmbientRow09TransformedGeneratorA
        0 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row09_transformedGeneratorA_0_1 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        0 1 =
      alternatingSixAmbientRow09TransformedGeneratorA
        0 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((7 / 12) : ℂ) * ζ ^ 10 - ((7 / 12) : ℂ) * ζ ^ 14 + ((7 / 12) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 28 + ((5 / 12) : ℂ) * ζ ^ 30 - ((5 / 12) : ℂ) * ζ ^ 34 + ((5 / 12) : ℂ) * ζ ^ 38)
private theorem row09_transformedGeneratorA_0_2 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        0 2 =
      alternatingSixAmbientRow09TransformedGeneratorA
        0 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-ζ ^ 20 + ζ ^ 24 - ζ ^ 28)
private theorem row09_transformedGeneratorA_0_3 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        0 3 =
      alternatingSixAmbientRow09TransformedGeneratorA
        0 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 - ((5 / 4) : ℂ) * ζ ^ 20 + ((5 / 4) : ℂ) * ζ ^ 24 - ((5 / 4) : ℂ) * ζ ^ 28)
private theorem row09_transformedGeneratorA_0_4 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        0 4 =
      alternatingSixAmbientRow09TransformedGeneratorA
        0 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((7 / 12) : ℂ) * ζ ^ 10 + ((7 / 12) : ℂ) * ζ ^ 14 - ((7 / 12) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 28 - ((5 / 12) : ℂ) * ζ ^ 30 + ((5 / 12) : ℂ) * ζ ^ 34 - ((5 / 12) : ℂ) * ζ ^ 38)
private theorem row09_transformedGeneratorA_1_0 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        1 0 =
      alternatingSixAmbientRow09TransformedGeneratorA
        1 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 30 - ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 38)
private theorem row09_transformedGeneratorA_1_1 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        1 1 =
      alternatingSixAmbientRow09TransformedGeneratorA
        1 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((1 / 6) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 30 + ((1 / 3) : ℂ) * ζ ^ 34 - ((1 / 3) : ℂ) * ζ ^ 38 - ((1 / 6) : ℂ) * ζ ^ 40 + ((1 / 6) : ℂ) * ζ ^ 44 - ((1 / 6) : ℂ) * ζ ^ 48)
private theorem row09_transformedGeneratorA_1_2 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        1 2 =
      alternatingSixAmbientRow09TransformedGeneratorA
        1 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 30 - ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 38)
private theorem row09_transformedGeneratorA_1_3 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        1 3 =
      alternatingSixAmbientRow09TransformedGeneratorA
        1 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 30 + ((1 / 4) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 38)
private theorem row09_transformedGeneratorA_1_4 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        1 4 =
      alternatingSixAmbientRow09TransformedGeneratorA
        1 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((1 / 6) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 18 - ((5 / 12) : ℂ) * ζ ^ 20 + ((5 / 12) : ℂ) * ζ ^ 24 - ((5 / 12) : ℂ) * ζ ^ 28 + ((1 / 6) : ℂ) * ζ ^ 30 - ((1 / 6) : ℂ) * ζ ^ 34 + ((1 / 6) : ℂ) * ζ ^ 38 + ((1 / 6) : ℂ) * ζ ^ 40 - ((1 / 6) : ℂ) * ζ ^ 44 + ((1 / 6) : ℂ) * ζ ^ 48)
private theorem row09_transformedGeneratorA_2_0 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        2 0 =
      alternatingSixAmbientRow09TransformedGeneratorA
        2 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((5 / 4) : ℂ) + ((5 / 4) : ℂ) * ζ ^ 4 - ((5 / 4) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 20 - ((3 / 4) : ℂ) * ζ ^ 24 + ((3 / 4) : ℂ) * ζ ^ 28)
private theorem row09_transformedGeneratorA_2_1 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        2 1 =
      alternatingSixAmbientRow09TransformedGeneratorA
        2 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 28 + ((1 / 12) : ℂ) * ζ ^ 30 - ((1 / 12) : ℂ) * ζ ^ 34 + ((1 / 12) : ℂ) * ζ ^ 38)
private theorem row09_transformedGeneratorA_2_2 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        2 2 =
      alternatingSixAmbientRow09TransformedGeneratorA
        2 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((3 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 4 + ((3 / 4) : ℂ) * ζ ^ 8)
private theorem row09_transformedGeneratorA_2_3 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        2 3 =
      alternatingSixAmbientRow09TransformedGeneratorA
        2 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row09_transformedGeneratorA_2_4 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        2 4 =
      alternatingSixAmbientRow09TransformedGeneratorA
        2 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 28 - ((1 / 12) : ℂ) * ζ ^ 30 + ((1 / 12) : ℂ) * ζ ^ 34 - ((1 / 12) : ℂ) * ζ ^ 38)
private theorem row09_transformedGeneratorA_3_0 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        3 0 =
      alternatingSixAmbientRow09TransformedGeneratorA
        3 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((5 / 4) : ℂ) - ((5 / 4) : ℂ) * ζ ^ 4 + ((5 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row09_transformedGeneratorA_3_1 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        3 1 =
      alternatingSixAmbientRow09TransformedGeneratorA
        3 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 8 - ((1 / 12) : ℂ) * ζ ^ 10 + ((1 / 12) : ℂ) * ζ ^ 14 - ((1 / 12) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 28 + ((1 / 12) : ℂ) * ζ ^ 30 - ((1 / 12) : ℂ) * ζ ^ 34 + ((1 / 12) : ℂ) * ζ ^ 38)
private theorem row09_transformedGeneratorA_3_2 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        3 2 =
      alternatingSixAmbientRow09TransformedGeneratorA
        3 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 0
private theorem row09_transformedGeneratorA_3_3 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        3 3 =
      alternatingSixAmbientRow09TransformedGeneratorA
        3 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row09_transformedGeneratorA_3_4 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        3 4 =
      alternatingSixAmbientRow09TransformedGeneratorA
        3 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 10 - ((1 / 12) : ℂ) * ζ ^ 14 + ((1 / 12) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 28 - ((1 / 12) : ℂ) * ζ ^ 30 + ((1 / 12) : ℂ) * ζ ^ 34 - ((1 / 12) : ℂ) * ζ ^ 38)
private theorem row09_transformedGeneratorA_4_0 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        4 0 =
      alternatingSixAmbientRow09TransformedGeneratorA
        4 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 30 + ((1 / 4) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 38)
private theorem row09_transformedGeneratorA_4_1 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        4 1 =
      alternatingSixAmbientRow09TransformedGeneratorA
        4 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((1 / 6) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 18 - ((5 / 12) : ℂ) * ζ ^ 20 + ((5 / 12) : ℂ) * ζ ^ 24 - ((5 / 12) : ℂ) * ζ ^ 28 - ((1 / 6) : ℂ) * ζ ^ 30 + ((1 / 6) : ℂ) * ζ ^ 34 - ((1 / 6) : ℂ) * ζ ^ 38 + ((1 / 6) : ℂ) * ζ ^ 40 - ((1 / 6) : ℂ) * ζ ^ 44 + ((1 / 6) : ℂ) * ζ ^ 48)
private theorem row09_transformedGeneratorA_4_2 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        4 2 =
      alternatingSixAmbientRow09TransformedGeneratorA
        4 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 30 + ((1 / 4) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 38)
private theorem row09_transformedGeneratorA_4_3 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        4 3 =
      alternatingSixAmbientRow09TransformedGeneratorA
        4 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 30 - ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 38)
private theorem row09_transformedGeneratorA_4_4 :
    (alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis)
        4 4 =
      alternatingSixAmbientRow09TransformedGeneratorA
        4 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow09Eigenbasis,
      alternatingSixAmbientRow09EigenbasisInverse,
      alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixAmbientRow09TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row09 (-((1 / 6) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 30 - ((1 / 3) : ℂ) * ζ ^ 34 + ((1 / 3) : ℂ) * ζ ^ 38 - ((1 / 6) : ℂ) * ζ ^ 40 + ((1 / 6) : ℂ) * ζ ^ 44 - ((1 / 6) : ℂ) * ζ ^ 48)
/-- Exact conjugation formula for the row 09 first
generator. -/
theorem alternatingSixAmbientRow09TransformedGeneratorA_eq :
    alternatingSixAmbientRow09EigenbasisInverse *
        alternatingSixFiveAmbient_row09_matrixA *
        alternatingSixAmbientRow09Eigenbasis =
      alternatingSixAmbientRow09TransformedGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row09_transformedGeneratorA_0_0
  · exact row09_transformedGeneratorA_0_1
  · exact row09_transformedGeneratorA_0_2
  · exact row09_transformedGeneratorA_0_3
  · exact row09_transformedGeneratorA_0_4
  · exact row09_transformedGeneratorA_1_0
  · exact row09_transformedGeneratorA_1_1
  · exact row09_transformedGeneratorA_1_2
  · exact row09_transformedGeneratorA_1_3
  · exact row09_transformedGeneratorA_1_4
  · exact row09_transformedGeneratorA_2_0
  · exact row09_transformedGeneratorA_2_1
  · exact row09_transformedGeneratorA_2_2
  · exact row09_transformedGeneratorA_2_3
  · exact row09_transformedGeneratorA_2_4
  · exact row09_transformedGeneratorA_3_0
  · exact row09_transformedGeneratorA_3_1
  · exact row09_transformedGeneratorA_3_2
  · exact row09_transformedGeneratorA_3_3
  · exact row09_transformedGeneratorA_3_4
  · exact row09_transformedGeneratorA_4_0
  · exact row09_transformedGeneratorA_4_1
  · exact row09_transformedGeneratorA_4_2
  · exact row09_transformedGeneratorA_4_3
  · exact row09_transformedGeneratorA_4_4


end InductiveMcKay
end McKayConjecture
