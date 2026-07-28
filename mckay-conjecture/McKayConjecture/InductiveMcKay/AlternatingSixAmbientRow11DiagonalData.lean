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
# Checked diagonal data for ambient row 11

This generated module records an exact eigenbasis for the second generator
and the first generator in that basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenvalue block labels for row 11. -/
def alternatingSixAmbientRow11EigenvalueLabel :
    Fin 6 → Fin 4 :=
  ![0, 0, 1, 2, 2, 3]

/-- Second-generator eigenvalues, including their multiplicities. -/
def alternatingSixAmbientRow11GeneratorBEigenvalue :
    Fin 6 → ℂ :=
  fun i ↦
    alternatingSixOrderFourEigenvalue
      (alternatingSixAmbientRow11EigenvalueLabel i)

/-- Diagonal form of the row 11 second generator. -/
def alternatingSixAmbientRow11GeneratorBDiagonal :
    Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal
    alternatingSixAmbientRow11GeneratorBEigenvalue

/-- Checked eigenbasis for the row 11 second generator. -/
def alternatingSixAmbientRow11Eigenbasis :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [(1, 0), (-2, 20), (-1, 30)],
      alternatingSixCyclotomicValue [(1, 0), (1, 10), (-1, 30)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(-1, 0), ((1 / 2), 10), ((1 / 2), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [(1, 0), (-1, 20)],
      alternatingSixCyclotomicValue [((1 / 2), 20)]],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 2), 10), ((-1 / 2), 20)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 10)],
      alternatingSixCyclotomicValue [(1, 20)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 4), 10), ((-1 / 4), 20), ((-1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 10), (-1, 30)],
      alternatingSixCyclotomicValue [(-1, 0), (-1, 10), (1, 20), (1, 30)],
      alternatingSixCyclotomicValue [(2, 10), (-2, 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 10), (-1, 30)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [((1 / 2), 30)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue []]
  ]

/-- Checked inverse of the row 11 eigenbasis. -/
def alternatingSixAmbientRow11EigenbasisInverse :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((-1 / 4), 10), ((1 / 4), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 2), 10)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 10), ((1 / 4), 20)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 10), ((1 / 4), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 2), 10), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 2), 20), ((-1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 6), 0), ((-1 / 6), 10), ((1 / 6), 20), ((-1 / 6), 30)],
      alternatingSixCyclotomicValue [((-1 / 6), 0), ((1 / 3), 10), ((1 / 3), 20), ((-1 / 6), 30)],
      alternatingSixCyclotomicValue [((1 / 3), 0), ((-1 / 2), 10), ((-1 / 6), 20)],
      alternatingSixCyclotomicValue [((-1 / 3), 0), ((-1 / 2), 10), ((1 / 6), 20)],
      alternatingSixCyclotomicValue [((-5 / 12), 0), ((1 / 12), 10), ((1 / 12), 20), ((1 / 3), 30)],
      alternatingSixCyclotomicValue [(1, 0), ((-1 / 6), 10), ((1 / 3), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 6), 0), ((1 / 2), 10), ((-1 / 6), 20)],
      alternatingSixCyclotomicValue [((-1 / 3), 10), ((2 / 3), 30)],
      alternatingSixCyclotomicValue [((-1 / 6), 0), ((1 / 3), 10), ((1 / 3), 20), ((-1 / 6), 30)],
      alternatingSixCyclotomicValue [((1 / 6), 0), ((2 / 3), 10), ((-1 / 3), 20), ((1 / 6), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 3), 10), ((-1 / 2), 20), ((-1 / 3), 30)],
      alternatingSixCyclotomicValue [((-1 / 3), 0), ((-1 / 6), 10), ((1 / 6), 20), ((-1 / 6), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 3), 10), ((-1 / 6), 30)],
      alternatingSixCyclotomicValue [((1 / 3), 0), ((-2 / 3), 20)],
      alternatingSixCyclotomicValue [((-1 / 3), 0), ((-1 / 6), 10), ((1 / 6), 20), ((-1 / 6), 30)],
      alternatingSixCyclotomicValue [((1 / 3), 0), ((1 / 6), 10), ((-1 / 6), 20), ((1 / 6), 30)],
      alternatingSixCyclotomicValue [((1 / 3), 0), ((1 / 3), 20)],
      alternatingSixCyclotomicValue [((1 / 6), 0), ((1 / 6), 10), ((1 / 6), 20), ((-1 / 3), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 3), 10), ((1 / 6), 30)],
      alternatingSixCyclotomicValue [((1 / 6), 0), ((-1 / 3), 20), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 6), 0), ((1 / 6), 10), ((-1 / 6), 20), ((1 / 6), 30)],
      alternatingSixCyclotomicValue [((1 / 6), 0), ((-1 / 6), 10), ((1 / 6), 20), ((-1 / 6), 30)],
      alternatingSixCyclotomicValue [((-1 / 12), 0), ((1 / 4), 10), ((5 / 12), 20)],
      alternatingSixCyclotomicValue [((1 / 3), 0), ((1 / 3), 10), ((-1 / 6), 20), ((-1 / 6), 30)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue []]
  ]

/-- The row 11 first generator in the checked diagonal basis. -/
def alternatingSixAmbientRow11TransformedGeneratorA :
    Matrix (Fin 6) (Fin 6) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((-1 / 4), 10), ((-1 / 4), 20), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [((1 / 2), 10), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((-5 / 8), 0), ((3 / 8), 10), ((1 / 8), 20)],
      alternatingSixCyclotomicValue [((3 / 4), 0), ((-1 / 4), 10), ((-3 / 4), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((1 / 8), 10), ((-1 / 4), 20), ((1 / 8), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 10), ((1 / 4), 20), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 10), ((-1 / 4), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 10), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 8), 0), ((1 / 4), 10), ((-1 / 2), 20), ((-1 / 8), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((-1 / 4), 10), ((1 / 4), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 8), 0), ((1 / 8), 10), ((-1 / 8), 20), ((1 / 8), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 10), ((-1 / 4), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 2), 10)],
      alternatingSixCyclotomicValue [((1 / 2), 10)],
      alternatingSixCyclotomicValue [((1 / 8), 0), ((1 / 8), 30)]],
    ![alternatingSixCyclotomicValue [(1, 0), ((1 / 2), 10), ((-1 / 2), 20), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 10), ((1 / 2), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((1 / 4), 0), ((1 / 4), 10), ((-3 / 4), 20), ((-1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 10)]],
    ![alternatingSixCyclotomicValue [((3 / 4), 0), ((3 / 4), 10), ((-3 / 4), 20), (-1, 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((3 / 4), 10), ((3 / 4), 20), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 20)],
      alternatingSixCyclotomicValue [((3 / 8), 0), ((1 / 4), 10), ((-1 / 2), 20), ((-3 / 8), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 4), 10), ((-1 / 4), 20), ((1 / 2), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 8), 10), ((1 / 8), 20)]],
    ![alternatingSixCyclotomicValue [(-1, 0)],
      alternatingSixCyclotomicValue [(1, 0), (-1, 20)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 10), ((1 / 2), 20)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 10)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [((-1 / 4), 10), ((-1 / 4), 20), ((-1 / 4), 30)]]
  ]

macro "close_cyclotomic_row11" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)


private theorem row11_eigenbasisInverse_mul_0_0 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        0 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 10 + ((3 / 4) : ℂ) * ζ ^ 14 - ((3 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_0_1 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        0 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_0_2 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        0 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_0_3 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        0 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 8) : ℂ) * ζ ^ 20 - ((1 / 8) : ℂ) * ζ ^ 24 + ((1 / 8) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_0_4 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        0 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 10 + ((3 / 4) : ℂ) * ζ ^ 14 - ((3 / 4) : ℂ) * ζ ^ 18)
private theorem row11_eigenbasisInverse_mul_0_5 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        0 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        0 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((3 / 8) : ℂ) - ((3 / 8) : ℂ) * ζ ^ 4 + ((3 / 8) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_1_0 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        1 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_1_1 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        1 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_1_2 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        1 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((11 / 12) : ℂ) - ((11 / 12) : ℂ) * ζ ^ 4 + ((11 / 12) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 10 - ((1 / 12) : ℂ) * ζ ^ 14 + ((1 / 12) : ℂ) * ζ ^ 18)
private theorem row11_eigenbasisInverse_mul_1_3 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        1 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 20 + ((1 / 12) : ℂ) * ζ ^ 24 - ((1 / 12) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_1_4 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        1 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((7 / 6) : ℂ) - ((7 / 6) : ℂ) * ζ ^ 4 + ((7 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 18)
private theorem row11_eigenbasisInverse_mul_1_5 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        1 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        1 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 3) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 24) : ℂ) * ζ ^ 10 + ((1 / 24) : ℂ) * ζ ^ 14 - ((1 / 24) : ℂ) * ζ ^ 18 + ((1 / 24) : ℂ) * ζ ^ 20 - ((1 / 24) : ℂ) * ζ ^ 24 + ((1 / 24) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_2_0 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        2 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 6) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 18)
private theorem row11_eigenbasisInverse_mul_2_1 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        2 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 18)
private theorem row11_eigenbasisInverse_mul_2_2 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        2 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((4 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 4 - ((4 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 18)
private theorem row11_eigenbasisInverse_mul_2_3 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        2 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 10 - ((1 / 12) : ℂ) * ζ ^ 14 + ((1 / 12) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_2_4 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        2 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_2_5 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        2 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        2 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((5 / 12) : ℂ) - ((5 / 12) : ℂ) * ζ ^ 4 + ((5 / 12) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 20 + ((1 / 12) : ℂ) * ζ ^ 24 - ((1 / 12) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_3_0 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        3 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 6) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_3_1 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        3 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 3) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_3_2 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        3 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8)
private theorem row11_eigenbasisInverse_mul_3_3 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        3 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 12) : ℂ) * ζ ^ 10 + ((1 / 12) : ℂ) * ζ ^ 14 - ((1 / 12) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_3_4 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        3 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 3) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_3_5 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        3 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        3 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_4_0 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        4 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_4_1 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        4 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_4_2 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        4 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((5 / 12) : ℂ) - ((5 / 12) : ℂ) * ζ ^ 4 + ((5 / 12) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18)
private theorem row11_eigenbasisInverse_mul_4_3 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        4 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 10 - ((1 / 12) : ℂ) * ζ ^ 14 + ((1 / 12) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_4_4 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        4 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((2 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 4 - ((2 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_4_5 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        4 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        4 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 4 - ((1 / 12) : ℂ) * ζ ^ 8 + ((3 / 8) : ℂ) * ζ ^ 10 - ((3 / 8) : ℂ) * ζ ^ 14 + ((3 / 8) : ℂ) * ζ ^ 18 + ((1 / 24) : ℂ) * ζ ^ 20 - ((1 / 24) : ℂ) * ζ ^ 24 + ((1 / 24) : ℂ) * ζ ^ 28)
private theorem row11_eigenbasisInverse_mul_5_0 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        5 0 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 0 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 0
private theorem row11_eigenbasisInverse_mul_5_1 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        5 1 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 1 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 0
private theorem row11_eigenbasisInverse_mul_5_2 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        5 2 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 2 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 0
private theorem row11_eigenbasisInverse_mul_5_3 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        5 3 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 3 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 0
private theorem row11_eigenbasisInverse_mul_5_4 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        5 4 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 4 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 0
private theorem row11_eigenbasisInverse_mul_5_5 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis)
        5 5 =
      (1 : Matrix (Fin 6) (Fin 6) ℂ)
        5 5 := by
  rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixCyclotomicValue,
      Matrix.one_apply,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 0
/-- The displayed row 11 matrix is a left inverse of its
eigenbasis. -/
theorem alternatingSixAmbientRow11EigenbasisInverse_mul :
    alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixAmbientRow11Eigenbasis =
      1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row11_eigenbasisInverse_mul_0_0
  · exact row11_eigenbasisInverse_mul_0_1
  · exact row11_eigenbasisInverse_mul_0_2
  · exact row11_eigenbasisInverse_mul_0_3
  · exact row11_eigenbasisInverse_mul_0_4
  · exact row11_eigenbasisInverse_mul_0_5
  · exact row11_eigenbasisInverse_mul_1_0
  · exact row11_eigenbasisInverse_mul_1_1
  · exact row11_eigenbasisInverse_mul_1_2
  · exact row11_eigenbasisInverse_mul_1_3
  · exact row11_eigenbasisInverse_mul_1_4
  · exact row11_eigenbasisInverse_mul_1_5
  · exact row11_eigenbasisInverse_mul_2_0
  · exact row11_eigenbasisInverse_mul_2_1
  · exact row11_eigenbasisInverse_mul_2_2
  · exact row11_eigenbasisInverse_mul_2_3
  · exact row11_eigenbasisInverse_mul_2_4
  · exact row11_eigenbasisInverse_mul_2_5
  · exact row11_eigenbasisInverse_mul_3_0
  · exact row11_eigenbasisInverse_mul_3_1
  · exact row11_eigenbasisInverse_mul_3_2
  · exact row11_eigenbasisInverse_mul_3_3
  · exact row11_eigenbasisInverse_mul_3_4
  · exact row11_eigenbasisInverse_mul_3_5
  · exact row11_eigenbasisInverse_mul_4_0
  · exact row11_eigenbasisInverse_mul_4_1
  · exact row11_eigenbasisInverse_mul_4_2
  · exact row11_eigenbasisInverse_mul_4_3
  · exact row11_eigenbasisInverse_mul_4_4
  · exact row11_eigenbasisInverse_mul_4_5
  · exact row11_eigenbasisInverse_mul_5_0
  · exact row11_eigenbasisInverse_mul_5_1
  · exact row11_eigenbasisInverse_mul_5_2
  · exact row11_eigenbasisInverse_mul_5_3
  · exact row11_eigenbasisInverse_mul_5_4
  · exact row11_eigenbasisInverse_mul_5_5

/-- The displayed row 11 inverse is also a right inverse. -/
theorem alternatingSixAmbientRow11Eigenbasis_mul_inverse :
    alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow11EigenbasisInverse_mul


private theorem row11_generatorB_mul_eigenbasis_0_0 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        0 0 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        0 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((2 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 4 - ((2 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 10 - ((4 / 3) : ℂ) * ζ ^ 14 + ((4 / 3) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28)
private theorem row11_generatorB_mul_eigenbasis_0_1 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        0 1 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        0 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((4 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 4 - ((4 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28)
private theorem row11_generatorB_mul_eigenbasis_0_2 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        0 2 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        0 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 6) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18)
private theorem row11_generatorB_mul_eigenbasis_0_3 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        0 3 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        0 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28 - ζ ^ 30 + ζ ^ 34 - ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 44 - ((1 / 2) : ℂ) * ζ ^ 48 - ((1 / 2) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 58)
private theorem row11_generatorB_mul_eigenbasis_0_4 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        0 4 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        0 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 3) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28 + ζ ^ 40 - ζ ^ 44 + ζ ^ 48)
private theorem row11_generatorB_mul_eigenbasis_0_5 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        0 5 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        0 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 - ((5 / 12) : ℂ) * ζ ^ 20 + ((5 / 12) : ℂ) * ζ ^ 24 - ((5 / 12) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 58 - ((1 / 2) : ℂ) * ζ ^ 70 + ((1 / 2) : ℂ) * ζ ^ 74 - ((1 / 2) : ℂ) * ζ ^ 78)
private theorem row11_generatorB_mul_eigenbasis_1_0 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        1 0 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        1 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((4 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 4 - ((4 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 18)
private theorem row11_generatorB_mul_eigenbasis_1_1 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        1 1 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        1 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((2 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 18)
private theorem row11_generatorB_mul_eigenbasis_1_2 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        1 2 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        1 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 18)
private theorem row11_generatorB_mul_eigenbasis_1_3 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        1 3 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        1 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 + ((7 / 6) : ℂ) * ζ ^ 10 - ((7 / 6) : ℂ) * ζ ^ 14 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30 - ((1 / 2) : ℂ) * ζ ^ 34 + ((1 / 2) : ℂ) * ζ ^ 38)
private theorem row11_generatorB_mul_eigenbasis_1_4 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        1 4 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        1 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-ζ ^ 10 + ζ ^ 14 - ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ζ ^ 40 + ζ ^ 44 - ζ ^ 48)
private theorem row11_generatorB_mul_eigenbasis_1_5 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        1 5 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        1 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((5 / 6) : ℂ) - ((5 / 6) : ℂ) * ζ ^ 4 + ((5 / 6) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30 + ((1 / 2) : ℂ) * ζ ^ 34 - ((1 / 2) : ℂ) * ζ ^ 38 - ((1 / 4) : ℂ) * ζ ^ 40 + ((1 / 4) : ℂ) * ζ ^ 44 - ((1 / 4) : ℂ) * ζ ^ 48 - ((1 / 4) : ℂ) * ζ ^ 50 + ((1 / 4) : ℂ) * ζ ^ 54 - ((1 / 4) : ℂ) * ζ ^ 58 + ((1 / 4) : ℂ) * ζ ^ 70 - ((1 / 4) : ℂ) * ζ ^ 74 + ((1 / 4) : ℂ) * ζ ^ 78 + ((1 / 4) : ℂ) * ζ ^ 80 - ((1 / 4) : ℂ) * ζ ^ 84 + ((1 / 4) : ℂ) * ζ ^ 88)
private theorem row11_generatorB_mul_eigenbasis_2_0 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        2 0 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        2 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28)
private theorem row11_generatorB_mul_eigenbasis_2_1 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        2 1 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        2 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28)
private theorem row11_generatorB_mul_eigenbasis_2_2 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        2 2 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        2 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 18)
private theorem row11_generatorB_mul_eigenbasis_2_3 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        2 3 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        2 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((3 / 2) : ℂ) - ((3 / 2) : ℂ) * ζ ^ 4 + ((3 / 2) : ℂ) * ζ ^ 8 + ((3 / 2) : ℂ) * ζ ^ 10 - ((3 / 2) : ℂ) * ζ ^ 14 + ((3 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 - ζ ^ 40 + ζ ^ 44 - ζ ^ 48 - ζ ^ 50 + ζ ^ 54 - ζ ^ 58)
private theorem row11_generatorB_mul_eigenbasis_2_4 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        2 4 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        2 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 - ((7 / 3) : ℂ) * ζ ^ 10 + ((7 / 3) : ℂ) * ζ ^ 14 - ((7 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28 + (2 : ℂ) * ζ ^ 50 - (2 : ℂ) * ζ ^ 54 + (2 : ℂ) * ζ ^ 58)
private theorem row11_generatorB_mul_eigenbasis_2_5 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        2 5 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        2 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 12) : ℂ) * ζ ^ 10 - ((1 / 12) : ℂ) * ζ ^ 14 + ((1 / 12) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30 + ((1 / 2) : ℂ) * ζ ^ 34 - ((1 / 2) : ℂ) * ζ ^ 38 - ((1 / 2) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 54 - ((1 / 2) : ℂ) * ζ ^ 58)
private theorem row11_generatorB_mul_eigenbasis_3_0 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        3 0 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        3 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28)
private theorem row11_generatorB_mul_eigenbasis_3_1 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        3 1 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        3 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28)
private theorem row11_generatorB_mul_eigenbasis_3_2 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        3 2 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        3 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 18)
private theorem row11_generatorB_mul_eigenbasis_3_3 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        3 3 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        3 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28)
private theorem row11_generatorB_mul_eigenbasis_3_4 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        3 4 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        3 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28)
private theorem row11_generatorB_mul_eigenbasis_3_5 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        3 5 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        3 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 10 - ((1 / 12) : ℂ) * ζ ^ 14 + ((1 / 12) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 20 - ((3 / 4) : ℂ) * ζ ^ 24 + ((3 / 4) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 60 + ((1 / 2) : ℂ) * ζ ^ 64 - ((1 / 2) : ℂ) * ζ ^ 68 - ((1 / 2) : ℂ) * ζ ^ 80 + ((1 / 2) : ℂ) * ζ ^ 84 - ((1 / 2) : ℂ) * ζ ^ 88)
private theorem row11_generatorB_mul_eigenbasis_4_0 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        4 0 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        4 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 0
private theorem row11_generatorB_mul_eigenbasis_4_1 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        4 1 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        4 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 0
private theorem row11_generatorB_mul_eigenbasis_4_2 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        4 2 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        4 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 0
private theorem row11_generatorB_mul_eigenbasis_4_3 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        4 3 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        4 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 0
private theorem row11_generatorB_mul_eigenbasis_4_4 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        4 4 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        4 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 0
private theorem row11_generatorB_mul_eigenbasis_4_5 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        4 5 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        4 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-ζ ^ 30 + ζ ^ 34 - ζ ^ 38 - ζ ^ 50 + ζ ^ 54 - ζ ^ 58)
private theorem row11_generatorB_mul_eigenbasis_5_0 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        5 0 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        5 0 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28)
private theorem row11_generatorB_mul_eigenbasis_5_1 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        5 1 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        5 1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 3) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28)
private theorem row11_generatorB_mul_eigenbasis_5_2 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        5 2 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        5 2 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 8 - ((7 / 6) : ℂ) * ζ ^ 10 + ((7 / 6) : ℂ) * ζ ^ 14 - ((7 / 6) : ℂ) * ζ ^ 18)
private theorem row11_generatorB_mul_eigenbasis_5_3 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        5 3 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        5 3 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28)
private theorem row11_generatorB_mul_eigenbasis_5_4 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        5 4 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        5 4 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 18 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)
private theorem row11_generatorB_mul_eigenbasis_5_5 :
    (alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis)
        5 5 =
      (alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal)
        5 5 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp [
      alternatingSixFiveAmbient_row11_matrixB,
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11GeneratorBDiagonal,
      alternatingSixAmbientRow11GeneratorBEigenvalue,
      alternatingSixAmbientRow11EigenvalueLabel,
      alternatingSixOrderFourEigenvalue,
      alternatingSixOrderFourEigenvalueExponent,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 20 + ((1 / 12) : ℂ) * ζ ^ 24 - ((1 / 12) : ℂ) * ζ ^ 28)
/-- The checked row 11 basis diagonalizes the second
generator. -/
theorem alternatingSixAmbientRow11GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row11_matrixB *
        alternatingSixAmbientRow11Eigenbasis =
      alternatingSixAmbientRow11Eigenbasis *
        alternatingSixAmbientRow11GeneratorBDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row11_generatorB_mul_eigenbasis_0_0
  · exact row11_generatorB_mul_eigenbasis_0_1
  · exact row11_generatorB_mul_eigenbasis_0_2
  · exact row11_generatorB_mul_eigenbasis_0_3
  · exact row11_generatorB_mul_eigenbasis_0_4
  · exact row11_generatorB_mul_eigenbasis_0_5
  · exact row11_generatorB_mul_eigenbasis_1_0
  · exact row11_generatorB_mul_eigenbasis_1_1
  · exact row11_generatorB_mul_eigenbasis_1_2
  · exact row11_generatorB_mul_eigenbasis_1_3
  · exact row11_generatorB_mul_eigenbasis_1_4
  · exact row11_generatorB_mul_eigenbasis_1_5
  · exact row11_generatorB_mul_eigenbasis_2_0
  · exact row11_generatorB_mul_eigenbasis_2_1
  · exact row11_generatorB_mul_eigenbasis_2_2
  · exact row11_generatorB_mul_eigenbasis_2_3
  · exact row11_generatorB_mul_eigenbasis_2_4
  · exact row11_generatorB_mul_eigenbasis_2_5
  · exact row11_generatorB_mul_eigenbasis_3_0
  · exact row11_generatorB_mul_eigenbasis_3_1
  · exact row11_generatorB_mul_eigenbasis_3_2
  · exact row11_generatorB_mul_eigenbasis_3_3
  · exact row11_generatorB_mul_eigenbasis_3_4
  · exact row11_generatorB_mul_eigenbasis_3_5
  · exact row11_generatorB_mul_eigenbasis_4_0
  · exact row11_generatorB_mul_eigenbasis_4_1
  · exact row11_generatorB_mul_eigenbasis_4_2
  · exact row11_generatorB_mul_eigenbasis_4_3
  · exact row11_generatorB_mul_eigenbasis_4_4
  · exact row11_generatorB_mul_eigenbasis_4_5
  · exact row11_generatorB_mul_eigenbasis_5_0
  · exact row11_generatorB_mul_eigenbasis_5_1
  · exact row11_generatorB_mul_eigenbasis_5_2
  · exact row11_generatorB_mul_eigenbasis_5_3
  · exact row11_generatorB_mul_eigenbasis_5_4
  · exact row11_generatorB_mul_eigenbasis_5_5


private theorem row11_transformedGeneratorA_0_0 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        0 0 =
      alternatingSixAmbientRow11TransformedGeneratorA
        0 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 3) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 18 + ((7 / 6) : ℂ) * ζ ^ 20 - ((7 / 6) : ℂ) * ζ ^ 24 + ((7 / 6) : ℂ) * ζ ^ 28 + ((7 / 12) : ℂ) * ζ ^ 30 - ((7 / 12) : ℂ) * ζ ^ 34 + ((7 / 12) : ℂ) * ζ ^ 38 - ((5 / 12) : ℂ) * ζ ^ 40 + ((5 / 12) : ℂ) * ζ ^ 44 - ((5 / 12) : ℂ) * ζ ^ 48 - ((1 / 4) : ℂ) * ζ ^ 50 + ((1 / 4) : ℂ) * ζ ^ 54 - ((1 / 4) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_0_1 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        0 1 =
      alternatingSixAmbientRow11TransformedGeneratorA
        0 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((5 / 12) : ℂ) - ((5 / 12) : ℂ) * ζ ^ 4 + ((5 / 12) : ℂ) * ζ ^ 8 - ((1 / 12) : ℂ) * ζ ^ 10 + ((1 / 12) : ℂ) * ζ ^ 14 - ((1 / 12) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30 - ((2 / 3) : ℂ) * ζ ^ 34 + ((2 / 3) : ℂ) * ζ ^ 38 + ((1 / 12) : ℂ) * ζ ^ 40 - ((1 / 12) : ℂ) * ζ ^ 44 + ((1 / 12) : ℂ) * ζ ^ 48 - ((1 / 4) : ℂ) * ζ ^ 50 + ((1 / 4) : ℂ) * ζ ^ 54 - ((1 / 4) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_0_2 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        0 2 =
      alternatingSixAmbientRow11TransformedGeneratorA
        0 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 18 - ((1 / 24) : ℂ) * ζ ^ 20 + ((1 / 24) : ℂ) * ζ ^ 24 - ((1 / 24) : ℂ) * ζ ^ 28 - ((3 / 8) : ℂ) * ζ ^ 30 + ((3 / 8) : ℂ) * ζ ^ 34 - ((3 / 8) : ℂ) * ζ ^ 38 + ((1 / 3) : ℂ) * ζ ^ 40 - ((1 / 3) : ℂ) * ζ ^ 44 + ((1 / 3) : ℂ) * ζ ^ 48 + ((1 / 4) : ℂ) * ζ ^ 50 - ((1 / 4) : ℂ) * ζ ^ 54 + ((1 / 4) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_0_3 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        0 3 =
      alternatingSixAmbientRow11TransformedGeneratorA
        0 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((7 / 8) : ℂ) - ((7 / 8) : ℂ) * ζ ^ 4 + ((7 / 8) : ℂ) * ζ ^ 8 - ((5 / 8) : ℂ) * ζ ^ 10 + ((5 / 8) : ℂ) * ζ ^ 14 - ((5 / 8) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 + ((1 / 24) : ℂ) * ζ ^ 30 - ((1 / 24) : ℂ) * ζ ^ 34 + ((1 / 24) : ℂ) * ζ ^ 38 - ((1 / 4) : ℂ) * ζ ^ 40 + ((1 / 4) : ℂ) * ζ ^ 44 - ((1 / 4) : ℂ) * ζ ^ 48 - ((5 / 24) : ℂ) * ζ ^ 50 + ((5 / 24) : ℂ) * ζ ^ 54 - ((5 / 24) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_0_4 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        0 4 =
      alternatingSixAmbientRow11TransformedGeneratorA
        0 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 3) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 - ((1 / 6) : ℂ) * ζ ^ 30 + ((1 / 6) : ℂ) * ζ ^ 34 - ((1 / 6) : ℂ) * ζ ^ 38 + ((1 / 12) : ℂ) * ζ ^ 40 - ((1 / 12) : ℂ) * ζ ^ 44 + ((1 / 12) : ℂ) * ζ ^ 48 + ((2 / 3) : ℂ) * ζ ^ 50 - ((2 / 3) : ℂ) * ζ ^ 54 + ((2 / 3) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_0_5 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        0 5 =
      alternatingSixAmbientRow11TransformedGeneratorA
        0 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((3 / 8) : ℂ) + ((3 / 8) : ℂ) * ζ ^ 4 - ((3 / 8) : ℂ) * ζ ^ 8 - ((1 / 24) : ℂ) * ζ ^ 10 + ((1 / 24) : ℂ) * ζ ^ 14 - ((1 / 24) : ℂ) * ζ ^ 18 - ((7 / 24) : ℂ) * ζ ^ 20 + ((7 / 24) : ℂ) * ζ ^ 24 - ((7 / 24) : ℂ) * ζ ^ 28 - ((7 / 48) : ℂ) * ζ ^ 30 + ((7 / 48) : ℂ) * ζ ^ 34 - ((7 / 48) : ℂ) * ζ ^ 38 - ((5 / 16) : ℂ) * ζ ^ 40 + ((5 / 16) : ℂ) * ζ ^ 44 - ((5 / 16) : ℂ) * ζ ^ 48 - ((1 / 24) : ℂ) * ζ ^ 50 + ((1 / 24) : ℂ) * ζ ^ 54 - ((1 / 24) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_1_0 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        1 0 =
      alternatingSixAmbientRow11TransformedGeneratorA
        1 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((17 / 12) : ℂ) + ((17 / 12) : ℂ) * ζ ^ 4 - ((17 / 12) : ℂ) * ζ ^ 8 - ((1 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 18 + ((11 / 12) : ℂ) * ζ ^ 20 - ((11 / 12) : ℂ) * ζ ^ 24 + ((11 / 12) : ℂ) * ζ ^ 28 - ((7 / 12) : ℂ) * ζ ^ 40 + ((7 / 12) : ℂ) * ζ ^ 44 - ((7 / 12) : ℂ) * ζ ^ 48 - ((1 / 6) : ℂ) * ζ ^ 50 + ((1 / 6) : ℂ) * ζ ^ 54 - ((1 / 6) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_1_1 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        1 1 =
      alternatingSixAmbientRow11TransformedGeneratorA
        1 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 10 + ((3 / 4) : ℂ) * ζ ^ 14 - ((3 / 4) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30 - ((2 / 3) : ℂ) * ζ ^ 34 + ((2 / 3) : ℂ) * ζ ^ 38 - ((1 / 4) : ℂ) * ζ ^ 40 + ((1 / 4) : ℂ) * ζ ^ 44 - ((1 / 4) : ℂ) * ζ ^ 48 - ((1 / 6) : ℂ) * ζ ^ 50 + ((1 / 6) : ℂ) * ζ ^ 54 - ((1 / 6) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_1_2 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        1 2 =
      alternatingSixAmbientRow11TransformedGeneratorA
        1 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 3) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 24) : ℂ) * ζ ^ 10 + ((1 / 24) : ℂ) * ζ ^ 14 - ((1 / 24) : ℂ) * ζ ^ 18 - ((7 / 24) : ℂ) * ζ ^ 20 + ((7 / 24) : ℂ) * ζ ^ 24 - ((7 / 24) : ℂ) * ζ ^ 28 + ((1 / 4) : ℂ) * ζ ^ 30 - ((1 / 4) : ℂ) * ζ ^ 34 + ((1 / 4) : ℂ) * ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 48 - ((1 / 6) : ℂ) * ζ ^ 50 + ((1 / 6) : ℂ) * ζ ^ 54 - ((1 / 6) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_1_3 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        1 3 =
      alternatingSixAmbientRow11TransformedGeneratorA
        1 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((3 / 8) : ℂ) - ((3 / 8) : ℂ) * ζ ^ 4 + ((3 / 8) : ℂ) * ζ ^ 8 + ((1 / 24) : ℂ) * ζ ^ 10 - ((1 / 24) : ℂ) * ζ ^ 14 + ((1 / 24) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28 - ((7 / 24) : ℂ) * ζ ^ 30 + ((7 / 24) : ℂ) * ζ ^ 34 - ((7 / 24) : ℂ) * ζ ^ 38 + ((7 / 24) : ℂ) * ζ ^ 40 - ((7 / 24) : ℂ) * ζ ^ 44 + ((7 / 24) : ℂ) * ζ ^ 48 + ((5 / 12) : ℂ) * ζ ^ 50 - ((5 / 12) : ℂ) * ζ ^ 54 + ((5 / 12) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_1_4 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        1 4 =
      alternatingSixAmbientRow11TransformedGeneratorA
        1 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 18 - ((11 / 12) : ℂ) * ζ ^ 20 + ((11 / 12) : ℂ) * ζ ^ 24 - ((11 / 12) : ℂ) * ζ ^ 28 + ((1 / 12) : ℂ) * ζ ^ 30 - ((1 / 12) : ℂ) * ζ ^ 34 + ((1 / 12) : ℂ) * ζ ^ 38 + ((1 / 6) : ℂ) * ζ ^ 40 - ((1 / 6) : ℂ) * ζ ^ 44 + ((1 / 6) : ℂ) * ζ ^ 48 - ((2 / 3) : ℂ) * ζ ^ 50 + ((2 / 3) : ℂ) * ζ ^ 54 - ((2 / 3) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_1_5 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        1 5 =
      alternatingSixAmbientRow11TransformedGeneratorA
        1 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 10 - ((1 / 12) : ℂ) * ζ ^ 14 + ((1 / 12) : ℂ) * ζ ^ 18 - ((7 / 48) : ℂ) * ζ ^ 20 + ((7 / 48) : ℂ) * ζ ^ 24 - ((7 / 48) : ℂ) * ζ ^ 28 - ((1 / 48) : ℂ) * ζ ^ 30 + ((1 / 48) : ℂ) * ζ ^ 34 - ((1 / 48) : ℂ) * ζ ^ 38 - ((1 / 24) : ℂ) * ζ ^ 50 + ((1 / 24) : ℂ) * ζ ^ 54 - ((1 / 24) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_2_0 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        2 0 =
      alternatingSixAmbientRow11TransformedGeneratorA
        2 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 18 - ((7 / 6) : ℂ) * ζ ^ 20 + ((7 / 6) : ℂ) * ζ ^ 24 - ((7 / 6) : ℂ) * ζ ^ 28 - ((2 / 3) : ℂ) * ζ ^ 30 + ((2 / 3) : ℂ) * ζ ^ 34 - ((2 / 3) : ℂ) * ζ ^ 38 - ((1 / 3) : ℂ) * ζ ^ 40 + ((1 / 3) : ℂ) * ζ ^ 44 - ((1 / 3) : ℂ) * ζ ^ 48 - ((1 / 6) : ℂ) * ζ ^ 50 + ((1 / 6) : ℂ) * ζ ^ 54 - ((1 / 6) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_2_1 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        2 1 =
      alternatingSixAmbientRow11TransformedGeneratorA
        2 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 30 + ((1 / 2) : ℂ) * ζ ^ 34 - ((1 / 2) : ℂ) * ζ ^ 38 - ((1 / 6) : ℂ) * ζ ^ 50 + ((1 / 6) : ℂ) * ζ ^ 54 - ((1 / 6) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_2_2 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        2 2 =
      alternatingSixAmbientRow11TransformedGeneratorA
        2 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 + ((5 / 12) : ℂ) * ζ ^ 20 - ((5 / 12) : ℂ) * ζ ^ 24 + ((5 / 12) : ℂ) * ζ ^ 28 - ((2 / 3) : ℂ) * ζ ^ 30 + ((2 / 3) : ℂ) * ζ ^ 34 - ((2 / 3) : ℂ) * ζ ^ 38 - ((1 / 3) : ℂ) * ζ ^ 40 + ((1 / 3) : ℂ) * ζ ^ 44 - ((1 / 3) : ℂ) * ζ ^ 48 + ((1 / 3) : ℂ) * ζ ^ 50 - ((1 / 3) : ℂ) * ζ ^ 54 + ((1 / 3) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_2_3 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        2 3 =
      alternatingSixAmbientRow11TransformedGeneratorA
        2 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28 + ((11 / 12) : ℂ) * ζ ^ 30 - ((11 / 12) : ℂ) * ζ ^ 34 + ((11 / 12) : ℂ) * ζ ^ 38 - ((7 / 12) : ℂ) * ζ ^ 40 + ((7 / 12) : ℂ) * ζ ^ 44 - ((7 / 12) : ℂ) * ζ ^ 48 - ((7 / 12) : ℂ) * ζ ^ 50 + ((7 / 12) : ℂ) * ζ ^ 54 - ((7 / 12) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_2_4 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        2 4 =
      alternatingSixAmbientRow11TransformedGeneratorA
        2 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 28 - ((2 / 3) : ℂ) * ζ ^ 30 + ((2 / 3) : ℂ) * ζ ^ 34 - ((2 / 3) : ℂ) * ζ ^ 38 - ((1 / 6) : ℂ) * ζ ^ 40 + ((1 / 6) : ℂ) * ζ ^ 44 - ((1 / 6) : ℂ) * ζ ^ 48 + ((4 / 3) : ℂ) * ζ ^ 50 - ((4 / 3) : ℂ) * ζ ^ 54 + ((4 / 3) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_2_5 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        2 5 =
      alternatingSixAmbientRow11TransformedGeneratorA
        2 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((5 / 24) : ℂ) + ((5 / 24) : ℂ) * ζ ^ 4 - ((5 / 24) : ℂ) * ζ ^ 8 - ((1 / 8) : ℂ) * ζ ^ 10 + ((1 / 8) : ℂ) * ζ ^ 14 - ((1 / 8) : ℂ) * ζ ^ 18 - ((1 / 8) : ℂ) * ζ ^ 20 + ((1 / 8) : ℂ) * ζ ^ 24 - ((1 / 8) : ℂ) * ζ ^ 28 + ((1 / 24) : ℂ) * ζ ^ 30 - ((1 / 24) : ℂ) * ζ ^ 34 + ((1 / 24) : ℂ) * ζ ^ 38 + ((1 / 6) : ℂ) * ζ ^ 40 - ((1 / 6) : ℂ) * ζ ^ 44 + ((1 / 6) : ℂ) * ζ ^ 48 + ((1 / 6) : ℂ) * ζ ^ 50 - ((1 / 6) : ℂ) * ζ ^ 54 + ((1 / 6) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_3_0 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        3 0 =
      alternatingSixAmbientRow11TransformedGeneratorA
        3 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((5 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 4 - ((5 / 6) : ℂ) * ζ ^ 8 - ((11 / 6) : ℂ) * ζ ^ 10 + ((11 / 6) : ℂ) * ζ ^ 14 - ((11 / 6) : ℂ) * ζ ^ 18 + ((7 / 6) : ℂ) * ζ ^ 30 - ((7 / 6) : ℂ) * ζ ^ 34 + ((7 / 6) : ℂ) * ζ ^ 38 + ((1 / 6) : ℂ) * ζ ^ 40 - ((1 / 6) : ℂ) * ζ ^ 44 + ((1 / 6) : ℂ) * ζ ^ 48 - ((1 / 6) : ℂ) * ζ ^ 50 + ((1 / 6) : ℂ) * ζ ^ 54 - ((1 / 6) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_3_1 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        3 1 =
      alternatingSixAmbientRow11TransformedGeneratorA
        3 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 - ((7 / 6) : ℂ) * ζ ^ 20 + ((7 / 6) : ℂ) * ζ ^ 24 - ((7 / 6) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 30 - ((1 / 3) : ℂ) * ζ ^ 34 + ((1 / 3) : ℂ) * ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 48 - ((1 / 6) : ℂ) * ζ ^ 50 + ((1 / 6) : ℂ) * ζ ^ 54 - ((1 / 6) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_3_2 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        3 2 =
      alternatingSixAmbientRow11TransformedGeneratorA
        3 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((5 / 12) : ℂ) + ((5 / 12) : ℂ) * ζ ^ 4 - ((5 / 12) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 28 + ((7 / 6) : ℂ) * ζ ^ 30 - ((7 / 6) : ℂ) * ζ ^ 34 + ((7 / 6) : ℂ) * ζ ^ 38 - ((1 / 6) : ℂ) * ζ ^ 40 + ((1 / 6) : ℂ) * ζ ^ 44 - ((1 / 6) : ℂ) * ζ ^ 48 - ((1 / 3) : ℂ) * ζ ^ 50 + ((1 / 3) : ℂ) * ζ ^ 54 - ((1 / 3) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_3_3 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        3 3 =
      alternatingSixAmbientRow11TransformedGeneratorA
        3 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 - ((7 / 12) : ℂ) * ζ ^ 20 + ((7 / 12) : ℂ) * ζ ^ 24 - ((7 / 12) : ℂ) * ζ ^ 28 + ((5 / 12) : ℂ) * ζ ^ 30 - ((5 / 12) : ℂ) * ζ ^ 34 + ((5 / 12) : ℂ) * ζ ^ 38 + ((1 / 2) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 44 + ((1 / 2) : ℂ) * ζ ^ 48 - ((1 / 12) : ℂ) * ζ ^ 50 + ((1 / 12) : ℂ) * ζ ^ 54 - ((1 / 12) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_3_4 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        3 4 =
      alternatingSixAmbientRow11TransformedGeneratorA
        3 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 24 + ((3 / 2) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30 - ((1 / 2) : ℂ) * ζ ^ 34 + ((1 / 2) : ℂ) * ζ ^ 38 - ((11 / 6) : ℂ) * ζ ^ 40 + ((11 / 6) : ℂ) * ζ ^ 44 - ((11 / 6) : ℂ) * ζ ^ 48 + ((1 / 3) : ℂ) * ζ ^ 50 - ((1 / 3) : ℂ) * ζ ^ 54 + ((1 / 3) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_3_5 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        3 5 =
      alternatingSixAmbientRow11TransformedGeneratorA
        3 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 4 + ((1 / 12) : ℂ) * ζ ^ 8 + ((1 / 24) : ℂ) * ζ ^ 10 - ((1 / 24) : ℂ) * ζ ^ 14 + ((1 / 24) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((7 / 24) : ℂ) * ζ ^ 30 + ((7 / 24) : ℂ) * ζ ^ 34 - ((7 / 24) : ℂ) * ζ ^ 38 - ((1 / 6) : ℂ) * ζ ^ 40 + ((1 / 6) : ℂ) * ζ ^ 44 - ((1 / 6) : ℂ) * ζ ^ 48 + ((1 / 4) : ℂ) * ζ ^ 50 - ((1 / 4) : ℂ) * ζ ^ 54 + ((1 / 4) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_4_0 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        4 0 =
      alternatingSixAmbientRow11TransformedGeneratorA
        4 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((13 / 12) : ℂ) + ((13 / 12) : ℂ) * ζ ^ 4 - ((13 / 12) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30 - ((2 / 3) : ℂ) * ζ ^ 34 + ((2 / 3) : ℂ) * ζ ^ 38 + ((11 / 12) : ℂ) * ζ ^ 40 - ((11 / 12) : ℂ) * ζ ^ 44 + ((11 / 12) : ℂ) * ζ ^ 48 + ((1 / 3) : ℂ) * ζ ^ 50 - ((1 / 3) : ℂ) * ζ ^ 54 + ((1 / 3) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_4_1 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        4 1 =
      alternatingSixAmbientRow11TransformedGeneratorA
        4 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 8 - ((5 / 12) : ℂ) * ζ ^ 10 + ((5 / 12) : ℂ) * ζ ^ 14 - ((5 / 12) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28 - ((1 / 6) : ℂ) * ζ ^ 30 + ((1 / 6) : ℂ) * ζ ^ 34 - ((1 / 6) : ℂ) * ζ ^ 38 + ((1 / 4) : ℂ) * ζ ^ 40 - ((1 / 4) : ℂ) * ζ ^ 44 + ((1 / 4) : ℂ) * ζ ^ 48 + ((1 / 3) : ℂ) * ζ ^ 50 - ((1 / 3) : ℂ) * ζ ^ 54 + ((1 / 3) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_4_2 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        4 2 =
      alternatingSixAmbientRow11TransformedGeneratorA
        4 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((5 / 12) : ℂ) + ((5 / 12) : ℂ) * ζ ^ 4 - ((5 / 12) : ℂ) * ζ ^ 8 + ((7 / 24) : ℂ) * ζ ^ 10 - ((7 / 24) : ℂ) * ζ ^ 14 + ((7 / 24) : ℂ) * ζ ^ 18 + ((7 / 8) : ℂ) * ζ ^ 20 - ((7 / 8) : ℂ) * ζ ^ 24 + ((7 / 8) : ℂ) * ζ ^ 28 + ((5 / 12) : ℂ) * ζ ^ 30 - ((5 / 12) : ℂ) * ζ ^ 34 + ((5 / 12) : ℂ) * ζ ^ 38 - ((1 / 6) : ℂ) * ζ ^ 40 + ((1 / 6) : ℂ) * ζ ^ 44 - ((1 / 6) : ℂ) * ζ ^ 48 - ((1 / 6) : ℂ) * ζ ^ 50 + ((1 / 6) : ℂ) * ζ ^ 54 - ((1 / 6) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_4_3 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        4 3 =
      alternatingSixAmbientRow11TransformedGeneratorA
        4 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((1 / 8) : ℂ) - ((1 / 8) : ℂ) * ζ ^ 4 + ((1 / 8) : ℂ) * ζ ^ 8 - ((1 / 24) : ℂ) * ζ ^ 10 + ((1 / 24) : ℂ) * ζ ^ 14 - ((1 / 24) : ℂ) * ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 20 + ((3 / 4) : ℂ) * ζ ^ 24 - ((3 / 4) : ℂ) * ζ ^ 28 - ((5 / 8) : ℂ) * ζ ^ 30 + ((5 / 8) : ℂ) * ζ ^ 34 - ((5 / 8) : ℂ) * ζ ^ 38 + ((7 / 24) : ℂ) * ζ ^ 40 - ((7 / 24) : ℂ) * ζ ^ 44 + ((7 / 24) : ℂ) * ζ ^ 48 + ((1 / 6) : ℂ) * ζ ^ 50 - ((1 / 6) : ℂ) * ζ ^ 54 + ((1 / 6) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_4_4 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        4 4 =
      alternatingSixAmbientRow11TransformedGeneratorA
        4 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((5 / 12) : ℂ) * ζ ^ 10 - ((5 / 12) : ℂ) * ζ ^ 14 + ((5 / 12) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 20 - ((3 / 4) : ℂ) * ζ ^ 24 + ((3 / 4) : ℂ) * ζ ^ 28 + ((7 / 12) : ℂ) * ζ ^ 30 - ((7 / 12) : ℂ) * ζ ^ 34 + ((7 / 12) : ℂ) * ζ ^ 38 - ((2 / 3) : ℂ) * ζ ^ 50 + ((2 / 3) : ℂ) * ζ ^ 54 - ((2 / 3) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_4_5 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        4 5 =
      alternatingSixAmbientRow11TransformedGeneratorA
        4 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((5 / 24) : ℂ) - ((5 / 24) : ℂ) * ζ ^ 4 + ((5 / 24) : ℂ) * ζ ^ 8 - ((5 / 24) : ℂ) * ζ ^ 10 + ((5 / 24) : ℂ) * ζ ^ 14 - ((5 / 24) : ℂ) * ζ ^ 18 - ((11 / 48) : ℂ) * ζ ^ 20 + ((11 / 48) : ℂ) * ζ ^ 24 - ((11 / 48) : ℂ) * ζ ^ 28 - ((1 / 48) : ℂ) * ζ ^ 30 + ((1 / 48) : ℂ) * ζ ^ 34 - ((1 / 48) : ℂ) * ζ ^ 38 - ((1 / 6) : ℂ) * ζ ^ 40 + ((1 / 6) : ℂ) * ζ ^ 44 - ((1 / 6) : ℂ) * ζ ^ 48 - ((1 / 8) : ℂ) * ζ ^ 50 + ((1 / 8) : ℂ) * ζ ^ 54 - ((1 / 8) : ℂ) * ζ ^ 58)
private theorem row11_transformedGeneratorA_5_0 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        5 0 =
      alternatingSixAmbientRow11TransformedGeneratorA
        5 0 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 ((1 : ℂ) - ζ ^ 4 + ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28)
private theorem row11_transformedGeneratorA_5_1 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        5 1 =
      alternatingSixAmbientRow11TransformedGeneratorA
        5 1 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28)
private theorem row11_transformedGeneratorA_5_2 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        5 2 =
      alternatingSixAmbientRow11TransformedGeneratorA
        5 2 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((7 / 6) : ℂ) - ((7 / 6) : ℂ) * ζ ^ 4 + ((7 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 18 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)
private theorem row11_transformedGeneratorA_5_3 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        5 3 =
      alternatingSixAmbientRow11TransformedGeneratorA
        5 3 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 18 + ((7 / 6) : ℂ) * ζ ^ 20 - ((7 / 6) : ℂ) * ζ ^ 24 + ((7 / 6) : ℂ) * ζ ^ 28)
private theorem row11_transformedGeneratorA_5_4 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        5 4 =
      alternatingSixAmbientRow11TransformedGeneratorA
        5 4 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 18 - (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 28)
private theorem row11_transformedGeneratorA_5_5 :
    (alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis)
        5 5 =
      alternatingSixAmbientRow11TransformedGeneratorA
        5 5 := by
  simp_rw [Matrix.mul_apply]
  simp [
      alternatingSixAmbientRow11Eigenbasis,
      alternatingSixAmbientRow11EigenbasisInverse,
      alternatingSixFiveAmbient_row11_matrixA,
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue,
      Fin.sum_univ_succ]
  try close_cyclotomic_row11 (-((5 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 4 - ((5 / 6) : ℂ) * ζ ^ 8 + ((7 / 12) : ℂ) * ζ ^ 10 - ((7 / 12) : ℂ) * ζ ^ 14 + ((7 / 12) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 28)
/-- Exact conjugation formula for the row 11 first
generator. -/
theorem alternatingSixAmbientRow11TransformedGeneratorA_eq :
    alternatingSixAmbientRow11EigenbasisInverse *
        alternatingSixFiveAmbient_row11_matrixA *
        alternatingSixAmbientRow11Eigenbasis =
      alternatingSixAmbientRow11TransformedGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact row11_transformedGeneratorA_0_0
  · exact row11_transformedGeneratorA_0_1
  · exact row11_transformedGeneratorA_0_2
  · exact row11_transformedGeneratorA_0_3
  · exact row11_transformedGeneratorA_0_4
  · exact row11_transformedGeneratorA_0_5
  · exact row11_transformedGeneratorA_1_0
  · exact row11_transformedGeneratorA_1_1
  · exact row11_transformedGeneratorA_1_2
  · exact row11_transformedGeneratorA_1_3
  · exact row11_transformedGeneratorA_1_4
  · exact row11_transformedGeneratorA_1_5
  · exact row11_transformedGeneratorA_2_0
  · exact row11_transformedGeneratorA_2_1
  · exact row11_transformedGeneratorA_2_2
  · exact row11_transformedGeneratorA_2_3
  · exact row11_transformedGeneratorA_2_4
  · exact row11_transformedGeneratorA_2_5
  · exact row11_transformedGeneratorA_3_0
  · exact row11_transformedGeneratorA_3_1
  · exact row11_transformedGeneratorA_3_2
  · exact row11_transformedGeneratorA_3_3
  · exact row11_transformedGeneratorA_3_4
  · exact row11_transformedGeneratorA_3_5
  · exact row11_transformedGeneratorA_4_0
  · exact row11_transformedGeneratorA_4_1
  · exact row11_transformedGeneratorA_4_2
  · exact row11_transformedGeneratorA_4_3
  · exact row11_transformedGeneratorA_4_4
  · exact row11_transformedGeneratorA_4_5
  · exact row11_transformedGeneratorA_5_0
  · exact row11_transformedGeneratorA_5_1
  · exact row11_transformedGeneratorA_5_2
  · exact row11_transformedGeneratorA_5_3
  · exact row11_transformedGeneratorA_5_4
  · exact row11_transformedGeneratorA_5_5


end InductiveMcKay
end McKayConjecture
