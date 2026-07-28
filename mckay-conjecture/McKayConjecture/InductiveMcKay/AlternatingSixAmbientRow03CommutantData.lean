/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixCyclotomicNonzero
import McKayConjecture.InductiveMcKay.AlternatingSixDegreeThreeEigenvalues
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow03

/-!
# Checked commutant data for ambient row 03

This generated certificate contains only exact cyclotomic linear algebra:
an eigenbasis and inverse, diagonalization of the second generator, and two
nonzero connecting entries of the transformed first generator.
-/

noncomputable section

set_option linter.style.longLine false

open Polynomial

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Eigenbasis for the row 03 second generator. -/
def alternatingSixAmbientRow03Eigenbasis :
    Matrix (Fin 3) (Fin 3) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((-1 / 2), 4), ((1 / 2), 8), ((1 / 2), 12), ((1 / 2), 16), ((-1 / 2), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((1 / 2), 2), ((-1 / 2), 10), ((-1 / 2), 14), ((-1 / 2), 18), ((1 / 2), 20), ((-1 / 2), 22), ((1 / 2), 26), (1, 30)],
      alternatingSixCyclotomicValue [((-1 / 2), 0), ((-1 / 2), 2), ((1 / 2), 10), ((1 / 2), 14), ((1 / 2), 18), ((1 / 2), 20), ((1 / 2), 22), ((-1 / 2), 26), (-1, 30)]],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [((-1 / 2), 10), ((-1 / 2), 14), ((1 / 2), 26)],
      alternatingSixCyclotomicValue [((1 / 2), 10), ((1 / 2), 14), ((-1 / 2), 26)]],
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)]]
  ]

/-- Explicit inverse of the row 03 eigenbasis. -/
def alternatingSixAmbientRow03EigenbasisInverse :
    Matrix (Fin 3) (Fin 3) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [(1, 0), (1, 4), (-1, 8), (-1, 12), (-1, 16), (-1, 20), (1, 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 4), ((1 / 2), 8), ((1 / 2), 12), ((1 / 2), 16), (1, 20), ((-1 / 2), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 8), ((-1 / 2), 12), ((1 / 2), 28)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 2), ((-1 / 2), 10), ((-1 / 2), 14), ((-1 / 2), 18), ((-1 / 2), 22), ((1 / 2), 26)],
      alternatingSixCyclotomicValue [((-1 / 4), 2), ((1 / 4), 10), ((1 / 4), 18), ((1 / 4), 22), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 2), 10), ((-1 / 4), 14), ((1 / 4), 26), ((1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((-1 / 2), 2), ((1 / 2), 10), ((1 / 2), 14), ((1 / 2), 18), ((1 / 2), 22), ((-1 / 2), 26)],
      alternatingSixCyclotomicValue [((1 / 4), 2), ((-1 / 4), 10), ((-1 / 4), 18), ((-1 / 4), 22), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 2), 10), ((1 / 4), 14), ((-1 / 4), 26), ((-1 / 4), 30)]]
  ]

macro "close_cyclotomic_row03" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

private theorem row03_eigenbasisInverse_mul_row0
    (j : Fin 3) :
    (alternatingSixAmbientRow03EigenbasisInverse *
        alternatingSixAmbientRow03Eigenbasis) 0 j =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) 0 j := by
  rw [Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixAmbientRow03EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row03 (-(1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24)
  · simp [
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixAmbientRow03EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row03 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 16 - ((3 / 4) : ℂ) * ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 22 + ζ ^ 26)
  · simp [
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixAmbientRow03EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row03 (-((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 16 + ((3 / 4) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 22 - ζ ^ 26)
private theorem row03_eigenbasisInverse_mul_row1
    (j : Fin 3) :
    (alternatingSixAmbientRow03EigenbasisInverse *
        alternatingSixAmbientRow03Eigenbasis) 1 j =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) 1 j := by
  rw [Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixAmbientRow03EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row03 (-((1 / 4) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 22)
  · simp [
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixAmbientRow03EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row03 (-((1 / 2) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ((3 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 - ((3 / 4) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 8) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 14 - ((7 / 8) : ℂ) * ζ ^ 20 + ((5 / 8) : ℂ) * ζ ^ 24)
  · simp [
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixAmbientRow03EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row03 (((1 / 2) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 - ((3 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 + ((3 / 4) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 8) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 14 + ((7 / 8) : ℂ) * ζ ^ 20 - ((5 / 8) : ℂ) * ζ ^ 24)
private theorem row03_eigenbasisInverse_mul_row2
    (j : Fin 3) :
    (alternatingSixAmbientRow03EigenbasisInverse *
        alternatingSixAmbientRow03Eigenbasis) 2 j =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) 2 j := by
  rw [Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixAmbientRow03EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row03 (((1 / 4) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22)
  · simp [
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixAmbientRow03EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row03 (((1 / 2) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 2 - ((3 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 + ((3 / 4) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 8) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 14 + ((7 / 8) : ℂ) * ζ ^ 20 - ((5 / 8) : ℂ) * ζ ^ 24)
  · simp [
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixAmbientRow03EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row03 (-((1 / 2) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 2 + ((3 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 - ((3 / 4) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 8) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 14 - ((7 / 8) : ℂ) * ζ ^ 20 + ((5 / 8) : ℂ) * ζ ^ 24)
/-- The displayed inverse is a left inverse of the row 03 eigenbasis. -/
theorem alternatingSixAmbientRow03EigenbasisInverse_mul :
    alternatingSixAmbientRow03EigenbasisInverse *
        alternatingSixAmbientRow03Eigenbasis =
      1 := by
  ext i j
  fin_cases i
  · exact row03_eigenbasisInverse_mul_row0 j
  · exact row03_eigenbasisInverse_mul_row1 j
  · exact row03_eigenbasisInverse_mul_row2 j

/-- The displayed inverse is also a right inverse. -/
theorem alternatingSixAmbientRow03Eigenbasis_mul_inverse :
    alternatingSixAmbientRow03Eigenbasis *
        alternatingSixAmbientRow03EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow03EigenbasisInverse_mul

private theorem row03_generatorB_mul_eigenbasis_row0
    (j : Fin 3) :
    (alternatingSixFiveAmbient_row03_matrixB *
        alternatingSixAmbientRow03Eigenbasis) 0 j =
      (alternatingSixAmbientRow03Eigenbasis *
        Matrix.diagonal
          alternatingSixDegreeThreeGeneratorBEigenvalue) 0 j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixFiveAmbient_row03_matrixB,
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row03 0
  · simp [
      alternatingSixFiveAmbient_row03_matrixB,
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row03 (((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16 - ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ζ ^ 28)
  · simp [
      alternatingSixFiveAmbient_row03_matrixB,
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row03 (((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16 + ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ζ ^ 28)
private theorem row03_generatorB_mul_eigenbasis_row1
    (j : Fin 3) :
    (alternatingSixFiveAmbient_row03_matrixB *
        alternatingSixAmbientRow03Eigenbasis) 1 j =
      (alternatingSixAmbientRow03Eigenbasis *
        Matrix.diagonal
          alternatingSixDegreeThreeGeneratorBEigenvalue) 1 j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixFiveAmbient_row03_matrixB,
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row03 (-(1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24)
  · simp [
      alternatingSixFiveAmbient_row03_matrixB,
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row03 (((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((3 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((3 / 4) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 + ζ ^ 26)
  · simp [
      alternatingSixFiveAmbient_row03_matrixB,
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row03 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 + ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 + ((3 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 + ((3 / 4) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 - ζ ^ 26)
private theorem row03_generatorB_mul_eigenbasis_row2
    (j : Fin 3) :
    (alternatingSixFiveAmbient_row03_matrixB *
        alternatingSixAmbientRow03Eigenbasis) 2 j =
      (alternatingSixAmbientRow03Eigenbasis *
        Matrix.diagonal
          alternatingSixDegreeThreeGeneratorBEigenvalue) 2 j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixFiveAmbient_row03_matrixB,
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row03 (-(1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 16)
  · simp [
      alternatingSixFiveAmbient_row03_matrixB,
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row03 (ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 - ((5 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22)
  · simp [
      alternatingSixFiveAmbient_row03_matrixB,
      alternatingSixAmbientRow03Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row03 (-ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 + ((5 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 22)
/-- The checked row 03 basis diagonalizes the second generator. -/
theorem alternatingSixAmbientRow03GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row03_matrixB *
        alternatingSixAmbientRow03Eigenbasis =
      alternatingSixAmbientRow03Eigenbasis *
        Matrix.diagonal
          alternatingSixDegreeThreeGeneratorBEigenvalue := by
  ext i j
  fin_cases i
  · exact row03_generatorB_mul_eigenbasis_row0 j
  · exact row03_generatorB_mul_eigenbasis_row1 j
  · exact row03_generatorB_mul_eigenbasis_row2 j

/-- The row 03 first generator in the checked eigenbasis. -/
def alternatingSixAmbientRow03TransformedGeneratorA :
    Matrix (Fin 3) (Fin 3) ℂ :=
  alternatingSixAmbientRow03EigenbasisInverse *
    alternatingSixFiveAmbient_row03_matrixA *
    alternatingSixAmbientRow03Eigenbasis

/-- Rational polynomial for the row 03 connecting entry `01`. -/
def alternatingSixAmbientRow03Connecting01Polynomial : ℚ[X] :=
  Polynomial.C ((-1 / 4) : ℚ) + Polynomial.C ((1 / 4) : ℚ) * X ^ 2 + Polynomial.C ((-1 / 4) : ℚ) * X ^ 4 + Polynomial.C ((-1 / 4) : ℚ) * X ^ 10 + Polynomial.C ((1 / 4) : ℚ) * X ^ 16 + Polynomial.C ((-1 / 4) : ℚ) * X ^ 18 + Polynomial.C ((-1 / 4) : ℚ) * X ^ 22 + Polynomial.C ((1 / 2) : ℚ) * X ^ 30

/-- The row 03 connecting entry `01`. -/
def alternatingSixAmbientRow03Connecting01 : ℂ :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
    alternatingSixAmbientRow03Connecting01Polynomial

/-- Exact value of the transformed row 03 entry `01`. -/
theorem alternatingSixAmbientRow03TransformedGeneratorA_entry01 :
    alternatingSixAmbientRow03TransformedGeneratorA 0 1 =
      alternatingSixAmbientRow03Connecting01 := by
  unfold alternatingSixAmbientRow03TransformedGeneratorA
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow03Connecting01,
    alternatingSixAmbientRow03Connecting01Polynomial,
    alternatingSixAmbientRow03Eigenbasis,
    alternatingSixAmbientRow03EigenbasisInverse,
    alternatingSixFiveAmbient_row03_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_cyclotomic_row03 (((3 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 16 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 28 - ((5 / 4) : ℂ) * ζ ^ 30 + ((1 / 4) : ℂ) * ζ ^ 32 - ((3 / 2) : ℂ) * ζ ^ 34 + ((1 / 2) : ℂ) * ζ ^ 38 + ((1 / 4) : ℂ) * ζ ^ 40 + ((1 / 2) : ℂ) * ζ ^ 42 - ((1 / 4) : ℂ) * ζ ^ 44 + ((1 / 4) : ℂ) * ζ ^ 46 + ((1 / 2) : ℂ) * ζ ^ 50 - ((1 / 2) : ℂ) * ζ ^ 54)

/-- The transformed row 03 entry `01` is nonzero. -/
theorem alternatingSixAmbientRow03Connecting01_ne_zero :
    alternatingSixAmbientRow03Connecting01 ≠ 0 := by
  unfold alternatingSixAmbientRow03Connecting01
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientRow03Connecting01Polynomial] at hvalue
  · dsimp [alternatingSixAmbientRow03Connecting01Polynomial]
    compute_degree <;> norm_num

/-- Rational polynomial for the row 03 connecting entry `02`. -/
def alternatingSixAmbientRow03Connecting02Polynomial : ℚ[X] :=
  Polynomial.C ((-1 / 4) : ℚ) + Polynomial.C ((-1 / 4) : ℚ) * X ^ 2 + Polynomial.C ((-1 / 4) : ℚ) * X ^ 4 + Polynomial.C ((1 / 4) : ℚ) * X ^ 10 + Polynomial.C ((1 / 4) : ℚ) * X ^ 16 + Polynomial.C ((1 / 4) : ℚ) * X ^ 18 + Polynomial.C ((1 / 4) : ℚ) * X ^ 22 + Polynomial.C ((-1 / 2) : ℚ) * X ^ 30

/-- The row 03 connecting entry `02`. -/
def alternatingSixAmbientRow03Connecting02 : ℂ :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
    alternatingSixAmbientRow03Connecting02Polynomial

/-- Exact value of the transformed row 03 entry `02`. -/
theorem alternatingSixAmbientRow03TransformedGeneratorA_entry02 :
    alternatingSixAmbientRow03TransformedGeneratorA 0 2 =
      alternatingSixAmbientRow03Connecting02 := by
  unfold alternatingSixAmbientRow03TransformedGeneratorA
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow03Connecting02,
    alternatingSixAmbientRow03Connecting02Polynomial,
    alternatingSixAmbientRow03Eigenbasis,
    alternatingSixAmbientRow03EigenbasisInverse,
    alternatingSixFiveAmbient_row03_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_cyclotomic_row03 (((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 16 - ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 28 + ((5 / 4) : ℂ) * ζ ^ 30 + ((1 / 4) : ℂ) * ζ ^ 32 + ((3 / 2) : ℂ) * ζ ^ 34 - ((1 / 2) : ℂ) * ζ ^ 38 + ((1 / 4) : ℂ) * ζ ^ 40 - ((1 / 2) : ℂ) * ζ ^ 42 - ((1 / 4) : ℂ) * ζ ^ 44 - ((1 / 4) : ℂ) * ζ ^ 46 - ((1 / 2) : ℂ) * ζ ^ 50 + ((1 / 2) : ℂ) * ζ ^ 54)

/-- The transformed row 03 entry `02` is nonzero. -/
theorem alternatingSixAmbientRow03Connecting02_ne_zero :
    alternatingSixAmbientRow03Connecting02 ≠ 0 := by
  unfold alternatingSixAmbientRow03Connecting02
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientRow03Connecting02Polynomial] at hvalue
  · dsimp [alternatingSixAmbientRow03Connecting02Polynomial]
    compute_degree <;> norm_num

end InductiveMcKay
end McKayConjecture
