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
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow05

/-!
# Checked commutant data for ambient row 05

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

/-- Eigenbasis for the row 05 second generator. -/
def alternatingSixAmbientRow05Eigenbasis :
    Matrix (Fin 3) (Fin 3) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((-1 / 2), 4), ((1 / 2), 8), ((1 / 2), 12), ((1 / 2), 16), ((-1 / 2), 20), ((-1 / 2), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 4), ((1 / 2), 8), ((1 / 2), 10), ((1 / 2), 12), ((1 / 2), 14), ((1 / 2), 16), ((1 / 2), 20), ((-1 / 2), 26), ((-1 / 2), 28)],
      alternatingSixCyclotomicValue [((-1 / 2), 4), ((1 / 2), 8), ((-1 / 2), 10), ((1 / 2), 12), ((-1 / 2), 14), ((1 / 2), 16), ((1 / 2), 20), ((1 / 2), 26), ((-1 / 2), 28)]],
    ![alternatingSixCyclotomicValue [(-1, 0), (1, 8), (1, 12), (1, 20), (-1, 28)],
      alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue []],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)]]
  ]

/-- Explicit inverse of the row 05 eigenbasis. -/
def alternatingSixAmbientRow05EigenbasisInverse :
    Matrix (Fin 3) (Fin 3) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [((1 / 2), 8), ((1 / 2), 12), ((-1 / 2), 20), ((-1 / 2), 28)],
      alternatingSixCyclotomicValue []],
    ![alternatingSixCyclotomicValue [((-1 / 2), 2), ((1 / 2), 10), ((1 / 2), 14), ((1 / 2), 18), ((1 / 2), 22), ((-1 / 2), 26), (-1, 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 2), ((-1 / 4), 8), ((1 / 4), 10), ((-1 / 4), 12), ((1 / 2), 14), ((1 / 4), 18), ((1 / 4), 20), ((1 / 4), 22), ((-1 / 2), 26), ((1 / 4), 28), ((-1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((1 / 2), 2), ((-1 / 2), 10), ((-1 / 2), 14), ((-1 / 2), 18), ((-1 / 2), 22), ((1 / 2), 26), ((1 / 2), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 2), 2), ((-1 / 2), 10), ((-1 / 2), 14), ((-1 / 2), 18), ((-1 / 2), 22), ((1 / 2), 26), (1, 30)],
      alternatingSixCyclotomicValue [((1 / 4), 2), ((-1 / 4), 8), ((-1 / 4), 10), ((-1 / 4), 12), ((-1 / 2), 14), ((-1 / 4), 18), ((1 / 4), 20), ((-1 / 4), 22), ((1 / 2), 26), ((1 / 4), 28), ((1 / 4), 30)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 2), 2), ((1 / 2), 10), ((1 / 2), 14), ((1 / 2), 18), ((1 / 2), 22), ((-1 / 2), 26), ((-1 / 2), 30)]]
  ]

macro "close_cyclotomic_row05" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

private theorem row05_eigenbasisInverse_mul_row0
    (j : Fin 3) :
    (alternatingSixAmbientRow05EigenbasisInverse *
        alternatingSixAmbientRow05Eigenbasis) 0 j =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) 0 j := by
  rw [Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixAmbientRow05EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row05 (-(1 : ℂ) + ζ ^ 4 - ((3 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24)
  · simp [
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixAmbientRow05EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row05 0
  · simp [
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixAmbientRow05EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row05 0
private theorem row05_eigenbasisInverse_mul_row1
    (j : Fin 3) :
    (alternatingSixAmbientRow05EigenbasisInverse *
        alternatingSixAmbientRow05Eigenbasis) 1 j =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) 1 j := by
  rw [Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixAmbientRow05EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row05 (((1 / 2) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 6 + ((3 / 4) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 16 - ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 + ((3 / 4) : ℂ) * ζ ^ 26)
  · simp [
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixAmbientRow05EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row05 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)
  · simp [
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixAmbientRow05EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row05 (((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)
private theorem row05_eigenbasisInverse_mul_row2
    (j : Fin 3) :
    (alternatingSixAmbientRow05EigenbasisInverse *
        alternatingSixAmbientRow05Eigenbasis) 2 j =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) 2 j := by
  rw [Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixAmbientRow05EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row05 (((1 / 2) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 6 + ((3 / 4) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 16 + ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24 - ((3 / 4) : ℂ) * ζ ^ 26)
  · simp [
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixAmbientRow05EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row05 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 26)
  · simp [
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixAmbientRow05EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row05 (-((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 26)
/-- The displayed inverse is a left inverse of the row 05 eigenbasis. -/
theorem alternatingSixAmbientRow05EigenbasisInverse_mul :
    alternatingSixAmbientRow05EigenbasisInverse *
        alternatingSixAmbientRow05Eigenbasis =
      1 := by
  ext i j
  fin_cases i
  · exact row05_eigenbasisInverse_mul_row0 j
  · exact row05_eigenbasisInverse_mul_row1 j
  · exact row05_eigenbasisInverse_mul_row2 j

/-- The displayed inverse is also a right inverse. -/
theorem alternatingSixAmbientRow05Eigenbasis_mul_inverse :
    alternatingSixAmbientRow05Eigenbasis *
        alternatingSixAmbientRow05EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow05EigenbasisInverse_mul

private theorem row05_generatorB_mul_eigenbasis_row0
    (j : Fin 3) :
    (alternatingSixFiveAmbient_row05_matrixB *
        alternatingSixAmbientRow05Eigenbasis) 0 j =
      (alternatingSixAmbientRow05Eigenbasis *
        Matrix.diagonal
          alternatingSixDegreeThreeGeneratorBEigenvalue) 0 j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixFiveAmbient_row05_matrixB,
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row05 ((1 : ℂ) - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 16)
  · simp [
      alternatingSixFiveAmbient_row05_matrixB,
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row05 (((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)
  · simp [
      alternatingSixFiveAmbient_row05_matrixB,
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row05 (((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 26)
private theorem row05_generatorB_mul_eigenbasis_row1
    (j : Fin 3) :
    (alternatingSixFiveAmbient_row05_matrixB *
        alternatingSixAmbientRow05Eigenbasis) 1 j =
      (alternatingSixAmbientRow05Eigenbasis *
        Matrix.diagonal
          alternatingSixDegreeThreeGeneratorBEigenvalue) 1 j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixFiveAmbient_row05_matrixB,
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row05 0
  · simp [
      alternatingSixFiveAmbient_row05_matrixB,
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row05 0
  · simp [
      alternatingSixFiveAmbient_row05_matrixB,
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row05 0
private theorem row05_generatorB_mul_eigenbasis_row2
    (j : Fin 3) :
    (alternatingSixFiveAmbient_row05_matrixB *
        alternatingSixAmbientRow05Eigenbasis) 2 j =
      (alternatingSixAmbientRow05Eigenbasis *
        Matrix.diagonal
          alternatingSixDegreeThreeGeneratorBEigenvalue) 2 j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixFiveAmbient_row05_matrixB,
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row05 ((1 : ℂ) + ζ ^ 4 - ((5 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 16 - ζ ^ 20 + ζ ^ 24)
  · simp [
      alternatingSixFiveAmbient_row05_matrixB,
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row05 ((1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16)
  · simp [
      alternatingSixFiveAmbient_row05_matrixB,
      alternatingSixAmbientRow05Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row05 ((1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16)
/-- The checked row 05 basis diagonalizes the second generator. -/
theorem alternatingSixAmbientRow05GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row05_matrixB *
        alternatingSixAmbientRow05Eigenbasis =
      alternatingSixAmbientRow05Eigenbasis *
        Matrix.diagonal
          alternatingSixDegreeThreeGeneratorBEigenvalue := by
  ext i j
  fin_cases i
  · exact row05_generatorB_mul_eigenbasis_row0 j
  · exact row05_generatorB_mul_eigenbasis_row1 j
  · exact row05_generatorB_mul_eigenbasis_row2 j

/-- The row 05 first generator in the checked eigenbasis. -/
def alternatingSixAmbientRow05TransformedGeneratorA :
    Matrix (Fin 3) (Fin 3) ℂ :=
  alternatingSixAmbientRow05EigenbasisInverse *
    alternatingSixFiveAmbient_row05_matrixA *
    alternatingSixAmbientRow05Eigenbasis

/-- Rational polynomial for the row 05 connecting entry `01`. -/
def alternatingSixAmbientRow05Connecting01Polynomial : ℚ[X] :=
  Polynomial.C ((-1 / 2) : ℚ) + Polynomial.C ((1 / 2) : ℚ) * X ^ 8 + Polynomial.C ((-1 / 2) : ℚ) * X ^ 10 + Polynomial.C ((1 / 2) : ℚ) * X ^ 12 + Polynomial.C ((-1 / 2) : ℚ) * X ^ 28

/-- The row 05 connecting entry `01`. -/
def alternatingSixAmbientRow05Connecting01 : ℂ :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
    alternatingSixAmbientRow05Connecting01Polynomial

/-- Exact value of the transformed row 05 entry `01`. -/
theorem alternatingSixAmbientRow05TransformedGeneratorA_entry01 :
    alternatingSixAmbientRow05TransformedGeneratorA 0 1 =
      alternatingSixAmbientRow05Connecting01 := by
  unfold alternatingSixAmbientRow05TransformedGeneratorA
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow05Connecting01,
    alternatingSixAmbientRow05Connecting01Polynomial,
    alternatingSixAmbientRow05Eigenbasis,
    alternatingSixAmbientRow05EigenbasisInverse,
    alternatingSixFiveAmbient_row05_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_cyclotomic_row05 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30 + ((1 / 4) : ℂ) * ζ ^ 32 - ((1 / 2) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 36 + ((1 / 4) : ℂ) * ζ ^ 38 + ((1 / 4) : ℂ) * ζ ^ 40 - ((1 / 4) : ℂ) * ζ ^ 42 - ((1 / 4) : ℂ) * ζ ^ 44)

/-- The transformed row 05 entry `01` is nonzero. -/
theorem alternatingSixAmbientRow05Connecting01_ne_zero :
    alternatingSixAmbientRow05Connecting01 ≠ 0 := by
  unfold alternatingSixAmbientRow05Connecting01
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientRow05Connecting01Polynomial] at hvalue
  · dsimp [alternatingSixAmbientRow05Connecting01Polynomial]
    compute_degree <;> norm_num

/-- Rational polynomial for the row 05 connecting entry `02`. -/
def alternatingSixAmbientRow05Connecting02Polynomial : ℚ[X] :=
  Polynomial.C ((-1 / 2) : ℚ) + Polynomial.C ((1 / 2) : ℚ) * X ^ 8 + Polynomial.C ((1 / 2) : ℚ) * X ^ 10 + Polynomial.C ((1 / 2) : ℚ) * X ^ 12 + Polynomial.C ((-1 / 2) : ℚ) * X ^ 28

/-- The row 05 connecting entry `02`. -/
def alternatingSixAmbientRow05Connecting02 : ℂ :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
    alternatingSixAmbientRow05Connecting02Polynomial

/-- Exact value of the transformed row 05 entry `02`. -/
theorem alternatingSixAmbientRow05TransformedGeneratorA_entry02 :
    alternatingSixAmbientRow05TransformedGeneratorA 0 2 =
      alternatingSixAmbientRow05Connecting02 := by
  unfold alternatingSixAmbientRow05TransformedGeneratorA
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow05Connecting02,
    alternatingSixAmbientRow05Connecting02Polynomial,
    alternatingSixAmbientRow05Eigenbasis,
    alternatingSixAmbientRow05EigenbasisInverse,
    alternatingSixFiveAmbient_row05_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_cyclotomic_row05 (((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30 + ((1 / 4) : ℂ) * ζ ^ 32 + ((1 / 2) : ℂ) * ζ ^ 34 - ((1 / 4) : ℂ) * ζ ^ 36 - ((1 / 4) : ℂ) * ζ ^ 38 + ((1 / 4) : ℂ) * ζ ^ 40 + ((1 / 4) : ℂ) * ζ ^ 42 - ((1 / 4) : ℂ) * ζ ^ 44)

/-- The transformed row 05 entry `02` is nonzero. -/
theorem alternatingSixAmbientRow05Connecting02_ne_zero :
    alternatingSixAmbientRow05Connecting02 ≠ 0 := by
  unfold alternatingSixAmbientRow05Connecting02
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientRow05Connecting02Polynomial] at hvalue
  · dsimp [alternatingSixAmbientRow05Connecting02Polynomial]
    compute_degree <;> norm_num

end InductiveMcKay
end McKayConjecture
