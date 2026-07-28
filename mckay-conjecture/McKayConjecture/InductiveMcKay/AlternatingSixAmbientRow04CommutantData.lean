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
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow04

/-!
# Checked commutant data for ambient row 04

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

/-- Eigenbasis for the row 04 second generator. -/
def alternatingSixAmbientRow04Eigenbasis :
    Matrix (Fin 3) (Fin 3) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [],
      alternatingSixCyclotomicValue [(1, 2), (-1, 8), (1, 10), (-1, 12), (-1, 18), (1, 20), (-1, 22), (1, 28), (1, 30)],
      alternatingSixCyclotomicValue [(-1, 2), (-1, 8), (-1, 10), (-1, 12), (1, 18), (1, 20), (1, 22), (1, 28), (-1, 30)]],
    ![alternatingSixCyclotomicValue [(1, 0), (1, 8), (1, 12), (-1, 20), (-1, 28)],
      alternatingSixCyclotomicValue [(-1, 0), (1, 8), (-1, 10), (1, 12), (-1, 28), (1, 30)],
      alternatingSixCyclotomicValue [(-1, 0), (1, 8), (1, 10), (1, 12), (-1, 28), (-1, 30)]],
    ![alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)],
      alternatingSixCyclotomicValue [(1, 0)]]
  ]

/-- Explicit inverse of the row 04 eigenbasis. -/
def alternatingSixAmbientRow04EigenbasisInverse :
    Matrix (Fin 3) (Fin 3) ℂ :=
  ![
    ![alternatingSixCyclotomicValue [((-1 / 4), 4), ((1 / 4), 8), ((1 / 4), 12), ((1 / 4), 16), ((-1 / 4), 28)],
      alternatingSixCyclotomicValue [((1 / 2), 0), ((-1 / 4), 8), ((-1 / 4), 12), ((1 / 4), 20), ((1 / 4), 28)],
      alternatingSixCyclotomicValue [(1, 0), ((1 / 2), 4), ((-1 / 2), 8), ((-1 / 2), 12), ((-1 / 2), 16), ((1 / 2), 28)]],
    ![alternatingSixCyclotomicValue [((-1 / 4), 2), ((1 / 8), 4), ((-1 / 8), 8), ((1 / 4), 10), ((-1 / 8), 12), ((1 / 8), 14), ((-1 / 8), 16), ((1 / 4), 18), ((1 / 4), 22), ((-1 / 8), 26), ((1 / 8), 28), ((-3 / 8), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((1 / 8), 2), ((1 / 8), 8), ((-1 / 8), 10), ((1 / 8), 12), ((-1 / 4), 14), ((-1 / 8), 18), ((-1 / 8), 20), ((-1 / 8), 22), ((1 / 4), 26), ((-1 / 8), 28), ((1 / 8), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 4), ((1 / 4), 8), ((1 / 2), 10), ((1 / 4), 12), ((1 / 4), 14), ((1 / 4), 16), ((-1 / 4), 26), ((-1 / 4), 28), ((-1 / 4), 30)]],
    ![alternatingSixCyclotomicValue [((1 / 4), 2), ((1 / 8), 4), ((-1 / 8), 8), ((-1 / 4), 10), ((-1 / 8), 12), ((-1 / 8), 14), ((-1 / 8), 16), ((-1 / 4), 18), ((-1 / 4), 22), ((1 / 8), 26), ((1 / 8), 28), ((3 / 8), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 0), ((-1 / 8), 2), ((1 / 8), 8), ((1 / 8), 10), ((1 / 8), 12), ((1 / 4), 14), ((1 / 8), 18), ((-1 / 8), 20), ((1 / 8), 22), ((-1 / 4), 26), ((-1 / 8), 28), ((-1 / 8), 30)],
      alternatingSixCyclotomicValue [((-1 / 4), 4), ((1 / 4), 8), ((-1 / 2), 10), ((1 / 4), 12), ((-1 / 4), 14), ((1 / 4), 16), ((1 / 4), 26), ((-1 / 4), 28), ((1 / 4), 30)]]
  ]

macro "close_cyclotomic_row04" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

private theorem row04_eigenbasisInverse_mul_row0
    (j : Fin 3) :
    (alternatingSixAmbientRow04EigenbasisInverse *
        alternatingSixAmbientRow04Eigenbasis) 0 j =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) 0 j := by
  rw [Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixAmbientRow04EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row04 (((1 / 2) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 - ((3 / 4) : ℂ) * ζ ^ 16 + ((1 / 4) : ℂ) * ζ ^ 20 - ((1 / 4) : ℂ) * ζ ^ 24)
  · simp [
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixAmbientRow04EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row04 (((1 / 2) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 12 - ζ ^ 16 + ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24)
  · simp [
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixAmbientRow04EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row04 (((1 / 2) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 12 - ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24)
private theorem row04_eigenbasisInverse_mul_row1
    (j : Fin 3) :
    (alternatingSixAmbientRow04EigenbasisInverse *
        alternatingSixAmbientRow04Eigenbasis) 1 j =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) 1 j := by
  rw [Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixAmbientRow04EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row04 (-((1 / 4) : ℂ) + ((1 / 8) : ℂ) * ζ ^ 2 - ((1 / 8) : ℂ) * ζ ^ 6 + ((1 / 8) : ℂ) * ζ ^ 8 + ((5 / 8) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 12 - ((3 / 8) : ℂ) * ζ ^ 14 + ((3 / 8) : ℂ) * ζ ^ 16 + ((1 / 8) : ℂ) * ζ ^ 18 - ((1 / 8) : ℂ) * ζ ^ 20 - ((1 / 8) : ℂ) * ζ ^ 22 + ((1 / 8) : ℂ) * ζ ^ 24 - ((1 / 8) : ℂ) * ζ ^ 26)
  · simp [
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixAmbientRow04EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row04 (-((3 / 4) : ℂ) - ((1 / 8) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 - ((3 / 8) : ℂ) * ζ ^ 8 + ((7 / 8) : ℂ) * ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 12 - ((1 / 8) : ℂ) * ζ ^ 14 + ((3 / 4) : ℂ) * ζ ^ 16 - ((3 / 8) : ℂ) * ζ ^ 18 - ((1 / 8) : ℂ) * ζ ^ 20 + ((1 / 8) : ℂ) * ζ ^ 22 + ((5 / 8) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 28)
  · simp [
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixAmbientRow04EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row04 (((1 / 4) : ℂ) - ((1 / 8) : ℂ) * ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 8) : ℂ) * ζ ^ 8 + ((7 / 8) : ℂ) * ζ ^ 10 - ((1 / 8) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 16 + ((1 / 8) : ℂ) * ζ ^ 18 - ((3 / 8) : ℂ) * ζ ^ 20 + ((1 / 8) : ℂ) * ζ ^ 22 - ((1 / 8) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 28)
private theorem row04_eigenbasisInverse_mul_row2
    (j : Fin 3) :
    (alternatingSixAmbientRow04EigenbasisInverse *
        alternatingSixAmbientRow04Eigenbasis) 2 j =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) 2 j := by
  rw [Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixAmbientRow04EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row04 (-((1 / 4) : ℂ) - ((1 / 8) : ℂ) * ζ ^ 2 + ((1 / 8) : ℂ) * ζ ^ 6 + ((1 / 8) : ℂ) * ζ ^ 8 - ((5 / 8) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 12 + ((3 / 8) : ℂ) * ζ ^ 14 + ((3 / 8) : ℂ) * ζ ^ 16 - ((1 / 8) : ℂ) * ζ ^ 18 - ((1 / 8) : ℂ) * ζ ^ 20 + ((1 / 8) : ℂ) * ζ ^ 22 + ((1 / 8) : ℂ) * ζ ^ 24 + ((1 / 8) : ℂ) * ζ ^ 26)
  · simp [
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixAmbientRow04EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row04 (((1 / 4) : ℂ) + ((1 / 8) : ℂ) * ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 4 + ((1 / 8) : ℂ) * ζ ^ 8 - ((7 / 8) : ℂ) * ζ ^ 10 + ((1 / 8) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 16 - ((1 / 8) : ℂ) * ζ ^ 18 - ((3 / 8) : ℂ) * ζ ^ 20 - ((1 / 8) : ℂ) * ζ ^ 22 - ((1 / 8) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 4) : ℂ) * ζ ^ 28)
  · simp [
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixAmbientRow04EigenbasisInverse,
      alternatingSixCyclotomicValue, Matrix.one_apply,
      Fin.sum_univ_succ]
    try close_cyclotomic_row04 (-((3 / 4) : ℂ) + ((1 / 8) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 - ((3 / 8) : ℂ) * ζ ^ 8 - ((7 / 8) : ℂ) * ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 12 + ((1 / 8) : ℂ) * ζ ^ 14 + ((3 / 4) : ℂ) * ζ ^ 16 + ((3 / 8) : ℂ) * ζ ^ 18 - ((1 / 8) : ℂ) * ζ ^ 20 - ((1 / 8) : ℂ) * ζ ^ 22 + ((5 / 8) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 28)
/-- The displayed inverse is a left inverse of the row 04 eigenbasis. -/
theorem alternatingSixAmbientRow04EigenbasisInverse_mul :
    alternatingSixAmbientRow04EigenbasisInverse *
        alternatingSixAmbientRow04Eigenbasis =
      1 := by
  ext i j
  fin_cases i
  · exact row04_eigenbasisInverse_mul_row0 j
  · exact row04_eigenbasisInverse_mul_row1 j
  · exact row04_eigenbasisInverse_mul_row2 j

/-- The displayed inverse is also a right inverse. -/
theorem alternatingSixAmbientRow04Eigenbasis_mul_inverse :
    alternatingSixAmbientRow04Eigenbasis *
        alternatingSixAmbientRow04EigenbasisInverse =
      1 :=
  mul_eq_one_comm.mp
    alternatingSixAmbientRow04EigenbasisInverse_mul

private theorem row04_generatorB_mul_eigenbasis_row0
    (j : Fin 3) :
    (alternatingSixFiveAmbient_row04_matrixB *
        alternatingSixAmbientRow04Eigenbasis) 0 j =
      (alternatingSixAmbientRow04Eigenbasis *
        Matrix.diagonal
          alternatingSixDegreeThreeGeneratorBEigenvalue) 0 j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixFiveAmbient_row04_matrixB,
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row04 ((1 : ℂ) - ((1 / 2) : ℂ) * ζ ^ 8 + ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 16 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24)
  · simp [
      alternatingSixFiveAmbient_row04_matrixB,
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row04 (-(1 : ℂ) + ζ ^ 2 + (2 : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 6 - ((5 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 + ζ ^ 14 - ζ ^ 16 - (2 : ℂ) * ζ ^ 18 + ζ ^ 24 - ζ ^ 28)
  · simp [
      alternatingSixFiveAmbient_row04_matrixB,
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row04 (-(1 : ℂ) - ζ ^ 2 + (2 : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 6 - ((5 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 - ζ ^ 14 - ζ ^ 16 + (2 : ℂ) * ζ ^ 18 + ζ ^ 24 - ζ ^ 28)
private theorem row04_generatorB_mul_eigenbasis_row1
    (j : Fin 3) :
    (alternatingSixFiveAmbient_row04_matrixB *
        alternatingSixAmbientRow04Eigenbasis) 1 j =
      (alternatingSixAmbientRow04Eigenbasis *
        Matrix.diagonal
          alternatingSixDegreeThreeGeneratorBEigenvalue) 1 j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixFiveAmbient_row04_matrixB,
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row04 (-((1 / 2) : ℂ) * ζ ^ 4 - ζ ^ 12 + ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24)
  · simp [
      alternatingSixFiveAmbient_row04_matrixB,
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row04 ((1 : ℂ) - ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 6 + ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ζ ^ 16 + ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 26 - ζ ^ 28)
  · simp [
      alternatingSixFiveAmbient_row04_matrixB,
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row04 ((1 : ℂ) + ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 6 + ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ζ ^ 16 - ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26 - ζ ^ 28)
private theorem row04_generatorB_mul_eigenbasis_row2
    (j : Fin 3) :
    (alternatingSixFiveAmbient_row04_matrixB *
        alternatingSixAmbientRow04Eigenbasis) 2 j =
      (alternatingSixAmbientRow04Eigenbasis *
        Matrix.diagonal
          alternatingSixDegreeThreeGeneratorBEigenvalue) 2 j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases j
  · simp [
      alternatingSixFiveAmbient_row04_matrixB,
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row04 (((1 / 2) : ℂ) * ζ ^ 4 + ζ ^ 12 - ζ ^ 16 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24)
  · simp [
      alternatingSixFiveAmbient_row04_matrixB,
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row04 (-(1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 6 + ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)
  · simp [
      alternatingSixFiveAmbient_row04_matrixB,
      alternatingSixAmbientRow04Eigenbasis,
      alternatingSixDegreeThreeGeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    try close_cyclotomic_row04 (-(1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 6 + ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 26)
/-- The checked row 04 basis diagonalizes the second generator. -/
theorem alternatingSixAmbientRow04GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row04_matrixB *
        alternatingSixAmbientRow04Eigenbasis =
      alternatingSixAmbientRow04Eigenbasis *
        Matrix.diagonal
          alternatingSixDegreeThreeGeneratorBEigenvalue := by
  ext i j
  fin_cases i
  · exact row04_generatorB_mul_eigenbasis_row0 j
  · exact row04_generatorB_mul_eigenbasis_row1 j
  · exact row04_generatorB_mul_eigenbasis_row2 j

/-- The row 04 first generator in the checked eigenbasis. -/
def alternatingSixAmbientRow04TransformedGeneratorA :
    Matrix (Fin 3) (Fin 3) ℂ :=
  alternatingSixAmbientRow04EigenbasisInverse *
    alternatingSixFiveAmbient_row04_matrixA *
    alternatingSixAmbientRow04Eigenbasis

/-- Rational polynomial for the row 04 connecting entry `01`. -/
def alternatingSixAmbientRow04Connecting01Polynomial : ℚ[X] :=
  Polynomial.C ((-1 / 2) : ℚ) * X ^ 14 + Polynomial.C ((1 / 2) : ℚ) * X ^ 26

/-- The row 04 connecting entry `01`. -/
def alternatingSixAmbientRow04Connecting01 : ℂ :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
    alternatingSixAmbientRow04Connecting01Polynomial

/-- Exact value of the transformed row 04 entry `01`. -/
theorem alternatingSixAmbientRow04TransformedGeneratorA_entry01 :
    alternatingSixAmbientRow04TransformedGeneratorA 0 1 =
      alternatingSixAmbientRow04Connecting01 := by
  unfold alternatingSixAmbientRow04TransformedGeneratorA
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow04Connecting01,
    alternatingSixAmbientRow04Connecting01Polynomial,
    alternatingSixAmbientRow04Eigenbasis,
    alternatingSixAmbientRow04EigenbasisInverse,
    alternatingSixFiveAmbient_row04_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_cyclotomic_row04 (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((3 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 - ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 12 + ((5 / 4) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 16 - (2 : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 20 - ζ ^ 22 + ((3 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 26 + ((5 / 4) : ℂ) * ζ ^ 30 + ζ ^ 32 + ((3 / 4) : ℂ) * ζ ^ 34 - ((7 / 4) : ℂ) * ζ ^ 36 + ((1 / 4) : ℂ) * ζ ^ 38 + ((1 / 4) : ℂ) * ζ ^ 40 - ((1 / 4) : ℂ) * ζ ^ 44 - ((3 / 4) : ℂ) * ζ ^ 46 - ((1 / 4) : ℂ) * ζ ^ 48 - ((1 / 4) : ℂ) * ζ ^ 50 + ((1 / 4) : ℂ) * ζ ^ 52 + ((1 / 4) : ℂ) * ζ ^ 54)

/-- The transformed row 04 entry `01` is nonzero. -/
theorem alternatingSixAmbientRow04Connecting01_ne_zero :
    alternatingSixAmbientRow04Connecting01 ≠ 0 := by
  unfold alternatingSixAmbientRow04Connecting01
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientRow04Connecting01Polynomial] at hvalue
  · dsimp [alternatingSixAmbientRow04Connecting01Polynomial]
    compute_degree <;> norm_num

/-- Rational polynomial for the row 04 connecting entry `02`. -/
def alternatingSixAmbientRow04Connecting02Polynomial : ℚ[X] :=
  Polynomial.C ((1 / 2) : ℚ) * X ^ 14 + Polynomial.C ((-1 / 2) : ℚ) * X ^ 26

/-- The row 04 connecting entry `02`. -/
def alternatingSixAmbientRow04Connecting02 : ℂ :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
    alternatingSixAmbientRow04Connecting02Polynomial

/-- Exact value of the transformed row 04 entry `02`. -/
theorem alternatingSixAmbientRow04TransformedGeneratorA_entry02 :
    alternatingSixAmbientRow04TransformedGeneratorA 0 2 =
      alternatingSixAmbientRow04Connecting02 := by
  unfold alternatingSixAmbientRow04TransformedGeneratorA
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixAmbientRow04Connecting02,
    alternatingSixAmbientRow04Connecting02Polynomial,
    alternatingSixAmbientRow04Eigenbasis,
    alternatingSixAmbientRow04EigenbasisInverse,
    alternatingSixFiveAmbient_row04_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_cyclotomic_row04 (-((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((3 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 + ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 12 - ((5 / 4) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 16 + (2 : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 20 + ζ ^ 22 + ((3 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 26 - ((5 / 4) : ℂ) * ζ ^ 30 + ζ ^ 32 - ((3 / 4) : ℂ) * ζ ^ 34 - ((7 / 4) : ℂ) * ζ ^ 36 - ((1 / 4) : ℂ) * ζ ^ 38 + ((1 / 4) : ℂ) * ζ ^ 40 - ((1 / 4) : ℂ) * ζ ^ 44 + ((3 / 4) : ℂ) * ζ ^ 46 - ((1 / 4) : ℂ) * ζ ^ 48 + ((1 / 4) : ℂ) * ζ ^ 50 + ((1 / 4) : ℂ) * ζ ^ 52 - ((1 / 4) : ℂ) * ζ ^ 54)

/-- The transformed row 04 entry `02` is nonzero. -/
theorem alternatingSixAmbientRow04Connecting02_ne_zero :
    alternatingSixAmbientRow04Connecting02 ≠ 0 := by
  unfold alternatingSixAmbientRow04Connecting02
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientRow04Connecting02Polynomial] at hvalue
  · dsimp [alternatingSixAmbientRow04Connecting02Polynomial]
    compute_degree <;> norm_num

end InductiveMcKay
end McKayConjecture
