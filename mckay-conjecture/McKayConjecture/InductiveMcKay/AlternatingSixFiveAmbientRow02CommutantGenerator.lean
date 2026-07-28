/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixDegreeThreeEigenvalues
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientMatrixRelationsRow02
import McKayConjecture.InductiveMcKay.AlternatingSixFiveAmbientRow02CommutantBasis

/-!
# Generator data for the ambient row 02 commutant

This file verifies the small amount of exact cyclotomic linear algebra used
in the row 02 irreducibility proof.  In the explicit eigenbasis, the second
generator is diagonal with three distinct eigenvalues.  Two entries of the
first generator in that basis are nonzero, and hence connect all three
eigenspaces.
-/

noncomputable section

set_option linter.style.longLine false

open Polynomial

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The three eigenvalues of the row 02 second presentation generator. -/
def alternatingSixFiveAmbientRow02GeneratorBEigenvalue :
    Fin 3 → ℂ :=
  ![1, ζ ^ 30, -(ζ ^ 30)]

/-- Diagonal form of the row 02 second presentation generator. -/
def alternatingSixFiveAmbientRow02GeneratorBDiagonal :
    Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal
    alternatingSixFiveAmbientRow02GeneratorBEigenvalue

macro "close_cyclotomic" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

private theorem row02_generatorB_mul_eigenbasis_row0
    (j : Fin 3) :
    (alternatingSixFiveAmbient_row02_matrixB *
        alternatingSixFiveAmbientRow02Eigenbasis) 0 j =
      (alternatingSixFiveAmbientRow02Eigenbasis *
        alternatingSixFiveAmbientRow02GeneratorBDiagonal) 0 j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases j
  · simp [alternatingSixFiveAmbient_row02_matrixB,
    alternatingSixFiveAmbientRow02Eigenbasis,
    alternatingSixFiveAmbientRow02GeneratorBDiagonal,
    alternatingSixFiveAmbientRow02GeneratorBEigenvalue,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    close_cyclotomic
      (-(1 : ℂ) + (5 / 4 : ℂ) * ζ ^ 4 - (1 / 4 : ℂ) * ζ ^ 8 +
        (1 / 2 : ℂ) * ζ ^ 12 - (1 / 4 : ℂ) * ζ ^ 16)
  · simp [alternatingSixFiveAmbient_row02_matrixB,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixFiveAmbientRow02GeneratorBDiagonal,
      alternatingSixFiveAmbientRow02GeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    close_cyclotomic
      (-(3 / 2 : ℂ) + (1 / 4 : ℂ) * ζ ^ 2 +
        (5 / 4 : ℂ) * ζ ^ 4 - (1 / 4 : ℂ) * ζ ^ 6 -
        (1 / 4 : ℂ) * ζ ^ 8 + (7 / 4 : ℂ) * ζ ^ 10 -
        ζ ^ 14 + (1 / 4 : ℂ) * ζ ^ 16 +
        (1 / 2 : ℂ) * ζ ^ 18 - (1 / 4 : ℂ) * ζ ^ 22)
  · simp [alternatingSixFiveAmbient_row02_matrixB,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixFiveAmbientRow02GeneratorBDiagonal,
      alternatingSixFiveAmbientRow02GeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    close_cyclotomic
      (-(3 / 2 : ℂ) - (1 / 4 : ℂ) * ζ ^ 2 +
        (5 / 4 : ℂ) * ζ ^ 4 + (1 / 4 : ℂ) * ζ ^ 6 -
        (1 / 4 : ℂ) * ζ ^ 8 - (7 / 4 : ℂ) * ζ ^ 10 +
        ζ ^ 14 + (1 / 4 : ℂ) * ζ ^ 16 -
        (1 / 2 : ℂ) * ζ ^ 18 + (1 / 4 : ℂ) * ζ ^ 22)

private theorem row02_generatorB_mul_eigenbasis_row1
    (j : Fin 3) :
    (alternatingSixFiveAmbient_row02_matrixB *
        alternatingSixFiveAmbientRow02Eigenbasis) 1 j =
      (alternatingSixFiveAmbientRow02Eigenbasis *
        alternatingSixFiveAmbientRow02GeneratorBDiagonal) 1 j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases j
  · simp [alternatingSixFiveAmbient_row02_matrixB,
    alternatingSixFiveAmbientRow02Eigenbasis,
    alternatingSixFiveAmbientRow02GeneratorBDiagonal,
    alternatingSixFiveAmbientRow02GeneratorBEigenvalue,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    close_cyclotomic
      (-(3 / 4 : ℂ) * ζ ^ 4 + (1 / 2 : ℂ) * ζ ^ 8 -
        (1 / 2 : ℂ) * ζ ^ 12 + (1 / 2 : ℂ) * ζ ^ 16)
  · simp [alternatingSixFiveAmbient_row02_matrixB,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixFiveAmbientRow02GeneratorBDiagonal,
      alternatingSixFiveAmbientRow02GeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    close_cyclotomic
      ((1 : ℂ) - (1 / 4 : ℂ) * ζ ^ 2 -
        (3 / 4 : ℂ) * ζ ^ 4 - (3 / 4 : ℂ) * ζ ^ 10 +
        (1 / 2 : ℂ) * ζ ^ 12 + (1 / 2 : ℂ) * ζ ^ 14 -
        (1 / 2 : ℂ) * ζ ^ 16 + (1 / 2 : ℂ) * ζ ^ 18 +
        ζ ^ 20 - (1 / 2 : ℂ) * ζ ^ 24)
  · simp [alternatingSixFiveAmbient_row02_matrixB,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixFiveAmbientRow02GeneratorBDiagonal,
      alternatingSixFiveAmbientRow02GeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    close_cyclotomic
      ((1 : ℂ) + (1 / 4 : ℂ) * ζ ^ 2 -
        (3 / 4 : ℂ) * ζ ^ 4 + (3 / 4 : ℂ) * ζ ^ 10 +
        (1 / 2 : ℂ) * ζ ^ 12 - (1 / 2 : ℂ) * ζ ^ 14 -
        (1 / 2 : ℂ) * ζ ^ 16 - (1 / 2 : ℂ) * ζ ^ 18 +
        ζ ^ 20 - (1 / 2 : ℂ) * ζ ^ 24)

private theorem row02_generatorB_mul_eigenbasis_row2
    (j : Fin 3) :
    (alternatingSixFiveAmbient_row02_matrixB *
        alternatingSixFiveAmbientRow02Eigenbasis) 2 j =
      (alternatingSixFiveAmbientRow02Eigenbasis *
        alternatingSixFiveAmbientRow02GeneratorBDiagonal) 2 j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases j
  · simp [alternatingSixFiveAmbient_row02_matrixB,
    alternatingSixFiveAmbientRow02Eigenbasis,
    alternatingSixFiveAmbientRow02GeneratorBDiagonal,
    alternatingSixFiveAmbientRow02GeneratorBEigenvalue,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    close_cyclotomic
      (-(1 : ℂ) + ζ ^ 4 - ζ ^ 8)
  · simp [alternatingSixFiveAmbient_row02_matrixB,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixFiveAmbientRow02GeneratorBDiagonal,
      alternatingSixFiveAmbientRow02GeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    ring
  · simp [alternatingSixFiveAmbient_row02_matrixB,
      alternatingSixFiveAmbientRow02Eigenbasis,
      alternatingSixFiveAmbientRow02GeneratorBDiagonal,
      alternatingSixFiveAmbientRow02GeneratorBEigenvalue,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
    ring

/-- The explicit basis diagonalizes the row 02 second generator. -/
theorem alternatingSixFiveAmbientRow02GeneratorB_mul_eigenbasis :
    alternatingSixFiveAmbient_row02_matrixB *
        alternatingSixFiveAmbientRow02Eigenbasis =
      alternatingSixFiveAmbientRow02Eigenbasis *
        alternatingSixFiveAmbientRow02GeneratorBDiagonal := by
  ext i j
  fin_cases i
  · exact row02_generatorB_mul_eigenbasis_row0 j
  · exact row02_generatorB_mul_eigenbasis_row1 j
  · exact row02_generatorB_mul_eigenbasis_row2 j

/-- The row 02 first generator after conjugation to the checked eigenbasis. -/
def alternatingSixFiveAmbientRow02TransformedGeneratorA :
    Matrix (Fin 3) (Fin 3) ℂ :=
  alternatingSixFiveAmbientRow02EigenbasisInverse *
    alternatingSixFiveAmbient_row02_matrixA *
    alternatingSixFiveAmbientRow02Eigenbasis

/-- The `(0,1)` entry connecting the first two eigenspaces. -/
def alternatingSixFiveAmbientRow02TransformedGeneratorA01 : ℂ :=
  -(ζ ^ 30 + ζ ^ 26 - ζ ^ 14 - ζ ^ 10 + 1) / 2

/-- The `(0,2)` entry connecting the first and third eigenspaces. -/
def alternatingSixFiveAmbientRow02TransformedGeneratorA02 : ℂ :=
  (ζ ^ 30 + ζ ^ 26 - ζ ^ 14 - ζ ^ 10 - 1) / 2

/-- Exact value of the first connecting entry. -/
theorem alternatingSixFiveAmbientRow02TransformedGeneratorA_entry01 :
    alternatingSixFiveAmbientRow02TransformedGeneratorA 0 1 =
      alternatingSixFiveAmbientRow02TransformedGeneratorA01 := by
  unfold alternatingSixFiveAmbientRow02TransformedGeneratorA
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbientRow02TransformedGeneratorA01,
    alternatingSixFiveAmbientRow02EigenbasisInverse,
    alternatingSixFiveAmbient_row02_matrixA,
    alternatingSixFiveAmbientRow02Eigenbasis,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_cyclotomic
    ((3 / 8 : ℂ) + (5 / 16 : ℂ) * ζ ^ 2 +
      (1 / 16 : ℂ) * ζ ^ 4 - (1 / 8 : ℂ) * ζ ^ 6 -
      (3 / 8 : ℂ) * ζ ^ 8 - (9 / 16 : ℂ) * ζ ^ 10 +
      (1 / 4 : ℂ) * ζ ^ 12 - (1 / 2 : ℂ) * ζ ^ 14 -
      (3 / 4 : ℂ) * ζ ^ 16 - (3 / 4 : ℂ) * ζ ^ 20 -
      (15 / 16 : ℂ) * ζ ^ 22 + (1 / 16 : ℂ) * ζ ^ 24 +
      (5 / 4 : ℂ) * ζ ^ 26 + (1 / 2 : ℂ) * ζ ^ 28 +
      (7 / 16 : ℂ) * ζ ^ 30 + (1 / 4 : ℂ) * ζ ^ 32 +
      (1 / 4 : ℂ) * ζ ^ 34 + (1 / 4 : ℂ) * ζ ^ 36 -
      (1 / 8 : ℂ) * ζ ^ 38 - (1 / 16 : ℂ) * ζ ^ 42 -
      (3 / 16 : ℂ) * ζ ^ 44 - (3 / 8 : ℂ) * ζ ^ 46 +
      (3 / 16 : ℂ) * ζ ^ 50)

/-- Exact value of the second connecting entry. -/
theorem alternatingSixFiveAmbientRow02TransformedGeneratorA_entry02 :
    alternatingSixFiveAmbientRow02TransformedGeneratorA 0 2 =
      alternatingSixFiveAmbientRow02TransformedGeneratorA02 := by
  unfold alternatingSixFiveAmbientRow02TransformedGeneratorA
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbientRow02TransformedGeneratorA02,
    alternatingSixFiveAmbientRow02EigenbasisInverse,
    alternatingSixFiveAmbient_row02_matrixA,
    alternatingSixFiveAmbientRow02Eigenbasis,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_cyclotomic
    ((3 / 8 : ℂ) - (5 / 16 : ℂ) * ζ ^ 2 +
      (1 / 16 : ℂ) * ζ ^ 4 + (1 / 8 : ℂ) * ζ ^ 6 -
      (3 / 8 : ℂ) * ζ ^ 8 + (9 / 16 : ℂ) * ζ ^ 10 +
      (1 / 4 : ℂ) * ζ ^ 12 + (1 / 2 : ℂ) * ζ ^ 14 -
      (3 / 4 : ℂ) * ζ ^ 16 - (3 / 4 : ℂ) * ζ ^ 20 +
      (15 / 16 : ℂ) * ζ ^ 22 + (1 / 16 : ℂ) * ζ ^ 24 -
      (5 / 4 : ℂ) * ζ ^ 26 + (1 / 2 : ℂ) * ζ ^ 28 -
      (7 / 16 : ℂ) * ζ ^ 30 + (1 / 4 : ℂ) * ζ ^ 32 -
      (1 / 4 : ℂ) * ζ ^ 34 + (1 / 4 : ℂ) * ζ ^ 36 +
      (1 / 8 : ℂ) * ζ ^ 38 + (1 / 16 : ℂ) * ζ ^ 42 -
      (3 / 16 : ℂ) * ζ ^ 44 + (3 / 8 : ℂ) * ζ ^ 46 -
      (3 / 16 : ℂ) * ζ ^ 50)

private theorem row02_exact_connecting_plus_ne :
    (alternatingSixCyclotomicRoot ^ 30 +
        alternatingSixCyclotomicRoot ^ 26 -
        alternatingSixCyclotomicRoot ^ 14 -
        alternatingSixCyclotomicRoot ^ 10 + 1 :
      AlternatingSixCyclotomicField) ≠ 0 := by
  let p : ℚ[X] := X ^ 30 + X ^ 26 - X ^ 14 - X ^ 10 + 1
  have hp :
      AdjoinRoot.mk (Polynomial.cyclotomic 120 ℚ) p ≠ 0 := by
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt
      (Polynomial.cyclotomic.monic 120 ℚ)
    · intro hp0
      have hvalue :=
        congrArg (Polynomial.eval (2 : ℚ)) hp0
      norm_num [p] at hvalue
    · rw [Polynomial.natDegree_cyclotomic]
      have htotient : Nat.totient 120 = 32 := by decide
      rw [htotient]
      dsimp [p]
      compute_degree <;> norm_num
  rw [← AdjoinRoot.aeval_eq] at hp
  simpa only [p, map_add, map_sub, map_pow, map_one,
    aeval_X, alternatingSixCyclotomicRoot,
    AlternatingSixCyclotomicField] using hp

private theorem row02_exact_connecting_minus_ne :
    (alternatingSixCyclotomicRoot ^ 30 +
        alternatingSixCyclotomicRoot ^ 26 -
        alternatingSixCyclotomicRoot ^ 14 -
        alternatingSixCyclotomicRoot ^ 10 - 1 :
      AlternatingSixCyclotomicField) ≠ 0 := by
  let p : ℚ[X] := X ^ 30 + X ^ 26 - X ^ 14 - X ^ 10 - 1
  have hp :
      AdjoinRoot.mk (Polynomial.cyclotomic 120 ℚ) p ≠ 0 := by
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt
      (Polynomial.cyclotomic.monic 120 ℚ)
    · intro hp0
      have hvalue :=
        congrArg (Polynomial.eval (2 : ℚ)) hp0
      norm_num [p] at hvalue
    · rw [Polynomial.natDegree_cyclotomic]
      have htotient : Nat.totient 120 = 32 := by decide
      rw [htotient]
      dsimp [p]
      compute_degree <;> norm_num
  rw [← AdjoinRoot.aeval_eq] at hp
  simpa only [p, map_add, map_sub, map_pow, map_one,
    aeval_X, alternatingSixCyclotomicRoot,
    AlternatingSixCyclotomicField] using hp

private theorem row02_complex_connecting_plus_ne :
    ζ ^ 30 + ζ ^ 26 - ζ ^ 14 - ζ ^ 10 + 1 ≠ 0 := by
  have h :=
    alternatingSixCyclotomicEmbedding_injective.ne
      row02_exact_connecting_plus_ne
  simpa only [map_add, map_sub, map_pow, map_one, map_zero,
    alternatingSixCyclotomicEmbedding_root] using h

private theorem row02_complex_connecting_minus_ne :
    ζ ^ 30 + ζ ^ 26 - ζ ^ 14 - ζ ^ 10 - 1 ≠ 0 := by
  have h :=
    alternatingSixCyclotomicEmbedding_injective.ne
      row02_exact_connecting_minus_ne
  simpa only [map_add, map_sub, map_pow, map_one, map_zero,
    alternatingSixCyclotomicEmbedding_root] using h

/-- The first connecting entry is nonzero. -/
theorem alternatingSixFiveAmbientRow02TransformedGeneratorA01_ne_zero :
    alternatingSixFiveAmbientRow02TransformedGeneratorA01 ≠ 0 := by
  unfold alternatingSixFiveAmbientRow02TransformedGeneratorA01
  exact div_ne_zero
    (neg_ne_zero.mpr row02_complex_connecting_plus_ne)
    (by norm_num)

/-- The second connecting entry is nonzero. -/
theorem alternatingSixFiveAmbientRow02TransformedGeneratorA02_ne_zero :
    alternatingSixFiveAmbientRow02TransformedGeneratorA02 ≠ 0 := by
  unfold alternatingSixFiveAmbientRow02TransformedGeneratorA02
  exact div_ne_zero row02_complex_connecting_minus_ne (by norm_num)

end InductiveMcKay
end McKayConjecture
