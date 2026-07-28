/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DiagonalBasisMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow14DiagonalData

/-!
# Scalar common commutant for ambient row 14

The second generator is diagonal in the checked basis.  Its repeated
eigenspaces leave only 10 possible matrix
coordinates, and the generated exact row reduction for the transformed first
generator reduces those coordinates to a single scalar.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Entries between distinct second-generator eigenspaces vanish in its
commutant. -/
private theorem alternatingSixAmbientRow14_off_block
    (Y : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow14GeneratorBDiagonal =
        alternatingSixAmbientRow14GeneratorBDiagonal * Y)
    (i j : Fin 6)
    (different :
      alternatingSixAmbientRow14EigenvalueLabel i ≠
        alternatingSixAmbientRow14EigenvalueLabel j) :
    Y i j = 0 := by
  apply Matrix.entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
    Y alternatingSixAmbientRow14GeneratorBEigenvalue
  · exact commutesDiagonal
  · intro equalEigenvalues
    apply different
    apply alternatingSixOrderEightOddEigenvalue_injective
    simpa [
      alternatingSixAmbientRow14GeneratorBEigenvalue] using
      equalEigenvalues.symm

private theorem row14_reducedY00
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow14TransformedGeneratorA =
        alternatingSixAmbientRow14TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow14GeneratorBDiagonal =
        alternatingSixAmbientRow14GeneratorBDiagonal * Y) :
    Y 0 0 = Y 5 5 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 5 (by decide)

  have commutesA05 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA05
  simp only [Fin.sum_univ_succ] at commutesA05
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA05
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY15,
      hY25,
      hY35,
      hY45] at commutesA05

  linear_combination
    ((-(2 : ℂ) - (2 : ℂ) * ζ ^ 3 - (2 : ℂ) * ζ ^ 7 - (2 : ℂ) * ζ ^ 10 + (2 : ℂ) * ζ ^ 19 + (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 23 + (2 : ℂ) * ζ ^ 25 - (2 : ℂ) * ζ ^ 31)) * commutesA05
      - (
        ((-(1 : ℂ) - ((1 / 2) : ℂ) * ζ ^ 3 + ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 6 - ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 23 + ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 25 + ((1 / 2) : ℂ) * ζ ^ 26 - ((1 / 2) : ℂ) * ζ ^ 29 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 0
        + (((1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 3 - ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 6 + ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 25 - ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 29 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row14_reducedY11
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow14TransformedGeneratorA =
        alternatingSixAmbientRow14TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow14GeneratorBDiagonal =
        alternatingSixAmbientRow14GeneratorBDiagonal * Y) :
    Y 1 1 = Y 5 5 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 1 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51] at commutesA01
  have commutesA05 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA05
  simp only [Fin.sum_univ_succ] at commutesA05
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA05
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51] at commutesA05
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51] at commutesA11

  linear_combination
    ((-(24 : ℂ) - (14 : ℂ) * ζ ^ 3 - (26 : ℂ) * ζ ^ 5 - (14 : ℂ) * ζ ^ 7 - (24 : ℂ) * ζ ^ 10 - (12 : ℂ) * ζ ^ 15 + (14 : ℂ) * ζ ^ 19 - (4 : ℂ) * ζ ^ 20 + (14 : ℂ) * ζ ^ 23 + (6 : ℂ) * ζ ^ 30 - (14 : ℂ) * ζ ^ 31)) * commutesA01
      + ((-(2 : ℂ) - (2 : ℂ) * ζ ^ 3 - (2 : ℂ) * ζ ^ 7 - (2 : ℂ) * ζ ^ 10 + (2 : ℂ) * ζ ^ 19 + (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 23 + (2 : ℂ) * ζ ^ 25 - (2 : ℂ) * ζ ^ 31)) * commutesA05
      + ((((432 / 11) : ℂ) + ((430 / 11) : ℂ) * ζ ^ 3 + ((436 / 11) : ℂ) * ζ ^ 5 + ((430 / 11) : ℂ) * ζ ^ 7 + ((380 / 11) : ℂ) * ζ ^ 10 - ((92 / 11) : ℂ) * ζ ^ 15 - ((430 / 11) : ℂ) * ζ ^ 19 - ((190 / 11) : ℂ) * ζ ^ 20 - ((430 / 11) : ℂ) * ζ ^ 23 - ((296 / 11) : ℂ) * ζ ^ 25 - ((364 / 11) : ℂ) * ζ ^ 30 + ((430 / 11) : ℂ) * ζ ^ 31)) * commutesA10
      + (((5 : ℂ) - ζ ^ 3 + (8 : ℂ) * ζ ^ 5 - ζ ^ 7 + (11 : ℂ) * ζ ^ 10 + (16 : ℂ) * ζ ^ 15 + ζ ^ 19 + (11 : ℂ) * ζ ^ 20 + ζ ^ 23 + (9 : ℂ) * ζ ^ 25 + (6 : ℂ) * ζ ^ 30 - ζ ^ 31)) * commutesA11
      - (
        ((-((54 / 11) : ℂ) - ((41 / 2) : ℂ) * ζ ^ 3 + ((54 / 11) : ℂ) * ζ ^ 4 - ((221 / 22) : ℂ) * ζ ^ 5 - ((134 / 11) : ℂ) * ζ ^ 6 - ((237 / 11) : ℂ) * ζ ^ 8 + ((221 / 22) : ℂ) * ζ ^ 9 - ((11 / 2) : ℂ) * ζ ^ 10 - ((191 / 22) : ℂ) * ζ ^ 13 - ((147 / 22) : ℂ) * ζ ^ 14 - ((147 / 22) : ℂ) * ζ ^ 15 - ((64 / 11) : ℂ) * ζ ^ 18 + ((147 / 22) : ℂ) * ζ ^ 19 - ((4 / 11) : ℂ) * ζ ^ 20 + ((134 / 11) : ℂ) * ζ ^ 22 + ((113 / 22) : ℂ) * ζ ^ 23 + ((4 / 11) : ℂ) * ζ ^ 24 + ((311 / 22) : ℂ) * ζ ^ 25 + ((134 / 11) : ℂ) * ζ ^ 26 + ((197 / 11) : ℂ) * ζ ^ 28 - ((311 / 22) : ℂ) * ζ ^ 29 - ((134 / 11) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((43 / 11) : ℂ) + (20 : ℂ) * ζ ^ 3 - ((43 / 11) : ℂ) * ζ ^ 4 + ((221 / 22) : ℂ) * ζ ^ 5 + ((257 / 22) : ℂ) * ζ ^ 6 + ((226 / 11) : ℂ) * ζ ^ 8 - ((221 / 22) : ℂ) * ζ ^ 9 + ((11 / 2) : ℂ) * ζ ^ 10 + ((191 / 22) : ℂ) * ζ ^ 13 + ((68 / 11) : ℂ) * ζ ^ 14 + ((147 / 22) : ℂ) * ζ ^ 15 + ((139 / 22) : ℂ) * ζ ^ 18 - ((147 / 22) : ℂ) * ζ ^ 19 - ((3 / 22) : ℂ) * ζ ^ 20 - ((257 / 22) : ℂ) * ζ ^ 22 - ((51 / 11) : ℂ) * ζ ^ 23 + ((3 / 22) : ℂ) * ζ ^ 24 - ((150 / 11) : ℂ) * ζ ^ 25 - ((257 / 22) : ℂ) * ζ ^ 26 - ((197 / 11) : ℂ) * ζ ^ 28 + ((150 / 11) : ℂ) * ζ ^ 29 + ((257 / 22) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((((477 / 22) : ℂ) + ((887 / 44) : ℂ) * ζ ^ 3 - ((477 / 22) : ℂ) * ζ ^ 4 + ((161 / 11) : ℂ) * ζ ^ 5 - ((9 / 44) : ℂ) * ζ ^ 6 + ((146 / 11) : ℂ) * ζ ^ 8 - ((161 / 11) : ℂ) * ζ ^ 9 + ((277 / 44) : ℂ) * ζ ^ 10 + ((293 / 44) : ℂ) * ζ ^ 13 - ((13 / 2) : ℂ) * ζ ^ 14 + ((37 / 4) : ℂ) * ζ ^ 15 + ((433 / 44) : ℂ) * ζ ^ 18 - ((37 / 4) : ℂ) * ζ ^ 19 - ((227 / 22) : ℂ) * ζ ^ 20 + ((9 / 44) : ℂ) * ζ ^ 22 - ((175 / 22) : ℂ) * ζ ^ 23 + ((227 / 22) : ℂ) * ζ ^ 24 - (11 : ℂ) * ζ ^ 25 + ((9 / 44) : ℂ) * ζ ^ 26 - ((91 / 11) : ℂ) * ζ ^ 28 + (11 : ℂ) * ζ ^ 29 - ((9 / 44) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((((89 / 44) : ℂ) + ((27 / 22) : ℂ) * ζ ^ 3 - ((89 / 44) : ℂ) * ζ ^ 4 + ((53 / 22) : ℂ) * ζ ^ 5 + ((27 / 44) : ℂ) * ζ ^ 6 + ((41 / 44) : ℂ) * ζ ^ 8 - ((53 / 22) : ℂ) * ζ ^ 9 + ((97 / 44) : ℂ) * ζ ^ 10 - ((17 / 22) : ℂ) * ζ ^ 13 - ((35 / 22) : ℂ) * ζ ^ 14 + ((13 / 11) : ℂ) * ζ ^ 15 - ((127 / 44) : ℂ) * ζ ^ 18 - ((13 / 11) : ℂ) * ζ ^ 19 + ((53 / 22) : ℂ) * ζ ^ 20 - ((27 / 44) : ℂ) * ζ ^ 22 - ((9 / 22) : ℂ) * ζ ^ 23 - ((53 / 22) : ℂ) * ζ ^ 24 - ((9 / 22) : ℂ) * ζ ^ 25 - ((27 / 44) : ℂ) * ζ ^ 26 - ((3 / 2) : ℂ) * ζ ^ 28 + ((9 / 22) : ℂ) * ζ ^ 29 + ((27 / 44) : ℂ) * ζ ^ 30)) * Y 2 1
        + (((1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 3 - ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 6 + ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 25 - ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 29 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row14_reducedY12
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow14TransformedGeneratorA =
        alternatingSixAmbientRow14TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow14GeneratorBDiagonal =
        alternatingSixAmbientRow14GeneratorBDiagonal * Y) :
    Y 1 2 = 0 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 1 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51] at commutesA01
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51] at commutesA11

  linear_combination
    ((-(6 : ℂ) * ζ ^ 3 + (2 : ℂ) * ζ ^ 5 - (6 : ℂ) * ζ ^ 7 + (2 : ℂ) * ζ ^ 10 + (10 : ℂ) * ζ ^ 15 + (6 : ℂ) * ζ ^ 19 + (10 : ℂ) * ζ ^ 20 + (6 : ℂ) * ζ ^ 23 + (8 : ℂ) * ζ ^ 25 + (10 : ℂ) * ζ ^ 30 - (6 : ℂ) * ζ ^ 31)) * commutesA01
      + ((-((98 / 11) : ℂ) - ((32 / 11) : ℂ) * ζ ^ 3 - ((118 / 11) : ℂ) * ζ ^ 5 - ((32 / 11) : ℂ) * ζ ^ 7 - ((158 / 11) : ℂ) * ζ ^ 10 - ((138 / 11) : ℂ) * ζ ^ 15 + ((32 / 11) : ℂ) * ζ ^ 19 - ((70 / 11) : ℂ) * ζ ^ 20 + ((32 / 11) : ℂ) * ζ ^ 23 - ((58 / 11) : ℂ) * ζ ^ 25 + ((12 / 11) : ℂ) * ζ ^ 30 - ((32 / 11) : ℂ) * ζ ^ 31)) * commutesA10
      + (((4 : ℂ) + (6 : ℂ) * ζ ^ 3 + (4 : ℂ) * ζ ^ 5 + (6 : ℂ) * ζ ^ 7 + (2 : ℂ) * ζ ^ 10 - (6 : ℂ) * ζ ^ 15 - (6 : ℂ) * ζ ^ 19 - (6 : ℂ) * ζ ^ 20 - (6 : ℂ) * ζ ^ 23 - (6 : ℂ) * ζ ^ 25 - (8 : ℂ) * ζ ^ 30 + (6 : ℂ) * ζ ^ 31)) * commutesA11
      - (
        ((((49 / 22) : ℂ) + ((46 / 11) : ℂ) * ζ ^ 3 - ((49 / 22) : ℂ) * ζ ^ 4 + ((25 / 11) : ℂ) * ζ ^ 5 - ((1 / 11) : ℂ) * ζ ^ 6 + ((42 / 11) : ℂ) * ζ ^ 8 - ((25 / 11) : ℂ) * ζ ^ 9 + ((29 / 22) : ℂ) * ζ ^ 10 + ((76 / 11) : ℂ) * ζ ^ 13 - ((31 / 22) : ℂ) * ζ ^ 14 + ((28 / 11) : ℂ) * ζ ^ 15 + ((58 / 11) : ℂ) * ζ ^ 18 - ((28 / 11) : ℂ) * ζ ^ 19 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 11) : ℂ) * ζ ^ 22 + ((42 / 11) : ℂ) * ζ ^ 23 + ((1 / 2) : ℂ) * ζ ^ 24 - ((13 / 11) : ℂ) * ζ ^ 25 + ((1 / 11) : ℂ) * ζ ^ 26 + ((19 / 11) : ℂ) * ζ ^ 28 + ((13 / 11) : ℂ) * ζ ^ 29 - ((1 / 11) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((-((49 / 22) : ℂ) - ((46 / 11) : ℂ) * ζ ^ 3 + ((49 / 22) : ℂ) * ζ ^ 4 - ((25 / 11) : ℂ) * ζ ^ 5 + ((1 / 11) : ℂ) * ζ ^ 6 - ((42 / 11) : ℂ) * ζ ^ 8 + ((25 / 11) : ℂ) * ζ ^ 9 - ((29 / 22) : ℂ) * ζ ^ 10 - ((76 / 11) : ℂ) * ζ ^ 13 + ((31 / 22) : ℂ) * ζ ^ 14 - ((28 / 11) : ℂ) * ζ ^ 15 - ((58 / 11) : ℂ) * ζ ^ 18 + ((28 / 11) : ℂ) * ζ ^ 19 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 11) : ℂ) * ζ ^ 22 - ((42 / 11) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 24 + ((13 / 11) : ℂ) * ζ ^ 25 - ((1 / 11) : ℂ) * ζ ^ 26 - ((19 / 11) : ℂ) * ζ ^ 28 - ((13 / 11) : ℂ) * ζ ^ 29 + ((1 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((42 / 11) : ℂ) + ((20 / 11) : ℂ) * ζ ^ 3 + ((42 / 11) : ℂ) * ζ ^ 4 - ((9 / 22) : ℂ) * ζ ^ 5 + ((27 / 22) : ℂ) * ζ ^ 6 - ((7 / 11) : ℂ) * ζ ^ 8 + ((9 / 22) : ℂ) * ζ ^ 9 + ((59 / 22) : ℂ) * ζ ^ 10 + ((38 / 11) : ℂ) * ζ ^ 13 - ((16 / 11) : ℂ) * ζ ^ 14 + ((7 / 11) : ℂ) * ζ ^ 15 - ((2 / 11) : ℂ) * ζ ^ 18 - ((7 / 11) : ℂ) * ζ ^ 19 + ((30 / 11) : ℂ) * ζ ^ 20 - ((27 / 22) : ℂ) * ζ ^ 22 + ((7 / 22) : ℂ) * ζ ^ 23 - ((30 / 11) : ℂ) * ζ ^ 24 + ((26 / 11) : ℂ) * ζ ^ 25 - ((27 / 22) : ℂ) * ζ ^ 26 + ((3 / 11) : ℂ) * ζ ^ 28 - ((26 / 11) : ℂ) * ζ ^ 29 + ((27 / 22) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((-(1 : ℂ) - ((41 / 22) : ℂ) * ζ ^ 3 + ζ ^ 4 - ((16 / 11) : ℂ) * ζ ^ 5 - ((18 / 11) : ℂ) * ζ ^ 6 - ((49 / 22) : ℂ) * ζ ^ 8 + ((16 / 11) : ℂ) * ζ ^ 9 - ((45 / 22) : ℂ) * ζ ^ 10 - ((14 / 11) : ℂ) * ζ ^ 13 + ((9 / 22) : ℂ) * ζ ^ 14 + ((1 / 22) : ℂ) * ζ ^ 15 + ((14 / 11) : ℂ) * ζ ^ 18 - ((1 / 22) : ℂ) * ζ ^ 19 - ((39 / 22) : ℂ) * ζ ^ 20 + ((18 / 11) : ℂ) * ζ ^ 22 + ((4 / 11) : ℂ) * ζ ^ 23 + ((39 / 22) : ℂ) * ζ ^ 24 - ((28 / 11) : ℂ) * ζ ^ 25 + ((18 / 11) : ℂ) * ζ ^ 26 - ((19 / 22) : ℂ) * ζ ^ 28 + ((28 / 11) : ℂ) * ζ ^ 29 - ((18 / 11) : ℂ) * ζ ^ 30)) * Y 2 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row14_reducedY21
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow14TransformedGeneratorA =
        alternatingSixAmbientRow14TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow14GeneratorBDiagonal =
        alternatingSixAmbientRow14GeneratorBDiagonal * Y) :
    Y 2 1 = 0 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 1 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51] at commutesA01
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51] at commutesA11

  linear_combination
    ((-(8 : ℂ) * ζ ^ 3 + (8 : ℂ) * ζ ^ 5 - (8 : ℂ) * ζ ^ 7 + (18 : ℂ) * ζ ^ 10 + (28 : ℂ) * ζ ^ 15 + (8 : ℂ) * ζ ^ 19 + (26 : ℂ) * ζ ^ 20 + (8 : ℂ) * ζ ^ 23 + (20 : ℂ) * ζ ^ 25 + (14 : ℂ) * ζ ^ 30 - (8 : ℂ) * ζ ^ 31)) * commutesA01
      + ((-((326 / 11) : ℂ) - ((212 / 11) : ℂ) * ζ ^ 3 - ((402 / 11) : ℂ) * ζ ^ 5 - ((212 / 11) : ℂ) * ζ ^ 7 - ((448 / 11) : ℂ) * ζ ^ 10 - ((272 / 11) : ℂ) * ζ ^ 15 + ((212 / 11) : ℂ) * ζ ^ 19 - ((122 / 11) : ℂ) * ζ ^ 20 + ((212 / 11) : ℂ) * ζ ^ 23 - ((32 / 11) : ℂ) * ζ ^ 25 + ((122 / 11) : ℂ) * ζ ^ 30 - ((212 / 11) : ℂ) * ζ ^ 31)) * commutesA10
      + (((8 : ℂ) + (14 : ℂ) * ζ ^ 3 + (6 : ℂ) * ζ ^ 5 + (14 : ℂ) * ζ ^ 7 - (18 : ℂ) * ζ ^ 15 - (14 : ℂ) * ζ ^ 19 - (18 : ℂ) * ζ ^ 20 - (14 : ℂ) * ζ ^ 23 - (18 : ℂ) * ζ ^ 25 - (16 : ℂ) * ζ ^ 30 + (14 : ℂ) * ζ ^ 31)) * commutesA11
      - (
        ((((163 / 22) : ℂ) + ((305 / 22) : ℂ) * ζ ^ 3 - ((163 / 22) : ℂ) * ζ ^ 4 + ((15 / 2) : ℂ) * ζ ^ 5 + ((41 / 11) : ℂ) * ζ ^ 6 + ((174 / 11) : ℂ) * ζ ^ 8 - ((15 / 2) : ℂ) * ζ ^ 9 + ((51 / 11) : ℂ) * ζ ^ 10 + ((381 / 22) : ℂ) * ζ ^ 13 - ((10 / 11) : ℂ) * ζ ^ 14 + ((80 / 11) : ℂ) * ζ ^ 15 + ((153 / 11) : ℂ) * ζ ^ 18 - ((80 / 11) : ℂ) * ζ ^ 19 - ((19 / 11) : ℂ) * ζ ^ 20 - ((41 / 11) : ℂ) * ζ ^ 22 + ((15 / 2) : ℂ) * ζ ^ 23 + ((19 / 11) : ℂ) * ζ ^ 24 - ((153 / 22) : ℂ) * ζ ^ 25 - ((41 / 11) : ℂ) * ζ ^ 26 - ((26 / 11) : ℂ) * ζ ^ 28 + ((153 / 22) : ℂ) * ζ ^ 29 + ((41 / 11) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((-((163 / 22) : ℂ) - ((305 / 22) : ℂ) * ζ ^ 3 + ((163 / 22) : ℂ) * ζ ^ 4 - ((15 / 2) : ℂ) * ζ ^ 5 - ((41 / 11) : ℂ) * ζ ^ 6 - ((174 / 11) : ℂ) * ζ ^ 8 + ((15 / 2) : ℂ) * ζ ^ 9 - ((51 / 11) : ℂ) * ζ ^ 10 - ((381 / 22) : ℂ) * ζ ^ 13 + ((10 / 11) : ℂ) * ζ ^ 14 - ((80 / 11) : ℂ) * ζ ^ 15 - ((153 / 11) : ℂ) * ζ ^ 18 + ((80 / 11) : ℂ) * ζ ^ 19 + ((19 / 11) : ℂ) * ζ ^ 20 + ((41 / 11) : ℂ) * ζ ^ 22 - ((15 / 2) : ℂ) * ζ ^ 23 - ((19 / 11) : ℂ) * ζ ^ 24 + ((153 / 22) : ℂ) * ζ ^ 25 + ((41 / 11) : ℂ) * ζ ^ 26 + ((26 / 11) : ℂ) * ζ ^ 28 - ((153 / 22) : ℂ) * ζ ^ 29 - ((41 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((127 / 11) : ℂ) - ((25 / 11) : ℂ) * ζ ^ 3 + ((127 / 11) : ℂ) * ζ ^ 4 - ((137 / 22) : ℂ) * ζ ^ 5 + ((63 / 22) : ℂ) * ζ ^ 6 - ((37 / 22) : ℂ) * ζ ^ 8 + ((137 / 22) : ℂ) * ζ ^ 9 + ((95 / 22) : ℂ) * ζ ^ 10 + ((109 / 22) : ℂ) * ζ ^ 13 - ((16 / 11) : ℂ) * ζ ^ 14 - ((47 / 22) : ℂ) * ζ ^ 15 - ((35 / 11) : ℂ) * ζ ^ 18 + ((47 / 22) : ℂ) * ζ ^ 19 + ((205 / 22) : ℂ) * ζ ^ 20 - ((63 / 22) : ℂ) * ζ ^ 22 + ((28 / 11) : ℂ) * ζ ^ 23 - ((205 / 22) : ℂ) * ζ ^ 24 + ((89 / 11) : ℂ) * ζ ^ 25 - ((63 / 22) : ℂ) * ζ ^ 26 + ((61 / 22) : ℂ) * ζ ^ 28 - ((89 / 11) : ℂ) * ζ ^ 29 + ((63 / 22) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((-(3 : ℂ) - ((105 / 22) : ℂ) * ζ ^ 3 + (3 : ℂ) * ζ ^ 4 - ((65 / 22) : ℂ) * ζ ^ 5 - ((87 / 22) : ℂ) * ζ ^ 6 - ((115 / 22) : ℂ) * ζ ^ 8 + ((65 / 22) : ℂ) * ζ ^ 9 - ((127 / 22) : ℂ) * ζ ^ 10 - ((29 / 22) : ℂ) * ζ ^ 13 + ((20 / 11) : ℂ) * ζ ^ 14 - ((27 / 22) : ℂ) * ζ ^ 15 + ((35 / 11) : ℂ) * ζ ^ 18 + ((27 / 22) : ℂ) * ζ ^ 19 - ((101 / 22) : ℂ) * ζ ^ 20 + ((87 / 22) : ℂ) * ζ ^ 22 + ((1 / 11) : ℂ) * ζ ^ 23 + ((101 / 22) : ℂ) * ζ ^ 24 - ((97 / 22) : ℂ) * ζ ^ 25 + ((87 / 22) : ℂ) * ζ ^ 26 - ((17 / 22) : ℂ) * ζ ^ 28 + ((97 / 22) : ℂ) * ζ ^ 29 - ((87 / 22) : ℂ) * ζ ^ 30)) * Y 2 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row14_reducedY22
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow14TransformedGeneratorA =
        alternatingSixAmbientRow14TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow14GeneratorBDiagonal =
        alternatingSixAmbientRow14GeneratorBDiagonal * Y) :
    Y 2 2 = Y 5 5 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY25,
      hY30,
      hY31,
      hY32,
      hY35,
      hY40,
      hY41,
      hY42,
      hY45,
      hY50,
      hY51,
      hY52] at commutesA01
  have commutesA02 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA02
  simp only [Fin.sum_univ_succ] at commutesA02
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA02
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY25,
      hY30,
      hY31,
      hY32,
      hY35,
      hY40,
      hY41,
      hY42,
      hY45,
      hY50,
      hY51,
      hY52] at commutesA02
  have commutesA05 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA05
  simp only [Fin.sum_univ_succ] at commutesA05
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA05
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY25,
      hY30,
      hY31,
      hY32,
      hY35,
      hY40,
      hY41,
      hY42,
      hY45,
      hY50,
      hY51,
      hY52] at commutesA05
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY25,
      hY30,
      hY31,
      hY32,
      hY35,
      hY40,
      hY41,
      hY42,
      hY45,
      hY50,
      hY51,
      hY52] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY25,
      hY30,
      hY31,
      hY32,
      hY35,
      hY40,
      hY41,
      hY42,
      hY45,
      hY50,
      hY51,
      hY52] at commutesA11

  linear_combination
    ((((56 / 5) : ℂ) + ((48 / 5) : ℂ) * ζ ^ 3 + ((28 / 5) : ℂ) * ζ ^ 5 + ((48 / 5) : ℂ) * ζ ^ 7 + (8 : ℂ) * ζ ^ 10 - ((44 / 5) : ℂ) * ζ ^ 15 - ((48 / 5) : ℂ) * ζ ^ 19 - (12 : ℂ) * ζ ^ 20 - ((48 / 5) : ℂ) * ζ ^ 23 - ((52 / 5) : ℂ) * ζ ^ 25 - ((68 / 5) : ℂ) * ζ ^ 30 + ((48 / 5) : ℂ) * ζ ^ 31)) * commutesA01
      + ((-((18 / 5) : ℂ) - ((6 / 5) : ℂ) * ζ ^ 3 - ((6 / 5) : ℂ) * ζ ^ 7 + ((6 / 5) : ℂ) * ζ ^ 10 + ((6 / 5) : ℂ) * ζ ^ 19 + ((2 / 5) : ℂ) * ζ ^ 20 + ((6 / 5) : ℂ) * ζ ^ 23 - ((2 / 5) : ℂ) * ζ ^ 25 + ((8 / 5) : ℂ) * ζ ^ 30 - ((6 / 5) : ℂ) * ζ ^ 31)) * commutesA02
      + ((-(2 : ℂ) - (2 : ℂ) * ζ ^ 3 - (2 : ℂ) * ζ ^ 7 - (2 : ℂ) * ζ ^ 10 + (2 : ℂ) * ζ ^ 19 + (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 23 + (2 : ℂ) * ζ ^ 25 - (2 : ℂ) * ζ ^ 31)) * commutesA05
      + ((-((114 / 55) : ℂ) - ((522 / 55) : ℂ) * ζ ^ 3 - ((112 / 55) : ℂ) * ζ ^ 5 - ((522 / 55) : ℂ) * ζ ^ 7 + ((82 / 11) : ℂ) * ζ ^ 10 + ((856 / 55) : ℂ) * ζ ^ 15 + ((522 / 55) : ℂ) * ζ ^ 19 + ((190 / 11) : ℂ) * ζ ^ 20 + ((522 / 55) : ℂ) * ζ ^ 23 + ((798 / 55) : ℂ) * ζ ^ 25 + ((632 / 55) : ℂ) * ζ ^ 30 - ((522 / 55) : ℂ) * ζ ^ 31)) * commutesA10
      + ((-(8 : ℂ) - (6 : ℂ) * ζ ^ 3 - (6 : ℂ) * ζ ^ 5 - (6 : ℂ) * ζ ^ 7 - (8 : ℂ) * ζ ^ 10 + (2 : ℂ) * ζ ^ 15 + (6 : ℂ) * ζ ^ 19 + (4 : ℂ) * ζ ^ 20 + (6 : ℂ) * ζ ^ 23 + (4 : ℂ) * ζ ^ 25 + (8 : ℂ) * ζ ^ 30 - (6 : ℂ) * ζ ^ 31)) * commutesA11
      - (
        ((-((249 / 110) : ℂ) + ((94 / 55) : ℂ) * ζ ^ 3 + ((249 / 110) : ℂ) * ζ ^ 4 + ((96 / 55) : ℂ) * ζ ^ 5 + ((347 / 110) : ℂ) * ζ ^ 6 + ((25 / 22) : ℂ) * ζ ^ 8 - ((96 / 55) : ℂ) * ζ ^ 9 - ((181 / 110) : ℂ) * ζ ^ 10 - ((206 / 55) : ℂ) * ζ ^ 13 + ((24 / 5) : ℂ) * ζ ^ 14 + ((13 / 11) : ℂ) * ζ ^ 15 - ((587 / 110) : ℂ) * ζ ^ 18 - ((13 / 11) : ℂ) * ζ ^ 19 - ((49 / 55) : ℂ) * ζ ^ 20 - ((347 / 110) : ℂ) * ζ ^ 22 - ((287 / 55) : ℂ) * ζ ^ 23 + ((49 / 55) : ℂ) * ζ ^ 24 - ((17 / 11) : ℂ) * ζ ^ 25 - ((347 / 110) : ℂ) * ζ ^ 26 - ((472 / 55) : ℂ) * ζ ^ 28 + ((17 / 11) : ℂ) * ζ ^ 29 + ((347 / 110) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((39 / 22) : ℂ) - ((27 / 11) : ℂ) * ζ ^ 3 - ((39 / 22) : ℂ) * ζ ^ 4 - ((21 / 11) : ℂ) * ζ ^ 5 - ((81 / 22) : ℂ) * ζ ^ 6 - ((37 / 22) : ℂ) * ζ ^ 8 + ((21 / 11) : ℂ) * ζ ^ 9 + ((41 / 22) : ℂ) * ζ ^ 10 + ((40 / 11) : ℂ) * ζ ^ 13 - ((61 / 11) : ℂ) * ζ ^ 14 - ((71 / 55) : ℂ) * ζ ^ 15 + ((669 / 110) : ℂ) * ζ ^ 18 + ((71 / 55) : ℂ) * ζ ^ 19 + ((6 / 11) : ℂ) * ζ ^ 20 + ((81 / 22) : ℂ) * ζ ^ 22 + ((303 / 55) : ℂ) * ζ ^ 23 - ((6 / 11) : ℂ) * ζ ^ 24 + ((11 / 5) : ℂ) * ζ ^ 25 + ((81 / 22) : ℂ) * ζ ^ 26 + ((486 / 55) : ℂ) * ζ ^ 28 - ((11 / 5) : ℂ) * ζ ^ 29 - ((81 / 22) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((111 / 22) : ℂ) - ((189 / 22) : ℂ) * ζ ^ 3 + ((111 / 22) : ℂ) * ζ ^ 4 - ((95 / 22) : ℂ) * ζ ^ 5 - ((117 / 110) : ℂ) * ζ ^ 6 - ((579 / 110) : ℂ) * ζ ^ 8 + ((95 / 22) : ℂ) * ζ ^ 9 - ((303 / 55) : ℂ) * ζ ^ 10 - ((149 / 22) : ℂ) * ζ ^ 13 + ((489 / 110) : ℂ) * ζ ^ 14 - ((221 / 55) : ℂ) * ζ ^ 15 - ((369 / 110) : ℂ) * ζ ^ 18 + ((221 / 55) : ℂ) * ζ ^ 19 + ((57 / 110) : ℂ) * ζ ^ 20 + ((117 / 110) : ℂ) * ζ ^ 22 + ((49 / 22) : ℂ) * ζ ^ 23 - ((57 / 110) : ℂ) * ζ ^ 24 + ((15 / 22) : ℂ) * ζ ^ 25 + ((117 / 110) : ℂ) * ζ ^ 26 + ((138 / 55) : ℂ) * ζ ^ 28 - ((15 / 22) : ℂ) * ζ ^ 29 - ((117 / 110) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((((26 / 55) : ℂ) + ((23 / 10) : ℂ) * ζ ^ 3 - ((26 / 55) : ℂ) * ζ ^ 4 + ((13 / 22) : ℂ) * ζ ^ 5 + ((171 / 110) : ℂ) * ζ ^ 6 + ((43 / 22) : ℂ) * ζ ^ 8 - ((13 / 22) : ℂ) * ζ ^ 9 + ((161 / 110) : ℂ) * ζ ^ 10 + ((112 / 55) : ℂ) * ζ ^ 13 + ((1 / 11) : ℂ) * ζ ^ 14 - ((13 / 110) : ℂ) * ζ ^ 15 - ((34 / 55) : ℂ) * ζ ^ 18 + ((13 / 110) : ℂ) * ζ ^ 19 + ((151 / 110) : ℂ) * ζ ^ 20 - ((171 / 110) : ℂ) * ζ ^ 22 - ((7 / 55) : ℂ) * ζ ^ 23 - ((151 / 110) : ℂ) * ζ ^ 24 + ((167 / 55) : ℂ) * ζ ^ 25 - ((171 / 110) : ℂ) * ζ ^ 26 + ((79 / 55) : ℂ) * ζ ^ 28 - ((167 / 55) : ℂ) * ζ ^ 29 + ((171 / 110) : ℂ) * ζ ^ 30)) * Y 2 1
        + ((-((28 / 55) : ℂ) + ((27 / 110) : ℂ) * ζ ^ 3 + ((28 / 55) : ℂ) * ζ ^ 4 + ((9 / 55) : ℂ) * ζ ^ 5 + ((3 / 110) : ℂ) * ζ ^ 6 - ((5 / 11) : ℂ) * ζ ^ 8 - ((9 / 55) : ℂ) * ζ ^ 9 - ((12 / 55) : ℂ) * ζ ^ 10 + ((6 / 55) : ℂ) * ζ ^ 13 + ((27 / 110) : ℂ) * ζ ^ 14 + ((6 / 55) : ℂ) * ζ ^ 15 - ((27 / 110) : ℂ) * ζ ^ 18 - ((6 / 55) : ℂ) * ζ ^ 19 - ((17 / 110) : ℂ) * ζ ^ 20 - ((3 / 110) : ℂ) * ζ ^ 22 + ((23 / 110) : ℂ) * ζ ^ 23 + ((17 / 110) : ℂ) * ζ ^ 24 - ((17 / 110) : ℂ) * ζ ^ 25 - ((3 / 110) : ℂ) * ζ ^ 26 - ((14 / 55) : ℂ) * ζ ^ 28 + ((17 / 110) : ℂ) * ζ ^ 29 + ((3 / 110) : ℂ) * ζ ^ 30)) * Y 2 2
        + (((1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 3 - ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 6 + ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 25 - ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 29 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row14_reducedY33
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow14TransformedGeneratorA =
        alternatingSixAmbientRow14TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow14GeneratorBDiagonal =
        alternatingSixAmbientRow14GeneratorBDiagonal * Y) :
    Y 3 3 = Y 5 5 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 3 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY23,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51,
      hY53] at commutesA01
  have commutesA03 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (3 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA03
  simp only [Fin.sum_univ_succ] at commutesA03
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA03
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY23,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51,
      hY53] at commutesA03
  have commutesA05 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA05
  simp only [Fin.sum_univ_succ] at commutesA05
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA05
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY23,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51,
      hY53] at commutesA05
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY23,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51,
      hY53] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY23,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51,
      hY53] at commutesA11
  have commutesA13 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (3 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA13
  simp only [Fin.sum_univ_succ] at commutesA13
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA13
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY23,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51,
      hY53] at commutesA13

  linear_combination
    (((14 : ℂ) + ((58 / 7) : ℂ) * ζ ^ 3 + ((38 / 7) : ℂ) * ζ ^ 5 + ((58 / 7) : ℂ) * ζ ^ 7 + ((78 / 7) : ℂ) * ζ ^ 10 - ((10 / 7) : ℂ) * ζ ^ 15 - ((58 / 7) : ℂ) * ζ ^ 19 - (8 : ℂ) * ζ ^ 20 - ((58 / 7) : ℂ) * ζ ^ 23 - ((36 / 7) : ℂ) * ζ ^ 25 - ((82 / 7) : ℂ) * ζ ^ 30 + ((58 / 7) : ℂ) * ζ ^ 31)) * commutesA01
      + ((((10 / 7) : ℂ) + ((6 / 7) : ℂ) * ζ ^ 3 - ((4 / 7) : ℂ) * ζ ^ 5 + ((6 / 7) : ℂ) * ζ ^ 7 + ((2 / 7) : ℂ) * ζ ^ 10 - ((2 / 7) : ℂ) * ζ ^ 15 - ((6 / 7) : ℂ) * ζ ^ 19 - ((8 / 7) : ℂ) * ζ ^ 20 - ((6 / 7) : ℂ) * ζ ^ 23 + ((6 / 7) : ℂ) * ζ ^ 25 + ((4 / 7) : ℂ) * ζ ^ 30 + ((6 / 7) : ℂ) * ζ ^ 31)) * commutesA03
      + ((-(2 : ℂ) - (2 : ℂ) * ζ ^ 3 - (2 : ℂ) * ζ ^ 7 - (2 : ℂ) * ζ ^ 10 + (2 : ℂ) * ζ ^ 19 + (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 23 + (2 : ℂ) * ζ ^ 25 - (2 : ℂ) * ζ ^ 31)) * commutesA05
      + ((-((64 / 7) : ℂ) - ((120 / 7) : ℂ) * ζ ^ 3 - ((94 / 7) : ℂ) * ζ ^ 5 - ((120 / 7) : ℂ) * ζ ^ 7 - ((20 / 7) : ℂ) * ζ ^ 10 + ((82 / 7) : ℂ) * ζ ^ 15 + ((120 / 7) : ℂ) * ζ ^ 19 + ((110 / 7) : ℂ) * ζ ^ 20 + ((120 / 7) : ℂ) * ζ ^ 23 + ((120 / 7) : ℂ) * ζ ^ 25 + ((100 / 7) : ℂ) * ζ ^ 30 - ((120 / 7) : ℂ) * ζ ^ 31)) * commutesA10
      + ((-((50 / 7) : ℂ) - ((25 / 7) : ℂ) * ζ ^ 3 - ((25 / 7) : ℂ) * ζ ^ 5 - ((25 / 7) : ℂ) * ζ ^ 7 - ((60 / 7) : ℂ) * ζ ^ 10 - ((15 / 7) : ℂ) * ζ ^ 15 + ((25 / 7) : ℂ) * ζ ^ 19 + ((12 / 7) : ℂ) * ζ ^ 20 + ((25 / 7) : ℂ) * ζ ^ 23 - ((8 / 7) : ℂ) * ζ ^ 25 + ((34 / 7) : ℂ) * ζ ^ 30 - ((25 / 7) : ℂ) * ζ ^ 31)) * commutesA11
      + ((((9 / 7) : ℂ) + ((3 / 7) : ℂ) * ζ ^ 5 + ((11 / 7) : ℂ) * ζ ^ 10 - ζ ^ 15 - ((3 / 7) : ℂ) * ζ ^ 20 - ((1 / 7) : ℂ) * ζ ^ 25 - ((6 / 7) : ℂ) * ζ ^ 30)) * commutesA13
      - (
        ((-((23 / 33) : ℂ) + ((221 / 42) : ℂ) * ζ ^ 3 + ((23 / 33) : ℂ) * ζ ^ 4 + ((100 / 21) : ℂ) * ζ ^ 5 + ((669 / 154) : ℂ) * ζ ^ 6 + ((2419 / 462) : ℂ) * ζ ^ 8 - ((100 / 21) : ℂ) * ζ ^ 9 - ((87 / 77) : ℂ) * ζ ^ 10 + ((29 / 77) : ℂ) * ζ ^ 13 + ((843 / 154) : ℂ) * ζ ^ 14 + ((173 / 66) : ℂ) * ζ ^ 15 - ((53 / 21) : ℂ) * ζ ^ 18 - ((173 / 66) : ℂ) * ζ ^ 19 - ((19 / 462) : ℂ) * ζ ^ 20 - ((669 / 154) : ℂ) * ζ ^ 22 - ((643 / 154) : ℂ) * ζ ^ 23 + ((19 / 462) : ℂ) * ζ ^ 24 - ((191 / 42) : ℂ) * ζ ^ 25 - ((669 / 154) : ℂ) * ζ ^ 26 - ((2243 / 231) : ℂ) * ζ ^ 28 + ((191 / 42) : ℂ) * ζ ^ 29 + ((669 / 154) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((89 / 154) : ℂ) - ((95 / 14) : ℂ) * ζ ^ 3 - ((89 / 154) : ℂ) * ζ ^ 4 - ((67 / 14) : ℂ) * ζ ^ 5 - ((417 / 77) : ℂ) * ζ ^ 6 - ((416 / 77) : ℂ) * ζ ^ 8 + ((67 / 14) : ℂ) * ζ ^ 9 + ((141 / 154) : ℂ) * ζ ^ 10 - ((51 / 77) : ℂ) * ζ ^ 13 - ((975 / 154) : ℂ) * ζ ^ 14 - ((27 / 11) : ℂ) * ζ ^ 15 + ((23 / 7) : ℂ) * ζ ^ 18 + ((27 / 11) : ℂ) * ζ ^ 19 - ((17 / 77) : ℂ) * ζ ^ 20 + ((417 / 77) : ℂ) * ζ ^ 22 + ((426 / 77) : ℂ) * ζ ^ 23 + ((17 / 77) : ℂ) * ζ ^ 24 + ((37 / 7) : ℂ) * ζ ^ 25 + ((417 / 77) : ℂ) * ζ ^ 26 + ((755 / 77) : ℂ) * ζ ^ 28 - ((37 / 7) : ℂ) * ζ ^ 29 - ((417 / 77) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((544 / 77) : ℂ) - ((3573 / 308) : ℂ) * ζ ^ 3 + ((544 / 77) : ℂ) * ζ ^ 4 - ((1185 / 154) : ℂ) * ζ ^ 5 - ((225 / 308) : ℂ) * ζ ^ 6 - ((348 / 77) : ℂ) * ζ ^ 8 + ((1185 / 154) : ℂ) * ζ ^ 9 - ((3635 / 924) : ℂ) * ζ ^ 10 - ((83 / 12) : ℂ) * ζ ^ 13 + ((740 / 231) : ℂ) * ζ ^ 14 - ((4985 / 924) : ℂ) * ζ ^ 15 - ((1021 / 308) : ℂ) * ζ ^ 18 + ((4985 / 924) : ℂ) * ζ ^ 19 + ((1283 / 462) : ℂ) * ζ ^ 20 + ((225 / 308) : ℂ) * ζ ^ 22 + ((898 / 231) : ℂ) * ζ ^ 23 - ((1283 / 462) : ℂ) * ζ ^ 24 + ((248 / 77) : ℂ) * ζ ^ 25 + ((225 / 308) : ℂ) * ζ ^ 26 + ((23 / 7) : ℂ) * ζ ^ 28 - ((248 / 77) : ℂ) * ζ ^ 29 - ((225 / 308) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((-((19 / 154) : ℂ) + ((479 / 308) : ℂ) * ζ ^ 3 + ((19 / 154) : ℂ) * ζ ^ 4 - ((7 / 44) : ℂ) * ζ ^ 5 + ((267 / 308) : ℂ) * ζ ^ 6 + ((183 / 308) : ℂ) * ζ ^ 8 + ((7 / 44) : ℂ) * ζ ^ 9 + ((181 / 308) : ℂ) * ζ ^ 10 + ((134 / 77) : ℂ) * ζ ^ 13 + ((43 / 154) : ℂ) * ζ ^ 14 - ((71 / 308) : ℂ) * ζ ^ 15 + ((47 / 154) : ℂ) * ζ ^ 18 + ((71 / 308) : ℂ) * ζ ^ 19 + ((41 / 308) : ℂ) * ζ ^ 20 - ((267 / 308) : ℂ) * ζ ^ 22 - ((39 / 154) : ℂ) * ζ ^ 23 - ((41 / 308) : ℂ) * ζ ^ 24 + ((333 / 154) : ℂ) * ζ ^ 25 - ((267 / 308) : ℂ) * ζ ^ 26 + ((219 / 154) : ℂ) * ζ ^ 28 - ((333 / 154) : ℂ) * ζ ^ 29 + ((267 / 308) : ℂ) * ζ ^ 30)) * Y 2 1
        + ((-((37 / 42) : ℂ) + ((43 / 42) : ℂ) * ζ ^ 3 + ((37 / 42) : ℂ) * ζ ^ 4 + ((1 / 42) : ℂ) * ζ ^ 5 + ((4 / 7) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((1 / 42) : ℂ) * ζ ^ 9 + ((3 / 14) : ℂ) * ζ ^ 10 + ((2 / 7) : ℂ) * ζ ^ 13 + ((5 / 14) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 15 - ((11 / 42) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 19 - ((5 / 21) : ℂ) * ζ ^ 20 - ((4 / 7) : ℂ) * ζ ^ 22 - ((6 / 7) : ℂ) * ζ ^ 23 + ((5 / 21) : ℂ) * ζ ^ 24 - ((5 / 21) : ℂ) * ζ ^ 25 - ((4 / 7) : ℂ) * ζ ^ 26 - ((2 / 21) : ℂ) * ζ ^ 28 + ((5 / 21) : ℂ) * ζ ^ 29 + ((4 / 7) : ℂ) * ζ ^ 30)) * Y 3 3
        + ((((9 / 28) : ℂ) - ((11 / 28) : ℂ) * ζ ^ 3 - ((9 / 28) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 5 - ((3 / 7) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 9 + ((1 / 14) : ℂ) * ζ ^ 10 - ((3 / 14) : ℂ) * ζ ^ 13 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 15 + ((11 / 28) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 19 + ((5 / 28) : ℂ) * ζ ^ 20 + ((3 / 7) : ℂ) * ζ ^ 22 + ((5 / 7) : ℂ) * ζ ^ 23 - ((5 / 28) : ℂ) * ζ ^ 24 + ((2 / 7) : ℂ) * ζ ^ 25 + ((3 / 7) : ℂ) * ζ ^ 26 + ((1 / 7) : ℂ) * ζ ^ 28 - ((2 / 7) : ℂ) * ζ ^ 29 - ((3 / 7) : ℂ) * ζ ^ 30)) * Y 4 3
        + (((1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 3 - ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 6 + ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 25 - ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 29 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row14_reducedY34
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow14TransformedGeneratorA =
        alternatingSixAmbientRow14TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow14GeneratorBDiagonal =
        alternatingSixAmbientRow14GeneratorBDiagonal * Y) :
    Y 3 4 = 0 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY54 :
      Y 5 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 4 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY24,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51,
      hY54] at commutesA01
  have commutesA04 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (4 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA04
  simp only [Fin.sum_univ_succ] at commutesA04
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA04
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY24,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51,
      hY54] at commutesA04
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY24,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51,
      hY54] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY24,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51,
      hY54] at commutesA11
  have commutesA14 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (4 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA14
  simp only [Fin.sum_univ_succ] at commutesA14
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA14
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY24,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51,
      hY54] at commutesA14

  linear_combination
    ((-(26 : ℂ) - ((166 / 7) : ℂ) * ζ ^ 3 - ((158 / 7) : ℂ) * ζ ^ 5 - ((166 / 7) : ℂ) * ζ ^ 7 - ((132 / 7) : ℂ) * ζ ^ 10 + ((60 / 7) : ℂ) * ζ ^ 15 + ((166 / 7) : ℂ) * ζ ^ 19 + (16 : ℂ) * ζ ^ 20 + ((166 / 7) : ℂ) * ζ ^ 23 + ((104 / 7) : ℂ) * ζ ^ 25 + ((170 / 7) : ℂ) * ζ ^ 30 - ((166 / 7) : ℂ) * ζ ^ 31)) * commutesA01
      + ((((10 / 7) : ℂ) + ((6 / 7) : ℂ) * ζ ^ 3 - ((4 / 7) : ℂ) * ζ ^ 5 + ((6 / 7) : ℂ) * ζ ^ 7 + ((2 / 7) : ℂ) * ζ ^ 10 - ((2 / 7) : ℂ) * ζ ^ 15 - ((6 / 7) : ℂ) * ζ ^ 19 - ((8 / 7) : ℂ) * ζ ^ 20 - ((6 / 7) : ℂ) * ζ ^ 23 + ((6 / 7) : ℂ) * ζ ^ 25 + ((4 / 7) : ℂ) * ζ ^ 30 + ((6 / 7) : ℂ) * ζ ^ 31)) * commutesA04
      + ((((163 / 7) : ℂ) + ((240 / 7) : ℂ) * ζ ^ 3 + ((153 / 7) : ℂ) * ζ ^ 5 + ((240 / 7) : ℂ) * ζ ^ 7 + ((61 / 7) : ℂ) * ζ ^ 10 - ((227 / 7) : ℂ) * ζ ^ 15 - ((240 / 7) : ℂ) * ζ ^ 19 - ((227 / 7) : ℂ) * ζ ^ 20 - ((240 / 7) : ℂ) * ζ ^ 23 - ((275 / 7) : ℂ) * ζ ^ 25 - ((228 / 7) : ℂ) * ζ ^ 30 + ((240 / 7) : ℂ) * ζ ^ 31)) * commutesA10
      + ((((97 / 7) : ℂ) + ((66 / 7) : ℂ) * ζ ^ 3 + ((108 / 7) : ℂ) * ζ ^ 5 + ((66 / 7) : ℂ) * ζ ^ 7 + ((101 / 7) : ℂ) * ζ ^ 10 + ((34 / 7) : ℂ) * ζ ^ 15 - ((66 / 7) : ℂ) * ζ ^ 19 - ((9 / 7) : ℂ) * ζ ^ 20 - ((66 / 7) : ℂ) * ζ ^ 23 - ((22 / 7) : ℂ) * ζ ^ 25 - ((64 / 7) : ℂ) * ζ ^ 30 + ((66 / 7) : ℂ) * ζ ^ 31)) * commutesA11
      + ((((9 / 7) : ℂ) + ((3 / 7) : ℂ) * ζ ^ 5 + ((11 / 7) : ℂ) * ζ ^ 10 - ζ ^ 15 - ((3 / 7) : ℂ) * ζ ^ 20 - ((1 / 7) : ℂ) * ζ ^ 25 - ((6 / 7) : ℂ) * ζ ^ 30)) * commutesA14
      - (
        ((-((155 / 308) : ℂ) - ((3811 / 308) : ℂ) * ζ ^ 3 + ((155 / 308) : ℂ) * ζ ^ 4 - ((1971 / 308) : ℂ) * ζ ^ 5 - ((876 / 77) : ℂ) * ζ ^ 6 - ((1117 / 77) : ℂ) * ζ ^ 8 + ((1971 / 308) : ℂ) * ζ ^ 9 - ((353 / 154) : ℂ) * ζ ^ 10 + ((571 / 154) : ℂ) * ζ ^ 13 - ((1399 / 154) : ℂ) * ζ ^ 14 - ((723 / 308) : ℂ) * ζ ^ 15 + ((1311 / 308) : ℂ) * ζ ^ 18 + ((723 / 308) : ℂ) * ζ ^ 19 - ((281 / 308) : ℂ) * ζ ^ 20 + ((876 / 77) : ℂ) * ζ ^ 22 + ((937 / 77) : ℂ) * ζ ^ 23 + ((281 / 308) : ℂ) * ζ ^ 24 + ((1695 / 154) : ℂ) * ζ ^ 25 + ((876 / 77) : ℂ) * ζ ^ 26 + ((1668 / 77) : ℂ) * ζ ^ 28 - ((1695 / 154) : ℂ) * ζ ^ 29 - ((876 / 77) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((2 / 11) : ℂ) + ((983 / 77) : ℂ) * ζ ^ 3 - ((2 / 11) : ℂ) * ζ ^ 4 + ((512 / 77) : ℂ) * ζ ^ 5 + ((909 / 77) : ℂ) * ζ ^ 6 + ((2157 / 154) : ℂ) * ζ ^ 8 - ((512 / 77) : ℂ) * ζ ^ 9 + ((171 / 77) : ℂ) * ζ ^ 10 - ((269 / 77) : ℂ) * ζ ^ 13 + ((738 / 77) : ℂ) * ζ ^ 14 + ((323 / 154) : ℂ) * ζ ^ 15 - ((358 / 77) : ℂ) * ζ ^ 18 - ((323 / 154) : ℂ) * ζ ^ 19 + ((113 / 154) : ℂ) * ζ ^ 20 - ((909 / 77) : ℂ) * ζ ^ 22 - ((992 / 77) : ℂ) * ζ ^ 23 - ((113 / 154) : ℂ) * ζ ^ 24 - ((1739 / 154) : ℂ) * ζ ^ 25 - ((909 / 77) : ℂ) * ζ ^ 26 - ((1679 / 77) : ℂ) * ζ ^ 28 + ((1739 / 154) : ℂ) * ζ ^ 29 + ((909 / 77) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((((5233 / 308) : ℂ) + ((7341 / 308) : ℂ) * ζ ^ 3 - ((5233 / 308) : ℂ) * ζ ^ 4 + ((4747 / 308) : ℂ) * ζ ^ 5 + ((27 / 14) : ℂ) * ζ ^ 6 + ((4357 / 308) : ℂ) * ζ ^ 8 - ((4747 / 308) : ℂ) * ζ ^ 9 + ((3327 / 308) : ℂ) * ζ ^ 10 + ((1084 / 77) : ℂ) * ζ ^ 13 - ((2733 / 308) : ℂ) * ζ ^ 14 + ((794 / 77) : ℂ) * ζ ^ 15 + ((2841 / 308) : ℂ) * ζ ^ 18 - ((794 / 77) : ℂ) * ζ ^ 19 - ((39 / 7) : ℂ) * ζ ^ 20 - ((27 / 14) : ℂ) * ζ ^ 22 - ((2449 / 308) : ℂ) * ζ ^ 23 + ((39 / 7) : ℂ) * ζ ^ 24 - ((516 / 77) : ℂ) * ζ ^ 25 - ((27 / 14) : ℂ) * ζ ^ 26 - ((57 / 7) : ℂ) * ζ ^ 28 + ((516 / 77) : ℂ) * ζ ^ 29 + ((27 / 14) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((((25 / 308) : ℂ) - ((809 / 308) : ℂ) * ζ ^ 3 - ((25 / 308) : ℂ) * ζ ^ 4 - ((5 / 22) : ℂ) * ζ ^ 5 - ((173 / 77) : ℂ) * ζ ^ 6 - ((1021 / 308) : ℂ) * ζ ^ 8 + ((5 / 22) : ℂ) * ζ ^ 9 - ((207 / 154) : ℂ) * ζ ^ 10 - ((955 / 308) : ℂ) * ζ ^ 13 - ((139 / 154) : ℂ) * ζ ^ 14 + ((293 / 308) : ℂ) * ζ ^ 15 - ((79 / 154) : ℂ) * ζ ^ 18 - ((293 / 308) : ℂ) * ζ ^ 19 - ((193 / 154) : ℂ) * ζ ^ 20 + ((173 / 77) : ℂ) * ζ ^ 22 + ((26 / 77) : ℂ) * ζ ^ 23 + ((193 / 154) : ℂ) * ζ ^ 24 - ((390 / 77) : ℂ) * ζ ^ 25 + ((173 / 77) : ℂ) * ζ ^ 26 - ((467 / 154) : ℂ) * ζ ^ 28 + ((390 / 77) : ℂ) * ζ ^ 29 - ((173 / 77) : ℂ) * ζ ^ 30)) * Y 2 1
        + ((-((37 / 42) : ℂ) + ((43 / 42) : ℂ) * ζ ^ 3 + ((37 / 42) : ℂ) * ζ ^ 4 + ((1 / 42) : ℂ) * ζ ^ 5 + ((4 / 7) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((1 / 42) : ℂ) * ζ ^ 9 + ((3 / 14) : ℂ) * ζ ^ 10 + ((2 / 7) : ℂ) * ζ ^ 13 + ((5 / 14) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 15 - ((11 / 42) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 19 - ((5 / 21) : ℂ) * ζ ^ 20 - ((4 / 7) : ℂ) * ζ ^ 22 - ((6 / 7) : ℂ) * ζ ^ 23 + ((5 / 21) : ℂ) * ζ ^ 24 - ((5 / 21) : ℂ) * ζ ^ 25 - ((4 / 7) : ℂ) * ζ ^ 26 - ((2 / 21) : ℂ) * ζ ^ 28 + ((5 / 21) : ℂ) * ζ ^ 29 + ((4 / 7) : ℂ) * ζ ^ 30)) * Y 3 4
        + ((((9 / 28) : ℂ) - ((11 / 28) : ℂ) * ζ ^ 3 - ((9 / 28) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 5 - ((3 / 7) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 9 + ((1 / 14) : ℂ) * ζ ^ 10 - ((3 / 14) : ℂ) * ζ ^ 13 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 4) : ℂ) * ζ ^ 15 + ((11 / 28) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 19 + ((5 / 28) : ℂ) * ζ ^ 20 + ((3 / 7) : ℂ) * ζ ^ 22 + ((5 / 7) : ℂ) * ζ ^ 23 - ((5 / 28) : ℂ) * ζ ^ 24 + ((2 / 7) : ℂ) * ζ ^ 25 + ((3 / 7) : ℂ) * ζ ^ 26 + ((1 / 7) : ℂ) * ζ ^ 28 - ((2 / 7) : ℂ) * ζ ^ 29 - ((3 / 7) : ℂ) * ζ ^ 30)) * Y 4 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row14_reducedY43
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow14TransformedGeneratorA =
        alternatingSixAmbientRow14TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow14GeneratorBDiagonal =
        alternatingSixAmbientRow14GeneratorBDiagonal * Y) :
    Y 4 3 = 0 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 3 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY23,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51,
      hY53] at commutesA01
  have commutesA03 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (3 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA03
  simp only [Fin.sum_univ_succ] at commutesA03
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA03
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY23,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51,
      hY53] at commutesA03
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY23,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51,
      hY53] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY23,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51,
      hY53] at commutesA11
  have commutesA13 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (3 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA13
  simp only [Fin.sum_univ_succ] at commutesA13
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA13
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY23,
      hY30,
      hY31,
      hY40,
      hY41,
      hY50,
      hY51,
      hY53] at commutesA13

  linear_combination
    ((((100 / 7) : ℂ) + ((170 / 21) : ℂ) * ζ ^ 3 + ((152 / 21) : ℂ) * ζ ^ 5 + ((170 / 21) : ℂ) * ζ ^ 7 + ((314 / 21) : ℂ) * ζ ^ 10 - ((10 / 21) : ℂ) * ζ ^ 15 - ((170 / 21) : ℂ) * ζ ^ 19 - ((10 / 7) : ℂ) * ζ ^ 20 - ((170 / 21) : ℂ) * ζ ^ 23 - ((46 / 21) : ℂ) * ζ ^ 25 - ((184 / 21) : ℂ) * ζ ^ 30 + ((170 / 21) : ℂ) * ζ ^ 31)) * commutesA01
      + ((((10 / 7) : ℂ) + ((4 / 7) : ℂ) * ζ ^ 3 + ((4 / 7) : ℂ) * ζ ^ 7 - ((6 / 7) : ℂ) * ζ ^ 10 - ((6 / 7) : ℂ) * ζ ^ 15 - ((4 / 7) : ℂ) * ζ ^ 19 + ((6 / 7) : ℂ) * ζ ^ 20 - ((4 / 7) : ℂ) * ζ ^ 23 + ((2 / 7) : ℂ) * ζ ^ 30 + ((4 / 7) : ℂ) * ζ ^ 31)) * commutesA03
      + ((-((46 / 3) : ℂ) - ((388 / 21) : ℂ) * ζ ^ 3 - ((386 / 21) : ℂ) * ζ ^ 5 - ((388 / 21) : ℂ) * ζ ^ 7 - ((74 / 7) : ℂ) * ζ ^ 10 + ((92 / 21) : ℂ) * ζ ^ 15 + ((388 / 21) : ℂ) * ζ ^ 19 + ((44 / 3) : ℂ) * ζ ^ 20 + ((388 / 21) : ℂ) * ζ ^ 23 + ((292 / 21) : ℂ) * ζ ^ 25 + ((132 / 7) : ℂ) * ζ ^ 30 - ((388 / 21) : ℂ) * ζ ^ 31)) * commutesA10
      + ((-((121 / 21) : ℂ) - ((13 / 21) : ℂ) * ζ ^ 3 - ((68 / 21) : ℂ) * ζ ^ 5 - ((13 / 21) : ℂ) * ζ ^ 7 - (9 : ℂ) * ζ ^ 10 - ((82 / 21) : ℂ) * ζ ^ 15 + ((13 / 21) : ℂ) * ζ ^ 19 - ((67 / 21) : ℂ) * ζ ^ 20 + ((13 / 21) : ℂ) * ζ ^ 23 - ((59 / 21) : ℂ) * ζ ^ 25 + (2 : ℂ) * ζ ^ 30 - ((13 / 21) : ℂ) * ζ ^ 31)) * commutesA11
      + ((((5 / 7) : ℂ) - ((1 / 7) : ℂ) * ζ ^ 3 + ((6 / 7) : ℂ) * ζ ^ 5 - ((1 / 7) : ℂ) * ζ ^ 7 + ((13 / 7) : ℂ) * ζ ^ 10 - ((2 / 7) : ℂ) * ζ ^ 15 + ((1 / 7) : ℂ) * ζ ^ 19 + ((3 / 7) : ℂ) * ζ ^ 20 + ((1 / 7) : ℂ) * ζ ^ 23 - ((9 / 7) : ℂ) * ζ ^ 25 - ((2 / 7) : ℂ) * ζ ^ 30 - ((1 / 7) : ℂ) * ζ ^ 31)) * commutesA13
      - (
        ((((61 / 77) : ℂ) + ((1789 / 231) : ℂ) * ζ ^ 3 - ((61 / 77) : ℂ) * ζ ^ 4 + ((2609 / 462) : ℂ) * ζ ^ 5 + ((1234 / 231) : ℂ) * ζ ^ 6 + ((111 / 14) : ℂ) * ζ ^ 8 - ((2609 / 462) : ℂ) * ζ ^ 9 - ((37 / 42) : ℂ) * ζ ^ 10 + ((1945 / 462) : ℂ) * ζ ^ 13 + ((2875 / 462) : ℂ) * ζ ^ 14 + ((397 / 66) : ℂ) * ζ ^ 15 - ((251 / 462) : ℂ) * ζ ^ 18 - ((397 / 66) : ℂ) * ζ ^ 19 - ((584 / 231) : ℂ) * ζ ^ 20 - ((1234 / 231) : ℂ) * ζ ^ 22 - ((415 / 231) : ℂ) * ζ ^ 23 + ((584 / 231) : ℂ) * ζ ^ 24 - ((1172 / 231) : ℂ) * ζ ^ 25 - ((1234 / 231) : ℂ) * ζ ^ 26 - ((2627 / 231) : ℂ) * ζ ^ 28 + ((1172 / 231) : ℂ) * ζ ^ 29 + ((1234 / 231) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((-((421 / 462) : ℂ) - ((2020 / 231) : ℂ) * ζ ^ 3 + ((421 / 462) : ℂ) * ζ ^ 4 - ((1387 / 231) : ℂ) * ζ ^ 5 - ((1322 / 231) : ℂ) * ζ ^ 6 - ((353 / 42) : ℂ) * ζ ^ 8 + ((1387 / 231) : ℂ) * ζ ^ 9 + ((37 / 42) : ℂ) * ζ ^ 10 - ((934 / 231) : ℂ) * ζ ^ 13 - ((1017 / 154) : ℂ) * ζ ^ 14 - ((787 / 154) : ℂ) * ζ ^ 15 + ((201 / 154) : ℂ) * ζ ^ 18 + ((787 / 154) : ℂ) * ζ ^ 19 + ((1025 / 462) : ℂ) * ζ ^ 20 + ((1322 / 231) : ℂ) * ζ ^ 22 + ((481 / 231) : ℂ) * ζ ^ 23 - ((1025 / 462) : ℂ) * ζ ^ 24 + ((398 / 77) : ℂ) * ζ ^ 25 + ((1322 / 231) : ℂ) * ζ ^ 26 + ((2638 / 231) : ℂ) * ζ ^ 28 - ((398 / 77) : ℂ) * ζ ^ 29 - ((1322 / 231) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((137 / 14) : ℂ) - ((4979 / 462) : ℂ) * ζ ^ 3 + ((137 / 14) : ℂ) * ζ ^ 4 - ((1227 / 154) : ℂ) * ζ ^ 5 - ((53 / 462) : ℂ) * ζ ^ 6 - ((1402 / 231) : ℂ) * ζ ^ 8 + ((1227 / 154) : ℂ) * ζ ^ 9 - ((563 / 154) : ℂ) * ζ ^ 10 - ((1294 / 231) : ℂ) * ζ ^ 13 + ((818 / 231) : ℂ) * ζ ^ 14 - ((2669 / 462) : ℂ) * ζ ^ 15 - ((59 / 14) : ℂ) * ζ ^ 18 + ((2669 / 462) : ℂ) * ζ ^ 19 + ((1121 / 231) : ℂ) * ζ ^ 20 + ((53 / 462) : ℂ) * ζ ^ 22 + ((659 / 231) : ℂ) * ζ ^ 23 - ((1121 / 231) : ℂ) * ζ ^ 24 + ((326 / 77) : ℂ) * ζ ^ 25 + ((53 / 462) : ℂ) * ζ ^ 26 + ((97 / 21) : ℂ) * ζ ^ 28 - ((326 / 77) : ℂ) * ζ ^ 29 - ((53 / 462) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((-((67 / 132) : ℂ) + ((3 / 7) : ℂ) * ζ ^ 3 + ((67 / 132) : ℂ) * ζ ^ 4 - ((87 / 154) : ℂ) * ζ ^ 5 - ((1 / 924) : ℂ) * ζ ^ 6 - ((17 / 308) : ℂ) * ζ ^ 8 + ((87 / 154) : ℂ) * ζ ^ 9 - ((521 / 924) : ℂ) * ζ ^ 10 + ((425 / 231) : ℂ) * ζ ^ 13 + ((130 / 231) : ℂ) * ζ ^ 14 - ((305 / 462) : ℂ) * ζ ^ 15 + ((181 / 308) : ℂ) * ζ ^ 18 + ((305 / 462) : ℂ) * ζ ^ 19 - ((193 / 462) : ℂ) * ζ ^ 20 + ((1 / 924) : ℂ) * ζ ^ 22 - ((5 / 21) : ℂ) * ζ ^ 23 + ((193 / 462) : ℂ) * ζ ^ 24 + ((125 / 77) : ℂ) * ζ ^ 25 + ((1 / 924) : ℂ) * ζ ^ 26 + ((40 / 33) : ℂ) * ζ ^ 28 - ((125 / 77) : ℂ) * ζ ^ 29 - ((1 / 924) : ℂ) * ζ ^ 30)) * Y 2 1
        + ((((5 / 42) : ℂ) + ζ ^ 3 - ((5 / 42) : ℂ) * ζ ^ 4 + ((5 / 14) : ℂ) * ζ ^ 5 + ((8 / 21) : ℂ) * ζ ^ 6 + ((10 / 21) : ℂ) * ζ ^ 8 - ((5 / 14) : ℂ) * ζ ^ 9 - ((1 / 6) : ℂ) * ζ ^ 13 + ((8 / 21) : ℂ) * ζ ^ 14 - ((19 / 21) : ℂ) * ζ ^ 15 - ((16 / 21) : ℂ) * ζ ^ 18 + ((19 / 21) : ℂ) * ζ ^ 19 + ((13 / 42) : ℂ) * ζ ^ 20 - ((8 / 21) : ℂ) * ζ ^ 22 - ((2 / 7) : ℂ) * ζ ^ 23 - ((13 / 42) : ℂ) * ζ ^ 24 - ((2 / 21) : ℂ) * ζ ^ 25 - ((8 / 21) : ℂ) * ζ ^ 26 - ((1 / 21) : ℂ) * ζ ^ 28 + ((2 / 21) : ℂ) * ζ ^ 29 + ((8 / 21) : ℂ) * ζ ^ 30)) * Y 3 3
        + ((-((23 / 28) : ℂ) - ((4 / 7) : ℂ) * ζ ^ 3 + ((23 / 28) : ℂ) * ζ ^ 4 - ((1 / 7) : ℂ) * ζ ^ 5 - ((9 / 28) : ℂ) * ζ ^ 6 - ((3 / 4) : ℂ) * ζ ^ 8 + ((1 / 7) : ℂ) * ζ ^ 9 - ((1 / 28) : ℂ) * ζ ^ 10 + ((4 / 7) : ℂ) * ζ ^ 13 - ((2 / 7) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 15 + ((17 / 28) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 19 + ((1 / 14) : ℂ) * ζ ^ 20 + ((9 / 28) : ℂ) * ζ ^ 22 + ((3 / 14) : ℂ) * ζ ^ 23 - ((1 / 14) : ℂ) * ζ ^ 24 + ((1 / 14) : ℂ) * ζ ^ 25 + ((9 / 28) : ℂ) * ζ ^ 26 + ((1 / 14) : ℂ) * ζ ^ 28 - ((1 / 14) : ℂ) * ζ ^ 29 - ((9 / 28) : ℂ) * ζ ^ 30)) * Y 4 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row14_reducedY44
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow14TransformedGeneratorA =
        alternatingSixAmbientRow14TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow14GeneratorBDiagonal =
        alternatingSixAmbientRow14GeneratorBDiagonal * Y) :
    Y 4 4 = Y 5 5 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY54 :
      Y 5 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 4 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY24,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51,
      hY54] at commutesA01
  have commutesA04 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (4 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA04
  simp only [Fin.sum_univ_succ] at commutesA04
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA04
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY24,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51,
      hY54] at commutesA04
  have commutesA05 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA05
  simp only [Fin.sum_univ_succ] at commutesA05
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA05
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY24,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51,
      hY54] at commutesA05
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY24,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51,
      hY54] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY24,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51,
      hY54] at commutesA11
  have commutesA14 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (4 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA14
  simp only [Fin.sum_univ_succ] at commutesA14
  simp [
      alternatingSixAmbientRow14TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA14
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY24,
      hY25,
      hY30,
      hY31,
      hY35,
      hY40,
      hY41,
      hY45,
      hY50,
      hY51,
      hY54] at commutesA14

  linear_combination
    ((-((208 / 7) : ℂ) - ((130 / 7) : ℂ) * ζ ^ 3 - ((192 / 7) : ℂ) * ζ ^ 5 - ((130 / 7) : ℂ) * ζ ^ 7 - ((194 / 7) : ℂ) * ζ ^ 10 - ((22 / 7) : ℂ) * ζ ^ 15 + ((130 / 7) : ℂ) * ζ ^ 19 + ((60 / 7) : ℂ) * ζ ^ 20 + ((130 / 7) : ℂ) * ζ ^ 23 + ((64 / 7) : ℂ) * ζ ^ 25 + ((130 / 7) : ℂ) * ζ ^ 30 - ((130 / 7) : ℂ) * ζ ^ 31)) * commutesA01
      + ((((10 / 7) : ℂ) + ((4 / 7) : ℂ) * ζ ^ 3 + ((4 / 7) : ℂ) * ζ ^ 7 - ((6 / 7) : ℂ) * ζ ^ 10 - ((6 / 7) : ℂ) * ζ ^ 15 - ((4 / 7) : ℂ) * ζ ^ 19 + ((6 / 7) : ℂ) * ζ ^ 20 - ((4 / 7) : ℂ) * ζ ^ 23 + ((2 / 7) : ℂ) * ζ ^ 30 + ((4 / 7) : ℂ) * ζ ^ 31)) * commutesA04
      + ((-(2 : ℂ) - (2 : ℂ) * ζ ^ 3 - (2 : ℂ) * ζ ^ 7 - (2 : ℂ) * ζ ^ 10 + (2 : ℂ) * ζ ^ 19 + (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 23 + (2 : ℂ) * ζ ^ 25 - (2 : ℂ) * ζ ^ 31)) * commutesA05
      + (((35 : ℂ) + ((303 / 7) : ℂ) * ζ ^ 3 + ((262 / 7) : ℂ) * ζ ^ 5 + ((303 / 7) : ℂ) * ζ ^ 7 + ((169 / 7) : ℂ) * ζ ^ 10 - ((150 / 7) : ℂ) * ζ ^ 15 - ((303 / 7) : ℂ) * ζ ^ 19 - (29 : ℂ) * ζ ^ 20 - ((303 / 7) : ℂ) * ζ ^ 23 - ((267 / 7) : ℂ) * ζ ^ 25 - ((264 / 7) : ℂ) * ζ ^ 30 + ((303 / 7) : ℂ) * ζ ^ 31)) * commutesA10
      + ((((81 / 7) : ℂ) + ((26 / 7) : ℂ) * ζ ^ 3 + ((87 / 7) : ℂ) * ζ ^ 5 + ((26 / 7) : ℂ) * ζ ^ 7 + (16 : ℂ) * ζ ^ 10 + ((87 / 7) : ℂ) * ζ ^ 15 - ((26 / 7) : ℂ) * ζ ^ 19 + ((36 / 7) : ℂ) * ζ ^ 20 - ((26 / 7) : ℂ) * ζ ^ 23 + ((27 / 7) : ℂ) * ζ ^ 25 - (3 : ℂ) * ζ ^ 30 + ((26 / 7) : ℂ) * ζ ^ 31)) * commutesA11
      + ((((5 / 7) : ℂ) - ((1 / 7) : ℂ) * ζ ^ 3 + ((6 / 7) : ℂ) * ζ ^ 5 - ((1 / 7) : ℂ) * ζ ^ 7 + ((13 / 7) : ℂ) * ζ ^ 10 - ((2 / 7) : ℂ) * ζ ^ 15 + ((1 / 7) : ℂ) * ζ ^ 19 + ((3 / 7) : ℂ) * ζ ^ 20 + ((1 / 7) : ℂ) * ζ ^ 23 - ((9 / 7) : ℂ) * ζ ^ 25 - ((2 / 7) : ℂ) * ζ ^ 30 - ((1 / 7) : ℂ) * ζ ^ 31)) * commutesA14
      - (
        ((-((823 / 308) : ℂ) - ((1510 / 77) : ℂ) * ζ ^ 3 + ((823 / 308) : ℂ) * ζ ^ 4 - ((71 / 7) : ℂ) * ζ ^ 5 - ((597 / 44) : ℂ) * ζ ^ 6 - ((6113 / 308) : ℂ) * ζ ^ 8 + ((71 / 7) : ℂ) * ζ ^ 9 - ((965 / 308) : ℂ) * ζ ^ 10 - ((368 / 77) : ℂ) * ζ ^ 13 - ((1607 / 154) : ℂ) * ζ ^ 14 - ((1051 / 154) : ℂ) * ζ ^ 15 - ((3 / 28) : ℂ) * ζ ^ 18 + ((1051 / 154) : ℂ) * ζ ^ 19 - ((1 / 2) : ℂ) * ζ ^ 20 + ((597 / 44) : ℂ) * ζ ^ 22 + ((800 / 77) : ℂ) * ζ ^ 23 + ((1 / 2) : ℂ) * ζ ^ 24 + ((1109 / 77) : ℂ) * ζ ^ 25 + ((597 / 44) : ℂ) * ζ ^ 26 + ((3543 / 154) : ℂ) * ζ ^ 28 - ((1109 / 77) : ℂ) * ζ ^ 29 - ((597 / 44) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((192 / 77) : ℂ) + ((433 / 22) : ℂ) * ζ ^ 3 - ((192 / 77) : ℂ) * ζ ^ 4 + ((72 / 7) : ℂ) * ζ ^ 5 + ((1031 / 77) : ℂ) * ζ ^ 6 + ((1509 / 77) : ℂ) * ζ ^ 8 - ((72 / 7) : ℂ) * ζ ^ 9 + ((244 / 77) : ℂ) * ζ ^ 10 + ((324 / 77) : ℂ) * ζ ^ 13 + ((787 / 77) : ℂ) * ζ ^ 14 + ((487 / 77) : ℂ) * ζ ^ 15 - ((487 / 77) : ℂ) * ζ ^ 19 - ((1 / 14) : ℂ) * ζ ^ 20 - ((1031 / 77) : ℂ) * ζ ^ 22 - ((778 / 77) : ℂ) * ζ ^ 23 + ((1 / 14) : ℂ) * ζ ^ 24 - ((1076 / 77) : ℂ) * ζ ^ 25 - ((1031 / 77) : ℂ) * ζ ^ 26 - ((1777 / 77) : ℂ) * ζ ^ 28 + ((1076 / 77) : ℂ) * ζ ^ 29 + ((1031 / 77) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((((6793 / 308) : ℂ) + ((3937 / 154) : ℂ) * ζ ^ 3 - ((6793 / 308) : ℂ) * ζ ^ 4 + ((1399 / 77) : ℂ) * ζ ^ 5 + ((117 / 154) : ℂ) * ζ ^ 6 + ((1136 / 77) : ℂ) * ζ ^ 8 - ((1399 / 77) : ℂ) * ζ ^ 9 + ((2923 / 308) : ℂ) * ζ ^ 10 + ((1901 / 154) : ℂ) * ζ ^ 13 - ((2689 / 308) : ℂ) * ζ ^ 14 + ((930 / 77) : ℂ) * ζ ^ 15 + ((843 / 77) : ℂ) * ζ ^ 18 - ((930 / 77) : ℂ) * ζ ^ 19 - ((2913 / 308) : ℂ) * ζ ^ 20 - ((117 / 154) : ℂ) * ζ ^ 22 - ((687 / 77) : ℂ) * ζ ^ 23 + ((2913 / 308) : ℂ) * ζ ^ 24 - ((786 / 77) : ℂ) * ζ ^ 25 - ((117 / 154) : ℂ) * ζ ^ 26 - ((66 / 7) : ℂ) * ζ ^ 28 + ((786 / 77) : ℂ) * ζ ^ 29 + ((117 / 154) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((((51 / 44) : ℂ) - ((351 / 308) : ℂ) * ζ ^ 3 - ((51 / 44) : ℂ) * ζ ^ 4 + ((449 / 308) : ℂ) * ζ ^ 5 - ((52 / 77) : ℂ) * ζ ^ 6 - ((17 / 14) : ℂ) * ζ ^ 8 - ((449 / 308) : ℂ) * ζ ^ 9 + ((293 / 308) : ℂ) * ζ ^ 10 - ((761 / 308) : ℂ) * ζ ^ 13 - ((501 / 308) : ℂ) * ζ ^ 14 + ((331 / 308) : ℂ) * ζ ^ 15 - ((291 / 154) : ℂ) * ζ ^ 18 - ((331 / 308) : ℂ) * ζ ^ 19 + ((135 / 308) : ℂ) * ζ ^ 20 + ((52 / 77) : ℂ) * ζ ^ 22 - ((15 / 308) : ℂ) * ζ ^ 23 - ((135 / 308) : ℂ) * ζ ^ 24 - ((949 / 308) : ℂ) * ζ ^ 25 + ((52 / 77) : ℂ) * ζ ^ 26 - ((59 / 22) : ℂ) * ζ ^ 28 + ((949 / 308) : ℂ) * ζ ^ 29 - ((52 / 77) : ℂ) * ζ ^ 30)) * Y 2 1
        + ((((5 / 42) : ℂ) + ζ ^ 3 - ((5 / 42) : ℂ) * ζ ^ 4 + ((5 / 14) : ℂ) * ζ ^ 5 + ((8 / 21) : ℂ) * ζ ^ 6 + ((10 / 21) : ℂ) * ζ ^ 8 - ((5 / 14) : ℂ) * ζ ^ 9 - ((1 / 6) : ℂ) * ζ ^ 13 + ((8 / 21) : ℂ) * ζ ^ 14 - ((19 / 21) : ℂ) * ζ ^ 15 - ((16 / 21) : ℂ) * ζ ^ 18 + ((19 / 21) : ℂ) * ζ ^ 19 + ((13 / 42) : ℂ) * ζ ^ 20 - ((8 / 21) : ℂ) * ζ ^ 22 - ((2 / 7) : ℂ) * ζ ^ 23 - ((13 / 42) : ℂ) * ζ ^ 24 - ((2 / 21) : ℂ) * ζ ^ 25 - ((8 / 21) : ℂ) * ζ ^ 26 - ((1 / 21) : ℂ) * ζ ^ 28 + ((2 / 21) : ℂ) * ζ ^ 29 + ((8 / 21) : ℂ) * ζ ^ 30)) * Y 3 4
        + ((-((23 / 28) : ℂ) - ((4 / 7) : ℂ) * ζ ^ 3 + ((23 / 28) : ℂ) * ζ ^ 4 - ((1 / 7) : ℂ) * ζ ^ 5 - ((9 / 28) : ℂ) * ζ ^ 6 - ((3 / 4) : ℂ) * ζ ^ 8 + ((1 / 7) : ℂ) * ζ ^ 9 - ((1 / 28) : ℂ) * ζ ^ 10 + ((4 / 7) : ℂ) * ζ ^ 13 - ((2 / 7) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 15 + ((17 / 28) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 19 + ((1 / 14) : ℂ) * ζ ^ 20 + ((9 / 28) : ℂ) * ζ ^ 22 + ((3 / 14) : ℂ) * ζ ^ 23 - ((1 / 14) : ℂ) * ζ ^ 24 + ((1 / 14) : ℂ) * ζ ^ 25 + ((9 / 28) : ℂ) * ζ ^ 26 + ((1 / 14) : ℂ) * ζ ^ 28 - ((1 / 14) : ℂ) * ζ ^ 29 - ((9 / 28) : ℂ) * ζ ^ 30)) * Y 4 4
        + (((1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 3 - ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 6 + ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 25 - ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 29 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation


/-- A matrix commuting with both transformed row 14 generators is
scalar. -/
theorem alternatingSixAmbientRow14Transformed_scalar_commutant
    (Y : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow14TransformedGeneratorA =
        alternatingSixAmbientRow14TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow14GeneratorBDiagonal =
        alternatingSixAmbientRow14GeneratorBDiagonal * Y) :
    ∃ c : ℂ,
      Y = c • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 3 (by decide)
  have hY54 :
      Y 5 4 = 0 :=
    alternatingSixAmbientRow14_off_block
      Y commutesDiagonal 5 4 (by decide)

  have reducedY00 : Y 0 0 = Y 5 5 :=
    row14_reducedY00 Y commutesA commutesDiagonal
  have reducedY11 : Y 1 1 = Y 5 5 :=
    row14_reducedY11 Y commutesA commutesDiagonal
  have reducedY12 : Y 1 2 = 0 :=
    row14_reducedY12 Y commutesA commutesDiagonal
  have reducedY21 : Y 2 1 = 0 :=
    row14_reducedY21 Y commutesA commutesDiagonal
  have reducedY22 : Y 2 2 = Y 5 5 :=
    row14_reducedY22 Y commutesA commutesDiagonal
  have reducedY33 : Y 3 3 = Y 5 5 :=
    row14_reducedY33 Y commutesA commutesDiagonal
  have reducedY34 : Y 3 4 = 0 :=
    row14_reducedY34 Y commutesA commutesDiagonal
  have reducedY43 : Y 4 3 = 0 :=
    row14_reducedY43 Y commutesA commutesDiagonal
  have reducedY44 : Y 4 4 = Y 5 5 :=
    row14_reducedY44 Y commutesA commutesDiagonal

  refine ⟨Y 5 5, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY23,
      hY24,
      hY25,
      hY30,
      hY31,
      hY32,
      hY35,
      hY40,
      hY41,
      hY42,
      hY45,
      hY50,
      hY51,
      hY52,
      hY53,
      hY54,
      reducedY00,
      reducedY11,
      reducedY12,
      reducedY21,
      reducedY22,
      reducedY33,
      reducedY34,
      reducedY43,
      reducedY44]

/-- Every matrix commuting with both original row 14 presentation
generators is scalar. -/
theorem alternatingSixAmbientRow14_scalar_commutant
    (X : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesA :
      X * alternatingSixFiveAmbient_row14_matrixA =
        alternatingSixFiveAmbient_row14_matrixA * X)
    (commutesB :
      X * alternatingSixFiveAmbient_row14_matrixB =
        alternatingSixFiveAmbient_row14_matrixB * X) :
    ∃ c : ℂ,
      X = c • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  apply Matrix.scalar_commutant_of_diagonal_basis
    alternatingSixFiveAmbient_row14_matrixA
    alternatingSixFiveAmbient_row14_matrixB
    alternatingSixAmbientRow14Eigenbasis
    alternatingSixAmbientRow14EigenbasisInverse
    alternatingSixAmbientRow14TransformedGeneratorA
    alternatingSixAmbientRow14GeneratorBEigenvalue
    alternatingSixAmbientRow14EigenbasisInverse_mul
    alternatingSixAmbientRow14Eigenbasis_mul_inverse
    alternatingSixAmbientRow14GeneratorB_mul_eigenbasis
    alternatingSixAmbientRow14TransformedGeneratorA_eq
    alternatingSixAmbientRow14Transformed_scalar_commutant
    X commutesA commutesB

end InductiveMcKay
end McKayConjecture
