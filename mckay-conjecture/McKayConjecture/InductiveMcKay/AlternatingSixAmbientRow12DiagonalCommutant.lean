/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DiagonalBasisMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow12DiagonalData

/-!
# Scalar common commutant for ambient row 12

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
private theorem alternatingSixAmbientRow12_off_block
    (Y : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow12GeneratorBDiagonal =
        alternatingSixAmbientRow12GeneratorBDiagonal * Y)
    (i j : Fin 6)
    (different :
      alternatingSixAmbientRow12EigenvalueLabel i ≠
        alternatingSixAmbientRow12EigenvalueLabel j) :
    Y i j = 0 := by
  apply Matrix.entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
    Y alternatingSixAmbientRow12GeneratorBEigenvalue
  · exact commutesDiagonal
  · intro equalEigenvalues
    apply different
    apply alternatingSixOrderEightOddEigenvalue_injective
    simpa [
      alternatingSixAmbientRow12GeneratorBEigenvalue] using
      equalEigenvalues.symm

private theorem row12_reducedY00
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow12TransformedGeneratorA =
        alternatingSixAmbientRow12TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow12GeneratorBDiagonal =
        alternatingSixAmbientRow12GeneratorBDiagonal * Y) :
    Y 0 0 = Y 5 5 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 5 (by decide)

  have commutesA05 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA05
  simp only [Fin.sum_univ_succ] at commutesA05
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
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
    (((2 : ℂ) * ζ ^ 3 + (2 : ℂ) * ζ ^ 5 + (2 : ℂ) * ζ ^ 7 + (2 : ℂ) * ζ ^ 10 - (2 : ℂ) * ζ ^ 15 - (2 : ℂ) * ζ ^ 19 - (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 23 - (2 : ℂ) * ζ ^ 30 + (2 : ℂ) * ζ ^ 31)) * commutesA05
      - (
        ((-(1 : ℂ) - ((1 / 2) : ℂ) * ζ ^ 3 + ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 5 + ((1 / 2) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 9 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 25 - ((1 / 2) : ℂ) * ζ ^ 26 - ((1 / 2) : ℂ) * ζ ^ 29 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 0
        + (((1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 3 - ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 5 - ((1 / 2) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 9 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 25 + ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 29 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row12_reducedY11
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow12TransformedGeneratorA =
        alternatingSixAmbientRow12TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow12GeneratorBDiagonal =
        alternatingSixAmbientRow12GeneratorBDiagonal * Y) :
    Y 1 1 = Y 5 5 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 1 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY31,
      hY41,
      hY51] at commutesA01
  have commutesA05 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA05
  simp only [Fin.sum_univ_succ] at commutesA05
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
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
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY10,
      hY13,
      hY14,
      hY15,
      hY31,
      hY41,
      hY51] at commutesA11

  linear_combination
    ((((3538 / 97) : ℂ) - ((4840 / 97) : ℂ) * ζ ^ 3 + ((3044 / 97) : ℂ) * ζ ^ 5 - ((4840 / 97) : ℂ) * ζ ^ 7 - ((5126 / 97) : ℂ) * ζ ^ 10 + ((4424 / 97) : ℂ) * ζ ^ 15 + ((4840 / 97) : ℂ) * ζ ^ 19 + ((1804 / 97) : ℂ) * ζ ^ 20 + ((4840 / 97) : ℂ) * ζ ^ 23 - ((5398 / 97) : ℂ) * ζ ^ 25 + ((1010 / 97) : ℂ) * ζ ^ 30 - ((4840 / 97) : ℂ) * ζ ^ 31)) * commutesA01
      + (((2 : ℂ) * ζ ^ 3 + (2 : ℂ) * ζ ^ 5 + (2 : ℂ) * ζ ^ 7 + (2 : ℂ) * ζ ^ 10 - (2 : ℂ) * ζ ^ 15 - (2 : ℂ) * ζ ^ 19 - (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 23 - (2 : ℂ) * ζ ^ 30 + (2 : ℂ) * ζ ^ 31)) * commutesA05
      + ((((1184 / 97) : ℂ) - ((1050 / 97) : ℂ) * ζ ^ 3 + ((286 / 97) : ℂ) * ζ ^ 5 - ((1050 / 97) : ℂ) * ζ ^ 7 - ((1478 / 97) : ℂ) * ζ ^ 10 + ((1274 / 97) : ℂ) * ζ ^ 15 + ((1050 / 97) : ℂ) * ζ ^ 19 + ((118 / 97) : ℂ) * ζ ^ 20 + ((1050 / 97) : ℂ) * ζ ^ 23 - ((1436 / 97) : ℂ) * ζ ^ 25 + ((650 / 97) : ℂ) * ζ ^ 30 - ((1050 / 97) : ℂ) * ζ ^ 31)) * commutesA10
      + ((-((1216 / 97) : ℂ) + ((984 / 97) : ℂ) * ζ ^ 3 - ((472 / 97) : ℂ) * ζ ^ 5 + ((984 / 97) : ℂ) * ζ ^ 7 + ((1282 / 97) : ℂ) * ζ ^ 10 - ((1256 / 97) : ℂ) * ζ ^ 15 - ((984 / 97) : ℂ) * ζ ^ 19 - ((74 / 97) : ℂ) * ζ ^ 20 - ((984 / 97) : ℂ) * ζ ^ 23 + ((1328 / 97) : ℂ) * ζ ^ 25 - ((526 / 97) : ℂ) * ζ ^ 30 + ((984 / 97) : ℂ) * ζ ^ 31)) * commutesA11
      - (
        ((-((341 / 97) : ℂ) * ζ ^ 3 + ((3441 / 194) : ℂ) * ζ ^ 5 + ((1467 / 194) : ℂ) * ζ ^ 6 - ((5979 / 194) : ℂ) * ζ ^ 8 - ((3441 / 194) : ℂ) * ζ ^ 9 + ((3976 / 97) : ℂ) * ζ ^ 10 - ((217 / 194) : ℂ) * ζ ^ 13 - ((6485 / 194) : ℂ) * ζ ^ 14 + ((279 / 194) : ℂ) * ζ ^ 15 + ((1301 / 97) : ℂ) * ζ ^ 18 - ((279 / 194) : ℂ) * ζ ^ 19 - ((3683 / 194) : ℂ) * ζ ^ 20 - ((1467 / 194) : ℂ) * ζ ^ 22 - ((505 / 194) : ℂ) * ζ ^ 23 + ((3683 / 194) : ℂ) * ζ ^ 24 - ((24 / 97) : ℂ) * ζ ^ 25 - ((1467 / 194) : ℂ) * ζ ^ 26 + ((24 / 97) : ℂ) * ζ ^ 29 + ((1467 / 194) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((-(1 : ℂ) + ((585 / 194) : ℂ) * ζ ^ 3 + ζ ^ 4 - ((1769 / 97) : ℂ) * ζ ^ 5 - ((685 / 97) : ℂ) * ζ ^ 6 + ((2941 / 97) : ℂ) * ζ ^ 8 + ((1769 / 97) : ℂ) * ζ ^ 9 - ((3976 / 97) : ℂ) * ζ ^ 10 + ((217 / 194) : ℂ) * ζ ^ 13 + ((3291 / 97) : ℂ) * ζ ^ 14 - ((279 / 194) : ℂ) * ζ ^ 15 - ((2699 / 194) : ℂ) * ζ ^ 18 + ((279 / 194) : ℂ) * ζ ^ 19 + ((3683 / 194) : ℂ) * ζ ^ 20 + ((685 / 97) : ℂ) * ζ ^ 22 + ((505 / 194) : ℂ) * ζ ^ 23 - ((3683 / 194) : ℂ) * ζ ^ 24 + ((145 / 194) : ℂ) * ζ ^ 25 + ((685 / 97) : ℂ) * ζ ^ 26 - ((145 / 194) : ℂ) * ζ ^ 29 - ((685 / 97) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((600 / 97) : ℂ) - ((1415 / 194) : ℂ) * ζ ^ 3 + ((600 / 97) : ℂ) * ζ ^ 4 - ((1595 / 194) : ℂ) * ζ ^ 5 + ((984 / 97) : ℂ) * ζ ^ 6 - ((580 / 97) : ℂ) * ζ ^ 8 + ((1595 / 194) : ℂ) * ζ ^ 9 + ((1742 / 97) : ℂ) * ζ ^ 10 + ((477 / 194) : ℂ) * ζ ^ 13 - ((758 / 97) : ℂ) * ζ ^ 14 + ((27 / 97) : ℂ) * ζ ^ 15 - ((6 / 97) : ℂ) * ζ ^ 18 - ((27 / 97) : ℂ) * ζ ^ 19 - ((1481 / 194) : ℂ) * ζ ^ 20 - ((984 / 97) : ℂ) * ζ ^ 22 - ((1111 / 194) : ℂ) * ζ ^ 23 + ((1481 / 194) : ℂ) * ζ ^ 24 + ((1051 / 97) : ℂ) * ζ ^ 25 - ((984 / 97) : ℂ) * ζ ^ 26 + ((325 / 97) : ℂ) * ζ ^ 28 - ((1051 / 97) : ℂ) * ζ ^ 29 + ((984 / 97) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((-((1769 / 194) : ℂ) + ((1259 / 194) : ℂ) * ζ ^ 3 + ((1769 / 194) : ℂ) * ζ ^ 4 - ((1065 / 97) : ℂ) * ζ ^ 5 + ((964 / 97) : ℂ) * ζ ^ 6 - ((2563 / 194) : ℂ) * ζ ^ 8 + ((1065 / 97) : ℂ) * ζ ^ 9 + ((4255 / 194) : ℂ) * ζ ^ 10 - ((104 / 97) : ℂ) * ζ ^ 13 - ((2327 / 194) : ℂ) * ζ ^ 14 + ((849 / 194) : ℂ) * ζ ^ 15 + ((743 / 194) : ℂ) * ζ ^ 18 - ((849 / 194) : ℂ) * ζ ^ 19 - ((519 / 97) : ℂ) * ζ ^ 20 - ((964 / 97) : ℂ) * ζ ^ 22 - ((1218 / 97) : ℂ) * ζ ^ 23 + ((519 / 97) : ℂ) * ζ ^ 24 + ((1331 / 97) : ℂ) * ζ ^ 25 - ((964 / 97) : ℂ) * ζ ^ 26 + ((505 / 194) : ℂ) * ζ ^ 28 - ((1331 / 97) : ℂ) * ζ ^ 29 + ((964 / 97) : ℂ) * ζ ^ 30)) * Y 2 1
        + (((1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 3 - ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 5 - ((1 / 2) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 9 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 25 + ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 29 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row12_reducedY12
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow12TransformedGeneratorA =
        alternatingSixAmbientRow12TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow12GeneratorBDiagonal =
        alternatingSixAmbientRow12GeneratorBDiagonal * Y) :
    Y 1 2 = 0 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 1 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY31,
      hY41,
      hY51] at commutesA01
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY10,
      hY13,
      hY14,
      hY15,
      hY31,
      hY41,
      hY51] at commutesA11

  linear_combination
    ((((2410 / 97) : ℂ) - ((5372 / 97) : ℂ) * ζ ^ 3 + ((4102 / 97) : ℂ) * ζ ^ 5 - ((5372 / 97) : ℂ) * ζ ^ 7 - ((4566 / 97) : ℂ) * ζ ^ 10 + ((3652 / 97) : ℂ) * ζ ^ 15 + ((5372 / 97) : ℂ) * ζ ^ 19 + ((3064 / 97) : ℂ) * ζ ^ 20 + ((5372 / 97) : ℂ) * ζ ^ 23 - ((5228 / 97) : ℂ) * ζ ^ 25 - ((342 / 97) : ℂ) * ζ ^ 30 - ((5372 / 97) : ℂ) * ζ ^ 31)) * commutesA01
      + ((((896 / 97) : ℂ) - ((1256 / 97) : ℂ) * ζ ^ 3 + ((746 / 97) : ℂ) * ζ ^ 5 - ((1256 / 97) : ℂ) * ζ ^ 7 - ((1302 / 97) : ℂ) * ζ ^ 10 + ((1242 / 97) : ℂ) * ζ ^ 15 + ((1256 / 97) : ℂ) * ζ ^ 19 + ((514 / 97) : ℂ) * ζ ^ 20 + ((1256 / 97) : ℂ) * ζ ^ 23 - ((1438 / 97) : ℂ) * ζ ^ 25 + ((214 / 97) : ℂ) * ζ ^ 30 - ((1256 / 97) : ℂ) * ζ ^ 31)) * commutesA10
      + ((-((894 / 97) : ℂ) + ((1248 / 97) : ℂ) * ζ ^ 3 - ((698 / 97) : ℂ) * ζ ^ 5 + ((1248 / 97) : ℂ) * ζ ^ 7 + ((1290 / 97) : ℂ) * ζ ^ 10 - ((1134 / 97) : ℂ) * ζ ^ 15 - ((1248 / 97) : ℂ) * ζ ^ 19 - ((444 / 97) : ℂ) * ζ ^ 20 - ((1248 / 97) : ℂ) * ζ ^ 23 + ((1372 / 97) : ℂ) * ζ ^ 25 - ((246 / 97) : ℂ) * ζ ^ 30 + ((1248 / 97) : ℂ) * ζ ^ 31)) * commutesA11
      - (
        ((-((309 / 194) : ℂ) * ζ ^ 3 + ((1205 / 97) : ℂ) * ζ ^ 5 + ((715 / 97) : ℂ) * ζ ^ 6 - ((6677 / 194) : ℂ) * ζ ^ 8 - ((1205 / 97) : ℂ) * ζ ^ 9 + ((3971 / 97) : ℂ) * ζ ^ 10 - ((1981 / 194) : ℂ) * ζ ^ 13 - ((3256 / 97) : ℂ) * ζ ^ 14 + ((1189 / 194) : ℂ) * ζ ^ 15 + ((1307 / 97) : ℂ) * ζ ^ 18 - ((1189 / 194) : ℂ) * ζ ^ 19 - ((1931 / 97) : ℂ) * ζ ^ 20 - ((715 / 97) : ℂ) * ζ ^ 22 + ((171 / 194) : ℂ) * ζ ^ 23 + ((1931 / 97) : ℂ) * ζ ^ 24 - ((385 / 194) : ℂ) * ζ ^ 25 - ((715 / 97) : ℂ) * ζ ^ 26 + ((385 / 194) : ℂ) * ζ ^ 29 + ((715 / 97) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((309 / 194) : ℂ) * ζ ^ 3 - ((1205 / 97) : ℂ) * ζ ^ 5 - ((715 / 97) : ℂ) * ζ ^ 6 + ((6677 / 194) : ℂ) * ζ ^ 8 + ((1205 / 97) : ℂ) * ζ ^ 9 - ((3971 / 97) : ℂ) * ζ ^ 10 + ((1981 / 194) : ℂ) * ζ ^ 13 + ((3256 / 97) : ℂ) * ζ ^ 14 - ((1189 / 194) : ℂ) * ζ ^ 15 - ((1307 / 97) : ℂ) * ζ ^ 18 + ((1189 / 194) : ℂ) * ζ ^ 19 + ((1931 / 97) : ℂ) * ζ ^ 20 + ((715 / 97) : ℂ) * ζ ^ 22 - ((171 / 194) : ℂ) * ζ ^ 23 - ((1931 / 97) : ℂ) * ζ ^ 24 + ((385 / 194) : ℂ) * ζ ^ 25 + ((715 / 97) : ℂ) * ζ ^ 26 - ((385 / 194) : ℂ) * ζ ^ 29 - ((715 / 97) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((1089 / 194) : ℂ) - ((268 / 97) : ℂ) * ζ ^ 3 + ((1089 / 194) : ℂ) * ζ ^ 4 - ((808 / 97) : ℂ) * ζ ^ 5 + ((1248 / 97) : ℂ) * ζ ^ 6 - ((1237 / 194) : ℂ) * ζ ^ 8 + ((808 / 97) : ℂ) * ζ ^ 9 + ((3541 / 194) : ℂ) * ζ ^ 10 + ((170 / 97) : ℂ) * ζ ^ 13 - ((1045 / 194) : ℂ) * ζ ^ 14 + ((809 / 194) : ℂ) * ζ ^ 15 + ((25 / 194) : ℂ) * ζ ^ 18 - ((809 / 194) : ℂ) * ζ ^ 19 - ((951 / 97) : ℂ) * ζ ^ 20 - ((1248 / 97) : ℂ) * ζ ^ 22 - ((1331 / 194) : ℂ) * ζ ^ 23 + ((951 / 97) : ℂ) * ζ ^ 24 + ((874 / 97) : ℂ) * ζ ^ 25 - ((1248 / 97) : ℂ) * ζ ^ 26 + ((107 / 97) : ℂ) * ζ ^ 28 - ((874 / 97) : ℂ) * ζ ^ 29 + ((1248 / 97) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((-((1205 / 194) : ℂ) + ((964 / 97) : ℂ) * ζ ^ 3 + ((1205 / 194) : ℂ) * ζ ^ 4 - ((1249 / 97) : ℂ) * ζ ^ 5 + ((1031 / 97) : ℂ) * ζ ^ 6 - ((2283 / 194) : ℂ) * ζ ^ 8 + ((1249 / 97) : ℂ) * ζ ^ 9 + ((1998 / 97) : ℂ) * ζ ^ 10 - ((430 / 97) : ℂ) * ζ ^ 13 - ((967 / 97) : ℂ) * ζ ^ 14 + ((1505 / 194) : ℂ) * ζ ^ 15 + ((675 / 194) : ℂ) * ζ ^ 18 - ((1505 / 194) : ℂ) * ζ ^ 19 - ((1475 / 194) : ℂ) * ζ ^ 20 - ((1031 / 97) : ℂ) * ζ ^ 22 - ((2491 / 194) : ℂ) * ζ ^ 23 + ((1475 / 194) : ℂ) * ζ ^ 24 + ((1196 / 97) : ℂ) * ζ ^ 25 - ((1031 / 97) : ℂ) * ζ ^ 26 - ((171 / 194) : ℂ) * ζ ^ 28 - ((1196 / 97) : ℂ) * ζ ^ 29 + ((1031 / 97) : ℂ) * ζ ^ 30)) * Y 2 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row12_reducedY21
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow12TransformedGeneratorA =
        alternatingSixAmbientRow12TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow12GeneratorBDiagonal =
        alternatingSixAmbientRow12GeneratorBDiagonal * Y) :
    Y 2 1 = 0 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 1 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY31,
      hY41,
      hY51] at commutesA01
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY10,
      hY13,
      hY14,
      hY15,
      hY31,
      hY41,
      hY51] at commutesA11

  linear_combination
    ((((2388 / 97) : ℂ) - ((5090 / 97) : ℂ) * ζ ^ 3 + ((3768 / 97) : ℂ) * ζ ^ 5 - ((5090 / 97) : ℂ) * ζ ^ 7 - ((4434 / 97) : ℂ) * ζ ^ 10 + ((3628 / 97) : ℂ) * ζ ^ 15 + ((5090 / 97) : ℂ) * ζ ^ 19 + ((2682 / 97) : ℂ) * ζ ^ 20 + ((5090 / 97) : ℂ) * ζ ^ 23 - ((4890 / 97) : ℂ) * ζ ^ 25 - ((378 / 97) : ℂ) * ζ ^ 30 - ((5090 / 97) : ℂ) * ζ ^ 31)) * commutesA01
      + ((((684 / 97) : ℂ) - ((1184 / 97) : ℂ) * ζ ^ 3 + ((508 / 97) : ℂ) * ζ ^ 5 - ((1184 / 97) : ℂ) * ζ ^ 7 - ((1388 / 97) : ℂ) * ζ ^ 10 + ((1240 / 97) : ℂ) * ζ ^ 15 + ((1184 / 97) : ℂ) * ζ ^ 19 + ((660 / 97) : ℂ) * ζ ^ 20 + ((1184 / 97) : ℂ) * ζ ^ 23 - ((1232 / 97) : ℂ) * ζ ^ 25 + ((308 / 97) : ℂ) * ζ ^ 30 - ((1184 / 97) : ℂ) * ζ ^ 31)) * commutesA10
      + ((-((886 / 97) : ℂ) + ((1022 / 97) : ℂ) * ζ ^ 3 - ((700 / 97) : ℂ) * ζ ^ 5 + ((1022 / 97) : ℂ) * ζ ^ 7 + ((1242 / 97) : ℂ) * ζ ^ 10 - ((896 / 97) : ℂ) * ζ ^ 15 - ((1022 / 97) : ℂ) * ζ ^ 19 - ((358 / 97) : ℂ) * ζ ^ 20 - ((1022 / 97) : ℂ) * ζ ^ 23 + ((1302 / 97) : ℂ) * ζ ^ 25 - ((180 / 97) : ℂ) * ζ ^ 30 + ((1022 / 97) : ℂ) * ζ ^ 31)) * commutesA11
      - (
        ((-((255 / 97) : ℂ) * ζ ^ 3 + ((1194 / 97) : ℂ) * ζ ^ 5 + ((1361 / 194) : ℂ) * ζ ^ 6 - ((3233 / 97) : ℂ) * ζ ^ 8 - ((1194 / 97) : ℂ) * ζ ^ 9 + ((7517 / 194) : ℂ) * ζ ^ 10 - ((1873 / 194) : ℂ) * ζ ^ 13 - ((3078 / 97) : ℂ) * ζ ^ 14 + ((435 / 97) : ℂ) * ζ ^ 15 + ((2445 / 194) : ℂ) * ζ ^ 18 - ((435 / 97) : ℂ) * ζ ^ 19 - ((1879 / 97) : ℂ) * ζ ^ 20 - ((1361 / 194) : ℂ) * ζ ^ 22 + ((189 / 194) : ℂ) * ζ ^ 23 + ((1879 / 97) : ℂ) * ζ ^ 24 - ((497 / 194) : ℂ) * ζ ^ 25 - ((1361 / 194) : ℂ) * ζ ^ 26 + ((497 / 194) : ℂ) * ζ ^ 29 + ((1361 / 194) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((255 / 97) : ℂ) * ζ ^ 3 - ((1194 / 97) : ℂ) * ζ ^ 5 - ((1361 / 194) : ℂ) * ζ ^ 6 + ((3233 / 97) : ℂ) * ζ ^ 8 + ((1194 / 97) : ℂ) * ζ ^ 9 - ((7517 / 194) : ℂ) * ζ ^ 10 + ((1873 / 194) : ℂ) * ζ ^ 13 + ((3078 / 97) : ℂ) * ζ ^ 14 - ((435 / 97) : ℂ) * ζ ^ 15 - ((2445 / 194) : ℂ) * ζ ^ 18 + ((435 / 97) : ℂ) * ζ ^ 19 + ((1879 / 97) : ℂ) * ζ ^ 20 + ((1361 / 194) : ℂ) * ζ ^ 22 - ((189 / 194) : ℂ) * ζ ^ 23 - ((1879 / 97) : ℂ) * ζ ^ 24 + ((497 / 194) : ℂ) * ζ ^ 25 + ((1361 / 194) : ℂ) * ζ ^ 26 - ((497 / 194) : ℂ) * ζ ^ 29 - ((1361 / 194) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((785 / 194) : ℂ) - ((669 / 194) : ℂ) * ζ ^ 3 + ((785 / 194) : ℂ) * ζ ^ 4 - ((745 / 97) : ℂ) * ζ ^ 5 + ((1022 / 97) : ℂ) * ζ ^ 6 - ((1163 / 194) : ℂ) * ζ ^ 8 + ((745 / 97) : ℂ) * ζ ^ 9 + ((1551 / 97) : ℂ) * ζ ^ 10 + ((483 / 194) : ℂ) * ζ ^ 13 - ((529 / 97) : ℂ) * ζ ^ 14 + ((741 / 194) : ℂ) * ζ ^ 15 + ((144 / 97) : ℂ) * ζ ^ 18 - ((741 / 194) : ℂ) * ζ ^ 19 - ((852 / 97) : ℂ) * ζ ^ 20 - ((1022 / 97) : ℂ) * ζ ^ 22 - ((539 / 97) : ℂ) * ζ ^ 23 + ((852 / 97) : ℂ) * ζ ^ 24 + ((772 / 97) : ℂ) * ζ ^ 25 - ((1022 / 97) : ℂ) * ζ ^ 26 + ((154 / 97) : ℂ) * ζ ^ 28 - ((772 / 97) : ℂ) * ζ ^ 29 + ((1022 / 97) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((-((694 / 97) : ℂ) + ((897 / 97) : ℂ) * ζ ^ 3 + ((694 / 97) : ℂ) * ζ ^ 4 - ((2327 / 194) : ℂ) * ζ ^ 5 + ((1017 / 97) : ℂ) * ζ ^ 6 - ((2411 / 194) : ℂ) * ζ ^ 8 + ((2327 / 194) : ℂ) * ζ ^ 9 + ((3901 / 194) : ℂ) * ζ ^ 10 - ((731 / 194) : ℂ) * ζ ^ 13 - ((1867 / 194) : ℂ) * ζ ^ 14 + ((676 / 97) : ℂ) * ζ ^ 15 + ((501 / 194) : ℂ) * ζ ^ 18 - ((676 / 97) : ℂ) * ζ ^ 19 - ((736 / 97) : ℂ) * ζ ^ 20 - ((1017 / 97) : ℂ) * ζ ^ 22 - ((2355 / 194) : ℂ) * ζ ^ 23 + ((736 / 97) : ℂ) * ζ ^ 24 + ((1133 / 97) : ℂ) * ζ ^ 25 - ((1017 / 97) : ℂ) * ζ ^ 26 - ((189 / 194) : ℂ) * ζ ^ 28 - ((1133 / 97) : ℂ) * ζ ^ 29 + ((1017 / 97) : ℂ) * ζ ^ 30)) * Y 2 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row12_reducedY22
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow12TransformedGeneratorA =
        alternatingSixAmbientRow12TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow12GeneratorBDiagonal =
        alternatingSixAmbientRow12GeneratorBDiagonal * Y) :
    Y 2 2 = Y 5 5 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY31,
      hY41,
      hY51] at commutesA01
  have commutesA02 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA02
  simp only [Fin.sum_univ_succ] at commutesA02
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA02
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY32,
      hY42,
      hY52] at commutesA02
  have commutesA05 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA05
  simp only [Fin.sum_univ_succ] at commutesA05
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
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
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY10,
      hY13,
      hY14,
      hY15,
      hY31,
      hY41,
      hY51] at commutesA11

  linear_combination
    ((((942 / 97) : ℂ) - ((5126 / 97) : ℂ) * ζ ^ 3 + ((4566 / 97) : ℂ) * ζ ^ 5 - ((5126 / 97) : ℂ) * ζ ^ 7 - ((3324 / 97) : ℂ) * ζ ^ 10 + ((2368 / 97) : ℂ) * ζ ^ 15 + ((5126 / 97) : ℂ) * ζ ^ 19 + ((3870 / 97) : ℂ) * ζ ^ 20 + ((5126 / 97) : ℂ) * ζ ^ 23 - ((4314 / 97) : ℂ) * ζ ^ 25 - ((1686 / 97) : ℂ) * ζ ^ 30 - ((5126 / 97) : ℂ) * ζ ^ 31)) * commutesA01
      + (((2 : ℂ) - (2 : ℂ) * ζ ^ 3 - (2 : ℂ) * ζ ^ 7 - (2 : ℂ) * ζ ^ 10 + (4 : ℂ) * ζ ^ 15 + (2 : ℂ) * ζ ^ 19 - (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 23 - (2 : ℂ) * ζ ^ 25 - (2 : ℂ) * ζ ^ 31)) * commutesA02
      + (((2 : ℂ) * ζ ^ 3 + (2 : ℂ) * ζ ^ 5 + (2 : ℂ) * ζ ^ 7 + (2 : ℂ) * ζ ^ 10 - (2 : ℂ) * ζ ^ 15 - (2 : ℂ) * ζ ^ 19 - (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 23 - (2 : ℂ) * ζ ^ 30 + (2 : ℂ) * ζ ^ 31)) * commutesA05
      + ((((418 / 97) : ℂ) - ((1284 / 97) : ℂ) * ζ ^ 3 + ((914 / 97) : ℂ) * ζ ^ 5 - ((1284 / 97) : ℂ) * ζ ^ 7 - ((956 / 97) : ℂ) * ζ ^ 10 + ((1038 / 97) : ℂ) * ζ ^ 15 + ((1284 / 97) : ℂ) * ζ ^ 19 + ((856 / 97) : ℂ) * ζ ^ 20 + ((1284 / 97) : ℂ) * ζ ^ 23 - ((1378 / 97) : ℂ) * ζ ^ 25 - ((286 / 97) : ℂ) * ζ ^ 30 - ((1284 / 97) : ℂ) * ζ ^ 31)) * commutesA10
      + ((-((466 / 97) : ℂ) + ((1282 / 97) : ℂ) * ζ ^ 3 - ((902 / 97) : ℂ) * ζ ^ 5 + ((1282 / 97) : ℂ) * ζ ^ 7 + ((1050 / 97) : ℂ) * ζ ^ 10 - ((914 / 97) : ℂ) * ζ ^ 15 - ((1282 / 97) : ℂ) * ζ ^ 19 - ((790 / 97) : ℂ) * ζ ^ 20 - ((1282 / 97) : ℂ) * ζ ^ 23 + ((1216 / 97) : ℂ) * ζ ^ 25 + ((84 / 97) : ℂ) * ζ ^ 30 + ((1282 / 97) : ℂ) * ζ ^ 31)) * commutesA11
      - (
        ((((1 / 2) : ℂ) - ((75 / 97) : ℂ) * ζ ^ 3 - ((1 / 2) : ℂ) * ζ ^ 4 + ((845 / 194) : ℂ) * ζ ^ 5 + ((1279 / 194) : ℂ) * ζ ^ 6 - ((6301 / 194) : ℂ) * ζ ^ 8 - ((845 / 194) : ℂ) * ζ ^ 9 + ((6593 / 194) : ℂ) * ζ ^ 10 - ((3575 / 194) : ℂ) * ζ ^ 13 - ((2657 / 97) : ℂ) * ζ ^ 14 + ((2019 / 194) : ℂ) * ζ ^ 15 + ((2157 / 194) : ℂ) * ζ ^ 18 - ((2019 / 194) : ℂ) * ζ ^ 19 - ((3245 / 194) : ℂ) * ζ ^ 20 - ((1279 / 194) : ℂ) * ζ ^ 22 + ((470 / 97) : ℂ) * ζ ^ 23 + ((3245 / 194) : ℂ) * ζ ^ 24 - ((557 / 194) : ℂ) * ζ ^ 25 - ((1279 / 194) : ℂ) * ζ ^ 26 + ((557 / 194) : ℂ) * ζ ^ 29 + ((1279 / 194) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((53 / 194) : ℂ) * ζ ^ 3 - ((471 / 97) : ℂ) * ζ ^ 5 - ((1279 / 194) : ℂ) * ζ ^ 6 + ((6495 / 194) : ℂ) * ζ ^ 8 + ((471 / 97) : ℂ) * ζ ^ 9 - ((6787 / 194) : ℂ) * ζ ^ 10 + ((1739 / 97) : ℂ) * ζ ^ 13 + ((2754 / 97) : ℂ) * ζ ^ 14 - ((961 / 97) : ℂ) * ζ ^ 15 - ((2157 / 194) : ℂ) * ζ ^ 18 + ((961 / 97) : ℂ) * ζ ^ 19 + ((1671 / 97) : ℂ) * ζ ^ 20 + ((1279 / 194) : ℂ) * ζ ^ 22 - ((843 / 194) : ℂ) * ζ ^ 23 - ((1671 / 97) : ℂ) * ζ ^ 24 + ((557 / 194) : ℂ) * ζ ^ 25 + ((1279 / 194) : ℂ) * ζ ^ 26 - ((557 / 194) : ℂ) * ζ ^ 29 - ((1279 / 194) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((221 / 97) : ℂ) + ((224 / 97) : ℂ) * ζ ^ 3 + ((221 / 97) : ℂ) * ζ ^ 4 - ((784 / 97) : ℂ) * ζ ^ 5 + ((2467 / 194) : ℂ) * ζ ^ 6 - ((385 / 97) : ℂ) * ζ ^ 8 + ((784 / 97) : ℂ) * ζ ^ 9 + ((2607 / 194) : ℂ) * ζ ^ 10 - ((6 / 97) : ℂ) * ζ ^ 13 - ((70 / 97) : ℂ) * ζ ^ 14 + ((1439 / 194) : ℂ) * ζ ^ 15 - ((115 / 194) : ℂ) * ζ ^ 18 - ((1439 / 194) : ℂ) * ζ ^ 19 - ((941 / 97) : ℂ) * ζ ^ 20 - ((2467 / 194) : ℂ) * ζ ^ 22 - ((1521 / 194) : ℂ) * ζ ^ 23 + ((941 / 97) : ℂ) * ζ ^ 24 + ((558 / 97) : ℂ) * ζ ^ 25 - ((2467 / 194) : ℂ) * ζ ^ 26 - ((143 / 97) : ℂ) * ζ ^ 28 - ((558 / 97) : ℂ) * ζ ^ 29 + ((2467 / 194) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((-((471 / 194) : ℂ) + ((2325 / 194) : ℂ) * ζ ^ 3 + ((471 / 194) : ℂ) * ζ ^ 4 - ((1258 / 97) : ℂ) * ζ ^ 5 + ((961 / 97) : ℂ) * ζ ^ 6 - ((831 / 97) : ℂ) * ζ ^ 8 + ((1258 / 97) : ℂ) * ζ ^ 9 + ((3133 / 194) : ℂ) * ζ ^ 10 - ((1379 / 194) : ℂ) * ζ ^ 13 - ((1211 / 194) : ℂ) * ζ ^ 14 + ((952 / 97) : ℂ) * ζ ^ 15 + ((242 / 97) : ℂ) * ζ ^ 18 - ((952 / 97) : ℂ) * ζ ^ 19 - ((1751 / 194) : ℂ) * ζ ^ 20 - ((961 / 97) : ℂ) * ζ ^ 22 - ((2199 / 194) : ℂ) * ζ ^ 23 + ((1751 / 194) : ℂ) * ζ ^ 24 + ((881 / 97) : ℂ) * ζ ^ 25 - ((961 / 97) : ℂ) * ζ ^ 26 - ((843 / 194) : ℂ) * ζ ^ 28 - ((881 / 97) : ℂ) * ζ ^ 29 + ((961 / 97) : ℂ) * ζ ^ 30)) * Y 2 1
        + ((-((3 / 2) : ℂ) + ((3 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 6 - ((3 / 2) : ℂ) * ζ ^ 8 + ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 13 - ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 15 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 19 - ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 23 + ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 25 - ((1 / 2) : ℂ) * ζ ^ 26 - ((1 / 2) : ℂ) * ζ ^ 29 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 2 2
        + (((1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 3 - ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 5 - ((1 / 2) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 9 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 25 + ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 29 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row12_reducedY33
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow12TransformedGeneratorA =
        alternatingSixAmbientRow12TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow12GeneratorBDiagonal =
        alternatingSixAmbientRow12GeneratorBDiagonal * Y) :
    Y 3 3 = Y 5 5 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 3 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY31,
      hY41,
      hY51] at commutesA01
  have commutesA03 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (3 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA03
  simp only [Fin.sum_univ_succ] at commutesA03
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA03
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY13,
      hY23,
      hY53] at commutesA03
  have commutesA05 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA05
  simp only [Fin.sum_univ_succ] at commutesA05
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
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
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY10,
      hY13,
      hY14,
      hY15,
      hY31,
      hY41,
      hY51] at commutesA11
  have commutesA13 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (3 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA13
  simp only [Fin.sum_univ_succ] at commutesA13
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA13
  simp only [
      hY03,
      hY10,
      hY13,
      hY14,
      hY15,
      hY23,
      hY53] at commutesA13

  linear_combination
    ((-((33420 / 7081) : ℂ) + ((5640 / 7081) : ℂ) * ζ ^ 3 - ((15604 / 7081) : ℂ) * ζ ^ 5 + ((5640 / 7081) : ℂ) * ζ ^ 7 + ((21652 / 7081) : ℂ) * ζ ^ 10 + ((15816 / 7081) : ℂ) * ζ ^ 15 - ((5640 / 7081) : ℂ) * ζ ^ 19 + ((29220 / 7081) : ℂ) * ζ ^ 20 - ((5640 / 7081) : ℂ) * ζ ^ 23 - ((4104 / 7081) : ℂ) * ζ ^ 25 - ((38356 / 7081) : ℂ) * ζ ^ 30 + ((5640 / 7081) : ℂ) * ζ ^ 31)) * commutesA01
      + (((8 : ℂ) - (4 : ℂ) * ζ ^ 3 + (2 : ℂ) * ζ ^ 5 - (4 : ℂ) * ζ ^ 7 - (2 : ℂ) * ζ ^ 10 - (2 : ℂ) * ζ ^ 15 + (4 : ℂ) * ζ ^ 19 - (8 : ℂ) * ζ ^ 20 + (4 : ℂ) * ζ ^ 23 + (4 : ℂ) * ζ ^ 25 + (4 : ℂ) * ζ ^ 30 - (4 : ℂ) * ζ ^ 31)) * commutesA03
      + (((2 : ℂ) * ζ ^ 3 + (2 : ℂ) * ζ ^ 5 + (2 : ℂ) * ζ ^ 7 + (2 : ℂ) * ζ ^ 10 - (2 : ℂ) * ζ ^ 15 - (2 : ℂ) * ζ ^ 19 - (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 23 - (2 : ℂ) * ζ ^ 30 + (2 : ℂ) * ζ ^ 31)) * commutesA05
      + ((-((63604 / 7081) : ℂ) + ((7454 / 7081) : ℂ) * ζ ^ 3 - ((100402 / 7081) : ℂ) * ζ ^ 5 + ((7454 / 7081) : ℂ) * ζ ^ 7 + ((55122 / 7081) : ℂ) * ζ ^ 10 + ((80082 / 7081) : ℂ) * ζ ^ 15 - ((7454 / 7081) : ℂ) * ζ ^ 19 + ((68298 / 7081) : ℂ) * ζ ^ 20 - ((7454 / 7081) : ℂ) * ζ ^ 23 + ((6448 / 7081) : ℂ) * ζ ^ 25 - ((133726 / 7081) : ℂ) * ζ ^ 30 + ((7454 / 7081) : ℂ) * ζ ^ 31)) * commutesA10
      + ((((20336 / 7081) : ℂ) - ((12280 / 7081) : ℂ) * ζ ^ 3 + ((15092 / 7081) : ℂ) * ζ ^ 5 - ((12280 / 7081) : ℂ) * ζ ^ 7 - ((7168 / 7081) : ℂ) * ζ ^ 10 - ((11536 / 7081) : ℂ) * ζ ^ 15 + ((12280 / 7081) : ℂ) * ζ ^ 19 - ((25052 / 7081) : ℂ) * ζ ^ 20 + ((12280 / 7081) : ℂ) * ζ ^ 23 + ((1704 / 7081) : ℂ) * ζ ^ 25 + ((23048 / 7081) : ℂ) * ζ ^ 30 - ((12280 / 7081) : ℂ) * ζ ^ 31)) * commutesA11
      + ((-(12 : ℂ) + (8 : ℂ) * ζ ^ 3 - (12 : ℂ) * ζ ^ 5 + (8 : ℂ) * ζ ^ 7 + (2 : ℂ) * ζ ^ 10 + (8 : ℂ) * ζ ^ 15 - (8 : ℂ) * ζ ^ 19 + (14 : ℂ) * ζ ^ 20 - (8 : ℂ) * ζ ^ 23 - (14 : ℂ) * ζ ^ 30 + (8 : ℂ) * ζ ^ 31)) * commutesA13
      - (
        ((((76 / 73) : ℂ) - ((65615 / 14162) : ℂ) * ζ ^ 3 - ((76 / 73) : ℂ) * ζ ^ 4 - ((82599 / 14162) : ℂ) * ζ ^ 5 + ((13849 / 14162) : ℂ) * ζ ^ 6 - ((21655 / 7081) : ℂ) * ζ ^ 8 + ((82599 / 14162) : ℂ) * ζ ^ 9 - ((21710 / 7081) : ℂ) * ζ ^ 10 - ((31499 / 14162) : ℂ) * ζ ^ 13 + ((57269 / 14162) : ℂ) * ζ ^ 14 - ((16382 / 7081) : ℂ) * ζ ^ 15 + ((19609 / 14162) : ℂ) * ζ ^ 18 + ((16382 / 7081) : ℂ) * ζ ^ 19 + ((6084 / 7081) : ℂ) * ζ ^ 20 - ((13849 / 14162) : ℂ) * ζ ^ 22 + ((17446 / 7081) : ℂ) * ζ ^ 23 - ((6084 / 7081) : ℂ) * ζ ^ 24 + ((117555 / 14162) : ℂ) * ζ ^ 25 - ((13849 / 14162) : ℂ) * ζ ^ 26 - ((32 / 73) : ℂ) * ζ ^ 28 - ((117555 / 14162) : ℂ) * ζ ^ 29 + ((13849 / 14162) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((-((93 / 73) : ℂ) + ((24805 / 7081) : ℂ) * ζ ^ 3 + ((93 / 73) : ℂ) * ζ ^ 4 - ((19083 / 7081) : ℂ) * ζ ^ 5 + ((787 / 7081) : ℂ) * ζ ^ 6 + ((47651 / 7081) : ℂ) * ζ ^ 8 + ((19083 / 7081) : ℂ) * ζ ^ 9 - ((8087 / 14162) : ℂ) * ζ ^ 10 - ((40559 / 7081) : ℂ) * ζ ^ 13 + ((9661 / 14162) : ℂ) * ζ ^ 14 + ((7167 / 7081) : ℂ) * ζ ^ 15 - ((321 / 97) : ℂ) * ζ ^ 18 - ((7167 / 7081) : ℂ) * ζ ^ 19 + ((36305 / 7081) : ℂ) * ζ ^ 20 - ((787 / 7081) : ℂ) * ζ ^ 22 - ((25885 / 7081) : ℂ) * ζ ^ 23 - ((36305 / 7081) : ℂ) * ζ ^ 24 - ((27398 / 7081) : ℂ) * ζ ^ 25 - ((787 / 7081) : ℂ) * ζ ^ 26 + ((441 / 73) : ℂ) * ζ ^ 28 + ((27398 / 7081) : ℂ) * ζ ^ 29 + ((787 / 7081) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((7824 / 7081) : ℂ) - ((18083 / 14162) : ℂ) * ζ ^ 3 + ((7824 / 7081) : ℂ) * ζ ^ 4 + ((49565 / 14162) : ℂ) * ζ ^ 5 + ((16820 / 7081) : ℂ) * ζ ^ 6 - ((52222 / 7081) : ℂ) * ζ ^ 8 - ((49565 / 14162) : ℂ) * ζ ^ 9 - ((9822 / 7081) : ℂ) * ζ ^ 10 + ((99763 / 14162) : ℂ) * ζ ^ 13 + ((26642 / 7081) : ℂ) * ζ ^ 14 - ((12611 / 7081) : ℂ) * ζ ^ 15 - ((21426 / 7081) : ℂ) * ζ ^ 18 + ((12611 / 7081) : ℂ) * ζ ^ 19 - ((42697 / 14162) : ℂ) * ζ ^ 20 - ((16820 / 7081) : ℂ) * ζ ^ 22 + ((30571 / 14162) : ℂ) * ζ ^ 23 + ((42697 / 14162) : ℂ) * ζ ^ 24 + ((37342 / 7081) : ℂ) * ζ ^ 25 - ((16820 / 7081) : ℂ) * ζ ^ 26 - ((43777 / 7081) : ℂ) * ζ ^ 28 - ((37342 / 7081) : ℂ) * ζ ^ 29 + ((16820 / 7081) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((((8355 / 7081) : ℂ) + ((1861 / 7081) : ℂ) * ζ ^ 3 - ((8355 / 7081) : ℂ) * ζ ^ 4 + ((8985 / 7081) : ℂ) * ζ ^ 5 + ((1660 / 7081) : ℂ) * ζ ^ 6 + ((5413 / 7081) : ℂ) * ζ ^ 8 - ((8985 / 7081) : ℂ) * ζ ^ 9 + ((20 / 7081) : ℂ) * ζ ^ 10 + ((5364 / 7081) : ℂ) * ζ ^ 13 + ((1640 / 7081) : ℂ) * ζ ^ 14 - ((7156 / 7081) : ℂ) * ζ ^ 15 - ((2710 / 7081) : ℂ) * ζ ^ 18 + ((7156 / 7081) : ℂ) * ζ ^ 19 - ((13259 / 7081) : ℂ) * ζ ^ 20 - ((1660 / 7081) : ℂ) * ζ ^ 22 - ((6788 / 7081) : ℂ) * ζ ^ 23 + ((13259 / 7081) : ℂ) * ζ ^ 24 - ((5237 / 7081) : ℂ) * ζ ^ 25 - ((1660 / 7081) : ℂ) * ζ ^ 26 - ((9589 / 7081) : ℂ) * ζ ^ 28 + ((5237 / 7081) : ℂ) * ζ ^ 29 + ((1660 / 7081) : ℂ) * ζ ^ 30)) * Y 2 1
        + ((-((56 / 73) : ℂ) + ((46 / 73) : ℂ) * ζ ^ 3 + ((56 / 73) : ℂ) * ζ ^ 4 + ((586 / 73) : ℂ) * ζ ^ 5 - ((43 / 73) : ℂ) * ζ ^ 6 - ((609 / 146) : ℂ) * ζ ^ 8 - ((586 / 73) : ℂ) * ζ ^ 9 + ((531 / 146) : ℂ) * ζ ^ 10 + ((1161 / 146) : ℂ) * ζ ^ 13 - ((617 / 146) : ℂ) * ζ ^ 14 + ((95 / 73) : ℂ) * ζ ^ 15 + ((104 / 73) : ℂ) * ζ ^ 18 - ((95 / 73) : ℂ) * ζ ^ 19 - ((437 / 73) : ℂ) * ζ ^ 20 + ((43 / 73) : ℂ) * ζ ^ 22 + ((87 / 73) : ℂ) * ζ ^ 23 + ((437 / 73) : ℂ) * ζ ^ 24 - ((287 / 73) : ℂ) * ζ ^ 25 + ((43 / 73) : ℂ) * ζ ^ 26 - ((409 / 73) : ℂ) * ζ ^ 28 + ((287 / 73) : ℂ) * ζ ^ 29 - ((43 / 73) : ℂ) * ζ ^ 30)) * Y 3 3
        + ((-((76 / 73) : ℂ) - ((167 / 73) : ℂ) * ζ ^ 3 + ((76 / 73) : ℂ) * ζ ^ 4 - ((39 / 73) : ℂ) * ζ ^ 5 + ((145 / 73) : ℂ) * ζ ^ 6 - ((571 / 146) : ℂ) * ζ ^ 8 + ((39 / 73) : ℂ) * ζ ^ 9 + ((267 / 146) : ℂ) * ζ ^ 10 - ((96 / 73) : ℂ) * ζ ^ 13 + ((23 / 146) : ℂ) * ζ ^ 14 + ((155 / 73) : ℂ) * ζ ^ 15 + ((235 / 73) : ℂ) * ζ ^ 18 - ((155 / 73) : ℂ) * ζ ^ 19 - ((623 / 146) : ℂ) * ζ ^ 20 - ((145 / 73) : ℂ) * ζ ^ 22 + ((1133 / 146) : ℂ) * ζ ^ 23 + ((623 / 146) : ℂ) * ζ ^ 24 - ((49 / 146) : ℂ) * ζ ^ 25 - ((145 / 73) : ℂ) * ζ ^ 26 - ((1131 / 146) : ℂ) * ζ ^ 28 + ((49 / 146) : ℂ) * ζ ^ 29 + ((145 / 73) : ℂ) * ζ ^ 30)) * Y 4 3
        + (((1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 3 - ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 5 - ((1 / 2) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 9 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 25 + ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 29 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row12_reducedY34
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow12TransformedGeneratorA =
        alternatingSixAmbientRow12TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow12GeneratorBDiagonal =
        alternatingSixAmbientRow12GeneratorBDiagonal * Y) :
    Y 3 4 = 0 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY54 :
      Y 5 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 4 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY31,
      hY41,
      hY51] at commutesA01
  have commutesA04 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (4 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA04
  simp only [Fin.sum_univ_succ] at commutesA04
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA04
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY14,
      hY24,
      hY54] at commutesA04
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY10,
      hY13,
      hY14,
      hY15,
      hY31,
      hY41,
      hY51] at commutesA11
  have commutesA14 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (4 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA14
  simp only [Fin.sum_univ_succ] at commutesA14
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA14
  simp only [
      hY04,
      hY10,
      hY13,
      hY14,
      hY15,
      hY24,
      hY54] at commutesA14

  linear_combination
    ((-((2682 / 7081) : ℂ) - ((41652 / 7081) : ℂ) * ζ ^ 3 + ((64254 / 7081) : ℂ) * ζ ^ 5 - ((41652 / 7081) : ℂ) * ζ ^ 7 + ((6004 / 7081) : ℂ) * ζ ^ 10 - ((27070 / 7081) : ℂ) * ζ ^ 15 + ((41652 / 7081) : ℂ) * ζ ^ 19 - ((6376 / 7081) : ℂ) * ζ ^ 20 + ((41652 / 7081) : ℂ) * ζ ^ 23 - ((7718 / 7081) : ℂ) * ζ ^ 25 + ((1590 / 7081) : ℂ) * ζ ^ 30 - ((41652 / 7081) : ℂ) * ζ ^ 31)) * commutesA01
      + (((8 : ℂ) - (4 : ℂ) * ζ ^ 3 + (2 : ℂ) * ζ ^ 5 - (4 : ℂ) * ζ ^ 7 - (2 : ℂ) * ζ ^ 10 - (2 : ℂ) * ζ ^ 15 + (4 : ℂ) * ζ ^ 19 - (8 : ℂ) * ζ ^ 20 + (4 : ℂ) * ζ ^ 23 + (4 : ℂ) * ζ ^ 25 + (4 : ℂ) * ζ ^ 30 - (4 : ℂ) * ζ ^ 31)) * commutesA04
      + ((((59868 / 7081) : ℂ) - ((118416 / 7081) : ℂ) * ζ ^ 3 + ((75534 / 7081) : ℂ) * ζ ^ 5 - ((118416 / 7081) : ℂ) * ζ ^ 7 + ((52460 / 7081) : ℂ) * ζ ^ 10 - ((9838 / 7081) : ℂ) * ζ ^ 15 + ((118416 / 7081) : ℂ) * ζ ^ 19 - ((96432 / 7081) : ℂ) * ζ ^ 20 + ((118416 / 7081) : ℂ) * ζ ^ 23 - ((32734 / 7081) : ℂ) * ζ ^ 25 + ((45868 / 7081) : ℂ) * ζ ^ 30 - ((118416 / 7081) : ℂ) * ζ ^ 31)) * commutesA10
      + ((-((4104 / 7081) : ℂ) + ((29220 / 7081) : ℂ) * ζ ^ 3 - ((38356 / 7081) : ℂ) * ζ ^ 5 + ((29220 / 7081) : ℂ) * ζ ^ 7 - ((5640 / 7081) : ℂ) * ζ ^ 10 + ((4200 / 7081) : ℂ) * ζ ^ 15 - ((29220 / 7081) : ℂ) * ζ ^ 19 + ((19708 / 7081) : ℂ) * ζ ^ 20 - ((29220 / 7081) : ℂ) * ζ ^ 23 + ((16704 / 7081) : ℂ) * ζ ^ 25 - ((15816 / 7081) : ℂ) * ζ ^ 30 + ((29220 / 7081) : ℂ) * ζ ^ 31)) * commutesA11
      + ((-(12 : ℂ) + (8 : ℂ) * ζ ^ 3 - (12 : ℂ) * ζ ^ 5 + (8 : ℂ) * ζ ^ 7 + (2 : ℂ) * ζ ^ 10 + (8 : ℂ) * ζ ^ 15 - (8 : ℂ) * ζ ^ 19 + (14 : ℂ) * ζ ^ 20 - (8 : ℂ) * ζ ^ 23 - (14 : ℂ) * ζ ^ 30 + (8 : ℂ) * ζ ^ 31)) * commutesA14
      - (
        ((((124 / 73) : ℂ) + ((33273 / 14162) : ℂ) * ζ ^ 3 - ((124 / 73) : ℂ) * ζ ^ 4 - ((5124 / 7081) : ℂ) * ζ ^ 5 - ((44818 / 7081) : ℂ) * ζ ^ 6 + ((14312 / 7081) : ℂ) * ζ ^ 8 + ((5124 / 7081) : ℂ) * ζ ^ 9 + ((1715 / 14162) : ℂ) * ζ ^ 10 - ((18059 / 14162) : ℂ) * ζ ^ 13 - ((91351 / 14162) : ℂ) * ζ ^ 14 + ((79645 / 14162) : ℂ) * ζ ^ 15 + ((26169 / 14162) : ℂ) * ζ ^ 18 - ((79645 / 14162) : ℂ) * ζ ^ 19 + ((14063 / 14162) : ℂ) * ζ ^ 20 + ((44818 / 7081) : ℂ) * ζ ^ 22 - ((2735 / 14162) : ℂ) * ζ ^ 23 - ((14063 / 14162) : ℂ) * ζ ^ 24 - ((43521 / 14162) : ℂ) * ζ ^ 25 + ((44818 / 7081) : ℂ) * ζ ^ 26 - ((33 / 73) : ℂ) * ζ ^ 28 + ((43521 / 14162) : ℂ) * ζ ^ 29 - ((44818 / 7081) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((-((48 / 73) : ℂ) - ((875 / 14162) : ℂ) * ζ ^ 3 + ((48 / 73) : ℂ) * ζ ^ 4 + ((8907 / 7081) : ℂ) * ζ ^ 5 + ((30753 / 7081) : ℂ) * ζ ^ 6 + ((26763 / 14162) : ℂ) * ζ ^ 8 - ((8907 / 7081) : ℂ) * ζ ^ 9 - ((13807 / 7081) : ℂ) * ζ ^ 10 + ((36683 / 14162) : ℂ) * ζ ^ 13 + ((44560 / 7081) : ℂ) * ζ ^ 14 - ((109715 / 14162) : ℂ) * ζ ^ 15 - ((983 / 194) : ℂ) * ζ ^ 18 + ((109715 / 14162) : ℂ) * ζ ^ 19 + ((23184 / 7081) : ℂ) * ζ ^ 20 - ((30753 / 7081) : ℂ) * ζ ^ 22 - ((53583 / 7081) : ℂ) * ζ ^ 23 - ((23184 / 7081) : ℂ) * ζ ^ 24 + ((24137 / 7081) : ℂ) * ζ ^ 25 - ((30753 / 7081) : ℂ) * ζ ^ 26 + ((1197 / 146) : ℂ) * ζ ^ 28 - ((24137 / 7081) : ℂ) * ζ ^ 29 + ((30753 / 7081) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((((4086 / 7081) : ℂ) - ((369 / 7081) : ℂ) * ζ ^ 3 - ((4086 / 7081) : ℂ) * ζ ^ 4 - ((36023 / 14162) : ℂ) * ζ ^ 5 + ((42412 / 7081) : ℂ) * ζ ^ 6 - ((34404 / 7081) : ℂ) * ζ ^ 8 + ((36023 / 14162) : ℂ) * ζ ^ 9 - ((15741 / 14162) : ℂ) * ζ ^ 10 - ((46393 / 14162) : ℂ) * ζ ^ 13 + ((100565 / 14162) : ℂ) * ζ ^ 14 + ((45069 / 14162) : ℂ) * ζ ^ 15 - ((49365 / 14162) : ℂ) * ζ ^ 18 - ((45069 / 14162) : ℂ) * ζ ^ 19 + ((13427 / 7081) : ℂ) * ζ ^ 20 - ((42412 / 7081) : ℂ) * ζ ^ 22 + ((99519 / 14162) : ℂ) * ζ ^ 23 - ((13427 / 7081) : ℂ) * ζ ^ 24 + ((67458 / 7081) : ℂ) * ζ ^ 25 - ((42412 / 7081) : ℂ) * ζ ^ 26 - ((30707 / 7081) : ℂ) * ζ ^ 28 - ((67458 / 7081) : ℂ) * ζ ^ 29 + ((42412 / 7081) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((((1341 / 14162) : ℂ) + ((24219 / 14162) : ℂ) * ζ ^ 3 - ((1341 / 14162) : ℂ) * ζ ^ 4 - ((34179 / 14162) : ℂ) * ζ ^ 5 + ((3108 / 7081) : ℂ) * ζ ^ 6 + ((1501 / 7081) : ℂ) * ζ ^ 8 + ((34179 / 14162) : ℂ) * ζ ^ 9 - ((7982 / 7081) : ℂ) * ζ ^ 10 - ((34361 / 14162) : ℂ) * ζ ^ 13 + ((11090 / 7081) : ℂ) * ζ ^ 14 + ((31541 / 14162) : ℂ) * ζ ^ 15 - ((10745 / 14162) : ℂ) * ζ ^ 18 - ((31541 / 14162) : ℂ) * ζ ^ 19 + ((9949 / 7081) : ℂ) * ζ ^ 20 - ((3108 / 7081) : ℂ) * ζ ^ 22 + ((4049 / 14162) : ℂ) * ζ ^ 23 - ((9949 / 7081) : ℂ) * ζ ^ 24 + ((13713 / 14162) : ℂ) * ζ ^ 25 - ((3108 / 7081) : ℂ) * ζ ^ 26 + ((795 / 14162) : ℂ) * ζ ^ 28 - ((13713 / 14162) : ℂ) * ζ ^ 29 + ((3108 / 7081) : ℂ) * ζ ^ 30)) * Y 2 1
        + ((-((56 / 73) : ℂ) + ((46 / 73) : ℂ) * ζ ^ 3 + ((56 / 73) : ℂ) * ζ ^ 4 + ((586 / 73) : ℂ) * ζ ^ 5 - ((43 / 73) : ℂ) * ζ ^ 6 - ((609 / 146) : ℂ) * ζ ^ 8 - ((586 / 73) : ℂ) * ζ ^ 9 + ((531 / 146) : ℂ) * ζ ^ 10 + ((1161 / 146) : ℂ) * ζ ^ 13 - ((617 / 146) : ℂ) * ζ ^ 14 + ((95 / 73) : ℂ) * ζ ^ 15 + ((104 / 73) : ℂ) * ζ ^ 18 - ((95 / 73) : ℂ) * ζ ^ 19 - ((437 / 73) : ℂ) * ζ ^ 20 + ((43 / 73) : ℂ) * ζ ^ 22 + ((87 / 73) : ℂ) * ζ ^ 23 + ((437 / 73) : ℂ) * ζ ^ 24 - ((287 / 73) : ℂ) * ζ ^ 25 + ((43 / 73) : ℂ) * ζ ^ 26 - ((409 / 73) : ℂ) * ζ ^ 28 + ((287 / 73) : ℂ) * ζ ^ 29 - ((43 / 73) : ℂ) * ζ ^ 30)) * Y 3 4
        + ((-((76 / 73) : ℂ) - ((167 / 73) : ℂ) * ζ ^ 3 + ((76 / 73) : ℂ) * ζ ^ 4 - ((39 / 73) : ℂ) * ζ ^ 5 + ((145 / 73) : ℂ) * ζ ^ 6 - ((571 / 146) : ℂ) * ζ ^ 8 + ((39 / 73) : ℂ) * ζ ^ 9 + ((267 / 146) : ℂ) * ζ ^ 10 - ((96 / 73) : ℂ) * ζ ^ 13 + ((23 / 146) : ℂ) * ζ ^ 14 + ((155 / 73) : ℂ) * ζ ^ 15 + ((235 / 73) : ℂ) * ζ ^ 18 - ((155 / 73) : ℂ) * ζ ^ 19 - ((623 / 146) : ℂ) * ζ ^ 20 - ((145 / 73) : ℂ) * ζ ^ 22 + ((1133 / 146) : ℂ) * ζ ^ 23 + ((623 / 146) : ℂ) * ζ ^ 24 - ((49 / 146) : ℂ) * ζ ^ 25 - ((145 / 73) : ℂ) * ζ ^ 26 - ((1131 / 146) : ℂ) * ζ ^ 28 + ((49 / 146) : ℂ) * ζ ^ 29 + ((145 / 73) : ℂ) * ζ ^ 30)) * Y 4 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row12_reducedY43
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow12TransformedGeneratorA =
        alternatingSixAmbientRow12TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow12GeneratorBDiagonal =
        alternatingSixAmbientRow12GeneratorBDiagonal * Y) :
    Y 4 3 = 0 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 3 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY31,
      hY41,
      hY51] at commutesA01
  have commutesA03 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (3 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA03
  simp only [Fin.sum_univ_succ] at commutesA03
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA03
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY13,
      hY23,
      hY53] at commutesA03
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY10,
      hY13,
      hY14,
      hY15,
      hY31,
      hY41,
      hY51] at commutesA11
  have commutesA13 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (3 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA13
  simp only [Fin.sum_univ_succ] at commutesA13
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA13
  simp only [
      hY03,
      hY10,
      hY13,
      hY14,
      hY15,
      hY23,
      hY53] at commutesA13

  linear_combination
    ((-((160472 / 7081) : ℂ) - ((140320 / 7081) : ℂ) * ζ ^ 3 + ((57772 / 7081) : ℂ) * ζ ^ 5 - ((140320 / 7081) : ℂ) * ζ ^ 7 + ((128632 / 7081) : ℂ) * ζ ^ 10 + ((177808 / 7081) : ℂ) * ζ ^ 15 + ((140320 / 7081) : ℂ) * ζ ^ 19 + ((101048 / 7081) : ℂ) * ζ ^ 20 + ((140320 / 7081) : ℂ) * ζ ^ 23 - ((184148 / 7081) : ℂ) * ζ ^ 25 - ((151164 / 7081) : ℂ) * ζ ^ 30 - ((140320 / 7081) : ℂ) * ζ ^ 31)) * commutesA01
      + (((38 : ℂ) + (18 : ℂ) * ζ ^ 3 + (2 : ℂ) * ζ ^ 5 + (18 : ℂ) * ζ ^ 7 - (38 : ℂ) * ζ ^ 10 - (42 : ℂ) * ζ ^ 15 - (18 : ℂ) * ζ ^ 19 - (10 : ℂ) * ζ ^ 20 - (18 : ℂ) * ζ ^ 23 + (32 : ℂ) * ζ ^ 25 + (32 : ℂ) * ζ ^ 30 + (18 : ℂ) * ζ ^ 31)) * commutesA03
      + ((-((572804 / 7081) : ℂ) - ((217592 / 7081) : ℂ) * ζ ^ 3 - ((81548 / 7081) : ℂ) * ζ ^ 5 - ((217592 / 7081) : ℂ) * ζ ^ 7 + ((524496 / 7081) : ℂ) * ζ ^ 10 + ((555560 / 7081) : ℂ) * ζ ^ 15 + ((217592 / 7081) : ℂ) * ζ ^ 19 + ((265988 / 7081) : ℂ) * ζ ^ 20 + ((217592 / 7081) : ℂ) * ζ ^ 23 - ((479620 / 7081) : ℂ) * ζ ^ 25 - ((451716 / 7081) : ℂ) * ζ ^ 30 - ((217592 / 7081) : ℂ) * ζ ^ 31)) * commutesA10
      + ((((123608 / 7081) : ℂ) + ((47992 / 7081) : ℂ) * ζ ^ 3 + ((22060 / 7081) : ℂ) * ζ ^ 5 + ((47992 / 7081) : ℂ) * ζ ^ 7 - ((100284 / 7081) : ℂ) * ζ ^ 10 - ((132628 / 7081) : ℂ) * ζ ^ 15 - ((47992 / 7081) : ℂ) * ζ ^ 19 - ((75580 / 7081) : ℂ) * ζ ^ 20 - ((47992 / 7081) : ℂ) * ζ ^ 23 + ((101636 / 7081) : ℂ) * ζ ^ 25 + ((119412 / 7081) : ℂ) * ζ ^ 30 + ((47992 / 7081) : ℂ) * ζ ^ 31)) * commutesA11
      + ((-(82 : ℂ) - (18 : ℂ) * ζ ^ 3 - (28 : ℂ) * ζ ^ 5 - (18 : ℂ) * ζ ^ 7 + (70 : ℂ) * ζ ^ 10 + (80 : ℂ) * ζ ^ 15 + (18 : ℂ) * ζ ^ 19 + (46 : ℂ) * ζ ^ 20 + (18 : ℂ) * ζ ^ 23 - (54 : ℂ) * ζ ^ 25 - (76 : ℂ) * ζ ^ 30 - (18 : ℂ) * ζ ^ 31)) * commutesA13
      - (
        ((((361 / 73) : ℂ) - ((479667 / 14162) : ℂ) * ζ ^ 3 - ((361 / 73) : ℂ) * ζ ^ 4 - ((187130 / 7081) : ℂ) * ζ ^ 5 - ((157035 / 14162) : ℂ) * ζ ^ 6 - ((284801 / 14162) : ℂ) * ζ ^ 8 + ((187130 / 7081) : ℂ) * ζ ^ 9 - ((274867 / 14162) : ℂ) * ζ ^ 10 - ((2699 / 14162) : ℂ) * ζ ^ 13 + ((58916 / 7081) : ℂ) * ζ ^ 14 + ((24145 / 14162) : ℂ) * ζ ^ 15 + ((102685 / 7081) : ℂ) * ζ ^ 18 - ((24145 / 14162) : ℂ) * ζ ^ 19 + ((186145 / 14162) : ℂ) * ζ ^ 20 + ((157035 / 14162) : ℂ) * ζ ^ 22 + ((100647 / 7081) : ℂ) * ζ ^ 23 - ((186145 / 14162) : ℂ) * ζ ^ 24 + ((210571 / 7081) : ℂ) * ζ ^ 25 + ((157035 / 14162) : ℂ) * ζ ^ 26 - ((256 / 73) : ℂ) * ζ ^ 28 - ((210571 / 7081) : ℂ) * ζ ^ 29 - ((157035 / 14162) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((-((1271 / 146) : ℂ) + ((401873 / 14162) : ℂ) * ζ ^ 3 + ((1271 / 146) : ℂ) * ζ ^ 4 - ((123755 / 7081) : ℂ) * ζ ^ 5 + ((66732 / 7081) : ℂ) * ζ ^ 6 + ((25423 / 14162) : ℂ) * ζ ^ 8 + ((123755 / 7081) : ℂ) * ζ ^ 9 + ((160795 / 14162) : ℂ) * ζ ^ 10 - ((262636 / 7081) : ℂ) * ζ ^ 13 - ((27331 / 14162) : ℂ) * ζ ^ 14 + ((102436 / 7081) : ℂ) * ζ ^ 15 - ((138866 / 7081) : ℂ) * ζ ^ 18 - ((102436 / 7081) : ℂ) * ζ ^ 19 + ((115429 / 7081) : ℂ) * ζ ^ 20 - ((66732 / 7081) : ℂ) * ζ ^ 22 + ((38742 / 7081) : ℂ) * ζ ^ 23 - ((115429 / 7081) : ℂ) * ζ ^ 24 - ((213578 / 7081) : ℂ) * ζ ^ 25 - ((66732 / 7081) : ℂ) * ζ ^ 26 + ((2394 / 73) : ℂ) * ζ ^ 28 + ((213578 / 7081) : ℂ) * ζ ^ 29 + ((66732 / 7081) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((45517 / 14162) : ℂ) - ((302969 / 14162) : ℂ) * ζ ^ 3 + ((45517 / 14162) : ℂ) * ζ ^ 4 + ((119910 / 7081) : ℂ) * ζ ^ 5 - ((17483 / 7081) : ℂ) * ζ ^ 6 - ((113455 / 14162) : ℂ) * ζ ^ 8 - ((119910 / 7081) : ℂ) * ζ ^ 9 - ((216248 / 7081) : ℂ) * ζ ^ 10 + ((425857 / 14162) : ℂ) * ζ ^ 13 + ((198765 / 7081) : ℂ) * ζ ^ 14 - ((97255 / 14162) : ℂ) * ζ ^ 15 - ((2429 / 7081) : ℂ) * ζ ^ 18 + ((97255 / 14162) : ℂ) * ζ ^ 19 - ((9838 / 7081) : ℂ) * ζ ^ 20 + ((17483 / 7081) : ℂ) * ζ ^ 22 - ((16731 / 7081) : ℂ) * ζ ^ 23 + ((9838 / 7081) : ℂ) * ζ ^ 24 + ((236152 / 7081) : ℂ) * ζ ^ 25 + ((17483 / 7081) : ℂ) * ζ ^ 26 - ((100534 / 7081) : ℂ) * ζ ^ 28 - ((236152 / 7081) : ℂ) * ζ ^ 29 - ((17483 / 7081) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((((40118 / 7081) : ℂ) + ((44296 / 7081) : ℂ) * ζ ^ 3 - ((40118 / 7081) : ℂ) * ζ ^ 4 + ((16459 / 7081) : ℂ) * ζ ^ 5 + ((23082 / 7081) : ℂ) * ζ ^ 6 + ((32158 / 7081) : ℂ) * ζ ^ 8 - ((16459 / 7081) : ℂ) * ζ ^ 9 - ((3561 / 7081) : ℂ) * ζ ^ 10 + ((9372 / 7081) : ℂ) * ζ ^ 13 + ((26643 / 7081) : ℂ) * ζ ^ 14 - ((34443 / 7081) : ℂ) * ζ ^ 15 - ((37938 / 7081) : ℂ) * ζ ^ 18 + ((34443 / 7081) : ℂ) * ζ ^ 19 - ((46421 / 7081) : ℂ) * ζ ^ 20 - ((23082 / 7081) : ℂ) * ζ ^ 22 - ((75890 / 7081) : ℂ) * ζ ^ 23 + ((46421 / 7081) : ℂ) * ζ ^ 24 + ((27142 / 7081) : ℂ) * ζ ^ 25 - ((23082 / 7081) : ℂ) * ζ ^ 26 - ((37791 / 7081) : ℂ) * ζ ^ 28 - ((27142 / 7081) : ℂ) * ζ ^ 29 + ((23082 / 7081) : ℂ) * ζ ^ 30)) * Y 2 1
        + ((((549 / 146) : ℂ) + ((401 / 73) : ℂ) * ζ ^ 3 - ((549 / 146) : ℂ) * ζ ^ 4 + ((3205 / 73) : ℂ) * ζ ^ 5 + ((243 / 146) : ℂ) * ζ ^ 6 + ((1337 / 73) : ℂ) * ζ ^ 8 - ((3205 / 73) : ℂ) * ζ ^ 9 + ((588 / 73) : ℂ) * ζ ^ 10 + ((5443 / 146) : ℂ) * ζ ^ 13 - ((933 / 146) : ℂ) * ζ ^ 14 - ((2361 / 146) : ℂ) * ζ ^ 15 + ((373 / 73) : ℂ) * ζ ^ 18 + ((2361 / 146) : ℂ) * ζ ^ 19 - ((4299 / 146) : ℂ) * ζ ^ 20 - ((243 / 146) : ℂ) * ζ ^ 22 - ((1437 / 73) : ℂ) * ζ ^ 23 + ((4299 / 146) : ℂ) * ζ ^ 24 + ((31 / 73) : ℂ) * ζ ^ 25 - ((243 / 146) : ℂ) * ζ ^ 26 - ((2138 / 73) : ℂ) * ζ ^ 28 - ((31 / 73) : ℂ) * ζ ^ 29 + ((243 / 146) : ℂ) * ζ ^ 30)) * Y 3 3
        + ((-((334 / 73) : ℂ) - ((1724 / 73) : ℂ) * ζ ^ 3 + ((334 / 73) : ℂ) * ζ ^ 4 - ((895 / 146) : ℂ) * ζ ^ 5 - ((234 / 73) : ℂ) * ζ ^ 6 - ((996 / 73) : ℂ) * ζ ^ 8 + ((895 / 146) : ℂ) * ζ ^ 9 + ((725 / 73) : ℂ) * ζ ^ 10 + ((750 / 73) : ℂ) * ζ ^ 13 - ((959 / 73) : ℂ) * ζ ^ 14 + ((262 / 73) : ℂ) * ζ ^ 15 + ((4579 / 146) : ℂ) * ζ ^ 18 - ((262 / 73) : ℂ) * ζ ^ 19 - ((5339 / 146) : ℂ) * ζ ^ 20 + ((234 / 73) : ℂ) * ζ ^ 22 + ((1585 / 146) : ℂ) * ζ ^ 23 + ((5339 / 146) : ℂ) * ζ ^ 24 + ((2060 / 73) : ℂ) * ζ ^ 25 + ((234 / 73) : ℂ) * ζ ^ 26 - ((2985 / 73) : ℂ) * ζ ^ 28 - ((2060 / 73) : ℂ) * ζ ^ 29 - ((234 / 73) : ℂ) * ζ ^ 30)) * Y 4 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row12_reducedY44
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow12TransformedGeneratorA =
        alternatingSixAmbientRow12TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow12GeneratorBDiagonal =
        alternatingSixAmbientRow12GeneratorBDiagonal * Y) :
    Y 4 4 = Y 5 5 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY54 :
      Y 5 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 4 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY31,
      hY41,
      hY51] at commutesA01
  have commutesA04 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (4 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA04
  simp only [Fin.sum_univ_succ] at commutesA04
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA04
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY05,
      hY14,
      hY24,
      hY54] at commutesA04
  have commutesA05 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA05
  simp only [Fin.sum_univ_succ] at commutesA05
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
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
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY10,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA10
  have commutesA11 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA11
  simp only [Fin.sum_univ_succ] at commutesA11
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA11
  simp only [
      hY01,
      hY10,
      hY13,
      hY14,
      hY15,
      hY31,
      hY41,
      hY51] at commutesA11
  have commutesA14 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (4 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA14
  simp only [Fin.sum_univ_succ] at commutesA14
  simp [
      alternatingSixAmbientRow12TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA14
  simp only [
      hY04,
      hY10,
      hY13,
      hY14,
      hY15,
      hY24,
      hY54] at commutesA14

  linear_combination
    ((((321040 / 7081) : ℂ) - ((249752 / 7081) : ℂ) * ζ ^ 3 + ((290668 / 7081) : ℂ) * ζ ^ 5 - ((249752 / 7081) : ℂ) * ζ ^ 7 - ((359496 / 7081) : ℂ) * ζ ^ 10 - ((5888 / 7081) : ℂ) * ζ ^ 15 + ((249752 / 7081) : ℂ) * ζ ^ 19 - ((17540 / 7081) : ℂ) * ζ ^ 20 + ((249752 / 7081) : ℂ) * ζ ^ 23 - ((140436 / 7081) : ℂ) * ζ ^ 25 + ((194868 / 7081) : ℂ) * ζ ^ 30 - ((249752 / 7081) : ℂ) * ζ ^ 31)) * commutesA01
      + (((38 : ℂ) + (18 : ℂ) * ζ ^ 3 + (2 : ℂ) * ζ ^ 5 + (18 : ℂ) * ζ ^ 7 - (38 : ℂ) * ζ ^ 10 - (42 : ℂ) * ζ ^ 15 - (18 : ℂ) * ζ ^ 19 - (10 : ℂ) * ζ ^ 20 - (18 : ℂ) * ζ ^ 23 + (32 : ℂ) * ζ ^ 25 + (32 : ℂ) * ζ ^ 30 + (18 : ℂ) * ζ ^ 31)) * commutesA04
      + (((2 : ℂ) * ζ ^ 3 + (2 : ℂ) * ζ ^ 5 + (2 : ℂ) * ζ ^ 7 + (2 : ℂ) * ζ ^ 10 - (2 : ℂ) * ζ ^ 15 - (2 : ℂ) * ζ ^ 19 - (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 23 - (2 : ℂ) * ζ ^ 30 + (2 : ℂ) * ζ ^ 31)) * commutesA05
      + ((((510072 / 7081) : ℂ) - ((178858 / 7081) : ℂ) * ζ ^ 3 + ((449050 / 7081) : ℂ) * ζ ^ 5 - ((178858 / 7081) : ℂ) * ζ ^ 7 - ((354714 / 7081) : ℂ) * ζ ^ 10 - ((357774 / 7081) : ℂ) * ζ ^ 15 + ((178858 / 7081) : ℂ) * ζ ^ 19 - ((444978 / 7081) : ℂ) * ζ ^ 20 + ((178858 / 7081) : ℂ) * ζ ^ 23 + ((45236 / 7081) : ℂ) * ζ ^ 25 + ((609394 / 7081) : ℂ) * ζ ^ 30 - ((178858 / 7081) : ℂ) * ζ ^ 31)) * commutesA10
      + ((-((184148 / 7081) : ℂ) + ((101048 / 7081) : ℂ) * ζ ^ 3 - ((151164 / 7081) : ℂ) * ζ ^ 5 + ((101048 / 7081) : ℂ) * ζ ^ 7 + ((140320 / 7081) : ℂ) * ζ ^ 10 + ((59424 / 7081) : ℂ) * ζ ^ 15 - ((101048 / 7081) : ℂ) * ζ ^ 19 + ((126376 / 7081) : ℂ) * ζ ^ 20 - ((101048 / 7081) : ℂ) * ζ ^ 23 + ((22532 / 7081) : ℂ) * ζ ^ 25 - ((177808 / 7081) : ℂ) * ζ ^ 30 + ((101048 / 7081) : ℂ) * ζ ^ 31)) * commutesA11
      + ((-(82 : ℂ) - (18 : ℂ) * ζ ^ 3 - (28 : ℂ) * ζ ^ 5 - (18 : ℂ) * ζ ^ 7 + (70 : ℂ) * ζ ^ 10 + (80 : ℂ) * ζ ^ 15 + (18 : ℂ) * ζ ^ 19 + (46 : ℂ) * ζ ^ 20 + (18 : ℂ) * ζ ^ 23 - (54 : ℂ) * ζ ^ 25 - (76 : ℂ) * ζ ^ 30 - (18 : ℂ) * ζ ^ 31)) * commutesA14
      - (
        ((((589 / 73) : ℂ) + ((160517 / 7081) : ℂ) * ζ ^ 3 - ((589 / 73) : ℂ) * ζ ^ 4 + ((127734 / 7081) : ℂ) * ζ ^ 5 - ((41347 / 7081) : ℂ) * ζ ^ 6 + ((140779 / 14162) : ℂ) * ζ ^ 8 - ((127734 / 7081) : ℂ) * ζ ^ 9 + ((590415 / 14162) : ℂ) * ζ ^ 10 + ((1567 / 14162) : ℂ) * ζ ^ 13 - ((673109 / 14162) : ℂ) * ζ ^ 14 + ((280671 / 14162) : ℂ) * ζ ^ 15 + ((77595 / 7081) : ℂ) * ζ ^ 18 - ((280671 / 14162) : ℂ) * ζ ^ 19 - ((247993 / 14162) : ℂ) * ζ ^ 20 + ((41347 / 7081) : ℂ) * ζ ^ 22 - ((56477 / 7081) : ℂ) * ζ ^ 23 + ((247993 / 14162) : ℂ) * ζ ^ 24 - ((206219 / 7081) : ℂ) * ζ ^ 25 + ((41347 / 7081) : ℂ) * ζ ^ 26 - ((264 / 73) : ℂ) * ζ ^ 28 + ((206219 / 7081) : ℂ) * ζ ^ 29 - ((41347 / 7081) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((-((328 / 73) : ℂ) + ((6341 / 14162) : ℂ) * ζ ^ 3 + ((328 / 73) : ℂ) * ζ ^ 4 - ((87867 / 7081) : ℂ) * ζ ^ 5 + ((135171 / 14162) : ℂ) * ζ ^ 6 + ((22682 / 7081) : ℂ) * ζ ^ 8 + ((87867 / 7081) : ℂ) * ζ ^ 9 - ((731065 / 14162) : ℂ) * ζ ^ 10 - ((147067 / 14162) : ℂ) * ζ ^ 13 + ((433118 / 7081) : ℂ) * ζ ^ 14 - ((331499 / 14162) : ℂ) * ζ ^ 15 - ((303217 / 7081) : ℂ) * ζ ^ 18 + ((331499 / 14162) : ℂ) * ζ ^ 19 + ((382938 / 7081) : ℂ) * ζ ^ 20 - ((135171 / 14162) : ℂ) * ζ ^ 22 - ((40791 / 14162) : ℂ) * ζ ^ 23 - ((382938 / 7081) : ℂ) * ζ ^ 24 + ((19879 / 14162) : ℂ) * ζ ^ 25 - ((135171 / 14162) : ℂ) * ζ ^ 26 + ((3249 / 73) : ℂ) * ζ ^ 28 - ((19879 / 14162) : ℂ) * ζ ^ 29 + ((135171 / 14162) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((72697 / 14162) : ℂ) - ((219271 / 7081) : ℂ) * ζ ^ 3 + ((72697 / 14162) : ℂ) * ζ ^ 4 - ((493955 / 14162) : ℂ) * ζ ^ 5 + ((71366 / 7081) : ℂ) * ζ ^ 6 - ((389019 / 14162) : ℂ) * ζ ^ 8 + ((493955 / 14162) : ℂ) * ζ ^ 9 - ((29875 / 14162) : ℂ) * ζ ^ 10 - ((26529 / 7081) : ℂ) * ζ ^ 13 + ((172607 / 14162) : ℂ) * ζ ^ 14 + ((180550 / 7081) : ℂ) * ζ ^ 15 + ((169969 / 7081) : ℂ) * ζ ^ 18 - ((180550 / 7081) : ℂ) * ζ ^ 19 + ((54455 / 7081) : ℂ) * ζ ^ 20 - ((71366 / 7081) : ℂ) * ζ ^ 22 + ((529577 / 14162) : ℂ) * ζ ^ 23 - ((54455 / 7081) : ℂ) * ζ ^ 24 + ((461528 / 7081) : ℂ) * ζ ^ 25 - ((71366 / 7081) : ℂ) * ζ ^ 26 + ((13503 / 7081) : ℂ) * ζ ^ 28 - ((461528 / 7081) : ℂ) * ζ ^ 29 + ((71366 / 7081) : ℂ) * ζ ^ 30)) * Y 1 2
        + ((-((80260 / 7081) : ℂ) + ((28215 / 7081) : ℂ) * ζ ^ 3 + ((80260 / 7081) : ℂ) * ζ ^ 4 - ((118704 / 7081) : ℂ) * ζ ^ 5 + ((37176 / 7081) : ℂ) * ζ ^ 6 - ((89874 / 7081) : ℂ) * ζ ^ 8 + ((118704 / 7081) : ℂ) * ζ ^ 9 + ((89259 / 7081) : ℂ) * ζ ^ 10 - ((63910 / 7081) : ℂ) * ζ ^ 13 - ((52083 / 7081) : ℂ) * ζ ^ 14 + ((98990 / 7081) : ℂ) * ζ ^ 15 + ((38699 / 7081) : ℂ) * ζ ^ 18 - ((98990 / 7081) : ℂ) * ζ ^ 19 + ((44503 / 7081) : ℂ) * ζ ^ 20 - ((37176 / 7081) : ℂ) * ζ ^ 22 + ((9343 / 7081) : ℂ) * ζ ^ 23 - ((44503 / 7081) : ℂ) * ζ ^ 24 + ((66703 / 7081) : ℂ) * ζ ^ 25 - ((37176 / 7081) : ℂ) * ζ ^ 26 + ((48717 / 7081) : ℂ) * ζ ^ 28 - ((66703 / 7081) : ℂ) * ζ ^ 29 + ((37176 / 7081) : ℂ) * ζ ^ 30)) * Y 2 1
        + ((((549 / 146) : ℂ) + ((401 / 73) : ℂ) * ζ ^ 3 - ((549 / 146) : ℂ) * ζ ^ 4 + ((3205 / 73) : ℂ) * ζ ^ 5 + ((243 / 146) : ℂ) * ζ ^ 6 + ((1337 / 73) : ℂ) * ζ ^ 8 - ((3205 / 73) : ℂ) * ζ ^ 9 + ((588 / 73) : ℂ) * ζ ^ 10 + ((5443 / 146) : ℂ) * ζ ^ 13 - ((933 / 146) : ℂ) * ζ ^ 14 - ((2361 / 146) : ℂ) * ζ ^ 15 + ((373 / 73) : ℂ) * ζ ^ 18 + ((2361 / 146) : ℂ) * ζ ^ 19 - ((4299 / 146) : ℂ) * ζ ^ 20 - ((243 / 146) : ℂ) * ζ ^ 22 - ((1437 / 73) : ℂ) * ζ ^ 23 + ((4299 / 146) : ℂ) * ζ ^ 24 + ((31 / 73) : ℂ) * ζ ^ 25 - ((243 / 146) : ℂ) * ζ ^ 26 - ((2138 / 73) : ℂ) * ζ ^ 28 - ((31 / 73) : ℂ) * ζ ^ 29 + ((243 / 146) : ℂ) * ζ ^ 30)) * Y 3 4
        + ((-((334 / 73) : ℂ) - ((1724 / 73) : ℂ) * ζ ^ 3 + ((334 / 73) : ℂ) * ζ ^ 4 - ((895 / 146) : ℂ) * ζ ^ 5 - ((234 / 73) : ℂ) * ζ ^ 6 - ((996 / 73) : ℂ) * ζ ^ 8 + ((895 / 146) : ℂ) * ζ ^ 9 + ((725 / 73) : ℂ) * ζ ^ 10 + ((750 / 73) : ℂ) * ζ ^ 13 - ((959 / 73) : ℂ) * ζ ^ 14 + ((262 / 73) : ℂ) * ζ ^ 15 + ((4579 / 146) : ℂ) * ζ ^ 18 - ((262 / 73) : ℂ) * ζ ^ 19 - ((5339 / 146) : ℂ) * ζ ^ 20 + ((234 / 73) : ℂ) * ζ ^ 22 + ((1585 / 146) : ℂ) * ζ ^ 23 + ((5339 / 146) : ℂ) * ζ ^ 24 + ((2060 / 73) : ℂ) * ζ ^ 25 + ((234 / 73) : ℂ) * ζ ^ 26 - ((2985 / 73) : ℂ) * ζ ^ 28 - ((2060 / 73) : ℂ) * ζ ^ 29 - ((234 / 73) : ℂ) * ζ ^ 30)) * Y 4 4
        + (((1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 3 - ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 5 - ((1 / 2) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 9 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 25 + ((1 / 2) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 29 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation


/-- A matrix commuting with both transformed row 12 generators is
scalar. -/
theorem alternatingSixAmbientRow12Transformed_scalar_commutant
    (Y : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow12TransformedGeneratorA =
        alternatingSixAmbientRow12TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow12GeneratorBDiagonal =
        alternatingSixAmbientRow12GeneratorBDiagonal * Y) :
    ∃ c : ℂ,
      Y = c • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 3 (by decide)
  have hY54 :
      Y 5 4 = 0 :=
    alternatingSixAmbientRow12_off_block
      Y commutesDiagonal 5 4 (by decide)

  have reducedY00 : Y 0 0 = Y 5 5 :=
    row12_reducedY00 Y commutesA commutesDiagonal
  have reducedY11 : Y 1 1 = Y 5 5 :=
    row12_reducedY11 Y commutesA commutesDiagonal
  have reducedY12 : Y 1 2 = 0 :=
    row12_reducedY12 Y commutesA commutesDiagonal
  have reducedY21 : Y 2 1 = 0 :=
    row12_reducedY21 Y commutesA commutesDiagonal
  have reducedY22 : Y 2 2 = Y 5 5 :=
    row12_reducedY22 Y commutesA commutesDiagonal
  have reducedY33 : Y 3 3 = Y 5 5 :=
    row12_reducedY33 Y commutesA commutesDiagonal
  have reducedY34 : Y 3 4 = 0 :=
    row12_reducedY34 Y commutesA commutesDiagonal
  have reducedY43 : Y 4 3 = 0 :=
    row12_reducedY43 Y commutesA commutesDiagonal
  have reducedY44 : Y 4 4 = Y 5 5 :=
    row12_reducedY44 Y commutesA commutesDiagonal

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

/-- Every matrix commuting with both original row 12 presentation
generators is scalar. -/
theorem alternatingSixAmbientRow12_scalar_commutant
    (X : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesA :
      X * alternatingSixFiveAmbient_row12_matrixA =
        alternatingSixFiveAmbient_row12_matrixA * X)
    (commutesB :
      X * alternatingSixFiveAmbient_row12_matrixB =
        alternatingSixFiveAmbient_row12_matrixB * X) :
    ∃ c : ℂ,
      X = c • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  apply Matrix.scalar_commutant_of_diagonal_basis
    alternatingSixFiveAmbient_row12_matrixA
    alternatingSixFiveAmbient_row12_matrixB
    alternatingSixAmbientRow12Eigenbasis
    alternatingSixAmbientRow12EigenbasisInverse
    alternatingSixAmbientRow12TransformedGeneratorA
    alternatingSixAmbientRow12GeneratorBEigenvalue
    alternatingSixAmbientRow12EigenbasisInverse_mul
    alternatingSixAmbientRow12Eigenbasis_mul_inverse
    alternatingSixAmbientRow12GeneratorB_mul_eigenbasis
    alternatingSixAmbientRow12TransformedGeneratorA_eq
    alternatingSixAmbientRow12Transformed_scalar_commutant
    X commutesA commutesB

end InductiveMcKay
end McKayConjecture
