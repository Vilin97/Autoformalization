/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DiagonalBasisMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow11DiagonalData

/-!
# Scalar common commutant for ambient row 11

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
private theorem alternatingSixAmbientRow11_off_block
    (Y : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow11GeneratorBDiagonal =
        alternatingSixAmbientRow11GeneratorBDiagonal * Y)
    (i j : Fin 6)
    (different :
      alternatingSixAmbientRow11EigenvalueLabel i ≠
        alternatingSixAmbientRow11EigenvalueLabel j) :
    Y i j = 0 := by
  apply Matrix.entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
    Y alternatingSixAmbientRow11GeneratorBEigenvalue
  · exact commutesDiagonal
  · intro equalEigenvalues
    apply different
    apply alternatingSixOrderFourEigenvalue_injective
    simpa [
      alternatingSixAmbientRow11GeneratorBEigenvalue] using
      equalEigenvalues.symm

private theorem row11_reducedY00
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow11TransformedGeneratorA =
        alternatingSixAmbientRow11TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow11GeneratorBDiagonal =
        alternatingSixAmbientRow11GeneratorBDiagonal * Y) :
    Y 0 0 = Y 5 5 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 1 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY21,
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA05
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY15,
      hY25,
      hY35,
      hY45] at commutesA05

  linear_combination
    ((((2 / 3) : ℂ) - ((4 / 3) : ℂ) * ζ ^ 20)) * commutesA01
      + ((((8 / 3) : ℂ) + ((16 / 3) : ℂ) * ζ ^ 10 + ((8 / 3) : ℂ) * ζ ^ 20 - ((8 / 3) : ℂ) * ζ ^ 30)) * commutesA05
      - (
        ((-((2 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 4 - ((2 / 3) : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((1 / 3) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row11_reducedY01
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow11TransformedGeneratorA =
        alternatingSixAmbientRow11TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow11GeneratorBDiagonal =
        alternatingSixAmbientRow11GeneratorBDiagonal * Y) :
    Y 0 1 = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 1 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY21,
      hY31,
      hY41,
      hY51] at commutesA01

  linear_combination
    ((((2 / 3) : ℂ) * ζ ^ 10 - ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA01
      - (
        ((-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28)) * Y 0 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row11_reducedY10
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow11TransformedGeneratorA =
        alternatingSixAmbientRow11TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow11GeneratorBDiagonal =
        alternatingSixAmbientRow11GeneratorBDiagonal * Y) :
    Y 1 0 = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY21,
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA02
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY12,
      hY32,
      hY42,
      hY52] at commutesA02
  have commutesA10 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA10
  simp only [Fin.sum_univ_succ] at commutesA10
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY12,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA10
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA12
  simp only [
      hY02,
      hY12,
      hY13,
      hY14,
      hY15,
      hY32,
      hY42,
      hY52] at commutesA12

  linear_combination
    ((((4 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 20)) * commutesA01
      + ((-((8 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 20)) * commutesA02
      + ((-((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 20 + ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA10
      + ((((4 / 3) : ℂ) - ((8 / 3) : ℂ) * ζ ^ 20)) * commutesA12
      - (
        ((((1 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((1 / 6) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((ζ ^ 10 - ζ ^ 14 + ζ ^ 18)) * Y 2 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row11_reducedY11
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow11TransformedGeneratorA =
        alternatingSixAmbientRow11TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow11GeneratorBDiagonal =
        alternatingSixAmbientRow11GeneratorBDiagonal * Y) :
    Y 1 1 = Y 5 5 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY21,
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA02
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY12,
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA05
  simp only [
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY12,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA10
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA12
  simp only [
      hY02,
      hY12,
      hY13,
      hY14,
      hY15,
      hY32,
      hY42,
      hY52] at commutesA12

  linear_combination
    ((((4 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 30)) * commutesA01
      + ((((4 / 3) : ℂ) - ((8 / 3) : ℂ) * ζ ^ 10 - ((8 / 3) : ℂ) * ζ ^ 20 + ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA02
      + ((((8 / 3) : ℂ) + ((16 / 3) : ℂ) * ζ ^ 10 + ((8 / 3) : ℂ) * ζ ^ 20 - ((8 / 3) : ℂ) * ζ ^ 30)) * commutesA05
      + ((((4 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 30)) * commutesA10
      + ((((4 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 10 + ((4 / 3) : ℂ) * ζ ^ 20 - ((8 / 3) : ℂ) * ζ ^ 30)) * commutesA12
      - (
        ((((3 / 2) : ℂ) * ζ ^ 10 - ((3 / 2) : ℂ) * ζ ^ 14 + ((3 / 2) : ℂ) * ζ ^ 18 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)) * Y 0 0
        + ((-((1 / 3) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((ζ ^ 20 - ζ ^ 24 + ζ ^ 28)) * Y 1 0
        + ((-((2 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 4 - ((2 / 3) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + ζ ^ 20 - ζ ^ 24 + ζ ^ 28)) * Y 2 2
        + ((((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row11_reducedY22
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow11TransformedGeneratorA =
        alternatingSixAmbientRow11TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow11GeneratorBDiagonal =
        alternatingSixAmbientRow11GeneratorBDiagonal * Y) :
    Y 2 2 = Y 5 5 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY21,
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA02
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY12,
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA05
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY15,
      hY25,
      hY35,
      hY45] at commutesA05

  linear_combination
    ((((2 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 10 - ((4 / 3) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 30)) * commutesA01
      + ((-((8 / 3) : ℂ) * ζ ^ 10 + ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA02
      + ((((8 / 3) : ℂ) + ((16 / 3) : ℂ) * ζ ^ 10 + ((8 / 3) : ℂ) * ζ ^ 20 - ((8 / 3) : ℂ) * ζ ^ 30)) * commutesA05
      - (
        ((((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((1 / 3) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-(1 : ℂ) + ζ ^ 4 - ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row11_reducedY33
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow11TransformedGeneratorA =
        alternatingSixAmbientRow11TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow11GeneratorBDiagonal =
        alternatingSixAmbientRow11GeneratorBDiagonal * Y) :
    Y 3 3 = Y 5 5 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 3 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY21,
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA02
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY12,
      hY32,
      hY42,
      hY52] at commutesA02
  have commutesA03 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (3 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA03
  simp only [Fin.sum_univ_succ] at commutesA03
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA03
  simp only [
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA05
  simp only [
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY12,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA10
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA12
  simp only [
      hY02,
      hY12,
      hY13,
      hY14,
      hY15,
      hY32,
      hY42,
      hY52] at commutesA12
  have commutesA13 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (3 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA13
  simp only [Fin.sum_univ_succ] at commutesA13
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA13
  simp only [
      hY03,
      hY12,
      hY13,
      hY14,
      hY15,
      hY23,
      hY53] at commutesA13

  linear_combination
    ((((4 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 30)) * commutesA01
      + ((((4 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 20)) * commutesA02
      + ((((4 / 3) : ℂ) + (4 : ℂ) * ζ ^ 10 + ((4 / 3) : ℂ) * ζ ^ 20)) * commutesA03
      + ((((8 / 3) : ℂ) + ((16 / 3) : ℂ) * ζ ^ 10 + ((8 / 3) : ℂ) * ζ ^ 20 - ((8 / 3) : ℂ) * ζ ^ 30)) * commutesA05
      + ((-((4 / 3) : ℂ) * ζ ^ 10 + ((8 / 3) : ℂ) * ζ ^ 30)) * commutesA10
      + ((-((8 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 20)) * commutesA12
      + ((((4 / 3) : ℂ) - ((4 / 3) : ℂ) * ζ ^ 10 + ((4 / 3) : ℂ) * ζ ^ 20 + ((8 / 3) : ℂ) * ζ ^ 30)) * commutesA13
      - (
        ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ζ ^ 20 - ζ ^ 24 + ζ ^ 28)) * Y 0 0
        + ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18)) * Y 0 1
        + ((-((5 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 4 - ((5 / 6) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 20 + ((4 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((1 / 6) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 - ((5 / 3) : ℂ) * ζ ^ 20 + ((5 / 3) : ℂ) * ζ ^ 24 - ((5 / 3) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((3 / 2) : ℂ) * ζ ^ 10 - ((3 / 2) : ℂ) * ζ ^ 14 + ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28)) * Y 3 3
        + ((-((4 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 4 - ((4 / 3) : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 10 + (2 : ℂ) * ζ ^ 14 - (2 : ℂ) * ζ ^ 18 - ((4 / 3) : ℂ) * ζ ^ 20 + ((4 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28)) * Y 4 3
        + ((((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row11_reducedY34
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow11TransformedGeneratorA =
        alternatingSixAmbientRow11TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow11GeneratorBDiagonal =
        alternatingSixAmbientRow11GeneratorBDiagonal * Y) :
    Y 3 4 = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY54 :
      Y 5 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 4 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY21,
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA02
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY12,
      hY32,
      hY42,
      hY52] at commutesA02
  have commutesA04 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (4 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA04
  simp only [Fin.sum_univ_succ] at commutesA04
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA04
  simp only [
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY12,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA10
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA12
  simp only [
      hY02,
      hY12,
      hY13,
      hY14,
      hY15,
      hY32,
      hY42,
      hY52] at commutesA12
  have commutesA14 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (4 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA14
  simp only [Fin.sum_univ_succ] at commutesA14
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA14
  simp only [
      hY04,
      hY12,
      hY13,
      hY14,
      hY15,
      hY24,
      hY54] at commutesA14

  linear_combination
    ((-((4 / 3) : ℂ) * ζ ^ 10 - ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA01
      + ((-((8 / 3) : ℂ) - ((8 / 3) : ℂ) * ζ ^ 20)) * commutesA02
      + ((((4 / 3) : ℂ) + (4 : ℂ) * ζ ^ 10 + ((4 / 3) : ℂ) * ζ ^ 20)) * commutesA04
      + ((((8 / 3) : ℂ) - ((4 / 3) : ℂ) * ζ ^ 10 - ((4 / 3) : ℂ) * ζ ^ 20 - ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA10
      + ((((16 / 3) : ℂ) - ((8 / 3) : ℂ) * ζ ^ 20)) * commutesA12
      + ((((4 / 3) : ℂ) - ((4 / 3) : ℂ) * ζ ^ 10 + ((4 / 3) : ℂ) * ζ ^ 20 + ((8 / 3) : ℂ) * ζ ^ 30)) * commutesA14
      - (
        ((((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((1 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + (((1 : ℂ) - ζ ^ 4 + ζ ^ 8 + (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 24 + (2 : ℂ) * ζ ^ 28)) * Y 1 0
        + (((1 : ℂ) - ζ ^ 4 + ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 + (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 24 + (2 : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((3 / 2) : ℂ) * ζ ^ 10 - ((3 / 2) : ℂ) * ζ ^ 14 + ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28)) * Y 3 4
        + ((-((4 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 4 - ((4 / 3) : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 10 + (2 : ℂ) * ζ ^ 14 - (2 : ℂ) * ζ ^ 18 - ((4 / 3) : ℂ) * ζ ^ 20 + ((4 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28)) * Y 4 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row11_reducedY43
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow11TransformedGeneratorA =
        alternatingSixAmbientRow11TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow11GeneratorBDiagonal =
        alternatingSixAmbientRow11GeneratorBDiagonal * Y) :
    Y 4 3 = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 3 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY21,
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA02
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY12,
      hY32,
      hY42,
      hY52] at commutesA02
  have commutesA03 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (3 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA03
  simp only [Fin.sum_univ_succ] at commutesA03
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA03
  simp only [
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY12,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA10
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA12
  simp only [
      hY02,
      hY12,
      hY13,
      hY14,
      hY15,
      hY32,
      hY42,
      hY52] at commutesA12
  have commutesA13 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (3 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA13
  simp only [Fin.sum_univ_succ] at commutesA13
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA13
  simp only [
      hY03,
      hY12,
      hY13,
      hY14,
      hY15,
      hY23,
      hY53] at commutesA13

  linear_combination
    ((((2 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 20)) * commutesA01
      + ((((4 / 3) : ℂ) * ζ ^ 10 + (2 : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 30)) * commutesA02
      + (((2 : ℂ) + ((8 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 30)) * commutesA03
      + ((-((2 / 3) : ℂ) - (2 : ℂ) * ζ ^ 10 + ((4 / 3) : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 30)) * commutesA10
      + ((-(2 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 10 + ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA12
      + ((-((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 10 + ((10 / 3) : ℂ) * ζ ^ 20 + ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA13
      - (
        ((-((13 / 12) : ℂ) + ((13 / 12) : ℂ) * ζ ^ 4 - ((13 / 12) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 18 + ((7 / 6) : ℂ) * ζ ^ 20 - ((7 / 6) : ℂ) * ζ ^ 24 + ((7 / 6) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((5 / 12) : ℂ) - ((5 / 12) : ℂ) * ζ ^ 4 + ((5 / 12) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 - ((4 / 3) : ℂ) * ζ ^ 20 + ((4 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((1 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 4 - ((1 / 12) : ℂ) * ζ ^ 8 - ((5 / 4) : ℂ) * ζ ^ 10 + ((5 / 4) : ℂ) * ζ ^ 14 - ((5 / 4) : ℂ) * ζ ^ 18 - ((5 / 6) : ℂ) * ζ ^ 20 + ((5 / 6) : ℂ) * ζ ^ 24 - ((5 / 6) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((((7 / 6) : ℂ) - ((7 / 6) : ℂ) * ζ ^ 4 + ((7 / 6) : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 28)) * Y 3 3
        + ((-((7 / 3) : ℂ) + ((7 / 3) : ℂ) * ζ ^ 4 - ((7 / 3) : ℂ) * ζ ^ 8 - ((3 / 2) : ℂ) * ζ ^ 10 + ((3 / 2) : ℂ) * ζ ^ 14 - ((3 / 2) : ℂ) * ζ ^ 18 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)) * Y 4 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row11_reducedY44
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow11TransformedGeneratorA =
        alternatingSixAmbientRow11TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow11GeneratorBDiagonal =
        alternatingSixAmbientRow11GeneratorBDiagonal * Y) :
    Y 4 4 = Y 5 5 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY54 :
      Y 5 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 4 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY21,
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA02
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY12,
      hY32,
      hY42,
      hY52] at commutesA02
  have commutesA04 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (4 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA04
  simp only [Fin.sum_univ_succ] at commutesA04
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA04
  simp only [
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA05
  simp only [
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
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA10
  simp only [
      hY12,
      hY13,
      hY14,
      hY15,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA10
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA12
  simp only [
      hY02,
      hY12,
      hY13,
      hY14,
      hY15,
      hY32,
      hY42,
      hY52] at commutesA12
  have commutesA14 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (4 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA14
  simp only [Fin.sum_univ_succ] at commutesA14
  simp [
      alternatingSixAmbientRow11TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA14
  simp only [
      hY04,
      hY12,
      hY13,
      hY14,
      hY15,
      hY24,
      hY54] at commutesA14

  linear_combination
    ((-((2 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 20 - ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA01
      + ((-((8 / 3) : ℂ) * ζ ^ 10 - (4 : ℂ) * ζ ^ 20 + ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA02
      + (((2 : ℂ) + ((8 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 30)) * commutesA04
      + ((((8 / 3) : ℂ) + ((16 / 3) : ℂ) * ζ ^ 10 + ((8 / 3) : ℂ) * ζ ^ 20 - ((8 / 3) : ℂ) * ζ ^ 30)) * commutesA05
      + ((((4 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 20 - ((10 / 3) : ℂ) * ζ ^ 30)) * commutesA10
      + (((4 : ℂ) + ((4 / 3) : ℂ) * ζ ^ 10 - ((8 / 3) : ℂ) * ζ ^ 30)) * commutesA12
      + ((-((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 10 + ((10 / 3) : ℂ) * ζ ^ 20 + ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA14
      - (
        ((((3 / 2) : ℂ) - ((3 / 2) : ℂ) * ζ ^ 4 + ((3 / 2) : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 10 - (2 : ℂ) * ζ ^ 14 + (2 : ℂ) * ζ ^ 18 - (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((1 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 + (3 : ℂ) * ζ ^ 20 - (3 : ℂ) * ζ ^ 24 + (3 : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((1 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 8 + ((3 / 2) : ℂ) * ζ ^ 10 - ((3 / 2) : ℂ) * ζ ^ 14 + ((3 / 2) : ℂ) * ζ ^ 18 + ((5 / 3) : ℂ) * ζ ^ 20 - ((5 / 3) : ℂ) * ζ ^ 24 + ((5 / 3) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + ζ ^ 20 - ζ ^ 24 + ζ ^ 28)) * Y 2 2
        + ((((7 / 6) : ℂ) - ((7 / 6) : ℂ) * ζ ^ 4 + ((7 / 6) : ℂ) * ζ ^ 8 + ζ ^ 10 - ζ ^ 14 + ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 28)) * Y 3 4
        + ((-((7 / 3) : ℂ) + ((7 / 3) : ℂ) * ζ ^ 4 - ((7 / 3) : ℂ) * ζ ^ 8 - ((3 / 2) : ℂ) * ζ ^ 10 + ((3 / 2) : ℂ) * ζ ^ 14 - ((3 / 2) : ℂ) * ζ ^ 18 - ζ ^ 20 + ζ ^ 24 - ζ ^ 28)) * Y 4 4
        + ((((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 8 - ζ ^ 10 + ζ ^ 14 - ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation


/-- A matrix commuting with both transformed row 11 generators is
scalar. -/
theorem alternatingSixAmbientRow11Transformed_scalar_commutant
    (Y : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow11TransformedGeneratorA =
        alternatingSixAmbientRow11TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow11GeneratorBDiagonal =
        alternatingSixAmbientRow11GeneratorBDiagonal * Y) :
    ∃ c : ℂ,
      Y = c • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY45 :
      Y 4 5 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 4 5 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 3 (by decide)
  have hY54 :
      Y 5 4 = 0 :=
    alternatingSixAmbientRow11_off_block
      Y commutesDiagonal 5 4 (by decide)

  have reducedY00 : Y 0 0 = Y 5 5 :=
    row11_reducedY00 Y commutesA commutesDiagonal
  have reducedY01 : Y 0 1 = 0 :=
    row11_reducedY01 Y commutesA commutesDiagonal
  have reducedY10 : Y 1 0 = 0 :=
    row11_reducedY10 Y commutesA commutesDiagonal
  have reducedY11 : Y 1 1 = Y 5 5 :=
    row11_reducedY11 Y commutesA commutesDiagonal
  have reducedY22 : Y 2 2 = Y 5 5 :=
    row11_reducedY22 Y commutesA commutesDiagonal
  have reducedY33 : Y 3 3 = Y 5 5 :=
    row11_reducedY33 Y commutesA commutesDiagonal
  have reducedY34 : Y 3 4 = 0 :=
    row11_reducedY34 Y commutesA commutesDiagonal
  have reducedY43 : Y 4 3 = 0 :=
    row11_reducedY43 Y commutesA commutesDiagonal
  have reducedY44 : Y 4 4 = Y 5 5 :=
    row11_reducedY44 Y commutesA commutesDiagonal

  refine ⟨Y 5 5, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [
      hY02,
      hY03,
      hY04,
      hY05,
      hY12,
      hY13,
      hY14,
      hY15,
      hY20,
      hY21,
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
      reducedY01,
      reducedY10,
      reducedY11,
      reducedY22,
      reducedY33,
      reducedY34,
      reducedY43,
      reducedY44]

/-- Every matrix commuting with both original row 11 presentation
generators is scalar. -/
theorem alternatingSixAmbientRow11_scalar_commutant
    (X : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesA :
      X * alternatingSixFiveAmbient_row11_matrixA =
        alternatingSixFiveAmbient_row11_matrixA * X)
    (commutesB :
      X * alternatingSixFiveAmbient_row11_matrixB =
        alternatingSixFiveAmbient_row11_matrixB * X) :
    ∃ c : ℂ,
      X = c • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  apply Matrix.scalar_commutant_of_diagonal_basis
    alternatingSixFiveAmbient_row11_matrixA
    alternatingSixFiveAmbient_row11_matrixB
    alternatingSixAmbientRow11Eigenbasis
    alternatingSixAmbientRow11EigenbasisInverse
    alternatingSixAmbientRow11TransformedGeneratorA
    alternatingSixAmbientRow11GeneratorBEigenvalue
    alternatingSixAmbientRow11EigenbasisInverse_mul
    alternatingSixAmbientRow11Eigenbasis_mul_inverse
    alternatingSixAmbientRow11GeneratorB_mul_eigenbasis
    alternatingSixAmbientRow11TransformedGeneratorA_eq
    alternatingSixAmbientRow11Transformed_scalar_commutant
    X commutesA commutesB

end InductiveMcKay
end McKayConjecture
