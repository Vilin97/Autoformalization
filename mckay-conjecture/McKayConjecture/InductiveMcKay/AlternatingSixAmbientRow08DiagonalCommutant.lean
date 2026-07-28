/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DiagonalBasisMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow08DiagonalData

/-!
# Scalar common commutant for ambient row 08

The second generator is diagonal in the checked basis.  Its repeated
eigenspaces leave only 7 possible matrix
coordinates, and the generated exact row reduction for the transformed first
generator reduces those coordinates to a single scalar.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Entries between distinct second-generator eigenspaces vanish in its
commutant. -/
private theorem alternatingSixAmbientRow08_off_block
    (Y : Matrix (Fin 5) (Fin 5) ℂ)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow08GeneratorBDiagonal =
        alternatingSixAmbientRow08GeneratorBDiagonal * Y)
    (i j : Fin 5)
    (different :
      alternatingSixAmbientRow08EigenvalueLabel i ≠
        alternatingSixAmbientRow08EigenvalueLabel j) :
    Y i j = 0 := by
  apply Matrix.entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
    Y alternatingSixAmbientRow08GeneratorBEigenvalue
  · exact commutesDiagonal
  · intro equalEigenvalues
    apply different
    apply alternatingSixOrderFourEigenvalue_injective
    simpa [
      alternatingSixAmbientRow08GeneratorBEigenvalue] using
      equalEigenvalues.symm

private theorem row08_reducedY00
    (Y : Matrix (Fin 5)
      (Fin 5) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow08TransformedGeneratorA =
        alternatingSixAmbientRow08TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow08GeneratorBDiagonal =
        alternatingSixAmbientRow08GeneratorBDiagonal * Y) :
    Y 0 0 = Y 4 4 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 3 4 (by decide)

  have commutesA04 :=
    congrFun (congrFun commutesA
      (0 : Fin 5))
      (4 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA04
  simp only [Fin.sum_univ_succ] at commutesA04
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA04
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY14,
      hY24,
      hY34] at commutesA04

  linear_combination
    ((-((4 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA04
      - (
        ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 4 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row08_reducedY11
    (Y : Matrix (Fin 5)
      (Fin 5) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow08TransformedGeneratorA =
        alternatingSixAmbientRow08TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow08GeneratorBDiagonal =
        alternatingSixAmbientRow08GeneratorBDiagonal * Y) :
    Y 1 1 = Y 4 4 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 4 1 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 5))
      (1 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY14,
      hY21,
      hY24,
      hY31,
      hY34,
      hY41] at commutesA01
  have commutesA04 :=
    congrFun (congrFun commutesA
      (0 : Fin 5))
      (4 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA04
  simp only [Fin.sum_univ_succ] at commutesA04
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA04
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY14,
      hY21,
      hY24,
      hY31,
      hY34,
      hY41] at commutesA04

  linear_combination
    ((((4 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA01
      + ((-((4 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA04
      - (
        ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 4 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row08_reducedY22
    (Y : Matrix (Fin 5)
      (Fin 5) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow08TransformedGeneratorA =
        alternatingSixAmbientRow08TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow08GeneratorBDiagonal =
        alternatingSixAmbientRow08GeneratorBDiagonal * Y) :
    Y 2 2 = Y 4 4 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 4 2 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 5))
      (1 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY21,
      hY24,
      hY31,
      hY34,
      hY41,
      hY42] at commutesA01
  have commutesA02 :=
    congrFun (congrFun commutesA
      (0 : Fin 5))
      (2 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA02
  simp only [Fin.sum_univ_succ] at commutesA02
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA02
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY21,
      hY24,
      hY31,
      hY34,
      hY41,
      hY42] at commutesA02
  have commutesA04 :=
    congrFun (congrFun commutesA
      (0 : Fin 5))
      (4 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA04
  simp only [Fin.sum_univ_succ] at commutesA04
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA04
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY21,
      hY24,
      hY31,
      hY34,
      hY41,
      hY42] at commutesA04
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 5))
      (2 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA12
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY21,
      hY24,
      hY31,
      hY34,
      hY41,
      hY42] at commutesA12

  linear_combination
    ((-((2 / 3) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 30)) * commutesA01
      + (((1 : ℂ) - ((1 / 3) : ℂ) * ζ ^ 30)) * commutesA02
      + ((-((4 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA04
      + (((1 : ℂ))) * commutesA12
      - (
        ((-((3 / 8) : ℂ) + ((3 / 8) : ℂ) * ζ ^ 4 - ((3 / 8) : ℂ) * ζ ^ 8 - ((3 / 8) : ℂ) * ζ ^ 20 + ((3 / 8) : ℂ) * ζ ^ 24 - ((3 / 8) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((1 / 8) : ℂ) + ((1 / 8) : ℂ) * ζ ^ 4 - ((1 / 8) : ℂ) * ζ ^ 8 - ((1 / 8) : ℂ) * ζ ^ 20 + ((1 / 8) : ℂ) * ζ ^ 24 - ((1 / 8) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 4 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row08_reducedY23
    (Y : Matrix (Fin 5)
      (Fin 5) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow08TransformedGeneratorA =
        alternatingSixAmbientRow08TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow08GeneratorBDiagonal =
        alternatingSixAmbientRow08GeneratorBDiagonal * Y) :
    Y 2 3 = 0 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 4 3 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 5))
      (1 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY21,
      hY31,
      hY41,
      hY43] at commutesA01
  have commutesA03 :=
    congrFun (congrFun commutesA
      (0 : Fin 5))
      (3 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA03
  simp only [Fin.sum_univ_succ] at commutesA03
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA03
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY21,
      hY31,
      hY41,
      hY43] at commutesA03
  have commutesA13 :=
    congrFun (congrFun commutesA
      (1 : Fin 5))
      (3 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA13
  simp only [Fin.sum_univ_succ] at commutesA13
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA13
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY21,
      hY31,
      hY41,
      hY43] at commutesA13

  linear_combination
    ((-((2 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 30)) * commutesA01
      + (((1 : ℂ) - ((1 / 3) : ℂ) * ζ ^ 30)) * commutesA03
      + (((1 : ℂ))) * commutesA13
      - (
        ((-((1 / 8) : ℂ) + ((1 / 8) : ℂ) * ζ ^ 4 - ((1 / 8) : ℂ) * ζ ^ 8 - ((1 / 8) : ℂ) * ζ ^ 20 + ((1 / 8) : ℂ) * ζ ^ 24 - ((1 / 8) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((1 / 8) : ℂ) - ((1 / 8) : ℂ) * ζ ^ 4 + ((1 / 8) : ℂ) * ζ ^ 8 + ((1 / 8) : ℂ) * ζ ^ 20 - ((1 / 8) : ℂ) * ζ ^ 24 + ((1 / 8) : ℂ) * ζ ^ 28)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row08_reducedY32
    (Y : Matrix (Fin 5)
      (Fin 5) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow08TransformedGeneratorA =
        alternatingSixAmbientRow08TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow08GeneratorBDiagonal =
        alternatingSixAmbientRow08GeneratorBDiagonal * Y) :
    Y 3 2 = 0 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 4 2 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 5))
      (1 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY21,
      hY31,
      hY41,
      hY42] at commutesA01
  have commutesA02 :=
    congrFun (congrFun commutesA
      (0 : Fin 5))
      (2 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA02
  simp only [Fin.sum_univ_succ] at commutesA02
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA02
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY21,
      hY31,
      hY41,
      hY42] at commutesA02
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 5))
      (2 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA12
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY21,
      hY31,
      hY41,
      hY42] at commutesA12

  linear_combination
    (((2 : ℂ) - ζ ^ 30)) * commutesA01
      + ((-((1 / 3) : ℂ) + ζ ^ 30)) * commutesA02
      + ((-(3 : ℂ))) * commutesA12
      - (
        ((-((3 / 8) : ℂ) + ((3 / 8) : ℂ) * ζ ^ 4 - ((3 / 8) : ℂ) * ζ ^ 8 - ((3 / 8) : ℂ) * ζ ^ 20 + ((3 / 8) : ℂ) * ζ ^ 24 - ((3 / 8) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((3 / 8) : ℂ) - ((3 / 8) : ℂ) * ζ ^ 4 + ((3 / 8) : ℂ) * ζ ^ 8 + ((3 / 8) : ℂ) * ζ ^ 20 - ((3 / 8) : ℂ) * ζ ^ 24 + ((3 / 8) : ℂ) * ζ ^ 28)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row08_reducedY33
    (Y : Matrix (Fin 5)
      (Fin 5) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow08TransformedGeneratorA =
        alternatingSixAmbientRow08TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow08GeneratorBDiagonal =
        alternatingSixAmbientRow08GeneratorBDiagonal * Y) :
    Y 3 3 = Y 4 4 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 4 3 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 5))
      (1 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY21,
      hY24,
      hY31,
      hY34,
      hY41,
      hY43] at commutesA01
  have commutesA03 :=
    congrFun (congrFun commutesA
      (0 : Fin 5))
      (3 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA03
  simp only [Fin.sum_univ_succ] at commutesA03
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA03
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY21,
      hY24,
      hY31,
      hY34,
      hY41,
      hY43] at commutesA03
  have commutesA04 :=
    congrFun (congrFun commutesA
      (0 : Fin 5))
      (4 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA04
  simp only [Fin.sum_univ_succ] at commutesA04
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA04
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY21,
      hY24,
      hY31,
      hY34,
      hY41,
      hY43] at commutesA04
  have commutesA13 :=
    congrFun (congrFun commutesA
      (1 : Fin 5))
      (3 : Fin 5)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA13
  simp only [Fin.sum_univ_succ] at commutesA13
  simp [
      alternatingSixAmbientRow08TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA13
  simp only [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY21,
      hY24,
      hY31,
      hY34,
      hY41,
      hY43] at commutesA13

  linear_combination
    (((2 : ℂ) + ζ ^ 30)) * commutesA01
      + ((-((1 / 3) : ℂ) + ζ ^ 30)) * commutesA03
      + ((-((4 / 3) : ℂ) + ((4 / 3) : ℂ) * ζ ^ 30)) * commutesA04
      + ((-(3 : ℂ))) * commutesA13
      - (
        ((-((1 / 8) : ℂ) + ((1 / 8) : ℂ) * ζ ^ 4 - ((1 / 8) : ℂ) * ζ ^ 8 - ((1 / 8) : ℂ) * ζ ^ 20 + ((1 / 8) : ℂ) * ζ ^ 24 - ((1 / 8) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((3 / 8) : ℂ) + ((3 / 8) : ℂ) * ζ ^ 4 - ((3 / 8) : ℂ) * ζ ^ 8 - ((3 / 8) : ℂ) * ζ ^ 20 + ((3 / 8) : ℂ) * ζ ^ 24 - ((3 / 8) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 4 4)
        * alternatingSixComplexCyclotomicRoot_relation


/-- A matrix commuting with both transformed row 08 generators is
scalar. -/
theorem alternatingSixAmbientRow08Transformed_scalar_commutant
    (Y : Matrix (Fin 5) (Fin 5) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow08TransformedGeneratorA =
        alternatingSixAmbientRow08TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow08GeneratorBDiagonal =
        alternatingSixAmbientRow08GeneratorBDiagonal * Y) :
    ∃ c : ℂ,
      Y = c • (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow08_off_block
      Y commutesDiagonal 4 3 (by decide)

  have reducedY00 : Y 0 0 = Y 4 4 :=
    row08_reducedY00 Y commutesA commutesDiagonal
  have reducedY11 : Y 1 1 = Y 4 4 :=
    row08_reducedY11 Y commutesA commutesDiagonal
  have reducedY22 : Y 2 2 = Y 4 4 :=
    row08_reducedY22 Y commutesA commutesDiagonal
  have reducedY23 : Y 2 3 = 0 :=
    row08_reducedY23 Y commutesA commutesDiagonal
  have reducedY32 : Y 3 2 = 0 :=
    row08_reducedY32 Y commutesA commutesDiagonal
  have reducedY33 : Y 3 3 = Y 4 4 :=
    row08_reducedY33 Y commutesA commutesDiagonal

  refine ⟨Y 4 4, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [
      hY01,
      hY02,
      hY03,
      hY04,
      hY10,
      hY12,
      hY13,
      hY14,
      hY20,
      hY21,
      hY24,
      hY30,
      hY31,
      hY34,
      hY40,
      hY41,
      hY42,
      hY43,
      reducedY00,
      reducedY11,
      reducedY22,
      reducedY23,
      reducedY32,
      reducedY33]

/-- Every matrix commuting with both original row 08 presentation
generators is scalar. -/
theorem alternatingSixAmbientRow08_scalar_commutant
    (X : Matrix (Fin 5) (Fin 5) ℂ)
    (commutesA :
      X * alternatingSixFiveAmbient_row08_matrixA =
        alternatingSixFiveAmbient_row08_matrixA * X)
    (commutesB :
      X * alternatingSixFiveAmbient_row08_matrixB =
        alternatingSixFiveAmbient_row08_matrixB * X) :
    ∃ c : ℂ,
      X = c • (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
  apply Matrix.scalar_commutant_of_diagonal_basis
    alternatingSixFiveAmbient_row08_matrixA
    alternatingSixFiveAmbient_row08_matrixB
    alternatingSixAmbientRow08Eigenbasis
    alternatingSixAmbientRow08EigenbasisInverse
    alternatingSixAmbientRow08TransformedGeneratorA
    alternatingSixAmbientRow08GeneratorBEigenvalue
    alternatingSixAmbientRow08EigenbasisInverse_mul
    alternatingSixAmbientRow08Eigenbasis_mul_inverse
    alternatingSixAmbientRow08GeneratorB_mul_eigenbasis
    alternatingSixAmbientRow08TransformedGeneratorA_eq
    alternatingSixAmbientRow08Transformed_scalar_commutant
    X commutesA commutesB

end InductiveMcKay
end McKayConjecture
