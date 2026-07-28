/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DiagonalBasisMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow07DiagonalData

/-!
# Scalar common commutant for ambient row 07

The second generator is diagonal in the checked basis.  Its repeated
eigenspaces leave only 4 possible matrix
coordinates, and the generated exact row reduction for the transformed first
generator reduces those coordinates to a single scalar.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Entries between distinct second-generator eigenspaces vanish in its
commutant. -/
private theorem alternatingSixAmbientRow07_off_block
    (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow07GeneratorBDiagonal =
        alternatingSixAmbientRow07GeneratorBDiagonal * Y)
    (i j : Fin 4)
    (different :
      alternatingSixAmbientRow07EigenvalueLabel i ≠
        alternatingSixAmbientRow07EigenvalueLabel j) :
    Y i j = 0 := by
  apply Matrix.entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
    Y alternatingSixAmbientRow07GeneratorBEigenvalue
  · exact commutesDiagonal
  · intro equalEigenvalues
    apply different
    apply alternatingSixOrderEightOddEigenvalue_injective
    simpa [
      alternatingSixAmbientRow07GeneratorBEigenvalue] using
      equalEigenvalues.symm

private theorem row07_reducedY00
    (Y : Matrix (Fin 4)
      (Fin 4) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow07TransformedGeneratorA =
        alternatingSixAmbientRow07TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow07GeneratorBDiagonal =
        alternatingSixAmbientRow07GeneratorBDiagonal * Y) :
    Y 0 0 = Y 3 3 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 2 3 (by decide)

  have commutesA03 :=
    congrFun (congrFun commutesA
      (0 : Fin 4))
      (3 : Fin 4)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA03
  simp only [Fin.sum_univ_succ] at commutesA03
  simp [
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA03
  simp only [
      hY01,
      hY02,
      hY03,
      hY13,
      hY23] at commutesA03

  linear_combination
    ((((56 / 41) : ℂ) - ((40 / 41) : ℂ) * ζ ^ 3 + ((4 / 41) : ℂ) * ζ ^ 5 - ((40 / 41) : ℂ) * ζ ^ 7 - ((44 / 41) : ℂ) * ζ ^ 10 + ((36 / 41) : ℂ) * ζ ^ 15 + ((40 / 41) : ℂ) * ζ ^ 19 - ((68 / 41) : ℂ) * ζ ^ 20 + ((40 / 41) : ℂ) * ζ ^ 23 - ((36 / 41) : ℂ) * ζ ^ 25 + ((56 / 41) : ℂ) * ζ ^ 30 - ((40 / 41) : ℂ) * ζ ^ 31)) * commutesA03
      - (
        ((-((69 / 41) : ℂ) + ((20 / 41) : ℂ) * ζ ^ 3 + ((69 / 41) : ℂ) * ζ ^ 4 - ((16 / 41) : ℂ) * ζ ^ 5 - ((59 / 41) : ℂ) * ζ ^ 8 + ((16 / 41) : ℂ) * ζ ^ 9 + ((7 / 41) : ℂ) * ζ ^ 10 - ((6 / 41) : ℂ) * ζ ^ 13 - ((7 / 41) : ℂ) * ζ ^ 14 - ((2 / 41) : ℂ) * ζ ^ 15 + ((17 / 41) : ℂ) * ζ ^ 18 + ((2 / 41) : ℂ) * ζ ^ 19 + ((18 / 41) : ℂ) * ζ ^ 20 - ((32 / 41) : ℂ) * ζ ^ 23 - ((18 / 41) : ℂ) * ζ ^ 24 + ((20 / 41) : ℂ) * ζ ^ 25 + ((28 / 41) : ℂ) * ζ ^ 28 - ((20 / 41) : ℂ) * ζ ^ 29)) * Y 0 0
        + ((((69 / 41) : ℂ) - ((20 / 41) : ℂ) * ζ ^ 3 - ((69 / 41) : ℂ) * ζ ^ 4 + ((16 / 41) : ℂ) * ζ ^ 5 + ((59 / 41) : ℂ) * ζ ^ 8 - ((16 / 41) : ℂ) * ζ ^ 9 - ((7 / 41) : ℂ) * ζ ^ 10 + ((6 / 41) : ℂ) * ζ ^ 13 + ((7 / 41) : ℂ) * ζ ^ 14 + ((2 / 41) : ℂ) * ζ ^ 15 - ((17 / 41) : ℂ) * ζ ^ 18 - ((2 / 41) : ℂ) * ζ ^ 19 - ((18 / 41) : ℂ) * ζ ^ 20 + ((32 / 41) : ℂ) * ζ ^ 23 + ((18 / 41) : ℂ) * ζ ^ 24 - ((20 / 41) : ℂ) * ζ ^ 25 - ((28 / 41) : ℂ) * ζ ^ 28 + ((20 / 41) : ℂ) * ζ ^ 29)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row07_reducedY11
    (Y : Matrix (Fin 4)
      (Fin 4) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow07TransformedGeneratorA =
        alternatingSixAmbientRow07TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow07GeneratorBDiagonal =
        alternatingSixAmbientRow07GeneratorBDiagonal * Y) :
    Y 1 1 = Y 3 3 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 3 1 (by decide)

  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 4))
      (1 : Fin 4)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA01
  simp only [
      hY01,
      hY02,
      hY03,
      hY21,
      hY31] at commutesA01
  have commutesA03 :=
    congrFun (congrFun commutesA
      (0 : Fin 4))
      (3 : Fin 4)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA03
  simp only [Fin.sum_univ_succ] at commutesA03
  simp [
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA03
  simp only [
      hY01,
      hY02,
      hY03,
      hY13,
      hY23] at commutesA03

  linear_combination
    ((-((8 / 3) : ℂ) - ((4 / 3) : ℂ) * ζ ^ 5 + ((4 / 3) : ℂ) * ζ ^ 10 + (4 : ℂ) * ζ ^ 15 + ((4 / 3) : ℂ) * ζ ^ 20 - ((4 / 3) : ℂ) * ζ ^ 25 - ((8 / 3) : ℂ) * ζ ^ 30)) * commutesA01
      + ((((56 / 41) : ℂ) - ((40 / 41) : ℂ) * ζ ^ 3 + ((4 / 41) : ℂ) * ζ ^ 5 - ((40 / 41) : ℂ) * ζ ^ 7 - ((44 / 41) : ℂ) * ζ ^ 10 + ((36 / 41) : ℂ) * ζ ^ 15 + ((40 / 41) : ℂ) * ζ ^ 19 - ((68 / 41) : ℂ) * ζ ^ 20 + ((40 / 41) : ℂ) * ζ ^ 23 - ((36 / 41) : ℂ) * ζ ^ 25 + ((56 / 41) : ℂ) * ζ ^ 30 - ((40 / 41) : ℂ) * ζ ^ 31)) * commutesA03
      - (
        ((((80 / 123) : ℂ) + ((224 / 123) : ℂ) * ζ ^ 3 - ((80 / 123) : ℂ) * ζ ^ 4 + ((280 / 123) : ℂ) * ζ ^ 5 + ((64 / 41) : ℂ) * ζ ^ 8 - ((280 / 123) : ℂ) * ζ ^ 9 + ((48 / 41) : ℂ) * ζ ^ 10 + ((76 / 41) : ℂ) * ζ ^ 13 - ((48 / 41) : ℂ) * ζ ^ 14 - ((84 / 41) : ℂ) * ζ ^ 15 - ((24 / 41) : ℂ) * ζ ^ 18 + ((84 / 41) : ℂ) * ζ ^ 19 - ((64 / 41) : ℂ) * ζ ^ 20 - ((424 / 123) : ℂ) * ζ ^ 23 + ((64 / 41) : ℂ) * ζ ^ 24 - ((104 / 123) : ℂ) * ζ ^ 25 - ((80 / 123) : ℂ) * ζ ^ 28 + ((104 / 123) : ℂ) * ζ ^ 29)) * Y 0 0
        + ((-((7 / 3) : ℂ) - ((4 / 3) : ℂ) * ζ ^ 3 + ((7 / 3) : ℂ) * ζ ^ 4 - ((8 / 3) : ℂ) * ζ ^ 5 - (3 : ℂ) * ζ ^ 8 + ((8 / 3) : ℂ) * ζ ^ 9 - ζ ^ 10 - (2 : ℂ) * ζ ^ 13 + ζ ^ 14 + (2 : ℂ) * ζ ^ 15 + ζ ^ 18 - (2 : ℂ) * ζ ^ 19 + (2 : ℂ) * ζ ^ 20 + ((8 / 3) : ℂ) * ζ ^ 23 - (2 : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 25 + ((4 / 3) : ℂ) * ζ ^ 28 - ((4 / 3) : ℂ) * ζ ^ 29)) * Y 1 1
        + ((((69 / 41) : ℂ) - ((20 / 41) : ℂ) * ζ ^ 3 - ((69 / 41) : ℂ) * ζ ^ 4 + ((16 / 41) : ℂ) * ζ ^ 5 + ((59 / 41) : ℂ) * ζ ^ 8 - ((16 / 41) : ℂ) * ζ ^ 9 - ((7 / 41) : ℂ) * ζ ^ 10 + ((6 / 41) : ℂ) * ζ ^ 13 + ((7 / 41) : ℂ) * ζ ^ 14 + ((2 / 41) : ℂ) * ζ ^ 15 - ((17 / 41) : ℂ) * ζ ^ 18 - ((2 / 41) : ℂ) * ζ ^ 19 - ((18 / 41) : ℂ) * ζ ^ 20 + ((32 / 41) : ℂ) * ζ ^ 23 + ((18 / 41) : ℂ) * ζ ^ 24 - ((20 / 41) : ℂ) * ζ ^ 25 - ((28 / 41) : ℂ) * ζ ^ 28 + ((20 / 41) : ℂ) * ζ ^ 29)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row07_reducedY22
    (Y : Matrix (Fin 4)
      (Fin 4) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow07TransformedGeneratorA =
        alternatingSixAmbientRow07TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow07GeneratorBDiagonal =
        alternatingSixAmbientRow07GeneratorBDiagonal * Y) :
    Y 2 2 = Y 3 3 := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 3 2 (by decide)

  have commutesA02 :=
    congrFun (congrFun commutesA
      (0 : Fin 4))
      (2 : Fin 4)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA02
  simp only [Fin.sum_univ_succ] at commutesA02
  simp [
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA02
  simp only [
      hY01,
      hY02,
      hY03,
      hY12,
      hY32] at commutesA02
  have commutesA03 :=
    congrFun (congrFun commutesA
      (0 : Fin 4))
      (3 : Fin 4)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA03
  simp only [Fin.sum_univ_succ] at commutesA03
  simp [
      alternatingSixAmbientRow07TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA03
  simp only [
      hY01,
      hY02,
      hY03,
      hY13,
      hY23] at commutesA03

  linear_combination
    ((((8 / 3) : ℂ) * ζ ^ 3 + ((4 / 3) : ℂ) * ζ ^ 5 + ((8 / 3) : ℂ) * ζ ^ 7 - ((8 / 3) : ℂ) * ζ ^ 10 - ((4 / 3) : ℂ) * ζ ^ 15 - ((8 / 3) : ℂ) * ζ ^ 19 - ((8 / 3) : ℂ) * ζ ^ 23 + ((4 / 3) : ℂ) * ζ ^ 25 + ((4 / 3) : ℂ) * ζ ^ 30 + ((8 / 3) : ℂ) * ζ ^ 31)) * commutesA02
      + ((((56 / 41) : ℂ) - ((40 / 41) : ℂ) * ζ ^ 3 + ((4 / 41) : ℂ) * ζ ^ 5 - ((40 / 41) : ℂ) * ζ ^ 7 - ((44 / 41) : ℂ) * ζ ^ 10 + ((36 / 41) : ℂ) * ζ ^ 15 + ((40 / 41) : ℂ) * ζ ^ 19 - ((68 / 41) : ℂ) * ζ ^ 20 + ((40 / 41) : ℂ) * ζ ^ 23 - ((36 / 41) : ℂ) * ζ ^ 25 + ((56 / 41) : ℂ) * ζ ^ 30 - ((40 / 41) : ℂ) * ζ ^ 31)) * commutesA03
      - (
        ((-((28 / 41) : ℂ) + ((20 / 41) : ℂ) * ζ ^ 3 + ((28 / 41) : ℂ) * ζ ^ 4 - ((16 / 41) : ℂ) * ζ ^ 5 - ((4 / 3) : ℂ) * ζ ^ 6 - ((218 / 123) : ℂ) * ζ ^ 8 + ((16 / 41) : ℂ) * ζ ^ 9 - ((184 / 123) : ℂ) * ζ ^ 10 - ((6 / 41) : ℂ) * ζ ^ 13 + ((20 / 123) : ℂ) * ζ ^ 14 - ((2 / 41) : ℂ) * ζ ^ 15 + ((10 / 123) : ℂ) * ζ ^ 18 + ((2 / 41) : ℂ) * ζ ^ 19 + ((259 / 123) : ℂ) * ζ ^ 20 + ((4 / 3) : ℂ) * ζ ^ 22 - ((32 / 41) : ℂ) * ζ ^ 23 - ((259 / 123) : ℂ) * ζ ^ 24 + ((20 / 41) : ℂ) * ζ ^ 25 + ((4 / 3) : ℂ) * ζ ^ 26 + ((125 / 123) : ℂ) * ζ ^ 28 - ((20 / 41) : ℂ) * ζ ^ 29 - ((4 / 3) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((-(1 : ℂ) + ζ ^ 4 + ((4 / 3) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ((5 / 3) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 18 - ((5 / 3) : ℂ) * ζ ^ 20 - ((4 / 3) : ℂ) * ζ ^ 22 + ((5 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 26 - ((1 / 3) : ℂ) * ζ ^ 28 + ((4 / 3) : ℂ) * ζ ^ 30)) * Y 2 2
        + ((((69 / 41) : ℂ) - ((20 / 41) : ℂ) * ζ ^ 3 - ((69 / 41) : ℂ) * ζ ^ 4 + ((16 / 41) : ℂ) * ζ ^ 5 + ((59 / 41) : ℂ) * ζ ^ 8 - ((16 / 41) : ℂ) * ζ ^ 9 - ((7 / 41) : ℂ) * ζ ^ 10 + ((6 / 41) : ℂ) * ζ ^ 13 + ((7 / 41) : ℂ) * ζ ^ 14 + ((2 / 41) : ℂ) * ζ ^ 15 - ((17 / 41) : ℂ) * ζ ^ 18 - ((2 / 41) : ℂ) * ζ ^ 19 - ((18 / 41) : ℂ) * ζ ^ 20 + ((32 / 41) : ℂ) * ζ ^ 23 + ((18 / 41) : ℂ) * ζ ^ 24 - ((20 / 41) : ℂ) * ζ ^ 25 - ((28 / 41) : ℂ) * ζ ^ 28 + ((20 / 41) : ℂ) * ζ ^ 29)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation


/-- A matrix commuting with both transformed row 07 generators is
scalar. -/
theorem alternatingSixAmbientRow07Transformed_scalar_commutant
    (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow07TransformedGeneratorA =
        alternatingSixAmbientRow07TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow07GeneratorBDiagonal =
        alternatingSixAmbientRow07GeneratorBDiagonal * Y) :
    ∃ c : ℂ,
      Y = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hY01 :
      Y 0 1 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 0 1 (by decide)
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY10 :
      Y 1 0 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 1 0 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow07_off_block
      Y commutesDiagonal 3 2 (by decide)

  have reducedY00 : Y 0 0 = Y 3 3 :=
    row07_reducedY00 Y commutesA commutesDiagonal
  have reducedY11 : Y 1 1 = Y 3 3 :=
    row07_reducedY11 Y commutesA commutesDiagonal
  have reducedY22 : Y 2 2 = Y 3 3 :=
    row07_reducedY22 Y commutesA commutesDiagonal

  refine ⟨Y 3 3, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [
      hY01,
      hY02,
      hY03,
      hY10,
      hY12,
      hY13,
      hY20,
      hY21,
      hY23,
      hY30,
      hY31,
      hY32,
      reducedY00,
      reducedY11,
      reducedY22]

/-- Every matrix commuting with both original row 07 presentation
generators is scalar. -/
theorem alternatingSixAmbientRow07_scalar_commutant
    (X : Matrix (Fin 4) (Fin 4) ℂ)
    (commutesA :
      X * alternatingSixFiveAmbient_row07_matrixA =
        alternatingSixFiveAmbient_row07_matrixA * X)
    (commutesB :
      X * alternatingSixFiveAmbient_row07_matrixB =
        alternatingSixFiveAmbient_row07_matrixB * X) :
    ∃ c : ℂ,
      X = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  apply Matrix.scalar_commutant_of_diagonal_basis
    alternatingSixFiveAmbient_row07_matrixA
    alternatingSixFiveAmbient_row07_matrixB
    alternatingSixAmbientRow07Eigenbasis
    alternatingSixAmbientRow07EigenbasisInverse
    alternatingSixAmbientRow07TransformedGeneratorA
    alternatingSixAmbientRow07GeneratorBEigenvalue
    alternatingSixAmbientRow07EigenbasisInverse_mul
    alternatingSixAmbientRow07Eigenbasis_mul_inverse
    alternatingSixAmbientRow07GeneratorB_mul_eigenbasis
    alternatingSixAmbientRow07TransformedGeneratorA_eq
    alternatingSixAmbientRow07Transformed_scalar_commutant
    X commutesA commutesB

end InductiveMcKay
end McKayConjecture
