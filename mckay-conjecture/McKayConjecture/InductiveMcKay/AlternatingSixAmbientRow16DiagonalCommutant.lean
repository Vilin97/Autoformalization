/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DiagonalBasisMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow16DiagonalData

/-!
# Scalar common commutant for ambient row 16

The second generator is diagonal in the checked basis.  The exact
commutator system is normalized one equation at a time, and each reduced
relation is assembled from short checked combination steps.  This keeps
every declaration within Lean's default elaboration budget.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Entries between distinct second-generator eigenspaces
vanish in its commutant. -/
private theorem alternatingSixAmbientRow16_off_block
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y)
    (i j : Fin 8)
    (different :
      alternatingSixAmbientRow16EigenvalueLabel i ≠
        alternatingSixAmbientRow16EigenvalueLabel j) :
    Y i j = 0 := by
  apply Matrix.entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
    Y alternatingSixAmbientRow16GeneratorBEigenvalue
  · exact commutesDiagonal
  · intro equalEigenvalues
    apply different
    apply alternatingSixOrderFourEigenvalue_injective
    simpa [
      alternatingSixAmbientRow16GeneratorBEigenvalue] using
      equalEigenvalues.symm


private theorem row16_commutatorEquation00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 24)) * Y 0 1
      + ((-((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28)) * Y 1 0) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY60 :
      Y 6 0 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 0 (by decide)
  have hY70 :
      Y 7 0 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 0 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (0 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY06,
      hY07,
      hY20,
      hY30,
      hY40,
      hY50,
      hY60,
      hY70] at equation
  linear_combination equation

private theorem row16_commutatorEquation01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((((3 / 4) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 12 - ((3 / 4) : ℂ) * ζ ^ 28)) * Y 0 1
      + ((-((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28)) * Y 1 1) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY61 :
      Y 6 1 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 1 (by decide)
  have hY71 :
      Y 7 1 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 1 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (1 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY06,
      hY07,
      hY21,
      hY31,
      hY41,
      hY51,
      hY61,
      hY71] at equation
  linear_combination equation

private theorem row16_commutatorEquation02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 12 - ((3 / 4) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 + ζ ^ 30)) * Y 0 1
      + ((((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 28)) * Y 3 2) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY62 :
      Y 6 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 2 (by decide)
  have hY72 :
      Y 7 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 2 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (2 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY06,
      hY07,
      hY12,
      hY42,
      hY52,
      hY62,
      hY72] at equation
  linear_combination equation

private theorem row16_commutatorEquation03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((-((1 / 2) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 28)) * Y 3 3) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 3 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 3 (by decide)
  have hY63 :
      Y 6 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 3 (by decide)
  have hY73 :
      Y 7 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 3 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (3 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY06,
      hY07,
      hY13,
      hY43,
      hY53,
      hY63,
      hY73] at equation
  linear_combination equation

private theorem row16_commutatorEquation04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((15 / 44) : ℂ) + ((3 / 22) : ℂ) * ζ ^ 8 + ((3 / 22) : ℂ) * ζ ^ 12 - ((3 / 22) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((((9 / 44) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 12 + ((9 / 44) : ℂ) * ζ ^ 24)) * Y 0 1
      + ((((15 / 44) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 8 - ((3 / 22) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((((15 / 22) : ℂ) - ((15 / 44) : ℂ) * ζ ^ 8 - ((21 / 44) : ℂ) * ζ ^ 12 + ((9 / 44) : ℂ) * ζ ^ 24 + ((15 / 44) : ℂ) * ζ ^ 28)) * Y 5 4) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY64 :
      Y 6 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 4 (by decide)
  have hY74 :
      Y 7 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 4 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (4 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY06,
      hY07,
      hY14,
      hY24,
      hY34,
      hY64,
      hY74] at equation
  linear_combination equation

private theorem row16_commutatorEquation05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((15 / 22) : ℂ) + ((15 / 44) : ℂ) * ζ ^ 8 + ((21 / 44) : ℂ) * ζ ^ 12 - ((9 / 44) : ℂ) * ζ ^ 24 - ((15 / 44) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((((9 / 44) : ℂ) - ((3 / 44) : ℂ) * ζ ^ 8 - ((15 / 44) : ℂ) * ζ ^ 12 + ((9 / 22) : ℂ) * ζ ^ 24 + ((3 / 44) : ℂ) * ζ ^ 28)) * Y 0 1
      + ((((15 / 44) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 8 - ((3 / 22) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 28)) * Y 4 5
      + ((((15 / 22) : ℂ) - ((15 / 44) : ℂ) * ζ ^ 8 - ((21 / 44) : ℂ) * ζ ^ 12 + ((9 / 44) : ℂ) * ζ ^ 24 + ((15 / 44) : ℂ) * ζ ^ 28)) * Y 5 5) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY65 :
      Y 6 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 5 (by decide)
  have hY75 :
      Y 7 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 5 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (5 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY06,
      hY07,
      hY15,
      hY25,
      hY35,
      hY65,
      hY75] at equation
  linear_combination equation

private theorem row16_commutatorEquation06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ζ ^ 30)) * Y 0 1
      + ((((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 30)) * Y 6 6
      + ((((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 28)) * Y 7 6) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY26 :
      Y 2 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 6 (by decide)
  have hY36 :
      Y 3 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 6 (by decide)
  have hY46 :
      Y 4 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 6 (by decide)
  have hY56 :
      Y 5 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 6 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (6 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY06,
      hY07,
      hY16,
      hY26,
      hY36,
      hY46,
      hY56] at equation
  linear_combination equation

private theorem row16_commutatorEquation07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((-((1 / 2) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 28)) * Y 7 7) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY27 :
      Y 2 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 7 (by decide)
  have hY37 :
      Y 3 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 7 (by decide)
  have hY47 :
      Y 4 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 7 (by decide)
  have hY57 :
      Y 5 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 7 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (7 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY06,
      hY07,
      hY17,
      hY27,
      hY37,
      hY47,
      hY57] at equation
  linear_combination equation

private theorem row16_commutatorEquation12
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 12 - ((3 / 4) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 + ζ ^ 30)) * Y 1 1
      + ((-((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ζ ^ 30)) * Y 2 2
      + ((((1 / 2) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY62 :
      Y 6 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 2 (by decide)
  have hY72 :
      Y 7 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 2 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (2 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY02,
      hY12,
      hY13,
      hY14,
      hY15,
      hY16,
      hY17,
      hY42,
      hY52,
      hY62,
      hY72] at equation
  linear_combination equation

private theorem row16_commutatorEquation13
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((1 / 2) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ζ ^ 30)) * Y 2 3
      + ((((1 / 2) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 3 3) = 0 := by
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 3 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 3 (by decide)
  have hY63 :
      Y 6 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 3 (by decide)
  have hY73 :
      Y 7 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 3 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (3 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY03,
      hY12,
      hY13,
      hY14,
      hY15,
      hY16,
      hY17,
      hY43,
      hY53,
      hY63,
      hY73] at equation
  linear_combination equation

private theorem row16_commutatorEquation14
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((15 / 44) : ℂ) + ((3 / 22) : ℂ) * ζ ^ 8 + ((3 / 22) : ℂ) * ζ ^ 12 - ((3 / 22) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((((9 / 44) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 12 + ((9 / 44) : ℂ) * ζ ^ 24)) * Y 1 1
      + ((-((9 / 44) : ℂ) + ((3 / 22) : ℂ) * ζ ^ 12 - ((9 / 44) : ℂ) * ζ ^ 24)) * Y 4 4
      + ((-((9 / 44) : ℂ) + ((3 / 44) : ℂ) * ζ ^ 8 + ((15 / 44) : ℂ) * ζ ^ 12 - ((9 / 22) : ℂ) * ζ ^ 24 - ((3 / 44) : ℂ) * ζ ^ 28)) * Y 5 4) = 0 := by
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY64 :
      Y 6 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 4 (by decide)
  have hY74 :
      Y 7 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 4 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (4 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY04,
      hY12,
      hY13,
      hY14,
      hY15,
      hY16,
      hY17,
      hY24,
      hY34,
      hY64,
      hY74] at equation
  linear_combination equation

private theorem row16_commutatorEquation16
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 4) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ζ ^ 30)) * Y 1 1
      + ((((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 12 - ((3 / 4) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 + ζ ^ 30)) * Y 6 6
      + ((((1 / 2) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 6) = 0 := by
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY26 :
      Y 2 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 6 (by decide)
  have hY36 :
      Y 3 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 6 (by decide)
  have hY46 :
      Y 4 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 6 (by decide)
  have hY56 :
      Y 5 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 6 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (6 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY06,
      hY12,
      hY13,
      hY14,
      hY15,
      hY16,
      hY17,
      hY26,
      hY36,
      hY46,
      hY56] at equation
  linear_combination equation

private theorem row16_commutatorEquation17
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((1 / 2) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 4) : ℂ) * ζ ^ 12 - ((3 / 4) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 + ζ ^ 30)) * Y 6 7
      + ((((1 / 2) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY27 :
      Y 2 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 7 (by decide)
  have hY37 :
      Y 3 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 7 (by decide)
  have hY47 :
      Y 4 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 7 (by decide)
  have hY57 :
      Y 5 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 7 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (7 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY07,
      hY12,
      hY13,
      hY14,
      hY15,
      hY16,
      hY17,
      hY27,
      hY37,
      hY47,
      hY57] at equation
  linear_combination equation

private theorem row16_commutatorEquation24
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((3 / 11) : ℂ) + ((1 / 44) : ℂ) * ζ ^ 2 + ((3 / 22) : ℂ) * ζ ^ 6 + ((7 / 44) : ℂ) * ζ ^ 8 + ((7 / 44) : ℂ) * ζ ^ 12 - ((5 / 44) : ℂ) * ζ ^ 18 - ((1 / 44) : ℂ) * ζ ^ 22 - ((7 / 44) : ℂ) * ζ ^ 28 + ((3 / 44) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((2 / 11) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 2 - ((3 / 22) : ℂ) * ζ ^ 6 - ((1 / 22) : ℂ) * ζ ^ 8 - ((1 / 11) : ℂ) * ζ ^ 12 + ((2 / 11) : ℂ) * ζ ^ 18 + ((1 / 11) : ℂ) * ζ ^ 22 + ((3 / 44) : ℂ) * ζ ^ 24 + ((1 / 22) : ℂ) * ζ ^ 28 - ((5 / 44) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((3 / 11) : ℂ) - ((1 / 44) : ℂ) * ζ ^ 2 - ((3 / 22) : ℂ) * ζ ^ 6 - ((7 / 44) : ℂ) * ζ ^ 8 - ((7 / 44) : ℂ) * ζ ^ 12 + ((5 / 44) : ℂ) * ζ ^ 18 + ((1 / 44) : ℂ) * ζ ^ 22 + ((7 / 44) : ℂ) * ζ ^ 28 - ((3 / 44) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((1 / 22) : ℂ) + ((7 / 22) : ℂ) * ζ ^ 6 - ((1 / 44) : ℂ) * ζ ^ 8 + ((3 / 44) : ℂ) * ζ ^ 12 - ((6 / 11) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 24 + ((1 / 44) : ℂ) * ζ ^ 28 + ((7 / 22) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY26 :
      Y 2 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 6 (by decide)
  have hY27 :
      Y 2 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 7 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY64 :
      Y 6 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 4 (by decide)
  have hY74 :
      Y 7 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 4 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (2 : Fin 8))
      (4 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY04,
      hY14,
      hY20,
      hY21,
      hY24,
      hY25,
      hY26,
      hY27,
      hY34,
      hY64,
      hY74] at equation
  linear_combination equation

private theorem row16_commutatorEquation25
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((1 / 22) : ℂ) - ((7 / 22) : ℂ) * ζ ^ 6 + ((1 / 44) : ℂ) * ζ ^ 8 - ((3 / 44) : ℂ) * ζ ^ 12 + ((6 / 11) : ℂ) * ζ ^ 18 - ((5 / 44) : ℂ) * ζ ^ 24 - ((1 / 44) : ℂ) * ζ ^ 28 - ((7 / 22) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((5 / 11) : ℂ) + ((27 / 44) : ℂ) * ζ ^ 2 + ((13 / 44) : ℂ) * ζ ^ 6 + ((27 / 44) : ℂ) * ζ ^ 8 + ((21 / 44) : ℂ) * ζ ^ 12 - ((21 / 44) : ℂ) * ζ ^ 18 - ((27 / 44) : ℂ) * ζ ^ 22 - ((13 / 44) : ℂ) * ζ ^ 24 - ((27 / 44) : ℂ) * ζ ^ 28 + ((5 / 11) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((3 / 11) : ℂ) - ((1 / 44) : ℂ) * ζ ^ 2 - ((3 / 22) : ℂ) * ζ ^ 6 - ((7 / 44) : ℂ) * ζ ^ 8 - ((7 / 44) : ℂ) * ζ ^ 12 + ((5 / 44) : ℂ) * ζ ^ 18 + ((1 / 44) : ℂ) * ζ ^ 22 + ((7 / 44) : ℂ) * ζ ^ 28 - ((3 / 44) : ℂ) * ζ ^ 30)) * Y 4 5
      + ((((1 / 22) : ℂ) + ((7 / 22) : ℂ) * ζ ^ 6 - ((1 / 44) : ℂ) * ζ ^ 8 + ((3 / 44) : ℂ) * ζ ^ 12 - ((6 / 11) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 24 + ((1 / 44) : ℂ) * ζ ^ 28 + ((7 / 22) : ℂ) * ζ ^ 30)) * Y 5 5) = 0 := by
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY26 :
      Y 2 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 6 (by decide)
  have hY27 :
      Y 2 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 7 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY65 :
      Y 6 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 5 (by decide)
  have hY75 :
      Y 7 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 5 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (2 : Fin 8))
      (5 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow16TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY05,
      hY15,
      hY20,
      hY21,
      hY24,
      hY25,
      hY26,
      hY27,
      hY35,
      hY65,
      hY75] at equation
  linear_combination equation


private theorem row16_reducedY00_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((17 / 12) : ℂ) - ((7 / 4) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((7 / 2) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 18 + ((7 / 4) : ℂ) * ζ ^ 22 - ((17 / 12) : ℂ) * ζ ^ 24 - ((7 / 2) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((3 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((25 / 12) : ℂ) * ζ ^ 8 + ((17 / 12) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 22 - ((17 / 12) : ℂ) * ζ ^ 24 + ((25 / 12) : ℂ) * ζ ^ 28 - ((5 / 2) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((59 / 3) : ℂ) + (3 : ℂ) * ζ ^ 2 - (14 : ℂ) * ζ ^ 6 + (14 : ℂ) * ζ ^ 8 + (14 : ℂ) * ζ ^ 12 + (17 : ℂ) * ζ ^ 18 - (3 : ℂ) * ζ ^ 22 - (14 : ℂ) * ζ ^ 28 - (7 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((7 / 2) : ℂ) + ((5 / 2) : ℂ) * ζ ^ 2 + ((7 / 2) : ℂ) * ζ ^ 4 - (5 : ℂ) * ζ ^ 6 + (5 : ℂ) * ζ ^ 10 - ((7 / 2) : ℂ) * ζ ^ 12 - ((5 / 2) : ℂ) * ζ ^ 14 + ((7 / 2) : ℂ) * ζ ^ 16 + ((7 / 4) : ℂ) * ζ ^ 18 - ((7 / 2) : ℂ) * ζ ^ 20 - ((7 / 4) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((((3 / 2) : ℂ) * ζ ^ 2 - ((5 / 2) : ℂ) * ζ ^ 6 + (7 : ℂ) * ζ ^ 8 + ((7 / 4) : ℂ) * ζ ^ 10 - ((7 / 2) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 14 - ((3 / 4) : ℂ) * ζ ^ 18 - ((7 / 2) : ℂ) * ζ ^ 24 - ((7 / 4) : ℂ) * ζ ^ 26)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY00_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((3 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 2 - ((5 / 12) : ℂ) * ζ ^ 8 - ((5 / 12) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 22 + ((5 / 12) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((-((8 / 3) : ℂ) - ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 6 + ((23 / 4) : ℂ) * ζ ^ 12 + ((7 / 4) : ℂ) * ζ ^ 18 + ζ ^ 22 - ((8 / 3) : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((3 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((25 / 12) : ℂ) * ζ ^ 8 + ((17 / 12) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 22 - ((17 / 12) : ℂ) * ζ ^ 24 + ((25 / 12) : ℂ) * ζ ^ 28 - ((5 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((3 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ((5 / 12) : ℂ) * ζ ^ 8 + ((5 / 12) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22 - ((5 / 12) : ℂ) * ζ ^ 28)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY00_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((3 : ℂ) - ζ ^ 2 - ((14 / 3) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 + ζ ^ 22 + (3 : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((3 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ((3 / 4) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 + ((5 / 12) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((5 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 2 - ((5 / 4) : ℂ) * ζ ^ 4 + ((7 / 2) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 10 - ((9 / 4) : ℂ) * ζ ^ 12 - ((3 / 4) : ℂ) * ζ ^ 14 + ((9 / 4) : ℂ) * ζ ^ 16 + ((3 / 4) : ℂ) * ζ ^ 18 - ((9 / 4) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 22 + ((3 / 2) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((3 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 2 - ((3 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 - ((5 / 12) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 26)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY00_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((8 / 3) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((9 / 2) : ℂ) * ζ ^ 12 + ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((8 / 3) : ℂ) * ζ ^ 24 - ζ ^ 30)) * Y 0 1
      + ((-((3 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((25 / 12) : ℂ) * ζ ^ 8 + ((17 / 12) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 22 - ((17 / 12) : ℂ) * ζ ^ 24 + ((25 / 12) : ℂ) * ζ ^ 28 - ((5 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((3 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ((5 / 12) : ℂ) * ζ ^ 8 + ((5 / 12) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22 - ((5 / 12) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((5 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((5 / 4) : ℂ) * ζ ^ 8 - ((5 / 4) : ℂ) * ζ ^ 12 - ((5 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22 + ((5 / 4) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((5 / 2) : ℂ) + ((7 / 4) : ℂ) * ζ ^ 6 - ((5 / 4) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 12 - ((11 / 4) : ℂ) * ζ ^ 18 + ((5 / 4) : ℂ) * ζ ^ 28 + ((7 / 4) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY00_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((5 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 2 + ((8 / 3) : ℂ) * ζ ^ 6 - (5 : ℂ) * ζ ^ 8 - (5 : ℂ) * ζ ^ 12 - (3 : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 22 + (5 : ℂ) * ζ ^ 28 + ((4 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((15 / 22) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 2 - ((15 / 22) : ℂ) * ζ ^ 4 + ((5 / 22) : ℂ) * ζ ^ 6 + ((15 / 11) : ℂ) * ζ ^ 8 - ((3 / 11) : ℂ) * ζ ^ 10 + ((5 / 11) : ℂ) * ζ ^ 14 - ((15 / 22) : ℂ) * ζ ^ 16 - ((5 / 22) : ℂ) * ζ ^ 18 + ((15 / 22) : ℂ) * ζ ^ 20 + ((2 / 11) : ℂ) * ζ ^ 22 - ((15 / 22) : ℂ) * ζ ^ 24 - ((2 / 11) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((15 / 44) : ℂ) - ((25 / 44) : ℂ) * ζ ^ 2 - ((15 / 44) : ℂ) * ζ ^ 4 + ((19 / 22) : ℂ) * ζ ^ 6 - ((15 / 22) : ℂ) * ζ ^ 8 - ((19 / 22) : ℂ) * ζ ^ 10 + ((45 / 44) : ℂ) * ζ ^ 12 + ((15 / 44) : ℂ) * ζ ^ 14 - ((45 / 44) : ℂ) * ζ ^ 16 - ((3 / 11) : ℂ) * ζ ^ 18 + ((45 / 44) : ℂ) * ζ ^ 20 + ((3 / 11) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((-((15 / 22) : ℂ) + ((3 / 22) : ℂ) * ζ ^ 2 + ((15 / 22) : ℂ) * ζ ^ 4 - ((5 / 22) : ℂ) * ζ ^ 6 - ((15 / 11) : ℂ) * ζ ^ 8 + ((3 / 11) : ℂ) * ζ ^ 10 - ((5 / 11) : ℂ) * ζ ^ 14 + ((15 / 22) : ℂ) * ζ ^ 16 + ((5 / 22) : ℂ) * ζ ^ 18 - ((15 / 22) : ℂ) * ζ ^ 20 - ((2 / 11) : ℂ) * ζ ^ 22 + ((15 / 22) : ℂ) * ζ ^ 24 + ((2 / 11) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((15 / 11) : ℂ) - ((5 / 22) : ℂ) * ζ ^ 2 + ((15 / 11) : ℂ) * ζ ^ 4 + ((13 / 44) : ℂ) * ζ ^ 6 - ((45 / 11) : ℂ) * ζ ^ 8 - ((2 / 11) : ℂ) * ζ ^ 10 + ((45 / 44) : ℂ) * ζ ^ 12 - ((35 / 44) : ℂ) * ζ ^ 14 + ((15 / 22) : ℂ) * ζ ^ 16 + ((13 / 44) : ℂ) * ζ ^ 18 - ((15 / 22) : ℂ) * ζ ^ 20 - ((2 / 11) : ℂ) * ζ ^ 22 + ((75 / 44) : ℂ) * ζ ^ 24 + ((5 / 11) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY00_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 0 0
      + ((-((3 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((25 / 12) : ℂ) * ζ ^ 8 + ((17 / 12) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 22 - ((17 / 12) : ℂ) * ζ ^ 24 + ((25 / 12) : ℂ) * ζ ^ 28 - ((5 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((3 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ((5 / 12) : ℂ) * ζ ^ 8 + ((5 / 12) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22 - ((5 / 12) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((5 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((5 / 4) : ℂ) * ζ ^ 8 - ((5 / 4) : ℂ) * ζ ^ 12 - ((5 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22 + ((5 / 4) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((5 / 2) : ℂ) + ((7 / 4) : ℂ) * ζ ^ 6 - ((5 / 4) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 12 - ((11 / 4) : ℂ) * ζ ^ 18 + ((5 / 4) : ℂ) * ζ ^ 28 + ((7 / 4) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY00_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28 - ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-(1 : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 4 - ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 16 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((5 / 3) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 + ((5 / 3) : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 6 - ((11 / 6) : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 10 + ((7 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((7 / 2) : ℂ) * ζ ^ 16 - ζ ^ 18 + (2 : ℂ) * ζ ^ 20 + ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 + ((4 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((1 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 - ((5 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 + ((2 / 3) : ℂ) * ζ ^ 28)) * Y 6 7
        + (((1 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ζ ^ 4 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY00_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 0 0
      + ((((1 / 2) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 12 - ((1 / 6) : ℂ) * ζ ^ 24 + ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY00_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((10 / 3) : ℂ) * ζ ^ 2 + ((4 / 3) : ℂ) * ζ ^ 6 - (5 : ℂ) * ζ ^ 8 + ((5 / 3) : ℂ) * ζ ^ 12 + ((5 / 3) : ℂ) * ζ ^ 18 + ((10 / 3) : ℂ) * ζ ^ 22 - ((5 / 3) : ℂ) * ζ ^ 24 + (5 : ℂ) * ζ ^ 28 - ((14 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((4 / 11) : ℂ) * ζ ^ 2 + ((9 / 22) : ℂ) * ζ ^ 6 + ((5 / 11) : ℂ) * ζ ^ 8 - ((19 / 22) : ℂ) * ζ ^ 10 + ((5 / 22) : ℂ) * ζ ^ 12 + ((5 / 22) : ℂ) * ζ ^ 14 - ((10 / 11) : ℂ) * ζ ^ 16 + ((2 / 11) : ℂ) * ζ ^ 18 + ((10 / 11) : ℂ) * ζ ^ 20 - ((7 / 11) : ℂ) * ζ ^ 22 - ((15 / 22) : ℂ) * ζ ^ 24 + ((7 / 11) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((5 / 4) : ℂ) - ((19 / 44) : ℂ) * ζ ^ 2 + ((5 / 4) : ℂ) * ζ ^ 4 - ((13 / 44) : ℂ) * ζ ^ 6 - ((45 / 44) : ℂ) * ζ ^ 8 + ((13 / 44) : ℂ) * ζ ^ 10 + ((15 / 11) : ℂ) * ζ ^ 12 - ((3 / 11) : ℂ) * ζ ^ 14 - ((15 / 11) : ℂ) * ζ ^ 16 + ((21 / 22) : ℂ) * ζ ^ 18 + ((45 / 44) : ℂ) * ζ ^ 20 - ((21 / 22) : ℂ) * ζ ^ 22)) * Y 1 1
        + ((((5 / 4) : ℂ) + ((19 / 44) : ℂ) * ζ ^ 2 - ((5 / 4) : ℂ) * ζ ^ 4 + ((13 / 44) : ℂ) * ζ ^ 6 + ((45 / 44) : ℂ) * ζ ^ 8 - ((13 / 44) : ℂ) * ζ ^ 10 - ((15 / 11) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 14 + ((15 / 11) : ℂ) * ζ ^ 16 - ((21 / 22) : ℂ) * ζ ^ 18 - ((45 / 44) : ℂ) * ζ ^ 20 + ((21 / 22) : ℂ) * ζ ^ 22)) * Y 4 4
        + ((((5 / 2) : ℂ) + ((15 / 22) : ℂ) * ζ ^ 2 - ((5 / 2) : ℂ) * ζ ^ 4 + ((35 / 44) : ℂ) * ζ ^ 6 + ((25 / 11) : ℂ) * ζ ^ 8 - ((45 / 44) : ℂ) * ζ ^ 10 - ((115 / 44) : ℂ) * ζ ^ 12 + ((29 / 44) : ℂ) * ζ ^ 14 + ((25 / 11) : ℂ) * ζ ^ 16 - ((20 / 11) : ℂ) * ζ ^ 18 - ((35 / 22) : ℂ) * ζ ^ 20 + ((35 / 22) : ℂ) * ζ ^ 22 - ((15 / 44) : ℂ) * ζ ^ 24 + ((7 / 22) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY00_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 0 0
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY00_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((2 : ℂ) - ((4 / 3) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 22 + ((4 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 2) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((1 / 2) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 - ((3 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 22 - ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26 + ζ ^ 28)) * Y 1 1
        + ((-((7 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((7 / 6) : ℂ) * ζ ^ 6 - ((7 / 6) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 14 - ((5 / 6) : ℂ) * ζ ^ 16 - ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 26 - (2 : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((1 / 2) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 16 + ((3 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 22 + ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 - ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 0 0 = Y 7 7 := by
  have reduced :=
    row16_reducedY00_combinationStep05 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row16_reducedY01_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 28)) * Y 0 1
      + ((((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 12)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-ζ ^ 8 + ζ ^ 12 - ζ ^ 24 + ζ ^ 28)) * equation
      - (
        ((-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 16 + ((1 / 4) : ℂ) * ζ ^ 20)) * Y 0 1
        + ((-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 24)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY01_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 28)) * Y 0 0
      + (((1 : ℂ) - ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 28)) * Y 0 1
      + ((((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 12)) * Y 1 0
      + ((-((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 28)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY01_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(1 : ℂ) + ζ ^ 8 + ζ ^ 12 - ζ ^ 28)) * equation
      - (
        ((-((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 24)) * Y 0 0
        + ((-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((3 / 2) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 16 - ((3 / 4) : ℂ) * ζ ^ 20 + ((3 / 4) : ℂ) * ζ ^ 24)) * Y 0 1
        + ((((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 24)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY01_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 0 1
      + ((((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 12)) * Y 1 0
      + ((-((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY01_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((5 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 24 - ((5 / 3) : ℂ) * ζ ^ 28)) * equation
      - (
        ((-((7 / 22) : ℂ) * ζ ^ 8 + ((1 / 11) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 16 - ((3 / 22) : ℂ) * ζ ^ 20 + ((5 / 22) : ℂ) * ζ ^ 24)) * Y 0 0
        + ((((1 / 11) : ℂ) * ζ ^ 8 - ((9 / 44) : ℂ) * ζ ^ 12 + ((9 / 44) : ℂ) * ζ ^ 16 - ((15 / 44) : ℂ) * ζ ^ 20)) * Y 0 1
        + ((((7 / 22) : ℂ) * ζ ^ 8 - ((1 / 11) : ℂ) * ζ ^ 12 - ((3 / 22) : ℂ) * ζ ^ 16 + ((3 / 22) : ℂ) * ζ ^ 20 - ((5 / 22) : ℂ) * ζ ^ 24)) * Y 4 4
        + ((((39 / 44) : ℂ) * ζ ^ 8 - ((19 / 44) : ℂ) * ζ ^ 12 - ((3 / 22) : ℂ) * ζ ^ 16 - ((25 / 44) : ℂ) * ζ ^ 24)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY01_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 0 1) = 0 := by
  have previous :=
    row16_reducedY01_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((1 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28)) * equation
      - (
        ((((3 / 22) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 4 - ((1 / 22) : ℂ) * ζ ^ 8 + ((1 / 11) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 24)) * Y 1 0
        + ((((3 / 44) : ℂ) - ((3 / 44) : ℂ) * ζ ^ 4 - ((1 / 22) : ℂ) * ζ ^ 8 - ((3 / 22) : ℂ) * ζ ^ 20)) * Y 1 1
        + ((-((3 / 44) : ℂ) + ((3 / 44) : ℂ) * ζ ^ 4 + ((1 / 22) : ℂ) * ζ ^ 8 + ((3 / 22) : ℂ) * ζ ^ 20)) * Y 4 4
        + ((-((3 / 44) : ℂ) + ((3 / 44) : ℂ) * ζ ^ 4 + ((3 / 44) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 20 + ((1 / 22) : ℂ) * ζ ^ 24)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 0 1 = 0 := by
  have reduced :=
    row16_reducedY01_combinationStep03 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row16_reducedY10_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 8 - ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)) * Y 0 1
      + ((((3 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 28)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-(3 : ℂ) + (2 : ℂ) * ζ ^ 12 - (3 : ℂ) * ζ ^ 24)) * equation
      - (
        ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((3 / 4) : ℂ) * ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 12 - ((3 / 4) : ℂ) * ζ ^ 16)) * Y 0 1
        + ((-((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 20)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY10_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 4) : ℂ) * ζ ^ 12)) * Y 0 0
      + ((-((1 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28)) * Y 0 1
      + ((((3 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((1 / 4) : ℂ) * ζ ^ 12)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY10_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((1 : ℂ) - ζ ^ 8 + ζ ^ 28)) * equation
      - (
        ((((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 24)) * Y 0 0
        + ((((3 / 4) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 16 + ((3 / 4) : ℂ) * ζ ^ 20 - ((3 / 4) : ℂ) * ζ ^ 24)) * Y 0 1
        + ((-((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 24)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY10_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((3 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((1 / 4) : ℂ) * ζ ^ 12)) * Y 1 1
      + ((((1 / 4) : ℂ) * ζ ^ 12)) * Y 4 4
      + ((-((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 28)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY10_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((2 / 3) : ℂ) + ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 24)) * equation
      - (
        ((-((5 / 22) : ℂ) + ((5 / 22) : ℂ) * ζ ^ 4 - ((3 / 22) : ℂ) * ζ ^ 8 - ((1 / 11) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 16 - ((1 / 11) : ℂ) * ζ ^ 20)) * Y 0 0
        + ((-((5 / 44) : ℂ) + ((5 / 44) : ℂ) * ζ ^ 4 + ((3 / 22) : ℂ) * ζ ^ 8 - ((3 / 22) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 16)) * Y 0 1
        + ((((5 / 22) : ℂ) - ((5 / 22) : ℂ) * ζ ^ 4 + ((3 / 22) : ℂ) * ζ ^ 8 + ((1 / 11) : ℂ) * ζ ^ 12 - ((1 / 11) : ℂ) * ζ ^ 16 + ((1 / 11) : ℂ) * ζ ^ 20)) * Y 4 4
        + ((((5 / 11) : ℂ) - ((5 / 11) : ℂ) * ζ ^ 4 + ((21 / 44) : ℂ) * ζ ^ 8 + ((1 / 11) : ℂ) * ζ ^ 12 - ((1 / 11) : ℂ) * ζ ^ 16 + ((5 / 22) : ℂ) * ζ ^ 20)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY10_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 1 0) = 0 := by
  have previous :=
    row16_reducedY10_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((1 / 3) : ℂ) + ζ ^ 8 + ζ ^ 12 - ζ ^ 28)) * equation
      - (
        ((-((3 / 22) : ℂ) + ((3 / 22) : ℂ) * ζ ^ 4 - ((3 / 11) : ℂ) * ζ ^ 8 + ((3 / 22) : ℂ) * ζ ^ 16 - ((3 / 22) : ℂ) * ζ ^ 20 + ((3 / 22) : ℂ) * ζ ^ 24)) * Y 1 0
        + ((-((3 / 44) : ℂ) + ((3 / 44) : ℂ) * ζ ^ 4 + ((3 / 22) : ℂ) * ζ ^ 8 - ((9 / 44) : ℂ) * ζ ^ 12 + ((9 / 44) : ℂ) * ζ ^ 16 - ((9 / 44) : ℂ) * ζ ^ 20)) * Y 1 1
        + ((((3 / 44) : ℂ) - ((3 / 44) : ℂ) * ζ ^ 4 - ((3 / 22) : ℂ) * ζ ^ 8 + ((9 / 44) : ℂ) * ζ ^ 12 - ((9 / 44) : ℂ) * ζ ^ 16 + ((9 / 44) : ℂ) * ζ ^ 20)) * Y 4 4
        + ((((3 / 44) : ℂ) - ((3 / 44) : ℂ) * ζ ^ 4 - ((9 / 22) : ℂ) * ζ ^ 8 + ((9 / 22) : ℂ) * ζ ^ 12 - ((15 / 44) : ℂ) * ζ ^ 16 + ((15 / 44) : ℂ) * ζ ^ 20 + ((3 / 44) : ℂ) * ζ ^ 24)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY10
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 1 0 = 0 := by
  have reduced :=
    row16_reducedY10_combinationStep03 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row16_reducedY11_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((13 / 6) : ℂ) - ((7 / 4) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((17 / 4) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 18 + ((7 / 4) : ℂ) * ζ ^ 22 - ((13 / 6) : ℂ) * ζ ^ 24 - ((7 / 2) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((3 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((25 / 12) : ℂ) * ζ ^ 8 + ((13 / 6) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 22 - ((13 / 6) : ℂ) * ζ ^ 24 + ((25 / 12) : ℂ) * ζ ^ 28 - ((5 / 2) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((77 / 3) : ℂ) + (3 : ℂ) * ζ ^ 2 - (14 : ℂ) * ζ ^ 6 + (17 : ℂ) * ζ ^ 8 + (17 : ℂ) * ζ ^ 12 + (17 : ℂ) * ζ ^ 18 - (3 : ℂ) * ζ ^ 22 - (17 : ℂ) * ζ ^ 28 - (7 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((17 / 4) : ℂ) + ((5 / 2) : ℂ) * ζ ^ 2 + ((17 / 4) : ℂ) * ζ ^ 4 - (5 : ℂ) * ζ ^ 6 + (5 : ℂ) * ζ ^ 10 - ((17 / 4) : ℂ) * ζ ^ 12 - ((5 / 2) : ℂ) * ζ ^ 14 + ((17 / 4) : ℂ) * ζ ^ 16 + ((7 / 4) : ℂ) * ζ ^ 18 - ((17 / 4) : ℂ) * ζ ^ 20 - ((7 / 4) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((((3 / 2) : ℂ) * ζ ^ 2 - ((5 / 2) : ℂ) * ζ ^ 6 + ((17 / 2) : ℂ) * ζ ^ 8 + ((7 / 4) : ℂ) * ζ ^ 10 - ((17 / 4) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 14 - ((3 / 4) : ℂ) * ζ ^ 18 - ((17 / 4) : ℂ) * ζ ^ 24 - ((7 / 4) : ℂ) * ζ ^ 26)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY11_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 2) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 2 - ((5 / 12) : ℂ) * ζ ^ 8 - ((5 / 12) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 22 + ((5 / 12) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((-((41 / 12) : ℂ) - ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 6 + ((23 / 4) : ℂ) * ζ ^ 12 + ((7 / 4) : ℂ) * ζ ^ 18 + ζ ^ 22 - ((41 / 12) : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((3 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((25 / 12) : ℂ) * ζ ^ 8 + ((13 / 6) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 22 - ((13 / 6) : ℂ) * ζ ^ 24 + ((25 / 12) : ℂ) * ζ ^ 28 - ((5 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1 / 2) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ((5 / 12) : ℂ) * ζ ^ 8 + ((5 / 12) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22 - ((5 / 12) : ℂ) * ζ ^ 28)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY11_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((2 : ℂ) - ζ ^ 2 - ((11 / 3) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 + ζ ^ 22 + (2 : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 2) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 + ((5 / 12) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 4) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((5 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 2 - ((5 / 4) : ℂ) * ζ ^ 4 + ((11 / 4) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 10 - ((3 / 2) : ℂ) * ζ ^ 12 - ((3 / 4) : ℂ) * ζ ^ 14 + ((3 / 2) : ℂ) * ζ ^ 16 + ((3 / 4) : ℂ) * ζ ^ 18 - ((3 / 2) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 22 + ((3 / 2) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((1 / 2) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 - ((5 / 12) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 26)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY11_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((8 / 3) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((9 / 2) : ℂ) * ζ ^ 12 + ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((8 / 3) : ℂ) * ζ ^ 24 - ζ ^ 30)) * Y 0 1
      + ((-((3 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((25 / 12) : ℂ) * ζ ^ 8 + ((13 / 6) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 22 - ((13 / 6) : ℂ) * ζ ^ 24 + ((25 / 12) : ℂ) * ζ ^ 28 - ((5 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1 / 2) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ((5 / 12) : ℂ) * ζ ^ 8 + ((5 / 12) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22 - ((5 / 12) : ℂ) * ζ ^ 28)) * Y 1 1
      + (((2 : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((5 / 4) : ℂ) * ζ ^ 8 - ((5 / 4) : ℂ) * ζ ^ 12 - ((5 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22 + ((5 / 4) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 4 4
      + (((4 : ℂ) + ((7 / 4) : ℂ) * ζ ^ 6 - (2 : ℂ) * ζ ^ 8 - ((13 / 4) : ℂ) * ζ ^ 12 - ((11 / 4) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 24 + (2 : ℂ) * ζ ^ 28 + ((7 / 4) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY11_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((14 / 3) : ℂ) - ((1 / 3) : ℂ) * ζ ^ 2 + ((8 / 3) : ℂ) * ζ ^ 6 - (3 : ℂ) * ζ ^ 8 - (3 : ℂ) * ζ ^ 12 - (3 : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 22 + (3 : ℂ) * ζ ^ 28 + ((4 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((9 / 22) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 2 - ((9 / 22) : ℂ) * ζ ^ 4 + ((5 / 22) : ℂ) * ζ ^ 6 + ((9 / 11) : ℂ) * ζ ^ 8 - ((3 / 11) : ℂ) * ζ ^ 10 + ((5 / 11) : ℂ) * ζ ^ 14 - ((9 / 22) : ℂ) * ζ ^ 16 - ((5 / 22) : ℂ) * ζ ^ 18 + ((9 / 22) : ℂ) * ζ ^ 20 + ((2 / 11) : ℂ) * ζ ^ 22 - ((9 / 22) : ℂ) * ζ ^ 24 - ((2 / 11) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((9 / 44) : ℂ) - ((25 / 44) : ℂ) * ζ ^ 2 - ((9 / 44) : ℂ) * ζ ^ 4 + ((19 / 22) : ℂ) * ζ ^ 6 - ((9 / 22) : ℂ) * ζ ^ 8 - ((19 / 22) : ℂ) * ζ ^ 10 + ((27 / 44) : ℂ) * ζ ^ 12 + ((15 / 44) : ℂ) * ζ ^ 14 - ((27 / 44) : ℂ) * ζ ^ 16 - ((3 / 11) : ℂ) * ζ ^ 18 + ((27 / 44) : ℂ) * ζ ^ 20 + ((3 / 11) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((-((9 / 22) : ℂ) + ((3 / 22) : ℂ) * ζ ^ 2 + ((9 / 22) : ℂ) * ζ ^ 4 - ((5 / 22) : ℂ) * ζ ^ 6 - ((9 / 11) : ℂ) * ζ ^ 8 + ((3 / 11) : ℂ) * ζ ^ 10 - ((5 / 11) : ℂ) * ζ ^ 14 + ((9 / 22) : ℂ) * ζ ^ 16 + ((5 / 22) : ℂ) * ζ ^ 18 - ((9 / 22) : ℂ) * ζ ^ 20 - ((2 / 11) : ℂ) * ζ ^ 22 + ((9 / 22) : ℂ) * ζ ^ 24 + ((2 / 11) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((9 / 11) : ℂ) - ((5 / 22) : ℂ) * ζ ^ 2 + ((9 / 11) : ℂ) * ζ ^ 4 + ((13 / 44) : ℂ) * ζ ^ 6 - ((27 / 11) : ℂ) * ζ ^ 8 - ((2 / 11) : ℂ) * ζ ^ 10 + ((27 / 44) : ℂ) * ζ ^ 12 - ((35 / 44) : ℂ) * ζ ^ 14 + ((9 / 22) : ℂ) * ζ ^ 16 + ((13 / 44) : ℂ) * ζ ^ 18 - ((9 / 22) : ℂ) * ζ ^ 20 - ((2 / 11) : ℂ) * ζ ^ 22 + ((45 / 44) : ℂ) * ζ ^ 24 + ((5 / 11) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY11_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((3 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((25 / 12) : ℂ) * ζ ^ 8 + ((13 / 6) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 22 - ((13 / 6) : ℂ) * ζ ^ 24 + ((25 / 12) : ℂ) * ζ ^ 28 - ((5 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1 / 2) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ((5 / 12) : ℂ) * ζ ^ 8 + ((5 / 12) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22 - ((5 / 12) : ℂ) * ζ ^ 28)) * Y 1 1
      + (((2 : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((5 / 4) : ℂ) * ζ ^ 8 - ((5 / 4) : ℂ) * ζ ^ 12 - ((5 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22 + ((5 / 4) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 4 4
      + (((4 : ℂ) + ((7 / 4) : ℂ) * ζ ^ 6 - (2 : ℂ) * ζ ^ 8 - ((13 / 4) : ℂ) * ζ ^ 12 - ((11 / 4) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 24 + (2 : ℂ) * ζ ^ 28 + ((7 / 4) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY11_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28 - ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-(1 : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 4 - ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 16 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((5 / 3) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 + ((5 / 3) : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 6 - ((11 / 6) : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 10 + ((7 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((7 / 2) : ℂ) * ζ ^ 16 - ζ ^ 18 + (2 : ℂ) * ζ ^ 20 + ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 + ((4 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((1 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 - ((5 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 + ((2 / 3) : ℂ) * ζ ^ 28)) * Y 6 7
        + (((1 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ζ ^ 4 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY11_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 2) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 12 - ((1 / 6) : ℂ) * ζ ^ 24 + ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((3 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY11_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((10 / 3) : ℂ) * ζ ^ 2 + ((4 / 3) : ℂ) * ζ ^ 6 - (3 : ℂ) * ζ ^ 8 + ((14 / 3) : ℂ) * ζ ^ 12 + ((5 / 3) : ℂ) * ζ ^ 18 + ((10 / 3) : ℂ) * ζ ^ 22 - ((14 / 3) : ℂ) * ζ ^ 24 + (3 : ℂ) * ζ ^ 28 - ((14 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((4 / 11) : ℂ) * ζ ^ 2 + ((9 / 22) : ℂ) * ζ ^ 6 - ((5 / 22) : ℂ) * ζ ^ 8 - ((19 / 22) : ℂ) * ζ ^ 10 + ((7 / 11) : ℂ) * ζ ^ 12 + ((5 / 22) : ℂ) * ζ ^ 14 - ((23 / 22) : ℂ) * ζ ^ 16 + ((2 / 11) : ℂ) * ζ ^ 18 + ((23 / 22) : ℂ) * ζ ^ 20 - ((7 / 11) : ℂ) * ζ ^ 22 - ((9 / 22) : ℂ) * ζ ^ 24 + ((7 / 11) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-(2 : ℂ) - ((19 / 44) : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 4 - ((13 / 44) : ℂ) * ζ ^ 6 - ((15 / 11) : ℂ) * ζ ^ 8 + ((13 / 44) : ℂ) * ζ ^ 10 + ((69 / 44) : ℂ) * ζ ^ 12 - ((3 / 11) : ℂ) * ζ ^ 14 - ((69 / 44) : ℂ) * ζ ^ 16 + ((21 / 22) : ℂ) * ζ ^ 18 + ((27 / 44) : ℂ) * ζ ^ 20 - ((21 / 22) : ℂ) * ζ ^ 22)) * Y 1 1
        + (((2 : ℂ) + ((19 / 44) : ℂ) * ζ ^ 2 - (2 : ℂ) * ζ ^ 4 + ((13 / 44) : ℂ) * ζ ^ 6 + ((15 / 11) : ℂ) * ζ ^ 8 - ((13 / 44) : ℂ) * ζ ^ 10 - ((69 / 44) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 14 + ((69 / 44) : ℂ) * ζ ^ 16 - ((21 / 22) : ℂ) * ζ ^ 18 - ((27 / 44) : ℂ) * ζ ^ 20 + ((21 / 22) : ℂ) * ζ ^ 22)) * Y 4 4
        + (((4 : ℂ) + ((15 / 22) : ℂ) * ζ ^ 2 - (4 : ℂ) * ζ ^ 4 + ((35 / 44) : ℂ) * ζ ^ 6 + ((115 / 44) : ℂ) * ζ ^ 8 - ((45 / 44) : ℂ) * ζ ^ 10 - ((31 / 11) : ℂ) * ζ ^ 12 + ((29 / 44) : ℂ) * ζ ^ 14 + ((115 / 44) : ℂ) * ζ ^ 16 - ((20 / 11) : ℂ) * ζ ^ 18 - ((31 / 44) : ℂ) * ζ ^ 20 + ((35 / 22) : ℂ) * ζ ^ 22 - ((9 / 44) : ℂ) * ζ ^ 24 + ((7 / 22) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY11_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 1 1
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY11_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((2 : ℂ) - ((4 / 3) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 22 + ((4 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 2) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((1 / 2) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 - ((3 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 22 - ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26 + ζ ^ 28)) * Y 1 1
        + ((-((7 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((7 / 6) : ℂ) * ζ ^ 6 - ((7 / 6) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 14 - ((5 / 6) : ℂ) * ζ ^ 16 - ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 26 - (2 : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((1 / 2) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 16 + ((3 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 22 + ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 - ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY11
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 1 1 = Y 7 7 := by
  have reduced :=
    row16_reducedY11_combinationStep05 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row16_reducedY22_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((43 / 12) : ℂ) + ((31 / 4) : ℂ) * ζ ^ 12 - ((43 / 12) : ℂ) * ζ ^ 24)) * Y 0 1
      + ((-((25 / 6) : ℂ) * ζ ^ 8 + ((43 / 12) : ℂ) * ζ ^ 12 - ((43 / 12) : ℂ) * ζ ^ 24 + ((25 / 6) : ℂ) * ζ ^ 28)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((136 / 3) : ℂ) + (31 : ℂ) * ζ ^ 8 + (31 : ℂ) * ζ ^ 12 - (31 : ℂ) * ζ ^ 28)) * equation
      - (
        ((-((31 / 4) : ℂ) + ((31 / 4) : ℂ) * ζ ^ 4 - ((31 / 4) : ℂ) * ζ ^ 12 + ((31 / 4) : ℂ) * ζ ^ 16 - ((31 / 4) : ℂ) * ζ ^ 20)) * Y 0 1
        + ((((31 / 2) : ℂ) * ζ ^ 8 - ((31 / 4) : ℂ) * ζ ^ 12 - ((31 / 4) : ℂ) * ζ ^ 24)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY22_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((5 / 4) : ℂ) - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((-((73 / 12) : ℂ) + ((23 / 2) : ℂ) * ζ ^ 12 - ((73 / 12) : ℂ) * ζ ^ 24)) * Y 0 1
      + ((-((25 / 6) : ℂ) * ζ ^ 8 + ((43 / 12) : ℂ) * ζ ^ 12 - ((43 / 12) : ℂ) * ζ ^ 24 + ((25 / 6) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((5 / 4) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 - ((5 / 6) : ℂ) * ζ ^ 28)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY22_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((5 : ℂ) - ((25 / 3) : ℂ) * ζ ^ 12 + (5 : ℂ) * ζ ^ 24)) * equation
      - (
        ((-((5 / 4) : ℂ) + ((5 / 4) : ℂ) * ζ ^ 4 + ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 4) : ℂ) * ζ ^ 20)) * Y 0 0
        + ((((5 / 2) : ℂ) - ((5 / 2) : ℂ) * ζ ^ 4 + ((25 / 4) : ℂ) * ζ ^ 8 - ((15 / 4) : ℂ) * ζ ^ 12 + ((15 / 4) : ℂ) * ζ ^ 16 - ((15 / 4) : ℂ) * ζ ^ 20)) * Y 0 1
        + ((((5 / 4) : ℂ) - ((5 / 4) : ℂ) * ζ ^ 4 - ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 4) : ℂ) * ζ ^ 20)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY22_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((7 / 4) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 - ((5 / 3) : ℂ) * ζ ^ 8 - ((5 / 3) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 3) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((41 / 12) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + (7 : ℂ) * ζ ^ 12 + ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((41 / 12) : ℂ) * ζ ^ 24 - ζ ^ 30)) * Y 0 1
      + ((-((25 / 6) : ℂ) * ζ ^ 8 + ((43 / 12) : ℂ) * ζ ^ 12 - ((43 / 12) : ℂ) * ζ ^ 24 + ((25 / 6) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((5 / 4) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 - ((5 / 6) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((-((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((4 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have previous :=
    row16_reducedY22_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation02
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + (4 : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 12 - ((10 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 28 + (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 6) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 6 - ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 26 - ((1 / 2) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((8 / 3) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 2 + (3 : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((7 / 2) : ℂ) * ζ ^ 12 - ((1 / 6) : ℂ) * ζ ^ 14 - ((19 / 6) : ℂ) * ζ ^ 16 + ((1 / 3) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 - (2 : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 + (2 : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((1 / 6) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 6 + ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((((7 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 - ((7 / 6) : ℂ) * ζ ^ 4 - ((2 / 3) : ℂ) * ζ ^ 6 + ((1 / 6) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 16 + ((1 / 3) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY22_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((8 / 3) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((9 / 2) : ℂ) * ζ ^ 12 + ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((8 / 3) : ℂ) * ζ ^ 24 - ζ ^ 30)) * Y 0 1
      + ((-((25 / 6) : ℂ) * ζ ^ 8 + ((43 / 12) : ℂ) * ζ ^ 12 - ((43 / 12) : ℂ) * ζ ^ 24 + ((25 / 6) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((5 / 4) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 - ((5 / 6) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((-((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((4 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((13 / 4) : ℂ) - ((5 / 2) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((((13 / 2) : ℂ) - ((13 / 4) : ℂ) * ζ ^ 8 - ((23 / 4) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 24 + ((13 / 4) : ℂ) * ζ ^ 28)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY22_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((19 / 3) : ℂ) - (8 : ℂ) * ζ ^ 8 - (8 : ℂ) * ζ ^ 12 + (8 : ℂ) * ζ ^ 28)) * equation
      - (
        ((((12 / 11) : ℂ) - ((12 / 11) : ℂ) * ζ ^ 4 + ((24 / 11) : ℂ) * ζ ^ 8 - ((12 / 11) : ℂ) * ζ ^ 16 + ((12 / 11) : ℂ) * ζ ^ 20 - ((12 / 11) : ℂ) * ζ ^ 24)) * Y 0 0
        + ((((6 / 11) : ℂ) - ((6 / 11) : ℂ) * ζ ^ 4 - ((12 / 11) : ℂ) * ζ ^ 8 + ((18 / 11) : ℂ) * ζ ^ 12 - ((18 / 11) : ℂ) * ζ ^ 16 + ((18 / 11) : ℂ) * ζ ^ 20)) * Y 0 1
        + ((-((12 / 11) : ℂ) + ((12 / 11) : ℂ) * ζ ^ 4 - ((24 / 11) : ℂ) * ζ ^ 8 + ((12 / 11) : ℂ) * ζ ^ 16 - ((12 / 11) : ℂ) * ζ ^ 20 + ((12 / 11) : ℂ) * ζ ^ 24)) * Y 4 4
        + ((-((24 / 11) : ℂ) + ((24 / 11) : ℂ) * ζ ^ 4 - ((72 / 11) : ℂ) * ζ ^ 8 + ((18 / 11) : ℂ) * ζ ^ 12 + ((12 / 11) : ℂ) * ζ ^ 16 - ((12 / 11) : ℂ) * ζ ^ 20 + ((30 / 11) : ℂ) * ζ ^ 24)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY22_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((25 / 6) : ℂ) * ζ ^ 8 + ((43 / 12) : ℂ) * ζ ^ 12 - ((43 / 12) : ℂ) * ζ ^ 24 + ((25 / 6) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((5 / 4) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 - ((5 / 6) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((-((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((4 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((13 / 4) : ℂ) - ((5 / 2) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((((13 / 2) : ℂ) - ((13 / 4) : ℂ) * ζ ^ 8 - ((23 / 4) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 24 + ((13 / 4) : ℂ) * ζ ^ 28)) * Y 5 4
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY22_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28 - ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-(1 : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 4 - ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 16 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((5 / 3) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 + ((5 / 3) : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 6 - ((11 / 6) : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 10 + ((7 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((7 / 2) : ℂ) * ζ ^ 16 - ζ ^ 18 + (2 : ℂ) * ζ ^ 20 + ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 + ((4 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((1 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 - ((5 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 + ((2 / 3) : ℂ) * ζ ^ 28)) * Y 6 7
        + (((1 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ζ ^ 4 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY22_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 2) : ℂ) * ζ ^ 6 - ((10 / 3) : ℂ) * ζ ^ 8 + ((41 / 12) : ℂ) * ζ ^ 12 - ((41 / 12) : ℂ) * ζ ^ 24 + ((10 / 3) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((11 / 4) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 + ((5 / 3) : ℂ) * ζ ^ 8 + ((5 / 3) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 3) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 1
      + (((1 : ℂ))) * Y 2 2
      + ((((13 / 4) : ℂ) - ((5 / 2) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((((13 / 2) : ℂ) - ((13 / 4) : ℂ) * ζ ^ 8 - ((23 / 4) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 24 + ((13 / 4) : ℂ) * ζ ^ 28)) * Y 5 4
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY22_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation12
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 6) : ℂ) * ζ ^ 6 - ((1 / 6) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 22 + ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 26 - ((1 / 6) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((3 / 2) : ℂ) * ζ ^ 4 - ((3 / 2) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ((7 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 16 + ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 - ((4 / 3) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 + ((2 / 3) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((3 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((3 / 2) : ℂ) * ζ ^ 4 + ((3 / 2) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ((7 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 16 - ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 + ((4 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26 - ((2 / 3) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((4 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 + ((4 / 3) : ℂ) * ζ ^ 4 + ((4 / 3) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 16 - ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 + ((7 / 6) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 26 - ((1 / 3) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY22_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 2) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 12 - ((1 / 6) : ℂ) * ζ ^ 24 + ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 1
      + (((1 : ℂ))) * Y 2 2
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY22_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(8 : ℂ) * ζ ^ 8 + ((19 / 3) : ℂ) * ζ ^ 12 - ((19 / 3) : ℂ) * ζ ^ 24 + (8 : ℂ) * ζ ^ 28)) * equation
      - (
        ((((5 / 22) : ℂ) * ζ ^ 8 + ((19 / 22) : ℂ) * ζ ^ 12 - ((43 / 22) : ℂ) * ζ ^ 16 + ((43 / 22) : ℂ) * ζ ^ 20 - ((12 / 11) : ℂ) * ζ ^ 24)) * Y 1 0
        + ((-((13 / 4) : ℂ) + ((13 / 4) : ℂ) * ζ ^ 4 - ((105 / 44) : ℂ) * ζ ^ 8 + ((129 / 44) : ℂ) * ζ ^ 12 - ((129 / 44) : ℂ) * ζ ^ 16 + ((18 / 11) : ℂ) * ζ ^ 20)) * Y 1 1
        + ((((13 / 4) : ℂ) - ((13 / 4) : ℂ) * ζ ^ 4 + ((105 / 44) : ℂ) * ζ ^ 8 - ((129 / 44) : ℂ) * ζ ^ 12 + ((129 / 44) : ℂ) * ζ ^ 16 - ((18 / 11) : ℂ) * ζ ^ 20)) * Y 4 4
        + ((((13 / 2) : ℂ) - ((13 / 2) : ℂ) * ζ ^ 4 + ((215 / 44) : ℂ) * ζ ^ 8 - ((239 / 44) : ℂ) * ζ ^ 12 + ((215 / 44) : ℂ) * ζ ^ 16 - ((101 / 44) : ℂ) * ζ ^ 20 - ((6 / 11) : ℂ) * ζ ^ 24)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY22_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 2 2
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY22_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((2 : ℂ) - ((4 / 3) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 22 + ((4 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 2) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((1 / 2) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 - ((3 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 22 - ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26 + ζ ^ 28)) * Y 1 1
        + ((-((7 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((7 / 6) : ℂ) * ζ ^ 6 - ((7 / 6) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 14 - ((5 / 6) : ℂ) * ζ ^ 16 - ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 26 - (2 : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((1 / 2) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 16 + ((3 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 22 + ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 - ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY22
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 2 2 = Y 7 7 := by
  have reduced :=
    row16_reducedY22_combinationStep07 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row16_reducedY23_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((10 / 3) : ℂ) + ((7 / 6) : ℂ) * ζ ^ 2 + ((13 / 12) : ℂ) * ζ ^ 6 + ((7 / 6) : ℂ) * ζ ^ 8 + ((10 / 3) : ℂ) * ζ ^ 12 - ((10 / 3) : ℂ) * ζ ^ 18 - ((7 / 6) : ℂ) * ζ ^ 22 - ((13 / 12) : ℂ) * ζ ^ 24 - ((7 / 6) : ℂ) * ζ ^ 28 + ((10 / 3) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((9 / 4) : ℂ) + ((9 / 4) : ℂ) * ζ ^ 2 + ((10 / 3) : ℂ) * ζ ^ 12 - ((13 / 6) : ℂ) * ζ ^ 18 - ((9 / 4) : ℂ) * ζ ^ 22 - ((13 / 6) : ℂ) * ζ ^ 24 + ((10 / 3) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-(13 : ℂ) - ((26 / 3) : ℂ) * ζ ^ 2 + ((40 / 3) : ℂ) * ζ ^ 6 + ((40 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 - ((41 / 3) : ℂ) * ζ ^ 18 + ((26 / 3) : ℂ) * ζ ^ 22 + (9 : ℂ) * ζ ^ 24 - ((40 / 3) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((1 / 12) : ℂ) - ((10 / 3) : ℂ) * ζ ^ 2 - ((1 / 12) : ℂ) * ζ ^ 4 + ((67 / 12) : ℂ) * ζ ^ 6 + ((9 / 4) : ℂ) * ζ ^ 8 - ((67 / 12) : ℂ) * ζ ^ 10 - ((67 / 12) : ℂ) * ζ ^ 12 + ((9 / 4) : ℂ) * ζ ^ 14 + ((67 / 12) : ℂ) * ζ ^ 16 - ((1 / 12) : ℂ) * ζ ^ 18 - ((10 / 3) : ℂ) * ζ ^ 20 + ((1 / 12) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((((9 / 4) : ℂ) - ((9 / 4) : ℂ) * ζ ^ 2 - ((9 / 4) : ℂ) * ζ ^ 4 + ((9 / 4) : ℂ) * ζ ^ 6 + ((11 / 2) : ℂ) * ζ ^ 8 - ((1 / 12) : ℂ) * ζ ^ 10 - ((10 / 3) : ℂ) * ζ ^ 12 - ((10 / 3) : ℂ) * ζ ^ 14 + ((13 / 6) : ℂ) * ζ ^ 18 + ((9 / 4) : ℂ) * ζ ^ 20 - ((10 / 3) : ℂ) * ζ ^ 24 + ((1 / 12) : ℂ) * ζ ^ 26)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY23_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((7 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 22 - ((5 / 12) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((61 / 12) : ℂ) + ((29 / 12) : ℂ) * ζ ^ 2 + ((4 / 3) : ℂ) * ζ ^ 6 + ((29 / 12) : ℂ) * ζ ^ 8 + ((17 / 6) : ℂ) * ζ ^ 12 - ((17 / 6) : ℂ) * ζ ^ 18 - ((29 / 12) : ℂ) * ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 - ((29 / 12) : ℂ) * ζ ^ 28 + ((61 / 12) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((9 / 4) : ℂ) + ((9 / 4) : ℂ) * ζ ^ 2 + ((10 / 3) : ℂ) * ζ ^ 12 - ((13 / 6) : ℂ) * ζ ^ 18 - ((9 / 4) : ℂ) * ζ ^ 22 - ((13 / 6) : ℂ) * ζ ^ 24 + ((10 / 3) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((7 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 22 + ((5 / 12) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY23_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((4 / 3) : ℂ) - (2 : ℂ) * ζ ^ 2 + ((7 / 3) : ℂ) * ζ ^ 6 - (2 : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 22 - ((7 / 3) : ℂ) * ζ ^ 24 + (2 : ℂ) * ζ ^ 28 - ((4 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((7 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 2 - ((7 / 12) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 6 + ((13 / 12) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 + ((7 / 12) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((7 / 4) : ℂ) - ((5 / 4) : ℂ) * ζ ^ 2 - ((7 / 4) : ℂ) * ζ ^ 4 + ζ ^ 6 + ((3 / 2) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 10 + ((7 / 4) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 14 - ((13 / 4) : ℂ) * ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 18 + ((13 / 4) : ℂ) * ζ ^ 20 - ζ ^ 22 - ((3 / 2) : ℂ) * ζ ^ 24 + ζ ^ 26)) * Y 0 1
        + ((-((7 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 2 + ((7 / 12) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 6 - ((13 / 12) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 - ((7 / 12) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 26)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY23_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 2 - ((3 / 4) : ℂ) * ζ ^ 6 - ζ ^ 8 + ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 22 - ((3 / 4) : ℂ) * ζ ^ 24 + ζ ^ 28)) * Y 0 0
      + ((-((3 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 8 + ζ ^ 12 - ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 28 + ((3 / 4) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((9 / 4) : ℂ) + ((9 / 4) : ℂ) * ζ ^ 2 + ((10 / 3) : ℂ) * ζ ^ 12 - ((13 / 6) : ℂ) * ζ ^ 18 - ((9 / 4) : ℂ) * ζ ^ 22 - ((13 / 6) : ℂ) * ζ ^ 24 + ((10 / 3) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((7 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 22 + ((5 / 12) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((4 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 30)) * Y 3 3) = 0 := by
  have previous :=
    row16_reducedY23_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation03
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + (4 : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 12 - ((10 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 28 + (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((7 / 6) : ℂ) - ((5 / 6) : ℂ) * ζ ^ 2 + ((7 / 6) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 6 - ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 16 - ((1 / 3) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-(4 : ℂ) + ((11 / 6) : ℂ) * ζ ^ 2 + (4 : ℂ) * ζ ^ 4 - (3 : ℂ) * ζ ^ 6 - ζ ^ 8 + (3 : ℂ) * ζ ^ 10 + ((11 / 6) : ℂ) * ζ ^ 12 - ((4 / 3) : ℂ) * ζ ^ 14 - ((11 / 6) : ℂ) * ζ ^ 16 + ((11 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 - ((11 / 6) : ℂ) * ζ ^ 22 - ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 + ζ ^ 28)) * Y 0 1
        + ((((1 / 6) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 6 + ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((((7 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 - ((7 / 6) : ℂ) * ζ ^ 4 - ((2 / 3) : ℂ) * ζ ^ 6 + ((1 / 6) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 16 + ((1 / 3) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY23_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((9 / 4) : ℂ) + ((9 / 4) : ℂ) * ζ ^ 2 + ((10 / 3) : ℂ) * ζ ^ 12 - ((13 / 6) : ℂ) * ζ ^ 18 - ((9 / 4) : ℂ) * ζ ^ 22 - ((13 / 6) : ℂ) * ζ ^ 24 + ((10 / 3) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((7 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 22 + ((5 / 12) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((4 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 2 - ((3 / 4) : ℂ) * ζ ^ 6 - ζ ^ 8 + ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 22 - ((3 / 4) : ℂ) * ζ ^ 24 + ζ ^ 28)) * Y 4 4
      + ((((9 / 4) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((7 / 4) : ℂ) * ζ ^ 6 - ((7 / 4) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 12 + ((11 / 4) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ζ ^ 24 + ((7 / 4) : ℂ) * ζ ^ 28 - ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY23_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((1 : ℂ) + (3 : ℂ) * ζ ^ 2 - ((1 / 3) : ℂ) * ζ ^ 6 - ((8 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 - (3 : ℂ) * ζ ^ 22 - ((7 / 3) : ℂ) * ζ ^ 24 + ((8 / 3) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((9 / 22) : ℂ) - ((3 / 11) : ℂ) * ζ ^ 2 - ((9 / 22) : ℂ) * ζ ^ 4 - ((4 / 11) : ℂ) * ζ ^ 6 + ((5 / 11) : ℂ) * ζ ^ 8 + ((17 / 22) : ℂ) * ζ ^ 10 + ((7 / 22) : ℂ) * ζ ^ 12 - ((15 / 22) : ℂ) * ζ ^ 14 - ((15 / 22) : ℂ) * ζ ^ 16 + ((7 / 22) : ℂ) * ζ ^ 18 + ((15 / 22) : ℂ) * ζ ^ 20 + ((1 / 11) : ℂ) * ζ ^ 22 - ((4 / 11) : ℂ) * ζ ^ 24 - ((1 / 11) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((6 / 11) : ℂ) + ((19 / 22) : ℂ) * ζ ^ 2 + ((6 / 11) : ℂ) * ζ ^ 4 - ((41 / 44) : ℂ) * ζ ^ 6 - ((37 / 44) : ℂ) * ζ ^ 8 + ((41 / 44) : ℂ) * ζ ^ 10 + ((45 / 44) : ℂ) * ζ ^ 12 - ((21 / 44) : ℂ) * ζ ^ 14 - ((45 / 44) : ℂ) * ζ ^ 16 - ((3 / 22) : ℂ) * ζ ^ 18 + ((6 / 11) : ℂ) * ζ ^ 20 + ((3 / 22) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((-((9 / 22) : ℂ) + ((3 / 11) : ℂ) * ζ ^ 2 + ((9 / 22) : ℂ) * ζ ^ 4 + ((4 / 11) : ℂ) * ζ ^ 6 - ((5 / 11) : ℂ) * ζ ^ 8 - ((17 / 22) : ℂ) * ζ ^ 10 - ((7 / 22) : ℂ) * ζ ^ 12 + ((15 / 22) : ℂ) * ζ ^ 14 + ((15 / 22) : ℂ) * ζ ^ 16 - ((7 / 22) : ℂ) * ζ ^ 18 - ((15 / 22) : ℂ) * ζ ^ 20 - ((1 / 11) : ℂ) * ζ ^ 22 + ((4 / 11) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((69 / 44) : ℂ) + ((17 / 11) : ℂ) * ζ ^ 2 + ((69 / 44) : ℂ) * ζ ^ 4 - ((1 / 44) : ℂ) * ζ ^ 6 - ((87 / 44) : ℂ) * ζ ^ 8 - ζ ^ 10 + ((5 / 22) : ℂ) * ζ ^ 12 + ((27 / 22) : ℂ) * ζ ^ 14 + ((15 / 22) : ℂ) * ζ ^ 16 - ((41 / 44) : ℂ) * ζ ^ 18 - ((51 / 44) : ℂ) * ζ ^ 20 - ((1 / 11) : ℂ) * ζ ^ 22 + ((10 / 11) : ℂ) * ζ ^ 24 + ((5 / 22) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY23_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((7 / 4) : ℂ) + ((7 / 4) : ℂ) * ζ ^ 2 + ((5 / 2) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 - ((7 / 4) : ℂ) * ζ ^ 22 - ((3 / 2) : ℂ) * ζ ^ 24 + ((5 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((3 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 2 + ((3 / 4) : ℂ) * ζ ^ 6 + ζ ^ 8 - ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 22 + ((3 / 4) : ℂ) * ζ ^ 24 - ζ ^ 28)) * Y 1 1
      + (((1 : ℂ))) * Y 2 3
      + ((((3 / 4) : ℂ) + ((3 / 4) : ℂ) * ζ ^ 2 - ((3 / 4) : ℂ) * ζ ^ 6 - ζ ^ 8 + ζ ^ 18 - ((3 / 4) : ℂ) * ζ ^ 22 - ((3 / 4) : ℂ) * ζ ^ 24 + ζ ^ 28)) * Y 4 4
      + ((((9 / 4) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((7 / 4) : ℂ) * ζ ^ 6 - ((7 / 4) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 12 + ((11 / 4) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ζ ^ 24 + ((7 / 4) : ℂ) * ζ ^ 28 - ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY23_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation13
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((4 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 4 - ((4 / 3) : ℂ) * ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 12 - ((7 / 6) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 16 + ((7 / 6) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 20 - ((7 / 6) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 + ((1 / 3) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((3 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((3 / 2) : ℂ) * ζ ^ 4 + ((3 / 2) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ((7 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 16 - ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 + ((4 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26 - ((2 / 3) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((4 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 + ((4 / 3) : ℂ) * ζ ^ 4 + ((4 / 3) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 16 - ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 + ((7 / 6) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 26 - ((1 / 3) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY23_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 2 3) = 0 := by
  have previous :=
    row16_reducedY23_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((13 / 3) : ℂ) + (5 : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 + ((16 / 3) : ℂ) * ζ ^ 12 - (4 : ℂ) * ζ ^ 18 - (5 : ℂ) * ζ ^ 22 - ((10 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 + (6 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((3 / 11) : ℂ) + ((1 / 22) : ℂ) * ζ ^ 2 + ((3 / 11) : ℂ) * ζ ^ 4 - ((3 / 11) : ℂ) * ζ ^ 6 - ((7 / 11) : ℂ) * ζ ^ 8 + ((21 / 22) : ℂ) * ζ ^ 10 + ((5 / 11) : ℂ) * ζ ^ 12 - ((3 / 22) : ℂ) * ζ ^ 14 - ((6 / 11) : ℂ) * ζ ^ 16 - ((3 / 22) : ℂ) * ζ ^ 18 + ((6 / 11) : ℂ) * ζ ^ 20 + ((9 / 11) : ℂ) * ζ ^ 22 - ((1 / 11) : ℂ) * ζ ^ 24 - ((9 / 11) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((18 / 11) : ℂ) + ((3 / 11) : ℂ) * ζ ^ 2 + ((18 / 11) : ℂ) * ζ ^ 4 + ((27 / 44) : ℂ) * ζ ^ 6 - ((17 / 22) : ℂ) * ζ ^ 8 - ((27 / 44) : ℂ) * ζ ^ 10 + ((9 / 11) : ℂ) * ζ ^ 12 + ((9 / 44) : ℂ) * ζ ^ 14 - ((9 / 11) : ℂ) * ζ ^ 16 - ((27 / 22) : ℂ) * ζ ^ 18 + ((3 / 22) : ℂ) * ζ ^ 20 + ((27 / 22) : ℂ) * ζ ^ 22)) * Y 1 1
        + ((((18 / 11) : ℂ) - ((3 / 11) : ℂ) * ζ ^ 2 - ((18 / 11) : ℂ) * ζ ^ 4 - ((27 / 44) : ℂ) * ζ ^ 6 + ((17 / 22) : ℂ) * ζ ^ 8 + ((27 / 44) : ℂ) * ζ ^ 10 - ((9 / 11) : ℂ) * ζ ^ 12 - ((9 / 44) : ℂ) * ζ ^ 14 + ((9 / 11) : ℂ) * ζ ^ 16 + ((27 / 22) : ℂ) * ζ ^ 18 - ((3 / 22) : ℂ) * ζ ^ 20 - ((27 / 22) : ℂ) * ζ ^ 22)) * Y 4 4
        + ((((69 / 22) : ℂ) - ((23 / 44) : ℂ) * ζ ^ 2 - ((69 / 22) : ℂ) * ζ ^ 4 - ((15 / 11) : ℂ) * ζ ^ 6 + ((27 / 22) : ℂ) * ζ ^ 8 + ((75 / 44) : ℂ) * ζ ^ 10 - ((31 / 22) : ℂ) * ζ ^ 12 - ((21 / 44) : ℂ) * ζ ^ 14 + ((15 / 11) : ℂ) * ζ ^ 16 + ((105 / 44) : ℂ) * ζ ^ 18 - ((45 / 22) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 24 - ((9 / 22) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY23
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 2 3 = 0 := by
  have reduced :=
    row16_reducedY23_combinationStep05 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row16_reducedY32_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((7 / 6) : ℂ) - ((17 / 4) : ℂ) * ζ ^ 2 - ((11 / 12) : ℂ) * ζ ^ 6 - ((5 / 4) : ℂ) * ζ ^ 8 - ((10 / 3) : ℂ) * ζ ^ 12 + ((37 / 12) : ℂ) * ζ ^ 18 + ((17 / 4) : ℂ) * ζ ^ 22 + ((17 / 4) : ℂ) * ζ ^ 24 + ((5 / 4) : ℂ) * ζ ^ 28 - (3 : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((37 / 12) : ℂ) - ((13 / 6) : ℂ) * ζ ^ 2 - ((1 / 12) : ℂ) * ζ ^ 6 + ((13 / 6) : ℂ) * ζ ^ 8 - ((7 / 6) : ℂ) * ζ ^ 12 - ((7 / 6) : ℂ) * ζ ^ 18 + ((13 / 6) : ℂ) * ζ ^ 22 - ((1 / 12) : ℂ) * ζ ^ 24 - ((13 / 6) : ℂ) * ζ ^ 28 - ((37 / 12) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((((76 / 3) : ℂ) - ((14 / 3) : ℂ) * ζ ^ 2 - (12 : ℂ) * ζ ^ 6 - ((40 / 3) : ℂ) * ζ ^ 8 - ((62 / 3) : ℂ) * ζ ^ 12 + ((76 / 3) : ℂ) * ζ ^ 18 + ((14 / 3) : ℂ) * ζ ^ 22 + ((37 / 3) : ℂ) * ζ ^ 24 + ((40 / 3) : ℂ) * ζ ^ 28 - (13 : ℂ) * ζ ^ 30)) * equation
      - (
        ((((31 / 6) : ℂ) + ((37 / 12) : ℂ) * ζ ^ 2 - ((31 / 6) : ℂ) * ζ ^ 4 - ((31 / 6) : ℂ) * ζ ^ 6 + ((37 / 12) : ℂ) * ζ ^ 8 + ((31 / 6) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 12 - ((25 / 12) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 16 + ((13 / 4) : ℂ) * ζ ^ 18 + ((10 / 3) : ℂ) * ζ ^ 20 - ((13 / 4) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((((37 / 12) : ℂ) + ((13 / 6) : ℂ) * ζ ^ 2 - ((37 / 12) : ℂ) * ζ ^ 4 - ((25 / 12) : ℂ) * ζ ^ 6 - ((65 / 12) : ℂ) * ζ ^ 8 + ((13 / 4) : ℂ) * ζ ^ 10 + ((10 / 3) : ℂ) * ζ ^ 12 + ((37 / 12) : ℂ) * ζ ^ 14 + ((7 / 6) : ℂ) * ζ ^ 18 + ((37 / 12) : ℂ) * ζ ^ 20 + ((10 / 3) : ℂ) * ζ ^ 24 - ((13 / 4) : ℂ) * ζ ^ 26)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY32_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((7 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 6 + ((5 / 12) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 - ((7 / 12) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 22 - ζ ^ 24 - ((5 / 12) : ℂ) * ζ ^ 28 - ((5 / 12) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((7 / 12) : ℂ) - ((11 / 4) : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 + ((7 / 4) : ℂ) * ζ ^ 8 - ((25 / 12) : ℂ) * ζ ^ 12 + ((10 / 3) : ℂ) * ζ ^ 18 + ((11 / 4) : ℂ) * ζ ^ 22 + ((11 / 4) : ℂ) * ζ ^ 24 - ((7 / 4) : ℂ) * ζ ^ 28 - ((9 / 2) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((37 / 12) : ℂ) - ((13 / 6) : ℂ) * ζ ^ 2 - ((1 / 12) : ℂ) * ζ ^ 6 + ((13 / 6) : ℂ) * ζ ^ 8 - ((7 / 6) : ℂ) * ζ ^ 12 - ((7 / 6) : ℂ) * ζ ^ 18 + ((13 / 6) : ℂ) * ζ ^ 22 - ((1 / 12) : ℂ) * ζ ^ 24 - ((13 / 6) : ℂ) * ζ ^ 28 - ((37 / 12) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((7 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 6 - ((5 / 12) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 12 + ((7 / 12) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 22 + ζ ^ 24 + ((5 / 12) : ℂ) * ζ ^ 28 + ((5 / 12) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY32_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((2 : ℂ) + ((7 / 3) : ℂ) * ζ ^ 2 + ((7 / 3) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ((13 / 3) : ℂ) * ζ ^ 18 - ((7 / 3) : ℂ) * ζ ^ 22 - ((7 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28 + ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((7 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 2 - ((7 / 12) : ℂ) * ζ ^ 4 - ((1 / 12) : ℂ) * ζ ^ 6 + ((2 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 10 - ((1 / 12) : ℂ) * ζ ^ 12 + ((5 / 12) : ℂ) * ζ ^ 14 + ((7 / 12) : ℂ) * ζ ^ 18 + ((7 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((7 / 4) : ℂ) - ((3 / 2) : ℂ) * ζ ^ 2 - ((7 / 4) : ℂ) * ζ ^ 4 + ((5 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((7 / 4) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 14 - (2 : ℂ) * ζ ^ 16 - ((1 / 4) : ℂ) * ζ ^ 18 + (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((7 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 2 + ((7 / 12) : ℂ) * ζ ^ 4 + ((1 / 12) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 10 + ((1 / 12) : ℂ) * ζ ^ 12 - ((5 / 12) : ℂ) * ζ ^ 14 - ((7 / 12) : ℂ) * ζ ^ 18 - ((7 / 12) : ℂ) * ζ ^ 20 + ((1 / 12) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY32_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((7 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 2 + ζ ^ 6 + ((3 / 4) : ℂ) * ζ ^ 8 + ((3 / 2) : ℂ) * ζ ^ 12 - ((7 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 - ((3 / 4) : ℂ) * ζ ^ 28 + ((5 / 4) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((((1 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 22 + ((3 / 4) : ℂ) * ζ ^ 24 - ((1 / 4) : ℂ) * ζ ^ 28 - ζ ^ 30)) * Y 0 1
      + ((-((37 / 12) : ℂ) - ((13 / 6) : ℂ) * ζ ^ 2 - ((1 / 12) : ℂ) * ζ ^ 6 + ((13 / 6) : ℂ) * ζ ^ 8 - ((7 / 6) : ℂ) * ζ ^ 12 - ((7 / 6) : ℂ) * ζ ^ 18 + ((13 / 6) : ℂ) * ζ ^ 22 - ((1 / 12) : ℂ) * ζ ^ 24 - ((13 / 6) : ℂ) * ζ ^ 28 - ((37 / 12) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((7 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 6 - ((5 / 12) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 12 + ((7 / 12) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 22 + ζ ^ 24 + ((5 / 12) : ℂ) * ζ ^ 28 + ((5 / 12) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have previous :=
    row16_reducedY32_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation02
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((2 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 - ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((1 / 6) : ℂ) - ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 4 - ((2 / 3) : ℂ) * ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 12 - ((5 / 6) : ℂ) * ζ ^ 14 + ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 18 - ((5 / 6) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 26 + ((2 / 3) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((5 / 6) : ℂ) - ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 - ((3 / 2) : ℂ) * ζ ^ 10 - ((7 / 3) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 14 + (2 : ℂ) * ζ ^ 16 + ((4 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 22 + ((8 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 26 - ((8 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((1 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 - ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 + ((5 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 - ((2 / 3) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-(1 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 4 + ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY32_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((37 / 12) : ℂ) - ((13 / 6) : ℂ) * ζ ^ 2 - ((1 / 12) : ℂ) * ζ ^ 6 + ((13 / 6) : ℂ) * ζ ^ 8 - ((7 / 6) : ℂ) * ζ ^ 12 - ((7 / 6) : ℂ) * ζ ^ 18 + ((13 / 6) : ℂ) * ζ ^ 22 - ((1 / 12) : ℂ) * ζ ^ 24 - ((13 / 6) : ℂ) * ζ ^ 28 - ((37 / 12) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((7 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 6 - ((5 / 12) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 12 + ((7 / 12) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 22 + ζ ^ 24 + ((5 / 12) : ℂ) * ζ ^ 28 + ((5 / 12) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((-((7 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 2 + ζ ^ 6 + ((3 / 4) : ℂ) * ζ ^ 8 + ((3 / 2) : ℂ) * ζ ^ 12 - ((7 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 - ((3 / 4) : ℂ) * ζ ^ 28 + ((5 / 4) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-(3 : ℂ) + ζ ^ 2 + ((3 / 2) : ℂ) * ζ ^ 6 + ζ ^ 8 + ((13 / 4) : ℂ) * ζ ^ 12 - ((13 / 4) : ℂ) * ζ ^ 18 - ζ ^ 22 - ((3 / 2) : ℂ) * ζ ^ 24 - ζ ^ 28 + (3 : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY32_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((13 / 3) : ℂ) + ζ ^ 2 + ((8 / 3) : ℂ) * ζ ^ 6 + ((5 / 3) : ℂ) * ζ ^ 8 + ((10 / 3) : ℂ) * ζ ^ 12 - ((13 / 3) : ℂ) * ζ ^ 18 - ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 - ((5 / 3) : ℂ) * ζ ^ 28 + (3 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((3 / 11) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 2 + ((3 / 11) : ℂ) * ζ ^ 4 + ((2 / 11) : ℂ) * ζ ^ 6 - ((15 / 22) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 10 + ((2 / 11) : ℂ) * ζ ^ 12 + ((5 / 11) : ℂ) * ζ ^ 14 + ((1 / 22) : ℂ) * ζ ^ 16 - ((3 / 11) : ℂ) * ζ ^ 18 - ((1 / 22) : ℂ) * ζ ^ 20 + ((9 / 22) : ℂ) * ζ ^ 22 + ((5 / 22) : ℂ) * ζ ^ 24 - ((9 / 22) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((7 / 11) : ℂ) - ((6 / 11) : ℂ) * ζ ^ 2 + ((7 / 11) : ℂ) * ζ ^ 4 + ((12 / 11) : ℂ) * ζ ^ 6 - ((1 / 22) : ℂ) * ζ ^ 8 - ((12 / 11) : ℂ) * ζ ^ 10 - ((3 / 44) : ℂ) * ζ ^ 12 + ((9 / 22) : ℂ) * ζ ^ 14 + ((3 / 44) : ℂ) * ζ ^ 16 - ((27 / 44) : ℂ) * ζ ^ 18 - ((15 / 44) : ℂ) * ζ ^ 20 + ((27 / 44) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((((3 / 11) : ℂ) + ((1 / 11) : ℂ) * ζ ^ 2 - ((3 / 11) : ℂ) * ζ ^ 4 - ((2 / 11) : ℂ) * ζ ^ 6 + ((15 / 22) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 10 - ((2 / 11) : ℂ) * ζ ^ 12 - ((5 / 11) : ℂ) * ζ ^ 14 - ((1 / 22) : ℂ) * ζ ^ 16 + ((3 / 11) : ℂ) * ζ ^ 18 + ((1 / 22) : ℂ) * ζ ^ 20 - ((9 / 22) : ℂ) * ζ ^ 22 - ((5 / 22) : ℂ) * ζ ^ 24 + ((9 / 22) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((1 / 22) : ℂ) - ((7 / 22) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 4 + ((7 / 11) : ℂ) * ζ ^ 6 + ((73 / 44) : ℂ) * ζ ^ 8 - ((43 / 44) : ℂ) * ζ ^ 10 - ((23 / 44) : ℂ) * ζ ^ 12 - ((8 / 11) : ℂ) * ζ ^ 14 - ((1 / 22) : ℂ) * ζ ^ 16 + ((3 / 44) : ℂ) * ζ ^ 18 - ((5 / 22) : ℂ) * ζ ^ 20 - ((9 / 22) : ℂ) * ζ ^ 22 - ((25 / 44) : ℂ) * ζ ^ 24 + ((45 / 44) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY32_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((5 / 4) : ℂ) - ((3 / 2) : ℂ) * ζ ^ 2 + ((5 / 4) : ℂ) * ζ ^ 6 + ((3 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 22 + ((5 / 4) : ℂ) * ζ ^ 24 - ((3 / 2) : ℂ) * ζ ^ 28 - ((5 / 4) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((7 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 - ζ ^ 6 - ((3 / 4) : ℂ) * ζ ^ 8 - ((3 / 2) : ℂ) * ζ ^ 12 + ((7 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 + ((3 / 4) : ℂ) * ζ ^ 28 - ((5 / 4) : ℂ) * ζ ^ 30)) * Y 1 1
      + (((1 : ℂ))) * Y 3 2
      + ((-((7 / 4) : ℂ) + ((1 / 4) : ℂ) * ζ ^ 2 + ζ ^ 6 + ((3 / 4) : ℂ) * ζ ^ 8 + ((3 / 2) : ℂ) * ζ ^ 12 - ((7 / 4) : ℂ) * ζ ^ 18 - ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 - ((3 / 4) : ℂ) * ζ ^ 28 + ((5 / 4) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-(3 : ℂ) + ζ ^ 2 + ((3 / 2) : ℂ) * ζ ^ 6 + ζ ^ 8 + ((13 / 4) : ℂ) * ζ ^ 12 - ((13 / 4) : ℂ) * ζ ^ 18 - ζ ^ 22 - ((3 / 2) : ℂ) * ζ ^ 24 - ζ ^ 28 + (3 : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY32_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation12
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) - ((4 / 3) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((5 / 6) : ℂ) + ζ ^ 2 + ((3 / 2) : ℂ) * ζ ^ 4 - ((2 / 3) : ℂ) * ζ ^ 6 - ((1 / 6) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 14 + ((4 / 3) : ℂ) * ζ ^ 16 - ((2 / 3) : ℂ) * ζ ^ 18 - ((5 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((7 / 6) : ℂ) - ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((7 / 6) : ℂ) * ζ ^ 6 - ((7 / 6) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 - ((1 / 3) : ℂ) * ζ ^ 14 - ((5 / 6) : ℂ) * ζ ^ 16 + ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 26 - (2 : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((7 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ((7 / 6) : ℂ) * ζ ^ 6 + ((7 / 6) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 14 + ((5 / 6) : ℂ) * ζ ^ 16 - ((2 / 3) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 26 + (2 : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((1 / 2) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 + ((3 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 22 - ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 + ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY32_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 3 2) = 0 := by
  have previous :=
    row16_reducedY32_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(3 : ℂ) - ((10 / 3) : ℂ) * ζ ^ 2 + (3 : ℂ) * ζ ^ 6 + ((10 / 3) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 12 - ((4 / 3) : ℂ) * ζ ^ 18 + ((10 / 3) : ℂ) * ζ ^ 22 + (3 : ℂ) * ζ ^ 24 - ((10 / 3) : ℂ) * ζ ^ 28 - (3 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((5 / 22) : ℂ) - ((4 / 11) : ℂ) * ζ ^ 2 + ((5 / 22) : ℂ) * ζ ^ 4 + ((13 / 22) : ℂ) * ζ ^ 6 - ((3 / 11) : ℂ) * ζ ^ 8 - ((23 / 22) : ℂ) * ζ ^ 10 - ((9 / 22) : ℂ) * ζ ^ 12 + ((7 / 11) : ℂ) * ζ ^ 14 + ((19 / 22) : ℂ) * ζ ^ 16 - ((1 / 22) : ℂ) * ζ ^ 18 - ((19 / 22) : ℂ) * ζ ^ 20 - ((9 / 22) : ℂ) * ζ ^ 22 + ((5 / 11) : ℂ) * ζ ^ 24 + ((9 / 22) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((25 / 22) : ℂ) - ((41 / 44) : ℂ) * ζ ^ 2 - ((25 / 22) : ℂ) * ζ ^ 4 + ((6 / 11) : ℂ) * ζ ^ 6 + ((47 / 44) : ℂ) * ζ ^ 8 - ((6 / 11) : ℂ) * ζ ^ 10 - ((57 / 44) : ℂ) * ζ ^ 12 + ((3 / 44) : ℂ) * ζ ^ 14 + ((57 / 44) : ℂ) * ζ ^ 16 + ((27 / 44) : ℂ) * ζ ^ 18 - ((15 / 22) : ℂ) * ζ ^ 20 - ((27 / 44) : ℂ) * ζ ^ 22)) * Y 1 1
        + ((-((25 / 22) : ℂ) + ((41 / 44) : ℂ) * ζ ^ 2 + ((25 / 22) : ℂ) * ζ ^ 4 - ((6 / 11) : ℂ) * ζ ^ 6 - ((47 / 44) : ℂ) * ζ ^ 8 + ((6 / 11) : ℂ) * ζ ^ 10 + ((57 / 44) : ℂ) * ζ ^ 12 - ((3 / 44) : ℂ) * ζ ^ 14 - ((57 / 44) : ℂ) * ζ ^ 16 - ((27 / 44) : ℂ) * ζ ^ 18 + ((15 / 22) : ℂ) * ζ ^ 20 + ((27 / 44) : ℂ) * ζ ^ 22)) * Y 4 4
        + ((-((105 / 44) : ℂ) + ((37 / 22) : ℂ) * ζ ^ 2 + ((105 / 44) : ℂ) * ζ ^ 4 - ((35 / 44) : ℂ) * ζ ^ 6 - ((25 / 11) : ℂ) * ζ ^ 8 + ((25 / 44) : ℂ) * ζ ^ 10 + ((105 / 44) : ℂ) * ζ ^ 12 + ((2 / 11) : ℂ) * ζ ^ 14 - ((95 / 44) : ℂ) * ζ ^ 16 - ((5 / 4) : ℂ) * ζ ^ 18 + ((41 / 44) : ℂ) * ζ ^ 20 + ((45 / 44) : ℂ) * ζ ^ 22 + ((5 / 22) : ℂ) * ζ ^ 24 + ((9 / 44) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY32
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 3 2 = 0 := by
  have reduced :=
    row16_reducedY32_combinationStep05 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row16_reducedY33_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((7 / 2) : ℂ) * ζ ^ 2 - (2 : ℂ) * ζ ^ 6 + (5 : ℂ) * ζ ^ 18 + ((7 / 2) : ℂ) * ζ ^ 22 - (7 : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-(3 : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 + ((3 / 2) : ℂ) * ζ ^ 18 + (3 : ℂ) * ζ ^ 22 - (5 : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    (((6 : ℂ) * ζ ^ 2 - (28 : ℂ) * ζ ^ 6 + (34 : ℂ) * ζ ^ 18 - (6 : ℂ) * ζ ^ 22 - (14 : ℂ) * ζ ^ 30)) * equation
      - (
        (((5 : ℂ) * ζ ^ 2 - (10 : ℂ) * ζ ^ 6 + (10 : ℂ) * ζ ^ 10 - (5 : ℂ) * ζ ^ 14 + ((7 / 2) : ℂ) * ζ ^ 18 - ((7 / 2) : ℂ) * ζ ^ 22)) * Y 0 1
        + (((3 : ℂ) * ζ ^ 2 - (5 : ℂ) * ζ ^ 6 + ((7 / 2) : ℂ) * ζ ^ 10 + (5 : ℂ) * ζ ^ 14 - ((3 / 2) : ℂ) * ζ ^ 18 - ((7 / 2) : ℂ) * ζ ^ 26)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY33_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22)) * Y 0 0
      + ((-(2 : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 6 + ((7 / 2) : ℂ) * ζ ^ 18 + (2 : ℂ) * ζ ^ 22 - (4 : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-(3 : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 + ((3 / 2) : ℂ) * ζ ^ 18 + (3 : ℂ) * ζ ^ 22 - (5 : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY33_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) * ζ ^ 2 + (4 : ℂ) * ζ ^ 18 + (2 : ℂ) * ζ ^ 22 - (4 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 6 - ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 18 + ζ ^ 26)) * Y 0 0
        + ((-((3 / 2) : ℂ) * ζ ^ 2 - ((3 / 2) : ℂ) * ζ ^ 10 - ((3 / 2) : ℂ) * ζ ^ 14 + ((3 / 2) : ℂ) * ζ ^ 18 - (3 : ℂ) * ζ ^ 22 + (3 : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 6 + ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 18 - ζ ^ 26)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY33_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((3 / 2) : ℂ) + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 - ζ ^ 18 - ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((8 / 3) : ℂ) - ((3 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 6 + ((9 / 2) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 18 + ((3 / 2) : ℂ) * ζ ^ 22 - ((8 / 3) : ℂ) * ζ ^ 24 - (3 : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-(3 : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 + ((3 / 2) : ℂ) * ζ ^ 18 + (3 : ℂ) * ζ ^ 22 - (5 : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22)) * Y 1 1
      + ((((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 3 3) = 0 := by
  have previous :=
    row16_reducedY33_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation03
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((2 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 - ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        (((1 : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 - ζ ^ 4 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 16 + ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((5 / 3) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 3) : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 6 + ((11 / 6) : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 10 - ((7 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((7 / 2) : ℂ) * ζ ^ 16 - ζ ^ 18 - (2 : ℂ) * ζ ^ 20 + ζ ^ 22 + ((4 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 - ((4 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((1 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 - ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 + ((5 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 - ((2 / 3) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-(1 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 4 + ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY33_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((8 / 3) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((9 / 2) : ℂ) * ζ ^ 12 + ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((8 / 3) : ℂ) * ζ ^ 24 - ζ ^ 30)) * Y 0 1
      + ((-(3 : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 + ((3 / 2) : ℂ) * ζ ^ 18 + (3 : ℂ) * ζ ^ 22 - (5 : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22)) * Y 1 1
      + ((((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((-((1 / 2) : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 - ((5 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ζ ^ 30)) * Y 4 4
      + ((((7 / 2) : ℂ) * ζ ^ 6 - ((11 / 2) : ℂ) * ζ ^ 18 + ((7 / 2) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY33_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) * ζ ^ 2 + ((16 / 3) : ℂ) * ζ ^ 6 - (6 : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((3 / 11) : ℂ) * ζ ^ 2 + ((5 / 11) : ℂ) * ζ ^ 6 - ((6 / 11) : ℂ) * ζ ^ 10 + ((10 / 11) : ℂ) * ζ ^ 14 - ((5 / 11) : ℂ) * ζ ^ 18 + ((4 / 11) : ℂ) * ζ ^ 22 - ((4 / 11) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((25 / 22) : ℂ) * ζ ^ 2 + ((19 / 11) : ℂ) * ζ ^ 6 - ((19 / 11) : ℂ) * ζ ^ 10 + ((15 / 22) : ℂ) * ζ ^ 14 - ((6 / 11) : ℂ) * ζ ^ 18 + ((6 / 11) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((((3 / 11) : ℂ) * ζ ^ 2 - ((5 / 11) : ℂ) * ζ ^ 6 + ((6 / 11) : ℂ) * ζ ^ 10 - ((10 / 11) : ℂ) * ζ ^ 14 + ((5 / 11) : ℂ) * ζ ^ 18 - ((4 / 11) : ℂ) * ζ ^ 22 + ((4 / 11) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((5 / 11) : ℂ) * ζ ^ 2 + ((13 / 22) : ℂ) * ζ ^ 6 - ((4 / 11) : ℂ) * ζ ^ 10 - ((35 / 22) : ℂ) * ζ ^ 14 + ((13 / 22) : ℂ) * ζ ^ 18 - ((4 / 11) : ℂ) * ζ ^ 22 + ((10 / 11) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY33_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-(3 : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 + ((3 / 2) : ℂ) * ζ ^ 18 + (3 : ℂ) * ζ ^ 22 - (5 : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22)) * Y 1 1
      + ((((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((-((1 / 2) : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 - ((5 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ζ ^ 30)) * Y 4 4
      + ((((7 / 2) : ℂ) * ζ ^ 6 - ((11 / 2) : ℂ) * ζ ^ 18 + ((7 / 2) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY33_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28 - ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-(1 : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 4 - ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 16 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((5 / 3) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 + ((5 / 3) : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 6 - ((11 / 6) : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 10 + ((7 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((7 / 2) : ℂ) * ζ ^ 16 - ζ ^ 18 + (2 : ℂ) * ζ ^ 20 + ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 + ((4 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((1 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 - ((5 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 + ((2 / 3) : ℂ) * ζ ^ 28)) * Y 6 7
        + (((1 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ζ ^ 4 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY33_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-(3 : ℂ) * ζ ^ 2 + ((3 / 2) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 + (3 : ℂ) * ζ ^ 22 - ((1 / 6) : ℂ) * ζ ^ 24 + ((5 / 6) : ℂ) * ζ ^ 28 - ((9 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((1 / 2) : ℂ) - ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 + ζ ^ 18 + ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 1
      + (((1 : ℂ))) * Y 3 3
      + ((-((1 / 2) : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 - ((5 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ζ ^ 30)) * Y 4 4
      + ((((7 / 2) : ℂ) * ζ ^ 6 - ((11 / 2) : ℂ) * ζ ^ 18 + ((7 / 2) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY33_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation13
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) - ((4 / 3) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((((1 / 2) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((1 / 2) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 16 - ((3 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 22 + ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26 - ζ ^ 28)) * Y 1 1
        + ((((7 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ((7 / 6) : ℂ) * ζ ^ 6 + ((7 / 6) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 14 + ((5 / 6) : ℂ) * ζ ^ 16 - ((2 / 3) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 26 + (2 : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((1 / 2) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 + ((3 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 22 - ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 + ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY33_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 2) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 12 - ((1 / 6) : ℂ) * ζ ^ 24 + ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 1
      + (((1 : ℂ))) * Y 3 3
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY33_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((20 / 3) : ℂ) * ζ ^ 2 + ((8 / 3) : ℂ) * ζ ^ 6 + ((10 / 3) : ℂ) * ζ ^ 18 + ((20 / 3) : ℂ) * ζ ^ 22 - ((28 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((8 / 11) : ℂ) * ζ ^ 2 + ((9 / 11) : ℂ) * ζ ^ 6 - ((19 / 11) : ℂ) * ζ ^ 10 + ((5 / 11) : ℂ) * ζ ^ 14 + ((4 / 11) : ℂ) * ζ ^ 18 - ((14 / 11) : ℂ) * ζ ^ 22 + ((14 / 11) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((19 / 22) : ℂ) * ζ ^ 2 - ((13 / 22) : ℂ) * ζ ^ 6 + ((13 / 22) : ℂ) * ζ ^ 10 - ((6 / 11) : ℂ) * ζ ^ 14 + ((21 / 11) : ℂ) * ζ ^ 18 - ((21 / 11) : ℂ) * ζ ^ 22)) * Y 1 1
        + ((((19 / 22) : ℂ) * ζ ^ 2 + ((13 / 22) : ℂ) * ζ ^ 6 - ((13 / 22) : ℂ) * ζ ^ 10 + ((6 / 11) : ℂ) * ζ ^ 14 - ((21 / 11) : ℂ) * ζ ^ 18 + ((21 / 11) : ℂ) * ζ ^ 22)) * Y 4 4
        + ((((15 / 11) : ℂ) * ζ ^ 2 + ((35 / 22) : ℂ) * ζ ^ 6 - ((45 / 22) : ℂ) * ζ ^ 10 + ((29 / 22) : ℂ) * ζ ^ 14 - ((40 / 11) : ℂ) * ζ ^ 18 + ((35 / 11) : ℂ) * ζ ^ 22 + ((7 / 11) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY33_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 3 3
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY33_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((2 : ℂ) - ((4 / 3) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 22 + ((4 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 2) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((1 / 2) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 - ((3 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 22 - ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26 + ζ ^ 28)) * Y 1 1
        + ((-((7 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((7 / 6) : ℂ) * ζ ^ 6 - ((7 / 6) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 14 - ((5 / 6) : ℂ) * ζ ^ 16 - ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 26 - (2 : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((1 / 2) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 16 + ((3 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 22 + ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 - ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY33
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 3 3 = Y 7 7 := by
  have reduced :=
    row16_reducedY33_combinationStep07 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row16_reducedY44_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((169 / 132) : ℂ) - ((13 / 11) : ℂ) * ζ ^ 2 - ((10 / 11) : ℂ) * ζ ^ 6 + ((43 / 11) : ℂ) * ζ ^ 12 + ((16 / 11) : ℂ) * ζ ^ 18 + ((13 / 11) : ℂ) * ζ ^ 22 - ((169 / 132) : ℂ) * ζ ^ 24 - ((26 / 11) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((6 / 11) : ℂ) * ζ ^ 2 + ((10 / 11) : ℂ) * ζ ^ 6 - ((347 / 132) : ℂ) * ζ ^ 8 + ((169 / 132) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 18 + ((6 / 11) : ℂ) * ζ ^ 22 - ((169 / 132) : ℂ) * ζ ^ 24 + ((347 / 132) : ℂ) * ζ ^ 28 - ((16 / 11) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((685 / 33) : ℂ) + ((12 / 11) : ℂ) * ζ ^ 2 - ((104 / 11) : ℂ) * ζ ^ 6 + ((172 / 11) : ℂ) * ζ ^ 8 + ((172 / 11) : ℂ) * ζ ^ 12 + ((116 / 11) : ℂ) * ζ ^ 18 - ((12 / 11) : ℂ) * ζ ^ 22 - ((172 / 11) : ℂ) * ζ ^ 28 - ((52 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((43 / 11) : ℂ) + ((16 / 11) : ℂ) * ζ ^ 2 + ((43 / 11) : ℂ) * ζ ^ 4 - ((32 / 11) : ℂ) * ζ ^ 6 + ((32 / 11) : ℂ) * ζ ^ 10 - ((43 / 11) : ℂ) * ζ ^ 12 - ((16 / 11) : ℂ) * ζ ^ 14 + ((43 / 11) : ℂ) * ζ ^ 16 + ((13 / 11) : ℂ) * ζ ^ 18 - ((43 / 11) : ℂ) * ζ ^ 20 - ((13 / 11) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((((6 / 11) : ℂ) * ζ ^ 2 - ((16 / 11) : ℂ) * ζ ^ 6 + ((86 / 11) : ℂ) * ζ ^ 8 + ((13 / 11) : ℂ) * ζ ^ 10 - ((43 / 11) : ℂ) * ζ ^ 12 + ((16 / 11) : ℂ) * ζ ^ 14 - ((3 / 11) : ℂ) * ζ ^ 18 - ((43 / 11) : ℂ) * ζ ^ 24 - ((13 / 11) : ℂ) * ζ ^ 26)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY44_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((5 / 44) : ℂ) + ((12 / 11) : ℂ) * ζ ^ 2 + ((6 / 11) : ℂ) * ζ ^ 6 - ((115 / 132) : ℂ) * ζ ^ 8 - ((115 / 132) : ℂ) * ζ ^ 12 + ((6 / 11) : ℂ) * ζ ^ 18 - ((12 / 11) : ℂ) * ζ ^ 22 + ((115 / 132) : ℂ) * ζ ^ 28 + ((3 / 11) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((257 / 66) : ℂ) + ((14 / 11) : ℂ) * ζ ^ 2 + ((26 / 11) : ℂ) * ζ ^ 6 + ((157 / 44) : ℂ) * ζ ^ 12 - ((2 / 11) : ℂ) * ζ ^ 18 - ((14 / 11) : ℂ) * ζ ^ 22 - ((257 / 66) : ℂ) * ζ ^ 24 + ((28 / 11) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((6 / 11) : ℂ) * ζ ^ 2 + ((10 / 11) : ℂ) * ζ ^ 6 - ((347 / 132) : ℂ) * ζ ^ 8 + ((169 / 132) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 18 + ((6 / 11) : ℂ) * ζ ^ 22 - ((169 / 132) : ℂ) * ζ ^ 24 + ((347 / 132) : ℂ) * ζ ^ 28 - ((16 / 11) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((5 / 44) : ℂ) - ((12 / 11) : ℂ) * ζ ^ 2 - ((6 / 11) : ℂ) * ζ ^ 6 + ((115 / 132) : ℂ) * ζ ^ 8 + ((115 / 132) : ℂ) * ζ ^ 12 - ((6 / 11) : ℂ) * ζ ^ 18 + ((12 / 11) : ℂ) * ζ ^ 22 - ((115 / 132) : ℂ) * ζ ^ 28 - ((3 / 11) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY44_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((5 / 11) : ℂ) - ((24 / 11) : ℂ) * ζ ^ 2 + ((12 / 11) : ℂ) * ζ ^ 6 - ((100 / 33) : ℂ) * ζ ^ 12 + ((60 / 11) : ℂ) * ζ ^ 18 + ((24 / 11) : ℂ) * ζ ^ 22 - ((5 / 11) : ℂ) * ζ ^ 24 - ((48 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((5 / 44) : ℂ) - ((12 / 11) : ℂ) * ζ ^ 2 - ((5 / 44) : ℂ) * ζ ^ 4 + ((6 / 11) : ℂ) * ζ ^ 6 + ((115 / 132) : ℂ) * ζ ^ 8 - ((12 / 11) : ℂ) * ζ ^ 10 - ((3 / 11) : ℂ) * ζ ^ 14 - ((6 / 11) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 20 + ((12 / 11) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((115 / 44) : ℂ) - ((27 / 11) : ℂ) * ζ ^ 2 - ((115 / 44) : ℂ) * ζ ^ 4 - ((9 / 11) : ℂ) * ζ ^ 6 + ((25 / 11) : ℂ) * ζ ^ 8 - ((9 / 11) : ℂ) * ζ ^ 10 + ((15 / 44) : ℂ) * ζ ^ 12 - ((27 / 11) : ℂ) * ζ ^ 14 - ((15 / 44) : ℂ) * ζ ^ 16 + ((18 / 11) : ℂ) * ζ ^ 18 + ((15 / 44) : ℂ) * ζ ^ 20 - ((36 / 11) : ℂ) * ζ ^ 22 + ((36 / 11) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((5 / 44) : ℂ) + ((12 / 11) : ℂ) * ζ ^ 2 + ((5 / 44) : ℂ) * ζ ^ 4 - ((6 / 11) : ℂ) * ζ ^ 6 - ((115 / 132) : ℂ) * ζ ^ 8 + ((12 / 11) : ℂ) * ζ ^ 10 + ((3 / 11) : ℂ) * ζ ^ 14 + ((6 / 11) : ℂ) * ζ ^ 18 - ((5 / 44) : ℂ) * ζ ^ 20 - ((12 / 11) : ℂ) * ζ ^ 26)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY44_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((17 / 12) : ℂ) + ((49 / 66) : ℂ) * ζ ^ 2 + ((4 / 33) : ℂ) * ζ ^ 6 - ((19 / 12) : ℂ) * ζ ^ 8 - ((19 / 12) : ℂ) * ζ ^ 12 + ((41 / 66) : ℂ) * ζ ^ 18 - ((49 / 66) : ℂ) * ζ ^ 22 + ((19 / 12) : ℂ) * ζ ^ 28 + ((2 / 33) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((277 / 66) : ℂ) - ((17 / 22) : ℂ) * ζ ^ 2 + ((97 / 66) : ℂ) * ζ ^ 6 + ((571 / 132) : ℂ) * ζ ^ 12 + ((199 / 66) : ℂ) * ζ ^ 18 + ((17 / 22) : ℂ) * ζ ^ 22 - ((277 / 66) : ℂ) * ζ ^ 24 - ((17 / 11) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((6 / 11) : ℂ) * ζ ^ 2 + ((10 / 11) : ℂ) * ζ ^ 6 - ((347 / 132) : ℂ) * ζ ^ 8 + ((169 / 132) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 18 + ((6 / 11) : ℂ) * ζ ^ 22 - ((169 / 132) : ℂ) * ζ ^ 24 + ((347 / 132) : ℂ) * ζ ^ 28 - ((16 / 11) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((5 / 44) : ℂ) - ((12 / 11) : ℂ) * ζ ^ 2 - ((6 / 11) : ℂ) * ζ ^ 6 + ((115 / 132) : ℂ) * ζ ^ 8 + ((115 / 132) : ℂ) * ζ ^ 12 - ((6 / 11) : ℂ) * ζ ^ 18 + ((12 / 11) : ℂ) * ζ ^ 22 - ((115 / 132) : ℂ) * ζ ^ 28 - ((3 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((101 / 66) : ℂ) + ((23 / 66) : ℂ) * ζ ^ 2 + ((14 / 33) : ℂ) * ζ ^ 6 + ((47 / 66) : ℂ) * ζ ^ 8 + ((47 / 66) : ℂ) * ζ ^ 12 - ((5 / 66) : ℂ) * ζ ^ 18 - ((23 / 66) : ℂ) * ζ ^ 22 - ((47 / 66) : ℂ) * ζ ^ 28 + ((7 / 33) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((7 / 22) : ℂ) - ((13 / 33) : ℂ) * ζ ^ 2 + ((25 / 66) : ℂ) * ζ ^ 6 + ((19 / 33) : ℂ) * ζ ^ 8 - ((2 / 33) : ℂ) * ζ ^ 12 - ((7 / 11) : ℂ) * ζ ^ 18 + ((13 / 33) : ℂ) * ζ ^ 22 + ((5 / 11) : ℂ) * ζ ^ 24 - ((19 / 33) : ℂ) * ζ ^ 28 + ((2 / 33) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have previous :=
    row16_reducedY44_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation02
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((92 / 33) : ℂ) - ((26 / 33) : ℂ) * ζ ^ 2 - ((68 / 33) : ℂ) * ζ ^ 6 + ((94 / 33) : ℂ) * ζ ^ 8 + ((94 / 33) : ℂ) * ζ ^ 12 + ((14 / 11) : ℂ) * ζ ^ 18 + ((26 / 33) : ℂ) * ζ ^ 22 - ((94 / 33) : ℂ) * ζ ^ 28 - ((34 / 33) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((3 / 22) : ℂ) + ((47 / 22) : ℂ) * ζ ^ 2 + ((35 / 66) : ℂ) * ζ ^ 4 + ((47 / 66) : ℂ) * ζ ^ 6 + ((2 / 11) : ℂ) * ζ ^ 8 - ((47 / 22) : ℂ) * ζ ^ 10 + ((47 / 33) : ℂ) * ζ ^ 14 + ((13 / 33) : ℂ) * ζ ^ 16 - ((47 / 66) : ℂ) * ζ ^ 18 - ((5 / 11) : ℂ) * ζ ^ 20 - ((47 / 66) : ℂ) * ζ ^ 22 - ((17 / 66) : ℂ) * ζ ^ 24 + ((47 / 66) : ℂ) * ζ ^ 26 + ((17 / 66) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((10 / 33) : ℂ) + ((43 / 66) : ℂ) * ζ ^ 2 - ((23 / 33) : ℂ) * ζ ^ 4 - ((5 / 11) : ℂ) * ζ ^ 6 - ((35 / 66) : ℂ) * ζ ^ 8 + ((62 / 33) : ℂ) * ζ ^ 10 - ((25 / 22) : ℂ) * ζ ^ 12 + ((47 / 66) : ℂ) * ζ ^ 14 + ((49 / 66) : ℂ) * ζ ^ 16 - ((47 / 33) : ℂ) * ζ ^ 18 + ((3 / 11) : ℂ) * ζ ^ 20 + ((94 / 33) : ℂ) * ζ ^ 22 + ((34 / 33) : ℂ) * ζ ^ 24 - ((94 / 33) : ℂ) * ζ ^ 26 - ((34 / 33) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((3 / 22) : ℂ) - ((47 / 22) : ℂ) * ζ ^ 2 - ((35 / 66) : ℂ) * ζ ^ 4 - ((47 / 66) : ℂ) * ζ ^ 6 - ((2 / 11) : ℂ) * ζ ^ 8 + ((47 / 22) : ℂ) * ζ ^ 10 - ((47 / 33) : ℂ) * ζ ^ 14 - ((13 / 33) : ℂ) * ζ ^ 16 + ((47 / 66) : ℂ) * ζ ^ 18 + ((5 / 11) : ℂ) * ζ ^ 20 + ((47 / 66) : ℂ) * ζ ^ 22 + ((17 / 66) : ℂ) * ζ ^ 24 - ((47 / 66) : ℂ) * ζ ^ 26 - ((17 / 66) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((25 / 66) : ℂ) + ((13 / 66) : ℂ) * ζ ^ 2 + ((25 / 66) : ℂ) * ζ ^ 4 - ((13 / 33) : ℂ) * ζ ^ 6 + ((43 / 66) : ℂ) * ζ ^ 8 + ((13 / 22) : ℂ) * ζ ^ 10 + ((17 / 66) : ℂ) * ζ ^ 12 - ((13 / 22) : ℂ) * ζ ^ 14 - ((32 / 33) : ℂ) * ζ ^ 16 - ((2 / 33) : ℂ) * ζ ^ 18 + ((47 / 66) : ℂ) * ζ ^ 20 + ((17 / 66) : ℂ) * ζ ^ 22 - ((47 / 66) : ℂ) * ζ ^ 24 - ((17 / 66) : ℂ) * ζ ^ 26)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY44_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((43 / 44) : ℂ) + ((4 / 11) : ℂ) * ζ ^ 2 + ((2 / 11) : ℂ) * ζ ^ 6 - ((133 / 132) : ℂ) * ζ ^ 8 - ((133 / 132) : ℂ) * ζ ^ 12 + ((2 / 11) : ℂ) * ζ ^ 18 - ((4 / 11) : ℂ) * ζ ^ 22 + ((133 / 132) : ℂ) * ζ ^ 28 + ((1 / 11) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((109 / 33) : ℂ) - ((12 / 11) : ℂ) * ζ ^ 2 - ((5 / 11) : ℂ) * ζ ^ 6 + ((279 / 44) : ℂ) * ζ ^ 12 + ((19 / 11) : ℂ) * ζ ^ 18 + ((12 / 11) : ℂ) * ζ ^ 22 - ((109 / 33) : ℂ) * ζ ^ 24 - ((24 / 11) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((6 / 11) : ℂ) * ζ ^ 2 + ((10 / 11) : ℂ) * ζ ^ 6 - ((347 / 132) : ℂ) * ζ ^ 8 + ((169 / 132) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 18 + ((6 / 11) : ℂ) * ζ ^ 22 - ((169 / 132) : ℂ) * ζ ^ 24 + ((347 / 132) : ℂ) * ζ ^ 28 - ((16 / 11) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((5 / 44) : ℂ) - ((12 / 11) : ℂ) * ζ ^ 2 - ((6 / 11) : ℂ) * ζ ^ 6 + ((115 / 132) : ℂ) * ζ ^ 8 + ((115 / 132) : ℂ) * ζ ^ 12 - ((6 / 11) : ℂ) * ζ ^ 18 + ((12 / 11) : ℂ) * ζ ^ 22 - ((115 / 132) : ℂ) * ζ ^ 28 - ((3 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((101 / 66) : ℂ) + ((23 / 66) : ℂ) * ζ ^ 2 + ((14 / 33) : ℂ) * ζ ^ 6 + ((47 / 66) : ℂ) * ζ ^ 8 + ((47 / 66) : ℂ) * ζ ^ 12 - ((5 / 66) : ℂ) * ζ ^ 18 - ((23 / 66) : ℂ) * ζ ^ 22 - ((47 / 66) : ℂ) * ζ ^ 28 + ((7 / 33) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((17 / 22) : ℂ) - ((47 / 66) : ℂ) * ζ ^ 2 - ((61 / 66) : ℂ) * ζ ^ 6 + ((5 / 33) : ℂ) * ζ ^ 8 - ((2 / 33) : ℂ) * ζ ^ 12 + ((17 / 22) : ℂ) * ζ ^ 18 + ((47 / 66) : ℂ) * ζ ^ 22 + ((5 / 33) : ℂ) * ζ ^ 24 - ((5 / 33) : ℂ) * ζ ^ 28 - ((41 / 66) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((7 / 22) : ℂ) - ((13 / 33) : ℂ) * ζ ^ 2 + ((25 / 66) : ℂ) * ζ ^ 6 + ((19 / 33) : ℂ) * ζ ^ 8 - ((2 / 33) : ℂ) * ζ ^ 12 - ((7 / 11) : ℂ) * ζ ^ 18 + ((13 / 33) : ℂ) * ζ ^ 22 + ((5 / 11) : ℂ) * ζ ^ 24 - ((19 / 33) : ℂ) * ζ ^ 28 + ((2 / 33) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((29 / 66) : ℂ) + ((25 / 66) : ℂ) * ζ ^ 2 - ((2 / 33) : ℂ) * ζ ^ 6 - ((19 / 33) : ℂ) * ζ ^ 8 - ((19 / 33) : ℂ) * ζ ^ 12 + ((29 / 66) : ℂ) * ζ ^ 18 - ((25 / 66) : ℂ) * ζ ^ 22 + ((19 / 33) : ℂ) * ζ ^ 28 - ((1 / 33) : ℂ) * ζ ^ 30)) * Y 3 3) = 0 := by
  have previous :=
    row16_reducedY44_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation03
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((4 / 33) : ℂ) + ((68 / 33) : ℂ) * ζ ^ 2 + ((68 / 33) : ℂ) * ζ ^ 6 - ((24 / 11) : ℂ) * ζ ^ 8 - ((24 / 11) : ℂ) * ζ ^ 12 + ((4 / 33) : ℂ) * ζ ^ 18 - ((68 / 33) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 + ((24 / 11) : ℂ) * ζ ^ 28 + ((6 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((9 / 22) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 2 - ((9 / 22) : ℂ) * ζ ^ 4 - ((9 / 22) : ℂ) * ζ ^ 6 + ((61 / 66) : ℂ) * ζ ^ 8 + ((61 / 66) : ℂ) * ζ ^ 10 - ((1 / 33) : ℂ) * ζ ^ 12 - ((12 / 11) : ℂ) * ζ ^ 14 - ((17 / 33) : ℂ) * ζ ^ 16 + ((25 / 66) : ℂ) * ζ ^ 18 + ((25 / 66) : ℂ) * ζ ^ 20 + ((3 / 22) : ℂ) * ζ ^ 22 - ((6 / 11) : ℂ) * ζ ^ 24 - ((3 / 22) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((21 / 22) : ℂ) - ((47 / 66) : ℂ) * ζ ^ 2 + ((21 / 22) : ℂ) * ζ ^ 4 + ((56 / 33) : ℂ) * ζ ^ 6 + ((37 / 22) : ℂ) * ζ ^ 8 - ((56 / 33) : ℂ) * ζ ^ 10 - ((43 / 22) : ℂ) * ζ ^ 12 + ((25 / 66) : ℂ) * ζ ^ 14 + ((43 / 22) : ℂ) * ζ ^ 16 + ((7 / 6) : ℂ) * ζ ^ 18 - ((79 / 33) : ℂ) * ζ ^ 20 - ((7 / 6) : ℂ) * ζ ^ 22 - ((3 / 11) : ℂ) * ζ ^ 24 + ((12 / 11) : ℂ) * ζ ^ 26 + ((3 / 11) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((47 / 66) : ℂ) + ((119 / 66) : ℂ) * ζ ^ 2 + ((115 / 66) : ℂ) * ζ ^ 4 + ((7 / 33) : ℂ) * ζ ^ 6 - ((61 / 66) : ℂ) * ζ ^ 8 - ((43 / 33) : ℂ) * ζ ^ 10 + ((7 / 33) : ℂ) * ζ ^ 12 + ((61 / 66) : ℂ) * ζ ^ 14 + ((9 / 11) : ℂ) * ζ ^ 16 - ((47 / 66) : ℂ) * ζ ^ 18 - ((43 / 66) : ℂ) * ζ ^ 20 - ((25 / 66) : ℂ) * ζ ^ 22 - ((3 / 22) : ℂ) * ζ ^ 24 + ((6 / 11) : ℂ) * ζ ^ 26 + ((3 / 22) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((9 / 22) : ℂ) + ((3 / 22) : ℂ) * ζ ^ 2 + ((9 / 22) : ℂ) * ζ ^ 4 + ((9 / 22) : ℂ) * ζ ^ 6 - ((61 / 66) : ℂ) * ζ ^ 8 - ((61 / 66) : ℂ) * ζ ^ 10 + ((1 / 33) : ℂ) * ζ ^ 12 + ((12 / 11) : ℂ) * ζ ^ 14 + ((17 / 33) : ℂ) * ζ ^ 16 - ((25 / 66) : ℂ) * ζ ^ 18 - ((25 / 66) : ℂ) * ζ ^ 20 - ((3 / 22) : ℂ) * ζ ^ 22 + ((6 / 11) : ℂ) * ζ ^ 24 + ((3 / 22) : ℂ) * ζ ^ 26)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY44_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((8 / 3) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((9 / 2) : ℂ) * ζ ^ 12 + ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((8 / 3) : ℂ) * ζ ^ 24 - ζ ^ 30)) * Y 0 1
      + ((-((6 / 11) : ℂ) * ζ ^ 2 + ((10 / 11) : ℂ) * ζ ^ 6 - ((347 / 132) : ℂ) * ζ ^ 8 + ((169 / 132) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 18 + ((6 / 11) : ℂ) * ζ ^ 22 - ((169 / 132) : ℂ) * ζ ^ 24 + ((347 / 132) : ℂ) * ζ ^ 28 - ((16 / 11) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((5 / 44) : ℂ) - ((12 / 11) : ℂ) * ζ ^ 2 - ((6 / 11) : ℂ) * ζ ^ 6 + ((115 / 132) : ℂ) * ζ ^ 8 + ((115 / 132) : ℂ) * ζ ^ 12 - ((6 / 11) : ℂ) * ζ ^ 18 + ((12 / 11) : ℂ) * ζ ^ 22 - ((115 / 132) : ℂ) * ζ ^ 28 - ((3 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((101 / 66) : ℂ) + ((23 / 66) : ℂ) * ζ ^ 2 + ((14 / 33) : ℂ) * ζ ^ 6 + ((47 / 66) : ℂ) * ζ ^ 8 + ((47 / 66) : ℂ) * ζ ^ 12 - ((5 / 66) : ℂ) * ζ ^ 18 - ((23 / 66) : ℂ) * ζ ^ 22 - ((47 / 66) : ℂ) * ζ ^ 28 + ((7 / 33) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((17 / 22) : ℂ) - ((47 / 66) : ℂ) * ζ ^ 2 - ((61 / 66) : ℂ) * ζ ^ 6 + ((5 / 33) : ℂ) * ζ ^ 8 - ((2 / 33) : ℂ) * ζ ^ 12 + ((17 / 22) : ℂ) * ζ ^ 18 + ((47 / 66) : ℂ) * ζ ^ 22 + ((5 / 33) : ℂ) * ζ ^ 24 - ((5 / 33) : ℂ) * ζ ^ 28 - ((41 / 66) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((7 / 22) : ℂ) - ((13 / 33) : ℂ) * ζ ^ 2 + ((25 / 66) : ℂ) * ζ ^ 6 + ((19 / 33) : ℂ) * ζ ^ 8 - ((2 / 33) : ℂ) * ζ ^ 12 - ((7 / 11) : ℂ) * ζ ^ 18 + ((13 / 33) : ℂ) * ζ ^ 22 + ((5 / 11) : ℂ) * ζ ^ 24 - ((19 / 33) : ℂ) * ζ ^ 28 + ((2 / 33) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((29 / 66) : ℂ) + ((25 / 66) : ℂ) * ζ ^ 2 - ((2 / 33) : ℂ) * ζ ^ 6 - ((19 / 33) : ℂ) * ζ ^ 8 - ((19 / 33) : ℂ) * ζ ^ 12 + ((29 / 66) : ℂ) * ζ ^ 18 - ((25 / 66) : ℂ) * ζ ^ 22 + ((19 / 33) : ℂ) * ζ ^ 28 - ((1 / 33) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((109 / 44) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 2 + ((13 / 11) : ℂ) * ζ ^ 6 - ((81 / 44) : ℂ) * ζ ^ 8 - ((81 / 44) : ℂ) * ζ ^ 12 - ((29 / 22) : ℂ) * ζ ^ 18 + ((3 / 22) : ℂ) * ζ ^ 22 + ((81 / 44) : ℂ) * ζ ^ 28 + ((13 / 22) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((109 / 22) : ℂ) + ((21 / 11) : ℂ) * ζ ^ 6 - ((109 / 44) : ℂ) * ζ ^ 8 - ((95 / 22) : ℂ) * ζ ^ 12 - ((61 / 22) : ℂ) * ζ ^ 18 + ((7 / 11) : ℂ) * ζ ^ 24 + ((109 / 44) : ℂ) * ζ ^ 28 + ((21 / 11) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY44_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((5 : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + (4 : ℂ) * ζ ^ 6 - ((17 / 3) : ℂ) * ζ ^ 8 - ((17 / 3) : ℂ) * ζ ^ 12 - ((10 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 22 + ((17 / 3) : ℂ) * ζ ^ 28 + (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((((17 / 22) : ℂ) - ((4 / 11) : ℂ) * ζ ^ 2 - ((17 / 22) : ℂ) * ζ ^ 4 + ((2 / 11) : ℂ) * ζ ^ 6 + ((17 / 11) : ℂ) * ζ ^ 8 - ((1 / 11) : ℂ) * ζ ^ 10 + ((4 / 11) : ℂ) * ζ ^ 14 - ((17 / 22) : ℂ) * ζ ^ 16 - ((2 / 11) : ℂ) * ζ ^ 18 + ((17 / 22) : ℂ) * ζ ^ 20 + ((3 / 11) : ℂ) * ζ ^ 22 - ((17 / 22) : ℂ) * ζ ^ 24 - ((3 / 11) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((17 / 44) : ℂ) - ((5 / 11) : ℂ) * ζ ^ 2 - ((17 / 44) : ℂ) * ζ ^ 4 + ((9 / 11) : ℂ) * ζ ^ 6 - ((17 / 22) : ℂ) * ζ ^ 8 - ((9 / 11) : ℂ) * ζ ^ 10 + ((51 / 44) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 14 - ((51 / 44) : ℂ) * ζ ^ 16 - ((9 / 22) : ℂ) * ζ ^ 18 + ((51 / 44) : ℂ) * ζ ^ 20 + ((9 / 22) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((-((17 / 22) : ℂ) + ((4 / 11) : ℂ) * ζ ^ 2 + ((17 / 22) : ℂ) * ζ ^ 4 - ((2 / 11) : ℂ) * ζ ^ 6 - ((17 / 11) : ℂ) * ζ ^ 8 + ((1 / 11) : ℂ) * ζ ^ 10 - ((4 / 11) : ℂ) * ζ ^ 14 + ((17 / 22) : ℂ) * ζ ^ 16 + ((2 / 11) : ℂ) * ζ ^ 18 - ((17 / 22) : ℂ) * ζ ^ 20 - ((3 / 11) : ℂ) * ζ ^ 22 + ((17 / 22) : ℂ) * ζ ^ 24 + ((3 / 11) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((17 / 11) : ℂ) + ((5 / 11) : ℂ) * ζ ^ 2 + ((17 / 11) : ℂ) * ζ ^ 4 + ((4 / 11) : ℂ) * ζ ^ 6 - ((51 / 11) : ℂ) * ζ ^ 8 - ((13 / 22) : ℂ) * ζ ^ 10 + ((51 / 44) : ℂ) * ζ ^ 12 - ((7 / 11) : ℂ) * ζ ^ 14 + ((17 / 22) : ℂ) * ζ ^ 16 + ((1 / 22) : ℂ) * ζ ^ 18 - ((17 / 22) : ℂ) * ζ ^ 20 - ((3 / 11) : ℂ) * ζ ^ 22 + ((85 / 44) : ℂ) * ζ ^ 24 + ((15 / 22) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY44_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((6 / 11) : ℂ) * ζ ^ 2 + ((10 / 11) : ℂ) * ζ ^ 6 - ((347 / 132) : ℂ) * ζ ^ 8 + ((169 / 132) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 18 + ((6 / 11) : ℂ) * ζ ^ 22 - ((169 / 132) : ℂ) * ζ ^ 24 + ((347 / 132) : ℂ) * ζ ^ 28 - ((16 / 11) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((5 / 44) : ℂ) - ((12 / 11) : ℂ) * ζ ^ 2 - ((6 / 11) : ℂ) * ζ ^ 6 + ((115 / 132) : ℂ) * ζ ^ 8 + ((115 / 132) : ℂ) * ζ ^ 12 - ((6 / 11) : ℂ) * ζ ^ 18 + ((12 / 11) : ℂ) * ζ ^ 22 - ((115 / 132) : ℂ) * ζ ^ 28 - ((3 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((101 / 66) : ℂ) + ((23 / 66) : ℂ) * ζ ^ 2 + ((14 / 33) : ℂ) * ζ ^ 6 + ((47 / 66) : ℂ) * ζ ^ 8 + ((47 / 66) : ℂ) * ζ ^ 12 - ((5 / 66) : ℂ) * ζ ^ 18 - ((23 / 66) : ℂ) * ζ ^ 22 - ((47 / 66) : ℂ) * ζ ^ 28 + ((7 / 33) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((17 / 22) : ℂ) - ((47 / 66) : ℂ) * ζ ^ 2 - ((61 / 66) : ℂ) * ζ ^ 6 + ((5 / 33) : ℂ) * ζ ^ 8 - ((2 / 33) : ℂ) * ζ ^ 12 + ((17 / 22) : ℂ) * ζ ^ 18 + ((47 / 66) : ℂ) * ζ ^ 22 + ((5 / 33) : ℂ) * ζ ^ 24 - ((5 / 33) : ℂ) * ζ ^ 28 - ((41 / 66) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((7 / 22) : ℂ) - ((13 / 33) : ℂ) * ζ ^ 2 + ((25 / 66) : ℂ) * ζ ^ 6 + ((19 / 33) : ℂ) * ζ ^ 8 - ((2 / 33) : ℂ) * ζ ^ 12 - ((7 / 11) : ℂ) * ζ ^ 18 + ((13 / 33) : ℂ) * ζ ^ 22 + ((5 / 11) : ℂ) * ζ ^ 24 - ((19 / 33) : ℂ) * ζ ^ 28 + ((2 / 33) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((29 / 66) : ℂ) + ((25 / 66) : ℂ) * ζ ^ 2 - ((2 / 33) : ℂ) * ζ ^ 6 - ((19 / 33) : ℂ) * ζ ^ 8 - ((19 / 33) : ℂ) * ζ ^ 12 + ((29 / 66) : ℂ) * ζ ^ 18 - ((25 / 66) : ℂ) * ζ ^ 22 + ((19 / 33) : ℂ) * ζ ^ 28 - ((1 / 33) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((109 / 44) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 2 + ((13 / 11) : ℂ) * ζ ^ 6 - ((81 / 44) : ℂ) * ζ ^ 8 - ((81 / 44) : ℂ) * ζ ^ 12 - ((29 / 22) : ℂ) * ζ ^ 18 + ((3 / 22) : ℂ) * ζ ^ 22 + ((81 / 44) : ℂ) * ζ ^ 28 + ((13 / 22) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((109 / 22) : ℂ) + ((21 / 11) : ℂ) * ζ ^ 6 - ((109 / 44) : ℂ) * ζ ^ 8 - ((95 / 22) : ℂ) * ζ ^ 12 - ((61 / 22) : ℂ) * ζ ^ 18 + ((7 / 11) : ℂ) * ζ ^ 24 + ((109 / 44) : ℂ) * ζ ^ 28 + ((21 / 11) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY44_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28 - ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-(1 : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 4 - ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 16 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((5 / 3) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 + ((5 / 3) : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 6 - ((11 / 6) : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 10 + ((7 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((7 / 2) : ℂ) * ζ ^ 16 - ζ ^ 18 + (2 : ℂ) * ζ ^ 20 + ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 + ((4 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((1 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 - ((5 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 + ((2 / 3) : ℂ) * ζ ^ 28)) * Y 6 7
        + (((1 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ζ ^ 4 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY44_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((2 / 3) : ℂ) * ζ ^ 2 + ((7 / 6) : ℂ) * ζ ^ 6 - ((317 / 132) : ℂ) * ζ ^ 8 + ((149 / 132) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 - ((149 / 132) : ℂ) * ζ ^ 24 + ((317 / 132) : ℂ) * ζ ^ 28 - ((11 / 6) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((139 / 132) : ℂ) - ((41 / 33) : ℂ) * ζ ^ 2 - ((4 / 33) : ℂ) * ζ ^ 6 + ((203 / 132) : ℂ) * ζ ^ 8 + ((203 / 132) : ℂ) * ζ ^ 12 - ((37 / 33) : ℂ) * ζ ^ 18 + ((41 / 33) : ℂ) * ζ ^ 22 - ((203 / 132) : ℂ) * ζ ^ 28 - ((2 / 33) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((4 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 28)) * Y 2 2
      + ((((17 / 22) : ℂ) - ((47 / 66) : ℂ) * ζ ^ 2 - ((61 / 66) : ℂ) * ζ ^ 6 + ((5 / 33) : ℂ) * ζ ^ 8 - ((2 / 33) : ℂ) * ζ ^ 12 + ((17 / 22) : ℂ) * ζ ^ 18 + ((47 / 66) : ℂ) * ζ ^ 22 + ((5 / 33) : ℂ) * ζ ^ 24 - ((5 / 33) : ℂ) * ζ ^ 28 - ((41 / 66) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((29 / 66) : ℂ) + ((25 / 66) : ℂ) * ζ ^ 2 - ((2 / 33) : ℂ) * ζ ^ 6 - ((19 / 33) : ℂ) * ζ ^ 8 - ((19 / 33) : ℂ) * ζ ^ 12 + ((29 / 66) : ℂ) * ζ ^ 18 - ((25 / 66) : ℂ) * ζ ^ 22 + ((19 / 33) : ℂ) * ζ ^ 28 - ((1 / 33) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((109 / 44) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 2 + ((13 / 11) : ℂ) * ζ ^ 6 - ((81 / 44) : ℂ) * ζ ^ 8 - ((81 / 44) : ℂ) * ζ ^ 12 - ((29 / 22) : ℂ) * ζ ^ 18 + ((3 / 22) : ℂ) * ζ ^ 22 + ((81 / 44) : ℂ) * ζ ^ 28 + ((13 / 22) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((109 / 22) : ℂ) + ((21 / 11) : ℂ) * ζ ^ 6 - ((109 / 44) : ℂ) * ζ ^ 8 - ((95 / 22) : ℂ) * ζ ^ 12 - ((61 / 22) : ℂ) * ζ ^ 18 + ((7 / 11) : ℂ) * ζ ^ 24 + ((109 / 44) : ℂ) * ζ ^ 28 + ((21 / 11) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY44_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation12
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((20 / 33) : ℂ) * ζ ^ 2 - ((4 / 33) : ℂ) * ζ ^ 6 - ((14 / 33) : ℂ) * ζ ^ 8 + ((2 / 33) : ℂ) * ζ ^ 12 - ((10 / 33) : ℂ) * ζ ^ 18 - ((20 / 33) : ℂ) * ζ ^ 22 - ((2 / 33) : ℂ) * ζ ^ 24 + ((14 / 33) : ℂ) * ζ ^ 28 + ((8 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((2 / 11) : ℂ) * ζ ^ 2 - ((10 / 33) : ℂ) * ζ ^ 4 - ((1 / 66) : ℂ) * ζ ^ 6 + ((1 / 22) : ℂ) * ζ ^ 8 + ((5 / 22) : ℂ) * ζ ^ 10 + ((3 / 22) : ℂ) * ζ ^ 12 - ((5 / 22) : ℂ) * ζ ^ 14 - ((29 / 66) : ℂ) * ζ ^ 16 + ((1 / 11) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 + ((4 / 33) : ℂ) * ζ ^ 22 + ((2 / 11) : ℂ) * ζ ^ 24 - ((7 / 66) : ℂ) * ζ ^ 26 - ((2 / 11) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((7 / 6) : ℂ) + ((5 / 33) : ℂ) * ζ ^ 2 - ((19 / 22) : ℂ) * ζ ^ 4 - ((19 / 33) : ℂ) * ζ ^ 6 + ((19 / 66) : ℂ) * ζ ^ 8 + ((4 / 11) : ℂ) * ζ ^ 10 + ((2 / 11) : ℂ) * ζ ^ 12 - ((3 / 22) : ℂ) * ζ ^ 14 + ((4 / 33) : ℂ) * ζ ^ 16 + ((3 / 11) : ℂ) * ζ ^ 18 - ((8 / 33) : ℂ) * ζ ^ 20 - ((16 / 33) : ℂ) * ζ ^ 22 - ((8 / 11) : ℂ) * ζ ^ 24 + ((14 / 33) : ℂ) * ζ ^ 26 + ((8 / 11) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((7 / 6) : ℂ) - ((5 / 33) : ℂ) * ζ ^ 2 + ((19 / 22) : ℂ) * ζ ^ 4 + ((19 / 33) : ℂ) * ζ ^ 6 - ((19 / 66) : ℂ) * ζ ^ 8 - ((4 / 11) : ℂ) * ζ ^ 10 - ((2 / 11) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 14 - ((4 / 33) : ℂ) * ζ ^ 16 - ((3 / 11) : ℂ) * ζ ^ 18 + ((8 / 33) : ℂ) * ζ ^ 20 + ((16 / 33) : ℂ) * ζ ^ 22 + ((8 / 11) : ℂ) * ζ ^ 24 - ((14 / 33) : ℂ) * ζ ^ 26 - ((8 / 11) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((7 / 22) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 2 + ((7 / 22) : ℂ) * ζ ^ 4 + ((9 / 22) : ℂ) * ζ ^ 6 - ((9 / 22) : ℂ) * ζ ^ 8 - ((9 / 22) : ℂ) * ζ ^ 10 + ((5 / 33) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 14 - ((5 / 33) : ℂ) * ζ ^ 16 - ((26 / 33) : ℂ) * ζ ^ 18 + ((17 / 66) : ℂ) * ζ ^ 20 + ((26 / 33) : ℂ) * ζ ^ 22 + ((4 / 11) : ℂ) * ζ ^ 24 - ((7 / 33) : ℂ) * ζ ^ 26 - ((4 / 11) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY44_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((5 / 11) : ℂ) * ζ ^ 2 + ((12 / 11) : ℂ) * ζ ^ 6 - ((347 / 132) : ℂ) * ζ ^ 8 + ((169 / 132) : ℂ) * ζ ^ 12 + ((5 / 22) : ℂ) * ζ ^ 18 + ((5 / 11) : ℂ) * ζ ^ 22 - ((169 / 132) : ℂ) * ζ ^ 24 + ((347 / 132) : ℂ) * ζ ^ 28 - ((17 / 11) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((27 / 44) : ℂ) - ((19 / 22) : ℂ) * ζ ^ 2 - ((2 / 11) : ℂ) * ζ ^ 6 + ((127 / 132) : ℂ) * ζ ^ 8 + ((127 / 132) : ℂ) * ζ ^ 12 - ((15 / 22) : ℂ) * ζ ^ 18 + ((19 / 22) : ℂ) * ζ ^ 22 - ((127 / 132) : ℂ) * ζ ^ 28 - ((1 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((4 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 28)) * Y 2 2
      + ((((3 / 22) : ℂ) - ((7 / 11) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 6 + ((4 / 11) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 18 + ((7 / 11) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 24 - ((4 / 11) : ℂ) * ζ ^ 28 - ((1 / 11) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((109 / 44) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 2 + ((13 / 11) : ℂ) * ζ ^ 6 - ((81 / 44) : ℂ) * ζ ^ 8 - ((81 / 44) : ℂ) * ζ ^ 12 - ((29 / 22) : ℂ) * ζ ^ 18 + ((3 / 22) : ℂ) * ζ ^ 22 + ((81 / 44) : ℂ) * ζ ^ 28 + ((13 / 22) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((109 / 22) : ℂ) + ((21 / 11) : ℂ) * ζ ^ 6 - ((109 / 44) : ℂ) * ζ ^ 8 - ((95 / 22) : ℂ) * ζ ^ 12 - ((61 / 22) : ℂ) * ζ ^ 18 + ((7 / 11) : ℂ) * ζ ^ 24 + ((109 / 44) : ℂ) * ζ ^ 28 + ((21 / 11) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY44_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation13
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((4 / 11) : ℂ) - ((20 / 33) : ℂ) * ζ ^ 2 - ((2 / 11) : ℂ) * ζ ^ 6 + ((20 / 33) : ℂ) * ζ ^ 8 + ((2 / 33) : ℂ) * ζ ^ 12 + ((2 / 33) : ℂ) * ζ ^ 18 + ((20 / 33) : ℂ) * ζ ^ 22 - ((2 / 11) : ℂ) * ζ ^ 24 - ((20 / 33) : ℂ) * ζ ^ 28 - ((4 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((1 / 11) : ℂ) - ((2 / 33) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 4 + ((1 / 11) : ℂ) * ζ ^ 6 - ((5 / 66) : ℂ) * ζ ^ 8 - ((8 / 33) : ℂ) * ζ ^ 10 - ((1 / 22) : ℂ) * ζ ^ 12 + ((19 / 66) : ℂ) * ζ ^ 14 + ((13 / 66) : ℂ) * ζ ^ 16 - ((2 / 33) : ℂ) * ζ ^ 18 - ((7 / 66) : ℂ) * ζ ^ 20 - ((1 / 11) : ℂ) * ζ ^ 22 + ((5 / 33) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((17 / 66) : ℂ) - ((5 / 66) : ℂ) * ζ ^ 2 + ((17 / 66) : ℂ) * ζ ^ 4 - ((1 / 22) : ℂ) * ζ ^ 6 - ((29 / 66) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 10 + ((9 / 22) : ℂ) * ζ ^ 12 + ((1 / 33) : ℂ) * ζ ^ 14 - ((9 / 22) : ℂ) * ζ ^ 16 - ((16 / 33) : ℂ) * ζ ^ 18 + ((19 / 33) : ℂ) * ζ ^ 20 + ((16 / 33) : ℂ) * ζ ^ 22 + ((2 / 11) : ℂ) * ζ ^ 24 - ((10 / 33) : ℂ) * ζ ^ 26 - ((2 / 11) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((7 / 11) : ℂ) + ((7 / 66) : ℂ) * ζ ^ 2 - ((1 / 3) : ℂ) * ζ ^ 4 - ((29 / 66) : ℂ) * ζ ^ 6 + ((4 / 11) : ℂ) * ζ ^ 8 + ((3 / 22) : ℂ) * ζ ^ 10 - ((5 / 33) : ℂ) * ζ ^ 12 - ((2 / 33) : ℂ) * ζ ^ 14 + ((5 / 11) : ℂ) * ζ ^ 16 + ((4 / 33) : ℂ) * ζ ^ 18 - ((14 / 33) : ℂ) * ζ ^ 20 - ((14 / 33) : ℂ) * ζ ^ 22 - ((4 / 11) : ℂ) * ζ ^ 24 + ((20 / 33) : ℂ) * ζ ^ 26 + ((4 / 11) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((((17 / 66) : ℂ) + ((5 / 66) : ℂ) * ζ ^ 2 - ((17 / 66) : ℂ) * ζ ^ 4 + ((1 / 22) : ℂ) * ζ ^ 6 + ((29 / 66) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 10 - ((9 / 22) : ℂ) * ζ ^ 12 - ((1 / 33) : ℂ) * ζ ^ 14 + ((9 / 22) : ℂ) * ζ ^ 16 + ((16 / 33) : ℂ) * ζ ^ 18 - ((19 / 33) : ℂ) * ζ ^ 20 - ((16 / 33) : ℂ) * ζ ^ 22 - ((2 / 11) : ℂ) * ζ ^ 24 + ((10 / 33) : ℂ) * ζ ^ 26 + ((2 / 11) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY44_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 2) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 12 - ((1 / 6) : ℂ) * ζ ^ 24 + ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((4 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 28)) * Y 2 2
      + ((((3 / 22) : ℂ) - ((7 / 11) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 6 + ((4 / 11) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 18 + ((7 / 11) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 24 - ((4 / 11) : ℂ) * ζ ^ 28 - ((1 / 11) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((15 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((((30 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 6 - ((15 / 11) : ℂ) * ζ ^ 8 - ((31 / 22) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((29 / 22) : ℂ) * ζ ^ 24 + ((15 / 11) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY44_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((4 / 3) : ℂ) * ζ ^ 2 + ((10 / 3) : ℂ) * ζ ^ 6 - (9 : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 18 - ((4 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 + (9 : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((10 / 11) : ℂ) * ζ ^ 2 + ((4 / 11) : ℂ) * ζ ^ 6 + ((14 / 11) : ℂ) * ζ ^ 8 - ((2 / 11) : ℂ) * ζ ^ 10 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 11) : ℂ) * ζ ^ 14 - ((13 / 11) : ℂ) * ζ ^ 16 + ((5 / 11) : ℂ) * ζ ^ 18 + ((13 / 11) : ℂ) * ζ ^ 20 - ((3 / 11) : ℂ) * ζ ^ 22 - ((27 / 22) : ℂ) * ζ ^ 24 + ((3 / 11) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((49 / 44) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 2 + ((49 / 44) : ℂ) * ζ ^ 4 - ((9 / 22) : ℂ) * ζ ^ 6 - ((51 / 44) : ℂ) * ζ ^ 8 + ((9 / 22) : ℂ) * ζ ^ 10 + ((39 / 22) : ℂ) * ζ ^ 12 - ((15 / 22) : ℂ) * ζ ^ 14 - ((39 / 22) : ℂ) * ζ ^ 16 + ((9 / 22) : ℂ) * ζ ^ 18 + ((81 / 44) : ℂ) * ζ ^ 20 - ((9 / 22) : ℂ) * ζ ^ 22)) * Y 1 1
        + ((((49 / 44) : ℂ) + ((1 / 11) : ℂ) * ζ ^ 2 - ((49 / 44) : ℂ) * ζ ^ 4 + ((9 / 22) : ℂ) * ζ ^ 6 + ((51 / 44) : ℂ) * ζ ^ 8 - ((9 / 22) : ℂ) * ζ ^ 10 - ((39 / 22) : ℂ) * ζ ^ 12 + ((15 / 22) : ℂ) * ζ ^ 14 + ((39 / 22) : ℂ) * ζ ^ 16 - ((9 / 22) : ℂ) * ζ ^ 18 - ((81 / 44) : ℂ) * ζ ^ 20 + ((9 / 22) : ℂ) * ζ ^ 22)) * Y 4 4
        + ((((49 / 22) : ℂ) - ((3 / 11) : ℂ) * ζ ^ 2 - ((49 / 22) : ℂ) * ζ ^ 4 + ζ ^ 6 + ((65 / 22) : ℂ) * ζ ^ 8 - ((10 / 11) : ℂ) * ζ ^ 10 - ((157 / 44) : ℂ) * ζ ^ 12 + ((29 / 22) : ℂ) * ζ ^ 14 + ((65 / 22) : ℂ) * ζ ^ 16 - ((13 / 22) : ℂ) * ζ ^ 18 - ((34 / 11) : ℂ) * ζ ^ 20 + ((15 / 22) : ℂ) * ζ ^ 22 - ((27 / 44) : ℂ) * ζ ^ 24 + ((3 / 22) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY44_combinationStep09
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((4 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 28)) * Y 2 2
      + ((((3 / 22) : ℂ) - ((7 / 11) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 6 + ((4 / 11) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 18 + ((7 / 11) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 24 - ((4 / 11) : ℂ) * ζ ^ 28 - ((1 / 11) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((15 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((((30 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 6 - ((15 / 11) : ℂ) * ζ ^ 8 - ((31 / 22) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((29 / 22) : ℂ) * ζ ^ 24 + ((15 / 11) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY44_combinationStep08 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((2 : ℂ) - ((4 / 3) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 22 + ((4 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 2) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((1 / 2) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 - ((3 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 22 - ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26 + ζ ^ 28)) * Y 1 1
        + ((-((7 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((7 / 6) : ℂ) * ζ ^ 6 - ((7 / 6) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 14 - ((5 / 6) : ℂ) * ζ ^ 16 - ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 26 - (2 : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((1 / 2) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 16 + ((3 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 22 + ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 - ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY44_combinationStep10
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 4 4
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY44_combinationStep09 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation24
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(4 : ℂ) + (2 : ℂ) * ζ ^ 2 - (2 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 - (2 : ℂ) * ζ ^ 22 + (2 : ℂ) * ζ ^ 28)) * equation
      - (
        ((((8 / 11) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 2 - ((15 / 22) : ℂ) * ζ ^ 4 - ((9 / 22) : ℂ) * ζ ^ 6 + ((10 / 11) : ℂ) * ζ ^ 8 + ((15 / 22) : ℂ) * ζ ^ 10 - ((5 / 22) : ℂ) * ζ ^ 12 - ((9 / 11) : ℂ) * ζ ^ 14 - ((1 / 22) : ℂ) * ζ ^ 16 + ((9 / 22) : ℂ) * ζ ^ 18 + ((2 / 11) : ℂ) * ζ ^ 20 - ((3 / 22) : ℂ) * ζ ^ 22 - ((7 / 22) : ℂ) * ζ ^ 24 + ((3 / 22) : ℂ) * ζ ^ 26)) * Y 2 2
        + ((-((13 / 22) : ℂ) + ((1 / 11) : ℂ) * ζ ^ 2 + ((9 / 22) : ℂ) * ζ ^ 4 - ((1 / 22) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 + ((3 / 22) : ℂ) * ζ ^ 10 + ((9 / 22) : ℂ) * ζ ^ 12 + ((5 / 22) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16 - ((3 / 22) : ℂ) * ζ ^ 18 + ((3 / 11) : ℂ) * ζ ^ 20 + ((5 / 22) : ℂ) * ζ ^ 22 + ((1 / 11) : ℂ) * ζ ^ 24 - ((5 / 22) : ℂ) * ζ ^ 26)) * Y 2 3
        + ((-((8 / 11) : ℂ) + ((3 / 22) : ℂ) * ζ ^ 2 + ((15 / 22) : ℂ) * ζ ^ 4 + ((9 / 22) : ℂ) * ζ ^ 6 - ((10 / 11) : ℂ) * ζ ^ 8 - ((15 / 22) : ℂ) * ζ ^ 10 + ((5 / 22) : ℂ) * ζ ^ 12 + ((9 / 11) : ℂ) * ζ ^ 14 + ((1 / 22) : ℂ) * ζ ^ 16 - ((9 / 22) : ℂ) * ζ ^ 18 - ((2 / 11) : ℂ) * ζ ^ 20 + ((3 / 22) : ℂ) * ζ ^ 22 + ((7 / 22) : ℂ) * ζ ^ 24 - ((3 / 22) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((28 / 11) : ℂ) + ((1 / 11) : ℂ) * ζ ^ 2 - ((28 / 11) : ℂ) * ζ ^ 4 - ((19 / 22) : ℂ) * ζ ^ 6 + ((20 / 11) : ℂ) * ζ ^ 8 + ((9 / 11) : ℂ) * ζ ^ 10 - ((23 / 22) : ℂ) * ζ ^ 12 - ((27 / 22) : ℂ) * ζ ^ 14 + ((12 / 11) : ℂ) * ζ ^ 16 + ((13 / 22) : ℂ) * ζ ^ 18 - ((5 / 11) : ℂ) * ζ ^ 20 - ((7 / 11) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 24 + ((7 / 11) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY44
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 4 4 = Y 7 7 := by
  have reduced :=
    row16_reducedY44_combinationStep10 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row16_reducedY45_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((5 / 44) : ℂ) - ((8 / 11) : ℂ) * ζ ^ 2 - ((6 / 11) : ℂ) * ζ ^ 8 + ((17 / 22) : ℂ) * ζ ^ 12 + ((8 / 11) : ℂ) * ζ ^ 18 + ((8 / 11) : ℂ) * ζ ^ 22 - ((5 / 22) : ℂ) * ζ ^ 24 + ((6 / 11) : ℂ) * ζ ^ 28 - ((9 / 11) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((5 / 44) : ℂ) - ((8 / 11) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 6 - ((29 / 44) : ℂ) * ζ ^ 8 + ((5 / 44) : ℂ) * ζ ^ 12 + ((8 / 11) : ℂ) * ζ ^ 22 - ((29 / 44) : ℂ) * ζ ^ 24 + ((29 / 44) : ℂ) * ζ ^ 28 - ((8 / 11) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((68 / 11) : ℂ) - ((36 / 11) : ℂ) * ζ ^ 6 + ((34 / 11) : ℂ) * ζ ^ 8 + ((63 / 11) : ℂ) * ζ ^ 12 + ((68 / 11) : ℂ) * ζ ^ 18 - ((5 / 11) : ℂ) * ζ ^ 24 - ((34 / 11) : ℂ) * ζ ^ 28 - ((36 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((63 / 44) : ℂ) + ((8 / 11) : ℂ) * ζ ^ 2 + ((63 / 44) : ℂ) * ζ ^ 4 - ((17 / 11) : ℂ) * ζ ^ 6 - ((5 / 44) : ℂ) * ζ ^ 8 + ((17 / 11) : ℂ) * ζ ^ 10 - ((29 / 44) : ℂ) * ζ ^ 12 - ((9 / 11) : ℂ) * ζ ^ 14 + ((29 / 44) : ℂ) * ζ ^ 16 + ((9 / 11) : ℂ) * ζ ^ 18 - ((17 / 22) : ℂ) * ζ ^ 20 - ((9 / 11) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((-((5 / 44) : ℂ) + ((8 / 11) : ℂ) * ζ ^ 2 + ((5 / 44) : ℂ) * ζ ^ 4 - ((9 / 11) : ℂ) * ζ ^ 6 + ((23 / 11) : ℂ) * ζ ^ 8 + ((9 / 11) : ℂ) * ζ ^ 10 - ((17 / 22) : ℂ) * ζ ^ 12 + ((8 / 11) : ℂ) * ζ ^ 14 - ((5 / 44) : ℂ) * ζ ^ 20 - ((17 / 22) : ℂ) * ζ ^ 24 - ((9 / 11) : ℂ) * ζ ^ 26)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY45_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((17 / 22) : ℂ) + ((8 / 11) : ℂ) * ζ ^ 6 - ((17 / 44) : ℂ) * ζ ^ 8 - ((37 / 44) : ℂ) * ζ ^ 12 - ((9 / 11) : ℂ) * ζ ^ 18 - ((3 / 44) : ℂ) * ζ ^ 24 + ((17 / 44) : ℂ) * ζ ^ 28 + ((8 / 11) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((65 / 44) : ℂ) - ((32 / 11) : ℂ) * ζ ^ 2 - ((15 / 44) : ℂ) * ζ ^ 8 + ((145 / 44) : ℂ) * ζ ^ 12 + ((32 / 11) : ℂ) * ζ ^ 18 + ((32 / 11) : ℂ) * ζ ^ 22 - ((65 / 22) : ℂ) * ζ ^ 24 + ((15 / 44) : ℂ) * ζ ^ 28 - ((36 / 11) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((5 / 44) : ℂ) - ((8 / 11) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 6 - ((29 / 44) : ℂ) * ζ ^ 8 + ((5 / 44) : ℂ) * ζ ^ 12 + ((8 / 11) : ℂ) * ζ ^ 22 - ((29 / 44) : ℂ) * ζ ^ 24 + ((29 / 44) : ℂ) * ζ ^ 28 - ((8 / 11) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((17 / 22) : ℂ) - ((8 / 11) : ℂ) * ζ ^ 6 + ((17 / 44) : ℂ) * ζ ^ 8 + ((37 / 44) : ℂ) * ζ ^ 12 + ((9 / 11) : ℂ) * ζ ^ 18 + ((3 / 44) : ℂ) * ζ ^ 24 - ((17 / 44) : ℂ) * ζ ^ 28 - ((8 / 11) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY45_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((17 / 11) : ℂ) + ((36 / 11) : ℂ) * ζ ^ 2 + ((20 / 11) : ℂ) * ζ ^ 8 - ((54 / 11) : ℂ) * ζ ^ 12 - ((36 / 11) : ℂ) * ζ ^ 18 - ((36 / 11) : ℂ) * ζ ^ 22 + ((34 / 11) : ℂ) * ζ ^ 24 - ((20 / 11) : ℂ) * ζ ^ 28 + ((68 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((17 / 22) : ℂ) + ((17 / 22) : ℂ) * ζ ^ 4 - ((8 / 11) : ℂ) * ζ ^ 6 + ((17 / 11) : ℂ) * ζ ^ 10 + ((5 / 11) : ℂ) * ζ ^ 12 - ((8 / 11) : ℂ) * ζ ^ 14 + ((9 / 11) : ℂ) * ζ ^ 18 - ((17 / 22) : ℂ) * ζ ^ 20 + ((5 / 11) : ℂ) * ζ ^ 24 - ((17 / 11) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((15 / 11) : ℂ) + ((24 / 11) : ℂ) * ζ ^ 2 - ((15 / 11) : ℂ) * ζ ^ 4 - ((24 / 11) : ℂ) * ζ ^ 6 + ((51 / 22) : ℂ) * ζ ^ 8 + ((51 / 11) : ℂ) * ζ ^ 10 - ((51 / 22) : ℂ) * ζ ^ 12 + ((81 / 22) : ℂ) * ζ ^ 16 - ((24 / 11) : ℂ) * ζ ^ 18 - ((81 / 22) : ℂ) * ζ ^ 20 + ((51 / 11) : ℂ) * ζ ^ 22 + ((15 / 11) : ℂ) * ζ ^ 24 - ((51 / 11) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((17 / 22) : ℂ) - ((17 / 22) : ℂ) * ζ ^ 4 + ((8 / 11) : ℂ) * ζ ^ 6 - ((17 / 11) : ℂ) * ζ ^ 10 - ((5 / 11) : ℂ) * ζ ^ 12 + ((8 / 11) : ℂ) * ζ ^ 14 - ((9 / 11) : ℂ) * ζ ^ 18 + ((17 / 22) : ℂ) * ζ ^ 20 - ((5 / 11) : ℂ) * ζ ^ 24 + ((17 / 11) : ℂ) * ζ ^ 26)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY45_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((17 / 6) : ℂ) + ((161 / 66) : ℂ) * ζ ^ 6 - ((17 / 12) : ℂ) * ζ ^ 8 - ((7 / 4) : ℂ) * ζ ^ 12 - ((149 / 33) : ℂ) * ζ ^ 18 + ((13 / 12) : ℂ) * ζ ^ 24 + ((17 / 12) : ℂ) * ζ ^ 28 + ((161 / 66) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((587 / 132) : ℂ) - ((190 / 33) : ℂ) * ζ ^ 2 - ((347 / 132) : ℂ) * ζ ^ 8 + ((507 / 44) : ℂ) * ζ ^ 12 + ((190 / 33) : ℂ) * ζ ^ 18 + ((190 / 33) : ℂ) * ζ ^ 22 - ((587 / 66) : ℂ) * ζ ^ 24 + ((347 / 132) : ℂ) * ζ ^ 28 - ((565 / 66) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((5 / 44) : ℂ) - ((8 / 11) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 6 - ((29 / 44) : ℂ) * ζ ^ 8 + ((5 / 44) : ℂ) * ζ ^ 12 + ((8 / 11) : ℂ) * ζ ^ 22 - ((29 / 44) : ℂ) * ζ ^ 24 + ((29 / 44) : ℂ) * ζ ^ 28 - ((8 / 11) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((17 / 22) : ℂ) - ((8 / 11) : ℂ) * ζ ^ 6 + ((17 / 44) : ℂ) * ζ ^ 8 + ((37 / 44) : ℂ) * ζ ^ 12 + ((9 / 11) : ℂ) * ζ ^ 18 + ((3 / 44) : ℂ) * ζ ^ 24 - ((17 / 44) : ℂ) * ζ ^ 28 - ((8 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((68 / 33) : ℂ) - ((113 / 66) : ℂ) * ζ ^ 6 + ((34 / 33) : ℂ) * ζ ^ 8 + ((10 / 11) : ℂ) * ζ ^ 12 + ((122 / 33) : ℂ) * ζ ^ 18 - ((38 / 33) : ℂ) * ζ ^ 24 - ((34 / 33) : ℂ) * ζ ^ 28 - ((113 / 66) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((21 / 11) : ℂ) + ((34 / 33) : ℂ) * ζ ^ 2 - ((29 / 33) : ℂ) * ζ ^ 6 - ((29 / 33) : ℂ) * ζ ^ 8 - ((31 / 22) : ℂ) * ζ ^ 12 - ((34 / 33) : ℂ) * ζ ^ 22 + ((29 / 33) : ℂ) * ζ ^ 24 + ((29 / 33) : ℂ) * ζ ^ 28 + ((35 / 66) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have previous :=
    row16_reducedY45_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation02
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((140 / 33) : ℂ) - ((84 / 11) : ℂ) * ζ ^ 6 + ((70 / 33) : ℂ) * ζ ^ 8 + ((62 / 11) : ℂ) * ζ ^ 12 + ((256 / 33) : ℂ) * ζ ^ 18 + ((46 / 33) : ℂ) * ζ ^ 24 - ((70 / 33) : ℂ) * ζ ^ 28 - ((84 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((2 / 33) : ℂ) + ((70 / 33) : ℂ) * ζ ^ 2 - ((2 / 33) : ℂ) * ζ ^ 4 + ((139 / 66) : ℂ) * ζ ^ 6 + ((127 / 33) : ℂ) * ζ ^ 8 - ((19 / 6) : ℂ) * ζ ^ 10 - ((62 / 33) : ℂ) * ζ ^ 12 + ((31 / 22) : ℂ) * ζ ^ 14 + ((62 / 33) : ℂ) * ζ ^ 16 - ((2 / 11) : ℂ) * ζ ^ 18 - ((21 / 11) : ℂ) * ζ ^ 20 - ((29 / 33) : ℂ) * ζ ^ 22 - ((21 / 11) : ℂ) * ζ ^ 24 + ((35 / 66) : ℂ) * ζ ^ 26 + ((21 / 11) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((98 / 33) : ℂ) + ((8 / 11) : ℂ) * ζ ^ 2 - ((98 / 33) : ℂ) * ζ ^ 4 - ((59 / 33) : ℂ) * ζ ^ 6 + ((95 / 66) : ℂ) * ζ ^ 8 + ((94 / 33) : ℂ) * ζ ^ 10 - ((29 / 3) : ℂ) * ζ ^ 12 + ((27 / 22) : ℂ) * ζ ^ 14 + ((29 / 3) : ℂ) * ζ ^ 16 - ((27 / 11) : ℂ) * ζ ^ 18 - ((42 / 11) : ℂ) * ζ ^ 20 + ((116 / 33) : ℂ) * ζ ^ 22 + ((84 / 11) : ℂ) * ζ ^ 24 - ((70 / 33) : ℂ) * ζ ^ 26 - ((84 / 11) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((2 / 33) : ℂ) - ((70 / 33) : ℂ) * ζ ^ 2 + ((2 / 33) : ℂ) * ζ ^ 4 - ((139 / 66) : ℂ) * ζ ^ 6 - ((127 / 33) : ℂ) * ζ ^ 8 + ((19 / 6) : ℂ) * ζ ^ 10 + ((62 / 33) : ℂ) * ζ ^ 12 - ((31 / 22) : ℂ) * ζ ^ 14 - ((62 / 33) : ℂ) * ζ ^ 16 + ((2 / 11) : ℂ) * ζ ^ 18 + ((21 / 11) : ℂ) * ζ ^ 20 + ((29 / 33) : ℂ) * ζ ^ 22 + ((21 / 11) : ℂ) * ζ ^ 24 - ((35 / 66) : ℂ) * ζ ^ 26 - ((21 / 11) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((98 / 33) : ℂ) - ((34 / 33) : ℂ) * ζ ^ 2 + ((98 / 33) : ℂ) * ζ ^ 4 + ((35 / 33) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 - ((35 / 33) : ℂ) * ζ ^ 10 + ((149 / 66) : ℂ) * ζ ^ 12 + ((31 / 22) : ℂ) * ζ ^ 14 - ((92 / 33) : ℂ) * ζ ^ 16 - ((21 / 11) : ℂ) * ζ ^ 18 + ((29 / 33) : ℂ) * ζ ^ 20 + ((21 / 11) : ℂ) * ζ ^ 22 - ((35 / 66) : ℂ) * ζ ^ 24 - ((21 / 11) : ℂ) * ζ ^ 26)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY45_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((65 / 22) : ℂ) + ((10 / 11) : ℂ) * ζ ^ 6 - ((65 / 44) : ℂ) * ζ ^ 8 - ((91 / 44) : ℂ) * ζ ^ 12 - ((25 / 11) : ℂ) * ζ ^ 18 + ((39 / 44) : ℂ) * ζ ^ 24 + ((65 / 44) : ℂ) * ζ ^ 28 + ((10 / 11) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((39 / 44) : ℂ) - ((15 / 11) : ℂ) * ζ ^ 2 + ((13 / 44) : ℂ) * ζ ^ 8 + ((65 / 44) : ℂ) * ζ ^ 12 + ((15 / 11) : ℂ) * ζ ^ 18 + ((15 / 11) : ℂ) * ζ ^ 22 - ((39 / 22) : ℂ) * ζ ^ 24 - ((13 / 44) : ℂ) * ζ ^ 28 - ((10 / 11) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((5 / 44) : ℂ) - ((8 / 11) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 6 - ((29 / 44) : ℂ) * ζ ^ 8 + ((5 / 44) : ℂ) * ζ ^ 12 + ((8 / 11) : ℂ) * ζ ^ 22 - ((29 / 44) : ℂ) * ζ ^ 24 + ((29 / 44) : ℂ) * ζ ^ 28 - ((8 / 11) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((17 / 22) : ℂ) - ((8 / 11) : ℂ) * ζ ^ 6 + ((17 / 44) : ℂ) * ζ ^ 8 + ((37 / 44) : ℂ) * ζ ^ 12 + ((9 / 11) : ℂ) * ζ ^ 18 + ((3 / 44) : ℂ) * ζ ^ 24 - ((17 / 44) : ℂ) * ζ ^ 28 - ((8 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((68 / 33) : ℂ) - ((113 / 66) : ℂ) * ζ ^ 6 + ((34 / 33) : ℂ) * ζ ^ 8 + ((10 / 11) : ℂ) * ζ ^ 12 + ((122 / 33) : ℂ) * ζ ^ 18 - ((38 / 33) : ℂ) * ζ ^ 24 - ((34 / 33) : ℂ) * ζ ^ 28 - ((113 / 66) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((161 / 66) : ℂ) + ((97 / 33) : ℂ) * ζ ^ 2 + ((17 / 66) : ℂ) * ζ ^ 6 + ((97 / 33) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 - ((4 / 3) : ℂ) * ζ ^ 18 - ((97 / 33) : ℂ) * ζ ^ 22 - ((17 / 66) : ℂ) * ζ ^ 24 - ((97 / 33) : ℂ) * ζ ^ 28 + ((161 / 66) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((21 / 11) : ℂ) + ((34 / 33) : ℂ) * ζ ^ 2 - ((29 / 33) : ℂ) * ζ ^ 6 - ((29 / 33) : ℂ) * ζ ^ 8 - ((31 / 22) : ℂ) * ζ ^ 12 - ((34 / 33) : ℂ) * ζ ^ 22 + ((29 / 33) : ℂ) * ζ ^ 24 + ((29 / 33) : ℂ) * ζ ^ 28 + ((35 / 66) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((-((4 / 33) : ℂ) + ((101 / 66) : ℂ) * ζ ^ 6 + ((2 / 33) : ℂ) * ζ ^ 8 + ((7 / 22) : ℂ) * ζ ^ 12 - ((74 / 33) : ℂ) * ζ ^ 18 + ((13 / 66) : ℂ) * ζ ^ 24 - ((2 / 33) : ℂ) * ζ ^ 28 + ((101 / 66) : ℂ) * ζ ^ 30)) * Y 3 3) = 0 := by
  have previous :=
    row16_reducedY45_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation03
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((56 / 11) : ℂ) + ((194 / 33) : ℂ) * ζ ^ 2 - ((86 / 33) : ℂ) * ζ ^ 6 + ((194 / 33) : ℂ) * ζ ^ 8 + ((34 / 33) : ℂ) * ζ ^ 12 - ((34 / 33) : ℂ) * ζ ^ 18 - ((194 / 33) : ℂ) * ζ ^ 22 + ((86 / 33) : ℂ) * ζ ^ 24 - ((194 / 33) : ℂ) * ζ ^ 28 + ((56 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((38 / 33) : ℂ) - ((97 / 66) : ℂ) * ζ ^ 2 - ((38 / 33) : ℂ) * ζ ^ 4 + ((157 / 66) : ℂ) * ζ ^ 6 - ((2 / 33) : ℂ) * ζ ^ 8 - ((10 / 11) : ℂ) * ζ ^ 10 + ((41 / 66) : ℂ) * ζ ^ 12 + ((17 / 66) : ℂ) * ζ ^ 14 + ((28 / 33) : ℂ) * ζ ^ 16 + ((13 / 66) : ℂ) * ζ ^ 18 - ((70 / 33) : ℂ) * ζ ^ 20 + ((14 / 11) : ℂ) * ζ ^ 22 + ((97 / 66) : ℂ) * ζ ^ 24 - ((14 / 11) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((67 / 66) : ℂ) - ((22 / 3) : ℂ) * ζ ^ 2 + ((67 / 66) : ℂ) * ζ ^ 4 + ((53 / 11) : ℂ) * ζ ^ 6 - ((163 / 66) : ℂ) * ζ ^ 8 - ((53 / 11) : ℂ) * ζ ^ 10 + ((214 / 33) : ℂ) * ζ ^ 12 + ((29 / 6) : ℂ) * ζ ^ 14 - ((214 / 33) : ℂ) * ζ ^ 16 - ((14 / 33) : ℂ) * ζ ^ 18 + ((265 / 66) : ℂ) * ζ ^ 20 + ((14 / 33) : ℂ) * ζ ^ 22 - ((28 / 11) : ℂ) * ζ ^ 24 - ((97 / 33) : ℂ) * ζ ^ 26 + ((28 / 11) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((7 / 66) : ℂ) - ((28 / 11) : ℂ) * ζ ^ 2 + ((67 / 22) : ℂ) * ζ ^ 4 - ((103 / 66) : ℂ) * ζ ^ 6 - ((31 / 22) : ℂ) * ζ ^ 8 + ((9 / 2) : ℂ) * ζ ^ 10 - ((9 / 11) : ℂ) * ζ ^ 12 - ((79 / 22) : ℂ) * ζ ^ 14 + ((124 / 33) : ℂ) * ζ ^ 16 + ((9 / 11) : ℂ) * ζ ^ 18 - ((181 / 66) : ℂ) * ζ ^ 20 + ((70 / 33) : ℂ) * ζ ^ 22 - ((14 / 11) : ℂ) * ζ ^ 24 - ((97 / 66) : ℂ) * ζ ^ 26 + ((14 / 11) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((38 / 33) : ℂ) + ((97 / 66) : ℂ) * ζ ^ 2 + ((38 / 33) : ℂ) * ζ ^ 4 - ((157 / 66) : ℂ) * ζ ^ 6 + ((2 / 33) : ℂ) * ζ ^ 8 + ((10 / 11) : ℂ) * ζ ^ 10 - ((41 / 66) : ℂ) * ζ ^ 12 - ((17 / 66) : ℂ) * ζ ^ 14 - ((28 / 33) : ℂ) * ζ ^ 16 - ((13 / 66) : ℂ) * ζ ^ 18 + ((70 / 33) : ℂ) * ζ ^ 20 - ((14 / 11) : ℂ) * ζ ^ 22 - ((97 / 66) : ℂ) * ζ ^ 24 + ((14 / 11) : ℂ) * ζ ^ 26)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY45_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((30 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 6 - ((15 / 11) : ℂ) * ζ ^ 8 - ((31 / 22) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((29 / 22) : ℂ) * ζ ^ 24 + ((15 / 11) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((29 / 22) : ℂ) - ζ ^ 2 + ((14 / 11) : ℂ) * ζ ^ 8 + ((15 / 11) : ℂ) * ζ ^ 12 + ζ ^ 18 + ζ ^ 22 - ((29 / 11) : ℂ) * ζ ^ 24 - ((14 / 11) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((5 / 44) : ℂ) - ((8 / 11) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 6 - ((29 / 44) : ℂ) * ζ ^ 8 + ((5 / 44) : ℂ) * ζ ^ 12 + ((8 / 11) : ℂ) * ζ ^ 22 - ((29 / 44) : ℂ) * ζ ^ 24 + ((29 / 44) : ℂ) * ζ ^ 28 - ((8 / 11) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((17 / 22) : ℂ) - ((8 / 11) : ℂ) * ζ ^ 6 + ((17 / 44) : ℂ) * ζ ^ 8 + ((37 / 44) : ℂ) * ζ ^ 12 + ((9 / 11) : ℂ) * ζ ^ 18 + ((3 / 44) : ℂ) * ζ ^ 24 - ((17 / 44) : ℂ) * ζ ^ 28 - ((8 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((68 / 33) : ℂ) - ((113 / 66) : ℂ) * ζ ^ 6 + ((34 / 33) : ℂ) * ζ ^ 8 + ((10 / 11) : ℂ) * ζ ^ 12 + ((122 / 33) : ℂ) * ζ ^ 18 - ((38 / 33) : ℂ) * ζ ^ 24 - ((34 / 33) : ℂ) * ζ ^ 28 - ((113 / 66) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((161 / 66) : ℂ) + ((97 / 33) : ℂ) * ζ ^ 2 + ((17 / 66) : ℂ) * ζ ^ 6 + ((97 / 33) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 - ((4 / 3) : ℂ) * ζ ^ 18 - ((97 / 33) : ℂ) * ζ ^ 22 - ((17 / 66) : ℂ) * ζ ^ 24 - ((97 / 33) : ℂ) * ζ ^ 28 + ((161 / 66) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((21 / 11) : ℂ) + ((34 / 33) : ℂ) * ζ ^ 2 - ((29 / 33) : ℂ) * ζ ^ 6 - ((29 / 33) : ℂ) * ζ ^ 8 - ((31 / 22) : ℂ) * ζ ^ 12 - ((34 / 33) : ℂ) * ζ ^ 22 + ((29 / 33) : ℂ) * ζ ^ 24 + ((29 / 33) : ℂ) * ζ ^ 28 + ((35 / 66) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((-((4 / 33) : ℂ) + ((101 / 66) : ℂ) * ζ ^ 6 + ((2 / 33) : ℂ) * ζ ^ 8 + ((7 / 22) : ℂ) * ζ ^ 12 - ((74 / 33) : ℂ) * ζ ^ 18 + ((13 / 66) : ℂ) * ζ ^ 24 - ((2 / 33) : ℂ) * ζ ^ 28 + ((101 / 66) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((5 / 22) : ℂ) + ((9 / 22) : ℂ) * ζ ^ 6 - ((5 / 44) : ℂ) * ζ ^ 8 - ((29 / 44) : ℂ) * ζ ^ 12 - ((17 / 22) : ℂ) * ζ ^ 18 - ((19 / 44) : ℂ) * ζ ^ 24 + ((5 / 44) : ℂ) * ζ ^ 28 + ((9 / 22) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((39 / 44) : ℂ) + ((4 / 11) : ℂ) * ζ ^ 2 + ((17 / 22) : ℂ) * ζ ^ 6 + ((7 / 22) : ℂ) * ζ ^ 8 - ((39 / 44) : ℂ) * ζ ^ 12 - ((17 / 11) : ℂ) * ζ ^ 18 - ((4 / 11) : ℂ) * ζ ^ 22 - ((7 / 22) : ℂ) * ζ ^ 24 - ((7 / 22) : ℂ) * ζ ^ 28 + ((13 / 11) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY45_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) + ((2 / 3) : ℂ) * ζ ^ 6 + ζ ^ 8 - ((7 / 3) : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 18 - ((13 / 3) : ℂ) * ζ ^ 24 - ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((10 / 11) : ℂ) - ((10 / 11) : ℂ) * ζ ^ 4 + ((2 / 11) : ℂ) * ζ ^ 6 + ((2 / 11) : ℂ) * ζ ^ 8 - ((2 / 11) : ℂ) * ζ ^ 10 + ((13 / 22) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 14 - ((5 / 11) : ℂ) * ζ ^ 16 - ((1 / 11) : ℂ) * ζ ^ 18 + ((5 / 11) : ℂ) * ζ ^ 20 + ((1 / 11) : ℂ) * ζ ^ 22 + ((3 / 22) : ℂ) * ζ ^ 24 - ((1 / 11) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((1 / 44) : ℂ) - ((4 / 11) : ℂ) * ζ ^ 2 - ((1 / 44) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 6 - ((3 / 4) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((15 / 22) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 14 - ((15 / 22) : ℂ) * ζ ^ 16 - ((3 / 22) : ℂ) * ζ ^ 18 - ((9 / 44) : ℂ) * ζ ^ 20 + ((3 / 22) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((-((10 / 11) : ℂ) + ((10 / 11) : ℂ) * ζ ^ 4 - ((2 / 11) : ℂ) * ζ ^ 6 - ((2 / 11) : ℂ) * ζ ^ 8 + ((2 / 11) : ℂ) * ζ ^ 10 - ((13 / 22) : ℂ) * ζ ^ 12 - ((3 / 11) : ℂ) * ζ ^ 14 + ((5 / 11) : ℂ) * ζ ^ 16 + ((1 / 11) : ℂ) * ζ ^ 18 - ((5 / 11) : ℂ) * ζ ^ 20 - ((1 / 11) : ℂ) * ζ ^ 22 - ((3 / 22) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((9 / 4) : ℂ) - ((4 / 11) : ℂ) * ζ ^ 2 + ((9 / 4) : ℂ) * ζ ^ 4 + ((1 / 22) : ℂ) * ζ ^ 6 - ((53 / 44) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 10 - ((35 / 44) : ℂ) * ζ ^ 12 - ((6 / 11) : ℂ) * ζ ^ 14 + ((5 / 11) : ℂ) * ζ ^ 16 + ((1 / 11) : ℂ) * ζ ^ 18 - ((59 / 44) : ℂ) * ζ ^ 20 - ((1 / 11) : ℂ) * ζ ^ 22 - ((15 / 44) : ℂ) * ζ ^ 24 + ((5 / 22) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY45_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((5 / 44) : ℂ) - ((8 / 11) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 6 - ((29 / 44) : ℂ) * ζ ^ 8 + ((5 / 44) : ℂ) * ζ ^ 12 + ((8 / 11) : ℂ) * ζ ^ 22 - ((29 / 44) : ℂ) * ζ ^ 24 + ((29 / 44) : ℂ) * ζ ^ 28 - ((8 / 11) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((17 / 22) : ℂ) - ((8 / 11) : ℂ) * ζ ^ 6 + ((17 / 44) : ℂ) * ζ ^ 8 + ((37 / 44) : ℂ) * ζ ^ 12 + ((9 / 11) : ℂ) * ζ ^ 18 + ((3 / 44) : ℂ) * ζ ^ 24 - ((17 / 44) : ℂ) * ζ ^ 28 - ((8 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((68 / 33) : ℂ) - ((113 / 66) : ℂ) * ζ ^ 6 + ((34 / 33) : ℂ) * ζ ^ 8 + ((10 / 11) : ℂ) * ζ ^ 12 + ((122 / 33) : ℂ) * ζ ^ 18 - ((38 / 33) : ℂ) * ζ ^ 24 - ((34 / 33) : ℂ) * ζ ^ 28 - ((113 / 66) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((161 / 66) : ℂ) + ((97 / 33) : ℂ) * ζ ^ 2 + ((17 / 66) : ℂ) * ζ ^ 6 + ((97 / 33) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 - ((4 / 3) : ℂ) * ζ ^ 18 - ((97 / 33) : ℂ) * ζ ^ 22 - ((17 / 66) : ℂ) * ζ ^ 24 - ((97 / 33) : ℂ) * ζ ^ 28 + ((161 / 66) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((21 / 11) : ℂ) + ((34 / 33) : ℂ) * ζ ^ 2 - ((29 / 33) : ℂ) * ζ ^ 6 - ((29 / 33) : ℂ) * ζ ^ 8 - ((31 / 22) : ℂ) * ζ ^ 12 - ((34 / 33) : ℂ) * ζ ^ 22 + ((29 / 33) : ℂ) * ζ ^ 24 + ((29 / 33) : ℂ) * ζ ^ 28 + ((35 / 66) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((-((4 / 33) : ℂ) + ((101 / 66) : ℂ) * ζ ^ 6 + ((2 / 33) : ℂ) * ζ ^ 8 + ((7 / 22) : ℂ) * ζ ^ 12 - ((74 / 33) : ℂ) * ζ ^ 18 + ((13 / 66) : ℂ) * ζ ^ 24 - ((2 / 33) : ℂ) * ζ ^ 28 + ((101 / 66) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((5 / 22) : ℂ) + ((9 / 22) : ℂ) * ζ ^ 6 - ((5 / 44) : ℂ) * ζ ^ 8 - ((29 / 44) : ℂ) * ζ ^ 12 - ((17 / 22) : ℂ) * ζ ^ 18 - ((19 / 44) : ℂ) * ζ ^ 24 + ((5 / 44) : ℂ) * ζ ^ 28 + ((9 / 22) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((15 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 28)) * Y 4 5
      + ((((39 / 44) : ℂ) + ((4 / 11) : ℂ) * ζ ^ 2 + ((17 / 22) : ℂ) * ζ ^ 6 + ((7 / 22) : ℂ) * ζ ^ 8 - ((39 / 44) : ℂ) * ζ ^ 12 - ((17 / 11) : ℂ) * ζ ^ 18 - ((4 / 11) : ℂ) * ζ ^ 22 - ((7 / 22) : ℂ) * ζ ^ 24 - ((7 / 22) : ℂ) * ζ ^ 28 + ((13 / 11) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((30 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 6 - ((15 / 11) : ℂ) * ζ ^ 8 - ((31 / 22) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((29 / 22) : ℂ) * ζ ^ 24 + ((15 / 11) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 5) = 0 := by
  have previous :=
    row16_reducedY45_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation05
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((16 / 3) : ℂ) - ((10 / 3) : ℂ) * ζ ^ 2 - ((8 / 3) : ℂ) * ζ ^ 6 + ((10 / 3) : ℂ) * ζ ^ 8 + ((10 / 3) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 18 + ((10 / 3) : ℂ) * ζ ^ 22 - ((10 / 3) : ℂ) * ζ ^ 28 - ((4 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((10 / 11) : ℂ) + ((25 / 11) : ℂ) * ζ ^ 2 + ((10 / 11) : ℂ) * ζ ^ 4 + ((1 / 22) : ℂ) * ζ ^ 6 - ((30 / 11) : ℂ) * ζ ^ 8 - ((13 / 11) : ℂ) * ζ ^ 10 + ((15 / 22) : ℂ) * ζ ^ 12 + ((21 / 22) : ℂ) * ζ ^ 14 + ((5 / 11) : ℂ) * ζ ^ 16 - ((21 / 22) : ℂ) * ζ ^ 18 - ((5 / 11) : ℂ) * ζ ^ 20 - ((2 / 11) : ℂ) * ζ ^ 22 + ((25 / 22) : ℂ) * ζ ^ 24 + ((5 / 11) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((5 / 22) : ℂ) - ((37 / 22) : ℂ) * ζ ^ 2 + ((5 / 22) : ℂ) * ζ ^ 4 + ((25 / 22) : ℂ) * ζ ^ 6 + ((15 / 11) : ℂ) * ζ ^ 8 - ((10 / 11) : ℂ) * ζ ^ 10 - ((15 / 11) : ℂ) * ζ ^ 12 + ((6 / 11) : ℂ) * ζ ^ 14 + ((25 / 22) : ℂ) * ζ ^ 16 + ((15 / 22) : ℂ) * ζ ^ 18 - ((25 / 22) : ℂ) * ζ ^ 20 - ((5 / 11) : ℂ) * ζ ^ 22 - ((5 / 22) : ℂ) * ζ ^ 24 - ((1 / 11) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((5 / 11) : ℂ) - ((7 / 11) : ℂ) * ζ ^ 2 - ((5 / 11) : ℂ) * ζ ^ 4 - ((3 / 11) : ℂ) * ζ ^ 6 + ((10 / 11) : ℂ) * ζ ^ 8 + ((8 / 11) : ℂ) * ζ ^ 10 - ((6 / 11) : ℂ) * ζ ^ 14 - ((5 / 11) : ℂ) * ζ ^ 16 + ((3 / 11) : ℂ) * ζ ^ 18 + ((5 / 11) : ℂ) * ζ ^ 20 + ((2 / 11) : ℂ) * ζ ^ 22 - ((5 / 11) : ℂ) * ζ ^ 24 - ((2 / 11) : ℂ) * ζ ^ 26)) * Y 4 5
        + ((((10 / 11) : ℂ) - ((25 / 11) : ℂ) * ζ ^ 2 - ((10 / 11) : ℂ) * ζ ^ 4 - ((1 / 22) : ℂ) * ζ ^ 6 + ((30 / 11) : ℂ) * ζ ^ 8 + ((13 / 11) : ℂ) * ζ ^ 10 - ((15 / 22) : ℂ) * ζ ^ 12 - ((21 / 22) : ℂ) * ζ ^ 14 - ((5 / 11) : ℂ) * ζ ^ 16 + ((21 / 22) : ℂ) * ζ ^ 18 + ((5 / 11) : ℂ) * ζ ^ 20 + ((2 / 11) : ℂ) * ζ ^ 22 - ((25 / 22) : ℂ) * ζ ^ 24 - ((5 / 11) : ℂ) * ζ ^ 26)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY45_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((17 / 132) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ((1 / 3) : ℂ) * ζ ^ 6 - ((169 / 132) : ℂ) * ζ ^ 8 + ((17 / 132) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 22 - ((169 / 132) : ℂ) * ζ ^ 24 + ((169 / 132) : ℂ) * ζ ^ 28 - ((2 / 3) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((7 / 66) : ℂ) - ((64 / 33) : ℂ) * ζ ^ 6 + ((7 / 132) : ℂ) * ζ ^ 8 + ((15 / 44) : ℂ) * ζ ^ 12 + ((199 / 66) : ℂ) * ζ ^ 18 + ((31 / 132) : ℂ) * ζ ^ 24 - ((7 / 132) : ℂ) * ζ ^ 28 - ((64 / 33) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((30 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 6 + ((15 / 11) : ℂ) * ζ ^ 8 + ((31 / 22) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((29 / 22) : ℂ) * ζ ^ 24 - ((15 / 11) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((161 / 66) : ℂ) + ((97 / 33) : ℂ) * ζ ^ 2 + ((17 / 66) : ℂ) * ζ ^ 6 + ((97 / 33) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 - ((4 / 3) : ℂ) * ζ ^ 18 - ((97 / 33) : ℂ) * ζ ^ 22 - ((17 / 66) : ℂ) * ζ ^ 24 - ((97 / 33) : ℂ) * ζ ^ 28 + ((161 / 66) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((4 / 33) : ℂ) + ((101 / 66) : ℂ) * ζ ^ 6 + ((2 / 33) : ℂ) * ζ ^ 8 + ((7 / 22) : ℂ) * ζ ^ 12 - ((74 / 33) : ℂ) * ζ ^ 18 + ((13 / 66) : ℂ) * ζ ^ 24 - ((2 / 33) : ℂ) * ζ ^ 28 + ((101 / 66) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((5 / 22) : ℂ) + ((9 / 22) : ℂ) * ζ ^ 6 - ((5 / 44) : ℂ) * ζ ^ 8 - ((29 / 44) : ℂ) * ζ ^ 12 - ((17 / 22) : ℂ) * ζ ^ 18 - ((19 / 44) : ℂ) * ζ ^ 24 + ((5 / 44) : ℂ) * ζ ^ 28 + ((9 / 22) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((15 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 28)) * Y 4 5
      + ((((39 / 44) : ℂ) + ((4 / 11) : ℂ) * ζ ^ 2 + ((17 / 22) : ℂ) * ζ ^ 6 + ((7 / 22) : ℂ) * ζ ^ 8 - ((39 / 44) : ℂ) * ζ ^ 12 - ((17 / 11) : ℂ) * ζ ^ 18 - ((4 / 11) : ℂ) * ζ ^ 22 - ((7 / 22) : ℂ) * ζ ^ 24 - ((7 / 22) : ℂ) * ζ ^ 28 + ((13 / 11) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((30 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 6 - ((15 / 11) : ℂ) * ζ ^ 8 - ((31 / 22) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((29 / 22) : ℂ) * ζ ^ 24 + ((15 / 11) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 5) = 0 := by
  have previous :=
    row16_reducedY45_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation12
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((20 / 33) : ℂ) + ((4 / 11) : ℂ) * ζ ^ 2 + ((26 / 33) : ℂ) * ζ ^ 6 + ((28 / 33) : ℂ) * ζ ^ 8 - ((20 / 33) : ℂ) * ζ ^ 12 - ((4 / 11) : ℂ) * ζ ^ 22 + ((28 / 33) : ℂ) * ζ ^ 24 - ((28 / 33) : ℂ) * ζ ^ 28 + ((4 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((19 / 66) : ℂ) + ((2 / 33) : ℂ) * ζ ^ 2 - ((31 / 66) : ℂ) * ζ ^ 4 + ((3 / 11) : ℂ) * ζ ^ 6 + ((1 / 11) : ℂ) * ζ ^ 8 - ((23 / 33) : ℂ) * ζ ^ 10 + ((1 / 11) : ℂ) * ζ ^ 12 + ((7 / 11) : ℂ) * ζ ^ 14 - ((3 / 11) : ℂ) * ζ ^ 16 + ((2 / 11) : ℂ) * ζ ^ 20 - ((14 / 33) : ℂ) * ζ ^ 22 + ((1 / 11) : ℂ) * ζ ^ 24 + ((7 / 33) : ℂ) * ζ ^ 26 - ((1 / 11) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((2 / 3) : ℂ) - ((10 / 33) : ℂ) * ζ ^ 2 + ((28 / 33) : ℂ) * ζ ^ 4 + ((15 / 11) : ℂ) * ζ ^ 6 - ((1 / 33) : ℂ) * ζ ^ 8 - ((31 / 33) : ℂ) * ζ ^ 10 - ((1 / 11) : ℂ) * ζ ^ 12 + ((7 / 11) : ℂ) * ζ ^ 14 + ((3 / 11) : ℂ) * ζ ^ 16 - ((14 / 11) : ℂ) * ζ ^ 18 - ((2 / 11) : ℂ) * ζ ^ 20 + ((56 / 33) : ℂ) * ζ ^ 22 - ((4 / 11) : ℂ) * ζ ^ 24 - ((28 / 33) : ℂ) * ζ ^ 26 + ((4 / 11) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((2 / 3) : ℂ) + ((10 / 33) : ℂ) * ζ ^ 2 - ((28 / 33) : ℂ) * ζ ^ 4 - ((15 / 11) : ℂ) * ζ ^ 6 + ((1 / 33) : ℂ) * ζ ^ 8 + ((31 / 33) : ℂ) * ζ ^ 10 + ((1 / 11) : ℂ) * ζ ^ 12 - ((7 / 11) : ℂ) * ζ ^ 14 - ((3 / 11) : ℂ) * ζ ^ 16 + ((14 / 11) : ℂ) * ζ ^ 18 + ((2 / 11) : ℂ) * ζ ^ 20 - ((56 / 33) : ℂ) * ζ ^ 22 + ((4 / 11) : ℂ) * ζ ^ 24 + ((28 / 33) : ℂ) * ζ ^ 26 - ((4 / 11) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((((53 / 33) : ℂ) + ((40 / 33) : ℂ) * ζ ^ 2 - ((53 / 33) : ℂ) * ζ ^ 4 - ((41 / 33) : ℂ) * ζ ^ 6 + ((29 / 33) : ℂ) * ζ ^ 8 + ((41 / 33) : ℂ) * ζ ^ 10 - ((14 / 11) : ℂ) * ζ ^ 12 - ((28 / 33) : ℂ) * ζ ^ 14 + ((14 / 11) : ℂ) * ζ ^ 16 + ((19 / 33) : ℂ) * ζ ^ 18 - ((7 / 11) : ℂ) * ζ ^ 20 - ((19 / 33) : ℂ) * ζ ^ 22 + ((2 / 11) : ℂ) * ζ ^ 24 + ((14 / 33) : ℂ) * ζ ^ 26 - ((2 / 11) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY45_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((5 / 44) : ℂ) - ((17 / 22) : ℂ) * ζ ^ 2 + ((9 / 22) : ℂ) * ζ ^ 6 - ((29 / 44) : ℂ) * ζ ^ 8 + ((5 / 44) : ℂ) * ζ ^ 12 + ((17 / 22) : ℂ) * ζ ^ 22 - ((29 / 44) : ℂ) * ζ ^ 24 + ((29 / 44) : ℂ) * ζ ^ 28 - ((17 / 22) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((5 / 22) : ℂ) - ((9 / 22) : ℂ) * ζ ^ 6 + ((5 / 44) : ℂ) * ζ ^ 8 + ((29 / 44) : ℂ) * ζ ^ 12 + ((17 / 22) : ℂ) * ζ ^ 18 + ((19 / 44) : ℂ) * ζ ^ 24 - ((5 / 44) : ℂ) * ζ ^ 28 - ((9 / 22) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((30 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 6 + ((15 / 11) : ℂ) * ζ ^ 8 + ((31 / 22) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((29 / 22) : ℂ) * ζ ^ 24 - ((15 / 11) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((17 / 22) : ℂ) + ((30 / 11) : ℂ) * ζ ^ 2 + ((5 / 11) : ℂ) * ζ ^ 6 + ((30 / 11) : ℂ) * ζ ^ 8 + ((4 / 11) : ℂ) * ζ ^ 12 - ((4 / 11) : ℂ) * ζ ^ 18 - ((30 / 11) : ℂ) * ζ ^ 22 - ((5 / 11) : ℂ) * ζ ^ 24 - ((30 / 11) : ℂ) * ζ ^ 28 + ((17 / 22) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((5 / 22) : ℂ) + ((9 / 22) : ℂ) * ζ ^ 6 - ((5 / 44) : ℂ) * ζ ^ 8 - ((29 / 44) : ℂ) * ζ ^ 12 - ((17 / 22) : ℂ) * ζ ^ 18 - ((19 / 44) : ℂ) * ζ ^ 24 + ((5 / 44) : ℂ) * ζ ^ 28 + ((9 / 22) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((15 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 28)) * Y 4 5
      + ((((39 / 44) : ℂ) + ((4 / 11) : ℂ) * ζ ^ 2 + ((17 / 22) : ℂ) * ζ ^ 6 + ((7 / 22) : ℂ) * ζ ^ 8 - ((39 / 44) : ℂ) * ζ ^ 12 - ((17 / 11) : ℂ) * ζ ^ 18 - ((4 / 11) : ℂ) * ζ ^ 22 - ((7 / 22) : ℂ) * ζ ^ 24 - ((7 / 22) : ℂ) * ζ ^ 28 + ((13 / 11) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((30 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 6 - ((15 / 11) : ℂ) * ζ ^ 8 - ((31 / 22) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((29 / 22) : ℂ) * ζ ^ 24 + ((15 / 11) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 5) = 0 := by
  have previous :=
    row16_reducedY45_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation13
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((70 / 33) : ℂ) - ((16 / 33) : ℂ) * ζ ^ 2 - ((6 / 11) : ℂ) * ζ ^ 6 - ((80 / 33) : ℂ) * ζ ^ 8 - ((52 / 33) : ℂ) * ζ ^ 12 + ((28 / 33) : ℂ) * ζ ^ 18 + ((16 / 33) : ℂ) * ζ ^ 22 + ((68 / 33) : ℂ) * ζ ^ 24 + ((80 / 33) : ℂ) * ζ ^ 28 + ((52 / 33) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((17 / 33) : ℂ) + ((5 / 22) : ℂ) * ζ ^ 2 + ((17 / 33) : ℂ) * ζ ^ 4 - ((10 / 33) : ℂ) * ζ ^ 6 - ((4 / 33) : ℂ) * ζ ^ 8 + ((2 / 11) : ℂ) * ζ ^ 10 - ((4 / 33) : ℂ) * ζ ^ 12 - ((23 / 33) : ℂ) * ζ ^ 14 - ((16 / 33) : ℂ) * ζ ^ 16 - ((17 / 33) : ℂ) * ζ ^ 18 + ((1 / 11) : ℂ) * ζ ^ 20 + ((13 / 33) : ℂ) * ζ ^ 22 - ((20 / 33) : ℂ) * ζ ^ 24 - ((13 / 33) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((31 / 33) : ℂ) + ((8 / 33) : ℂ) * ζ ^ 2 + ((31 / 33) : ℂ) * ζ ^ 4 + ((1 / 11) : ℂ) * ζ ^ 6 - ((5 / 33) : ℂ) * ζ ^ 8 - ((1 / 11) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 12 - ((19 / 11) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 + ((15 / 11) : ℂ) * ζ ^ 18 - ((26 / 33) : ℂ) * ζ ^ 20 - ((15 / 11) : ℂ) * ζ ^ 22 - ((26 / 33) : ℂ) * ζ ^ 24 + ((40 / 33) : ℂ) * ζ ^ 26 + ((26 / 33) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((5 / 3) : ℂ) - ((28 / 33) : ℂ) * ζ ^ 2 + ((21 / 11) : ℂ) * ζ ^ 4 + ((4 / 33) : ℂ) * ζ ^ 6 - ((43 / 33) : ℂ) * ζ ^ 8 + ((12 / 11) : ℂ) * ζ ^ 10 + ((7 / 33) : ℂ) * ζ ^ 12 - ((14 / 33) : ℂ) * ζ ^ 14 + ((1 / 33) : ℂ) * ζ ^ 16 + ((28 / 33) : ℂ) * ζ ^ 18 - ((14 / 11) : ℂ) * ζ ^ 20 + ((4 / 11) : ℂ) * ζ ^ 22 + ((52 / 33) : ℂ) * ζ ^ 24 - ((80 / 33) : ℂ) * ζ ^ 26 - ((52 / 33) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((((31 / 33) : ℂ) - ((8 / 33) : ℂ) * ζ ^ 2 - ((31 / 33) : ℂ) * ζ ^ 4 - ((1 / 11) : ℂ) * ζ ^ 6 + ((5 / 33) : ℂ) * ζ ^ 8 + ((1 / 11) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 12 + ((19 / 11) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 16 - ((15 / 11) : ℂ) * ζ ^ 18 + ((26 / 33) : ℂ) * ζ ^ 20 + ((15 / 11) : ℂ) * ζ ^ 22 + ((26 / 33) : ℂ) * ζ ^ 24 - ((40 / 33) : ℂ) * ζ ^ 26 - ((26 / 33) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY45_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((30 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 6 + ((15 / 11) : ℂ) * ζ ^ 8 + ((31 / 22) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((29 / 22) : ℂ) * ζ ^ 24 - ((15 / 11) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((17 / 22) : ℂ) + ((30 / 11) : ℂ) * ζ ^ 2 + ((5 / 11) : ℂ) * ζ ^ 6 + ((30 / 11) : ℂ) * ζ ^ 8 + ((4 / 11) : ℂ) * ζ ^ 12 - ((4 / 11) : ℂ) * ζ ^ 18 - ((30 / 11) : ℂ) * ζ ^ 22 - ((5 / 11) : ℂ) * ζ ^ 24 - ((30 / 11) : ℂ) * ζ ^ 28 + ((17 / 22) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((15 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 28)) * Y 4 5
      + ((((30 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 6 - ((15 / 11) : ℂ) * ζ ^ 8 - ((31 / 22) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((29 / 22) : ℂ) * ζ ^ 24 + ((15 / 11) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 5 5) = 0 := by
  have previous :=
    row16_reducedY45_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(1 : ℂ) - (2 : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 - ((7 / 3) : ℂ) * ζ ^ 8 - ζ ^ 12 + (2 : ℂ) * ζ ^ 22 - ((7 / 3) : ℂ) * ζ ^ 24 + ((7 / 3) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((((5 / 11) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 2 - ((5 / 11) : ℂ) * ζ ^ 4 + ((3 / 11) : ℂ) * ζ ^ 6 + ((5 / 11) : ℂ) * ζ ^ 8 - ((6 / 11) : ℂ) * ζ ^ 10 + ((7 / 22) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 14 - ((7 / 11) : ℂ) * ζ ^ 16 + ((7 / 11) : ℂ) * ζ ^ 20 - ((3 / 11) : ℂ) * ζ ^ 22 - ((7 / 22) : ℂ) * ζ ^ 24 + ((3 / 11) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((19 / 44) : ℂ) - ((9 / 22) : ℂ) * ζ ^ 2 + ((19 / 44) : ℂ) * ζ ^ 4 + ((3 / 22) : ℂ) * ζ ^ 6 - ((35 / 44) : ℂ) * ζ ^ 8 - ((3 / 22) : ℂ) * ζ ^ 10 + ((21 / 22) : ℂ) * ζ ^ 12 - ((21 / 22) : ℂ) * ζ ^ 16 + ((9 / 22) : ℂ) * ζ ^ 18 + ((21 / 44) : ℂ) * ζ ^ 20 - ((9 / 22) : ℂ) * ζ ^ 22)) * Y 1 1
        + ((((19 / 44) : ℂ) + ((9 / 22) : ℂ) * ζ ^ 2 - ((19 / 44) : ℂ) * ζ ^ 4 - ((3 / 22) : ℂ) * ζ ^ 6 + ((35 / 44) : ℂ) * ζ ^ 8 + ((3 / 22) : ℂ) * ζ ^ 10 - ((21 / 22) : ℂ) * ζ ^ 12 + ((21 / 22) : ℂ) * ζ ^ 16 - ((9 / 22) : ℂ) * ζ ^ 18 - ((21 / 44) : ℂ) * ζ ^ 20 + ((9 / 22) : ℂ) * ζ ^ 22)) * Y 4 4
        + ((((12 / 11) : ℂ) + ((17 / 22) : ℂ) * ζ ^ 2 - ((12 / 11) : ℂ) * ζ ^ 4 - ((3 / 22) : ℂ) * ζ ^ 6 + ((20 / 11) : ℂ) * ζ ^ 8 - ((7 / 4) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 14 + ((35 / 22) : ℂ) * ζ ^ 16 - ((9 / 11) : ℂ) * ζ ^ 18 - ((7 / 11) : ℂ) * ζ ^ 20 + ((15 / 22) : ℂ) * ζ ^ 22 - ((7 / 44) : ℂ) * ζ ^ 24 + ((3 / 22) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY45_combinationStep09
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 4 5) = 0 := by
  have previous :=
    row16_reducedY45_combinationStep08 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation25
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(4 : ℂ) + (2 : ℂ) * ζ ^ 2 - (2 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 - (2 : ℂ) * ζ ^ 22 + (2 : ℂ) * ζ ^ 28)) * equation
      - (
        ((-((28 / 11) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 2 + ((28 / 11) : ℂ) * ζ ^ 4 + ((19 / 22) : ℂ) * ζ ^ 6 - ((20 / 11) : ℂ) * ζ ^ 8 - ((9 / 11) : ℂ) * ζ ^ 10 + ((23 / 22) : ℂ) * ζ ^ 12 + ((27 / 22) : ℂ) * ζ ^ 14 - ((12 / 11) : ℂ) * ζ ^ 16 - ((13 / 22) : ℂ) * ζ ^ 18 + ((5 / 11) : ℂ) * ζ ^ 20 + ((7 / 11) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 24 - ((7 / 11) : ℂ) * ζ ^ 26)) * Y 2 2
        + ((((23 / 22) : ℂ) - ((7 / 11) : ℂ) * ζ ^ 2 + ((2 / 11) : ℂ) * ζ ^ 4 - ((1 / 11) : ℂ) * ζ ^ 6 + ((35 / 22) : ℂ) * ζ ^ 8 + ((1 / 11) : ℂ) * ζ ^ 10 - ((13 / 11) : ℂ) * ζ ^ 12 - ((35 / 22) : ℂ) * ζ ^ 14 + ((13 / 11) : ℂ) * ζ ^ 16 + ((10 / 11) : ℂ) * ζ ^ 18 - ((3 / 11) : ℂ) * ζ ^ 20 - ((10 / 11) : ℂ) * ζ ^ 22 - ((27 / 22) : ℂ) * ζ ^ 24 + ((10 / 11) : ℂ) * ζ ^ 26)) * Y 2 3
        + ((-((8 / 11) : ℂ) + ((3 / 22) : ℂ) * ζ ^ 2 + ((15 / 22) : ℂ) * ζ ^ 4 + ((9 / 22) : ℂ) * ζ ^ 6 - ((10 / 11) : ℂ) * ζ ^ 8 - ((15 / 22) : ℂ) * ζ ^ 10 + ((5 / 22) : ℂ) * ζ ^ 12 + ((9 / 11) : ℂ) * ζ ^ 14 + ((1 / 22) : ℂ) * ζ ^ 16 - ((9 / 22) : ℂ) * ζ ^ 18 - ((2 / 11) : ℂ) * ζ ^ 20 + ((3 / 22) : ℂ) * ζ ^ 22 + ((7 / 22) : ℂ) * ζ ^ 24 - ((3 / 22) : ℂ) * ζ ^ 26)) * Y 4 5
        + ((((28 / 11) : ℂ) + ((1 / 11) : ℂ) * ζ ^ 2 - ((28 / 11) : ℂ) * ζ ^ 4 - ((19 / 22) : ℂ) * ζ ^ 6 + ((20 / 11) : ℂ) * ζ ^ 8 + ((9 / 11) : ℂ) * ζ ^ 10 - ((23 / 22) : ℂ) * ζ ^ 12 - ((27 / 22) : ℂ) * ζ ^ 14 + ((12 / 11) : ℂ) * ζ ^ 16 + ((13 / 22) : ℂ) * ζ ^ 18 - ((5 / 11) : ℂ) * ζ ^ 20 - ((7 / 11) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 24 + ((7 / 11) : ℂ) * ζ ^ 26)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY45
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 4 5 = 0 := by
  have reduced :=
    row16_reducedY45_combinationStep09 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row16_reducedY54_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((1 / 44) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 6 - ((9 / 44) : ℂ) * ζ ^ 8 - ((2 / 11) : ℂ) * ζ ^ 12 + ((25 / 44) : ℂ) * ζ ^ 18 + ((1 / 11) : ℂ) * ζ ^ 22 + ((1 / 11) : ℂ) * ζ ^ 24 + ((9 / 44) : ℂ) * ζ ^ 28 - ((25 / 44) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((5 / 44) : ℂ) - ((21 / 44) : ℂ) * ζ ^ 2 + ((9 / 44) : ℂ) * ζ ^ 8 + ((1 / 44) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 18 + ((21 / 44) : ℂ) * ζ ^ 22 - ((5 / 22) : ℂ) * ζ ^ 24 - ((9 / 44) : ℂ) * ζ ^ 28 - ((25 / 44) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((((3 / 11) : ℂ) + ((21 / 11) : ℂ) * ζ ^ 2 - ((25 / 11) : ℂ) * ζ ^ 6 - ((8 / 11) : ℂ) * ζ ^ 8 - ((4 / 11) : ℂ) * ζ ^ 12 + ((25 / 11) : ℂ) * ζ ^ 18 - ((21 / 11) : ℂ) * ζ ^ 22 + ((5 / 11) : ℂ) * ζ ^ 24 + ((8 / 11) : ℂ) * ζ ^ 28)) * equation
      - (
        ((((1 / 11) : ℂ) + ((25 / 44) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 4 - ((23 / 22) : ℂ) * ζ ^ 6 + ((5 / 44) : ℂ) * ζ ^ 8 + ((23 / 22) : ℂ) * ζ ^ 10 + ((3 / 44) : ℂ) * ζ ^ 12 - ((21 / 44) : ℂ) * ζ ^ 14 - ((3 / 44) : ℂ) * ζ ^ 16 + ((2 / 11) : ℂ) * ζ ^ 20)) * Y 0 1
        + ((((5 / 44) : ℂ) + ((21 / 44) : ℂ) * ζ ^ 2 - ((5 / 44) : ℂ) * ζ ^ 4 - ((21 / 44) : ℂ) * ζ ^ 6 - ((7 / 44) : ℂ) * ζ ^ 8 + ((2 / 11) : ℂ) * ζ ^ 12 + ((25 / 44) : ℂ) * ζ ^ 14 - ((21 / 44) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 20 + ((2 / 11) : ℂ) * ζ ^ 24)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY54_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 11) : ℂ) - ((37 / 44) : ℂ) * ζ ^ 2 - ((3 / 11) : ℂ) * ζ ^ 6 + ((13 / 22) : ℂ) * ζ ^ 8 + ((13 / 44) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 18 + ((37 / 44) : ℂ) * ζ ^ 22 - ((15 / 22) : ℂ) * ζ ^ 24 - ((13 / 22) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((-((13 / 44) : ℂ) - ((115 / 44) : ℂ) * ζ ^ 2 - ((115 / 44) : ℂ) * ζ ^ 6 + ((81 / 44) : ℂ) * ζ ^ 8 + ((47 / 22) : ℂ) * ζ ^ 12 + ((25 / 11) : ℂ) * ζ ^ 18 + ((115 / 44) : ℂ) * ζ ^ 22 - ((47 / 44) : ℂ) * ζ ^ 24 - ((81 / 44) : ℂ) * ζ ^ 28 - ((25 / 11) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((5 / 44) : ℂ) - ((21 / 44) : ℂ) * ζ ^ 2 + ((9 / 44) : ℂ) * ζ ^ 8 + ((1 / 44) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 18 + ((21 / 44) : ℂ) * ζ ^ 22 - ((5 / 22) : ℂ) * ζ ^ 24 - ((9 / 44) : ℂ) * ζ ^ 28 - ((25 / 44) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1 / 11) : ℂ) + ((37 / 44) : ℂ) * ζ ^ 2 + ((3 / 11) : ℂ) * ζ ^ 6 - ((13 / 22) : ℂ) * ζ ^ 8 - ((13 / 44) : ℂ) * ζ ^ 12 - ((3 / 11) : ℂ) * ζ ^ 18 - ((37 / 44) : ℂ) * ζ ^ 22 + ((15 / 22) : ℂ) * ζ ^ 24 + ((13 / 22) : ℂ) * ζ ^ 28)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY54_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((21 / 11) : ℂ) - ((12 / 11) : ℂ) * ζ ^ 2 - ((12 / 11) : ℂ) * ζ ^ 6 + ((13 / 11) : ℂ) * ζ ^ 8 - ((8 / 11) : ℂ) * ζ ^ 12 - ((13 / 11) : ℂ) * ζ ^ 18 + ((12 / 11) : ℂ) * ζ ^ 22 + ((4 / 11) : ℂ) * ζ ^ 24 - ((13 / 11) : ℂ) * ζ ^ 28 + ((13 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 11) : ℂ) + ((37 / 44) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 4 - ((25 / 44) : ℂ) * ζ ^ 6 - ((9 / 44) : ℂ) * ζ ^ 8 + ((13 / 44) : ℂ) * ζ ^ 10 + ((13 / 44) : ℂ) * ζ ^ 12 - ((3 / 11) : ℂ) * ζ ^ 18 - ((1 / 11) : ℂ) * ζ ^ 20 + ((13 / 44) : ℂ) * ζ ^ 24 - ((13 / 44) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((3 / 11) : ℂ) + ((111 / 44) : ℂ) * ζ ^ 2 - ((3 / 11) : ℂ) * ζ ^ 4 - ((15 / 44) : ℂ) * ζ ^ 8 - ((9 / 11) : ℂ) * ζ ^ 10 - ((3 / 11) : ℂ) * ζ ^ 12 + ((75 / 44) : ℂ) * ζ ^ 14 + ((51 / 44) : ℂ) * ζ ^ 16 - ((75 / 44) : ℂ) * ζ ^ 18 - ((51 / 44) : ℂ) * ζ ^ 20 + ((39 / 44) : ℂ) * ζ ^ 22 + ((39 / 44) : ℂ) * ζ ^ 24 - ((39 / 44) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((1 / 11) : ℂ) - ((37 / 44) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 4 + ((25 / 44) : ℂ) * ζ ^ 6 + ((9 / 44) : ℂ) * ζ ^ 8 - ((13 / 44) : ℂ) * ζ ^ 10 - ((13 / 44) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 18 + ((1 / 11) : ℂ) * ζ ^ 20 - ((13 / 44) : ℂ) * ζ ^ 24 + ((13 / 44) : ℂ) * ζ ^ 26)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY54_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((1 / 2) : ℂ) - ((65 / 132) : ℂ) * ζ ^ 2 - ((2 / 33) : ℂ) * ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 12) : ℂ) * ζ ^ 12 + ((2 / 33) : ℂ) * ζ ^ 18 + ((65 / 132) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 - ((5 / 6) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((-((1 / 44) : ℂ) - ((227 / 132) : ℂ) * ζ ^ 2 - ((227 / 132) : ℂ) * ζ ^ 6 + ((215 / 132) : ℂ) * ζ ^ 8 + ((109 / 66) : ℂ) * ζ ^ 12 + ((5 / 22) : ℂ) * ζ ^ 18 + ((227 / 132) : ℂ) * ζ ^ 22 - ((109 / 132) : ℂ) * ζ ^ 24 - ((215 / 132) : ℂ) * ζ ^ 28 - ((5 / 22) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((5 / 44) : ℂ) - ((21 / 44) : ℂ) * ζ ^ 2 + ((9 / 44) : ℂ) * ζ ^ 8 + ((1 / 44) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 18 + ((21 / 44) : ℂ) * ζ ^ 22 - ((5 / 22) : ℂ) * ζ ^ 24 - ((9 / 44) : ℂ) * ζ ^ 28 - ((25 / 44) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1 / 11) : ℂ) + ((37 / 44) : ℂ) * ζ ^ 2 + ((3 / 11) : ℂ) * ζ ^ 6 - ((13 / 22) : ℂ) * ζ ^ 8 - ((13 / 44) : ℂ) * ζ ^ 12 - ((3 / 11) : ℂ) * ζ ^ 18 - ((37 / 44) : ℂ) * ζ ^ 22 + ((15 / 22) : ℂ) * ζ ^ 24 + ((13 / 22) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((13 / 22) : ℂ) - ((23 / 66) : ℂ) * ζ ^ 2 - ((7 / 33) : ℂ) * ζ ^ 6 - ((8 / 33) : ℂ) * ζ ^ 8 - ((4 / 33) : ℂ) * ζ ^ 12 + ((7 / 33) : ℂ) * ζ ^ 18 + ((23 / 66) : ℂ) * ζ ^ 22 - ((23 / 66) : ℂ) * ζ ^ 24 + ((8 / 33) : ℂ) * ζ ^ 28)) * Y 2 2
      + ((((5 / 66) : ℂ) + ((4 / 11) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 6 - ((4 / 11) : ℂ) * ζ ^ 8 + ((3 / 22) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 18 - ((4 / 11) : ℂ) * ζ ^ 22 - ((1 / 6) : ℂ) * ζ ^ 24 + ((4 / 11) : ℂ) * ζ ^ 28 + ((5 / 66) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have previous :=
    row16_reducedY54_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation02
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((56 / 33) : ℂ) + ((26 / 33) : ℂ) * ζ ^ 2 + ((34 / 33) : ℂ) * ζ ^ 6 - ((76 / 33) : ℂ) * ζ ^ 8 - ((38 / 33) : ℂ) * ζ ^ 12 - ((34 / 33) : ℂ) * ζ ^ 18 - ((26 / 33) : ℂ) * ζ ^ 22 + ((20 / 33) : ℂ) * ζ ^ 24 + ((76 / 33) : ℂ) * ζ ^ 28)) * equation
      - (
        ((-((17 / 66) : ℂ) - ((35 / 22) : ℂ) * ζ ^ 2 - ((3 / 22) : ℂ) * ζ ^ 4 + ((1 / 66) : ℂ) * ζ ^ 6 + ((3 / 22) : ℂ) * ζ ^ 8 + ((25 / 22) : ℂ) * ζ ^ 10 - ((5 / 11) : ℂ) * ζ ^ 12 - ζ ^ 14 + ((2 / 33) : ℂ) * ζ ^ 16 + ((8 / 11) : ℂ) * ζ ^ 18 + ((13 / 66) : ℂ) * ζ ^ 20 + ((14 / 33) : ℂ) * ζ ^ 22 - ((19 / 33) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((3 / 11) : ℂ) - ((1 / 22) : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 4 - ((14 / 33) : ℂ) * ζ ^ 6 + ((17 / 66) : ℂ) * ζ ^ 8 - ((8 / 11) : ℂ) * ζ ^ 10 + ((7 / 11) : ℂ) * ζ ^ 12 - ((3 / 11) : ℂ) * ζ ^ 14 - ((8 / 33) : ℂ) * ζ ^ 16 + ((6 / 11) : ℂ) * ζ ^ 18 - ((26 / 33) : ℂ) * ζ ^ 20 - ((56 / 33) : ℂ) * ζ ^ 22 + ((76 / 33) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((17 / 66) : ℂ) + ((35 / 22) : ℂ) * ζ ^ 2 + ((3 / 22) : ℂ) * ζ ^ 4 - ((1 / 66) : ℂ) * ζ ^ 6 - ((3 / 22) : ℂ) * ζ ^ 8 - ((25 / 22) : ℂ) * ζ ^ 10 + ((5 / 11) : ℂ) * ζ ^ 12 + ζ ^ 14 - ((2 / 33) : ℂ) * ζ ^ 16 - ((8 / 11) : ℂ) * ζ ^ 18 - ((13 / 66) : ℂ) * ζ ^ 20 - ((14 / 33) : ℂ) * ζ ^ 22 + ((19 / 33) : ℂ) * ζ ^ 26)) * Y 2 2
        + ((((23 / 66) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((23 / 66) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 6 - ((16 / 33) : ℂ) * ζ ^ 8 - ((4 / 11) : ℂ) * ζ ^ 10 + ((5 / 33) : ℂ) * ζ ^ 12 + ((17 / 33) : ℂ) * ζ ^ 14 + ((14 / 33) : ℂ) * ζ ^ 16 - ((13 / 66) : ℂ) * ζ ^ 18 - ((14 / 33) : ℂ) * ζ ^ 20 + ((19 / 33) : ℂ) * ζ ^ 24)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY54_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((2 / 11) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 6 + ((7 / 22) : ℂ) * ζ ^ 8 + ((7 / 44) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 22 - ((3 / 22) : ℂ) * ζ ^ 24 - ((7 / 22) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((((1 / 44) : ℂ) + ((9 / 44) : ℂ) * ζ ^ 2 + ((9 / 44) : ℂ) * ζ ^ 6 - ((13 / 44) : ℂ) * ζ ^ 8 - ((7 / 22) : ℂ) * ζ ^ 12 - ((1 / 11) : ℂ) * ζ ^ 18 - ((9 / 44) : ℂ) * ζ ^ 22 + ((7 / 44) : ℂ) * ζ ^ 24 + ((13 / 44) : ℂ) * ζ ^ 28 + ((1 / 11) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((5 / 44) : ℂ) - ((21 / 44) : ℂ) * ζ ^ 2 + ((9 / 44) : ℂ) * ζ ^ 8 + ((1 / 44) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 18 + ((21 / 44) : ℂ) * ζ ^ 22 - ((5 / 22) : ℂ) * ζ ^ 24 - ((9 / 44) : ℂ) * ζ ^ 28 - ((25 / 44) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1 / 11) : ℂ) + ((37 / 44) : ℂ) * ζ ^ 2 + ((3 / 11) : ℂ) * ζ ^ 6 - ((13 / 22) : ℂ) * ζ ^ 8 - ((13 / 44) : ℂ) * ζ ^ 12 - ((3 / 11) : ℂ) * ζ ^ 18 - ((37 / 44) : ℂ) * ζ ^ 22 + ((15 / 22) : ℂ) * ζ ^ 24 + ((13 / 22) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((13 / 22) : ℂ) - ((23 / 66) : ℂ) * ζ ^ 2 - ((7 / 33) : ℂ) * ζ ^ 6 - ((8 / 33) : ℂ) * ζ ^ 8 - ((4 / 33) : ℂ) * ζ ^ 12 + ((7 / 33) : ℂ) * ζ ^ 18 + ((23 / 66) : ℂ) * ζ ^ 22 - ((23 / 66) : ℂ) * ζ ^ 24 + ((8 / 33) : ℂ) * ζ ^ 28)) * Y 2 2
      + ((-((1 / 6) : ℂ) + ((29 / 66) : ℂ) * ζ ^ 2 + ((1 / 3) : ℂ) * ζ ^ 6 - ((14 / 33) : ℂ) * ζ ^ 8 - ((7 / 66) : ℂ) * ζ ^ 12 - ((20 / 33) : ℂ) * ζ ^ 18 - ((29 / 66) : ℂ) * ζ ^ 22 + ((29 / 66) : ℂ) * ζ ^ 24 + ((14 / 33) : ℂ) * ζ ^ 28 + ((1 / 66) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((5 / 66) : ℂ) + ((4 / 11) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 6 - ((4 / 11) : ℂ) * ζ ^ 8 + ((3 / 22) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 18 - ((4 / 11) : ℂ) * ζ ^ 22 - ((1 / 6) : ℂ) * ζ ^ 24 + ((4 / 11) : ℂ) * ζ ^ 28 + ((5 / 66) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((-((7 / 22) : ℂ) - ((25 / 66) : ℂ) * ζ ^ 2 + ((1 / 33) : ℂ) * ζ ^ 6 + ((17 / 33) : ℂ) * ζ ^ 8 + ((17 / 66) : ℂ) * ζ ^ 12 - ((1 / 33) : ℂ) * ζ ^ 18 + ((25 / 66) : ℂ) * ζ ^ 22 - ((13 / 66) : ℂ) * ζ ^ 24 - ((17 / 33) : ℂ) * ζ ^ 28)) * Y 3 3) = 0 := by
  have previous :=
    row16_reducedY54_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation03
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((34 / 33) : ℂ) - ((64 / 33) : ℂ) * ζ ^ 2 - ((26 / 33) : ℂ) * ζ ^ 6 + ((76 / 33) : ℂ) * ζ ^ 8 + ((38 / 33) : ℂ) * ζ ^ 12 + ((10 / 11) : ℂ) * ζ ^ 18 + ((64 / 33) : ℂ) * ζ ^ 22 - ((64 / 33) : ℂ) * ζ ^ 24 - ((76 / 33) : ℂ) * ζ ^ 28 + ((4 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((2 / 33) : ℂ) + ((7 / 66) : ℂ) * ζ ^ 2 + ((2 / 33) : ℂ) * ζ ^ 4 - ((3 / 22) : ℂ) * ζ ^ 6 - ((19 / 22) : ℂ) * ζ ^ 8 - ((23 / 66) : ℂ) * ζ ^ 10 + ((19 / 33) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 - ((19 / 33) : ℂ) * ζ ^ 18 - ((1 / 11) : ℂ) * ζ ^ 20 + ((1 / 11) : ℂ) * ζ ^ 22 + ((19 / 33) : ℂ) * ζ ^ 24 - ((1 / 11) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((31 / 66) : ℂ) - ((21 / 22) : ℂ) * ζ ^ 2 - ((31 / 66) : ℂ) * ζ ^ 4 - ((89 / 66) : ℂ) * ζ ^ 6 - ((7 / 33) : ℂ) * ζ ^ 8 + ((89 / 66) : ℂ) * ζ ^ 10 + ((32 / 33) : ℂ) * ζ ^ 12 - ((17 / 11) : ℂ) * ζ ^ 14 - ((32 / 33) : ℂ) * ζ ^ 16 + ((1 / 11) : ℂ) * ζ ^ 18 + ((95 / 33) : ℂ) * ζ ^ 20 - ((1 / 11) : ℂ) * ζ ^ 22 - ((2 / 11) : ℂ) * ζ ^ 24 - ((38 / 33) : ℂ) * ζ ^ 26 + ((2 / 11) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((23 / 66) : ℂ) - ((127 / 66) : ℂ) * ζ ^ 2 - ((41 / 66) : ℂ) * ζ ^ 4 + ((15 / 22) : ℂ) * ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((31 / 66) : ℂ) * ζ ^ 10 - ((59 / 66) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 14 - ((5 / 66) : ℂ) * ζ ^ 16 + ((35 / 33) : ℂ) * ζ ^ 18 + ((13 / 33) : ℂ) * ζ ^ 20 + ((1 / 11) : ℂ) * ζ ^ 22 - ((1 / 11) : ℂ) * ζ ^ 24 - ((19 / 33) : ℂ) * ζ ^ 26 + ((1 / 11) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((((2 / 33) : ℂ) - ((7 / 66) : ℂ) * ζ ^ 2 - ((2 / 33) : ℂ) * ζ ^ 4 + ((3 / 22) : ℂ) * ζ ^ 6 + ((19 / 22) : ℂ) * ζ ^ 8 + ((23 / 66) : ℂ) * ζ ^ 10 - ((19 / 33) : ℂ) * ζ ^ 12 - ((5 / 6) : ℂ) * ζ ^ 14 + ((19 / 33) : ℂ) * ζ ^ 18 + ((1 / 11) : ℂ) * ζ ^ 20 - ((1 / 11) : ℂ) * ζ ^ 22 - ((19 / 33) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 26)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY54_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((5 / 44) : ℂ) - ((21 / 44) : ℂ) * ζ ^ 2 + ((9 / 44) : ℂ) * ζ ^ 8 + ((1 / 44) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 18 + ((21 / 44) : ℂ) * ζ ^ 22 - ((5 / 22) : ℂ) * ζ ^ 24 - ((9 / 44) : ℂ) * ζ ^ 28 - ((25 / 44) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1 / 11) : ℂ) + ((37 / 44) : ℂ) * ζ ^ 2 + ((3 / 11) : ℂ) * ζ ^ 6 - ((13 / 22) : ℂ) * ζ ^ 8 - ((13 / 44) : ℂ) * ζ ^ 12 - ((3 / 11) : ℂ) * ζ ^ 18 - ((37 / 44) : ℂ) * ζ ^ 22 + ((15 / 22) : ℂ) * ζ ^ 24 + ((13 / 22) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((13 / 22) : ℂ) - ((23 / 66) : ℂ) * ζ ^ 2 - ((7 / 33) : ℂ) * ζ ^ 6 - ((8 / 33) : ℂ) * ζ ^ 8 - ((4 / 33) : ℂ) * ζ ^ 12 + ((7 / 33) : ℂ) * ζ ^ 18 + ((23 / 66) : ℂ) * ζ ^ 22 - ((23 / 66) : ℂ) * ζ ^ 24 + ((8 / 33) : ℂ) * ζ ^ 28)) * Y 2 2
      + ((-((1 / 6) : ℂ) + ((29 / 66) : ℂ) * ζ ^ 2 + ((1 / 3) : ℂ) * ζ ^ 6 - ((14 / 33) : ℂ) * ζ ^ 8 - ((7 / 66) : ℂ) * ζ ^ 12 - ((20 / 33) : ℂ) * ζ ^ 18 - ((29 / 66) : ℂ) * ζ ^ 22 + ((29 / 66) : ℂ) * ζ ^ 24 + ((14 / 33) : ℂ) * ζ ^ 28 + ((1 / 66) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((5 / 66) : ℂ) + ((4 / 11) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 6 - ((4 / 11) : ℂ) * ζ ^ 8 + ((3 / 22) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 18 - ((4 / 11) : ℂ) * ζ ^ 22 - ((1 / 6) : ℂ) * ζ ^ 24 + ((4 / 11) : ℂ) * ζ ^ 28 + ((5 / 66) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((-((7 / 22) : ℂ) - ((25 / 66) : ℂ) * ζ ^ 2 + ((1 / 33) : ℂ) * ζ ^ 6 + ((17 / 33) : ℂ) * ζ ^ 8 + ((17 / 66) : ℂ) * ζ ^ 12 - ((1 / 33) : ℂ) * ζ ^ 18 + ((25 / 66) : ℂ) * ζ ^ 22 - ((13 / 66) : ℂ) * ζ ^ 24 - ((17 / 33) : ℂ) * ζ ^ 28)) * Y 3 3
      + ((-((2 / 11) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 6 + ((7 / 22) : ℂ) * ζ ^ 8 + ((7 / 44) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 22 - ((3 / 22) : ℂ) * ζ ^ 24 - ((7 / 22) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((-((5 / 22) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 2 - ((2 / 11) : ℂ) * ζ ^ 6 + ((15 / 44) : ℂ) * ζ ^ 8 + ((15 / 44) : ℂ) * ζ ^ 12 + ((3 / 44) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 22 - ((15 / 44) : ℂ) * ζ ^ 28 - ((1 / 11) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY54_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) - ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 + (2 : ℂ) * ζ ^ 8 + ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 18 + ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 28)) * equation
      - (
        ((((1 / 22) : ℂ) + ((5 / 22) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 4 - ((1 / 11) : ℂ) * ζ ^ 6 - ((9 / 22) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 10 + ((2 / 11) : ℂ) * ζ ^ 12 + ((1 / 22) : ℂ) * ζ ^ 14 + ((1 / 11) : ℂ) * ζ ^ 16 - ((3 / 22) : ℂ) * ζ ^ 18 - ((1 / 11) : ℂ) * ζ ^ 20 + ((3 / 11) : ℂ) * ζ ^ 24)) * Y 0 0
        + ((-((5 / 44) : ℂ) + ((5 / 44) : ℂ) * ζ ^ 4 + ((3 / 44) : ℂ) * ζ ^ 6 - ((3 / 44) : ℂ) * ζ ^ 10 - ((3 / 22) : ℂ) * ζ ^ 12 + ((9 / 44) : ℂ) * ζ ^ 14 + ((3 / 22) : ℂ) * ζ ^ 16 - ((9 / 22) : ℂ) * ζ ^ 20)) * Y 0 1
        + ((-((1 / 22) : ℂ) - ((5 / 22) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 4 + ((1 / 11) : ℂ) * ζ ^ 6 + ((9 / 22) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 10 - ((2 / 11) : ℂ) * ζ ^ 12 - ((1 / 22) : ℂ) * ζ ^ 14 - ((1 / 11) : ℂ) * ζ ^ 16 + ((3 / 22) : ℂ) * ζ ^ 18 + ((1 / 11) : ℂ) * ζ ^ 20 - ((3 / 11) : ℂ) * ζ ^ 24)) * Y 4 4
        + ((-((5 / 22) : ℂ) - ((25 / 44) : ℂ) * ζ ^ 2 + ((5 / 22) : ℂ) * ζ ^ 4 + ((13 / 44) : ℂ) * ζ ^ 6 + ((45 / 44) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 10 - ((13 / 22) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 14 - ((1 / 11) : ℂ) * ζ ^ 16 + ((15 / 44) : ℂ) * ζ ^ 18 - ((2 / 11) : ℂ) * ζ ^ 20 - ((15 / 22) : ℂ) * ζ ^ 24)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY54_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((17 / 132) : ℂ) - ((5 / 12) : ℂ) * ζ ^ 2 + ((13 / 132) : ℂ) * ζ ^ 8 + ((7 / 44) : ℂ) * ζ ^ 12 + ((5 / 12) : ℂ) * ζ ^ 18 + ((5 / 12) : ℂ) * ζ ^ 22 - ((17 / 66) : ℂ) * ζ ^ 24 - ((13 / 132) : ℂ) * ζ ^ 28 - ((1 / 4) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((9 / 22) : ℂ) + ((131 / 132) : ℂ) * ζ ^ 2 + ((2 / 33) : ℂ) * ζ ^ 6 - ((61 / 66) : ℂ) * ζ ^ 8 - ((61 / 132) : ℂ) * ζ ^ 12 - ((2 / 33) : ℂ) * ζ ^ 18 - ((131 / 132) : ℂ) * ζ ^ 22 + ((17 / 33) : ℂ) * ζ ^ 24 + ((61 / 66) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((1 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 22 - ((2 / 11) : ℂ) * ζ ^ 24 - ((1 / 11) : ℂ) * ζ ^ 28)) * Y 2 2
      + ((-((1 / 6) : ℂ) + ((29 / 66) : ℂ) * ζ ^ 2 + ((1 / 3) : ℂ) * ζ ^ 6 - ((14 / 33) : ℂ) * ζ ^ 8 - ((7 / 66) : ℂ) * ζ ^ 12 - ((20 / 33) : ℂ) * ζ ^ 18 - ((29 / 66) : ℂ) * ζ ^ 22 + ((29 / 66) : ℂ) * ζ ^ 24 + ((14 / 33) : ℂ) * ζ ^ 28 + ((1 / 66) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((7 / 22) : ℂ) - ((25 / 66) : ℂ) * ζ ^ 2 + ((1 / 33) : ℂ) * ζ ^ 6 + ((17 / 33) : ℂ) * ζ ^ 8 + ((17 / 66) : ℂ) * ζ ^ 12 - ((1 / 33) : ℂ) * ζ ^ 18 + ((25 / 66) : ℂ) * ζ ^ 22 - ((13 / 66) : ℂ) * ζ ^ 24 - ((17 / 33) : ℂ) * ζ ^ 28)) * Y 3 3
      + ((-((2 / 11) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 6 + ((7 / 22) : ℂ) * ζ ^ 8 + ((7 / 44) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 22 - ((3 / 22) : ℂ) * ζ ^ 24 - ((7 / 22) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((-((5 / 22) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 2 - ((2 / 11) : ℂ) * ζ ^ 6 + ((15 / 44) : ℂ) * ζ ^ 8 + ((15 / 44) : ℂ) * ζ ^ 12 + ((3 / 44) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 22 - ((15 / 44) : ℂ) * ζ ^ 28 - ((1 / 11) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY54_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation12
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 33) : ℂ) - ((10 / 33) : ℂ) * ζ ^ 2 + ((8 / 33) : ℂ) * ζ ^ 8 - ((4 / 33) : ℂ) * ζ ^ 12 + ((10 / 33) : ℂ) * ζ ^ 18 + ((10 / 33) : ℂ) * ζ ^ 22 - ((4 / 33) : ℂ) * ζ ^ 24 - ((8 / 33) : ℂ) * ζ ^ 28 - ((14 / 33) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((1 / 22) : ℂ) + ((4 / 33) : ℂ) * ζ ^ 2 + ((7 / 66) : ℂ) * ζ ^ 4 - ((1 / 11) : ℂ) * ζ ^ 6 + ((1 / 33) : ℂ) * ζ ^ 8 - ((1 / 33) : ℂ) * ζ ^ 10 - ((2 / 33) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 14 + ((7 / 33) : ℂ) * ζ ^ 16 - ((1 / 11) : ℂ) * ζ ^ 18 - ((2 / 11) : ℂ) * ζ ^ 20 - ((1 / 33) : ℂ) * ζ ^ 22 - ((7 / 66) : ℂ) * ζ ^ 24 + ((2 / 33) : ℂ) * ζ ^ 26 + ((7 / 66) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((1 / 2) : ℂ) - ((2 / 11) : ℂ) * ζ ^ 2 + ((23 / 66) : ℂ) * ζ ^ 4 + ((25 / 66) : ℂ) * ζ ^ 6 - ((1 / 11) : ℂ) * ζ ^ 8 - ((17 / 66) : ℂ) * ζ ^ 10 - ((17 / 66) : ℂ) * ζ ^ 12 + ((7 / 66) : ℂ) * ζ ^ 16 + ((1 / 11) : ℂ) * ζ ^ 20 + ((4 / 33) : ℂ) * ζ ^ 22 + ((14 / 33) : ℂ) * ζ ^ 24 - ((8 / 33) : ℂ) * ζ ^ 26 - ((14 / 33) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((1 / 2) : ℂ) + ((2 / 11) : ℂ) * ζ ^ 2 - ((23 / 66) : ℂ) * ζ ^ 4 - ((25 / 66) : ℂ) * ζ ^ 6 + ((1 / 11) : ℂ) * ζ ^ 8 + ((17 / 66) : ℂ) * ζ ^ 10 + ((17 / 66) : ℂ) * ζ ^ 12 - ((7 / 66) : ℂ) * ζ ^ 16 - ((1 / 11) : ℂ) * ζ ^ 20 - ((4 / 33) : ℂ) * ζ ^ 22 - ((14 / 33) : ℂ) * ζ ^ 24 + ((8 / 33) : ℂ) * ζ ^ 26 + ((14 / 33) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((((1 / 22) : ℂ) + ((7 / 33) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 6 + ((1 / 33) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 + ((4 / 33) : ℂ) * ζ ^ 12 - ((5 / 33) : ℂ) * ζ ^ 14 - ((4 / 33) : ℂ) * ζ ^ 16 + ((25 / 66) : ℂ) * ζ ^ 18 - ((4 / 33) : ℂ) * ζ ^ 20 - ((25 / 66) : ℂ) * ζ ^ 22 - ((7 / 33) : ℂ) * ζ ^ 24 + ((4 / 33) : ℂ) * ζ ^ 26 + ((7 / 33) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY54_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((5 / 44) : ℂ) - ((23 / 44) : ℂ) * ζ ^ 2 + ((9 / 44) : ℂ) * ζ ^ 8 + ((1 / 44) : ℂ) * ζ ^ 12 + ((23 / 44) : ℂ) * ζ ^ 18 + ((23 / 44) : ℂ) * ζ ^ 22 - ((5 / 22) : ℂ) * ζ ^ 24 - ((9 / 44) : ℂ) * ζ ^ 28 - ((19 / 44) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((1 / 11) : ℂ) + ((27 / 44) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 6 - ((9 / 22) : ℂ) * ζ ^ 8 - ((9 / 44) : ℂ) * ζ ^ 12 - ((1 / 11) : ℂ) * ζ ^ 18 - ((27 / 44) : ℂ) * ζ ^ 22 + ((7 / 22) : ℂ) * ζ ^ 24 + ((9 / 22) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((1 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 22 - ((2 / 11) : ℂ) * ζ ^ 24 - ((1 / 11) : ℂ) * ζ ^ 28)) * Y 2 2
      + ((((3 / 22) : ℂ) + ((9 / 22) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 6 - ((13 / 22) : ℂ) * ζ ^ 8 - ((4 / 11) : ℂ) * ζ ^ 12 - ((3 / 11) : ℂ) * ζ ^ 18 - ((9 / 22) : ℂ) * ζ ^ 22 + ((9 / 22) : ℂ) * ζ ^ 24 + ((13 / 22) : ℂ) * ζ ^ 28 - ((2 / 11) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((2 / 11) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 6 + ((7 / 22) : ℂ) * ζ ^ 8 + ((7 / 44) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 22 - ((3 / 22) : ℂ) * ζ ^ 24 - ((7 / 22) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((-((5 / 22) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 2 - ((2 / 11) : ℂ) * ζ ^ 6 + ((15 / 44) : ℂ) * ζ ^ 8 + ((15 / 44) : ℂ) * ζ ^ 12 + ((3 / 44) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 22 - ((15 / 44) : ℂ) * ζ ^ 28 - ((1 / 11) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY54_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation13
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((8 / 33) : ℂ) + ((14 / 33) : ℂ) * ζ ^ 2 + ((2 / 33) : ℂ) * ζ ^ 6 - ((2 / 11) : ℂ) * ζ ^ 8 + ((2 / 11) : ℂ) * ζ ^ 12 - ((8 / 33) : ℂ) * ζ ^ 18 - ((14 / 33) : ℂ) * ζ ^ 22 + ((4 / 33) : ℂ) * ζ ^ 24 + ((2 / 11) : ℂ) * ζ ^ 28 + ((4 / 33) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((5 / 66) : ℂ) + ((5 / 66) : ℂ) * ζ ^ 4 + ((1 / 22) : ℂ) * ζ ^ 6 + ((1 / 33) : ℂ) * ζ ^ 8 + ((2 / 33) : ℂ) * ζ ^ 10 - ((1 / 11) : ℂ) * ζ ^ 14 - ((1 / 22) : ℂ) * ζ ^ 16 + ((5 / 66) : ℂ) * ζ ^ 18 + ((1 / 66) : ℂ) * ζ ^ 20 + ((1 / 33) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 24 - ((1 / 33) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((13 / 66) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 2 - ((13 / 66) : ℂ) * ζ ^ 4 - ((1 / 22) : ℂ) * ζ ^ 6 + ((1 / 11) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 10 - ((5 / 66) : ℂ) * ζ ^ 12 + ((13 / 66) : ℂ) * ζ ^ 14 + ((5 / 66) : ℂ) * ζ ^ 16 + ((4 / 33) : ℂ) * ζ ^ 18 - ((19 / 66) : ℂ) * ζ ^ 20 - ((4 / 33) : ℂ) * ζ ^ 22 - ((2 / 33) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 26 + ((2 / 33) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((10 / 33) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 4 + ((7 / 22) : ℂ) * ζ ^ 6 - ((2 / 33) : ℂ) * ζ ^ 8 - ((5 / 22) : ℂ) * ζ ^ 10 - ((2 / 33) : ℂ) * ζ ^ 12 - ((1 / 66) : ℂ) * ζ ^ 14 - ((5 / 33) : ℂ) * ζ ^ 16 + ((1 / 33) : ℂ) * ζ ^ 18 + ((4 / 11) : ℂ) * ζ ^ 20 + ((2 / 33) : ℂ) * ζ ^ 22 + ((4 / 33) : ℂ) * ζ ^ 24 - ((2 / 11) : ℂ) * ζ ^ 26 - ((4 / 33) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((13 / 66) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 + ((13 / 66) : ℂ) * ζ ^ 4 + ((1 / 22) : ℂ) * ζ ^ 6 - ((1 / 11) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 10 + ((5 / 66) : ℂ) * ζ ^ 12 - ((13 / 66) : ℂ) * ζ ^ 14 - ((5 / 66) : ℂ) * ζ ^ 16 - ((4 / 33) : ℂ) * ζ ^ 18 + ((19 / 66) : ℂ) * ζ ^ 20 + ((4 / 33) : ℂ) * ζ ^ 22 + ((2 / 33) : ℂ) * ζ ^ 24 - ((1 / 11) : ℂ) * ζ ^ 26 - ((2 / 33) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY54_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 22 - ((2 / 11) : ℂ) * ζ ^ 24 - ((1 / 11) : ℂ) * ζ ^ 28)) * Y 2 2
      + ((((3 / 22) : ℂ) + ((9 / 22) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 6 - ((13 / 22) : ℂ) * ζ ^ 8 - ((4 / 11) : ℂ) * ζ ^ 12 - ((3 / 11) : ℂ) * ζ ^ 18 - ((9 / 22) : ℂ) * ζ ^ 22 + ((9 / 22) : ℂ) * ζ ^ 24 + ((13 / 22) : ℂ) * ζ ^ 28 - ((2 / 11) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((1 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 22 + ((2 / 11) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((-((4 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 28)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY54_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(1 : ℂ) - ((7 / 3) : ℂ) * ζ ^ 2 + ((5 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((7 / 3) : ℂ) * ζ ^ 18 + ((7 / 3) : ℂ) * ζ ^ 22 - (2 : ℂ) * ζ ^ 24 - ((5 / 3) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((5 / 22) : ℂ) + ((3 / 11) : ℂ) * ζ ^ 2 - ((5 / 22) : ℂ) * ζ ^ 4 - ((3 / 11) : ℂ) * ζ ^ 6 - ((3 / 11) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 10 + ((3 / 11) : ℂ) * ζ ^ 12 - ((1 / 22) : ℂ) * ζ ^ 16 - ((3 / 11) : ℂ) * ζ ^ 18 + ((1 / 22) : ℂ) * ζ ^ 20 - ((1 / 22) : ℂ) * ζ ^ 22 + ((5 / 22) : ℂ) * ζ ^ 24 + ((1 / 22) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((5 / 44) : ℂ) + ((3 / 22) : ℂ) * ζ ^ 2 + ((5 / 44) : ℂ) * ζ ^ 4 - ((1 / 22) : ℂ) * ζ ^ 6 - ((2 / 11) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 10 + ((3 / 44) : ℂ) * ζ ^ 12 + ((9 / 22) : ℂ) * ζ ^ 14 - ((3 / 44) : ℂ) * ζ ^ 16 + ((3 / 44) : ℂ) * ζ ^ 18 - ((15 / 44) : ℂ) * ζ ^ 20 - ((3 / 44) : ℂ) * ζ ^ 22)) * Y 1 1
        + ((((5 / 44) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 2 - ((5 / 44) : ℂ) * ζ ^ 4 + ((1 / 22) : ℂ) * ζ ^ 6 + ((2 / 11) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 10 - ((3 / 44) : ℂ) * ζ ^ 12 - ((9 / 22) : ℂ) * ζ ^ 14 + ((3 / 44) : ℂ) * ζ ^ 16 - ((3 / 44) : ℂ) * ζ ^ 18 + ((15 / 44) : ℂ) * ζ ^ 20 + ((3 / 44) : ℂ) * ζ ^ 22)) * Y 4 4
        + ((((15 / 44) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 2 - ((15 / 44) : ℂ) * ζ ^ 4 - ((1 / 22) : ℂ) * ζ ^ 6 + ((5 / 22) : ℂ) * ζ ^ 8 - ((5 / 44) : ℂ) * ζ ^ 10 - ((9 / 11) : ℂ) * ζ ^ 14 + ((5 / 44) : ℂ) * ζ ^ 16 - ((3 / 11) : ℂ) * ζ ^ 18 + ((31 / 44) : ℂ) * ζ ^ 20 + ((5 / 44) : ℂ) * ζ ^ 22 + ((5 / 44) : ℂ) * ζ ^ 24 + ((1 / 44) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY54_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY54_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation24
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) * ζ ^ 2 + (4 : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 22 - (4 : ℂ) * ζ ^ 24 - (4 : ℂ) * ζ ^ 28)) * equation
      - (
        ((((1 / 11) : ℂ) + ((1 / 22) : ℂ) * ζ ^ 2 - ((3 / 22) : ℂ) * ζ ^ 4 - ((1 / 22) : ℂ) * ζ ^ 6 - ((25 / 22) : ℂ) * ζ ^ 8 - ((2 / 11) : ℂ) * ζ ^ 10 + ((8 / 11) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((3 / 22) : ℂ) * ζ ^ 16 - ((5 / 22) : ℂ) * ζ ^ 18 + ((3 / 22) : ℂ) * ζ ^ 20 + ((7 / 11) : ℂ) * ζ ^ 24 - ((3 / 11) : ℂ) * ζ ^ 26)) * Y 2 2
        + ((((3 / 22) : ℂ) + ((1 / 22) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 4 + ((4 / 11) : ℂ) * ζ ^ 8 - ((3 / 11) : ℂ) * ζ ^ 10 - ((5 / 22) : ℂ) * ζ ^ 12 - ((5 / 22) : ℂ) * ζ ^ 14 + ((5 / 22) : ℂ) * ζ ^ 16 - ((3 / 11) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 - ((2 / 11) : ℂ) * ζ ^ 24 + ((5 / 11) : ℂ) * ζ ^ 26)) * Y 2 3
        + ((-((1 / 11) : ℂ) - ((1 / 22) : ℂ) * ζ ^ 2 + ((3 / 22) : ℂ) * ζ ^ 4 + ((1 / 22) : ℂ) * ζ ^ 6 + ((25 / 22) : ℂ) * ζ ^ 8 + ((2 / 11) : ℂ) * ζ ^ 10 - ((8 / 11) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((3 / 22) : ℂ) * ζ ^ 16 + ((5 / 22) : ℂ) * ζ ^ 18 - ((3 / 22) : ℂ) * ζ ^ 20 - ((7 / 11) : ℂ) * ζ ^ 24 + ((3 / 11) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((15 / 11) : ℂ) + ((9 / 22) : ℂ) * ζ ^ 2 + ((15 / 11) : ℂ) * ζ ^ 4 - ((9 / 22) : ℂ) * ζ ^ 6 - ((39 / 22) : ℂ) * ζ ^ 8 + ((5 / 11) : ℂ) * ζ ^ 10 + ((6 / 11) : ℂ) * ζ ^ 12 + ((12 / 11) : ℂ) * ζ ^ 14 - ((7 / 11) : ℂ) * ζ ^ 16 + ((1 / 22) : ℂ) * ζ ^ 18 + ((2 / 11) : ℂ) * ζ ^ 20 - ((1 / 11) : ℂ) * ζ ^ 24 - ((14 / 11) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY54
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 5 4 = 0 := by
  have reduced :=
    row16_reducedY54_combinationStep08 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row16_reducedY55_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((43 / 33) : ℂ) - ((69 / 44) : ℂ) * ζ ^ 2 - ((12 / 11) : ℂ) * ζ ^ 6 + ((34 / 11) : ℂ) * ζ ^ 12 + ((45 / 22) : ℂ) * ζ ^ 18 + ((69 / 44) : ℂ) * ζ ^ 22 - ((43 / 33) : ℂ) * ζ ^ 24 - ((69 / 22) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((21 / 22) : ℂ) * ζ ^ 2 + ((12 / 11) : ℂ) * ζ ^ 6 - ((59 / 33) : ℂ) * ζ ^ 8 + ((43 / 33) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 18 + ((21 / 22) : ℂ) * ζ ^ 22 - ((43 / 33) : ℂ) * ζ ^ 24 + ((59 / 33) : ℂ) * ζ ^ 28 - ((45 / 22) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((580 / 33) : ℂ) + ((21 / 11) : ℂ) * ζ ^ 2 - ((138 / 11) : ℂ) * ζ ^ 6 + ((136 / 11) : ℂ) * ζ ^ 8 + ((136 / 11) : ℂ) * ζ ^ 12 + ((159 / 11) : ℂ) * ζ ^ 18 - ((21 / 11) : ℂ) * ζ ^ 22 - ((136 / 11) : ℂ) * ζ ^ 28 - ((69 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((34 / 11) : ℂ) + ((45 / 22) : ℂ) * ζ ^ 2 + ((34 / 11) : ℂ) * ζ ^ 4 - ((45 / 11) : ℂ) * ζ ^ 6 + ((45 / 11) : ℂ) * ζ ^ 10 - ((34 / 11) : ℂ) * ζ ^ 12 - ((45 / 22) : ℂ) * ζ ^ 14 + ((34 / 11) : ℂ) * ζ ^ 16 + ((69 / 44) : ℂ) * ζ ^ 18 - ((34 / 11) : ℂ) * ζ ^ 20 - ((69 / 44) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((((21 / 22) : ℂ) * ζ ^ 2 - ((45 / 22) : ℂ) * ζ ^ 6 + ((68 / 11) : ℂ) * ζ ^ 8 + ((69 / 44) : ℂ) * ζ ^ 10 - ((34 / 11) : ℂ) * ζ ^ 12 + ((45 / 22) : ℂ) * ζ ^ 14 - ((21 / 44) : ℂ) * ζ ^ 18 - ((34 / 11) : ℂ) * ζ ^ 24 - ((69 / 44) : ℂ) * ζ ^ 26)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY55_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((4 / 11) : ℂ) + ((7 / 44) : ℂ) * ζ ^ 2 - ((6 / 11) : ℂ) * ζ ^ 6 - ((7 / 33) : ℂ) * ζ ^ 8 - ((7 / 33) : ℂ) * ζ ^ 12 + ((31 / 44) : ℂ) * ζ ^ 18 - ((7 / 44) : ℂ) * ζ ^ 22 + ((7 / 33) : ℂ) * ζ ^ 28 - ((3 / 11) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((64 / 33) : ℂ) - ((3 / 11) : ℂ) * ζ ^ 2 - ((27 / 44) : ℂ) * ζ ^ 6 + ((46 / 11) : ℂ) * ζ ^ 12 - ((3 / 44) : ℂ) * ζ ^ 18 + ((3 / 11) : ℂ) * ζ ^ 22 - ((64 / 33) : ℂ) * ζ ^ 24 - ((6 / 11) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((21 / 22) : ℂ) * ζ ^ 2 + ((12 / 11) : ℂ) * ζ ^ 6 - ((59 / 33) : ℂ) * ζ ^ 8 + ((43 / 33) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 18 + ((21 / 22) : ℂ) * ζ ^ 22 - ((43 / 33) : ℂ) * ζ ^ 24 + ((59 / 33) : ℂ) * ζ ^ 28 - ((45 / 22) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((4 / 11) : ℂ) - ((7 / 44) : ℂ) * ζ ^ 2 + ((6 / 11) : ℂ) * ζ ^ 6 + ((7 / 33) : ℂ) * ζ ^ 8 + ((7 / 33) : ℂ) * ζ ^ 12 - ((31 / 44) : ℂ) * ζ ^ 18 + ((7 / 44) : ℂ) * ζ ^ 22 - ((7 / 33) : ℂ) * ζ ^ 28 + ((3 / 11) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY55_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((16 / 11) : ℂ) - ((31 / 11) : ℂ) * ζ ^ 2 - ((12 / 11) : ℂ) * ζ ^ 6 - ((76 / 33) : ℂ) * ζ ^ 12 + ((50 / 11) : ℂ) * ζ ^ 18 + ((31 / 11) : ℂ) * ζ ^ 22 + ((16 / 11) : ℂ) * ζ ^ 24 - ((62 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((4 / 11) : ℂ) - ((7 / 44) : ℂ) * ζ ^ 2 + ((4 / 11) : ℂ) * ζ ^ 4 + ((31 / 44) : ℂ) * ζ ^ 6 + ((7 / 33) : ℂ) * ζ ^ 8 - ((31 / 22) : ℂ) * ζ ^ 10 + ((3 / 11) : ℂ) * ζ ^ 14 - ((31 / 44) : ℂ) * ζ ^ 18 - ((4 / 11) : ℂ) * ζ ^ 20 + ((31 / 22) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((7 / 11) : ℂ) - ((57 / 44) : ℂ) * ζ ^ 2 - ((7 / 11) : ℂ) * ζ ^ 4 + ((9 / 11) : ℂ) * ζ ^ 6 + ((19 / 11) : ℂ) * ζ ^ 8 - ((129 / 44) : ℂ) * ζ ^ 10 - ((12 / 11) : ℂ) * ζ ^ 12 - ((57 / 44) : ℂ) * ζ ^ 14 + ((12 / 11) : ℂ) * ζ ^ 16 + ((93 / 44) : ℂ) * ζ ^ 18 - ((12 / 11) : ℂ) * ζ ^ 20 - ((93 / 22) : ℂ) * ζ ^ 22 + ((93 / 22) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((4 / 11) : ℂ) + ((7 / 44) : ℂ) * ζ ^ 2 - ((4 / 11) : ℂ) * ζ ^ 4 - ((31 / 44) : ℂ) * ζ ^ 6 - ((7 / 33) : ℂ) * ζ ^ 8 + ((31 / 22) : ℂ) * ζ ^ 10 - ((3 / 11) : ℂ) * ζ ^ 14 + ((31 / 44) : ℂ) * ζ ^ 18 + ((4 / 11) : ℂ) * ζ ^ 20 - ((31 / 22) : ℂ) * ζ ^ 26)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY55_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((2 / 3) : ℂ) + ((133 / 132) : ℂ) * ζ ^ 2 - ((37 / 33) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 + ((281 / 132) : ℂ) * ζ ^ 18 - ((133 / 132) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 28 - ((37 / 66) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((((34 / 33) : ℂ) + ((14 / 11) : ℂ) * ζ ^ 2 + ((37 / 132) : ℂ) * ζ ^ 6 - ((71 / 66) : ℂ) * ζ ^ 12 - ((299 / 132) : ℂ) * ζ ^ 18 - ((14 / 11) : ℂ) * ζ ^ 22 + ((34 / 33) : ℂ) * ζ ^ 24 + ((28 / 11) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((21 / 22) : ℂ) * ζ ^ 2 + ((12 / 11) : ℂ) * ζ ^ 6 - ((59 / 33) : ℂ) * ζ ^ 8 + ((43 / 33) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 18 + ((21 / 22) : ℂ) * ζ ^ 22 - ((43 / 33) : ℂ) * ζ ^ 24 + ((59 / 33) : ℂ) * ζ ^ 28 - ((45 / 22) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((4 / 11) : ℂ) - ((7 / 44) : ℂ) * ζ ^ 2 + ((6 / 11) : ℂ) * ζ ^ 6 + ((7 / 33) : ℂ) * ζ ^ 8 + ((7 / 33) : ℂ) * ζ ^ 12 - ((31 / 44) : ℂ) * ζ ^ 18 + ((7 / 44) : ℂ) * ζ ^ 22 - ((7 / 33) : ℂ) * ζ ^ 28 + ((3 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((34 / 33) : ℂ) - ((28 / 33) : ℂ) * ζ ^ 2 + ((19 / 33) : ℂ) * ζ ^ 6 + ((4 / 33) : ℂ) * ζ ^ 8 + ((4 / 33) : ℂ) * ζ ^ 12 - ((47 / 33) : ℂ) * ζ ^ 18 + ((28 / 33) : ℂ) * ζ ^ 22 - ((4 / 33) : ℂ) * ζ ^ 28 + ((19 / 66) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((67 / 66) : ℂ) - ((3 / 11) : ℂ) * ζ ^ 2 + ((41 / 66) : ℂ) * ζ ^ 6 + ((17 / 66) : ℂ) * ζ ^ 8 + ((13 / 33) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 18 + ((3 / 11) : ℂ) * ζ ^ 22 - ((4 / 33) : ℂ) * ζ ^ 24 - ((17 / 66) : ℂ) * ζ ^ 28 - ((13 / 33) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have previous :=
    row16_reducedY55_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation02
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((70 / 33) : ℂ) + ((16 / 11) : ℂ) * ζ ^ 2 + ((200 / 33) : ℂ) * ζ ^ 6 - ((116 / 33) : ℂ) * ζ ^ 8 - ((116 / 33) : ℂ) * ζ ^ 12 - ((152 / 33) : ℂ) * ζ ^ 18 - ((16 / 11) : ℂ) * ζ ^ 22 + ((116 / 33) : ℂ) * ζ ^ 28 + ((100 / 33) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 33) : ℂ) - ((29 / 11) : ℂ) * ζ ^ 2 - ((23 / 33) : ℂ) * ζ ^ 4 - ((29 / 33) : ℂ) * ζ ^ 6 - ((13 / 11) : ℂ) * ζ ^ 8 + ((29 / 11) : ℂ) * ζ ^ 10 - ((58 / 33) : ℂ) * ζ ^ 14 - ((8 / 11) : ℂ) * ζ ^ 16 + ((29 / 33) : ℂ) * ζ ^ 18 + ((37 / 33) : ℂ) * ζ ^ 20 + ((29 / 33) : ℂ) * ζ ^ 22 + ((25 / 33) : ℂ) * ζ ^ 24 - ((29 / 33) : ℂ) * ζ ^ 26 - ((25 / 33) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((98 / 33) : ℂ) - ((16 / 33) : ℂ) * ζ ^ 2 + ((122 / 33) : ℂ) * ζ ^ 4 + ((4 / 33) : ℂ) * ζ ^ 6 - ((10 / 33) : ℂ) * ζ ^ 8 - ((62 / 33) : ℂ) * ζ ^ 10 + ((51 / 11) : ℂ) * ζ ^ 12 - ((29 / 33) : ℂ) * ζ ^ 14 - ((43 / 11) : ℂ) * ζ ^ 16 + ((58 / 33) : ℂ) * ζ ^ 18 + ((2 / 33) : ℂ) * ζ ^ 20 - ((116 / 33) : ℂ) * ζ ^ 22 - ((100 / 33) : ℂ) * ζ ^ 24 + ((116 / 33) : ℂ) * ζ ^ 26 + ((100 / 33) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((1 / 33) : ℂ) + ((29 / 11) : ℂ) * ζ ^ 2 + ((23 / 33) : ℂ) * ζ ^ 4 + ((29 / 33) : ℂ) * ζ ^ 6 + ((13 / 11) : ℂ) * ζ ^ 8 - ((29 / 11) : ℂ) * ζ ^ 10 + ((58 / 33) : ℂ) * ζ ^ 14 + ((8 / 11) : ℂ) * ζ ^ 16 - ((29 / 33) : ℂ) * ζ ^ 18 - ((37 / 33) : ℂ) * ζ ^ 20 - ((29 / 33) : ℂ) * ζ ^ 22 - ((25 / 33) : ℂ) * ζ ^ 24 + ((29 / 33) : ℂ) * ζ ^ 26 + ((25 / 33) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((((17 / 11) : ℂ) + ((7 / 11) : ℂ) * ζ ^ 2 - ((17 / 11) : ℂ) * ζ ^ 4 - ((3 / 11) : ℂ) * ζ ^ 6 - ((16 / 33) : ℂ) * ζ ^ 8 - ((1 / 11) : ℂ) * ζ ^ 10 - ((25 / 33) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 14 + ((18 / 11) : ℂ) * ζ ^ 16 + ((13 / 33) : ℂ) * ζ ^ 18 - ((29 / 33) : ℂ) * ζ ^ 20 - ((25 / 33) : ℂ) * ζ ^ 22 + ((29 / 33) : ℂ) * ζ ^ 24 + ((25 / 33) : ℂ) * ζ ^ 26)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY55_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((8 / 11) : ℂ) + ((39 / 44) : ℂ) * ζ ^ 2 - ((2 / 11) : ℂ) * ζ ^ 6 - ((5 / 66) : ℂ) * ζ ^ 8 - ((5 / 66) : ℂ) * ζ ^ 12 + ((47 / 44) : ℂ) * ζ ^ 18 - ((39 / 44) : ℂ) * ζ ^ 22 + ((5 / 66) : ℂ) * ζ ^ 28 - ((1 / 11) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((167 / 66) : ℂ) - ((10 / 11) : ℂ) * ζ ^ 2 - ((35 / 44) : ℂ) * ζ ^ 6 + ((119 / 22) : ℂ) * ζ ^ 12 + ((45 / 44) : ℂ) * ζ ^ 18 + ((10 / 11) : ℂ) * ζ ^ 22 - ((167 / 66) : ℂ) * ζ ^ 24 - ((20 / 11) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((21 / 22) : ℂ) * ζ ^ 2 + ((12 / 11) : ℂ) * ζ ^ 6 - ((59 / 33) : ℂ) * ζ ^ 8 + ((43 / 33) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 18 + ((21 / 22) : ℂ) * ζ ^ 22 - ((43 / 33) : ℂ) * ζ ^ 24 + ((59 / 33) : ℂ) * ζ ^ 28 - ((45 / 22) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((4 / 11) : ℂ) - ((7 / 44) : ℂ) * ζ ^ 2 + ((6 / 11) : ℂ) * ζ ^ 6 + ((7 / 33) : ℂ) * ζ ^ 8 + ((7 / 33) : ℂ) * ζ ^ 12 - ((31 / 44) : ℂ) * ζ ^ 18 + ((7 / 44) : ℂ) * ζ ^ 22 - ((7 / 33) : ℂ) * ζ ^ 28 + ((3 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((34 / 33) : ℂ) - ((28 / 33) : ℂ) * ζ ^ 2 + ((19 / 33) : ℂ) * ζ ^ 6 + ((4 / 33) : ℂ) * ζ ^ 8 + ((4 / 33) : ℂ) * ζ ^ 12 - ((47 / 33) : ℂ) * ζ ^ 18 + ((28 / 33) : ℂ) * ζ ^ 22 - ((4 / 33) : ℂ) * ζ ^ 28 + ((19 / 66) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((46 / 33) : ℂ) - ((16 / 11) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 6 - ((49 / 33) : ℂ) * ζ ^ 8 + ((2 / 33) : ℂ) * ζ ^ 12 + ((46 / 33) : ℂ) * ζ ^ 18 + ((16 / 11) : ℂ) * ζ ^ 22 + ((23 / 66) : ℂ) * ζ ^ 24 + ((49 / 33) : ℂ) * ζ ^ 28 - ((23 / 22) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((67 / 66) : ℂ) - ((3 / 11) : ℂ) * ζ ^ 2 + ((41 / 66) : ℂ) * ζ ^ 6 + ((17 / 66) : ℂ) * ζ ^ 8 + ((13 / 33) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 18 + ((3 / 11) : ℂ) * ζ ^ 22 - ((4 / 33) : ℂ) * ζ ^ 24 - ((17 / 66) : ℂ) * ζ ^ 28 - ((13 / 33) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((2 / 33) : ℂ) + ((4 / 33) : ℂ) * ζ ^ 2 - ((31 / 33) : ℂ) * ζ ^ 6 - ((17 / 66) : ℂ) * ζ ^ 8 - ((17 / 66) : ℂ) * ζ ^ 12 + ((35 / 33) : ℂ) * ζ ^ 18 - ((4 / 33) : ℂ) * ζ ^ 22 + ((17 / 66) : ℂ) * ζ ^ 28 - ((31 / 66) : ℂ) * ζ ^ 30)) * Y 3 3) = 0 := by
  have previous :=
    row16_reducedY55_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation03
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((62 / 33) : ℂ) - ((30 / 11) : ℂ) * ζ ^ 2 + ((14 / 11) : ℂ) * ζ ^ 6 - ((104 / 33) : ℂ) * ζ ^ 8 + ((28 / 33) : ℂ) * ζ ^ 12 + ((62 / 33) : ℂ) * ζ ^ 18 + ((30 / 11) : ℂ) * ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 + ((104 / 33) : ℂ) * ζ ^ 28 - ((106 / 33) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((9 / 22) : ℂ) + ((53 / 66) : ℂ) * ζ ^ 2 + ((9 / 22) : ℂ) * ζ ^ 4 - ((35 / 22) : ℂ) * ζ ^ 6 - ((1 / 11) : ℂ) * ζ ^ 8 + ((10 / 11) : ℂ) * ζ ^ 10 - ((31 / 66) : ℂ) * ζ ^ 12 - ((19 / 33) : ℂ) * ζ ^ 14 - ((7 / 22) : ℂ) * ζ ^ 16 + ((4 / 33) : ℂ) * ζ ^ 18 + ((37 / 33) : ℂ) * ζ ^ 20 - ((53 / 66) : ℂ) * ζ ^ 22 - ((26 / 33) : ℂ) * ζ ^ 24 + ((53 / 66) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((173 / 66) : ℂ) + ((39 / 11) : ℂ) * ζ ^ 2 - ((173 / 66) : ℂ) * ζ ^ 4 - ((56 / 33) : ℂ) * ζ ^ 6 + ((71 / 33) : ℂ) * ζ ^ 8 + ((56 / 33) : ℂ) * ζ ^ 10 - ((50 / 11) : ℂ) * ζ ^ 12 - ((62 / 33) : ℂ) * ζ ^ 14 + ((50 / 11) : ℂ) * ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 - ((86 / 33) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 + ((53 / 33) : ℂ) * ζ ^ 24 + ((52 / 33) : ℂ) * ζ ^ 26 - ((53 / 33) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((5 / 11) : ℂ) + ((34 / 33) : ℂ) * ζ ^ 2 - ((10 / 11) : ℂ) * ζ ^ 4 + ((5 / 11) : ℂ) * ζ ^ 6 + ((1 / 11) : ℂ) * ζ ^ 8 - ((67 / 33) : ℂ) * ζ ^ 10 + ((5 / 11) : ℂ) * ζ ^ 12 + ((21 / 11) : ℂ) * ζ ^ 14 - ((20 / 11) : ℂ) * ζ ^ 16 - ((5 / 11) : ℂ) * ζ ^ 18 + ((49 / 33) : ℂ) * ζ ^ 20 - ((37 / 33) : ℂ) * ζ ^ 22 + ((53 / 66) : ℂ) * ζ ^ 24 + ((26 / 33) : ℂ) * ζ ^ 26 - ((53 / 66) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((((9 / 22) : ℂ) - ((53 / 66) : ℂ) * ζ ^ 2 - ((9 / 22) : ℂ) * ζ ^ 4 + ((35 / 22) : ℂ) * ζ ^ 6 + ((1 / 11) : ℂ) * ζ ^ 8 - ((10 / 11) : ℂ) * ζ ^ 10 + ((31 / 66) : ℂ) * ζ ^ 12 + ((19 / 33) : ℂ) * ζ ^ 14 + ((7 / 22) : ℂ) * ζ ^ 16 - ((4 / 33) : ℂ) * ζ ^ 18 - ((37 / 33) : ℂ) * ζ ^ 20 + ((53 / 66) : ℂ) * ζ ^ 22 + ((26 / 33) : ℂ) * ζ ^ 24 - ((53 / 66) : ℂ) * ζ ^ 26)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY55_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((41 / 22) : ℂ) + ζ ^ 2 - ζ ^ 6 + ((29 / 33) : ℂ) * ζ ^ 8 + ((29 / 33) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 - ζ ^ 22 - ((29 / 33) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((155 / 66) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 6 + ((49 / 11) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((155 / 66) : ℂ) * ζ ^ 24 - ζ ^ 30)) * Y 0 1
      + ((-((21 / 22) : ℂ) * ζ ^ 2 + ((12 / 11) : ℂ) * ζ ^ 6 - ((59 / 33) : ℂ) * ζ ^ 8 + ((43 / 33) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 18 + ((21 / 22) : ℂ) * ζ ^ 22 - ((43 / 33) : ℂ) * ζ ^ 24 + ((59 / 33) : ℂ) * ζ ^ 28 - ((45 / 22) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((4 / 11) : ℂ) - ((7 / 44) : ℂ) * ζ ^ 2 + ((6 / 11) : ℂ) * ζ ^ 6 + ((7 / 33) : ℂ) * ζ ^ 8 + ((7 / 33) : ℂ) * ζ ^ 12 - ((31 / 44) : ℂ) * ζ ^ 18 + ((7 / 44) : ℂ) * ζ ^ 22 - ((7 / 33) : ℂ) * ζ ^ 28 + ((3 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((34 / 33) : ℂ) - ((28 / 33) : ℂ) * ζ ^ 2 + ((19 / 33) : ℂ) * ζ ^ 6 + ((4 / 33) : ℂ) * ζ ^ 8 + ((4 / 33) : ℂ) * ζ ^ 12 - ((47 / 33) : ℂ) * ζ ^ 18 + ((28 / 33) : ℂ) * ζ ^ 22 - ((4 / 33) : ℂ) * ζ ^ 28 + ((19 / 66) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((46 / 33) : ℂ) - ((16 / 11) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 6 - ((49 / 33) : ℂ) * ζ ^ 8 + ((2 / 33) : ℂ) * ζ ^ 12 + ((46 / 33) : ℂ) * ζ ^ 18 + ((16 / 11) : ℂ) * ζ ^ 22 + ((23 / 66) : ℂ) * ζ ^ 24 + ((49 / 33) : ℂ) * ζ ^ 28 - ((23 / 22) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((67 / 66) : ℂ) - ((3 / 11) : ℂ) * ζ ^ 2 + ((41 / 66) : ℂ) * ζ ^ 6 + ((17 / 66) : ℂ) * ζ ^ 8 + ((13 / 33) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 18 + ((3 / 11) : ℂ) * ζ ^ 22 - ((4 / 33) : ℂ) * ζ ^ 24 - ((17 / 66) : ℂ) * ζ ^ 28 - ((13 / 33) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((2 / 33) : ℂ) + ((4 / 33) : ℂ) * ζ ^ 2 - ((31 / 33) : ℂ) * ζ ^ 6 - ((17 / 66) : ℂ) * ζ ^ 8 - ((17 / 66) : ℂ) * ζ ^ 12 + ((35 / 33) : ℂ) * ζ ^ 18 - ((4 / 33) : ℂ) * ζ ^ 22 + ((17 / 66) : ℂ) * ζ ^ 28 - ((31 / 66) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((25 / 22) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 2 + ((9 / 11) : ℂ) * ζ ^ 6 - ((21 / 22) : ℂ) * ζ ^ 8 - ((21 / 22) : ℂ) * ζ ^ 12 - ((41 / 44) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 22 + ((21 / 22) : ℂ) * ζ ^ 28 + ((9 / 22) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((25 / 11) : ℂ) + ((59 / 44) : ℂ) * ζ ^ 6 - ((25 / 22) : ℂ) * ζ ^ 8 - ((23 / 11) : ℂ) * ζ ^ 12 - ((87 / 44) : ℂ) * ζ ^ 18 + ((2 / 11) : ℂ) * ζ ^ 24 + ((25 / 22) : ℂ) * ζ ^ 28 + ((59 / 44) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY55_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((2 : ℂ) + ((1 / 3) : ℂ) * ζ ^ 2 + ((8 / 3) : ℂ) * ζ ^ 6 - ((10 / 3) : ℂ) * ζ ^ 8 - ((10 / 3) : ℂ) * ζ ^ 12 - ((7 / 3) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 22 + ((10 / 3) : ℂ) * ζ ^ 28 + ((4 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((5 / 11) : ℂ) - ((5 / 22) : ℂ) * ζ ^ 2 - ((5 / 11) : ℂ) * ζ ^ 4 + ((3 / 22) : ℂ) * ζ ^ 6 + ((10 / 11) : ℂ) * ζ ^ 8 - ((1 / 11) : ℂ) * ζ ^ 10 + ((3 / 11) : ℂ) * ζ ^ 14 - ((5 / 11) : ℂ) * ζ ^ 16 - ((3 / 22) : ℂ) * ζ ^ 18 + ((5 / 11) : ℂ) * ζ ^ 20 + ((2 / 11) : ℂ) * ζ ^ 22 - ((5 / 11) : ℂ) * ζ ^ 24 - ((2 / 11) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((5 / 22) : ℂ) - ((15 / 44) : ℂ) * ζ ^ 2 - ((5 / 22) : ℂ) * ζ ^ 4 + ((13 / 22) : ℂ) * ζ ^ 6 - ((5 / 11) : ℂ) * ζ ^ 8 - ((13 / 22) : ℂ) * ζ ^ 10 + ((15 / 22) : ℂ) * ζ ^ 12 + ((9 / 44) : ℂ) * ζ ^ 14 - ((15 / 22) : ℂ) * ζ ^ 16 - ((3 / 11) : ℂ) * ζ ^ 18 + ((15 / 22) : ℂ) * ζ ^ 20 + ((3 / 11) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((-((5 / 11) : ℂ) + ((5 / 22) : ℂ) * ζ ^ 2 + ((5 / 11) : ℂ) * ζ ^ 4 - ((3 / 22) : ℂ) * ζ ^ 6 - ((10 / 11) : ℂ) * ζ ^ 8 + ((1 / 11) : ℂ) * ζ ^ 10 - ((3 / 11) : ℂ) * ζ ^ 14 + ((5 / 11) : ℂ) * ζ ^ 16 + ((3 / 22) : ℂ) * ζ ^ 18 - ((5 / 11) : ℂ) * ζ ^ 20 - ((2 / 11) : ℂ) * ζ ^ 22 + ((5 / 11) : ℂ) * ζ ^ 24 + ((2 / 11) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((10 / 11) : ℂ) + ((5 / 22) : ℂ) * ζ ^ 2 + ((10 / 11) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 - ((30 / 11) : ℂ) * ζ ^ 8 - ((4 / 11) : ℂ) * ζ ^ 10 + ((15 / 22) : ℂ) * ζ ^ 12 - ((21 / 44) : ℂ) * ζ ^ 14 + ((5 / 11) : ℂ) * ζ ^ 16 + ((3 / 44) : ℂ) * ζ ^ 18 - ((5 / 11) : ℂ) * ζ ^ 20 - ((2 / 11) : ℂ) * ζ ^ 22 + ((25 / 22) : ℂ) * ζ ^ 24 + ((5 / 11) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY55_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((8 / 3) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((9 / 2) : ℂ) * ζ ^ 12 + ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((8 / 3) : ℂ) * ζ ^ 24 - ζ ^ 30)) * Y 0 1
      + ((-((21 / 22) : ℂ) * ζ ^ 2 + ((12 / 11) : ℂ) * ζ ^ 6 - ((59 / 33) : ℂ) * ζ ^ 8 + ((43 / 33) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 18 + ((21 / 22) : ℂ) * ζ ^ 22 - ((43 / 33) : ℂ) * ζ ^ 24 + ((59 / 33) : ℂ) * ζ ^ 28 - ((45 / 22) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((4 / 11) : ℂ) - ((7 / 44) : ℂ) * ζ ^ 2 + ((6 / 11) : ℂ) * ζ ^ 6 + ((7 / 33) : ℂ) * ζ ^ 8 + ((7 / 33) : ℂ) * ζ ^ 12 - ((31 / 44) : ℂ) * ζ ^ 18 + ((7 / 44) : ℂ) * ζ ^ 22 - ((7 / 33) : ℂ) * ζ ^ 28 + ((3 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((34 / 33) : ℂ) - ((28 / 33) : ℂ) * ζ ^ 2 + ((19 / 33) : ℂ) * ζ ^ 6 + ((4 / 33) : ℂ) * ζ ^ 8 + ((4 / 33) : ℂ) * ζ ^ 12 - ((47 / 33) : ℂ) * ζ ^ 18 + ((28 / 33) : ℂ) * ζ ^ 22 - ((4 / 33) : ℂ) * ζ ^ 28 + ((19 / 66) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((46 / 33) : ℂ) - ((16 / 11) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 6 - ((49 / 33) : ℂ) * ζ ^ 8 + ((2 / 33) : ℂ) * ζ ^ 12 + ((46 / 33) : ℂ) * ζ ^ 18 + ((16 / 11) : ℂ) * ζ ^ 22 + ((23 / 66) : ℂ) * ζ ^ 24 + ((49 / 33) : ℂ) * ζ ^ 28 - ((23 / 22) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((67 / 66) : ℂ) - ((3 / 11) : ℂ) * ζ ^ 2 + ((41 / 66) : ℂ) * ζ ^ 6 + ((17 / 66) : ℂ) * ζ ^ 8 + ((13 / 33) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 18 + ((3 / 11) : ℂ) * ζ ^ 22 - ((4 / 33) : ℂ) * ζ ^ 24 - ((17 / 66) : ℂ) * ζ ^ 28 - ((13 / 33) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((2 / 33) : ℂ) + ((4 / 33) : ℂ) * ζ ^ 2 - ((31 / 33) : ℂ) * ζ ^ 6 - ((17 / 66) : ℂ) * ζ ^ 8 - ((17 / 66) : ℂ) * ζ ^ 12 + ((35 / 33) : ℂ) * ζ ^ 18 - ((4 / 33) : ℂ) * ζ ^ 22 + ((17 / 66) : ℂ) * ζ ^ 28 - ((31 / 66) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((25 / 22) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 2 + ((9 / 11) : ℂ) * ζ ^ 6 - ((21 / 22) : ℂ) * ζ ^ 8 - ((21 / 22) : ℂ) * ζ ^ 12 - ((41 / 44) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 22 + ((21 / 22) : ℂ) * ζ ^ 28 + ((9 / 22) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((1 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 22 + ((2 / 11) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 28)) * Y 4 5
      + ((((25 / 11) : ℂ) + ((59 / 44) : ℂ) * ζ ^ 6 - ((25 / 22) : ℂ) * ζ ^ 8 - ((23 / 11) : ℂ) * ζ ^ 12 - ((87 / 44) : ℂ) * ζ ^ 18 + ((2 / 11) : ℂ) * ζ ^ 24 + ((25 / 22) : ℂ) * ζ ^ 28 + ((59 / 44) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((4 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 28)) * Y 5 5) = 0 := by
  have previous :=
    row16_reducedY55_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation05
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((10 / 3) : ℂ) * ζ ^ 2 + ((4 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 12 - ((4 / 3) : ℂ) * ζ ^ 18 - ((10 / 3) : ℂ) * ζ ^ 22 + ((4 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28)) * equation
      - (
        ((-((4 / 11) : ℂ) - ((39 / 22) : ℂ) * ζ ^ 2 + ((4 / 11) : ℂ) * ζ ^ 4 + ((19 / 22) : ℂ) * ζ ^ 6 + ((13 / 22) : ℂ) * ζ ^ 8 + ((3 / 11) : ℂ) * ζ ^ 10 - ((5 / 11) : ℂ) * ζ ^ 12 + ((25 / 22) : ℂ) * ζ ^ 18 - ((3 / 11) : ℂ) * ζ ^ 20 - ((5 / 11) : ℂ) * ζ ^ 24)) * Y 0 0
        + ((((7 / 22) : ℂ) + ((15 / 22) : ℂ) * ζ ^ 2 - ((7 / 22) : ℂ) * ζ ^ 4 - ((10 / 11) : ℂ) * ζ ^ 6 + ((1 / 22) : ℂ) * ζ ^ 8 + ((15 / 22) : ℂ) * ζ ^ 10 + ((1 / 11) : ℂ) * ζ ^ 12 - ((27 / 22) : ℂ) * ζ ^ 14 - ((5 / 22) : ℂ) * ζ ^ 18 + ((6 / 11) : ℂ) * ζ ^ 20 + ((1 / 11) : ℂ) * ζ ^ 24)) * Y 0 1
        + ((((1 / 11) : ℂ) + ((7 / 11) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 4 - ((2 / 11) : ℂ) * ζ ^ 6 - ((3 / 11) : ℂ) * ζ ^ 8 - ((3 / 11) : ℂ) * ζ ^ 10 + ((2 / 11) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 14 - ((5 / 11) : ℂ) * ζ ^ 18 + ((2 / 11) : ℂ) * ζ ^ 24)) * Y 4 5
        + ((((4 / 11) : ℂ) + ((39 / 22) : ℂ) * ζ ^ 2 - ((4 / 11) : ℂ) * ζ ^ 4 - ((19 / 22) : ℂ) * ζ ^ 6 - ((13 / 22) : ℂ) * ζ ^ 8 - ((3 / 11) : ℂ) * ζ ^ 10 + ((5 / 11) : ℂ) * ζ ^ 12 - ((25 / 22) : ℂ) * ζ ^ 18 + ((3 / 11) : ℂ) * ζ ^ 20 + ((5 / 11) : ℂ) * ζ ^ 24)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY55_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((21 / 22) : ℂ) * ζ ^ 2 + ((12 / 11) : ℂ) * ζ ^ 6 - ((59 / 33) : ℂ) * ζ ^ 8 + ((43 / 33) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 18 + ((21 / 22) : ℂ) * ζ ^ 22 - ((43 / 33) : ℂ) * ζ ^ 24 + ((59 / 33) : ℂ) * ζ ^ 28 - ((45 / 22) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((4 / 11) : ℂ) - ((7 / 44) : ℂ) * ζ ^ 2 + ((6 / 11) : ℂ) * ζ ^ 6 + ((7 / 33) : ℂ) * ζ ^ 8 + ((7 / 33) : ℂ) * ζ ^ 12 - ((31 / 44) : ℂ) * ζ ^ 18 + ((7 / 44) : ℂ) * ζ ^ 22 - ((7 / 33) : ℂ) * ζ ^ 28 + ((3 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((34 / 33) : ℂ) - ((28 / 33) : ℂ) * ζ ^ 2 + ((19 / 33) : ℂ) * ζ ^ 6 + ((4 / 33) : ℂ) * ζ ^ 8 + ((4 / 33) : ℂ) * ζ ^ 12 - ((47 / 33) : ℂ) * ζ ^ 18 + ((28 / 33) : ℂ) * ζ ^ 22 - ((4 / 33) : ℂ) * ζ ^ 28 + ((19 / 66) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((46 / 33) : ℂ) - ((16 / 11) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 6 - ((49 / 33) : ℂ) * ζ ^ 8 + ((2 / 33) : ℂ) * ζ ^ 12 + ((46 / 33) : ℂ) * ζ ^ 18 + ((16 / 11) : ℂ) * ζ ^ 22 + ((23 / 66) : ℂ) * ζ ^ 24 + ((49 / 33) : ℂ) * ζ ^ 28 - ((23 / 22) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((67 / 66) : ℂ) - ((3 / 11) : ℂ) * ζ ^ 2 + ((41 / 66) : ℂ) * ζ ^ 6 + ((17 / 66) : ℂ) * ζ ^ 8 + ((13 / 33) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 18 + ((3 / 11) : ℂ) * ζ ^ 22 - ((4 / 33) : ℂ) * ζ ^ 24 - ((17 / 66) : ℂ) * ζ ^ 28 - ((13 / 33) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((2 / 33) : ℂ) + ((4 / 33) : ℂ) * ζ ^ 2 - ((31 / 33) : ℂ) * ζ ^ 6 - ((17 / 66) : ℂ) * ζ ^ 8 - ((17 / 66) : ℂ) * ζ ^ 12 + ((35 / 33) : ℂ) * ζ ^ 18 - ((4 / 33) : ℂ) * ζ ^ 22 + ((17 / 66) : ℂ) * ζ ^ 28 - ((31 / 66) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((25 / 22) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 2 + ((9 / 11) : ℂ) * ζ ^ 6 - ((21 / 22) : ℂ) * ζ ^ 8 - ((21 / 22) : ℂ) * ζ ^ 12 - ((41 / 44) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 22 + ((21 / 22) : ℂ) * ζ ^ 28 + ((9 / 22) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((1 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 22 + ((2 / 11) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 28)) * Y 4 5
      + ((((25 / 11) : ℂ) + ((59 / 44) : ℂ) * ζ ^ 6 - ((25 / 22) : ℂ) * ζ ^ 8 - ((23 / 11) : ℂ) * ζ ^ 12 - ((87 / 44) : ℂ) * ζ ^ 18 + ((2 / 11) : ℂ) * ζ ^ 24 + ((25 / 22) : ℂ) * ζ ^ 28 + ((59 / 44) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((4 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 28)) * Y 5 5
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY55_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28 - ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-(1 : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 4 - ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 16 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((5 / 3) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 + ((5 / 3) : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 6 - ((11 / 6) : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 10 + ((7 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((7 / 2) : ℂ) * ζ ^ 16 - ζ ^ 18 + (2 : ℂ) * ζ ^ 20 + ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 + ((4 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((1 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 - ((5 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 + ((2 / 3) : ℂ) * ζ ^ 28)) * Y 6 7
        + (((1 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ζ ^ 4 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY55_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((5 / 6) : ℂ) * ζ ^ 2 + ((4 / 3) : ℂ) * ζ ^ 6 - ((13 / 11) : ℂ) * ζ ^ 8 + ((85 / 66) : ℂ) * ζ ^ 12 + ((5 / 12) : ℂ) * ζ ^ 18 + ((5 / 6) : ℂ) * ζ ^ 22 - ((85 / 66) : ℂ) * ζ ^ 24 + ((13 / 11) : ℂ) * ζ ^ 28 - ((13 / 6) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((23 / 33) : ℂ) - ((67 / 132) : ℂ) * ζ ^ 2 + ((37 / 33) : ℂ) * ζ ^ 6 + ((25 / 66) : ℂ) * ζ ^ 8 + ((25 / 66) : ℂ) * ζ ^ 12 - ((215 / 132) : ℂ) * ζ ^ 18 + ((67 / 132) : ℂ) * ζ ^ 22 - ((25 / 66) : ℂ) * ζ ^ 28 + ((37 / 66) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((15 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 28)) * Y 2 2
      + ((((46 / 33) : ℂ) - ((16 / 11) : ℂ) * ζ ^ 2 + ((1 / 11) : ℂ) * ζ ^ 6 - ((49 / 33) : ℂ) * ζ ^ 8 + ((2 / 33) : ℂ) * ζ ^ 12 + ((46 / 33) : ℂ) * ζ ^ 18 + ((16 / 11) : ℂ) * ζ ^ 22 + ((23 / 66) : ℂ) * ζ ^ 24 + ((49 / 33) : ℂ) * ζ ^ 28 - ((23 / 22) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((2 / 33) : ℂ) + ((4 / 33) : ℂ) * ζ ^ 2 - ((31 / 33) : ℂ) * ζ ^ 6 - ((17 / 66) : ℂ) * ζ ^ 8 - ((17 / 66) : ℂ) * ζ ^ 12 + ((35 / 33) : ℂ) * ζ ^ 18 - ((4 / 33) : ℂ) * ζ ^ 22 + ((17 / 66) : ℂ) * ζ ^ 28 - ((31 / 66) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((25 / 22) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 2 + ((9 / 11) : ℂ) * ζ ^ 6 - ((21 / 22) : ℂ) * ζ ^ 8 - ((21 / 22) : ℂ) * ζ ^ 12 - ((41 / 44) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 22 + ((21 / 22) : ℂ) * ζ ^ 28 + ((9 / 22) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((1 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 22 + ((2 / 11) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 28)) * Y 4 5
      + ((((25 / 11) : ℂ) + ((59 / 44) : ℂ) * ζ ^ 6 - ((25 / 22) : ℂ) * ζ ^ 8 - ((23 / 11) : ℂ) * ζ ^ 12 - ((87 / 44) : ℂ) * ζ ^ 18 + ((2 / 11) : ℂ) * ζ ^ 24 + ((25 / 22) : ℂ) * ζ ^ 28 + ((59 / 44) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((4 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 28)) * Y 5 5
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY55_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation12
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((20 / 33) : ℂ) * ζ ^ 2 - ((6 / 11) : ℂ) * ζ ^ 6 - ((8 / 33) : ℂ) * ζ ^ 8 + ((20 / 33) : ℂ) * ζ ^ 12 + ((10 / 33) : ℂ) * ζ ^ 18 + ((20 / 33) : ℂ) * ζ ^ 22 - ((20 / 33) : ℂ) * ζ ^ 24 + ((8 / 33) : ℂ) * ζ ^ 28 - ((2 / 33) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((2 / 11) : ℂ) * ζ ^ 2 + ((10 / 33) : ℂ) * ζ ^ 4 - ((5 / 33) : ℂ) * ζ ^ 6 - ((7 / 33) : ℂ) * ζ ^ 8 + ((3 / 11) : ℂ) * ζ ^ 10 + ((13 / 66) : ℂ) * ζ ^ 12 - ((3 / 11) : ℂ) * ζ ^ 14 + ((7 / 66) : ℂ) * ζ ^ 16 - ((1 / 11) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 20 + ((7 / 33) : ℂ) * ζ ^ 22 - ((1 / 66) : ℂ) * ζ ^ 24 - ((2 / 33) : ℂ) * ζ ^ 26 + ((1 / 66) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((1 / 3) : ℂ) + ((23 / 66) : ℂ) * ζ ^ 2 - ((7 / 11) : ℂ) * ζ ^ 4 - ((61 / 66) : ℂ) * ζ ^ 6 + ((1 / 22) : ℂ) * ζ ^ 8 + ((53 / 66) : ℂ) * ζ ^ 10 - ((1 / 66) : ℂ) * ζ ^ 12 - ((4 / 11) : ℂ) * ζ ^ 14 - ((19 / 66) : ℂ) * ζ ^ 16 + ((8 / 11) : ℂ) * ζ ^ 18 + ((19 / 33) : ℂ) * ζ ^ 20 - ((28 / 33) : ℂ) * ζ ^ 22 + ((2 / 33) : ℂ) * ζ ^ 24 + ((8 / 33) : ℂ) * ζ ^ 26 - ((2 / 33) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((1 / 3) : ℂ) - ((23 / 66) : ℂ) * ζ ^ 2 + ((7 / 11) : ℂ) * ζ ^ 4 + ((61 / 66) : ℂ) * ζ ^ 6 - ((1 / 22) : ℂ) * ζ ^ 8 - ((53 / 66) : ℂ) * ζ ^ 10 + ((1 / 66) : ℂ) * ζ ^ 12 + ((4 / 11) : ℂ) * ζ ^ 14 + ((19 / 66) : ℂ) * ζ ^ 16 - ((8 / 11) : ℂ) * ζ ^ 18 - ((19 / 33) : ℂ) * ζ ^ 20 + ((28 / 33) : ℂ) * ζ ^ 22 - ((2 / 33) : ℂ) * ζ ^ 24 - ((8 / 33) : ℂ) * ζ ^ 26 + ((2 / 33) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((67 / 66) : ℂ) - ((19 / 33) : ℂ) * ζ ^ 2 + ((67 / 66) : ℂ) * ζ ^ 4 + ((61 / 66) : ℂ) * ζ ^ 6 - ((14 / 33) : ℂ) * ζ ^ 8 - ((61 / 66) : ℂ) * ζ ^ 10 + ((17 / 33) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 - ((17 / 33) : ℂ) * ζ ^ 16 - ((25 / 66) : ℂ) * ζ ^ 18 - ((1 / 11) : ℂ) * ζ ^ 20 + ((25 / 66) : ℂ) * ζ ^ 22 - ((1 / 33) : ℂ) * ζ ^ 24 - ((4 / 33) : ℂ) * ζ ^ 26 + ((1 / 33) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY55_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((23 / 22) : ℂ) * ζ ^ 2 + ((10 / 11) : ℂ) * ζ ^ 6 - ((59 / 33) : ℂ) * ζ ^ 8 + ((43 / 33) : ℂ) * ζ ^ 12 + ((23 / 44) : ℂ) * ζ ^ 18 + ((23 / 22) : ℂ) * ζ ^ 22 - ((43 / 33) : ℂ) * ζ ^ 24 + ((59 / 33) : ℂ) * ζ ^ 28 - ((43 / 22) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((7 / 11) : ℂ) - ((17 / 44) : ℂ) * ζ ^ 2 + ((2 / 11) : ℂ) * ζ ^ 6 + ((4 / 33) : ℂ) * ζ ^ 8 + ((4 / 33) : ℂ) * ζ ^ 12 - ((25 / 44) : ℂ) * ζ ^ 18 + ((17 / 44) : ℂ) * ζ ^ 22 - ((4 / 33) : ℂ) * ζ ^ 28 + ((1 / 11) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((15 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 28)) * Y 2 2
      + ((((19 / 22) : ℂ) - ((15 / 11) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 6 - ((15 / 11) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 + ((19 / 22) : ℂ) * ζ ^ 18 + ((15 / 11) : ℂ) * ζ ^ 22 + ((21 / 22) : ℂ) * ζ ^ 24 + ((15 / 11) : ℂ) * ζ ^ 28 + ((1 / 11) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((25 / 22) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 2 + ((9 / 11) : ℂ) * ζ ^ 6 - ((21 / 22) : ℂ) * ζ ^ 8 - ((21 / 22) : ℂ) * ζ ^ 12 - ((41 / 44) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 22 + ((21 / 22) : ℂ) * ζ ^ 28 + ((9 / 22) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((1 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 22 + ((2 / 11) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 28)) * Y 4 5
      + ((((25 / 11) : ℂ) + ((59 / 44) : ℂ) * ζ ^ 6 - ((25 / 22) : ℂ) * ζ ^ 8 - ((23 / 11) : ℂ) * ζ ^ 12 - ((87 / 44) : ℂ) * ζ ^ 18 + ((2 / 11) : ℂ) * ζ ^ 24 + ((25 / 22) : ℂ) * ζ ^ 28 + ((59 / 44) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((4 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 28)) * Y 5 5
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY55_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation13
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((18 / 11) : ℂ) - ((8 / 11) : ℂ) * ζ ^ 2 - ((38 / 33) : ℂ) * ζ ^ 6 + ((8 / 11) : ℂ) * ζ ^ 8 - ((2 / 33) : ℂ) * ζ ^ 12 - ((2 / 33) : ℂ) * ζ ^ 18 + ((8 / 11) : ℂ) * ζ ^ 22 - ((38 / 33) : ℂ) * ζ ^ 24 - ((8 / 11) : ℂ) * ζ ^ 28 - ((18 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((9 / 22) : ℂ) + ((13 / 33) : ℂ) * ζ ^ 2 - ((9 / 22) : ℂ) * ζ ^ 4 - ((1 / 11) : ℂ) * ζ ^ 6 + ((8 / 33) : ℂ) * ζ ^ 8 - ((1 / 11) : ℂ) * ζ ^ 10 - ((4 / 33) : ℂ) * ζ ^ 12 + ((25 / 66) : ℂ) * ζ ^ 14 + ((10 / 33) : ℂ) * ζ ^ 16 + ((5 / 22) : ℂ) * ζ ^ 18 + ((7 / 66) : ℂ) * ζ ^ 20 - ((9 / 22) : ℂ) * ζ ^ 22 + ((2 / 11) : ℂ) * ζ ^ 24 + ((9 / 22) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((25 / 33) : ℂ) + ((8 / 33) : ℂ) * ζ ^ 2 - ((25 / 33) : ℂ) * ζ ^ 4 + ((1 / 22) : ℂ) * ζ ^ 6 + ((7 / 66) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 10 - ((49 / 66) : ℂ) * ζ ^ 12 + ((31 / 66) : ℂ) * ζ ^ 14 + ((49 / 66) : ℂ) * ζ ^ 16 - ((67 / 66) : ℂ) * ζ ^ 18 + ((1 / 11) : ℂ) * ζ ^ 20 + ((67 / 66) : ℂ) * ζ ^ 22 + ((9 / 11) : ℂ) * ζ ^ 24 - ((4 / 11) : ℂ) * ζ ^ 26 - ((9 / 11) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((35 / 66) : ℂ) + ((8 / 11) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 4 - ((8 / 11) : ℂ) * ζ ^ 6 + ((53 / 66) : ℂ) * ζ ^ 8 + ((4 / 11) : ℂ) * ζ ^ 10 - ((1 / 66) : ℂ) * ζ ^ 12 + ((13 / 33) : ℂ) * ζ ^ 14 + ((25 / 66) : ℂ) * ζ ^ 16 - ((26 / 33) : ℂ) * ζ ^ 18 + ((1 / 11) : ℂ) * ζ ^ 20 + ((14 / 33) : ℂ) * ζ ^ 22 - ((18 / 11) : ℂ) * ζ ^ 24 + ((8 / 11) : ℂ) * ζ ^ 26 + ((18 / 11) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((25 / 33) : ℂ) - ((8 / 33) : ℂ) * ζ ^ 2 + ((25 / 33) : ℂ) * ζ ^ 4 - ((1 / 22) : ℂ) * ζ ^ 6 - ((7 / 66) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 10 + ((49 / 66) : ℂ) * ζ ^ 12 - ((31 / 66) : ℂ) * ζ ^ 14 - ((49 / 66) : ℂ) * ζ ^ 16 + ((67 / 66) : ℂ) * ζ ^ 18 - ((1 / 11) : ℂ) * ζ ^ 20 - ((67 / 66) : ℂ) * ζ ^ 22 - ((9 / 11) : ℂ) * ζ ^ 24 + ((4 / 11) : ℂ) * ζ ^ 26 + ((9 / 11) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY55_combinationStep09
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 2) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 12 - ((1 / 6) : ℂ) * ζ ^ 24 + ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((15 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 28)) * Y 2 2
      + ((((19 / 22) : ℂ) - ((15 / 11) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 6 - ((15 / 11) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 + ((19 / 22) : ℂ) * ζ ^ 18 + ((15 / 11) : ℂ) * ζ ^ 22 + ((21 / 22) : ℂ) * ζ ^ 24 + ((15 / 11) : ℂ) * ζ ^ 28 + ((1 / 11) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((1 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 22 + ((2 / 11) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 28)) * Y 4 5
      + ((-((4 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 28)) * Y 5 5
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY55_combinationStep08 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) * ζ ^ 2 + ((4 / 3) : ℂ) * ζ ^ 6 - ((10 / 3) : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 12 + ζ ^ 18 + (2 : ℂ) * ζ ^ 22 - (2 : ℂ) * ζ ^ 24 + ((10 / 3) : ℂ) * ζ ^ 28 - ((10 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((4 / 11) : ℂ) * ζ ^ 2 + ((7 / 22) : ℂ) * ζ ^ 6 + ((2 / 11) : ℂ) * ζ ^ 8 - ((13 / 22) : ℂ) * ζ ^ 10 + ((3 / 11) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 14 - ((8 / 11) : ℂ) * ζ ^ 16 + ((2 / 11) : ℂ) * ζ ^ 18 + ((8 / 11) : ℂ) * ζ ^ 20 - ((5 / 11) : ℂ) * ζ ^ 22 - ((5 / 11) : ℂ) * ζ ^ 24 + ((5 / 11) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((25 / 22) : ℂ) - ((13 / 44) : ℂ) * ζ ^ 2 + ((25 / 22) : ℂ) * ζ ^ 4 - ((1 / 4) : ℂ) * ζ ^ 6 - ((19 / 22) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 10 + ((12 / 11) : ℂ) * ζ ^ 12 - ((3 / 11) : ℂ) * ζ ^ 14 - ((12 / 11) : ℂ) * ζ ^ 16 + ((15 / 22) : ℂ) * ζ ^ 18 + ((15 / 22) : ℂ) * ζ ^ 20 - ((15 / 22) : ℂ) * ζ ^ 22)) * Y 1 1
        + ((((25 / 22) : ℂ) + ((13 / 44) : ℂ) * ζ ^ 2 - ((25 / 22) : ℂ) * ζ ^ 4 + ((1 / 4) : ℂ) * ζ ^ 6 + ((19 / 22) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 10 - ((12 / 11) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 14 + ((12 / 11) : ℂ) * ζ ^ 16 - ((15 / 22) : ℂ) * ζ ^ 18 - ((15 / 22) : ℂ) * ζ ^ 20 + ((15 / 22) : ℂ) * ζ ^ 22)) * Y 4 4
        + ((((25 / 11) : ℂ) + ((9 / 22) : ℂ) * ζ ^ 2 - ((25 / 11) : ℂ) * ζ ^ 4 + ((29 / 44) : ℂ) * ζ ^ 6 + ((20 / 11) : ℂ) * ζ ^ 8 - ((35 / 44) : ℂ) * ζ ^ 10 - ((45 / 22) : ℂ) * ζ ^ 12 + ((27 / 44) : ℂ) * ζ ^ 14 + ((20 / 11) : ℂ) * ζ ^ 16 - ((14 / 11) : ℂ) * ζ ^ 18 - ζ ^ 20 + ((25 / 22) : ℂ) * ζ ^ 22 - ((5 / 22) : ℂ) * ζ ^ 24 + ((5 / 22) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY55_combinationStep10
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((15 / 11) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 22) : ℂ) * ζ ^ 28)) * Y 2 2
      + ((((19 / 22) : ℂ) - ((15 / 11) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 6 - ((15 / 11) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 + ((19 / 22) : ℂ) * ζ ^ 18 + ((15 / 11) : ℂ) * ζ ^ 22 + ((21 / 22) : ℂ) * ζ ^ 24 + ((15 / 11) : ℂ) * ζ ^ 28 + ((1 / 11) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((1 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 11) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 22 + ((2 / 11) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 28)) * Y 4 5
      + ((-((4 / 11) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 22) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 28)) * Y 5 5
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY55_combinationStep09 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((2 : ℂ) - ((4 / 3) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 22 + ((4 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 2) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((1 / 2) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 - ((3 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 22 - ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26 + ζ ^ 28)) * Y 1 1
        + ((-((7 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((7 / 6) : ℂ) * ζ ^ 6 - ((7 / 6) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 14 - ((5 / 6) : ℂ) * ζ ^ 16 - ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 26 - (2 : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((1 / 2) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 16 + ((3 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 22 + ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 - ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY55_combinationStep11
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 5 5
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY55_combinationStep10 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation25
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) * ζ ^ 2 + (4 : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 22 - (4 : ℂ) * ζ ^ 24 - (4 : ℂ) * ζ ^ 28)) * equation
      - (
        ((((15 / 11) : ℂ) - ((9 / 22) : ℂ) * ζ ^ 2 - ((15 / 11) : ℂ) * ζ ^ 4 + ((9 / 22) : ℂ) * ζ ^ 6 + ((39 / 22) : ℂ) * ζ ^ 8 - ((5 / 11) : ℂ) * ζ ^ 10 - ((6 / 11) : ℂ) * ζ ^ 12 - ((12 / 11) : ℂ) * ζ ^ 14 + ((7 / 11) : ℂ) * ζ ^ 16 - ((1 / 22) : ℂ) * ζ ^ 18 - ((2 / 11) : ℂ) * ζ ^ 20 + ((1 / 11) : ℂ) * ζ ^ 24 + ((14 / 11) : ℂ) * ζ ^ 26)) * Y 2 2
        + ((((19 / 22) : ℂ) - ((5 / 11) : ℂ) * ζ ^ 2 - ((23 / 11) : ℂ) * ζ ^ 4 + ((21 / 22) : ℂ) * ζ ^ 6 - ((37 / 22) : ℂ) * ζ ^ 8 + ((3 / 11) : ℂ) * ζ ^ 10 + ((47 / 22) : ℂ) * ζ ^ 12 + ((8 / 11) : ℂ) * ζ ^ 14 - ((10 / 11) : ℂ) * ζ ^ 16 + ((27 / 22) : ℂ) * ζ ^ 18 + ((23 / 11) : ℂ) * ζ ^ 20 + ((27 / 11) : ℂ) * ζ ^ 24 - ((20 / 11) : ℂ) * ζ ^ 26)) * Y 2 3
        + ((-((1 / 11) : ℂ) - ((1 / 22) : ℂ) * ζ ^ 2 + ((3 / 22) : ℂ) * ζ ^ 4 + ((1 / 22) : ℂ) * ζ ^ 6 + ((25 / 22) : ℂ) * ζ ^ 8 + ((2 / 11) : ℂ) * ζ ^ 10 - ((8 / 11) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((3 / 22) : ℂ) * ζ ^ 16 + ((5 / 22) : ℂ) * ζ ^ 18 - ((3 / 22) : ℂ) * ζ ^ 20 - ((7 / 11) : ℂ) * ζ ^ 24 + ((3 / 11) : ℂ) * ζ ^ 26)) * Y 4 5
        + ((-((15 / 11) : ℂ) + ((9 / 22) : ℂ) * ζ ^ 2 + ((15 / 11) : ℂ) * ζ ^ 4 - ((9 / 22) : ℂ) * ζ ^ 6 - ((39 / 22) : ℂ) * ζ ^ 8 + ((5 / 11) : ℂ) * ζ ^ 10 + ((6 / 11) : ℂ) * ζ ^ 12 + ((12 / 11) : ℂ) * ζ ^ 14 - ((7 / 11) : ℂ) * ζ ^ 16 + ((1 / 22) : ℂ) * ζ ^ 18 + ((2 / 11) : ℂ) * ζ ^ 20 - ((1 / 11) : ℂ) * ζ ^ 24 - ((14 / 11) : ℂ) * ζ ^ 26)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY55
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 5 5 = Y 7 7 := by
  have reduced :=
    row16_reducedY55_combinationStep11 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row16_reducedY66_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((43 / 12) : ℂ) - ((7 / 2) : ℂ) * ζ ^ 2 - (2 : ℂ) * ζ ^ 6 + ((31 / 4) : ℂ) * ζ ^ 12 + (5 : ℂ) * ζ ^ 18 + ((7 / 2) : ℂ) * ζ ^ 22 - ((43 / 12) : ℂ) * ζ ^ 24 - (7 : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-(3 : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 - ((25 / 6) : ℂ) * ζ ^ 8 + ((43 / 12) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 + (3 : ℂ) * ζ ^ 22 - ((43 / 12) : ℂ) * ζ ^ 24 + ((25 / 6) : ℂ) * ζ ^ 28 - (5 : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((136 / 3) : ℂ) + (6 : ℂ) * ζ ^ 2 - (28 : ℂ) * ζ ^ 6 + (31 : ℂ) * ζ ^ 8 + (31 : ℂ) * ζ ^ 12 + (34 : ℂ) * ζ ^ 18 - (6 : ℂ) * ζ ^ 22 - (31 : ℂ) * ζ ^ 28 - (14 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((31 / 4) : ℂ) + (5 : ℂ) * ζ ^ 2 + ((31 / 4) : ℂ) * ζ ^ 4 - (10 : ℂ) * ζ ^ 6 + (10 : ℂ) * ζ ^ 10 - ((31 / 4) : ℂ) * ζ ^ 12 - (5 : ℂ) * ζ ^ 14 + ((31 / 4) : ℂ) * ζ ^ 16 + ((7 / 2) : ℂ) * ζ ^ 18 - ((31 / 4) : ℂ) * ζ ^ 20 - ((7 / 2) : ℂ) * ζ ^ 22)) * Y 0 1
        + (((3 : ℂ) * ζ ^ 2 - (5 : ℂ) * ζ ^ 6 + ((31 / 2) : ℂ) * ζ ^ 8 + ((7 / 2) : ℂ) * ζ ^ 10 - ((31 / 4) : ℂ) * ζ ^ 12 + (5 : ℂ) * ζ ^ 14 - ((3 / 2) : ℂ) * ζ ^ 18 - ((31 / 4) : ℂ) * ζ ^ 24 - ((7 / 2) : ℂ) * ζ ^ 26)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY66_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((5 / 4) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((-((73 / 12) : ℂ) - (2 : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 6 + ((23 / 2) : ℂ) * ζ ^ 12 + ((7 / 2) : ℂ) * ζ ^ 18 + (2 : ℂ) * ζ ^ 22 - ((73 / 12) : ℂ) * ζ ^ 24 - (4 : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-(3 : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 - ((25 / 6) : ℂ) * ζ ^ 8 + ((43 / 12) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 + (3 : ℂ) * ζ ^ 22 - ((43 / 12) : ℂ) * ζ ^ 24 + ((25 / 6) : ℂ) * ζ ^ 28 - (5 : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((5 / 4) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY66_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((5 : ℂ) - (2 : ℂ) * ζ ^ 2 - ((25 / 3) : ℂ) * ζ ^ 12 + (4 : ℂ) * ζ ^ 18 + (2 : ℂ) * ζ ^ 22 + (5 : ℂ) * ζ ^ 24 - (4 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((5 / 4) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((5 / 4) : ℂ) * ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 18 - ((5 / 4) : ℂ) * ζ ^ 20 + ζ ^ 26)) * Y 0 0
        + ((((5 / 2) : ℂ) - ((3 / 2) : ℂ) * ζ ^ 2 - ((5 / 2) : ℂ) * ζ ^ 4 + ((25 / 4) : ℂ) * ζ ^ 8 - ((3 / 2) : ℂ) * ζ ^ 10 - ((15 / 4) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 14 + ((15 / 4) : ℂ) * ζ ^ 16 + ((3 / 2) : ℂ) * ζ ^ 18 - ((15 / 4) : ℂ) * ζ ^ 20 - (3 : ℂ) * ζ ^ 22 + (3 : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((5 / 4) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((5 / 4) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 18 + ((5 / 4) : ℂ) * ζ ^ 20 - ζ ^ 26)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY66_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-(2 : ℂ) + ζ ^ 2 - (2 : ℂ) * ζ ^ 6 + ((5 / 3) : ℂ) * ζ ^ 8 + ((5 / 3) : ℂ) * ζ ^ 12 + (3 : ℂ) * ζ ^ 18 - ζ ^ 22 - ((5 / 3) : ℂ) * ζ ^ 28 - ζ ^ 30)) * Y 0 0
      + ((-((16 / 3) : ℂ) - ζ ^ 2 + (9 : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 + ζ ^ 22 - ((16 / 3) : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-(3 : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 - ((25 / 6) : ℂ) * ζ ^ 8 + ((43 / 12) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 + (3 : ℂ) * ζ ^ 22 - ((43 / 12) : ℂ) * ζ ^ 24 + ((25 / 6) : ℂ) * ζ ^ 28 - (5 : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((5 / 4) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((13 / 4) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 - ((5 / 2) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 12 - ((5 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 2) : ℂ) * ζ ^ 28 + ζ ^ 30)) * Y 4 4
      + ((((13 / 2) : ℂ) + ((7 / 2) : ℂ) * ζ ^ 6 - ((13 / 4) : ℂ) * ζ ^ 8 - ((23 / 4) : ℂ) * ζ ^ 12 - ((11 / 2) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 24 + ((13 / 4) : ℂ) * ζ ^ 28 + ((7 / 2) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY66_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((19 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 + ((16 / 3) : ℂ) * ζ ^ 6 - (8 : ℂ) * ζ ^ 8 - (8 : ℂ) * ζ ^ 12 - (6 : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + (8 : ℂ) * ζ ^ 28 + ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((12 / 11) : ℂ) - ((3 / 11) : ℂ) * ζ ^ 2 - ((12 / 11) : ℂ) * ζ ^ 4 + ((5 / 11) : ℂ) * ζ ^ 6 + ((24 / 11) : ℂ) * ζ ^ 8 - ((6 / 11) : ℂ) * ζ ^ 10 + ((10 / 11) : ℂ) * ζ ^ 14 - ((12 / 11) : ℂ) * ζ ^ 16 - ((5 / 11) : ℂ) * ζ ^ 18 + ((12 / 11) : ℂ) * ζ ^ 20 + ((4 / 11) : ℂ) * ζ ^ 22 - ((12 / 11) : ℂ) * ζ ^ 24 - ((4 / 11) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((6 / 11) : ℂ) - ((25 / 22) : ℂ) * ζ ^ 2 - ((6 / 11) : ℂ) * ζ ^ 4 + ((19 / 11) : ℂ) * ζ ^ 6 - ((12 / 11) : ℂ) * ζ ^ 8 - ((19 / 11) : ℂ) * ζ ^ 10 + ((18 / 11) : ℂ) * ζ ^ 12 + ((15 / 22) : ℂ) * ζ ^ 14 - ((18 / 11) : ℂ) * ζ ^ 16 - ((6 / 11) : ℂ) * ζ ^ 18 + ((18 / 11) : ℂ) * ζ ^ 20 + ((6 / 11) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((-((12 / 11) : ℂ) + ((3 / 11) : ℂ) * ζ ^ 2 + ((12 / 11) : ℂ) * ζ ^ 4 - ((5 / 11) : ℂ) * ζ ^ 6 - ((24 / 11) : ℂ) * ζ ^ 8 + ((6 / 11) : ℂ) * ζ ^ 10 - ((10 / 11) : ℂ) * ζ ^ 14 + ((12 / 11) : ℂ) * ζ ^ 16 + ((5 / 11) : ℂ) * ζ ^ 18 - ((12 / 11) : ℂ) * ζ ^ 20 - ((4 / 11) : ℂ) * ζ ^ 22 + ((12 / 11) : ℂ) * ζ ^ 24 + ((4 / 11) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((24 / 11) : ℂ) - ((5 / 11) : ℂ) * ζ ^ 2 + ((24 / 11) : ℂ) * ζ ^ 4 + ((13 / 22) : ℂ) * ζ ^ 6 - ((72 / 11) : ℂ) * ζ ^ 8 - ((4 / 11) : ℂ) * ζ ^ 10 + ((18 / 11) : ℂ) * ζ ^ 12 - ((35 / 22) : ℂ) * ζ ^ 14 + ((12 / 11) : ℂ) * ζ ^ 16 + ((13 / 22) : ℂ) * ζ ^ 18 - ((12 / 11) : ℂ) * ζ ^ 20 - ((4 / 11) : ℂ) * ζ ^ 22 + ((30 / 11) : ℂ) * ζ ^ 24 + ((10 / 11) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY66_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((8 / 3) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((9 / 2) : ℂ) * ζ ^ 12 + ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((8 / 3) : ℂ) * ζ ^ 24 - ζ ^ 30)) * Y 0 1
      + ((-(3 : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 - ((25 / 6) : ℂ) * ζ ^ 8 + ((43 / 12) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 + (3 : ℂ) * ζ ^ 22 - ((43 / 12) : ℂ) * ζ ^ 24 + ((25 / 6) : ℂ) * ζ ^ 28 - (5 : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((5 / 4) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((13 / 4) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 - ((5 / 2) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 12 - ((5 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 2) : ℂ) * ζ ^ 28 + ζ ^ 30)) * Y 4 4
      + ((((13 / 2) : ℂ) + ((7 / 2) : ℂ) * ζ ^ 6 - ((13 / 4) : ℂ) * ζ ^ 8 - ((23 / 4) : ℂ) * ζ ^ 12 - ((11 / 2) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 24 + ((13 / 4) : ℂ) * ζ ^ 28 + ((7 / 2) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 6 6
      + ((-((4 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 30)) * Y 7 6) = 0 := by
  have previous :=
    row16_reducedY66_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation06
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - (4 : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 12 + ((10 / 3) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 6) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 6 - ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 26 - ((1 / 2) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((8 / 3) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 + (3 : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((7 / 2) : ℂ) * ζ ^ 12 + ((1 / 6) : ℂ) * ζ ^ 14 - ((19 / 6) : ℂ) * ζ ^ 16 - ((1 / 3) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 22 - (2 : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26 + (2 : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((1 / 6) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 6 + ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 6 6
        + ((((7 / 6) : ℂ) - ((5 / 6) : ℂ) * ζ ^ 2 - ((7 / 6) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 6 + ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 16 - ((1 / 3) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 26)) * Y 7 6)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY66_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-(3 : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 - ((25 / 6) : ℂ) * ζ ^ 8 + ((43 / 12) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 + (3 : ℂ) * ζ ^ 22 - ((43 / 12) : ℂ) * ζ ^ 24 + ((25 / 6) : ℂ) * ζ ^ 28 - (5 : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((5 / 4) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((13 / 4) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 6 - ((5 / 2) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 12 - ((5 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 2) : ℂ) * ζ ^ 28 + ζ ^ 30)) * Y 4 4
      + ((((13 / 2) : ℂ) + ((7 / 2) : ℂ) * ζ ^ 6 - ((13 / 4) : ℂ) * ζ ^ 8 - ((23 / 4) : ℂ) * ζ ^ 12 - ((11 / 2) : ℂ) * ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 24 + ((13 / 4) : ℂ) * ζ ^ 28 + ((7 / 2) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 6 6
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((4 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 30)) * Y 7 6
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY66_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28 - ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-(1 : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 4 - ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 16 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((5 / 3) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 + ((5 / 3) : ℂ) * ζ ^ 4 + (2 : ℂ) * ζ ^ 6 - ((11 / 6) : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 10 + ((7 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((7 / 2) : ℂ) * ζ ^ 16 - ζ ^ 18 + (2 : ℂ) * ζ ^ 20 + ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 + ((4 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((1 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 - ((5 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 + ((2 / 3) : ℂ) * ζ ^ 28)) * Y 6 7
        + (((1 : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ζ ^ 4 + ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY66_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((ζ ^ 6 - ((5 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 3) : ℂ) * ζ ^ 24 + ((5 / 3) : ℂ) * ζ ^ 28 - ζ ^ 30)) * Y 1 0
      + (((2 : ℂ) - ζ ^ 2 + (2 : ℂ) * ζ ^ 6 - ((5 / 3) : ℂ) * ζ ^ 8 - ((5 / 3) : ℂ) * ζ ^ 12 - (3 : ℂ) * ζ ^ 18 + ζ ^ 22 + ((5 / 3) : ℂ) * ζ ^ 28 + ζ ^ 30)) * Y 1 1
      + ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 6 6
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((4 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 30)) * Y 7 6
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY66_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((20 / 3) : ℂ) * ζ ^ 2 + ((8 / 3) : ℂ) * ζ ^ 6 - (8 : ℂ) * ζ ^ 8 + ((19 / 3) : ℂ) * ζ ^ 12 + ((10 / 3) : ℂ) * ζ ^ 18 + ((20 / 3) : ℂ) * ζ ^ 22 - ((19 / 3) : ℂ) * ζ ^ 24 + (8 : ℂ) * ζ ^ 28 - ((28 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((8 / 11) : ℂ) * ζ ^ 2 + ((9 / 11) : ℂ) * ζ ^ 6 + ((5 / 22) : ℂ) * ζ ^ 8 - ((19 / 11) : ℂ) * ζ ^ 10 + ((19 / 22) : ℂ) * ζ ^ 12 + ((5 / 11) : ℂ) * ζ ^ 14 - ((43 / 22) : ℂ) * ζ ^ 16 + ((4 / 11) : ℂ) * ζ ^ 18 + ((43 / 22) : ℂ) * ζ ^ 20 - ((14 / 11) : ℂ) * ζ ^ 22 - ((12 / 11) : ℂ) * ζ ^ 24 + ((14 / 11) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((13 / 4) : ℂ) - ((19 / 22) : ℂ) * ζ ^ 2 + ((13 / 4) : ℂ) * ζ ^ 4 - ((13 / 22) : ℂ) * ζ ^ 6 - ((105 / 44) : ℂ) * ζ ^ 8 + ((13 / 22) : ℂ) * ζ ^ 10 + ((129 / 44) : ℂ) * ζ ^ 12 - ((6 / 11) : ℂ) * ζ ^ 14 - ((129 / 44) : ℂ) * ζ ^ 16 + ((21 / 11) : ℂ) * ζ ^ 18 + ((18 / 11) : ℂ) * ζ ^ 20 - ((21 / 11) : ℂ) * ζ ^ 22)) * Y 1 1
        + ((((13 / 4) : ℂ) + ((19 / 22) : ℂ) * ζ ^ 2 - ((13 / 4) : ℂ) * ζ ^ 4 + ((13 / 22) : ℂ) * ζ ^ 6 + ((105 / 44) : ℂ) * ζ ^ 8 - ((13 / 22) : ℂ) * ζ ^ 10 - ((129 / 44) : ℂ) * ζ ^ 12 + ((6 / 11) : ℂ) * ζ ^ 14 + ((129 / 44) : ℂ) * ζ ^ 16 - ((21 / 11) : ℂ) * ζ ^ 18 - ((18 / 11) : ℂ) * ζ ^ 20 + ((21 / 11) : ℂ) * ζ ^ 22)) * Y 4 4
        + ((((13 / 2) : ℂ) + ((15 / 11) : ℂ) * ζ ^ 2 - ((13 / 2) : ℂ) * ζ ^ 4 + ((35 / 22) : ℂ) * ζ ^ 6 + ((215 / 44) : ℂ) * ζ ^ 8 - ((45 / 22) : ℂ) * ζ ^ 10 - ((239 / 44) : ℂ) * ζ ^ 12 + ((29 / 22) : ℂ) * ζ ^ 14 + ((215 / 44) : ℂ) * ζ ^ 16 - ((40 / 11) : ℂ) * ζ ^ 18 - ((101 / 44) : ℂ) * ζ ^ 20 + ((35 / 11) : ℂ) * ζ ^ 22 - ((6 / 11) : ℂ) * ζ ^ 24 + ((7 / 11) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY66_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((1 / 2) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 6) : ℂ) * ζ ^ 12 - ((1 / 6) : ℂ) * ζ ^ 24 + ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 1 1
      + (((1 : ℂ))) * Y 6 6
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY66_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation16
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 - ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((1 / 6) : ℂ) * ζ ^ 6 - ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 3) : ℂ) * ζ ^ 22 + ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 26 - ((1 / 6) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((3 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 - ((3 / 2) : ℂ) * ζ ^ 4 + ((3 / 2) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 - ((7 / 6) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 16 - ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 + ((4 / 3) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26 + ((2 / 3) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((3 / 2) : ℂ) * ζ ^ 4 - ((3 / 2) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 + ((7 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 16 + ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 - ((4 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 - ((2 / 3) : ℂ) * ζ ^ 28)) * Y 6 6
        + ((-((4 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + ((4 / 3) : ℂ) * ζ ^ 4 - ((4 / 3) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 12 - ((7 / 6) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 16 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 - ((7 / 6) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 - ((1 / 3) : ℂ) * ζ ^ 28)) * Y 7 6)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY66_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 6 6
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY66_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((2 : ℂ) - ((4 / 3) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 22 + ((4 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 2) : ℂ) + ((1 / 3) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((1 / 2) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 - ((3 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 22 - ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26 + ζ ^ 28)) * Y 1 1
        + ((-((7 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((7 / 6) : ℂ) * ζ ^ 6 - ((7 / 6) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 14 - ((5 / 6) : ℂ) * ζ ^ 16 - ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 26 - (2 : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((1 / 2) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 16 + ((3 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 20 - ((3 / 2) : ℂ) * ζ ^ 22 + ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 - ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY66
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 6 6 = Y 7 7 := by
  have reduced :=
    row16_reducedY66_combinationStep07 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row16_reducedY67_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((10 / 3) : ℂ) - ((7 / 6) : ℂ) * ζ ^ 2 - ((13 / 12) : ℂ) * ζ ^ 6 + ((7 / 6) : ℂ) * ζ ^ 8 + ((10 / 3) : ℂ) * ζ ^ 12 + ((10 / 3) : ℂ) * ζ ^ 18 + ((7 / 6) : ℂ) * ζ ^ 22 - ((13 / 12) : ℂ) * ζ ^ 24 - ((7 / 6) : ℂ) * ζ ^ 28 - ((10 / 3) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((9 / 4) : ℂ) - ((9 / 4) : ℂ) * ζ ^ 2 + ((10 / 3) : ℂ) * ζ ^ 12 + ((13 / 6) : ℂ) * ζ ^ 18 + ((9 / 4) : ℂ) * ζ ^ 22 - ((13 / 6) : ℂ) * ζ ^ 24 - ((10 / 3) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-(13 : ℂ) + ((26 / 3) : ℂ) * ζ ^ 2 - ((40 / 3) : ℂ) * ζ ^ 6 + ((40 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 + ((41 / 3) : ℂ) * ζ ^ 18 - ((26 / 3) : ℂ) * ζ ^ 22 + (9 : ℂ) * ζ ^ 24 - ((40 / 3) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((1 / 12) : ℂ) + ((10 / 3) : ℂ) * ζ ^ 2 - ((1 / 12) : ℂ) * ζ ^ 4 - ((67 / 12) : ℂ) * ζ ^ 6 + ((9 / 4) : ℂ) * ζ ^ 8 + ((67 / 12) : ℂ) * ζ ^ 10 - ((67 / 12) : ℂ) * ζ ^ 12 - ((9 / 4) : ℂ) * ζ ^ 14 + ((67 / 12) : ℂ) * ζ ^ 16 + ((1 / 12) : ℂ) * ζ ^ 18 - ((10 / 3) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((((9 / 4) : ℂ) + ((9 / 4) : ℂ) * ζ ^ 2 - ((9 / 4) : ℂ) * ζ ^ 4 - ((9 / 4) : ℂ) * ζ ^ 6 + ((11 / 2) : ℂ) * ζ ^ 8 + ((1 / 12) : ℂ) * ζ ^ 10 - ((10 / 3) : ℂ) * ζ ^ 12 + ((10 / 3) : ℂ) * ζ ^ 14 - ((13 / 6) : ℂ) * ζ ^ 18 + ((9 / 4) : ℂ) * ζ ^ 20 - ((10 / 3) : ℂ) * ζ ^ 24 - ((1 / 12) : ℂ) * ζ ^ 26)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY67_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((7 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 2 - ((1 / 4) : ℂ) * ζ ^ 6 - ((1 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 22 - ((5 / 12) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((61 / 12) : ℂ) - ((29 / 12) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 6 + ((29 / 12) : ℂ) * ζ ^ 8 + ((17 / 6) : ℂ) * ζ ^ 12 + ((17 / 6) : ℂ) * ζ ^ 18 + ((29 / 12) : ℂ) * ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 - ((29 / 12) : ℂ) * ζ ^ 28 - ((61 / 12) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((9 / 4) : ℂ) - ((9 / 4) : ℂ) * ζ ^ 2 + ((10 / 3) : ℂ) * ζ ^ 12 + ((13 / 6) : ℂ) * ζ ^ 18 + ((9 / 4) : ℂ) * ζ ^ 22 - ((13 / 6) : ℂ) * ζ ^ 24 - ((10 / 3) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((7 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 22 + ((5 / 12) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY67_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((4 / 3) : ℂ) + (2 : ℂ) * ζ ^ 2 - ((7 / 3) : ℂ) * ζ ^ 6 - (2 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 22 - ((7 / 3) : ℂ) * ζ ^ 24 + (2 : ℂ) * ζ ^ 28 + ((4 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((7 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 2 - ((7 / 12) : ℂ) * ζ ^ 4 + ((1 / 6) : ℂ) * ζ ^ 6 + ((13 / 12) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 18 + ((7 / 12) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((7 / 4) : ℂ) + ((5 / 4) : ℂ) * ζ ^ 2 - ((7 / 4) : ℂ) * ζ ^ 4 - ζ ^ 6 + ((3 / 2) : ℂ) * ζ ^ 8 + ((5 / 2) : ℂ) * ζ ^ 10 + ((7 / 4) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 14 - ((13 / 4) : ℂ) * ζ ^ 16 + ((1 / 2) : ℂ) * ζ ^ 18 + ((13 / 4) : ℂ) * ζ ^ 20 + ζ ^ 22 - ((3 / 2) : ℂ) * ζ ^ 24 - ζ ^ 26)) * Y 0 1
        + ((-((7 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 2 + ((7 / 12) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 6 - ((13 / 12) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 18 - ((7 / 12) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY67_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((4 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((13 / 3) : ℂ) - ((13 / 6) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 6 + ((13 / 6) : ℂ) * ζ ^ 8 + ((11 / 6) : ℂ) * ζ ^ 12 + ((11 / 6) : ℂ) * ζ ^ 18 + ((13 / 6) : ℂ) * ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 - ((13 / 6) : ℂ) * ζ ^ 28 - ((13 / 3) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((9 / 4) : ℂ) - ((9 / 4) : ℂ) * ζ ^ 2 + ((10 / 3) : ℂ) * ζ ^ 12 + ((13 / 6) : ℂ) * ζ ^ 18 + ((9 / 4) : ℂ) * ζ ^ 22 - ((13 / 6) : ℂ) * ζ ^ 24 - ((10 / 3) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((7 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 22 + ((5 / 12) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((3 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 2 + ((3 / 4) : ℂ) * ζ ^ 6 - ζ ^ 8 - ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 22 - ((3 / 4) : ℂ) * ζ ^ 24 + ζ ^ 28)) * Y 4 4
      + ((((9 / 4) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((7 / 4) : ℂ) * ζ ^ 6 - ((7 / 4) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 12 - ((11 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ζ ^ 24 + ((7 / 4) : ℂ) * ζ ^ 28 + ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY67_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((1 : ℂ) - (3 : ℂ) * ζ ^ 2 + ((1 / 3) : ℂ) * ζ ^ 6 - ((8 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 18 + (3 : ℂ) * ζ ^ 22 - ((7 / 3) : ℂ) * ζ ^ 24 + ((8 / 3) : ℂ) * ζ ^ 28 - ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((9 / 22) : ℂ) + ((3 / 11) : ℂ) * ζ ^ 2 - ((9 / 22) : ℂ) * ζ ^ 4 + ((4 / 11) : ℂ) * ζ ^ 6 + ((5 / 11) : ℂ) * ζ ^ 8 - ((17 / 22) : ℂ) * ζ ^ 10 + ((7 / 22) : ℂ) * ζ ^ 12 + ((15 / 22) : ℂ) * ζ ^ 14 - ((15 / 22) : ℂ) * ζ ^ 16 - ((7 / 22) : ℂ) * ζ ^ 18 + ((15 / 22) : ℂ) * ζ ^ 20 - ((1 / 11) : ℂ) * ζ ^ 22 - ((4 / 11) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((6 / 11) : ℂ) - ((19 / 22) : ℂ) * ζ ^ 2 + ((6 / 11) : ℂ) * ζ ^ 4 + ((41 / 44) : ℂ) * ζ ^ 6 - ((37 / 44) : ℂ) * ζ ^ 8 - ((41 / 44) : ℂ) * ζ ^ 10 + ((45 / 44) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 14 - ((45 / 44) : ℂ) * ζ ^ 16 + ((3 / 22) : ℂ) * ζ ^ 18 + ((6 / 11) : ℂ) * ζ ^ 20 - ((3 / 22) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((-((9 / 22) : ℂ) - ((3 / 11) : ℂ) * ζ ^ 2 + ((9 / 22) : ℂ) * ζ ^ 4 - ((4 / 11) : ℂ) * ζ ^ 6 - ((5 / 11) : ℂ) * ζ ^ 8 + ((17 / 22) : ℂ) * ζ ^ 10 - ((7 / 22) : ℂ) * ζ ^ 12 - ((15 / 22) : ℂ) * ζ ^ 14 + ((15 / 22) : ℂ) * ζ ^ 16 + ((7 / 22) : ℂ) * ζ ^ 18 - ((15 / 22) : ℂ) * ζ ^ 20 + ((1 / 11) : ℂ) * ζ ^ 22 + ((4 / 11) : ℂ) * ζ ^ 24 - ((1 / 11) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((69 / 44) : ℂ) - ((17 / 11) : ℂ) * ζ ^ 2 + ((69 / 44) : ℂ) * ζ ^ 4 + ((1 / 44) : ℂ) * ζ ^ 6 - ((87 / 44) : ℂ) * ζ ^ 8 + ζ ^ 10 + ((5 / 22) : ℂ) * ζ ^ 12 - ((27 / 22) : ℂ) * ζ ^ 14 + ((15 / 22) : ℂ) * ζ ^ 16 + ((41 / 44) : ℂ) * ζ ^ 18 - ((51 / 44) : ℂ) * ζ ^ 20 + ((1 / 11) : ℂ) * ζ ^ 22 + ((10 / 11) : ℂ) * ζ ^ 24 - ((5 / 22) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY67_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((9 / 4) : ℂ) - ((9 / 4) : ℂ) * ζ ^ 2 + ((10 / 3) : ℂ) * ζ ^ 12 + ((13 / 6) : ℂ) * ζ ^ 18 + ((9 / 4) : ℂ) * ζ ^ 22 - ((13 / 6) : ℂ) * ζ ^ 24 - ((10 / 3) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((7 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 6 + ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 22 + ((5 / 12) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((3 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 2 + ((3 / 4) : ℂ) * ζ ^ 6 - ζ ^ 8 - ζ ^ 18 + ((3 / 4) : ℂ) * ζ ^ 22 - ((3 / 4) : ℂ) * ζ ^ 24 + ζ ^ 28)) * Y 4 4
      + ((((9 / 4) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((7 / 4) : ℂ) * ζ ^ 6 - ((7 / 4) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 12 - ((11 / 4) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ζ ^ 24 + ((7 / 4) : ℂ) * ζ ^ 28 + ζ ^ 30)) * Y 5 4
      + ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((4 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY67_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - (4 : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 12 + ((10 / 3) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((7 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((7 / 6) : ℂ) * ζ ^ 4 - ((2 / 3) : ℂ) * ζ ^ 6 - ((1 / 6) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 16 + ((1 / 3) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-(4 : ℂ) - ((11 / 6) : ℂ) * ζ ^ 2 + (4 : ℂ) * ζ ^ 4 + (3 : ℂ) * ζ ^ 6 - ζ ^ 8 - (3 : ℂ) * ζ ^ 10 + ((11 / 6) : ℂ) * ζ ^ 12 + ((4 / 3) : ℂ) * ζ ^ 14 - ((11 / 6) : ℂ) * ζ ^ 16 - ((11 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 + ((11 / 6) : ℂ) * ζ ^ 22 - ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 26 + ζ ^ 28)) * Y 0 1
        + ((((1 / 6) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 4 - ((1 / 6) : ℂ) * ζ ^ 6 + ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 3) : ℂ) * ζ ^ 14 + ((1 / 3) : ℂ) * ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 6) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((7 / 6) : ℂ) - ((5 / 6) : ℂ) * ζ ^ 2 - ((7 / 6) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 6 + ((1 / 6) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 16 - ((1 / 3) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 6) : ℂ) * ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 26)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY67_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((5 / 6) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 - ((5 / 6) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((4 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 + ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 3) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 12 + ((3 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 6) : ℂ) * ζ ^ 28 - ((1 / 2) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((4 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 - ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 3) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row16_reducedY67_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((13 / 3) : ℂ) - (5 : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 + ((16 / 3) : ℂ) * ζ ^ 12 + (4 : ℂ) * ζ ^ 18 + (5 : ℂ) * ζ ^ 22 - ((10 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 - (6 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((3 / 11) : ℂ) - ((1 / 22) : ℂ) * ζ ^ 2 + ((3 / 11) : ℂ) * ζ ^ 4 + ((3 / 11) : ℂ) * ζ ^ 6 - ((7 / 11) : ℂ) * ζ ^ 8 - ((21 / 22) : ℂ) * ζ ^ 10 + ((5 / 11) : ℂ) * ζ ^ 12 + ((3 / 22) : ℂ) * ζ ^ 14 - ((6 / 11) : ℂ) * ζ ^ 16 + ((3 / 22) : ℂ) * ζ ^ 18 + ((6 / 11) : ℂ) * ζ ^ 20 - ((9 / 11) : ℂ) * ζ ^ 22 - ((1 / 11) : ℂ) * ζ ^ 24 + ((9 / 11) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((18 / 11) : ℂ) - ((3 / 11) : ℂ) * ζ ^ 2 + ((18 / 11) : ℂ) * ζ ^ 4 - ((27 / 44) : ℂ) * ζ ^ 6 - ((17 / 22) : ℂ) * ζ ^ 8 + ((27 / 44) : ℂ) * ζ ^ 10 + ((9 / 11) : ℂ) * ζ ^ 12 - ((9 / 44) : ℂ) * ζ ^ 14 - ((9 / 11) : ℂ) * ζ ^ 16 + ((27 / 22) : ℂ) * ζ ^ 18 + ((3 / 22) : ℂ) * ζ ^ 20 - ((27 / 22) : ℂ) * ζ ^ 22)) * Y 1 1
        + ((((18 / 11) : ℂ) + ((3 / 11) : ℂ) * ζ ^ 2 - ((18 / 11) : ℂ) * ζ ^ 4 + ((27 / 44) : ℂ) * ζ ^ 6 + ((17 / 22) : ℂ) * ζ ^ 8 - ((27 / 44) : ℂ) * ζ ^ 10 - ((9 / 11) : ℂ) * ζ ^ 12 + ((9 / 44) : ℂ) * ζ ^ 14 + ((9 / 11) : ℂ) * ζ ^ 16 - ((27 / 22) : ℂ) * ζ ^ 18 - ((3 / 22) : ℂ) * ζ ^ 20 + ((27 / 22) : ℂ) * ζ ^ 22)) * Y 4 4
        + ((((69 / 22) : ℂ) + ((23 / 44) : ℂ) * ζ ^ 2 - ((69 / 22) : ℂ) * ζ ^ 4 + ((15 / 11) : ℂ) * ζ ^ 6 + ((27 / 22) : ℂ) * ζ ^ 8 - ((75 / 44) : ℂ) * ζ ^ 10 - ((31 / 22) : ℂ) * ζ ^ 12 + ((21 / 44) : ℂ) * ζ ^ 14 + ((15 / 11) : ℂ) * ζ ^ 16 - ((105 / 44) : ℂ) * ζ ^ 18 + ((45 / 22) : ℂ) * ζ ^ 22 - ((1 / 22) : ℂ) * ζ ^ 24 + ((9 / 22) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY67_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 6 7) = 0 := by
  have previous :=
    row16_reducedY67_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 - ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ((1 / 3) : ℂ) * ζ ^ 10 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 6) : ℂ) * ζ ^ 14 - ((1 / 2) : ℂ) * ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 - ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 6) : ℂ) * ζ ^ 24 + ((1 / 6) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((4 / 3) : ℂ) - ((2 / 3) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 4 + ((4 / 3) : ℂ) * ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 16 - ((7 / 6) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 20 + ((7 / 6) : ℂ) * ζ ^ 22 - ((1 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 26 + ((1 / 3) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((3 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 2 + ((3 / 2) : ℂ) * ζ ^ 4 - ((3 / 2) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 + ((7 / 6) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((1 / 6) : ℂ) * ζ ^ 16 + ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 - ((4 / 3) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26 - ((2 / 3) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((-((4 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + ((4 / 3) : ℂ) * ζ ^ 4 - ((4 / 3) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 12 - ((7 / 6) : ℂ) * ζ ^ 14 - ((2 / 3) : ℂ) * ζ ^ 16 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 20 - ((7 / 6) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 - ((1 / 3) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY67
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 6 7 = 0 := by
  have reduced :=
    row16_reducedY67_combinationStep05 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row16_reducedY76_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((7 / 6) : ℂ) + ((17 / 4) : ℂ) * ζ ^ 2 + ((11 / 12) : ℂ) * ζ ^ 6 - ((5 / 4) : ℂ) * ζ ^ 8 - ((10 / 3) : ℂ) * ζ ^ 12 - ((37 / 12) : ℂ) * ζ ^ 18 - ((17 / 4) : ℂ) * ζ ^ 22 + ((17 / 4) : ℂ) * ζ ^ 24 + ((5 / 4) : ℂ) * ζ ^ 28 + (3 : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((37 / 12) : ℂ) + ((13 / 6) : ℂ) * ζ ^ 2 + ((1 / 12) : ℂ) * ζ ^ 6 + ((13 / 6) : ℂ) * ζ ^ 8 - ((7 / 6) : ℂ) * ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 - ((13 / 6) : ℂ) * ζ ^ 22 - ((1 / 12) : ℂ) * ζ ^ 24 - ((13 / 6) : ℂ) * ζ ^ 28 + ((37 / 12) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row16_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((((76 / 3) : ℂ) + ((14 / 3) : ℂ) * ζ ^ 2 + (12 : ℂ) * ζ ^ 6 - ((40 / 3) : ℂ) * ζ ^ 8 - ((62 / 3) : ℂ) * ζ ^ 12 - ((76 / 3) : ℂ) * ζ ^ 18 - ((14 / 3) : ℂ) * ζ ^ 22 + ((37 / 3) : ℂ) * ζ ^ 24 + ((40 / 3) : ℂ) * ζ ^ 28 + (13 : ℂ) * ζ ^ 30)) * equation
      - (
        ((((31 / 6) : ℂ) - ((37 / 12) : ℂ) * ζ ^ 2 - ((31 / 6) : ℂ) * ζ ^ 4 + ((31 / 6) : ℂ) * ζ ^ 6 + ((37 / 12) : ℂ) * ζ ^ 8 - ((31 / 6) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 12 + ((25 / 12) : ℂ) * ζ ^ 14 - ((1 / 4) : ℂ) * ζ ^ 16 - ((13 / 4) : ℂ) * ζ ^ 18 + ((10 / 3) : ℂ) * ζ ^ 20 + ((13 / 4) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((((37 / 12) : ℂ) - ((13 / 6) : ℂ) * ζ ^ 2 - ((37 / 12) : ℂ) * ζ ^ 4 + ((25 / 12) : ℂ) * ζ ^ 6 - ((65 / 12) : ℂ) * ζ ^ 8 - ((13 / 4) : ℂ) * ζ ^ 10 + ((10 / 3) : ℂ) * ζ ^ 12 - ((37 / 12) : ℂ) * ζ ^ 14 - ((7 / 6) : ℂ) * ζ ^ 18 + ((37 / 12) : ℂ) * ζ ^ 20 + ((10 / 3) : ℂ) * ζ ^ 24 + ((13 / 4) : ℂ) * ζ ^ 26)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY76_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((7 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 6 + ((5 / 12) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 + ((7 / 12) : ℂ) * ζ ^ 18 + ((1 / 12) : ℂ) * ζ ^ 22 - ζ ^ 24 - ((5 / 12) : ℂ) * ζ ^ 28 + ((5 / 12) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((7 / 12) : ℂ) + ((11 / 4) : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 + ((7 / 4) : ℂ) * ζ ^ 8 - ((25 / 12) : ℂ) * ζ ^ 12 - ((10 / 3) : ℂ) * ζ ^ 18 - ((11 / 4) : ℂ) * ζ ^ 22 + ((11 / 4) : ℂ) * ζ ^ 24 - ((7 / 4) : ℂ) * ζ ^ 28 + ((9 / 2) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((37 / 12) : ℂ) + ((13 / 6) : ℂ) * ζ ^ 2 + ((1 / 12) : ℂ) * ζ ^ 6 + ((13 / 6) : ℂ) * ζ ^ 8 - ((7 / 6) : ℂ) * ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 - ((13 / 6) : ℂ) * ζ ^ 22 - ((1 / 12) : ℂ) * ζ ^ 24 - ((13 / 6) : ℂ) * ζ ^ 28 + ((37 / 12) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((7 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 6 - ((5 / 12) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 12 - ((7 / 12) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 22 + ζ ^ 24 + ((5 / 12) : ℂ) * ζ ^ 28 - ((5 / 12) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row16_reducedY76_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((2 : ℂ) - ((7 / 3) : ℂ) * ζ ^ 2 - ((7 / 3) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 + ((13 / 3) : ℂ) * ζ ^ 18 + ((7 / 3) : ℂ) * ζ ^ 22 - ((7 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28 - ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((7 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 2 - ((7 / 12) : ℂ) * ζ ^ 4 + ((1 / 12) : ℂ) * ζ ^ 6 + ((2 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 10 - ((1 / 12) : ℂ) * ζ ^ 12 - ((5 / 12) : ℂ) * ζ ^ 14 - ((7 / 12) : ℂ) * ζ ^ 18 + ((7 / 12) : ℂ) * ζ ^ 20 - ((1 / 12) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((7 / 4) : ℂ) + ((3 / 2) : ℂ) * ζ ^ 2 - ((7 / 4) : ℂ) * ζ ^ 4 - ((5 / 4) : ℂ) * ζ ^ 6 + ((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 + ((7 / 4) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 14 - (2 : ℂ) * ζ ^ 16 + ((1 / 4) : ℂ) * ζ ^ 18 + (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 22 - ((1 / 4) : ℂ) * ζ ^ 24 + (2 : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((7 / 12) : ℂ) - ((1 / 12) : ℂ) * ζ ^ 2 + ((7 / 12) : ℂ) * ζ ^ 4 - ((1 / 12) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 10 + ((1 / 12) : ℂ) * ζ ^ 12 + ((5 / 12) : ℂ) * ζ ^ 14 + ((7 / 12) : ℂ) * ζ ^ 18 - ((7 / 12) : ℂ) * ζ ^ 20 + ((1 / 12) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY76_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((((7 / 6) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 2 + ((5 / 6) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ζ ^ 12 - ((7 / 6) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28 + ((5 / 3) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((5 / 6) : ℂ) + (2 : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 + ((3 / 2) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 12 - ((17 / 6) : ℂ) * ζ ^ 18 - (2 : ℂ) * ζ ^ 22 + (2 : ℂ) * ζ ^ 24 - ((3 / 2) : ℂ) * ζ ^ 28 + ((7 / 2) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((37 / 12) : ℂ) + ((13 / 6) : ℂ) * ζ ^ 2 + ((1 / 12) : ℂ) * ζ ^ 6 + ((13 / 6) : ℂ) * ζ ^ 8 - ((7 / 6) : ℂ) * ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 - ((13 / 6) : ℂ) * ζ ^ 22 - ((1 / 12) : ℂ) * ζ ^ 24 - ((13 / 6) : ℂ) * ζ ^ 28 + ((37 / 12) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((7 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 6 - ((5 / 12) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 12 - ((7 / 12) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 22 + ζ ^ 24 + ((5 / 12) : ℂ) * ζ ^ 28 - ((5 / 12) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((7 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((3 / 4) : ℂ) * ζ ^ 8 + ((3 / 2) : ℂ) * ζ ^ 12 + ((7 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 - ((3 / 4) : ℂ) * ζ ^ 28 - ((5 / 4) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-(3 : ℂ) - ζ ^ 2 - ((3 / 2) : ℂ) * ζ ^ 6 + ζ ^ 8 + ((13 / 4) : ℂ) * ζ ^ 12 + ((13 / 4) : ℂ) * ζ ^ 18 + ζ ^ 22 - ((3 / 2) : ℂ) * ζ ^ 24 - ζ ^ 28 - (3 : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row16_reducedY76_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((13 / 3) : ℂ) - ζ ^ 2 - ((8 / 3) : ℂ) * ζ ^ 6 + ((5 / 3) : ℂ) * ζ ^ 8 + ((10 / 3) : ℂ) * ζ ^ 12 + ((13 / 3) : ℂ) * ζ ^ 18 + ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 - ((5 / 3) : ℂ) * ζ ^ 28 - (3 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((3 / 11) : ℂ) + ((1 / 11) : ℂ) * ζ ^ 2 + ((3 / 11) : ℂ) * ζ ^ 4 - ((2 / 11) : ℂ) * ζ ^ 6 - ((15 / 22) : ℂ) * ζ ^ 8 + ((1 / 22) : ℂ) * ζ ^ 10 + ((2 / 11) : ℂ) * ζ ^ 12 - ((5 / 11) : ℂ) * ζ ^ 14 + ((1 / 22) : ℂ) * ζ ^ 16 + ((3 / 11) : ℂ) * ζ ^ 18 - ((1 / 22) : ℂ) * ζ ^ 20 - ((9 / 22) : ℂ) * ζ ^ 22 + ((5 / 22) : ℂ) * ζ ^ 24 + ((9 / 22) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((7 / 11) : ℂ) + ((6 / 11) : ℂ) * ζ ^ 2 + ((7 / 11) : ℂ) * ζ ^ 4 - ((12 / 11) : ℂ) * ζ ^ 6 - ((1 / 22) : ℂ) * ζ ^ 8 + ((12 / 11) : ℂ) * ζ ^ 10 - ((3 / 44) : ℂ) * ζ ^ 12 - ((9 / 22) : ℂ) * ζ ^ 14 + ((3 / 44) : ℂ) * ζ ^ 16 + ((27 / 44) : ℂ) * ζ ^ 18 - ((15 / 44) : ℂ) * ζ ^ 20 - ((27 / 44) : ℂ) * ζ ^ 22)) * Y 0 1
        + ((((3 / 11) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 2 - ((3 / 11) : ℂ) * ζ ^ 4 + ((2 / 11) : ℂ) * ζ ^ 6 + ((15 / 22) : ℂ) * ζ ^ 8 - ((1 / 22) : ℂ) * ζ ^ 10 - ((2 / 11) : ℂ) * ζ ^ 12 + ((5 / 11) : ℂ) * ζ ^ 14 - ((1 / 22) : ℂ) * ζ ^ 16 - ((3 / 11) : ℂ) * ζ ^ 18 + ((1 / 22) : ℂ) * ζ ^ 20 + ((9 / 22) : ℂ) * ζ ^ 22 - ((5 / 22) : ℂ) * ζ ^ 24 - ((9 / 22) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((1 / 22) : ℂ) + ((7 / 22) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 4 - ((7 / 11) : ℂ) * ζ ^ 6 + ((73 / 44) : ℂ) * ζ ^ 8 + ((43 / 44) : ℂ) * ζ ^ 10 - ((23 / 44) : ℂ) * ζ ^ 12 + ((8 / 11) : ℂ) * ζ ^ 14 - ((1 / 22) : ℂ) * ζ ^ 16 - ((3 / 44) : ℂ) * ζ ^ 18 - ((5 / 22) : ℂ) * ζ ^ 20 + ((9 / 22) : ℂ) * ζ ^ 22 - ((25 / 44) : ℂ) * ζ ^ 24 - ((45 / 44) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY76_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((37 / 12) : ℂ) + ((13 / 6) : ℂ) * ζ ^ 2 + ((1 / 12) : ℂ) * ζ ^ 6 + ((13 / 6) : ℂ) * ζ ^ 8 - ((7 / 6) : ℂ) * ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 - ((13 / 6) : ℂ) * ζ ^ 22 - ((1 / 12) : ℂ) * ζ ^ 24 - ((13 / 6) : ℂ) * ζ ^ 28 + ((37 / 12) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((7 / 12) : ℂ) + ((1 / 12) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 6 - ((5 / 12) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 12 - ((7 / 12) : ℂ) * ζ ^ 18 - ((1 / 12) : ℂ) * ζ ^ 22 + ζ ^ 24 + ((5 / 12) : ℂ) * ζ ^ 28 - ((5 / 12) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((7 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 2 - ζ ^ 6 + ((3 / 4) : ℂ) * ζ ^ 8 + ((3 / 2) : ℂ) * ζ ^ 12 + ((7 / 4) : ℂ) * ζ ^ 18 + ((1 / 4) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 - ((3 / 4) : ℂ) * ζ ^ 28 - ((5 / 4) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-(3 : ℂ) - ζ ^ 2 - ((3 / 2) : ℂ) * ζ ^ 6 + ζ ^ 8 + ((13 / 4) : ℂ) * ζ ^ 12 + ((13 / 4) : ℂ) * ζ ^ 18 + ζ ^ 22 - ((3 / 2) : ℂ) * ζ ^ 24 - ζ ^ 28 - (3 : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((7 / 6) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 2 + ((5 / 6) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ζ ^ 12 - ((7 / 6) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28 + ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 6
      + ((((3 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 6) = 0 := by
  have previous :=
    row16_reducedY76_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation06
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + (((2 : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 + ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((1 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 6 + ((5 / 6) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 10 - ((2 / 3) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ζ ^ 16 - ((1 / 6) : ℂ) * ζ ^ 18 - ((5 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 26 + ((2 / 3) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((5 / 6) : ℂ) + ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 2) : ℂ) * ζ ^ 8 + ((3 / 2) : ℂ) * ζ ^ 10 - ((7 / 3) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 14 + (2 : ℂ) * ζ ^ 16 - ((4 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 22 + ((8 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 26 - ((8 / 3) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((1 / 6) : ℂ) - ((5 / 6) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 4 - ((2 / 3) : ℂ) * ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 10 + ((2 / 3) : ℂ) * ζ ^ 12 - ((5 / 6) : ℂ) * ζ ^ 14 - ζ ^ 16 + ((1 / 6) : ℂ) * ζ ^ 18 + ((5 / 6) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 26 - ((2 / 3) : ℂ) * ζ ^ 28)) * Y 6 6
        + ((-(1 : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + ζ ^ 4 - ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 + ((5 / 6) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 14 - ((1 / 6) : ℂ) * ζ ^ 16 + ((1 / 2) : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((1 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 26)) * Y 7 6)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY76_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      ((-((11 / 6) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 2 + ((4 / 3) : ℂ) * ζ ^ 6 + ((2 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28 + ((11 / 6) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((7 / 6) : ℂ) - ((1 / 6) : ℂ) * ζ ^ 2 - ((5 / 6) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ζ ^ 12 + ((7 / 6) : ℂ) * ζ ^ 18 + ((1 / 6) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 28 - ((5 / 3) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((7 / 6) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 2 + ((5 / 6) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ζ ^ 12 - ((7 / 6) : ℂ) * ζ ^ 18 - ((1 / 6) : ℂ) * ζ ^ 22 - ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 3) : ℂ) * ζ ^ 28 + ((5 / 3) : ℂ) * ζ ^ 30)) * Y 6 6
      + ((((3 / 2) : ℂ) - ((1 / 2) : ℂ) * ζ ^ 2 + ζ ^ 6 - ((5 / 6) : ℂ) * ζ ^ 8 - ((5 / 6) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 18 + ((1 / 2) : ℂ) * ζ ^ 22 + ((5 / 6) : ℂ) * ζ ^ 28 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 7 6) = 0 := by
  have previous :=
    row16_reducedY76_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(3 : ℂ) + ((10 / 3) : ℂ) * ζ ^ 2 - (3 : ℂ) * ζ ^ 6 + ((10 / 3) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 12 + ((4 / 3) : ℂ) * ζ ^ 18 - ((10 / 3) : ℂ) * ζ ^ 22 + (3 : ℂ) * ζ ^ 24 - ((10 / 3) : ℂ) * ζ ^ 28 + (3 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((5 / 22) : ℂ) + ((4 / 11) : ℂ) * ζ ^ 2 + ((5 / 22) : ℂ) * ζ ^ 4 - ((13 / 22) : ℂ) * ζ ^ 6 - ((3 / 11) : ℂ) * ζ ^ 8 + ((23 / 22) : ℂ) * ζ ^ 10 - ((9 / 22) : ℂ) * ζ ^ 12 - ((7 / 11) : ℂ) * ζ ^ 14 + ((19 / 22) : ℂ) * ζ ^ 16 + ((1 / 22) : ℂ) * ζ ^ 18 - ((19 / 22) : ℂ) * ζ ^ 20 + ((9 / 22) : ℂ) * ζ ^ 22 + ((5 / 11) : ℂ) * ζ ^ 24 - ((9 / 22) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((25 / 22) : ℂ) + ((41 / 44) : ℂ) * ζ ^ 2 - ((25 / 22) : ℂ) * ζ ^ 4 - ((6 / 11) : ℂ) * ζ ^ 6 + ((47 / 44) : ℂ) * ζ ^ 8 + ((6 / 11) : ℂ) * ζ ^ 10 - ((57 / 44) : ℂ) * ζ ^ 12 - ((3 / 44) : ℂ) * ζ ^ 14 + ((57 / 44) : ℂ) * ζ ^ 16 - ((27 / 44) : ℂ) * ζ ^ 18 - ((15 / 22) : ℂ) * ζ ^ 20 + ((27 / 44) : ℂ) * ζ ^ 22)) * Y 1 1
        + ((-((25 / 22) : ℂ) - ((41 / 44) : ℂ) * ζ ^ 2 + ((25 / 22) : ℂ) * ζ ^ 4 + ((6 / 11) : ℂ) * ζ ^ 6 - ((47 / 44) : ℂ) * ζ ^ 8 - ((6 / 11) : ℂ) * ζ ^ 10 + ((57 / 44) : ℂ) * ζ ^ 12 + ((3 / 44) : ℂ) * ζ ^ 14 - ((57 / 44) : ℂ) * ζ ^ 16 + ((27 / 44) : ℂ) * ζ ^ 18 + ((15 / 22) : ℂ) * ζ ^ 20 - ((27 / 44) : ℂ) * ζ ^ 22)) * Y 4 4
        + ((-((105 / 44) : ℂ) - ((37 / 22) : ℂ) * ζ ^ 2 + ((105 / 44) : ℂ) * ζ ^ 4 + ((35 / 44) : ℂ) * ζ ^ 6 - ((25 / 11) : ℂ) * ζ ^ 8 - ((25 / 44) : ℂ) * ζ ^ 10 + ((105 / 44) : ℂ) * ζ ^ 12 - ((2 / 11) : ℂ) * ζ ^ 14 - ((95 / 44) : ℂ) * ζ ^ 16 + ((5 / 4) : ℂ) * ζ ^ 18 + ((41 / 44) : ℂ) * ζ ^ 20 - ((45 / 44) : ℂ) * ζ ^ 22 + ((5 / 22) : ℂ) * ζ ^ 24 - ((9 / 44) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY76_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 7 6) = 0 := by
  have previous :=
    row16_reducedY76_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row16_commutatorEquation16
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(2 : ℂ) + ((4 / 3) : ℂ) * ζ ^ 2 + ((4 / 3) : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 22 - ((4 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28 + (2 : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((5 / 6) : ℂ) - ζ ^ 2 + ((3 / 2) : ℂ) * ζ ^ 4 + ((2 / 3) : ℂ) * ζ ^ 6 - ((1 / 6) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 12 - ((1 / 3) : ℂ) * ζ ^ 14 + ((4 / 3) : ℂ) * ζ ^ 16 + ((2 / 3) : ℂ) * ζ ^ 18 - ((5 / 6) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 24 - ((1 / 3) : ℂ) * ζ ^ 26 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((7 / 6) : ℂ) + ((5 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 - ((7 / 6) : ℂ) * ζ ^ 6 - ((7 / 6) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 6) : ℂ) * ζ ^ 12 + ((1 / 3) : ℂ) * ζ ^ 14 - ((5 / 6) : ℂ) * ζ ^ 16 - ((2 / 3) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 26 - (2 : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((7 / 6) : ℂ) - ((5 / 6) : ℂ) * ζ ^ 2 - ((1 / 2) : ℂ) * ζ ^ 4 + ((7 / 6) : ℂ) * ζ ^ 6 + ((7 / 6) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 10 - ((1 / 6) : ℂ) * ζ ^ 12 - ((1 / 3) : ℂ) * ζ ^ 14 + ((5 / 6) : ℂ) * ζ ^ 16 + ((2 / 3) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 26 + (2 : ℂ) * ζ ^ 28)) * Y 6 6
        + ((-((1 / 2) : ℂ) + ((1 / 6) : ℂ) * ζ ^ 2 + ((1 / 2) : ℂ) * ζ ^ 4 + ((1 / 3) : ℂ) * ζ ^ 8 + ((1 / 3) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((1 / 3) : ℂ) * ζ ^ 16 - ((3 / 2) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 22 - ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 26 + ζ ^ 28)) * Y 7 6)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row16_reducedY76
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    Y 7 6 = 0 := by
  have reduced :=
    row16_reducedY76_combinationStep05 Y commutesA commutesDiagonal
  linear_combination reduced


/-- A matrix commuting with both transformed row 16 generators is
scalar. -/
theorem alternatingSixAmbientRow16Transformed_scalar_commutant
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow16TransformedGeneratorA =
        alternatingSixAmbientRow16TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow16GeneratorBDiagonal =
        alternatingSixAmbientRow16GeneratorBDiagonal * Y) :
    ∃ c : ℂ,
      Y = c • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY26 :
      Y 2 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 6 (by decide)
  have hY27 :
      Y 2 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 2 7 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY36 :
      Y 3 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 6 (by decide)
  have hY37 :
      Y 3 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 3 7 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 3 (by decide)
  have hY46 :
      Y 4 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 6 (by decide)
  have hY47 :
      Y 4 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 4 7 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 3 (by decide)
  have hY56 :
      Y 5 6 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 6 (by decide)
  have hY57 :
      Y 5 7 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 5 7 (by decide)
  have hY60 :
      Y 6 0 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 0 (by decide)
  have hY61 :
      Y 6 1 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 1 (by decide)
  have hY62 :
      Y 6 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 2 (by decide)
  have hY63 :
      Y 6 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 3 (by decide)
  have hY64 :
      Y 6 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 4 (by decide)
  have hY65 :
      Y 6 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 6 5 (by decide)
  have hY70 :
      Y 7 0 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 0 (by decide)
  have hY71 :
      Y 7 1 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 1 (by decide)
  have hY72 :
      Y 7 2 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 2 (by decide)
  have hY73 :
      Y 7 3 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 3 (by decide)
  have hY74 :
      Y 7 4 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 4 (by decide)
  have hY75 :
      Y 7 5 = 0 :=
    alternatingSixAmbientRow16_off_block
      Y commutesDiagonal 7 5 (by decide)

  have reducedY00 : Y 0 0 = Y 7 7 :=
    row16_reducedY00 Y commutesA commutesDiagonal
  have reducedY01 : Y 0 1 = 0 :=
    row16_reducedY01 Y commutesA commutesDiagonal
  have reducedY10 : Y 1 0 = 0 :=
    row16_reducedY10 Y commutesA commutesDiagonal
  have reducedY11 : Y 1 1 = Y 7 7 :=
    row16_reducedY11 Y commutesA commutesDiagonal
  have reducedY22 : Y 2 2 = Y 7 7 :=
    row16_reducedY22 Y commutesA commutesDiagonal
  have reducedY23 : Y 2 3 = 0 :=
    row16_reducedY23 Y commutesA commutesDiagonal
  have reducedY32 : Y 3 2 = 0 :=
    row16_reducedY32 Y commutesA commutesDiagonal
  have reducedY33 : Y 3 3 = Y 7 7 :=
    row16_reducedY33 Y commutesA commutesDiagonal
  have reducedY44 : Y 4 4 = Y 7 7 :=
    row16_reducedY44 Y commutesA commutesDiagonal
  have reducedY45 : Y 4 5 = 0 :=
    row16_reducedY45 Y commutesA commutesDiagonal
  have reducedY54 : Y 5 4 = 0 :=
    row16_reducedY54 Y commutesA commutesDiagonal
  have reducedY55 : Y 5 5 = Y 7 7 :=
    row16_reducedY55 Y commutesA commutesDiagonal
  have reducedY66 : Y 6 6 = Y 7 7 :=
    row16_reducedY66 Y commutesA commutesDiagonal
  have reducedY67 : Y 6 7 = 0 :=
    row16_reducedY67 Y commutesA commutesDiagonal
  have reducedY76 : Y 7 6 = 0 :=
    row16_reducedY76 Y commutesA commutesDiagonal
  refine ⟨Y 7 7, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [
      hY02,
      hY03,
      hY04,
      hY05,
      hY06,
      hY07,
      hY12,
      hY13,
      hY14,
      hY15,
      hY16,
      hY17,
      hY20,
      hY21,
      hY24,
      hY25,
      hY26,
      hY27,
      hY30,
      hY31,
      hY34,
      hY35,
      hY36,
      hY37,
      hY40,
      hY41,
      hY42,
      hY43,
      hY46,
      hY47,
      hY50,
      hY51,
      hY52,
      hY53,
      hY56,
      hY57,
      hY60,
      hY61,
      hY62,
      hY63,
      hY64,
      hY65,
      hY70,
      hY71,
      hY72,
      hY73,
      hY74,
      hY75,
      reducedY00,
      reducedY01,
      reducedY10,
      reducedY11,
      reducedY22,
      reducedY23,
      reducedY32,
      reducedY33,
      reducedY44,
      reducedY45,
      reducedY54,
      reducedY55,
      reducedY66,
      reducedY67,
      reducedY76]

/-- Every matrix commuting with both original row 16 presentation
generators is scalar. -/
theorem alternatingSixAmbientRow16_scalar_commutant
    (X : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      X * alternatingSixFiveAmbient_row16_matrixA =
        alternatingSixFiveAmbient_row16_matrixA * X)
    (commutesB :
      X * alternatingSixFiveAmbient_row16_matrixB =
        alternatingSixFiveAmbient_row16_matrixB * X) :
    ∃ c : ℂ,
      X = c • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  apply Matrix.scalar_commutant_of_diagonal_basis
    alternatingSixFiveAmbient_row16_matrixA
    alternatingSixFiveAmbient_row16_matrixB
    alternatingSixAmbientRow16Eigenbasis
    alternatingSixAmbientRow16EigenbasisInverse
    alternatingSixAmbientRow16TransformedGeneratorA
    alternatingSixAmbientRow16GeneratorBEigenvalue
    alternatingSixAmbientRow16EigenbasisInverse_mul
    alternatingSixAmbientRow16Eigenbasis_mul_inverse
    alternatingSixAmbientRow16GeneratorB_mul_eigenbasis
    alternatingSixAmbientRow16TransformedGeneratorA_eq
    alternatingSixAmbientRow16Transformed_scalar_commutant
    X commutesA commutesB

end InductiveMcKay
end McKayConjecture
