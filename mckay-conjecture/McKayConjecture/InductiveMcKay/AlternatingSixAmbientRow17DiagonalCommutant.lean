/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DiagonalBasisMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow17DiagonalData

/-!
# Scalar common commutant for ambient row 17

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
private theorem alternatingSixAmbientRow17_off_block
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y)
    (i j : Fin 8)
    (different :
      alternatingSixAmbientRow17EigenvalueLabel i ≠
        alternatingSixAmbientRow17EigenvalueLabel j) :
    Y i j = 0 := by
  apply Matrix.entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
    Y alternatingSixAmbientRow17GeneratorBEigenvalue
  · exact commutesDiagonal
  · intro equalEigenvalues
    apply different
    apply alternatingSixOrderFourEigenvalue_injective
    simpa [
      alternatingSixAmbientRow17GeneratorBEigenvalue] using
      equalEigenvalues.symm


private theorem row17_commutatorEquation00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((1 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 24 + ((3 / 4) : ℂ) * ζ ^ 28)) * Y 0 1
      + ((((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 24)) * Y 1 0) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY60 :
      Y 6 0 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 0 (by decide)
  have hY70 :
      Y 7 0 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 0 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (0 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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

private theorem row17_commutatorEquation01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((1 / 4) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 24)) * Y 0 0
      + ((((1 / 4) : ℂ) - ((3 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 24 + ((3 / 4) : ℂ) * ζ ^ 28)) * Y 0 1
      + ((((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 24)) * Y 1 1) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY61 :
      Y 6 1 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 1 (by decide)
  have hY71 :
      Y 7 1 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 1 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (1 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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

private theorem row17_commutatorEquation02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((2 / 41) : ℂ) + ((11 / 82) : ℂ) * ζ ^ 2 + ((3 / 82) : ℂ) * ζ ^ 6 + ((15 / 82) : ℂ) * ζ ^ 8 + ((21 / 164) : ℂ) * ζ ^ 12 + ((9 / 82) : ℂ) * ζ ^ 18 - ((11 / 82) : ℂ) * ζ ^ 22 + ((13 / 164) : ℂ) * ζ ^ 24 - ((15 / 82) : ℂ) * ζ ^ 28 - ((1 / 41) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((1 / 82) : ℂ) - ((27 / 41) : ℂ) * ζ ^ 2 - ((63 / 164) : ℂ) * ζ ^ 6 - ((55 / 82) : ℂ) * ζ ^ 8 - ((77 / 164) : ℂ) * ζ ^ 12 + ((4 / 41) : ℂ) * ζ ^ 18 + ((27 / 41) : ℂ) * ζ ^ 22 + ((12 / 41) : ℂ) * ζ ^ 24 + ((55 / 82) : ℂ) * ζ ^ 28 - ((10 / 41) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((2 / 41) : ℂ) - ((11 / 82) : ℂ) * ζ ^ 2 - ((3 / 82) : ℂ) * ζ ^ 6 - ((15 / 82) : ℂ) * ζ ^ 8 - ((21 / 164) : ℂ) * ζ ^ 12 - ((9 / 82) : ℂ) * ζ ^ 18 + ((11 / 82) : ℂ) * ζ ^ 22 - ((13 / 164) : ℂ) * ζ ^ 24 + ((15 / 82) : ℂ) * ζ ^ 28 + ((1 / 41) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((13 / 164) : ℂ) + ((9 / 41) : ℂ) * ζ ^ 2 + ((21 / 164) : ℂ) * ζ ^ 6 + ((23 / 164) : ℂ) * ζ ^ 8 + ((3 / 41) : ℂ) * ζ ^ 12 + ((11 / 82) : ℂ) * ζ ^ 18 - ((9 / 41) : ℂ) * ζ ^ 22 - ((4 / 41) : ℂ) * ζ ^ 24 - ((23 / 164) : ℂ) * ζ ^ 28 - ((7 / 82) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY62 :
      Y 6 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 2 (by decide)
  have hY72 :
      Y 7 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 2 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (2 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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

private theorem row17_commutatorEquation03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((13 / 164) : ℂ) - ((9 / 41) : ℂ) * ζ ^ 2 - ((21 / 164) : ℂ) * ζ ^ 6 - ((23 / 164) : ℂ) * ζ ^ 8 - ((3 / 41) : ℂ) * ζ ^ 12 - ((11 / 82) : ℂ) * ζ ^ 18 + ((9 / 41) : ℂ) * ζ ^ 22 + ((4 / 41) : ℂ) * ζ ^ 24 + ((23 / 164) : ℂ) * ζ ^ 28 + ((7 / 82) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((17 / 82) : ℂ) + ((9 / 164) : ℂ) * ζ ^ 2 - ((5 / 164) : ℂ) * ζ ^ 6 + ((4 / 41) : ℂ) * ζ ^ 8 - ((19 / 82) : ℂ) * ζ ^ 12 + ((13 / 82) : ℂ) * ζ ^ 18 - ((9 / 164) : ℂ) * ζ ^ 22 - ((1 / 41) : ℂ) * ζ ^ 24 - ((4 / 41) : ℂ) * ζ ^ 28 - ((6 / 41) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((2 / 41) : ℂ) - ((11 / 82) : ℂ) * ζ ^ 2 - ((3 / 82) : ℂ) * ζ ^ 6 - ((15 / 82) : ℂ) * ζ ^ 8 - ((21 / 164) : ℂ) * ζ ^ 12 - ((9 / 82) : ℂ) * ζ ^ 18 + ((11 / 82) : ℂ) * ζ ^ 22 - ((13 / 164) : ℂ) * ζ ^ 24 + ((15 / 82) : ℂ) * ζ ^ 28 + ((1 / 41) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((13 / 164) : ℂ) + ((9 / 41) : ℂ) * ζ ^ 2 + ((21 / 164) : ℂ) * ζ ^ 6 + ((23 / 164) : ℂ) * ζ ^ 8 + ((3 / 41) : ℂ) * ζ ^ 12 + ((11 / 82) : ℂ) * ζ ^ 18 - ((9 / 41) : ℂ) * ζ ^ 22 - ((4 / 41) : ℂ) * ζ ^ 24 - ((23 / 164) : ℂ) * ζ ^ 28 - ((7 / 82) : ℂ) * ζ ^ 30)) * Y 3 3) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 3 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 3 (by decide)
  have hY63 :
      Y 6 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 3 (by decide)
  have hY73 :
      Y 7 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 3 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (3 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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

private theorem row17_commutatorEquation04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((6 / 11) : ℂ) + ((3 / 22) : ℂ) * ζ ^ 8 - ((21 / 44) : ℂ) * ζ ^ 12 - ((9 / 44) : ℂ) * ζ ^ 24 - ((3 / 22) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((-((63 / 44) : ℂ) + ((57 / 44) : ℂ) * ζ ^ 8 + ((12 / 11) : ℂ) * ζ ^ 12 - ((69 / 44) : ℂ) * ζ ^ 24 - ((57 / 44) : ℂ) * ζ ^ 28)) * Y 0 1
      + ((((6 / 11) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 8 + ((21 / 44) : ℂ) * ζ ^ 12 + ((9 / 44) : ℂ) * ζ ^ 24 + ((3 / 22) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((((3 / 22) : ℂ) - ((9 / 22) : ℂ) * ζ ^ 8 - ((3 / 44) : ℂ) * ζ ^ 12 + ((27 / 44) : ℂ) * ζ ^ 24 + ((9 / 22) : ℂ) * ζ ^ 28)) * Y 5 4) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY64 :
      Y 6 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 4 (by decide)
  have hY74 :
      Y 7 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 4 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (4 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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

private theorem row17_commutatorEquation05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((3 / 22) : ℂ) + ((9 / 22) : ℂ) * ζ ^ 8 + ((3 / 44) : ℂ) * ζ ^ 12 - ((27 / 44) : ℂ) * ζ ^ 24 - ((9 / 22) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((((9 / 44) : ℂ) + ((39 / 44) : ℂ) * ζ ^ 8 + ((3 / 11) : ℂ) * ζ ^ 12 - ((9 / 44) : ℂ) * ζ ^ 24 - ((39 / 44) : ℂ) * ζ ^ 28)) * Y 0 1
      + ((((6 / 11) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 8 + ((21 / 44) : ℂ) * ζ ^ 12 + ((9 / 44) : ℂ) * ζ ^ 24 + ((3 / 22) : ℂ) * ζ ^ 28)) * Y 4 5
      + ((((3 / 22) : ℂ) - ((9 / 22) : ℂ) * ζ ^ 8 - ((3 / 44) : ℂ) * ζ ^ 12 + ((27 / 44) : ℂ) * ζ ^ 24 + ((9 / 22) : ℂ) * ζ ^ 28)) * Y 5 5) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY65 :
      Y 6 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 5 (by decide)
  have hY75 :
      Y 7 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 5 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (5 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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

private theorem row17_commutatorEquation06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((2 / 41) : ℂ) - ((11 / 82) : ℂ) * ζ ^ 2 - ((3 / 82) : ℂ) * ζ ^ 6 + ((15 / 82) : ℂ) * ζ ^ 8 + ((21 / 164) : ℂ) * ζ ^ 12 - ((9 / 82) : ℂ) * ζ ^ 18 + ((11 / 82) : ℂ) * ζ ^ 22 + ((13 / 164) : ℂ) * ζ ^ 24 - ((15 / 82) : ℂ) * ζ ^ 28 + ((1 / 41) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((1 / 82) : ℂ) + ((27 / 41) : ℂ) * ζ ^ 2 + ((63 / 164) : ℂ) * ζ ^ 6 - ((55 / 82) : ℂ) * ζ ^ 8 - ((77 / 164) : ℂ) * ζ ^ 12 - ((4 / 41) : ℂ) * ζ ^ 18 - ((27 / 41) : ℂ) * ζ ^ 22 + ((12 / 41) : ℂ) * ζ ^ 24 + ((55 / 82) : ℂ) * ζ ^ 28 + ((10 / 41) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((2 / 41) : ℂ) + ((11 / 82) : ℂ) * ζ ^ 2 + ((3 / 82) : ℂ) * ζ ^ 6 - ((15 / 82) : ℂ) * ζ ^ 8 - ((21 / 164) : ℂ) * ζ ^ 12 + ((9 / 82) : ℂ) * ζ ^ 18 - ((11 / 82) : ℂ) * ζ ^ 22 - ((13 / 164) : ℂ) * ζ ^ 24 + ((15 / 82) : ℂ) * ζ ^ 28 - ((1 / 41) : ℂ) * ζ ^ 30)) * Y 6 6
      + ((-((13 / 164) : ℂ) - ((9 / 41) : ℂ) * ζ ^ 2 - ((21 / 164) : ℂ) * ζ ^ 6 + ((23 / 164) : ℂ) * ζ ^ 8 + ((3 / 41) : ℂ) * ζ ^ 12 - ((11 / 82) : ℂ) * ζ ^ 18 + ((9 / 41) : ℂ) * ζ ^ 22 - ((4 / 41) : ℂ) * ζ ^ 24 - ((23 / 164) : ℂ) * ζ ^ 28 + ((7 / 82) : ℂ) * ζ ^ 30)) * Y 7 6) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY26 :
      Y 2 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 6 (by decide)
  have hY36 :
      Y 3 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 6 (by decide)
  have hY46 :
      Y 4 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 6 (by decide)
  have hY56 :
      Y 5 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 6 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (6 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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

private theorem row17_commutatorEquation07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((13 / 164) : ℂ) + ((9 / 41) : ℂ) * ζ ^ 2 + ((21 / 164) : ℂ) * ζ ^ 6 - ((23 / 164) : ℂ) * ζ ^ 8 - ((3 / 41) : ℂ) * ζ ^ 12 + ((11 / 82) : ℂ) * ζ ^ 18 - ((9 / 41) : ℂ) * ζ ^ 22 + ((4 / 41) : ℂ) * ζ ^ 24 + ((23 / 164) : ℂ) * ζ ^ 28 - ((7 / 82) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((17 / 82) : ℂ) - ((9 / 164) : ℂ) * ζ ^ 2 + ((5 / 164) : ℂ) * ζ ^ 6 + ((4 / 41) : ℂ) * ζ ^ 8 - ((19 / 82) : ℂ) * ζ ^ 12 - ((13 / 82) : ℂ) * ζ ^ 18 + ((9 / 164) : ℂ) * ζ ^ 22 - ((1 / 41) : ℂ) * ζ ^ 24 - ((4 / 41) : ℂ) * ζ ^ 28 + ((6 / 41) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((2 / 41) : ℂ) + ((11 / 82) : ℂ) * ζ ^ 2 + ((3 / 82) : ℂ) * ζ ^ 6 - ((15 / 82) : ℂ) * ζ ^ 8 - ((21 / 164) : ℂ) * ζ ^ 12 + ((9 / 82) : ℂ) * ζ ^ 18 - ((11 / 82) : ℂ) * ζ ^ 22 - ((13 / 164) : ℂ) * ζ ^ 24 + ((15 / 82) : ℂ) * ζ ^ 28 - ((1 / 41) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((13 / 164) : ℂ) - ((9 / 41) : ℂ) * ζ ^ 2 - ((21 / 164) : ℂ) * ζ ^ 6 + ((23 / 164) : ℂ) * ζ ^ 8 + ((3 / 41) : ℂ) * ζ ^ 12 - ((11 / 82) : ℂ) * ζ ^ 18 + ((9 / 41) : ℂ) * ζ ^ 22 - ((4 / 41) : ℂ) * ζ ^ 24 - ((23 / 164) : ℂ) * ζ ^ 28 + ((7 / 82) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY27 :
      Y 2 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 7 (by decide)
  have hY37 :
      Y 3 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 7 (by decide)
  have hY47 :
      Y 4 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 7 (by decide)
  have hY57 :
      Y 5 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 7 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (7 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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

private theorem row17_commutatorEquation12
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((2 / 41) : ℂ) + ((11 / 82) : ℂ) * ζ ^ 2 + ((3 / 82) : ℂ) * ζ ^ 6 + ((15 / 82) : ℂ) * ζ ^ 8 + ((21 / 164) : ℂ) * ζ ^ 12 + ((9 / 82) : ℂ) * ζ ^ 18 - ((11 / 82) : ℂ) * ζ ^ 22 + ((13 / 164) : ℂ) * ζ ^ 24 - ((15 / 82) : ℂ) * ζ ^ 28 - ((1 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1 / 82) : ℂ) - ((27 / 41) : ℂ) * ζ ^ 2 - ((63 / 164) : ℂ) * ζ ^ 6 - ((55 / 82) : ℂ) * ζ ^ 8 - ((77 / 164) : ℂ) * ζ ^ 12 + ((4 / 41) : ℂ) * ζ ^ 18 + ((27 / 41) : ℂ) * ζ ^ 22 + ((12 / 41) : ℂ) * ζ ^ 24 + ((55 / 82) : ℂ) * ζ ^ 28 - ((10 / 41) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((1 / 82) : ℂ) + ((27 / 41) : ℂ) * ζ ^ 2 + ((63 / 164) : ℂ) * ζ ^ 6 + ((55 / 82) : ℂ) * ζ ^ 8 + ((77 / 164) : ℂ) * ζ ^ 12 - ((4 / 41) : ℂ) * ζ ^ 18 - ((27 / 41) : ℂ) * ζ ^ 22 - ((12 / 41) : ℂ) * ζ ^ 24 - ((55 / 82) : ℂ) * ζ ^ 28 + ((10 / 41) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((17 / 82) : ℂ) - ((9 / 164) : ℂ) * ζ ^ 2 + ((5 / 164) : ℂ) * ζ ^ 6 - ((4 / 41) : ℂ) * ζ ^ 8 + ((19 / 82) : ℂ) * ζ ^ 12 - ((13 / 82) : ℂ) * ζ ^ 18 + ((9 / 164) : ℂ) * ζ ^ 22 + ((1 / 41) : ℂ) * ζ ^ 24 + ((4 / 41) : ℂ) * ζ ^ 28 + ((6 / 41) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY62 :
      Y 6 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 2 (by decide)
  have hY72 :
      Y 7 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 2 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (2 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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

private theorem row17_commutatorEquation13
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((13 / 164) : ℂ) - ((9 / 41) : ℂ) * ζ ^ 2 - ((21 / 164) : ℂ) * ζ ^ 6 - ((23 / 164) : ℂ) * ζ ^ 8 - ((3 / 41) : ℂ) * ζ ^ 12 - ((11 / 82) : ℂ) * ζ ^ 18 + ((9 / 41) : ℂ) * ζ ^ 22 + ((4 / 41) : ℂ) * ζ ^ 24 + ((23 / 164) : ℂ) * ζ ^ 28 + ((7 / 82) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((17 / 82) : ℂ) + ((9 / 164) : ℂ) * ζ ^ 2 - ((5 / 164) : ℂ) * ζ ^ 6 + ((4 / 41) : ℂ) * ζ ^ 8 - ((19 / 82) : ℂ) * ζ ^ 12 + ((13 / 82) : ℂ) * ζ ^ 18 - ((9 / 164) : ℂ) * ζ ^ 22 - ((1 / 41) : ℂ) * ζ ^ 24 - ((4 / 41) : ℂ) * ζ ^ 28 - ((6 / 41) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((1 / 82) : ℂ) + ((27 / 41) : ℂ) * ζ ^ 2 + ((63 / 164) : ℂ) * ζ ^ 6 + ((55 / 82) : ℂ) * ζ ^ 8 + ((77 / 164) : ℂ) * ζ ^ 12 - ((4 / 41) : ℂ) * ζ ^ 18 - ((27 / 41) : ℂ) * ζ ^ 22 - ((12 / 41) : ℂ) * ζ ^ 24 - ((55 / 82) : ℂ) * ζ ^ 28 + ((10 / 41) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((17 / 82) : ℂ) - ((9 / 164) : ℂ) * ζ ^ 2 + ((5 / 164) : ℂ) * ζ ^ 6 - ((4 / 41) : ℂ) * ζ ^ 8 + ((19 / 82) : ℂ) * ζ ^ 12 - ((13 / 82) : ℂ) * ζ ^ 18 + ((9 / 164) : ℂ) * ζ ^ 22 + ((1 / 41) : ℂ) * ζ ^ 24 + ((4 / 41) : ℂ) * ζ ^ 28 + ((6 / 41) : ℂ) * ζ ^ 30)) * Y 3 3) = 0 := by
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 3 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 3 (by decide)
  have hY63 :
      Y 6 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 3 (by decide)
  have hY73 :
      Y 7 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 3 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (3 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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

private theorem row17_commutatorEquation14
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((6 / 11) : ℂ) + ((3 / 22) : ℂ) * ζ ^ 8 - ((21 / 44) : ℂ) * ζ ^ 12 - ((9 / 44) : ℂ) * ζ ^ 24 - ((3 / 22) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((63 / 44) : ℂ) + ((57 / 44) : ℂ) * ζ ^ 8 + ((12 / 11) : ℂ) * ζ ^ 12 - ((69 / 44) : ℂ) * ζ ^ 24 - ((57 / 44) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((63 / 44) : ℂ) - ((57 / 44) : ℂ) * ζ ^ 8 - ((12 / 11) : ℂ) * ζ ^ 12 + ((69 / 44) : ℂ) * ζ ^ 24 + ((57 / 44) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((-((9 / 44) : ℂ) - ((39 / 44) : ℂ) * ζ ^ 8 - ((3 / 11) : ℂ) * ζ ^ 12 + ((9 / 44) : ℂ) * ζ ^ 24 + ((39 / 44) : ℂ) * ζ ^ 28)) * Y 5 4) = 0 := by
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY64 :
      Y 6 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 4 (by decide)
  have hY74 :
      Y 7 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 4 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (4 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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

private theorem row17_commutatorEquation16
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((2 / 41) : ℂ) - ((11 / 82) : ℂ) * ζ ^ 2 - ((3 / 82) : ℂ) * ζ ^ 6 + ((15 / 82) : ℂ) * ζ ^ 8 + ((21 / 164) : ℂ) * ζ ^ 12 - ((9 / 82) : ℂ) * ζ ^ 18 + ((11 / 82) : ℂ) * ζ ^ 22 + ((13 / 164) : ℂ) * ζ ^ 24 - ((15 / 82) : ℂ) * ζ ^ 28 + ((1 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1 / 82) : ℂ) + ((27 / 41) : ℂ) * ζ ^ 2 + ((63 / 164) : ℂ) * ζ ^ 6 - ((55 / 82) : ℂ) * ζ ^ 8 - ((77 / 164) : ℂ) * ζ ^ 12 - ((4 / 41) : ℂ) * ζ ^ 18 - ((27 / 41) : ℂ) * ζ ^ 22 + ((12 / 41) : ℂ) * ζ ^ 24 + ((55 / 82) : ℂ) * ζ ^ 28 + ((10 / 41) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((1 / 82) : ℂ) - ((27 / 41) : ℂ) * ζ ^ 2 - ((63 / 164) : ℂ) * ζ ^ 6 + ((55 / 82) : ℂ) * ζ ^ 8 + ((77 / 164) : ℂ) * ζ ^ 12 + ((4 / 41) : ℂ) * ζ ^ 18 + ((27 / 41) : ℂ) * ζ ^ 22 - ((12 / 41) : ℂ) * ζ ^ 24 - ((55 / 82) : ℂ) * ζ ^ 28 - ((10 / 41) : ℂ) * ζ ^ 30)) * Y 6 6
      + ((((17 / 82) : ℂ) + ((9 / 164) : ℂ) * ζ ^ 2 - ((5 / 164) : ℂ) * ζ ^ 6 - ((4 / 41) : ℂ) * ζ ^ 8 + ((19 / 82) : ℂ) * ζ ^ 12 + ((13 / 82) : ℂ) * ζ ^ 18 - ((9 / 164) : ℂ) * ζ ^ 22 + ((1 / 41) : ℂ) * ζ ^ 24 + ((4 / 41) : ℂ) * ζ ^ 28 - ((6 / 41) : ℂ) * ζ ^ 30)) * Y 7 6) = 0 := by
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY26 :
      Y 2 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 6 (by decide)
  have hY36 :
      Y 3 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 6 (by decide)
  have hY46 :
      Y 4 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 6 (by decide)
  have hY56 :
      Y 5 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 6 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (6 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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

private theorem row17_commutatorEquation17
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((13 / 164) : ℂ) + ((9 / 41) : ℂ) * ζ ^ 2 + ((21 / 164) : ℂ) * ζ ^ 6 - ((23 / 164) : ℂ) * ζ ^ 8 - ((3 / 41) : ℂ) * ζ ^ 12 + ((11 / 82) : ℂ) * ζ ^ 18 - ((9 / 41) : ℂ) * ζ ^ 22 + ((4 / 41) : ℂ) * ζ ^ 24 + ((23 / 164) : ℂ) * ζ ^ 28 - ((7 / 82) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((17 / 82) : ℂ) - ((9 / 164) : ℂ) * ζ ^ 2 + ((5 / 164) : ℂ) * ζ ^ 6 + ((4 / 41) : ℂ) * ζ ^ 8 - ((19 / 82) : ℂ) * ζ ^ 12 - ((13 / 82) : ℂ) * ζ ^ 18 + ((9 / 164) : ℂ) * ζ ^ 22 - ((1 / 41) : ℂ) * ζ ^ 24 - ((4 / 41) : ℂ) * ζ ^ 28 + ((6 / 41) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((1 / 82) : ℂ) - ((27 / 41) : ℂ) * ζ ^ 2 - ((63 / 164) : ℂ) * ζ ^ 6 + ((55 / 82) : ℂ) * ζ ^ 8 + ((77 / 164) : ℂ) * ζ ^ 12 + ((4 / 41) : ℂ) * ζ ^ 18 + ((27 / 41) : ℂ) * ζ ^ 22 - ((12 / 41) : ℂ) * ζ ^ 24 - ((55 / 82) : ℂ) * ζ ^ 28 - ((10 / 41) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((((17 / 82) : ℂ) + ((9 / 164) : ℂ) * ζ ^ 2 - ((5 / 164) : ℂ) * ζ ^ 6 - ((4 / 41) : ℂ) * ζ ^ 8 + ((19 / 82) : ℂ) * ζ ^ 12 + ((13 / 82) : ℂ) * ζ ^ 18 - ((9 / 164) : ℂ) * ζ ^ 22 + ((1 / 41) : ℂ) * ζ ^ 24 + ((4 / 41) : ℂ) * ζ ^ 28 - ((6 / 41) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY27 :
      Y 2 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 7 (by decide)
  have hY37 :
      Y 3 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 7 (by decide)
  have hY47 :
      Y 4 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 7 (by decide)
  have hY57 :
      Y 5 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 7 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (7 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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

private theorem row17_commutatorEquation24
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((1 / 22) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 2 - ((5 / 22) : ℂ) * ζ ^ 6 - ((17 / 44) : ℂ) * ζ ^ 8 + ((21 / 44) : ℂ) * ζ ^ 12 + ((7 / 44) : ℂ) * ζ ^ 18 + ((1 / 11) : ℂ) * ζ ^ 22 - ((13 / 44) : ℂ) * ζ ^ 24 + ((17 / 44) : ℂ) * ζ ^ 28 - ((5 / 11) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((9 / 22) : ℂ) + ((1 / 11) : ℂ) * ζ ^ 2 - ((23 / 44) : ℂ) * ζ ^ 6 + ((5 / 22) : ℂ) * ζ ^ 8 + ((31 / 44) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 18 - ((1 / 11) : ℂ) * ζ ^ 22 - ((13 / 22) : ℂ) * ζ ^ 24 - ((5 / 22) : ℂ) * ζ ^ 28 - ((1 / 22) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((1 / 22) : ℂ) + ((1 / 11) : ℂ) * ζ ^ 2 + ((5 / 22) : ℂ) * ζ ^ 6 + ((17 / 44) : ℂ) * ζ ^ 8 - ((21 / 44) : ℂ) * ζ ^ 12 - ((7 / 44) : ℂ) * ζ ^ 18 - ((1 / 11) : ℂ) * ζ ^ 22 + ((13 / 44) : ℂ) * ζ ^ 24 - ((17 / 44) : ℂ) * ζ ^ 28 + ((5 / 11) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((3 / 22) : ℂ) + ((1 / 44) : ℂ) * ζ ^ 2 - ((7 / 22) : ℂ) * ζ ^ 6 - ((1 / 11) : ℂ) * ζ ^ 8 + ((7 / 22) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 18 - ((1 / 44) : ℂ) * ζ ^ 22 - ((5 / 44) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 28 - ((3 / 22) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY26 :
      Y 2 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 6 (by decide)
  have hY27 :
      Y 2 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 7 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY64 :
      Y 6 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 4 (by decide)
  have hY74 :
      Y 7 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 4 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (2 : Fin 8))
      (4 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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

private theorem row17_commutatorEquation25
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((3 / 22) : ℂ) - ((1 / 44) : ℂ) * ζ ^ 2 + ((7 / 22) : ℂ) * ζ ^ 6 + ((1 / 11) : ℂ) * ζ ^ 8 - ((7 / 22) : ℂ) * ζ ^ 12 - ((3 / 11) : ℂ) * ζ ^ 18 + ((1 / 44) : ℂ) * ζ ^ 22 + ((5 / 44) : ℂ) * ζ ^ 24 - ((1 / 11) : ℂ) * ζ ^ 28 + ((3 / 22) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((3 / 11) : ℂ) + ((1 / 44) : ℂ) * ζ ^ 2 + ((19 / 44) : ℂ) * ζ ^ 6 - ((3 / 44) : ℂ) * ζ ^ 8 - ((3 / 22) : ℂ) * ζ ^ 12 - ((21 / 44) : ℂ) * ζ ^ 18 - ((1 / 44) : ℂ) * ζ ^ 22 + ((5 / 22) : ℂ) * ζ ^ 24 + ((3 / 44) : ℂ) * ζ ^ 28 - ((3 / 22) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((1 / 22) : ℂ) + ((1 / 11) : ℂ) * ζ ^ 2 + ((5 / 22) : ℂ) * ζ ^ 6 + ((17 / 44) : ℂ) * ζ ^ 8 - ((21 / 44) : ℂ) * ζ ^ 12 - ((7 / 44) : ℂ) * ζ ^ 18 - ((1 / 11) : ℂ) * ζ ^ 22 + ((13 / 44) : ℂ) * ζ ^ 24 - ((17 / 44) : ℂ) * ζ ^ 28 + ((5 / 11) : ℂ) * ζ ^ 30)) * Y 4 5
      + ((-((3 / 22) : ℂ) + ((1 / 44) : ℂ) * ζ ^ 2 - ((7 / 22) : ℂ) * ζ ^ 6 - ((1 / 11) : ℂ) * ζ ^ 8 + ((7 / 22) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 18 - ((1 / 44) : ℂ) * ζ ^ 22 - ((5 / 44) : ℂ) * ζ ^ 24 + ((1 / 11) : ℂ) * ζ ^ 28 - ((3 / 22) : ℂ) * ζ ^ 30)) * Y 5 5) = 0 := by
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY26 :
      Y 2 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 6 (by decide)
  have hY27 :
      Y 2 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 7 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY65 :
      Y 6 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 5 (by decide)
  have hY75 :
      Y 7 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 5 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (2 : Fin 8))
      (5 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow17TransformedGeneratorA,
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


private theorem row17_reducedY00_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((25 / 492) : ℂ) - ((317 / 123) : ℂ) * ζ ^ 2 + ((955 / 492) : ℂ) * ζ ^ 6 - ((97 / 123) : ℂ) * ζ ^ 8 + ((109 / 164) : ℂ) * ζ ^ 12 + ((135 / 164) : ℂ) * ζ ^ 18 + ((317 / 123) : ℂ) * ζ ^ 22 + ((643 / 246) : ℂ) * ζ ^ 24 + ((97 / 123) : ℂ) * ζ ^ 28 - ((2 / 123) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((87 / 164) : ℂ) + ((77 / 246) : ℂ) * ζ ^ 2 + ((137 / 164) : ℂ) * ζ ^ 6 + ((44 / 41) : ℂ) * ζ ^ 8 + ((76 / 123) : ℂ) * ζ ^ 12 - ((71 / 123) : ℂ) * ζ ^ 18 - ((77 / 246) : ℂ) * ζ ^ 22 - ((74 / 123) : ℂ) * ζ ^ 24 - ((44 / 41) : ℂ) * ζ ^ 28 - ((16 / 41) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((((43 / 123) : ℂ) + ((210 / 41) : ℂ) * ζ ^ 2 + ((757 / 123) : ℂ) * ζ ^ 6 + ((520 / 123) : ℂ) * ζ ^ 8 + ((176 / 41) : ℂ) * ζ ^ 12 - ((476 / 123) : ℂ) * ζ ^ 18 - ((210 / 41) : ℂ) * ζ ^ 22 - ((253 / 123) : ℂ) * ζ ^ 24 - ((520 / 123) : ℂ) * ζ ^ 28 + ((137 / 41) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((3 / 82) : ℂ) + ((949 / 246) : ℂ) * ζ ^ 2 - ((3 / 82) : ℂ) * ζ ^ 4 - ((524 / 123) : ℂ) * ζ ^ 6 + ((797 / 492) : ℂ) * ζ ^ 8 + ((103 / 246) : ℂ) * ζ ^ 10 - ζ ^ 12 + ((227 / 164) : ℂ) * ζ ^ 14 - ((89 / 41) : ℂ) * ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 18 + ((1321 / 492) : ℂ) * ζ ^ 20 - ((137 / 41) : ℂ) * ζ ^ 22 - ((130 / 41) : ℂ) * ζ ^ 24 + ((411 / 164) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((87 / 164) : ℂ) - ((77 / 246) : ℂ) * ζ ^ 2 - ((87 / 164) : ℂ) * ζ ^ 4 - ((257 / 492) : ℂ) * ζ ^ 6 - ((89 / 164) : ℂ) * ζ ^ 8 + ((257 / 492) : ℂ) * ζ ^ 10 + ((89 / 164) : ℂ) * ζ ^ 12 + ((73 / 164) : ℂ) * ζ ^ 14 - ((89 / 164) : ℂ) * ζ ^ 16 + ((137 / 164) : ℂ) * ζ ^ 18 + ((130 / 123) : ℂ) * ζ ^ 20 - ((137 / 164) : ℂ) * ζ ^ 22)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY00_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((215 / 492) : ℂ) - ((37 / 41) : ℂ) * ζ ^ 2 - ((341 / 492) : ℂ) * ζ ^ 6 + ((2 / 41) : ℂ) * ζ ^ 8 - ((385 / 492) : ℂ) * ζ ^ 12 + ((289 / 492) : ℂ) * ζ ^ 18 + ((37 / 41) : ℂ) * ζ ^ 22 - ((1 / 82) : ℂ) * ζ ^ 24 - ((2 / 41) : ℂ) * ζ ^ 28 - ((155 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((691 / 492) : ℂ) - ((13 / 82) : ℂ) * ζ ^ 2 - ((25 / 492) : ℂ) * ζ ^ 6 + ((103 / 123) : ℂ) * ζ ^ 8 + ((259 / 246) : ℂ) * ζ ^ 12 - ((263 / 246) : ℂ) * ζ ^ 18 + ((13 / 82) : ℂ) * ζ ^ 22 - ((1087 / 492) : ℂ) * ζ ^ 24 - ((103 / 123) : ℂ) * ζ ^ 28 + ((85 / 492) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((87 / 164) : ℂ) + ((77 / 246) : ℂ) * ζ ^ 2 + ((137 / 164) : ℂ) * ζ ^ 6 + ((44 / 41) : ℂ) * ζ ^ 8 + ((76 / 123) : ℂ) * ζ ^ 12 - ((71 / 123) : ℂ) * ζ ^ 18 - ((77 / 246) : ℂ) * ζ ^ 22 - ((74 / 123) : ℂ) * ζ ^ 24 - ((44 / 41) : ℂ) * ζ ^ 28 - ((16 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((215 / 492) : ℂ) + ((37 / 41) : ℂ) * ζ ^ 2 + ((341 / 492) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 + ((385 / 492) : ℂ) * ζ ^ 12 - ((289 / 492) : ℂ) * ζ ^ 18 - ((37 / 41) : ℂ) * ζ ^ 22 + ((1 / 82) : ℂ) * ζ ^ 24 + ((2 / 41) : ℂ) * ζ ^ 28 + ((155 / 123) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY00_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((200 / 41) : ℂ) + ((113 / 123) : ℂ) * ζ ^ 2 + ((55 / 41) : ℂ) * ζ ^ 6 - ((415 / 123) : ℂ) * ζ ^ 8 - ((8 / 41) : ℂ) * ζ ^ 12 + ((331 / 123) : ℂ) * ζ ^ 18 - ((113 / 123) : ℂ) * ζ ^ 22 + ((202 / 41) : ℂ) * ζ ^ 24 + ((415 / 123) : ℂ) * ζ ^ 28 + ((341 / 123) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((215 / 492) : ℂ) + ((37 / 41) : ℂ) * ζ ^ 2 - ((215 / 492) : ℂ) * ζ ^ 4 - ((103 / 492) : ℂ) * ζ ^ 6 + ((191 / 492) : ℂ) * ζ ^ 8 + ((103 / 492) : ℂ) * ζ ^ 10 - ((191 / 492) : ℂ) * ζ ^ 12 + ((19 / 41) : ℂ) * ζ ^ 14 + ((191 / 492) : ℂ) * ζ ^ 16 - ((341 / 492) : ℂ) * ζ ^ 18 + ((415 / 492) : ℂ) * ζ ^ 20 + ((341 / 492) : ℂ) * ζ ^ 22)) * Y 0 0
        + ((((329 / 123) : ℂ) - ((359 / 164) : ℂ) * ζ ^ 2 - ((329 / 123) : ℂ) * ζ ^ 4 + ((1111 / 246) : ℂ) * ζ ^ 6 - ((1699 / 492) : ℂ) * ζ ^ 8 - ((2561 / 492) : ℂ) * ζ ^ 10 + ((550 / 123) : ℂ) * ζ ^ 12 + ((73 / 41) : ℂ) * ζ ^ 14 - ((955 / 492) : ℂ) * ζ ^ 16 + ((683 / 246) : ℂ) * ζ ^ 18 - ((257 / 492) : ℂ) * ζ ^ 20 - ((1705 / 492) : ℂ) * ζ ^ 22 + ((415 / 164) : ℂ) * ζ ^ 24 + ((341 / 164) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((215 / 492) : ℂ) - ((37 / 41) : ℂ) * ζ ^ 2 + ((215 / 492) : ℂ) * ζ ^ 4 + ((103 / 492) : ℂ) * ζ ^ 6 - ((191 / 492) : ℂ) * ζ ^ 8 - ((103 / 492) : ℂ) * ζ ^ 10 + ((191 / 492) : ℂ) * ζ ^ 12 - ((19 / 41) : ℂ) * ζ ^ 14 - ((191 / 492) : ℂ) * ζ ^ 16 + ((341 / 492) : ℂ) * ζ ^ 18 - ((415 / 492) : ℂ) * ζ ^ 20 - ((341 / 492) : ℂ) * ζ ^ 22)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY00_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((10 / 123) : ℂ) + ((16 / 41) : ℂ) * ζ ^ 2 + ((97 / 246) : ℂ) * ζ ^ 6 - ((17 / 123) : ℂ) * ζ ^ 8 + ((91 / 246) : ℂ) * ζ ^ 12 - ((119 / 246) : ℂ) * ζ ^ 18 - ((16 / 41) : ℂ) * ζ ^ 22 - ((53 / 246) : ℂ) * ζ ^ 24 + ((17 / 123) : ℂ) * ζ ^ 28 + ((359 / 246) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((87 / 164) : ℂ) + ((77 / 246) : ℂ) * ζ ^ 2 + ((137 / 164) : ℂ) * ζ ^ 6 + ((44 / 41) : ℂ) * ζ ^ 8 + ((76 / 123) : ℂ) * ζ ^ 12 - ((71 / 123) : ℂ) * ζ ^ 18 - ((77 / 246) : ℂ) * ζ ^ 22 - ((74 / 123) : ℂ) * ζ ^ 24 - ((44 / 41) : ℂ) * ζ ^ 28 - ((16 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((215 / 492) : ℂ) + ((37 / 41) : ℂ) * ζ ^ 2 + ((341 / 492) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 + ((385 / 492) : ℂ) * ζ ^ 12 - ((289 / 492) : ℂ) * ζ ^ 18 - ((37 / 41) : ℂ) * ζ ^ 22 + ((1 / 82) : ℂ) * ζ ^ 24 + ((2 / 41) : ℂ) * ζ ^ 28 + ((155 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((125 / 164) : ℂ) - ((69 / 82) : ℂ) * ζ ^ 2 - ((183 / 164) : ℂ) * ζ ^ 6 - ((7 / 41) : ℂ) * ζ ^ 8 - ((77 / 164) : ℂ) * ζ ^ 12 + ((107 / 164) : ℂ) * ζ ^ 18 + ((69 / 82) : ℂ) * ζ ^ 22 - ((17 / 82) : ℂ) * ζ ^ 24 + ((7 / 41) : ℂ) * ζ ^ 28 - ((31 / 41) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((53 / 164) : ℂ) + ((60 / 451) : ℂ) * ζ ^ 2 - ((639 / 1804) : ℂ) * ζ ^ 6 + ((39 / 82) : ℂ) * ζ ^ 8 - ((11 / 164) : ℂ) * ζ ^ 12 - ((687 / 1804) : ℂ) * ζ ^ 18 - ((60 / 451) : ℂ) * ζ ^ 22 - ((61 / 82) : ℂ) * ζ ^ 24 - ((39 / 82) : ℂ) * ζ ^ 28 - ((197 / 902) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY00_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((32 / 41) : ℂ) - ((1811 / 1353) : ℂ) * ζ ^ 2 - ((889 / 1353) : ℂ) * ζ ^ 6 - ((73 / 123) : ℂ) * ζ ^ 8 - ((2 / 41) : ℂ) * ζ ^ 12 + ((1187 / 1353) : ℂ) * ζ ^ 18 + ((1811 / 1353) : ℂ) * ζ ^ 22 + ((8 / 123) : ℂ) * ζ ^ 24 + ((73 / 123) : ℂ) * ζ ^ 28 - ((1225 / 1353) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((607 / 1804) : ℂ) - ((1105 / 9922) : ℂ) * ζ ^ 2 + ((607 / 1804) : ℂ) * ζ ^ 4 - ((12821 / 19844) : ℂ) * ζ ^ 6 - ((523 / 1804) : ℂ) * ζ ^ 8 + ((9199 / 19844) : ℂ) * ζ ^ 10 - ((211 / 1804) : ℂ) * ζ ^ 12 - ((255 / 9922) : ℂ) * ζ ^ 14 + ((65 / 1804) : ℂ) * ζ ^ 16 - ((4847 / 19844) : ℂ) * ζ ^ 18 - ((89 / 1804) : ℂ) * ζ ^ 20 + ((1225 / 19844) : ℂ) * ζ ^ 22 - ((73 / 902) : ℂ) * ζ ^ 24 + ((1225 / 9922) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((371 / 1804) : ℂ) + ((27141 / 19844) : ℂ) * ζ ^ 2 + ((371 / 1804) : ℂ) * ζ ^ 4 - ((17305 / 19844) : ℂ) * ζ ^ 6 + ((549 / 902) : ℂ) * ζ ^ 8 - ((4276 / 4961) : ℂ) * ζ ^ 10 - ((1647 / 1804) : ℂ) * ζ ^ 12 - ((811 / 9922) : ℂ) * ζ ^ 14 + ((65 / 451) : ℂ) * ζ ^ 16 - ((39309 / 19844) : ℂ) * ζ ^ 18 - ((111 / 451) : ℂ) * ζ ^ 20 + ((1225 / 4961) : ℂ) * ζ ^ 22 - ((1387 / 1804) : ℂ) * ζ ^ 24 + ((23275 / 19844) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((607 / 1804) : ℂ) + ((1105 / 9922) : ℂ) * ζ ^ 2 - ((607 / 1804) : ℂ) * ζ ^ 4 + ((12821 / 19844) : ℂ) * ζ ^ 6 + ((523 / 1804) : ℂ) * ζ ^ 8 - ((9199 / 19844) : ℂ) * ζ ^ 10 + ((211 / 1804) : ℂ) * ζ ^ 12 + ((255 / 9922) : ℂ) * ζ ^ 14 - ((65 / 1804) : ℂ) * ζ ^ 16 + ((4847 / 19844) : ℂ) * ζ ^ 18 + ((89 / 1804) : ℂ) * ζ ^ 20 - ((1225 / 19844) : ℂ) * ζ ^ 22 + ((73 / 902) : ℂ) * ζ ^ 24 - ((1225 / 9922) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((391 / 1804) : ℂ) - ((3131 / 9922) : ℂ) * ζ ^ 2 - ((391 / 1804) : ℂ) * ζ ^ 4 + ((11513 / 19844) : ℂ) * ζ ^ 6 - ((37 / 1804) : ℂ) * ζ ^ 8 - ((647 / 19844) : ℂ) * ζ ^ 10 + ((633 / 1804) : ℂ) * ζ ^ 12 + ((765 / 9922) : ℂ) * ζ ^ 14 - ((195 / 1804) : ℂ) * ζ ^ 16 + ((14541 / 19844) : ℂ) * ζ ^ 18 + ((267 / 1804) : ℂ) * ζ ^ 20 - ((3675 / 19844) : ℂ) * ζ ^ 22 + ((219 / 902) : ℂ) * ζ ^ 24 - ((3675 / 9922) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY00_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 0 0
      + ((-((87 / 164) : ℂ) + ((77 / 246) : ℂ) * ζ ^ 2 + ((137 / 164) : ℂ) * ζ ^ 6 + ((44 / 41) : ℂ) * ζ ^ 8 + ((76 / 123) : ℂ) * ζ ^ 12 - ((71 / 123) : ℂ) * ζ ^ 18 - ((77 / 246) : ℂ) * ζ ^ 22 - ((74 / 123) : ℂ) * ζ ^ 24 - ((44 / 41) : ℂ) * ζ ^ 28 - ((16 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((215 / 492) : ℂ) + ((37 / 41) : ℂ) * ζ ^ 2 + ((341 / 492) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 + ((385 / 492) : ℂ) * ζ ^ 12 - ((289 / 492) : ℂ) * ζ ^ 18 - ((37 / 41) : ℂ) * ζ ^ 22 + ((1 / 82) : ℂ) * ζ ^ 24 + ((2 / 41) : ℂ) * ζ ^ 28 + ((155 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((125 / 164) : ℂ) - ((69 / 82) : ℂ) * ζ ^ 2 - ((183 / 164) : ℂ) * ζ ^ 6 - ((7 / 41) : ℂ) * ζ ^ 8 - ((77 / 164) : ℂ) * ζ ^ 12 + ((107 / 164) : ℂ) * ζ ^ 18 + ((69 / 82) : ℂ) * ζ ^ 22 - ((17 / 82) : ℂ) * ζ ^ 24 + ((7 / 41) : ℂ) * ζ ^ 28 - ((31 / 41) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((53 / 164) : ℂ) + ((60 / 451) : ℂ) * ζ ^ 2 - ((639 / 1804) : ℂ) * ζ ^ 6 + ((39 / 82) : ℂ) * ζ ^ 8 - ((11 / 164) : ℂ) * ζ ^ 12 - ((687 / 1804) : ℂ) * ζ ^ 18 - ((60 / 451) : ℂ) * ζ ^ 22 - ((61 / 82) : ℂ) * ζ ^ 24 - ((39 / 82) : ℂ) * ζ ^ 28 - ((197 / 902) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY00_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) + (2 : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 + ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((179 / 246) : ℂ) - ((2 / 41) : ℂ) * ζ ^ 2 + ((7 / 6) : ℂ) * ζ ^ 4 + ((18 / 41) : ℂ) * ζ ^ 6 - ((62 / 123) : ℂ) * ζ ^ 8 - ((71 / 82) : ℂ) * ζ ^ 10 - ((73 / 246) : ℂ) * ζ ^ 12 + ((193 / 246) : ℂ) * ζ ^ 14 + ((34 / 41) : ℂ) * ζ ^ 16 - ((35 / 82) : ℂ) * ζ ^ 18 - ((94 / 123) : ℂ) * ζ ^ 20 + ((79 / 246) : ℂ) * ζ ^ 24 + ((13 / 41) : ℂ) * ζ ^ 26 - ((28 / 123) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((7 / 123) : ℂ) + ((1 / 82) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 4 + ((55 / 246) : ℂ) * ζ ^ 6 + ((31 / 246) : ℂ) * ζ ^ 8 + ((1 / 123) : ℂ) * ζ ^ 10 + ((49 / 246) : ℂ) * ζ ^ 12 - ((20 / 41) : ℂ) * ζ ^ 14 - ((46 / 123) : ℂ) * ζ ^ 16 + ((19 / 82) : ℂ) * ζ ^ 18 + ((44 / 123) : ℂ) * ζ ^ 20 - ((56 / 123) : ℂ) * ζ ^ 24 - ((20 / 123) : ℂ) * ζ ^ 26 + ((16 / 41) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((8 / 123) : ℂ) - ((103 / 246) : ℂ) * ζ ^ 2 + ((1 / 3) : ℂ) * ζ ^ 4 + ((63 / 82) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 - ((301 / 246) : ℂ) * ζ ^ 10 - ((23 / 41) : ℂ) * ζ ^ 12 + ((143 / 246) : ℂ) * ζ ^ 14 + ((39 / 41) : ℂ) * ζ ^ 16 + ((26 / 123) : ℂ) * ζ ^ 18 - ((55 / 82) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((23 / 123) : ℂ) * ζ ^ 24 + ((58 / 123) : ℂ) * ζ ^ 26 - ((8 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((179 / 246) : ℂ) + ((2 / 41) : ℂ) * ζ ^ 2 - ((7 / 6) : ℂ) * ζ ^ 4 - ((18 / 41) : ℂ) * ζ ^ 6 + ((62 / 123) : ℂ) * ζ ^ 8 + ((71 / 82) : ℂ) * ζ ^ 10 + ((73 / 246) : ℂ) * ζ ^ 12 - ((193 / 246) : ℂ) * ζ ^ 14 - ((34 / 41) : ℂ) * ζ ^ 16 + ((35 / 82) : ℂ) * ζ ^ 18 + ((94 / 123) : ℂ) * ζ ^ 20 - ((79 / 246) : ℂ) * ζ ^ 24 - ((13 / 41) : ℂ) * ζ ^ 26 + ((28 / 123) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY00_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 0 0
      + ((-((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((43 / 82) : ℂ) * ζ ^ 6 + ((31 / 82) : ℂ) * ζ ^ 8 + ((10 / 123) : ℂ) * ζ ^ 12 - ((32 / 123) : ℂ) * ζ ^ 18 + ((19 / 246) : ℂ) * ζ ^ 22 - ((13 / 246) : ℂ) * ζ ^ 24 - ((31 / 82) : ℂ) * ζ ^ 28 - ((15 / 82) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY00_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((25 / 123) : ℂ) + ((254 / 1353) : ℂ) * ζ ^ 2 + ((79 / 451) : ℂ) * ζ ^ 6 + ((20 / 41) : ℂ) * ζ ^ 8 + ((14 / 41) : ℂ) * ζ ^ 12 - ((806 / 1353) : ℂ) * ζ ^ 18 - ((254 / 1353) : ℂ) * ζ ^ 22 - ((97 / 123) : ℂ) * ζ ^ 24 - ((20 / 41) : ℂ) * ζ ^ 28 - ((199 / 1353) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((97 / 1804) : ℂ) + ((1428 / 4961) : ℂ) * ζ ^ 2 + ((97 / 1804) : ℂ) * ζ ^ 4 - ((1437 / 19844) : ℂ) * ζ ^ 6 + ((57 / 164) : ℂ) * ζ ^ 8 + ((1945 / 19844) : ℂ) * ζ ^ 10 + ((83 / 1804) : ℂ) * ζ ^ 12 + ((2463 / 19844) : ℂ) * ζ ^ 14 + ((37 / 1804) : ℂ) * ζ ^ 16 + ((309 / 19844) : ℂ) * ζ ^ 18 + ((127 / 902) : ℂ) * ζ ^ 20 + ((199 / 19844) : ℂ) * ζ ^ 22 + ((30 / 451) : ℂ) * ζ ^ 24 + ((199 / 9922) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((475 / 451) : ℂ) + ((2841 / 4961) : ℂ) * ζ ^ 2 - ((475 / 451) : ℂ) * ζ ^ 4 + ((2901 / 9922) : ℂ) * ζ ^ 6 + ((43 / 164) : ℂ) * ζ ^ 8 - ((244 / 4961) : ℂ) * ζ ^ 10 + ((248 / 451) : ℂ) * ζ ^ 12 + ((20907 / 19844) : ℂ) * ζ ^ 14 + ((37 / 451) : ℂ) * ζ ^ 16 + ((2015 / 9922) : ℂ) * ζ ^ 18 + ((2083 / 1804) : ℂ) * ζ ^ 20 + ((199 / 4961) : ℂ) * ζ ^ 22 + ((285 / 451) : ℂ) * ζ ^ 24 + ((3781 / 19844) : ℂ) * ζ ^ 26)) * Y 1 1
        + ((-((475 / 451) : ℂ) - ((2841 / 4961) : ℂ) * ζ ^ 2 + ((475 / 451) : ℂ) * ζ ^ 4 - ((2901 / 9922) : ℂ) * ζ ^ 6 - ((43 / 164) : ℂ) * ζ ^ 8 + ((244 / 4961) : ℂ) * ζ ^ 10 - ((248 / 451) : ℂ) * ζ ^ 12 - ((20907 / 19844) : ℂ) * ζ ^ 14 - ((37 / 451) : ℂ) * ζ ^ 16 - ((2015 / 9922) : ℂ) * ζ ^ 18 - ((2083 / 1804) : ℂ) * ζ ^ 20 - ((199 / 4961) : ℂ) * ζ ^ 22 - ((285 / 451) : ℂ) * ζ ^ 24 - ((3781 / 19844) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((127 / 451) : ℂ) + ((939 / 9922) : ℂ) * ζ ^ 2 + ((127 / 451) : ℂ) * ζ ^ 4 - ((4809 / 9922) : ℂ) * ζ ^ 6 + ((45 / 164) : ℂ) * ζ ^ 8 + ((1579 / 4961) : ℂ) * ζ ^ 10 - ((575 / 902) : ℂ) * ζ ^ 12 - ((8535 / 19844) : ℂ) * ζ ^ 14 + ((185 / 902) : ℂ) * ζ ^ 16 - ((1323 / 4961) : ℂ) * ζ ^ 18 - ((661 / 1804) : ℂ) * ζ ^ 20 + ((995 / 9922) : ℂ) * ζ ^ 22 - ((195 / 451) : ℂ) * ζ ^ 24 - ((2587 / 19844) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY00_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 0 0
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY00_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((15 / 41) : ℂ) * ζ ^ 4 + ((45 / 82) : ℂ) * ζ ^ 6 - ((59 / 246) : ℂ) * ζ ^ 8 - ((69 / 82) : ℂ) * ζ ^ 10 - ((19 / 246) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ((65 / 246) : ℂ) * ζ ^ 16 - ((107 / 246) : ℂ) * ζ ^ 18 - ((29 / 82) : ℂ) * ζ ^ 20 + ((35 / 246) : ℂ) * ζ ^ 22 + ((10 / 41) : ℂ) * ζ ^ 24 - ((5 / 246) : ℂ) * ζ ^ 26 - ((7 / 123) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 + ((40 / 123) : ℂ) * ζ ^ 4 - ((85 / 246) : ℂ) * ζ ^ 6 - ((19 / 82) : ℂ) * ζ ^ 8 + ((103 / 246) : ℂ) * ζ ^ 10 + ((5 / 82) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ((47 / 246) : ℂ) * ζ ^ 16 + ((13 / 41) : ℂ) * ζ ^ 18 + ((73 / 246) : ℂ) * ζ ^ 20 - ((10 / 41) : ℂ) * ζ ^ 22 - ((28 / 123) : ℂ) * ζ ^ 24 + ((16 / 123) : ℂ) * ζ ^ 26 + ((4 / 41) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((4 / 41) : ℂ) * ζ ^ 4 - ((53 / 82) : ℂ) * ζ ^ 6 + ((68 / 123) : ℂ) * ζ ^ 8 + ((125 / 82) : ℂ) * ζ ^ 10 + ((49 / 123) : ℂ) * ζ ^ 12 - ((5 / 3) : ℂ) * ζ ^ 14 - ((53 / 41) : ℂ) * ζ ^ 16 + ((17 / 123) : ℂ) * ζ ^ 18 + ((151 / 123) : ℂ) * ζ ^ 20 + ((91 / 123) : ℂ) * ζ ^ 22 - ((30 / 41) : ℂ) * ζ ^ 24 - ((95 / 123) : ℂ) * ζ ^ 26 - ((20 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 - ((40 / 123) : ℂ) * ζ ^ 4 + ((85 / 246) : ℂ) * ζ ^ 6 + ((19 / 82) : ℂ) * ζ ^ 8 - ((103 / 246) : ℂ) * ζ ^ 10 - ((5 / 82) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((47 / 246) : ℂ) * ζ ^ 16 - ((13 / 41) : ℂ) * ζ ^ 18 - ((73 / 246) : ℂ) * ζ ^ 20 + ((10 / 41) : ℂ) * ζ ^ 22 + ((28 / 123) : ℂ) * ζ ^ 24 - ((16 / 123) : ℂ) * ζ ^ 26 - ((4 / 41) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 0 0 = Y 7 7 := by
  have reduced :=
    row17_reducedY00_combinationStep05 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row17_reducedY01_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-(1 : ℂ) + ((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 12 - ζ ^ 24 - ((1 / 2) : ℂ) * ζ ^ 28)) * Y 0 1
      + ((-((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-(2 : ℂ) * ζ ^ 8 - ζ ^ 12 + ζ ^ 24 + (2 : ℂ) * ζ ^ 28)) * equation
      - (
        (((1 : ℂ) - ζ ^ 4 + ((1 / 2) : ℂ) * ζ ^ 12 + ζ ^ 16 - ((5 / 4) : ℂ) * ζ ^ 20 + ((3 / 2) : ℂ) * ζ ^ 24)) * Y 0 1
        + ((((1 / 4) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 20)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY01_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 28)) * Y 0 0
      + (((1 : ℂ) + ((3 / 4) : ℂ) * ζ ^ 12 + ((1 / 4) : ℂ) * ζ ^ 24)) * Y 0 1
      + ((-((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY01_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(1 : ℂ) - ζ ^ 8 - (2 : ℂ) * ζ ^ 12 - ζ ^ 24 + ζ ^ 28)) * equation
      - (
        ((-((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 2) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 16 + ((1 / 4) : ℂ) * ζ ^ 20)) * Y 0 0
        + ((-((9 / 4) : ℂ) + ((9 / 4) : ℂ) * ζ ^ 4 - ((5 / 4) : ℂ) * ζ ^ 8 - ((7 / 4) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 16 - (2 : ℂ) * ζ ^ 20 + ((3 / 4) : ℂ) * ζ ^ 24)) * Y 0 1
        + ((((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 16 - ((1 / 4) : ℂ) * ζ ^ 20)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY01_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 0 1
      + ((-((1 / 4) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((1 / 2) : ℂ) * ζ ^ 8 + ((1 / 4) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((((7 / 22) : ℂ) - ((3 / 22) : ℂ) * ζ ^ 8 + ((1 / 44) : ℂ) * ζ ^ 12 + ((3 / 11) : ℂ) * ζ ^ 24 + ((3 / 22) : ℂ) * ζ ^ 28)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY01_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((17 / 33) : ℂ) + ((23 / 33) : ℂ) * ζ ^ 8 + ((20 / 33) : ℂ) * ζ ^ 12 - ((13 / 33) : ℂ) * ζ ^ 24 - ((23 / 33) : ℂ) * ζ ^ 28)) * equation
      - (
        ((((34 / 121) : ℂ) - ((34 / 121) : ℂ) * ζ ^ 4 + ((40 / 121) : ℂ) * ζ ^ 8 + ((14 / 121) : ℂ) * ζ ^ 12 - ((5 / 242) : ℂ) * ζ ^ 16 + ((49 / 484) : ℂ) * ζ ^ 20 + ((23 / 242) : ℂ) * ζ ^ 24)) * Y 0 0
        + ((((357 / 484) : ℂ) - ((357 / 484) : ℂ) * ζ ^ 4 - ((449 / 484) : ℂ) * ζ ^ 8 + ((477 / 484) : ℂ) * ζ ^ 12 - ((10 / 121) : ℂ) * ζ ^ 16 + ((339 / 484) : ℂ) * ζ ^ 20 + ((437 / 484) : ℂ) * ζ ^ 24)) * Y 0 1
        + ((-((34 / 121) : ℂ) + ((34 / 121) : ℂ) * ζ ^ 4 - ((40 / 121) : ℂ) * ζ ^ 8 - ((14 / 121) : ℂ) * ζ ^ 12 + ((5 / 242) : ℂ) * ζ ^ 16 - ((49 / 484) : ℂ) * ζ ^ 20 - ((23 / 242) : ℂ) * ζ ^ 24)) * Y 4 4
        + ((-((47 / 121) : ℂ) + ((47 / 121) : ℂ) * ζ ^ 4 + ((13 / 242) : ℂ) * ζ ^ 8 - ((42 / 121) : ℂ) * ζ ^ 12 + ((15 / 242) : ℂ) * ζ ^ 16 - ((147 / 484) : ℂ) * ζ ^ 20 - ((69 / 242) : ℂ) * ζ ^ 24)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY01_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 0 1) = 0 := by
  have previous :=
    row17_reducedY01_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((4 / 33) : ℂ) - ((8 / 33) : ℂ) * ζ ^ 8 + ((5 / 33) : ℂ) * ζ ^ 12 + ((5 / 33) : ℂ) * ζ ^ 24 + ((8 / 33) : ℂ) * ζ ^ 28)) * equation
      - (
        ((-((8 / 121) : ℂ) + ((8 / 121) : ℂ) * ζ ^ 4 - ((81 / 484) : ℂ) * ζ ^ 8 - ((19 / 484) : ℂ) * ζ ^ 12 + ((3 / 484) : ℂ) * ζ ^ 16 - ((9 / 242) : ℂ) * ζ ^ 20 - ((4 / 121) : ℂ) * ζ ^ 24)) * Y 1 0
        + ((-((21 / 121) : ℂ) + ((21 / 121) : ℂ) * ζ ^ 4 - ((41 / 242) : ℂ) * ζ ^ 8 - ((41 / 121) : ℂ) * ζ ^ 12 + ((3 / 121) : ℂ) * ζ ^ 16 - ((127 / 484) : ℂ) * ζ ^ 20 - ((38 / 121) : ℂ) * ζ ^ 24)) * Y 1 1
        + ((((21 / 121) : ℂ) - ((21 / 121) : ℂ) * ζ ^ 4 + ((41 / 242) : ℂ) * ζ ^ 8 + ((41 / 121) : ℂ) * ζ ^ 12 - ((3 / 121) : ℂ) * ζ ^ 16 + ((127 / 484) : ℂ) * ζ ^ 20 + ((38 / 121) : ℂ) * ζ ^ 24)) * Y 4 4
        + ((((71 / 242) : ℂ) - ((71 / 242) : ℂ) * ζ ^ 4 + ((12 / 121) : ℂ) * ζ ^ 8 + ((37 / 242) : ℂ) * ζ ^ 12 + ((15 / 242) : ℂ) * ζ ^ 16 - ((15 / 484) : ℂ) * ζ ^ 20 + ((26 / 121) : ℂ) * ζ ^ 24)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 0 1 = 0 := by
  have reduced :=
    row17_reducedY01_combinationStep03 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row17_reducedY10_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((3 : ℂ) - (6 : ℂ) * ζ ^ 8 - ((25 / 4) : ℂ) * ζ ^ 12 + ((9 / 4) : ℂ) * ζ ^ 24 + (6 : ℂ) * ζ ^ 28)) * Y 0 1
      + (((2 : ℂ) - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 12 + ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    (((7 : ℂ) - (5 : ℂ) * ζ ^ 8 - (2 : ℂ) * ζ ^ 12 + (11 : ℂ) * ζ ^ 24 + (5 : ℂ) * ζ ^ 28)) * equation
      - (
        ((-((5 / 4) : ℂ) + ((5 / 4) : ℂ) * ζ ^ 4 - ((7 / 4) : ℂ) * ζ ^ 8 + ((39 / 4) : ℂ) * ζ ^ 12 - (6 : ℂ) * ζ ^ 16 + ((13 / 4) : ℂ) * ζ ^ 20 + ((15 / 4) : ℂ) * ζ ^ 24)) * Y 0 1
        + ((-(2 : ℂ) + (2 : ℂ) * ζ ^ 4 - ((3 / 2) : ℂ) * ζ ^ 8 + ((3 / 2) : ℂ) * ζ ^ 12 - ((3 / 2) : ℂ) * ζ ^ 16 - ((5 / 4) : ℂ) * ζ ^ 20)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY10_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 12 - ((7 / 4) : ℂ) * ζ ^ 24 - ζ ^ 28)) * Y 0 0
      + ((((9 / 4) : ℂ) + ((5 / 4) : ℂ) * ζ ^ 8 - ((1 / 2) : ℂ) * ζ ^ 12 + ((3 / 4) : ℂ) * ζ ^ 24 - ((5 / 4) : ℂ) * ζ ^ 28)) * Y 0 1
      + (((2 : ℂ) - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 12 + ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 12 + ((7 / 4) : ℂ) * ζ ^ 24 + ζ ^ 28)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY10_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-(3 : ℂ) - (8 : ℂ) * ζ ^ 8 - (4 : ℂ) * ζ ^ 12 + (4 : ℂ) * ζ ^ 24 + (8 : ℂ) * ζ ^ 28)) * equation
      - (
        ((-ζ ^ 8 + ζ ^ 12 - ζ ^ 16 + (2 : ℂ) * ζ ^ 20)) * Y 0 0
        + ((-(7 : ℂ) * ζ ^ 8 + ζ ^ 12 + (5 : ℂ) * ζ ^ 16 - (7 : ℂ) * ζ ^ 20 + (6 : ℂ) * ζ ^ 24)) * Y 0 1
        + ((ζ ^ 8 - ζ ^ 12 + ζ ^ 16 - (2 : ℂ) * ζ ^ 20)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY10_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((2 : ℂ) - ((1 / 2) : ℂ) * ζ ^ 8 - ((1 / 4) : ℂ) * ζ ^ 12 + ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 12 + ((7 / 4) : ℂ) * ζ ^ 24 + ζ ^ 28)) * Y 1 1
      + ((ζ ^ 8 + ((3 / 4) : ℂ) * ζ ^ 12 - ((7 / 4) : ℂ) * ζ ^ 24 - ζ ^ 28)) * Y 4 4
      + ((((1 / 22) : ℂ) + ((10 / 11) : ℂ) * ζ ^ 8 + ((41 / 44) : ℂ) * ζ ^ 12 - ((3 / 44) : ℂ) * ζ ^ 24 - ((10 / 11) : ℂ) * ζ ^ 28)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY10_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((29 / 33) : ℂ) + ((8 / 33) : ℂ) * ζ ^ 8 - ((38 / 33) : ℂ) * ζ ^ 12 - ((38 / 33) : ℂ) * ζ ^ 24 - ((8 / 33) : ℂ) * ζ ^ 28)) * equation
      - (
        ((-((58 / 121) : ℂ) + ((58 / 121) : ℂ) * ζ ^ 4 + ((123 / 242) : ℂ) * ζ ^ 8 - ((7 / 242) : ℂ) * ζ ^ 12 + ((15 / 242) : ℂ) * ζ ^ 16 + ((21 / 121) : ℂ) * ζ ^ 20 + ((4 / 121) : ℂ) * ζ ^ 24)) * Y 0 0
        + ((((120 / 121) : ℂ) - ((120 / 121) : ℂ) * ζ ^ 4 + ((367 / 121) : ℂ) * ζ ^ 8 + ((8 / 121) : ℂ) * ζ ^ 12 + ((30 / 121) : ℂ) * ζ ^ 16 + ((377 / 242) : ℂ) * ζ ^ 20 + ((38 / 121) : ℂ) * ζ ^ 24)) * Y 0 1
        + ((((58 / 121) : ℂ) - ((58 / 121) : ℂ) * ζ ^ 4 - ((123 / 242) : ℂ) * ζ ^ 8 + ((7 / 242) : ℂ) * ζ ^ 12 - ((15 / 242) : ℂ) * ζ ^ 16 - ((21 / 121) : ℂ) * ζ ^ 20 - ((4 / 121) : ℂ) * ζ ^ 24)) * Y 4 4
        + ((((9 / 121) : ℂ) - ((9 / 121) : ℂ) * ζ ^ 4 - ((281 / 242) : ℂ) * ζ ^ 8 + ((21 / 242) : ℂ) * ζ ^ 12 - ((45 / 242) : ℂ) * ζ ^ 16 - ((63 / 121) : ℂ) * ζ ^ 20 - ((12 / 121) : ℂ) * ζ ^ 24)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY10_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 1 0) = 0 := by
  have previous :=
    row17_reducedY10_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((7 / 11) : ℂ) + ((13 / 33) : ℂ) * ζ ^ 8 - ((4 / 33) : ℂ) * ζ ^ 12 + ((29 / 33) : ℂ) * ζ ^ 24 - ((13 / 33) : ℂ) * ζ ^ 28)) * equation
      - (
        ((((79 / 121) : ℂ) - ((79 / 121) : ℂ) * ζ ^ 4 + ((3 / 121) : ℂ) * ζ ^ 8 + ((17 / 121) : ℂ) * ζ ^ 12 - ((21 / 242) : ℂ) * ζ ^ 16 - ((45 / 484) : ℂ) * ζ ^ 20 + ((13 / 242) : ℂ) * ζ ^ 24)) * Y 1 0
        + ((-((441 / 484) : ℂ) + ((441 / 484) : ℂ) * ζ ^ 4 - ((799 / 484) : ℂ) * ζ ^ 8 + ((415 / 484) : ℂ) * ζ ^ 12 - ((42 / 121) : ℂ) * ζ ^ 16 - ((499 / 484) : ℂ) * ζ ^ 20 + ((247 / 484) : ℂ) * ζ ^ 24)) * Y 1 1
        + ((((441 / 484) : ℂ) - ((441 / 484) : ℂ) * ζ ^ 4 + ((799 / 484) : ℂ) * ζ ^ 8 - ((415 / 484) : ℂ) * ζ ^ 12 + ((42 / 121) : ℂ) * ζ ^ 16 + ((499 / 484) : ℂ) * ζ ^ 20 - ((247 / 484) : ℂ) * ζ ^ 24)) * Y 4 4
        + ((-((41 / 484) : ℂ) + ((41 / 484) : ℂ) * ζ ^ 4 + ((87 / 484) : ℂ) * ζ ^ 8 + ((251 / 484) : ℂ) * ζ ^ 12 - ((105 / 121) : ℂ) * ζ ^ 16 + ((507 / 484) : ℂ) * ζ ^ 20 - ((169 / 484) : ℂ) * ζ ^ 24)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY10
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 1 0 = 0 := by
  have reduced :=
    row17_reducedY10_combinationStep03 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row17_reducedY11_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((467 / 492) : ℂ) - ((317 / 123) : ℂ) * ζ ^ 2 + ((955 / 492) : ℂ) * ζ ^ 6 + ((913 / 246) : ℂ) * ζ ^ 8 + ((191 / 164) : ℂ) * ζ ^ 12 + ((135 / 164) : ℂ) * ζ ^ 18 + ((317 / 123) : ℂ) * ζ ^ 22 - ((559 / 492) : ℂ) * ζ ^ 24 - ((913 / 246) : ℂ) * ζ ^ 28 - ((2 / 123) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((87 / 164) : ℂ) + ((77 / 246) : ℂ) * ζ ^ 2 + ((137 / 164) : ℂ) * ζ ^ 6 - ((29 / 164) : ℂ) * ζ ^ 8 - ((311 / 492) : ℂ) * ζ ^ 12 - ((71 / 123) : ℂ) * ζ ^ 18 - ((77 / 246) : ℂ) * ζ ^ 22 + ((73 / 492) : ℂ) * ζ ^ 24 + ((29 / 164) : ℂ) * ζ ^ 28 - ((16 / 41) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((572 / 123) : ℂ) + ((210 / 41) : ℂ) * ζ ^ 2 + ((757 / 123) : ℂ) * ζ ^ 6 + ((151 / 123) : ℂ) * ζ ^ 8 - ((29 / 41) : ℂ) * ζ ^ 12 - ((476 / 123) : ℂ) * ζ ^ 18 - ((210 / 41) : ℂ) * ζ ^ 22 - ((499 / 123) : ℂ) * ζ ^ 24 - ((151 / 123) : ℂ) * ζ ^ 28 + ((137 / 41) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((35 / 164) : ℂ) + ((949 / 246) : ℂ) * ζ ^ 2 + ((35 / 164) : ℂ) * ζ ^ 4 - ((524 / 123) : ℂ) * ζ ^ 6 - ((16 / 123) : ℂ) * ζ ^ 8 + ((103 / 246) : ℂ) * ζ ^ 10 - ((15 / 4) : ℂ) * ζ ^ 12 + ((227 / 164) : ℂ) * ζ ^ 14 + ((116 / 41) : ℂ) * ζ ^ 16 - ((1 / 2) : ℂ) * ζ ^ 18 - ((893 / 492) : ℂ) * ζ ^ 20 - ((137 / 41) : ℂ) * ζ ^ 22 - ((151 / 164) : ℂ) * ζ ^ 24 + ((411 / 164) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((87 / 164) : ℂ) - ((77 / 246) : ℂ) * ζ ^ 2 - ((87 / 164) : ℂ) * ζ ^ 4 - ((257 / 492) : ℂ) * ζ ^ 6 + ((29 / 41) : ℂ) * ζ ^ 8 + ((257 / 492) : ℂ) * ζ ^ 10 - ((29 / 41) : ℂ) * ζ ^ 12 + ((73 / 164) : ℂ) * ζ ^ 14 + ((29 / 41) : ℂ) * ζ ^ 16 + ((137 / 164) : ℂ) * ζ ^ 18 + ((151 / 492) : ℂ) * ζ ^ 20 - ((137 / 164) : ℂ) * ζ ^ 22)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY11_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((277 / 492) : ℂ) - ((37 / 41) : ℂ) * ζ ^ 2 - ((341 / 492) : ℂ) * ζ ^ 6 - ((37 / 82) : ℂ) * ζ ^ 8 - ((139 / 492) : ℂ) * ζ ^ 12 + ((289 / 492) : ℂ) * ζ ^ 18 + ((37 / 41) : ℂ) * ζ ^ 22 + ((203 / 164) : ℂ) * ζ ^ 24 + ((37 / 82) : ℂ) * ζ ^ 28 - ((155 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((((104 / 123) : ℂ) - ((13 / 82) : ℂ) * ζ ^ 2 - ((25 / 492) : ℂ) * ζ ^ 6 - ((941 / 492) : ℂ) * ζ ^ 8 - ((589 / 492) : ℂ) * ζ ^ 12 - ((263 / 246) : ℂ) * ζ ^ 18 + ((13 / 82) : ℂ) * ζ ^ 22 + ((1127 / 492) : ℂ) * ζ ^ 24 + ((941 / 492) : ℂ) * ζ ^ 28 + ((85 / 492) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((87 / 164) : ℂ) + ((77 / 246) : ℂ) * ζ ^ 2 + ((137 / 164) : ℂ) * ζ ^ 6 - ((29 / 164) : ℂ) * ζ ^ 8 - ((311 / 492) : ℂ) * ζ ^ 12 - ((71 / 123) : ℂ) * ζ ^ 18 - ((77 / 246) : ℂ) * ζ ^ 22 + ((73 / 492) : ℂ) * ζ ^ 24 + ((29 / 164) : ℂ) * ζ ^ 28 - ((16 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((277 / 492) : ℂ) + ((37 / 41) : ℂ) * ζ ^ 2 + ((341 / 492) : ℂ) * ζ ^ 6 + ((37 / 82) : ℂ) * ζ ^ 8 + ((139 / 492) : ℂ) * ζ ^ 12 - ((289 / 492) : ℂ) * ζ ^ 18 - ((37 / 41) : ℂ) * ζ ^ 22 - ((203 / 164) : ℂ) * ζ ^ 24 - ((37 / 82) : ℂ) * ζ ^ 28 + ((155 / 123) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY11_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((46 / 41) : ℂ) + ((113 / 123) : ℂ) * ζ ^ 2 + ((55 / 41) : ℂ) * ζ ^ 6 + ((692 / 123) : ℂ) * ζ ^ 8 + ((74 / 41) : ℂ) * ζ ^ 12 + ((331 / 123) : ℂ) * ζ ^ 18 - ((113 / 123) : ℂ) * ζ ^ 22 - ((249 / 41) : ℂ) * ζ ^ 24 - ((692 / 123) : ℂ) * ζ ^ 28 + ((341 / 123) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((277 / 492) : ℂ) + ((37 / 41) : ℂ) * ζ ^ 2 + ((277 / 492) : ℂ) * ζ ^ 4 - ((103 / 492) : ℂ) * ζ ^ 6 - ((55 / 492) : ℂ) * ζ ^ 8 + ((103 / 492) : ℂ) * ζ ^ 10 + ((55 / 492) : ℂ) * ζ ^ 12 + ((19 / 41) : ℂ) * ζ ^ 14 - ((55 / 492) : ℂ) * ζ ^ 16 - ((341 / 492) : ℂ) * ζ ^ 18 - ((173 / 123) : ℂ) * ζ ^ 20 + ((341 / 492) : ℂ) * ζ ^ 22)) * Y 0 0
        + ((-((1021 / 492) : ℂ) - ((359 / 164) : ℂ) * ζ ^ 2 + ((1021 / 492) : ℂ) * ζ ^ 4 + ((1111 / 246) : ℂ) * ζ ^ 6 + ((713 / 123) : ℂ) * ζ ^ 8 - ((2561 / 492) : ℂ) * ζ ^ 10 - ((2351 / 492) : ℂ) * ζ ^ 12 + ((73 / 41) : ℂ) * ζ ^ 14 + ((275 / 492) : ℂ) * ζ ^ 16 + ((683 / 246) : ℂ) * ζ ^ 18 + ((1219 / 492) : ℂ) * ζ ^ 20 - ((1705 / 492) : ℂ) * ζ ^ 22 - ((173 / 41) : ℂ) * ζ ^ 24 + ((341 / 164) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((277 / 492) : ℂ) - ((37 / 41) : ℂ) * ζ ^ 2 - ((277 / 492) : ℂ) * ζ ^ 4 + ((103 / 492) : ℂ) * ζ ^ 6 + ((55 / 492) : ℂ) * ζ ^ 8 - ((103 / 492) : ℂ) * ζ ^ 10 - ((55 / 492) : ℂ) * ζ ^ 12 - ((19 / 41) : ℂ) * ζ ^ 14 + ((55 / 492) : ℂ) * ζ ^ 16 + ((341 / 492) : ℂ) * ζ ^ 18 + ((173 / 123) : ℂ) * ζ ^ 20 - ((341 / 492) : ℂ) * ζ ^ 22)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY11_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((10 / 123) : ℂ) + ((16 / 41) : ℂ) * ζ ^ 2 + ((97 / 246) : ℂ) * ζ ^ 6 - ((17 / 123) : ℂ) * ζ ^ 8 + ((91 / 246) : ℂ) * ζ ^ 12 - ((119 / 246) : ℂ) * ζ ^ 18 - ((16 / 41) : ℂ) * ζ ^ 22 - ((53 / 246) : ℂ) * ζ ^ 24 + ((17 / 123) : ℂ) * ζ ^ 28 + ((359 / 246) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((87 / 164) : ℂ) + ((77 / 246) : ℂ) * ζ ^ 2 + ((137 / 164) : ℂ) * ζ ^ 6 - ((29 / 164) : ℂ) * ζ ^ 8 - ((311 / 492) : ℂ) * ζ ^ 12 - ((71 / 123) : ℂ) * ζ ^ 18 - ((77 / 246) : ℂ) * ζ ^ 22 + ((73 / 492) : ℂ) * ζ ^ 24 + ((29 / 164) : ℂ) * ζ ^ 28 - ((16 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((277 / 492) : ℂ) + ((37 / 41) : ℂ) * ζ ^ 2 + ((341 / 492) : ℂ) * ζ ^ 6 + ((37 / 82) : ℂ) * ζ ^ 8 + ((139 / 492) : ℂ) * ζ ^ 12 - ((289 / 492) : ℂ) * ζ ^ 18 - ((37 / 41) : ℂ) * ζ ^ 22 - ((203 / 164) : ℂ) * ζ ^ 24 - ((37 / 82) : ℂ) * ζ ^ 28 + ((155 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((203 / 164) : ℂ) - ((69 / 82) : ℂ) * ζ ^ 2 - ((183 / 164) : ℂ) * ζ ^ 6 - ((55 / 82) : ℂ) * ζ ^ 8 + ((5 / 164) : ℂ) * ζ ^ 12 + ((107 / 164) : ℂ) * ζ ^ 18 + ((69 / 82) : ℂ) * ζ ^ 22 + ((171 / 164) : ℂ) * ζ ^ 24 + ((55 / 82) : ℂ) * ζ ^ 28 - ((31 / 41) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((237 / 1804) : ℂ) + ((60 / 451) : ℂ) * ζ ^ 2 - ((639 / 1804) : ℂ) * ζ ^ 6 - ((421 / 451) : ℂ) * ζ ^ 8 - ((449 / 1804) : ℂ) * ζ ^ 12 - ((687 / 1804) : ℂ) * ζ ^ 18 - ((60 / 451) : ℂ) * ζ ^ 22 + ((1487 / 1804) : ℂ) * ζ ^ 24 + ((421 / 451) : ℂ) * ζ ^ 28 - ((197 / 902) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY11_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((1814 / 1353) : ℂ) - ((1811 / 1353) : ℂ) * ζ ^ 2 - ((889 / 1353) : ℂ) * ζ ^ 6 + ((74 / 451) : ℂ) * ζ ^ 8 - ((104 / 451) : ℂ) * ζ ^ 12 + ((1187 / 1353) : ℂ) * ζ ^ 18 + ((1811 / 1353) : ℂ) * ζ ^ 22 + ((1195 / 1353) : ℂ) * ζ ^ 24 - ((74 / 451) : ℂ) * ζ ^ 28 - ((1225 / 1353) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((10051 / 19844) : ℂ) - ((1105 / 9922) : ℂ) * ζ ^ 2 - ((10051 / 19844) : ℂ) * ζ ^ 4 - ((12821 / 19844) : ℂ) * ζ ^ 6 - ((1407 / 19844) : ℂ) * ζ ^ 8 + ((9199 / 19844) : ℂ) * ζ ^ 10 + ((1861 / 19844) : ℂ) * ζ ^ 12 - ((255 / 9922) : ℂ) * ζ ^ 14 - ((1417 / 19844) : ℂ) * ζ ^ 16 - ((4847 / 19844) : ℂ) * ζ ^ 18 - ((542 / 4961) : ℂ) * ζ ^ 20 + ((1225 / 19844) : ℂ) * ζ ^ 22 + ((111 / 4961) : ℂ) * ζ ^ 24 + ((1225 / 9922) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((9851 / 9922) : ℂ) + ((27141 / 19844) : ℂ) * ζ ^ 2 + ((9851 / 9922) : ℂ) * ζ ^ 4 - ((17305 / 19844) : ℂ) * ζ ^ 6 - ((25109 / 19844) : ℂ) * ζ ^ 8 - ((4276 / 4961) : ℂ) * ζ ^ 10 + ((4943 / 9922) : ℂ) * ζ ^ 12 - ((811 / 9922) : ℂ) * ζ ^ 14 - ((1417 / 4961) : ℂ) * ζ ^ 16 - ((39309 / 19844) : ℂ) * ζ ^ 18 - ((21817 / 19844) : ℂ) * ζ ^ 20 + ((1225 / 4961) : ℂ) * ζ ^ 22 + ((2109 / 9922) : ℂ) * ζ ^ 24 + ((23275 / 19844) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((10051 / 19844) : ℂ) + ((1105 / 9922) : ℂ) * ζ ^ 2 + ((10051 / 19844) : ℂ) * ζ ^ 4 + ((12821 / 19844) : ℂ) * ζ ^ 6 + ((1407 / 19844) : ℂ) * ζ ^ 8 - ((9199 / 19844) : ℂ) * ζ ^ 10 - ((1861 / 19844) : ℂ) * ζ ^ 12 + ((255 / 9922) : ℂ) * ζ ^ 14 + ((1417 / 19844) : ℂ) * ζ ^ 16 + ((4847 / 19844) : ℂ) * ζ ^ 18 + ((542 / 4961) : ℂ) * ζ ^ 20 - ((1225 / 19844) : ℂ) * ζ ^ 22 - ((111 / 4961) : ℂ) * ζ ^ 24 - ((1225 / 9922) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((1021 / 19844) : ℂ) - ((3131 / 9922) : ℂ) * ζ ^ 2 - ((1021 / 19844) : ℂ) * ζ ^ 4 + ((11513 / 19844) : ℂ) * ζ ^ 6 + ((9105 / 19844) : ℂ) * ζ ^ 8 - ((647 / 19844) : ℂ) * ζ ^ 10 - ((5583 / 19844) : ℂ) * ζ ^ 12 + ((765 / 9922) : ℂ) * ζ ^ 14 + ((4251 / 19844) : ℂ) * ζ ^ 16 + ((14541 / 19844) : ℂ) * ζ ^ 18 + ((1626 / 4961) : ℂ) * ζ ^ 20 - ((3675 / 19844) : ℂ) * ζ ^ 22 - ((333 / 4961) : ℂ) * ζ ^ 24 - ((3675 / 9922) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY11_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((87 / 164) : ℂ) + ((77 / 246) : ℂ) * ζ ^ 2 + ((137 / 164) : ℂ) * ζ ^ 6 - ((29 / 164) : ℂ) * ζ ^ 8 - ((311 / 492) : ℂ) * ζ ^ 12 - ((71 / 123) : ℂ) * ζ ^ 18 - ((77 / 246) : ℂ) * ζ ^ 22 + ((73 / 492) : ℂ) * ζ ^ 24 + ((29 / 164) : ℂ) * ζ ^ 28 - ((16 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((277 / 492) : ℂ) + ((37 / 41) : ℂ) * ζ ^ 2 + ((341 / 492) : ℂ) * ζ ^ 6 + ((37 / 82) : ℂ) * ζ ^ 8 + ((139 / 492) : ℂ) * ζ ^ 12 - ((289 / 492) : ℂ) * ζ ^ 18 - ((37 / 41) : ℂ) * ζ ^ 22 - ((203 / 164) : ℂ) * ζ ^ 24 - ((37 / 82) : ℂ) * ζ ^ 28 + ((155 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((203 / 164) : ℂ) - ((69 / 82) : ℂ) * ζ ^ 2 - ((183 / 164) : ℂ) * ζ ^ 6 - ((55 / 82) : ℂ) * ζ ^ 8 + ((5 / 164) : ℂ) * ζ ^ 12 + ((107 / 164) : ℂ) * ζ ^ 18 + ((69 / 82) : ℂ) * ζ ^ 22 + ((171 / 164) : ℂ) * ζ ^ 24 + ((55 / 82) : ℂ) * ζ ^ 28 - ((31 / 41) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((237 / 1804) : ℂ) + ((60 / 451) : ℂ) * ζ ^ 2 - ((639 / 1804) : ℂ) * ζ ^ 6 - ((421 / 451) : ℂ) * ζ ^ 8 - ((449 / 1804) : ℂ) * ζ ^ 12 - ((687 / 1804) : ℂ) * ζ ^ 18 - ((60 / 451) : ℂ) * ζ ^ 22 + ((1487 / 1804) : ℂ) * ζ ^ 24 + ((421 / 451) : ℂ) * ζ ^ 28 - ((197 / 902) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY11_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) + (2 : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 + ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((179 / 246) : ℂ) - ((2 / 41) : ℂ) * ζ ^ 2 + ((7 / 6) : ℂ) * ζ ^ 4 + ((18 / 41) : ℂ) * ζ ^ 6 - ((62 / 123) : ℂ) * ζ ^ 8 - ((71 / 82) : ℂ) * ζ ^ 10 - ((73 / 246) : ℂ) * ζ ^ 12 + ((193 / 246) : ℂ) * ζ ^ 14 + ((34 / 41) : ℂ) * ζ ^ 16 - ((35 / 82) : ℂ) * ζ ^ 18 - ((94 / 123) : ℂ) * ζ ^ 20 + ((79 / 246) : ℂ) * ζ ^ 24 + ((13 / 41) : ℂ) * ζ ^ 26 - ((28 / 123) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((7 / 123) : ℂ) + ((1 / 82) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 4 + ((55 / 246) : ℂ) * ζ ^ 6 + ((31 / 246) : ℂ) * ζ ^ 8 + ((1 / 123) : ℂ) * ζ ^ 10 + ((49 / 246) : ℂ) * ζ ^ 12 - ((20 / 41) : ℂ) * ζ ^ 14 - ((46 / 123) : ℂ) * ζ ^ 16 + ((19 / 82) : ℂ) * ζ ^ 18 + ((44 / 123) : ℂ) * ζ ^ 20 - ((56 / 123) : ℂ) * ζ ^ 24 - ((20 / 123) : ℂ) * ζ ^ 26 + ((16 / 41) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((8 / 123) : ℂ) - ((103 / 246) : ℂ) * ζ ^ 2 + ((1 / 3) : ℂ) * ζ ^ 4 + ((63 / 82) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 - ((301 / 246) : ℂ) * ζ ^ 10 - ((23 / 41) : ℂ) * ζ ^ 12 + ((143 / 246) : ℂ) * ζ ^ 14 + ((39 / 41) : ℂ) * ζ ^ 16 + ((26 / 123) : ℂ) * ζ ^ 18 - ((55 / 82) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((23 / 123) : ℂ) * ζ ^ 24 + ((58 / 123) : ℂ) * ζ ^ 26 - ((8 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((179 / 246) : ℂ) + ((2 / 41) : ℂ) * ζ ^ 2 - ((7 / 6) : ℂ) * ζ ^ 4 - ((18 / 41) : ℂ) * ζ ^ 6 + ((62 / 123) : ℂ) * ζ ^ 8 + ((71 / 82) : ℂ) * ζ ^ 10 + ((73 / 246) : ℂ) * ζ ^ 12 - ((193 / 246) : ℂ) * ζ ^ 14 - ((34 / 41) : ℂ) * ζ ^ 16 + ((35 / 82) : ℂ) * ζ ^ 18 + ((94 / 123) : ℂ) * ζ ^ 20 - ((79 / 246) : ℂ) * ζ ^ 24 - ((13 / 41) : ℂ) * ζ ^ 26 + ((28 / 123) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY11_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((43 / 82) : ℂ) * ζ ^ 6 + ((31 / 82) : ℂ) * ζ ^ 8 + ((10 / 123) : ℂ) * ζ ^ 12 - ((32 / 123) : ℂ) * ζ ^ 18 + ((19 / 246) : ℂ) * ζ ^ 22 - ((13 / 246) : ℂ) * ζ ^ 24 - ((31 / 82) : ℂ) * ζ ^ 28 - ((15 / 82) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((83 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY11_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((78 / 451) : ℂ) + ((254 / 1353) : ℂ) * ζ ^ 2 + ((79 / 451) : ℂ) * ζ ^ 6 - ((775 / 1353) : ℂ) * ζ ^ 8 - ((727 / 1353) : ℂ) * ζ ^ 12 - ((806 / 1353) : ℂ) * ζ ^ 18 - ((254 / 1353) : ℂ) * ζ ^ 22 + ((901 / 1353) : ℂ) * ζ ^ 24 + ((775 / 1353) : ℂ) * ζ ^ 28 - ((199 / 1353) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1395 / 19844) : ℂ) + ((1428 / 4961) : ℂ) * ζ ^ 2 + ((1395 / 19844) : ℂ) * ζ ^ 4 - ((1437 / 19844) : ℂ) * ζ ^ 6 - ((3337 / 9922) : ℂ) * ζ ^ 8 + ((1945 / 19844) : ℂ) * ζ ^ 10 - ((356 / 4961) : ℂ) * ζ ^ 12 + ((2463 / 19844) : ℂ) * ζ ^ 14 - ((63 / 9922) : ℂ) * ζ ^ 16 + ((309 / 19844) : ℂ) * ζ ^ 18 - ((2577 / 19844) : ℂ) * ζ ^ 20 + ((199 / 19844) : ℂ) * ζ ^ 22 - ((775 / 9922) : ℂ) * ζ ^ 24 + ((199 / 9922) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((19649 / 19844) : ℂ) + ((2841 / 4961) : ℂ) * ζ ^ 2 + ((19649 / 19844) : ℂ) * ζ ^ 4 + ((2901 / 9922) : ℂ) * ζ ^ 6 + ((2745 / 9922) : ℂ) * ζ ^ 8 - ((244 / 4961) : ℂ) * ζ ^ 10 - ((14221 / 19844) : ℂ) * ζ ^ 12 + ((20907 / 19844) : ℂ) * ζ ^ 14 - ((126 / 4961) : ℂ) * ζ ^ 16 + ((2015 / 9922) : ℂ) * ζ ^ 18 - ((20219 / 19844) : ℂ) * ζ ^ 20 + ((199 / 4961) : ℂ) * ζ ^ 22 - ((14725 / 19844) : ℂ) * ζ ^ 24 + ((3781 / 19844) : ℂ) * ζ ^ 26)) * Y 1 1
        + ((((19649 / 19844) : ℂ) - ((2841 / 4961) : ℂ) * ζ ^ 2 - ((19649 / 19844) : ℂ) * ζ ^ 4 - ((2901 / 9922) : ℂ) * ζ ^ 6 - ((2745 / 9922) : ℂ) * ζ ^ 8 + ((244 / 4961) : ℂ) * ζ ^ 10 + ((14221 / 19844) : ℂ) * ζ ^ 12 - ((20907 / 19844) : ℂ) * ζ ^ 14 + ((126 / 4961) : ℂ) * ζ ^ 16 - ((2015 / 9922) : ℂ) * ζ ^ 18 + ((20219 / 19844) : ℂ) * ζ ^ 20 - ((199 / 4961) : ℂ) * ζ ^ 22 + ((14725 / 19844) : ℂ) * ζ ^ 24 - ((3781 / 19844) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((3309 / 19844) : ℂ) + ((939 / 9922) : ℂ) * ζ ^ 2 - ((3309 / 19844) : ℂ) * ζ ^ 4 - ((4809 / 9922) : ℂ) * ζ ^ 6 - ((2462 / 4961) : ℂ) * ζ ^ 8 + ((1579 / 4961) : ℂ) * ζ ^ 10 + ((11335 / 19844) : ℂ) * ζ ^ 12 - ((8535 / 19844) : ℂ) * ζ ^ 14 - ((315 / 4961) : ℂ) * ζ ^ 16 - ((1323 / 4961) : ℂ) * ζ ^ 18 + ((3963 / 19844) : ℂ) * ζ ^ 20 + ((995 / 9922) : ℂ) * ζ ^ 22 + ((10075 / 19844) : ℂ) * ζ ^ 24 - ((2587 / 19844) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY11_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 1 1
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY11_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((15 / 41) : ℂ) * ζ ^ 4 + ((45 / 82) : ℂ) * ζ ^ 6 - ((59 / 246) : ℂ) * ζ ^ 8 - ((69 / 82) : ℂ) * ζ ^ 10 - ((19 / 246) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ((65 / 246) : ℂ) * ζ ^ 16 - ((107 / 246) : ℂ) * ζ ^ 18 - ((29 / 82) : ℂ) * ζ ^ 20 + ((35 / 246) : ℂ) * ζ ^ 22 + ((10 / 41) : ℂ) * ζ ^ 24 - ((5 / 246) : ℂ) * ζ ^ 26 - ((7 / 123) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 + ((40 / 123) : ℂ) * ζ ^ 4 - ((85 / 246) : ℂ) * ζ ^ 6 - ((19 / 82) : ℂ) * ζ ^ 8 + ((103 / 246) : ℂ) * ζ ^ 10 + ((5 / 82) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ((47 / 246) : ℂ) * ζ ^ 16 + ((13 / 41) : ℂ) * ζ ^ 18 + ((73 / 246) : ℂ) * ζ ^ 20 - ((10 / 41) : ℂ) * ζ ^ 22 - ((28 / 123) : ℂ) * ζ ^ 24 + ((16 / 123) : ℂ) * ζ ^ 26 + ((4 / 41) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((4 / 41) : ℂ) * ζ ^ 4 - ((53 / 82) : ℂ) * ζ ^ 6 + ((68 / 123) : ℂ) * ζ ^ 8 + ((125 / 82) : ℂ) * ζ ^ 10 + ((49 / 123) : ℂ) * ζ ^ 12 - ((5 / 3) : ℂ) * ζ ^ 14 - ((53 / 41) : ℂ) * ζ ^ 16 + ((17 / 123) : ℂ) * ζ ^ 18 + ((151 / 123) : ℂ) * ζ ^ 20 + ((91 / 123) : ℂ) * ζ ^ 22 - ((30 / 41) : ℂ) * ζ ^ 24 - ((95 / 123) : ℂ) * ζ ^ 26 - ((20 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 - ((40 / 123) : ℂ) * ζ ^ 4 + ((85 / 246) : ℂ) * ζ ^ 6 + ((19 / 82) : ℂ) * ζ ^ 8 - ((103 / 246) : ℂ) * ζ ^ 10 - ((5 / 82) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((47 / 246) : ℂ) * ζ ^ 16 - ((13 / 41) : ℂ) * ζ ^ 18 - ((73 / 246) : ℂ) * ζ ^ 20 + ((10 / 41) : ℂ) * ζ ^ 22 + ((28 / 123) : ℂ) * ζ ^ 24 - ((16 / 123) : ℂ) * ζ ^ 26 - ((4 / 41) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY11
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 1 1 = Y 7 7 := by
  have reduced :=
    row17_reducedY11_combinationStep05 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row17_reducedY22_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((221 / 246) : ℂ) + ((719 / 246) : ℂ) * ζ ^ 8 + ((75 / 41) : ℂ) * ζ ^ 12 + ((727 / 492) : ℂ) * ζ ^ 24 - ((719 / 246) : ℂ) * ζ ^ 28)) * Y 0 1
      + ((-((87 / 82) : ℂ) + ((147 / 164) : ℂ) * ζ ^ 8 - ((7 / 492) : ℂ) * ζ ^ 12 - ((223 / 492) : ℂ) * ζ ^ 24 - ((147 / 164) : ℂ) * ζ ^ 28)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((529 / 123) : ℂ) + ((671 / 123) : ℂ) * ζ ^ 8 + ((147 / 41) : ℂ) * ζ ^ 12 - ((752 / 123) : ℂ) * ζ ^ 24 - ((671 / 123) : ℂ) * ζ ^ 28)) * equation
      - (
        ((-((29 / 164) : ℂ) + ((29 / 164) : ℂ) * ζ ^ 4 + ((733 / 492) : ℂ) * ζ ^ 8 - ((19 / 4) : ℂ) * ζ ^ 12 + ((27 / 41) : ℂ) * ζ ^ 16 + ((107 / 123) : ℂ) * ζ ^ 20 - ((671 / 164) : ℂ) * ζ ^ 24)) * Y 0 1
        + ((((87 / 82) : ℂ) - ((87 / 82) : ℂ) * ζ ^ 4 + ((27 / 164) : ℂ) * ζ ^ 8 - ((27 / 164) : ℂ) * ζ ^ 12 + ((27 / 164) : ℂ) * ζ ^ 16 + ((671 / 492) : ℂ) * ζ ^ 20)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY22_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((31 / 246) : ℂ) - ((33 / 82) : ℂ) * ζ ^ 8 - ((131 / 123) : ℂ) * ζ ^ 12 + ((201 / 164) : ℂ) * ζ ^ 24 + ((33 / 82) : ℂ) * ζ ^ 28)) * Y 0 0
      + ((-((275 / 492) : ℂ) - ((529 / 492) : ℂ) * ζ ^ 8 - ((71 / 492) : ℂ) * ζ ^ 12 + ((10 / 123) : ℂ) * ζ ^ 24 + ((529 / 492) : ℂ) * ζ ^ 28)) * Y 0 1
      + ((-((87 / 82) : ℂ) + ((147 / 164) : ℂ) * ζ ^ 8 - ((7 / 492) : ℂ) * ζ ^ 12 - ((223 / 492) : ℂ) * ζ ^ 24 - ((147 / 164) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((31 / 246) : ℂ) + ((33 / 82) : ℂ) * ζ ^ 8 + ((131 / 123) : ℂ) * ζ ^ 12 - ((201 / 164) : ℂ) * ζ ^ 24 - ((33 / 82) : ℂ) * ζ ^ 28)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY22_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((154 / 41) : ℂ) + ((277 / 123) : ℂ) * ζ ^ 8 + ((66 / 41) : ℂ) * ζ ^ 12 - ((47 / 41) : ℂ) * ζ ^ 24 - ((277 / 123) : ℂ) * ζ ^ 28)) * equation
      - (
        ((-((31 / 246) : ℂ) + ((31 / 246) : ℂ) * ζ ^ 4 + ((34 / 123) : ℂ) * ζ ^ 8 - ((34 / 123) : ℂ) * ζ ^ 12 + ((34 / 123) : ℂ) * ζ ^ 16 - ((277 / 492) : ℂ) * ζ ^ 20)) * Y 0 0
        + ((((295 / 492) : ℂ) - ((295 / 492) : ℂ) * ζ ^ 4 + ((1153 / 492) : ℂ) * ζ ^ 8 - ((151 / 492) : ℂ) * ζ ^ 12 - ((170 / 123) : ℂ) * ζ ^ 16 + ((481 / 246) : ℂ) * ζ ^ 20 - ((277 / 164) : ℂ) * ζ ^ 24)) * Y 0 1
        + ((((31 / 246) : ℂ) - ((31 / 246) : ℂ) * ζ ^ 4 - ((34 / 123) : ℂ) * ζ ^ 8 + ((34 / 123) : ℂ) * ζ ^ 12 - ((34 / 123) : ℂ) * ζ ^ 16 + ((277 / 492) : ℂ) * ζ ^ 20)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY22_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((49 / 246) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 - ((51 / 82) : ℂ) * ζ ^ 8 - ((185 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((169 / 164) : ℂ) * ζ ^ 24 + ((51 / 82) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((235 / 492) : ℂ) + ((16 / 41) : ℂ) * ζ ^ 2 + ((97 / 246) : ℂ) * ζ ^ 6 - ((461 / 492) : ℂ) * ζ ^ 8 - ((253 / 492) : ℂ) * ζ ^ 12 - ((119 / 246) : ℂ) * ζ ^ 18 - ((16 / 41) : ℂ) * ζ ^ 22 + ((73 / 246) : ℂ) * ζ ^ 24 + ((461 / 492) : ℂ) * ζ ^ 28 + ((359 / 246) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((87 / 82) : ℂ) + ((147 / 164) : ℂ) * ζ ^ 8 - ((7 / 492) : ℂ) * ζ ^ 12 - ((223 / 492) : ℂ) * ζ ^ 24 - ((147 / 164) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((31 / 246) : ℂ) + ((33 / 82) : ℂ) * ζ ^ 8 + ((131 / 123) : ℂ) * ζ ^ 12 - ((201 / 164) : ℂ) * ζ ^ 24 - ((33 / 82) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((17 / 123) : ℂ) - ((79 / 82) : ℂ) * ζ ^ 2 + ((6 / 41) : ℂ) * ζ ^ 6 + ((49 / 123) : ℂ) * ζ ^ 8 + ((85 / 246) : ℂ) * ζ ^ 12 + ((13 / 123) : ℂ) * ζ ^ 18 + ((79 / 82) : ℂ) * ζ ^ 22 - ((28 / 41) : ℂ) * ζ ^ 24 - ((49 / 123) : ℂ) * ζ ^ 28 - ((53 / 123) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have previous :=
    row17_reducedY22_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation02
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((2 / 3) : ℂ) + (2 : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 - ((8 / 3) : ℂ) * ζ ^ 12 - ((4 / 3) : ℂ) * ζ ^ 18 - (2 : ℂ) * ζ ^ 22 + ((10 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28)) * equation
      - (
        ((((44 / 123) : ℂ) + ((61 / 246) : ℂ) * ζ ^ 2 - ((11 / 123) : ℂ) * ζ ^ 4 - ((151 / 246) : ℂ) * ζ ^ 6 + ((23 / 41) : ℂ) * ζ ^ 8 + ((73 / 82) : ℂ) * ζ ^ 10 - ((22 / 41) : ℂ) * ζ ^ 12 - ((53 / 82) : ℂ) * ζ ^ 14 + ((28 / 41) : ℂ) * ζ ^ 16 + ((14 / 41) : ℂ) * ζ ^ 18 - ((95 / 246) : ℂ) * ζ ^ 20 - ((8 / 123) : ℂ) * ζ ^ 22 - ((5 / 41) : ℂ) * ζ ^ 24 - ((2 / 123) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((11 / 123) : ℂ) - ((35 / 41) : ℂ) * ζ ^ 2 - ((151 / 123) : ℂ) * ζ ^ 4 + ((8 / 41) : ℂ) * ζ ^ 6 - ((137 / 246) : ℂ) * ζ ^ 8 - ((45 / 41) : ℂ) * ζ ^ 10 + ((37 / 123) : ℂ) * ζ ^ 12 + ((107 / 123) : ℂ) * ζ ^ 14 - ((48 / 41) : ℂ) * ζ ^ 16 - ((31 / 123) : ℂ) * ζ ^ 18 + ((304 / 123) : ℂ) * ζ ^ 20 - ((80 / 123) : ℂ) * ζ ^ 22 + ((55 / 123) : ℂ) * ζ ^ 24 - ((20 / 123) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((44 / 123) : ℂ) - ((61 / 246) : ℂ) * ζ ^ 2 + ((11 / 123) : ℂ) * ζ ^ 4 + ((151 / 246) : ℂ) * ζ ^ 6 - ((23 / 41) : ℂ) * ζ ^ 8 - ((73 / 82) : ℂ) * ζ ^ 10 + ((22 / 41) : ℂ) * ζ ^ 12 + ((53 / 82) : ℂ) * ζ ^ 14 - ((28 / 41) : ℂ) * ζ ^ 16 - ((14 / 41) : ℂ) * ζ ^ 18 + ((95 / 246) : ℂ) * ζ ^ 20 + ((8 / 123) : ℂ) * ζ ^ 22 + ((5 / 41) : ℂ) * ζ ^ 24 + ((2 / 123) : ℂ) * ζ ^ 26)) * Y 2 2
        + ((((7 / 82) : ℂ) + ((39 / 41) : ℂ) * ζ ^ 2 + ((29 / 82) : ℂ) * ζ ^ 4 - ((131 / 123) : ℂ) * ζ ^ 6 - ((25 / 123) : ℂ) * ζ ^ 8 + ((295 / 246) : ℂ) * ζ ^ 10 + ((71 / 246) : ℂ) * ζ ^ 12 - ((167 / 246) : ℂ) * ζ ^ 14 + ((7 / 123) : ℂ) * ζ ^ 16 + ((89 / 246) : ℂ) * ζ ^ 18 - ((11 / 41) : ℂ) * ζ ^ 20 - ((28 / 123) : ℂ) * ζ ^ 22 - ((23 / 246) : ℂ) * ζ ^ 24 - ((7 / 123) : ℂ) * ζ ^ 26)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY22_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((10 / 123) : ℂ) + ((16 / 41) : ℂ) * ζ ^ 2 + ((97 / 246) : ℂ) * ζ ^ 6 - ((17 / 123) : ℂ) * ζ ^ 8 + ((91 / 246) : ℂ) * ζ ^ 12 - ((119 / 246) : ℂ) * ζ ^ 18 - ((16 / 41) : ℂ) * ζ ^ 22 - ((53 / 246) : ℂ) * ζ ^ 24 + ((17 / 123) : ℂ) * ζ ^ 28 + ((359 / 246) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((87 / 82) : ℂ) + ((147 / 164) : ℂ) * ζ ^ 8 - ((7 / 492) : ℂ) * ζ ^ 12 - ((223 / 492) : ℂ) * ζ ^ 24 - ((147 / 164) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((31 / 246) : ℂ) + ((33 / 82) : ℂ) * ζ ^ 8 + ((131 / 123) : ℂ) * ζ ^ 12 - ((201 / 164) : ℂ) * ζ ^ 24 - ((33 / 82) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((17 / 123) : ℂ) - ((79 / 82) : ℂ) * ζ ^ 2 + ((6 / 41) : ℂ) * ζ ^ 6 + ((49 / 123) : ℂ) * ζ ^ 8 + ((85 / 246) : ℂ) * ζ ^ 12 + ((13 / 123) : ℂ) * ζ ^ 18 + ((79 / 82) : ℂ) * ζ ^ 22 - ((28 / 41) : ℂ) * ζ ^ 24 - ((49 / 123) : ℂ) * ζ ^ 28 - ((53 / 123) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((39 / 82) : ℂ) - ((69 / 82) : ℂ) * ζ ^ 8 - ((18 / 41) : ℂ) * ζ ^ 12 + ((137 / 164) : ℂ) * ζ ^ 24 + ((69 / 82) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((-((173 / 902) : ℂ) - ((413 / 902) : ℂ) * ζ ^ 8 - ((285 / 902) : ℂ) * ζ ^ 12 + ((145 / 1804) : ℂ) * ζ ^ 24 + ((413 / 902) : ℂ) * ζ ^ 28)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY22_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((758 / 1353) : ℂ) - ((581 / 1353) : ℂ) * ζ ^ 8 - ((126 / 451) : ℂ) * ζ ^ 12 + ((1283 / 1353) : ℂ) * ζ ^ 24 + ((581 / 1353) : ℂ) * ζ ^ 28)) * equation
      - (
        ((((1687 / 9922) : ℂ) - ((1687 / 9922) : ℂ) * ζ ^ 4 - ((1790 / 4961) : ℂ) * ζ ^ 8 - ((115 / 4961) : ℂ) * ζ ^ 12 - ((351 / 9922) : ℂ) * ζ ^ 16 - ((3147 / 19844) : ℂ) * ζ ^ 20 - ((581 / 9922) : ℂ) * ζ ^ 24)) * Y 0 0
        + ((-((23783 / 19844) : ℂ) + ((23783 / 19844) : ℂ) * ζ ^ 4 - ((13031 / 19844) : ℂ) * ζ ^ 8 - ((8231 / 19844) : ℂ) * ζ ^ 12 - ((702 / 4961) : ℂ) * ζ ^ 16 - ((26701 / 19844) : ℂ) * ζ ^ 20 - ((11039 / 19844) : ℂ) * ζ ^ 24)) * Y 0 1
        + ((-((1687 / 9922) : ℂ) + ((1687 / 9922) : ℂ) * ζ ^ 4 + ((1790 / 4961) : ℂ) * ζ ^ 8 + ((115 / 4961) : ℂ) * ζ ^ 12 + ((351 / 9922) : ℂ) * ζ ^ 16 + ((3147 / 19844) : ℂ) * ζ ^ 20 + ((581 / 9922) : ℂ) * ζ ^ 24)) * Y 4 4
        + ((((2661 / 9922) : ℂ) - ((2661 / 9922) : ℂ) * ζ ^ 4 + ((4349 / 9922) : ℂ) * ζ ^ 8 + ((345 / 4961) : ℂ) * ζ ^ 12 + ((1053 / 9922) : ℂ) * ζ ^ 16 + ((9441 / 19844) : ℂ) * ζ ^ 20 + ((1743 / 9922) : ℂ) * ζ ^ 24)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY22_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((87 / 82) : ℂ) + ((147 / 164) : ℂ) * ζ ^ 8 - ((7 / 492) : ℂ) * ζ ^ 12 - ((223 / 492) : ℂ) * ζ ^ 24 - ((147 / 164) : ℂ) * ζ ^ 28)) * Y 1 0
      + ((-((31 / 246) : ℂ) + ((33 / 82) : ℂ) * ζ ^ 8 + ((131 / 123) : ℂ) * ζ ^ 12 - ((201 / 164) : ℂ) * ζ ^ 24 - ((33 / 82) : ℂ) * ζ ^ 28)) * Y 1 1
      + ((((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((17 / 123) : ℂ) - ((79 / 82) : ℂ) * ζ ^ 2 + ((6 / 41) : ℂ) * ζ ^ 6 + ((49 / 123) : ℂ) * ζ ^ 8 + ((85 / 246) : ℂ) * ζ ^ 12 + ((13 / 123) : ℂ) * ζ ^ 18 + ((79 / 82) : ℂ) * ζ ^ 22 - ((28 / 41) : ℂ) * ζ ^ 24 - ((49 / 123) : ℂ) * ζ ^ 28 - ((53 / 123) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((39 / 82) : ℂ) - ((69 / 82) : ℂ) * ζ ^ 8 - ((18 / 41) : ℂ) * ζ ^ 12 + ((137 / 164) : ℂ) * ζ ^ 24 + ((69 / 82) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((-((173 / 902) : ℂ) - ((413 / 902) : ℂ) * ζ ^ 8 - ((285 / 902) : ℂ) * ζ ^ 12 + ((145 / 1804) : ℂ) * ζ ^ 24 + ((413 / 902) : ℂ) * ζ ^ 28)) * Y 5 4
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY22_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) + (2 : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 + ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((179 / 246) : ℂ) - ((2 / 41) : ℂ) * ζ ^ 2 + ((7 / 6) : ℂ) * ζ ^ 4 + ((18 / 41) : ℂ) * ζ ^ 6 - ((62 / 123) : ℂ) * ζ ^ 8 - ((71 / 82) : ℂ) * ζ ^ 10 - ((73 / 246) : ℂ) * ζ ^ 12 + ((193 / 246) : ℂ) * ζ ^ 14 + ((34 / 41) : ℂ) * ζ ^ 16 - ((35 / 82) : ℂ) * ζ ^ 18 - ((94 / 123) : ℂ) * ζ ^ 20 + ((79 / 246) : ℂ) * ζ ^ 24 + ((13 / 41) : ℂ) * ζ ^ 26 - ((28 / 123) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((7 / 123) : ℂ) + ((1 / 82) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 4 + ((55 / 246) : ℂ) * ζ ^ 6 + ((31 / 246) : ℂ) * ζ ^ 8 + ((1 / 123) : ℂ) * ζ ^ 10 + ((49 / 246) : ℂ) * ζ ^ 12 - ((20 / 41) : ℂ) * ζ ^ 14 - ((46 / 123) : ℂ) * ζ ^ 16 + ((19 / 82) : ℂ) * ζ ^ 18 + ((44 / 123) : ℂ) * ζ ^ 20 - ((56 / 123) : ℂ) * ζ ^ 24 - ((20 / 123) : ℂ) * ζ ^ 26 + ((16 / 41) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((8 / 123) : ℂ) - ((103 / 246) : ℂ) * ζ ^ 2 + ((1 / 3) : ℂ) * ζ ^ 4 + ((63 / 82) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 - ((301 / 246) : ℂ) * ζ ^ 10 - ((23 / 41) : ℂ) * ζ ^ 12 + ((143 / 246) : ℂ) * ζ ^ 14 + ((39 / 41) : ℂ) * ζ ^ 16 + ((26 / 123) : ℂ) * ζ ^ 18 - ((55 / 82) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((23 / 123) : ℂ) * ζ ^ 24 + ((58 / 123) : ℂ) * ζ ^ 26 - ((8 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((179 / 246) : ℂ) + ((2 / 41) : ℂ) * ζ ^ 2 - ((7 / 6) : ℂ) * ζ ^ 4 - ((18 / 41) : ℂ) * ζ ^ 6 + ((62 / 123) : ℂ) * ζ ^ 8 + ((71 / 82) : ℂ) * ζ ^ 10 + ((73 / 246) : ℂ) * ζ ^ 12 - ((193 / 246) : ℂ) * ζ ^ 14 - ((34 / 41) : ℂ) * ζ ^ 16 + ((35 / 82) : ℂ) * ζ ^ 18 + ((94 / 123) : ℂ) * ζ ^ 20 - ((79 / 246) : ℂ) * ζ ^ 24 - ((13 / 41) : ℂ) * ζ ^ 26 + ((28 / 123) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY22_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((57 / 82) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((43 / 82) : ℂ) * ζ ^ 6 + ((85 / 164) : ℂ) * ζ ^ 8 - ((47 / 492) : ℂ) * ζ ^ 12 - ((32 / 123) : ℂ) * ζ ^ 18 + ((19 / 246) : ℂ) * ζ ^ 22 - ((197 / 492) : ℂ) * ζ ^ 24 - ((85 / 164) : ℂ) * ζ ^ 28 - ((15 / 82) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((197 / 246) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 + ((51 / 82) : ℂ) * ζ ^ 8 + ((185 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 - ((169 / 164) : ℂ) * ζ ^ 24 - ((51 / 82) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + (((1 : ℂ))) * Y 2 2
      + ((((39 / 82) : ℂ) - ((69 / 82) : ℂ) * ζ ^ 8 - ((18 / 41) : ℂ) * ζ ^ 12 + ((137 / 164) : ℂ) * ζ ^ 24 + ((69 / 82) : ℂ) * ζ ^ 28)) * Y 4 4
      + ((-((173 / 902) : ℂ) - ((413 / 902) : ℂ) * ζ ^ 8 - ((285 / 902) : ℂ) * ζ ^ 12 + ((145 / 1804) : ℂ) * ζ ^ 24 + ((413 / 902) : ℂ) * ζ ^ 28)) * Y 5 4
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY22_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation12
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((4 / 3) : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 18 - ((4 / 3) : ℂ) * ζ ^ 22 + (2 : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((15 / 41) : ℂ) + ((35 / 246) : ℂ) * ζ ^ 2 + ((67 / 123) : ℂ) * ζ ^ 4 - ((86 / 123) : ℂ) * ζ ^ 6 - ((17 / 82) : ℂ) * ζ ^ 8 + ((116 / 123) : ℂ) * ζ ^ 10 - ((11 / 82) : ℂ) * ζ ^ 12 - ((69 / 82) : ℂ) * ζ ^ 14 + ((77 / 246) : ℂ) * ζ ^ 16 + ((115 / 246) : ℂ) * ζ ^ 18 - ((28 / 123) : ℂ) * ζ ^ 20 - ((55 / 246) : ℂ) * ζ ^ 22 - ((2 / 123) : ℂ) * ζ ^ 24 + ((5 / 41) : ℂ) * ζ ^ 26 + ((2 / 123) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((83 / 123) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 - ((191 / 123) : ℂ) * ζ ^ 4 + ((125 / 246) : ℂ) * ζ ^ 6 + ((155 / 123) : ℂ) * ζ ^ 8 - ((115 / 82) : ℂ) * ζ ^ 10 - ((1 / 123) : ℂ) * ζ ^ 12 + ((65 / 41) : ℂ) * ζ ^ 14 - ((107 / 123) : ℂ) * ζ ^ 16 - ((27 / 41) : ℂ) * ζ ^ 18 + ((57 / 41) : ℂ) * ζ ^ 20 - ((29 / 123) : ℂ) * ζ ^ 22 - ((20 / 123) : ℂ) * ζ ^ 24 - ((55 / 123) : ℂ) * ζ ^ 26 + ((20 / 123) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((83 / 123) : ℂ) + ((19 / 246) : ℂ) * ζ ^ 2 + ((191 / 123) : ℂ) * ζ ^ 4 - ((125 / 246) : ℂ) * ζ ^ 6 - ((155 / 123) : ℂ) * ζ ^ 8 + ((115 / 82) : ℂ) * ζ ^ 10 + ((1 / 123) : ℂ) * ζ ^ 12 - ((65 / 41) : ℂ) * ζ ^ 14 + ((107 / 123) : ℂ) * ζ ^ 16 + ((27 / 41) : ℂ) * ζ ^ 18 - ((57 / 41) : ℂ) * ζ ^ 20 + ((29 / 123) : ℂ) * ζ ^ 22 + ((20 / 123) : ℂ) * ζ ^ 24 + ((55 / 123) : ℂ) * ζ ^ 26 - ((20 / 123) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((17 / 123) : ℂ) - ((169 / 246) : ℂ) * ζ ^ 2 + ((8 / 123) : ℂ) * ζ ^ 4 + ((57 / 82) : ℂ) * ζ ^ 6 + ((101 / 246) : ℂ) * ζ ^ 8 - ((203 / 246) : ℂ) * ζ ^ 10 - ((89 / 246) : ℂ) * ζ ^ 12 + ((45 / 82) : ℂ) * ζ ^ 14 + ((71 / 246) : ℂ) * ζ ^ 16 - ((58 / 123) : ℂ) * ζ ^ 18 - ((11 / 82) : ℂ) * ζ ^ 20 + ((14 / 41) : ℂ) * ζ ^ 22 + ((4 / 41) : ℂ) * ζ ^ 24 - ((8 / 123) : ℂ) * ζ ^ 26 - ((4 / 41) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY22_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((43 / 82) : ℂ) * ζ ^ 6 + ((31 / 82) : ℂ) * ζ ^ 8 + ((10 / 123) : ℂ) * ζ ^ 12 - ((32 / 123) : ℂ) * ζ ^ 18 + ((19 / 246) : ℂ) * ζ ^ 22 - ((13 / 246) : ℂ) * ζ ^ 24 - ((31 / 82) : ℂ) * ζ ^ 28 - ((15 / 82) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + (((1 : ℂ))) * Y 2 2
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY22_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((509 / 1353) : ℂ) - ((115 / 1353) : ℂ) * ζ ^ 8 - ((265 / 1353) : ℂ) * ζ ^ 12 - ((166 / 1353) : ℂ) * ζ ^ 24 + ((115 / 1353) : ℂ) * ζ ^ 28)) * equation
      - (
        ((-((1231 / 9922) : ℂ) + ((1231 / 9922) : ℂ) * ζ ^ 4 + ((223 / 19844) : ℂ) * ζ ^ 8 - ((511 / 19844) : ℂ) * ζ ^ 12 + ((281 / 19844) : ℂ) * ζ ^ 16 + ((217 / 19844) : ℂ) * ζ ^ 20 - ((115 / 9922) : ℂ) * ζ ^ 24)) * Y 1 0
        + ((((1251 / 19844) : ℂ) - ((1251 / 19844) : ℂ) * ζ ^ 4 + ((10693 / 19844) : ℂ) * ζ ^ 8 - ((3309 / 19844) : ℂ) * ζ ^ 12 + ((281 / 4961) : ℂ) * ζ ^ 16 + ((1347 / 9922) : ℂ) * ζ ^ 20 - ((2185 / 19844) : ℂ) * ζ ^ 24)) * Y 1 1
        + ((-((1251 / 19844) : ℂ) + ((1251 / 19844) : ℂ) * ζ ^ 4 - ((10693 / 19844) : ℂ) * ζ ^ 8 + ((3309 / 19844) : ℂ) * ζ ^ 12 - ((281 / 4961) : ℂ) * ζ ^ 16 - ((1347 / 9922) : ℂ) * ζ ^ 20 + ((2185 / 19844) : ℂ) * ζ ^ 24)) * Y 4 4
        + ((-((2279 / 19844) : ℂ) + ((2279 / 19844) : ℂ) * ζ ^ 4 - ((4403 / 19844) : ℂ) * ζ ^ 8 - ((1315 / 19844) : ℂ) * ζ ^ 12 + ((1405 / 9922) : ℂ) * ζ ^ 16 - ((827 / 4961) : ℂ) * ζ ^ 20 + ((1495 / 19844) : ℂ) * ζ ^ 24)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY22_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 2 2
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY22_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((15 / 41) : ℂ) * ζ ^ 4 + ((45 / 82) : ℂ) * ζ ^ 6 - ((59 / 246) : ℂ) * ζ ^ 8 - ((69 / 82) : ℂ) * ζ ^ 10 - ((19 / 246) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ((65 / 246) : ℂ) * ζ ^ 16 - ((107 / 246) : ℂ) * ζ ^ 18 - ((29 / 82) : ℂ) * ζ ^ 20 + ((35 / 246) : ℂ) * ζ ^ 22 + ((10 / 41) : ℂ) * ζ ^ 24 - ((5 / 246) : ℂ) * ζ ^ 26 - ((7 / 123) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 + ((40 / 123) : ℂ) * ζ ^ 4 - ((85 / 246) : ℂ) * ζ ^ 6 - ((19 / 82) : ℂ) * ζ ^ 8 + ((103 / 246) : ℂ) * ζ ^ 10 + ((5 / 82) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ((47 / 246) : ℂ) * ζ ^ 16 + ((13 / 41) : ℂ) * ζ ^ 18 + ((73 / 246) : ℂ) * ζ ^ 20 - ((10 / 41) : ℂ) * ζ ^ 22 - ((28 / 123) : ℂ) * ζ ^ 24 + ((16 / 123) : ℂ) * ζ ^ 26 + ((4 / 41) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((4 / 41) : ℂ) * ζ ^ 4 - ((53 / 82) : ℂ) * ζ ^ 6 + ((68 / 123) : ℂ) * ζ ^ 8 + ((125 / 82) : ℂ) * ζ ^ 10 + ((49 / 123) : ℂ) * ζ ^ 12 - ((5 / 3) : ℂ) * ζ ^ 14 - ((53 / 41) : ℂ) * ζ ^ 16 + ((17 / 123) : ℂ) * ζ ^ 18 + ((151 / 123) : ℂ) * ζ ^ 20 + ((91 / 123) : ℂ) * ζ ^ 22 - ((30 / 41) : ℂ) * ζ ^ 24 - ((95 / 123) : ℂ) * ζ ^ 26 - ((20 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 - ((40 / 123) : ℂ) * ζ ^ 4 + ((85 / 246) : ℂ) * ζ ^ 6 + ((19 / 82) : ℂ) * ζ ^ 8 - ((103 / 246) : ℂ) * ζ ^ 10 - ((5 / 82) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((47 / 246) : ℂ) * ζ ^ 16 - ((13 / 41) : ℂ) * ζ ^ 18 - ((73 / 246) : ℂ) * ζ ^ 20 + ((10 / 41) : ℂ) * ζ ^ 22 + ((28 / 123) : ℂ) * ζ ^ 24 - ((16 / 123) : ℂ) * ζ ^ 26 - ((4 / 41) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY22
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 2 2 = Y 7 7 := by
  have reduced :=
    row17_reducedY22_combinationStep07 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row17_reducedY23_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((1381 / 246) : ℂ) - ((707 / 492) : ℂ) * ζ ^ 2 - ((983 / 492) : ℂ) * ζ ^ 6 - ((337 / 123) : ℂ) * ζ ^ 8 - ((427 / 492) : ℂ) * ζ ^ 12 - ((1555 / 492) : ℂ) * ζ ^ 18 + ((707 / 492) : ℂ) * ζ ^ 22 + ((2633 / 492) : ℂ) * ζ ^ 24 + ((337 / 123) : ℂ) * ζ ^ 28 - ((1627 / 492) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((25 / 246) : ℂ) - ((61 / 41) : ℂ) * ζ ^ 2 + ((65 / 492) : ℂ) * ζ ^ 6 + ((347 / 246) : ℂ) * ζ ^ 8 + ((43 / 492) : ℂ) * ζ ^ 12 + ((53 / 82) : ℂ) * ζ ^ 18 + ((61 / 41) : ℂ) * ζ ^ 22 - ((64 / 41) : ℂ) * ζ ^ 24 - ((347 / 246) : ℂ) * ζ ^ 28 + ((63 / 164) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((7 / 123) : ℂ) - ((413 / 41) : ℂ) * ζ ^ 2 - ((856 / 123) : ℂ) * ζ ^ 6 + ((473 / 41) : ℂ) * ζ ^ 8 + ((694 / 123) : ℂ) * ζ ^ 12 + ((169 / 41) : ℂ) * ζ ^ 18 + ((413 / 41) : ℂ) * ζ ^ 22 - ((775 / 123) : ℂ) * ζ ^ 24 - ((473 / 41) : ℂ) * ζ ^ 28 + ((65 / 123) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((923 / 164) : ℂ) - ((133 / 123) : ℂ) * ζ ^ 2 + ((923 / 164) : ℂ) * ζ ^ 4 + ((659 / 492) : ℂ) * ζ ^ 6 + ((19 / 492) : ℂ) * ζ ^ 8 + ((1529 / 246) : ℂ) * ζ ^ 10 - ((41 / 12) : ℂ) * ζ ^ 12 - ((875 / 123) : ℂ) * ζ ^ 14 - ((644 / 123) : ℂ) * ζ ^ 16 + ((97 / 12) : ℂ) * ζ ^ 18 + ((1117 / 164) : ℂ) * ζ ^ 20 - ((65 / 123) : ℂ) * ζ ^ 22 - ((1419 / 164) : ℂ) * ζ ^ 24 + ((65 / 164) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((25 / 246) : ℂ) + ((61 / 41) : ℂ) * ζ ^ 2 - ((25 / 246) : ℂ) * ζ ^ 4 - ((797 / 492) : ℂ) * ζ ^ 6 - ((161 / 123) : ℂ) * ζ ^ 8 + ((797 / 492) : ℂ) * ζ ^ 10 + ((161 / 123) : ℂ) * ζ ^ 12 - ((326 / 123) : ℂ) * ζ ^ 14 - ((161 / 123) : ℂ) * ζ ^ 16 + ((65 / 492) : ℂ) * ζ ^ 18 + ((473 / 164) : ℂ) * ζ ^ 20 - ((65 / 492) : ℂ) * ζ ^ 22)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY23_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((85 / 246) : ℂ) + ((179 / 164) : ℂ) * ζ ^ 2 + ((347 / 164) : ℂ) * ζ ^ 6 - ((185 / 123) : ℂ) * ζ ^ 8 - ((559 / 492) : ℂ) * ζ ^ 12 - ((239 / 492) : ℂ) * ζ ^ 18 - ((179 / 164) : ℂ) * ζ ^ 22 + ((7 / 164) : ℂ) * ζ ^ 24 + ((185 / 123) : ℂ) * ζ ^ 28 + ((85 / 492) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((171 / 164) : ℂ) + ((319 / 164) : ℂ) * ζ ^ 2 + ((383 / 123) : ℂ) * ζ ^ 6 - ((335 / 492) : ℂ) * ζ ^ 8 - ((227 / 82) : ℂ) * ζ ^ 12 + ((127 / 492) : ℂ) * ζ ^ 18 - ((319 / 164) : ℂ) * ζ ^ 22 - ((439 / 492) : ℂ) * ζ ^ 24 + ((335 / 492) : ℂ) * ζ ^ 28 + ((393 / 164) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((25 / 246) : ℂ) - ((61 / 41) : ℂ) * ζ ^ 2 + ((65 / 492) : ℂ) * ζ ^ 6 + ((347 / 246) : ℂ) * ζ ^ 8 + ((43 / 492) : ℂ) * ζ ^ 12 + ((53 / 82) : ℂ) * ζ ^ 18 + ((61 / 41) : ℂ) * ζ ^ 22 - ((64 / 41) : ℂ) * ζ ^ 24 - ((347 / 246) : ℂ) * ζ ^ 28 + ((63 / 164) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((85 / 246) : ℂ) - ((179 / 164) : ℂ) * ζ ^ 2 - ((347 / 164) : ℂ) * ζ ^ 6 + ((185 / 123) : ℂ) * ζ ^ 8 + ((559 / 492) : ℂ) * ζ ^ 12 + ((239 / 492) : ℂ) * ζ ^ 18 + ((179 / 164) : ℂ) * ζ ^ 22 - ((7 / 164) : ℂ) * ζ ^ 24 - ((185 / 123) : ℂ) * ζ ^ 28 - ((85 / 492) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY23_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((243 / 41) : ℂ) - ((691 / 123) : ℂ) * ζ ^ 2 - ((1493 / 123) : ℂ) * ζ ^ 6 + ((202 / 123) : ℂ) * ζ ^ 8 + ((740 / 123) : ℂ) * ζ ^ 12 + ((154 / 123) : ℂ) * ζ ^ 18 + ((691 / 123) : ℂ) * ζ ^ 22 + ((236 / 41) : ℂ) * ζ ^ 24 - ((202 / 123) : ℂ) * ζ ^ 28 - ((347 / 41) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((85 / 246) : ℂ) - ((179 / 164) : ℂ) * ζ ^ 2 - ((85 / 246) : ℂ) * ζ ^ 4 - ((42 / 41) : ℂ) * ζ ^ 6 + ((455 / 246) : ℂ) * ζ ^ 8 + ((42 / 41) : ℂ) * ζ ^ 10 - ((455 / 246) : ℂ) * ζ ^ 12 - ((175 / 246) : ℂ) * ζ ^ 14 + ((455 / 246) : ℂ) * ζ ^ 16 + ((347 / 164) : ℂ) * ζ ^ 18 - ((101 / 246) : ℂ) * ζ ^ 20 - ((347 / 164) : ℂ) * ζ ^ 22)) * Y 0 0
        + ((((1001 / 123) : ℂ) - ((785 / 164) : ℂ) * ζ ^ 2 - ((1001 / 123) : ℂ) * ζ ^ 4 - ((551 / 164) : ℂ) * ζ ^ 6 + ((503 / 246) : ℂ) * ζ ^ 8 + ((621 / 82) : ℂ) * ζ ^ 10 + ((986 / 123) : ℂ) * ζ ^ 12 - ((911 / 492) : ℂ) * ζ ^ 14 - ((2275 / 246) : ℂ) * ζ ^ 16 - ((261 / 41) : ℂ) * ζ ^ 18 + ((1567 / 246) : ℂ) * ζ ^ 20 + ((1735 / 164) : ℂ) * ζ ^ 22 - ((101 / 82) : ℂ) * ζ ^ 24 - ((1041 / 164) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((85 / 246) : ℂ) + ((179 / 164) : ℂ) * ζ ^ 2 + ((85 / 246) : ℂ) * ζ ^ 4 + ((42 / 41) : ℂ) * ζ ^ 6 - ((455 / 246) : ℂ) * ζ ^ 8 - ((42 / 41) : ℂ) * ζ ^ 10 + ((455 / 246) : ℂ) * ζ ^ 12 + ((175 / 246) : ℂ) * ζ ^ 14 - ((455 / 246) : ℂ) * ζ ^ 16 - ((347 / 164) : ℂ) * ζ ^ 18 + ((101 / 246) : ℂ) * ζ ^ 20 + ((347 / 164) : ℂ) * ζ ^ 22)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY23_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((17 / 82) : ℂ) + ((337 / 164) : ℂ) * ζ ^ 2 + ((323 / 164) : ℂ) * ζ ^ 6 - ((78 / 41) : ℂ) * ζ ^ 8 - ((243 / 164) : ℂ) * ζ ^ 12 - ((97 / 164) : ℂ) * ζ ^ 18 - ((337 / 164) : ℂ) * ζ ^ 22 + ((119 / 164) : ℂ) * ζ ^ 24 + ((78 / 41) : ℂ) * ζ ^ 28 + ((99 / 164) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((327 / 164) : ℂ) + ((95 / 164) : ℂ) * ζ ^ 2 + ((231 / 82) : ℂ) * ζ ^ 6 + ((55 / 164) : ℂ) * ζ ^ 8 - ((57 / 41) : ℂ) * ζ ^ 12 + ((115 / 164) : ℂ) * ζ ^ 18 - ((95 / 164) : ℂ) * ζ ^ 22 - ((311 / 164) : ℂ) * ζ ^ 24 - ((55 / 164) : ℂ) * ζ ^ 28 + ((307 / 164) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((25 / 246) : ℂ) - ((61 / 41) : ℂ) * ζ ^ 2 + ((65 / 492) : ℂ) * ζ ^ 6 + ((347 / 246) : ℂ) * ζ ^ 8 + ((43 / 492) : ℂ) * ζ ^ 12 + ((53 / 82) : ℂ) * ζ ^ 18 + ((61 / 41) : ℂ) * ζ ^ 22 - ((64 / 41) : ℂ) * ζ ^ 24 - ((347 / 246) : ℂ) * ζ ^ 28 + ((63 / 164) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((85 / 246) : ℂ) - ((179 / 164) : ℂ) * ζ ^ 2 - ((347 / 164) : ℂ) * ζ ^ 6 + ((185 / 123) : ℂ) * ζ ^ 8 + ((559 / 492) : ℂ) * ζ ^ 12 + ((239 / 492) : ℂ) * ζ ^ 18 + ((179 / 164) : ℂ) * ζ ^ 22 - ((7 / 164) : ℂ) * ζ ^ 24 - ((185 / 123) : ℂ) * ζ ^ 28 - ((85 / 492) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((17 / 123) : ℂ) - ((79 / 82) : ℂ) * ζ ^ 2 + ((6 / 41) : ℂ) * ζ ^ 6 + ((49 / 123) : ℂ) * ζ ^ 8 + ((85 / 246) : ℂ) * ζ ^ 12 + ((13 / 123) : ℂ) * ζ ^ 18 + ((79 / 82) : ℂ) * ζ ^ 22 - ((28 / 41) : ℂ) * ζ ^ 24 - ((49 / 123) : ℂ) * ζ ^ 28 - ((53 / 123) : ℂ) * ζ ^ 30)) * Y 3 3) = 0 := by
  have previous :=
    row17_reducedY23_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation03
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((2 / 3) : ℂ) + (2 : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 - ((8 / 3) : ℂ) * ζ ^ 12 - ((4 / 3) : ℂ) * ζ ^ 18 - (2 : ℂ) * ζ ^ 22 + ((10 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28)) * equation
      - (
        ((-((7 / 82) : ℂ) - ((39 / 41) : ℂ) * ζ ^ 2 - ((29 / 82) : ℂ) * ζ ^ 4 + ((131 / 123) : ℂ) * ζ ^ 6 + ((25 / 123) : ℂ) * ζ ^ 8 - ((295 / 246) : ℂ) * ζ ^ 10 - ((71 / 246) : ℂ) * ζ ^ 12 + ((167 / 246) : ℂ) * ζ ^ 14 - ((7 / 123) : ℂ) * ζ ^ 16 - ((89 / 246) : ℂ) * ζ ^ 18 + ((11 / 41) : ℂ) * ζ ^ 20 + ((28 / 123) : ℂ) * ζ ^ 22 + ((23 / 246) : ℂ) * ζ ^ 24 + ((7 / 123) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((100 / 123) : ℂ) + ((81 / 82) : ℂ) * ζ ^ 2 - ((173 / 246) : ℂ) * ζ ^ 4 - ((209 / 246) : ℂ) * ζ ^ 6 - ((11 / 82) : ℂ) * ζ ^ 8 + ((124 / 123) : ℂ) * ζ ^ 10 - ((13 / 246) : ℂ) * ζ ^ 12 - ((67 / 123) : ℂ) * ζ ^ 14 + ((4 / 41) : ℂ) * ζ ^ 16 + ((45 / 82) : ℂ) * ζ ^ 18 + ((2 / 123) : ℂ) * ζ ^ 20 - ((16 / 41) : ℂ) * ζ ^ 22 - ((8 / 123) : ℂ) * ζ ^ 24 - ((4 / 41) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((44 / 123) : ℂ) - ((61 / 246) : ℂ) * ζ ^ 2 + ((11 / 123) : ℂ) * ζ ^ 4 + ((151 / 246) : ℂ) * ζ ^ 6 - ((23 / 41) : ℂ) * ζ ^ 8 - ((73 / 82) : ℂ) * ζ ^ 10 + ((22 / 41) : ℂ) * ζ ^ 12 + ((53 / 82) : ℂ) * ζ ^ 14 - ((28 / 41) : ℂ) * ζ ^ 16 - ((14 / 41) : ℂ) * ζ ^ 18 + ((95 / 246) : ℂ) * ζ ^ 20 + ((8 / 123) : ℂ) * ζ ^ 22 + ((5 / 41) : ℂ) * ζ ^ 24 + ((2 / 123) : ℂ) * ζ ^ 26)) * Y 2 3
        + ((((7 / 82) : ℂ) + ((39 / 41) : ℂ) * ζ ^ 2 + ((29 / 82) : ℂ) * ζ ^ 4 - ((131 / 123) : ℂ) * ζ ^ 6 - ((25 / 123) : ℂ) * ζ ^ 8 + ((295 / 246) : ℂ) * ζ ^ 10 + ((71 / 246) : ℂ) * ζ ^ 12 - ((167 / 246) : ℂ) * ζ ^ 14 + ((7 / 123) : ℂ) * ζ ^ 16 + ((89 / 246) : ℂ) * ζ ^ 18 - ((11 / 41) : ℂ) * ζ ^ 20 - ((28 / 123) : ℂ) * ζ ^ 22 - ((23 / 246) : ℂ) * ζ ^ 24 - ((7 / 123) : ℂ) * ζ ^ 26)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY23_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((25 / 246) : ℂ) - ((61 / 41) : ℂ) * ζ ^ 2 + ((65 / 492) : ℂ) * ζ ^ 6 + ((347 / 246) : ℂ) * ζ ^ 8 + ((43 / 492) : ℂ) * ζ ^ 12 + ((53 / 82) : ℂ) * ζ ^ 18 + ((61 / 41) : ℂ) * ζ ^ 22 - ((64 / 41) : ℂ) * ζ ^ 24 - ((347 / 246) : ℂ) * ζ ^ 28 + ((63 / 164) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((85 / 246) : ℂ) - ((179 / 164) : ℂ) * ζ ^ 2 - ((347 / 164) : ℂ) * ζ ^ 6 + ((185 / 123) : ℂ) * ζ ^ 8 + ((559 / 492) : ℂ) * ζ ^ 12 + ((239 / 492) : ℂ) * ζ ^ 18 + ((179 / 164) : ℂ) * ζ ^ 22 - ((7 / 164) : ℂ) * ζ ^ 24 - ((185 / 123) : ℂ) * ζ ^ 28 - ((85 / 492) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((17 / 123) : ℂ) - ((79 / 82) : ℂ) * ζ ^ 2 + ((6 / 41) : ℂ) * ζ ^ 6 + ((49 / 123) : ℂ) * ζ ^ 8 + ((85 / 246) : ℂ) * ζ ^ 12 + ((13 / 123) : ℂ) * ζ ^ 18 + ((79 / 82) : ℂ) * ζ ^ 22 - ((28 / 41) : ℂ) * ζ ^ 24 - ((49 / 123) : ℂ) * ζ ^ 28 - ((53 / 123) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((-((17 / 82) : ℂ) + ((337 / 164) : ℂ) * ζ ^ 2 + ((323 / 164) : ℂ) * ζ ^ 6 - ((78 / 41) : ℂ) * ζ ^ 8 - ((243 / 164) : ℂ) * ζ ^ 12 - ((97 / 164) : ℂ) * ζ ^ 18 - ((337 / 164) : ℂ) * ζ ^ 22 + ((119 / 164) : ℂ) * ζ ^ 24 + ((78 / 41) : ℂ) * ζ ^ 28 + ((99 / 164) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((479 / 451) : ℂ) + ((635 / 1804) : ℂ) * ζ ^ 2 + ((2171 / 1804) : ℂ) * ζ ^ 6 + ((100 / 451) : ℂ) * ζ ^ 8 - ((745 / 1804) : ℂ) * ζ ^ 12 + ((691 / 1804) : ℂ) * ζ ^ 18 - ((635 / 1804) : ℂ) * ζ ^ 22 - ((2109 / 1804) : ℂ) * ζ ^ 24 - ((100 / 451) : ℂ) * ζ ^ 28 + ((1983 / 1804) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY23_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((785 / 1353) : ℂ) + ((805 / 451) : ℂ) * ζ ^ 2 + ((1829 / 1353) : ℂ) * ζ ^ 6 - ((956 / 451) : ℂ) * ζ ^ 8 - ((1942 / 1353) : ℂ) * ζ ^ 12 - ((1360 / 1353) : ℂ) * ζ ^ 18 - ((805 / 451) : ℂ) * ζ ^ 22 + ((2480 / 1353) : ℂ) * ζ ^ 24 + ((956 / 451) : ℂ) * ζ ^ 28 - ((413 / 1353) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((5197 / 9922) : ℂ) + ((21457 / 19844) : ℂ) * ζ ^ 2 + ((5197 / 9922) : ℂ) * ζ ^ 4 + ((1497 / 9922) : ℂ) * ζ ^ 6 - ((5908 / 4961) : ℂ) * ζ ^ 8 + ((459 / 4961) : ℂ) * ζ ^ 10 - ((1531 / 4961) : ℂ) * ζ ^ 12 + ((3187 / 9922) : ℂ) * ζ ^ 14 + ((97 / 4961) : ℂ) * ζ ^ 16 + ((4417 / 19844) : ℂ) * ζ ^ 18 - ((1957 / 4961) : ℂ) * ζ ^ 20 + ((413 / 19844) : ℂ) * ζ ^ 22 - ((1434 / 4961) : ℂ) * ζ ^ 24 + ((413 / 9922) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((14013 / 4961) : ℂ) - ((9805 / 4961) : ℂ) * ζ ^ 2 + ((14013 / 4961) : ℂ) * ζ ^ 4 + ((56713 / 19844) : ℂ) * ζ ^ 6 + ((12873 / 9922) : ℂ) * ζ ^ 8 - ((2707 / 4961) : ℂ) * ζ ^ 10 - ((14011 / 4961) : ℂ) * ζ ^ 12 + ((44999 / 19844) : ℂ) * ζ ^ 14 + ((388 / 4961) : ℂ) * ζ ^ 16 + ((44233 / 19844) : ℂ) * ζ ^ 18 - ((14648 / 4961) : ℂ) * ζ ^ 20 + ((413 / 4961) : ℂ) * ζ ^ 22 - ((13623 / 4961) : ℂ) * ζ ^ 24 + ((7847 / 19844) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((5197 / 9922) : ℂ) - ((21457 / 19844) : ℂ) * ζ ^ 2 - ((5197 / 9922) : ℂ) * ζ ^ 4 - ((1497 / 9922) : ℂ) * ζ ^ 6 + ((5908 / 4961) : ℂ) * ζ ^ 8 - ((459 / 4961) : ℂ) * ζ ^ 10 + ((1531 / 4961) : ℂ) * ζ ^ 12 - ((3187 / 9922) : ℂ) * ζ ^ 14 - ((97 / 4961) : ℂ) * ζ ^ 16 - ((4417 / 19844) : ℂ) * ζ ^ 18 + ((1957 / 4961) : ℂ) * ζ ^ 20 - ((413 / 19844) : ℂ) * ζ ^ 22 + ((1434 / 4961) : ℂ) * ζ ^ 24 - ((413 / 9922) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((11323 / 9922) : ℂ) - ((2155 / 19844) : ℂ) * ζ ^ 2 - ((11323 / 9922) : ℂ) * ζ ^ 4 - ((4517 / 4961) : ℂ) * ζ ^ 6 + ((1950 / 4961) : ℂ) * ζ ^ 8 + ((1789 / 9922) : ℂ) * ζ ^ 10 + ((4593 / 4961) : ℂ) * ζ ^ 12 - ((9561 / 9922) : ℂ) * ζ ^ 14 - ((291 / 4961) : ℂ) * ζ ^ 16 - ((13251 / 19844) : ℂ) * ζ ^ 18 + ((5871 / 4961) : ℂ) * ζ ^ 20 - ((1239 / 19844) : ℂ) * ζ ^ 22 + ((4302 / 4961) : ℂ) * ζ ^ 24 - ((1239 / 9922) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY23_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((45 / 82) : ℂ) - ((93 / 82) : ℂ) * ζ ^ 2 - ((47 / 164) : ℂ) * ζ ^ 6 + ((54 / 41) : ℂ) * ζ ^ 8 + ((61 / 164) : ℂ) * ζ ^ 12 + ((73 / 82) : ℂ) * ζ ^ 18 + ((93 / 82) : ℂ) * ζ ^ 22 - ((109 / 82) : ℂ) * ζ ^ 24 - ((54 / 41) : ℂ) * ζ ^ 28 + ((45 / 164) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((17 / 82) : ℂ) - ((337 / 164) : ℂ) * ζ ^ 2 - ((323 / 164) : ℂ) * ζ ^ 6 + ((78 / 41) : ℂ) * ζ ^ 8 + ((243 / 164) : ℂ) * ζ ^ 12 + ((97 / 164) : ℂ) * ζ ^ 18 + ((337 / 164) : ℂ) * ζ ^ 22 - ((119 / 164) : ℂ) * ζ ^ 24 - ((78 / 41) : ℂ) * ζ ^ 28 - ((99 / 164) : ℂ) * ζ ^ 30)) * Y 1 1
      + (((1 : ℂ))) * Y 2 3
      + ((-((17 / 82) : ℂ) + ((337 / 164) : ℂ) * ζ ^ 2 + ((323 / 164) : ℂ) * ζ ^ 6 - ((78 / 41) : ℂ) * ζ ^ 8 - ((243 / 164) : ℂ) * ζ ^ 12 - ((97 / 164) : ℂ) * ζ ^ 18 - ((337 / 164) : ℂ) * ζ ^ 22 + ((119 / 164) : ℂ) * ζ ^ 24 + ((78 / 41) : ℂ) * ζ ^ 28 + ((99 / 164) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((479 / 451) : ℂ) + ((635 / 1804) : ℂ) * ζ ^ 2 + ((2171 / 1804) : ℂ) * ζ ^ 6 + ((100 / 451) : ℂ) * ζ ^ 8 - ((745 / 1804) : ℂ) * ζ ^ 12 + ((691 / 1804) : ℂ) * ζ ^ 18 - ((635 / 1804) : ℂ) * ζ ^ 22 - ((2109 / 1804) : ℂ) * ζ ^ 24 - ((100 / 451) : ℂ) * ζ ^ 28 + ((1983 / 1804) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY23_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation13
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((4 / 3) : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 18 - ((4 / 3) : ℂ) * ζ ^ 22 + (2 : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((55 / 123) : ℂ) - ((61 / 246) : ℂ) * ζ ^ 2 - ((91 / 123) : ℂ) * ζ ^ 4 + ((151 / 246) : ℂ) * ζ ^ 6 + ((199 / 246) : ℂ) * ζ ^ 8 - ((197 / 246) : ℂ) * ζ ^ 10 - ((151 / 246) : ℂ) * ζ ^ 12 + ((57 / 82) : ℂ) * ζ ^ 14 + ((79 / 246) : ℂ) * ζ ^ 16 - ((95 / 246) : ℂ) * ζ ^ 18 - ((3 / 82) : ℂ) * ζ ^ 20 + ((49 / 246) : ℂ) * ζ ^ 22 + ((7 / 123) : ℂ) * ζ ^ 24 - ((23 / 246) : ℂ) * ζ ^ 26 - ((7 / 123) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((17 / 123) : ℂ) + ((169 / 246) : ℂ) * ζ ^ 2 - ((8 / 123) : ℂ) * ζ ^ 4 - ((57 / 82) : ℂ) * ζ ^ 6 - ((101 / 246) : ℂ) * ζ ^ 8 + ((203 / 246) : ℂ) * ζ ^ 10 + ((89 / 246) : ℂ) * ζ ^ 12 - ((45 / 82) : ℂ) * ζ ^ 14 - ((71 / 246) : ℂ) * ζ ^ 16 + ((58 / 123) : ℂ) * ζ ^ 18 + ((11 / 82) : ℂ) * ζ ^ 20 - ((14 / 41) : ℂ) * ζ ^ 22 - ((4 / 41) : ℂ) * ζ ^ 24 + ((8 / 123) : ℂ) * ζ ^ 26 + ((4 / 41) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((83 / 123) : ℂ) + ((19 / 246) : ℂ) * ζ ^ 2 + ((191 / 123) : ℂ) * ζ ^ 4 - ((125 / 246) : ℂ) * ζ ^ 6 - ((155 / 123) : ℂ) * ζ ^ 8 + ((115 / 82) : ℂ) * ζ ^ 10 + ((1 / 123) : ℂ) * ζ ^ 12 - ((65 / 41) : ℂ) * ζ ^ 14 + ((107 / 123) : ℂ) * ζ ^ 16 + ((27 / 41) : ℂ) * ζ ^ 18 - ((57 / 41) : ℂ) * ζ ^ 20 + ((29 / 123) : ℂ) * ζ ^ 22 + ((20 / 123) : ℂ) * ζ ^ 24 + ((55 / 123) : ℂ) * ζ ^ 26 - ((20 / 123) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((17 / 123) : ℂ) - ((169 / 246) : ℂ) * ζ ^ 2 + ((8 / 123) : ℂ) * ζ ^ 4 + ((57 / 82) : ℂ) * ζ ^ 6 + ((101 / 246) : ℂ) * ζ ^ 8 - ((203 / 246) : ℂ) * ζ ^ 10 - ((89 / 246) : ℂ) * ζ ^ 12 + ((45 / 82) : ℂ) * ζ ^ 14 + ((71 / 246) : ℂ) * ζ ^ 16 - ((58 / 123) : ℂ) * ζ ^ 18 - ((11 / 82) : ℂ) * ζ ^ 20 + ((14 / 41) : ℂ) * ζ ^ 22 + ((4 / 41) : ℂ) * ζ ^ 24 - ((8 / 123) : ℂ) * ζ ^ 26 - ((4 / 41) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY23_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 2 3) = 0 := by
  have previous :=
    row17_reducedY23_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((1231 / 1353) : ℂ) - ((587 / 1353) : ℂ) * ζ ^ 2 + ((256 / 451) : ℂ) * ζ ^ 6 + ((1175 / 1353) : ℂ) * ζ ^ 8 - ((6 / 451) : ℂ) * ζ ^ 12 + ((235 / 451) : ℂ) * ζ ^ 18 + ((587 / 1353) : ℂ) * ζ ^ 22 - ((1657 / 1353) : ℂ) * ζ ^ 24 - ((1175 / 1353) : ℂ) * ζ ^ 28 + ((335 / 451) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((521 / 9922) : ℂ) - ((8905 / 9922) : ℂ) * ζ ^ 2 + ((521 / 9922) : ℂ) * ζ ^ 4 + ((5979 / 19844) : ℂ) * ζ ^ 6 + ((3308 / 4961) : ℂ) * ζ ^ 8 - ((7153 / 19844) : ℂ) * ζ ^ 10 + ((467 / 4961) : ℂ) * ζ ^ 12 - ((1253 / 4961) : ℂ) * ζ ^ 14 + ((241 / 9922) : ℂ) * ζ ^ 16 - ((169 / 19844) : ℂ) * ζ ^ 18 + ((4489 / 19844) : ℂ) * ζ ^ 20 - ((1005 / 19844) : ℂ) * ζ ^ 22 + ((1175 / 9922) : ℂ) * ζ ^ 24 - ((1005 / 9922) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((29965 / 19844) : ℂ) - ((14225 / 9922) : ℂ) * ζ ^ 2 - ((29965 / 19844) : ℂ) * ζ ^ 4 - ((26761 / 19844) : ℂ) * ζ ^ 6 + ((19653 / 19844) : ℂ) * ζ ^ 8 + ((3902 / 4961) : ℂ) * ζ ^ 10 + ((20397 / 19844) : ℂ) * ζ ^ 12 - ((19429 / 9922) : ℂ) * ζ ^ 14 + ((482 / 4961) : ℂ) * ζ ^ 16 - ((7133 / 19844) : ℂ) * ζ ^ 18 + ((36183 / 19844) : ℂ) * ζ ^ 20 - ((1005 / 4961) : ℂ) * ζ ^ 22 + ((22325 / 19844) : ℂ) * ζ ^ 24 - ((19095 / 19844) : ℂ) * ζ ^ 26)) * Y 1 1
        + ((-((29965 / 19844) : ℂ) + ((14225 / 9922) : ℂ) * ζ ^ 2 + ((29965 / 19844) : ℂ) * ζ ^ 4 + ((26761 / 19844) : ℂ) * ζ ^ 6 - ((19653 / 19844) : ℂ) * ζ ^ 8 - ((3902 / 4961) : ℂ) * ζ ^ 10 - ((20397 / 19844) : ℂ) * ζ ^ 12 + ((19429 / 9922) : ℂ) * ζ ^ 14 - ((482 / 4961) : ℂ) * ζ ^ 16 + ((7133 / 19844) : ℂ) * ζ ^ 18 - ((36183 / 19844) : ℂ) * ζ ^ 20 + ((1005 / 4961) : ℂ) * ζ ^ 22 - ((22325 / 19844) : ℂ) * ζ ^ 24 + ((19095 / 19844) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((17383 / 19844) : ℂ) + ((4373 / 9922) : ℂ) * ζ ^ 2 + ((17383 / 19844) : ℂ) * ζ ^ 4 + ((12831 / 19844) : ℂ) * ζ ^ 6 - ((505 / 19844) : ℂ) * ζ ^ 8 - ((1300 / 4961) : ℂ) * ζ ^ 10 - ((20095 / 19844) : ℂ) * ζ ^ 12 + ((3155 / 9922) : ℂ) * ζ ^ 14 + ((1205 / 4961) : ℂ) * ζ ^ 16 + ((17681 / 19844) : ℂ) * ζ ^ 18 - ((9791 / 19844) : ℂ) * ζ ^ 20 - ((5025 / 9922) : ℂ) * ζ ^ 22 - ((15275 / 19844) : ℂ) * ζ ^ 24 + ((13065 / 19844) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY23
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 2 3 = 0 := by
  have reduced :=
    row17_reducedY23_combinationStep05 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row17_reducedY32_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((301 / 246) : ℂ) + ((2137 / 492) : ℂ) * ζ ^ 2 + ((128 / 123) : ℂ) * ζ ^ 6 + ((517 / 123) : ℂ) * ζ ^ 8 - ((47 / 246) : ℂ) * ζ ^ 12 - ((313 / 123) : ℂ) * ζ ^ 18 - ((2137 / 492) : ℂ) * ζ ^ 22 - ((391 / 164) : ℂ) * ζ ^ 24 - ((517 / 123) : ℂ) * ζ ^ 28 + ((188 / 123) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((4 / 123) : ℂ) - ((83 / 164) : ℂ) * ζ ^ 2 - ((545 / 492) : ℂ) * ζ ^ 6 - ((143 / 164) : ℂ) * ζ ^ 8 - ((575 / 492) : ℂ) * ζ ^ 12 + ((23 / 246) : ℂ) * ζ ^ 18 + ((83 / 164) : ℂ) * ζ ^ 22 + ((425 / 492) : ℂ) * ζ ^ 24 + ((143 / 164) : ℂ) * ζ ^ 28 + ((49 / 492) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((197 / 41) : ℂ) - ((344 / 123) : ℂ) * ζ ^ 2 - ((281 / 41) : ℂ) * ζ ^ 6 - ((93 / 41) : ℂ) * ζ ^ 8 - ((143 / 41) : ℂ) * ζ ^ 12 + ((95 / 123) : ℂ) * ζ ^ 18 + ((344 / 123) : ℂ) * ζ ^ 22 - ((166 / 123) : ℂ) * ζ ^ 24 + ((93 / 41) : ℂ) * ζ ^ 28 - ((545 / 123) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((11 / 492) : ℂ) - ((827 / 164) : ℂ) * ζ ^ 2 - ((11 / 492) : ℂ) * ζ ^ 4 + ((563 / 246) : ℂ) * ζ ^ 6 - ((563 / 492) : ℂ) * ζ ^ 8 - ((47 / 246) : ℂ) * ζ ^ 10 - ((23 / 12) : ℂ) * ζ ^ 12 - ((91 / 82) : ℂ) * ζ ^ 14 + ((445 / 123) : ℂ) * ζ ^ 16 - ((7 / 3) : ℂ) * ζ ^ 18 - ((269 / 82) : ℂ) * ζ ^ 20 + ((545 / 123) : ℂ) * ζ ^ 22 + ((279 / 164) : ℂ) * ζ ^ 24 - ((545 / 164) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((4 / 123) : ℂ) + ((83 / 164) : ℂ) * ζ ^ 2 - ((4 / 123) : ℂ) * ζ ^ 4 + ((74 / 123) : ℂ) * ζ ^ 6 + ((445 / 492) : ℂ) * ζ ^ 8 - ((74 / 123) : ℂ) * ζ ^ 10 - ((445 / 492) : ℂ) * ζ ^ 12 + ((67 / 164) : ℂ) * ζ ^ 14 + ((445 / 492) : ℂ) * ζ ^ 16 - ((545 / 492) : ℂ) * ζ ^ 18 - ((93 / 164) : ℂ) * ζ ^ 20 + ((545 / 492) : ℂ) * ζ ^ 22)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY32_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((103 / 82) : ℂ) + ((95 / 164) : ℂ) * ζ ^ 2 + ((121 / 123) : ℂ) * ζ ^ 6 - ((10 / 123) : ℂ) * ζ ^ 8 - ((55 / 246) : ℂ) * ζ ^ 12 - ((47 / 123) : ℂ) * ζ ^ 18 - ((95 / 164) : ℂ) * ζ ^ 22 + ((181 / 164) : ℂ) * ζ ^ 24 + ((10 / 123) : ℂ) * ζ ^ 28 + ((179 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((((229 / 164) : ℂ) - ((53 / 123) : ℂ) * ζ ^ 2 + ((505 / 492) : ℂ) * ζ ^ 6 - ((427 / 492) : ℂ) * ζ ^ 8 + ((271 / 492) : ℂ) * ζ ^ 12 + ((259 / 164) : ℂ) * ζ ^ 18 + ((53 / 123) : ℂ) * ζ ^ 22 + ((571 / 246) : ℂ) * ζ ^ 24 + ((427 / 492) : ℂ) * ζ ^ 28 + ((193 / 164) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((4 / 123) : ℂ) - ((83 / 164) : ℂ) * ζ ^ 2 - ((545 / 492) : ℂ) * ζ ^ 6 - ((143 / 164) : ℂ) * ζ ^ 8 - ((575 / 492) : ℂ) * ζ ^ 12 + ((23 / 246) : ℂ) * ζ ^ 18 + ((83 / 164) : ℂ) * ζ ^ 22 + ((425 / 492) : ℂ) * ζ ^ 24 + ((143 / 164) : ℂ) * ζ ^ 28 + ((49 / 492) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((103 / 82) : ℂ) - ((95 / 164) : ℂ) * ζ ^ 2 - ((121 / 123) : ℂ) * ζ ^ 6 + ((10 / 123) : ℂ) * ζ ^ 8 + ((55 / 246) : ℂ) * ζ ^ 12 + ((47 / 123) : ℂ) * ζ ^ 18 + ((95 / 164) : ℂ) * ζ ^ 22 - ((181 / 164) : ℂ) * ζ ^ 24 - ((10 / 123) : ℂ) * ζ ^ 28 - ((179 / 123) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY32_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((508 / 123) : ℂ) + ((81 / 41) : ℂ) * ζ ^ 2 - ((53 / 123) : ℂ) * ζ ^ 6 + ((473 / 123) : ℂ) * ζ ^ 8 + ((40 / 123) : ℂ) * ζ ^ 12 - ((176 / 41) : ℂ) * ζ ^ 18 - ((81 / 41) : ℂ) * ζ ^ 22 - ((1051 / 123) : ℂ) * ζ ^ 24 - ((473 / 123) : ℂ) * ζ ^ 28 - ((484 / 123) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((103 / 82) : ℂ) - ((95 / 164) : ℂ) * ζ ^ 2 + ((103 / 82) : ℂ) * ζ ^ 4 - ((199 / 492) : ℂ) * ζ ^ 6 - ((289 / 246) : ℂ) * ζ ^ 8 + ((199 / 492) : ℂ) * ζ ^ 10 + ((289 / 246) : ℂ) * ζ ^ 12 - ((727 / 492) : ℂ) * ζ ^ 14 - ((289 / 246) : ℂ) * ζ ^ 16 + ((121 / 123) : ℂ) * ζ ^ 18 - ((473 / 492) : ℂ) * ζ ^ 20 - ((121 / 123) : ℂ) * ζ ^ 22)) * Y 0 0
        + ((-((599 / 164) : ℂ) + ((216 / 41) : ℂ) * ζ ^ 2 + ((599 / 164) : ℂ) * ζ ^ 4 - ((1319 / 246) : ℂ) * ζ ^ 6 + ((2695 / 492) : ℂ) * ζ ^ 8 + ((1909 / 492) : ℂ) * ζ ^ 10 - ((4309 / 492) : ℂ) * ζ ^ 12 + ((599 / 492) : ℂ) * ζ ^ 14 + ((1445 / 246) : ℂ) * ζ ^ 16 - ((3149 / 492) : ℂ) * ζ ^ 18 - ((197 / 123) : ℂ) * ζ ^ 20 + ((605 / 123) : ℂ) * ζ ^ 22 - ((473 / 164) : ℂ) * ζ ^ 24 - ((121 / 41) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((103 / 82) : ℂ) + ((95 / 164) : ℂ) * ζ ^ 2 - ((103 / 82) : ℂ) * ζ ^ 4 + ((199 / 492) : ℂ) * ζ ^ 6 + ((289 / 246) : ℂ) * ζ ^ 8 - ((199 / 492) : ℂ) * ζ ^ 10 - ((289 / 246) : ℂ) * ζ ^ 12 + ((727 / 492) : ℂ) * ζ ^ 14 + ((289 / 246) : ℂ) * ζ ^ 16 - ((121 / 123) : ℂ) * ζ ^ 18 + ((473 / 492) : ℂ) * ζ ^ 20 + ((121 / 123) : ℂ) * ζ ^ 22)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY32_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((111 / 82) : ℂ) + ((57 / 164) : ℂ) * ζ ^ 2 + ((57 / 41) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 + ((15 / 41) : ℂ) * ζ ^ 12 + ((7 / 41) : ℂ) * ζ ^ 18 - ((57 / 164) : ℂ) * ζ ^ 22 + ((125 / 164) : ℂ) * ζ ^ 24 + ((2 / 41) : ℂ) * ζ ^ 28 + ((44 / 41) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((((225 / 164) : ℂ) - ((58 / 41) : ℂ) * ζ ^ 2 - ((67 / 164) : ℂ) * ζ ^ 6 - ((253 / 164) : ℂ) * ζ ^ 8 - ((173 / 164) : ℂ) * ζ ^ 12 + ((209 / 164) : ℂ) * ζ ^ 18 + ((58 / 41) : ℂ) * ζ ^ 22 + ((126 / 41) : ℂ) * ζ ^ 24 + ((253 / 164) : ℂ) * ζ ^ 28 + ((195 / 164) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((4 / 123) : ℂ) - ((83 / 164) : ℂ) * ζ ^ 2 - ((545 / 492) : ℂ) * ζ ^ 6 - ((143 / 164) : ℂ) * ζ ^ 8 - ((575 / 492) : ℂ) * ζ ^ 12 + ((23 / 246) : ℂ) * ζ ^ 18 + ((83 / 164) : ℂ) * ζ ^ 22 + ((425 / 492) : ℂ) * ζ ^ 24 + ((143 / 164) : ℂ) * ζ ^ 28 + ((49 / 492) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((103 / 82) : ℂ) - ((95 / 164) : ℂ) * ζ ^ 2 - ((121 / 123) : ℂ) * ζ ^ 6 + ((10 / 123) : ℂ) * ζ ^ 8 + ((55 / 246) : ℂ) * ζ ^ 12 + ((47 / 123) : ℂ) * ζ ^ 18 + ((95 / 164) : ℂ) * ζ ^ 22 - ((181 / 164) : ℂ) * ζ ^ 24 - ((10 / 123) : ℂ) * ζ ^ 28 - ((179 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 - ((4 / 123) : ℂ) * ζ ^ 8 - ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 + ((14 / 41) : ℂ) * ζ ^ 24 + ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have previous :=
    row17_reducedY32_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation02
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((2 / 3) : ℂ) + (2 : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 + ((2 / 3) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28 + ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((8 / 123) : ℂ) + ((103 / 246) : ℂ) * ζ ^ 2 + ((1 / 3) : ℂ) * ζ ^ 4 - ((63 / 82) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 + ((301 / 246) : ℂ) * ζ ^ 10 - ((23 / 41) : ℂ) * ζ ^ 12 - ((143 / 246) : ℂ) * ζ ^ 14 + ((39 / 41) : ℂ) * ζ ^ 16 - ((26 / 123) : ℂ) * ζ ^ 18 - ((55 / 82) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 22 + ((23 / 123) : ℂ) * ζ ^ 24 - ((58 / 123) : ℂ) * ζ ^ 26 - ((8 / 123) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((2 / 123) : ℂ) + ((64 / 123) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 4 + ((80 / 123) : ℂ) * ζ ^ 6 + ((85 / 246) : ℂ) * ζ ^ 8 - ((299 / 123) : ℂ) * ζ ^ 10 + ((89 / 123) : ℂ) * ζ ^ 12 + ((269 / 123) : ℂ) * ζ ^ 14 - ((102 / 41) : ℂ) * ζ ^ 16 - ((55 / 123) : ℂ) * ζ ^ 18 + ((94 / 41) : ℂ) * ζ ^ 20 - ((4 / 3) : ℂ) * ζ ^ 22 + ((25 / 123) : ℂ) * ζ ^ 24 + ((80 / 41) : ℂ) * ζ ^ 26 - ((80 / 123) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((8 / 123) : ℂ) - ((103 / 246) : ℂ) * ζ ^ 2 - ((1 / 3) : ℂ) * ζ ^ 4 + ((63 / 82) : ℂ) * ζ ^ 6 + ((2 / 41) : ℂ) * ζ ^ 8 - ((301 / 246) : ℂ) * ζ ^ 10 + ((23 / 41) : ℂ) * ζ ^ 12 + ((143 / 246) : ℂ) * ζ ^ 14 - ((39 / 41) : ℂ) * ζ ^ 16 + ((26 / 123) : ℂ) * ζ ^ 18 + ((55 / 82) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 - ((23 / 123) : ℂ) * ζ ^ 24 + ((58 / 123) : ℂ) * ζ ^ 26 + ((8 / 123) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((179 / 246) : ℂ) + ((2 / 41) : ℂ) * ζ ^ 2 + ((7 / 6) : ℂ) * ζ ^ 4 - ((18 / 41) : ℂ) * ζ ^ 6 - ((62 / 123) : ℂ) * ζ ^ 8 + ((71 / 82) : ℂ) * ζ ^ 10 - ((73 / 246) : ℂ) * ζ ^ 12 - ((193 / 246) : ℂ) * ζ ^ 14 + ((34 / 41) : ℂ) * ζ ^ 16 + ((35 / 82) : ℂ) * ζ ^ 18 - ((94 / 123) : ℂ) * ζ ^ 20 + ((79 / 246) : ℂ) * ζ ^ 24 - ((13 / 41) : ℂ) * ζ ^ 26 - ((28 / 123) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY32_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((4 / 123) : ℂ) - ((83 / 164) : ℂ) * ζ ^ 2 - ((545 / 492) : ℂ) * ζ ^ 6 - ((143 / 164) : ℂ) * ζ ^ 8 - ((575 / 492) : ℂ) * ζ ^ 12 + ((23 / 246) : ℂ) * ζ ^ 18 + ((83 / 164) : ℂ) * ζ ^ 22 + ((425 / 492) : ℂ) * ζ ^ 24 + ((143 / 164) : ℂ) * ζ ^ 28 + ((49 / 492) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((103 / 82) : ℂ) - ((95 / 164) : ℂ) * ζ ^ 2 - ((121 / 123) : ℂ) * ζ ^ 6 + ((10 / 123) : ℂ) * ζ ^ 8 + ((55 / 246) : ℂ) * ζ ^ 12 + ((47 / 123) : ℂ) * ζ ^ 18 + ((95 / 164) : ℂ) * ζ ^ 22 - ((181 / 164) : ℂ) * ζ ^ 24 - ((10 / 123) : ℂ) * ζ ^ 28 - ((179 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 - ((4 / 123) : ℂ) * ζ ^ 8 - ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 + ((14 / 41) : ℂ) * ζ ^ 24 + ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((111 / 82) : ℂ) + ((57 / 164) : ℂ) * ζ ^ 2 + ((57 / 41) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 + ((15 / 41) : ℂ) * ζ ^ 12 + ((7 / 41) : ℂ) * ζ ^ 18 - ((57 / 164) : ℂ) * ζ ^ 22 + ((125 / 164) : ℂ) * ζ ^ 24 + ((2 / 41) : ℂ) * ζ ^ 28 + ((44 / 41) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((397 / 902) : ℂ) - ((1691 / 1804) : ℂ) * ζ ^ 2 - ((133 / 451) : ℂ) * ζ ^ 6 - ((419 / 451) : ℂ) * ζ ^ 8 - ((29 / 902) : ℂ) * ζ ^ 12 + ((380 / 451) : ℂ) * ζ ^ 18 + ((1691 / 1804) : ℂ) * ζ ^ 22 + ((1977 / 1804) : ℂ) * ζ ^ 24 + ((419 / 451) : ℂ) * ζ ^ 28 + ((191 / 902) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY32_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((1514 / 1353) : ℂ) + ((1765 / 1353) : ℂ) * ζ ^ 2 + ((2263 / 1353) : ℂ) * ζ ^ 6 + ((1229 / 1353) : ℂ) * ζ ^ 8 + ((28 / 1353) : ℂ) * ζ ^ 12 - ((796 / 1353) : ℂ) * ζ ^ 18 - ((1765 / 1353) : ℂ) * ζ ^ 22 + ((523 / 1353) : ℂ) * ζ ^ 24 - ((1229 / 1353) : ℂ) * ζ ^ 28 + ((1744 / 1353) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((7375 / 9922) : ℂ) - ((7223 / 19844) : ℂ) * ζ ^ 2 - ((7375 / 9922) : ℂ) * ζ ^ 4 + ((16707 / 19844) : ℂ) * ζ ^ 6 + ((3489 / 9922) : ℂ) * ζ ^ 8 - ((13177 / 19844) : ℂ) * ζ ^ 10 + ((2105 / 9922) : ℂ) * ζ ^ 12 - ((1875 / 19844) : ℂ) * ζ ^ 14 - ((438 / 4961) : ℂ) * ζ ^ 16 + ((2637 / 9922) : ℂ) * ζ ^ 18 + ((183 / 19844) : ℂ) * ζ ^ 20 - ((436 / 4961) : ℂ) * ζ ^ 22 + ((1229 / 9922) : ℂ) * ζ ^ 24 - ((872 / 4961) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((4569 / 19844) : ℂ) - ((65137 / 19844) : ℂ) * ζ ^ 2 + ((4569 / 19844) : ℂ) * ζ ^ 4 + ((9507 / 19844) : ℂ) * ζ ^ 6 - ((32225 / 19844) : ℂ) * ζ ^ 8 + ((6007 / 4961) : ℂ) * ζ ^ 10 + ((30359 / 19844) : ℂ) * ζ ^ 12 - ((4482 / 4961) : ℂ) * ζ ^ 14 - ((1752 / 4961) : ℂ) * ζ ^ 16 + ((40511 / 19844) : ℂ) * ζ ^ 18 - ((5021 / 19844) : ℂ) * ζ ^ 20 - ((1744 / 4961) : ℂ) * ζ ^ 22 + ((23351 / 19844) : ℂ) * ζ ^ 24 - ((8284 / 4961) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((7375 / 9922) : ℂ) + ((7223 / 19844) : ℂ) * ζ ^ 2 + ((7375 / 9922) : ℂ) * ζ ^ 4 - ((16707 / 19844) : ℂ) * ζ ^ 6 - ((3489 / 9922) : ℂ) * ζ ^ 8 + ((13177 / 19844) : ℂ) * ζ ^ 10 - ((2105 / 9922) : ℂ) * ζ ^ 12 + ((1875 / 19844) : ℂ) * ζ ^ 14 + ((438 / 4961) : ℂ) * ζ ^ 16 - ((2637 / 9922) : ℂ) * ζ ^ 18 - ((183 / 19844) : ℂ) * ζ ^ 20 + ((436 / 4961) : ℂ) * ζ ^ 22 - ((1229 / 9922) : ℂ) * ζ ^ 24 + ((872 / 4961) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((2853 / 9922) : ℂ) + ((22131 / 19844) : ℂ) * ζ ^ 2 + ((2853 / 9922) : ℂ) * ζ ^ 4 - ((11753 / 19844) : ℂ) * ζ ^ 6 + ((1526 / 4961) : ℂ) * ζ ^ 8 + ((1163 / 19844) : ℂ) * ζ ^ 10 - ((6315 / 9922) : ℂ) * ζ ^ 12 + ((5625 / 19844) : ℂ) * ζ ^ 14 + ((1314 / 4961) : ℂ) * ζ ^ 16 - ((7911 / 9922) : ℂ) * ζ ^ 18 - ((549 / 19844) : ℂ) * ζ ^ 20 + ((1308 / 4961) : ℂ) * ζ ^ 22 - ((3687 / 9922) : ℂ) * ζ ^ 24 + ((2616 / 4961) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY32_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((1 / 41) : ℂ) - ((153 / 164) : ℂ) * ζ ^ 2 - ((161 / 164) : ℂ) * ζ ^ 6 - ((149 / 164) : ℂ) * ζ ^ 8 - ((133 / 164) : ℂ) * ζ ^ 12 + ((25 / 82) : ℂ) * ζ ^ 18 + ((153 / 164) : ℂ) * ζ ^ 22 + ((109 / 164) : ℂ) * ζ ^ 24 + ((149 / 164) : ℂ) * ζ ^ 28 - ((43 / 164) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((111 / 82) : ℂ) - ((57 / 164) : ℂ) * ζ ^ 2 - ((57 / 41) : ℂ) * ζ ^ 6 + ((2 / 41) : ℂ) * ζ ^ 8 - ((15 / 41) : ℂ) * ζ ^ 12 - ((7 / 41) : ℂ) * ζ ^ 18 + ((57 / 164) : ℂ) * ζ ^ 22 - ((125 / 164) : ℂ) * ζ ^ 24 - ((2 / 41) : ℂ) * ζ ^ 28 - ((44 / 41) : ℂ) * ζ ^ 30)) * Y 1 1
      + (((1 : ℂ))) * Y 3 2
      + ((((111 / 82) : ℂ) + ((57 / 164) : ℂ) * ζ ^ 2 + ((57 / 41) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 + ((15 / 41) : ℂ) * ζ ^ 12 + ((7 / 41) : ℂ) * ζ ^ 18 - ((57 / 164) : ℂ) * ζ ^ 22 + ((125 / 164) : ℂ) * ζ ^ 24 + ((2 / 41) : ℂ) * ζ ^ 28 + ((44 / 41) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((397 / 902) : ℂ) - ((1691 / 1804) : ℂ) * ζ ^ 2 - ((133 / 451) : ℂ) * ζ ^ 6 - ((419 / 451) : ℂ) * ζ ^ 8 - ((29 / 902) : ℂ) * ζ ^ 12 + ((380 / 451) : ℂ) * ζ ^ 18 + ((1691 / 1804) : ℂ) * ζ ^ 22 + ((1977 / 1804) : ℂ) * ζ ^ 24 + ((419 / 451) : ℂ) * ζ ^ 28 + ((191 / 902) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY32_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation12
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((7 / 123) : ℂ) + ((35 / 82) : ℂ) * ζ ^ 2 + ((7 / 123) : ℂ) * ζ ^ 4 - ((24 / 41) : ℂ) * ζ ^ 6 - ((11 / 246) : ℂ) * ζ ^ 8 + ((94 / 123) : ℂ) * ζ ^ 10 - ((35 / 82) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((55 / 82) : ℂ) * ζ ^ 16 + ((13 / 246) : ℂ) * ζ ^ 18 - ((71 / 123) : ℂ) * ζ ^ 20 + ((31 / 246) : ℂ) * ζ ^ 22 + ((32 / 123) : ℂ) * ζ ^ 24 - ((11 / 123) : ℂ) * ζ ^ 26 - ((2 / 123) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((4 / 41) : ℂ) - ((19 / 82) : ℂ) * ζ ^ 2 - ((4 / 41) : ℂ) * ζ ^ 4 + ((53 / 82) : ℂ) * ζ ^ 6 + ((68 / 123) : ℂ) * ζ ^ 8 - ((125 / 82) : ℂ) * ζ ^ 10 + ((49 / 123) : ℂ) * ζ ^ 12 + ((5 / 3) : ℂ) * ζ ^ 14 - ((53 / 41) : ℂ) * ζ ^ 16 - ((17 / 123) : ℂ) * ζ ^ 18 + ((151 / 123) : ℂ) * ζ ^ 20 - ((91 / 123) : ℂ) * ζ ^ 22 - ((30 / 41) : ℂ) * ζ ^ 24 + ((95 / 123) : ℂ) * ζ ^ 26 - ((20 / 123) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 + ((4 / 41) : ℂ) * ζ ^ 4 - ((53 / 82) : ℂ) * ζ ^ 6 - ((68 / 123) : ℂ) * ζ ^ 8 + ((125 / 82) : ℂ) * ζ ^ 10 - ((49 / 123) : ℂ) * ζ ^ 12 - ((5 / 3) : ℂ) * ζ ^ 14 + ((53 / 41) : ℂ) * ζ ^ 16 + ((17 / 123) : ℂ) * ζ ^ 18 - ((151 / 123) : ℂ) * ζ ^ 20 + ((91 / 123) : ℂ) * ζ ^ 22 + ((30 / 41) : ℂ) * ζ ^ 24 - ((95 / 123) : ℂ) * ζ ^ 26 + ((20 / 123) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((40 / 123) : ℂ) * ζ ^ 4 + ((85 / 246) : ℂ) * ζ ^ 6 - ((19 / 82) : ℂ) * ζ ^ 8 - ((103 / 246) : ℂ) * ζ ^ 10 + ((5 / 82) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((47 / 246) : ℂ) * ζ ^ 16 - ((13 / 41) : ℂ) * ζ ^ 18 + ((73 / 246) : ℂ) * ζ ^ 20 + ((10 / 41) : ℂ) * ζ ^ 22 - ((28 / 123) : ℂ) * ζ ^ 24 - ((16 / 123) : ℂ) * ζ ^ 26 + ((4 / 41) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY32_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 3 2) = 0 := by
  have previous :=
    row17_reducedY32_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((7 / 451) : ℂ) - ((1162 / 1353) : ℂ) * ζ ^ 2 - ((333 / 451) : ℂ) * ζ ^ 6 - ((977 / 1353) : ℂ) * ζ ^ 8 - ((565 / 1353) : ℂ) * ζ ^ 12 + ((857 / 1353) : ℂ) * ζ ^ 18 + ((1162 / 1353) : ℂ) * ζ ^ 22 + ((1382 / 1353) : ℂ) * ζ ^ 24 + ((977 / 1353) : ℂ) * ζ ^ 28 + ((17 / 451) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((79 / 4961) : ℂ) - ((9217 / 19844) : ℂ) * ζ ^ 2 - ((79 / 4961) : ℂ) * ζ ^ 4 - ((568 / 4961) : ℂ) * ζ ^ 6 - ((9855 / 19844) : ℂ) * ζ ^ 8 - ((13 / 4961) : ℂ) * ζ ^ 10 - ((1549 / 19844) : ℂ) * ζ ^ 12 - ((3029 / 19844) : ℂ) * ζ ^ 14 - ((405 / 19844) : ℂ) * ζ ^ 16 - ((2273 / 19844) : ℂ) * ζ ^ 18 - ((3741 / 19844) : ℂ) * ζ ^ 20 - ((51 / 19844) : ℂ) * ζ ^ 22 - ((977 / 9922) : ℂ) * ζ ^ 24 - ((51 / 9922) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((27303 / 19844) : ℂ) + ((17505 / 19844) : ℂ) * ζ ^ 2 + ((27303 / 19844) : ℂ) * ζ ^ 4 - ((12057 / 9922) : ℂ) * ζ ^ 6 - ((5419 / 19844) : ℂ) * ζ ^ 8 + ((509 / 4961) : ℂ) * ζ ^ 10 - ((16943 / 19844) : ℂ) * ζ ^ 12 - ((5526 / 4961) : ℂ) * ζ ^ 14 - ((405 / 4961) : ℂ) * ζ ^ 16 - ((10937 / 9922) : ℂ) * ζ ^ 18 - ((15083 / 9922) : ℂ) * ζ ^ 20 - ((51 / 4961) : ℂ) * ζ ^ 22 - ((18563 / 19844) : ℂ) * ζ ^ 24 - ((969 / 19844) : ℂ) * ζ ^ 26)) * Y 1 1
        + ((((27303 / 19844) : ℂ) - ((17505 / 19844) : ℂ) * ζ ^ 2 - ((27303 / 19844) : ℂ) * ζ ^ 4 + ((12057 / 9922) : ℂ) * ζ ^ 6 + ((5419 / 19844) : ℂ) * ζ ^ 8 - ((509 / 4961) : ℂ) * ζ ^ 10 + ((16943 / 19844) : ℂ) * ζ ^ 12 + ((5526 / 4961) : ℂ) * ζ ^ 14 + ((405 / 4961) : ℂ) * ζ ^ 16 + ((10937 / 9922) : ℂ) * ζ ^ 18 + ((15083 / 9922) : ℂ) * ζ ^ 20 + ((51 / 4961) : ℂ) * ζ ^ 22 + ((18563 / 19844) : ℂ) * ζ ^ 24 + ((969 / 19844) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((8671 / 19844) : ℂ) - ((15115 / 19844) : ℂ) * ζ ^ 2 - ((8671 / 19844) : ℂ) * ζ ^ 4 + ((3065 / 4961) : ℂ) * ζ ^ 6 - ((7107 / 19844) : ℂ) * ζ ^ 8 + ((1423 / 9922) : ℂ) * ζ ^ 10 + ((16751 / 19844) : ℂ) * ζ ^ 12 - ((163 / 9922) : ℂ) * ζ ^ 14 - ((2025 / 9922) : ℂ) * ζ ^ 16 + ((3904 / 4961) : ℂ) * ζ ^ 18 + ((2049 / 4961) : ℂ) * ζ ^ 20 - ((255 / 9922) : ℂ) * ζ ^ 22 + ((12701 / 19844) : ℂ) * ζ ^ 24 + ((663 / 19844) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY32
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 3 2 = 0 := by
  have reduced :=
    row17_reducedY32_combinationStep05 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row17_reducedY33_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((634 / 123) : ℂ) * ζ ^ 2 + ((955 / 246) : ℂ) * ζ ^ 6 + ((135 / 82) : ℂ) * ζ ^ 18 + ((634 / 123) : ℂ) * ζ ^ 22 - ((4 / 123) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((77 / 123) : ℂ) * ζ ^ 2 + ((137 / 82) : ℂ) * ζ ^ 6 - ((142 / 123) : ℂ) * ζ ^ 18 - ((77 / 123) : ℂ) * ζ ^ 22 - ((32 / 41) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((((420 / 41) : ℂ) * ζ ^ 2 + ((1514 / 123) : ℂ) * ζ ^ 6 - ((952 / 123) : ℂ) * ζ ^ 18 - ((420 / 41) : ℂ) * ζ ^ 22 + ((274 / 41) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((949 / 123) : ℂ) * ζ ^ 2 - ((1048 / 123) : ℂ) * ζ ^ 6 + ((103 / 123) : ℂ) * ζ ^ 10 + ((227 / 82) : ℂ) * ζ ^ 14 - ζ ^ 18 - ((274 / 41) : ℂ) * ζ ^ 22 + ((411 / 82) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((77 / 123) : ℂ) * ζ ^ 2 - ((257 / 246) : ℂ) * ζ ^ 6 + ((257 / 246) : ℂ) * ζ ^ 10 + ((73 / 82) : ℂ) * ζ ^ 14 + ((137 / 82) : ℂ) * ζ ^ 18 - ((137 / 82) : ℂ) * ζ ^ 22)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY33_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((74 / 41) : ℂ) * ζ ^ 2 - ((341 / 246) : ℂ) * ζ ^ 6 + ((289 / 246) : ℂ) * ζ ^ 18 + ((74 / 41) : ℂ) * ζ ^ 22 - ((310 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((13 / 41) : ℂ) * ζ ^ 2 - ((25 / 246) : ℂ) * ζ ^ 6 - ((263 / 123) : ℂ) * ζ ^ 18 + ((13 / 41) : ℂ) * ζ ^ 22 + ((85 / 246) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((77 / 123) : ℂ) * ζ ^ 2 + ((137 / 82) : ℂ) * ζ ^ 6 - ((142 / 123) : ℂ) * ζ ^ 18 - ((77 / 123) : ℂ) * ζ ^ 22 - ((32 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((74 / 41) : ℂ) * ζ ^ 2 + ((341 / 246) : ℂ) * ζ ^ 6 - ((289 / 246) : ℂ) * ζ ^ 18 - ((74 / 41) : ℂ) * ζ ^ 22 + ((310 / 123) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY33_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((226 / 123) : ℂ) * ζ ^ 2 + ((110 / 41) : ℂ) * ζ ^ 6 + ((662 / 123) : ℂ) * ζ ^ 18 - ((226 / 123) : ℂ) * ζ ^ 22 + ((682 / 123) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((74 / 41) : ℂ) * ζ ^ 2 - ((103 / 246) : ℂ) * ζ ^ 6 + ((103 / 246) : ℂ) * ζ ^ 10 + ((38 / 41) : ℂ) * ζ ^ 14 - ((341 / 246) : ℂ) * ζ ^ 18 + ((341 / 246) : ℂ) * ζ ^ 22)) * Y 0 0
        + ((-((359 / 82) : ℂ) * ζ ^ 2 + ((1111 / 123) : ℂ) * ζ ^ 6 - ((2561 / 246) : ℂ) * ζ ^ 10 + ((146 / 41) : ℂ) * ζ ^ 14 + ((683 / 123) : ℂ) * ζ ^ 18 - ((1705 / 246) : ℂ) * ζ ^ 22 + ((341 / 82) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((74 / 41) : ℂ) * ζ ^ 2 + ((103 / 246) : ℂ) * ζ ^ 6 - ((103 / 246) : ℂ) * ζ ^ 10 - ((38 / 41) : ℂ) * ζ ^ 14 + ((341 / 246) : ℂ) * ζ ^ 18 - ((341 / 246) : ℂ) * ζ ^ 22)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY33_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((83 / 123) : ℂ) - ((143 / 82) : ℂ) * ζ ^ 2 - ((445 / 246) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 + ((305 / 246) : ℂ) * ζ ^ 18 + ((143 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((248 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((10 / 123) : ℂ) - ((29 / 41) : ℂ) * ζ ^ 2 - ((61 / 123) : ℂ) * ζ ^ 6 - ((17 / 123) : ℂ) * ζ ^ 8 + ((91 / 246) : ℂ) * ζ ^ 12 - ((407 / 246) : ℂ) * ζ ^ 18 + ((29 / 41) : ℂ) * ζ ^ 22 - ((53 / 246) : ℂ) * ζ ^ 24 + ((17 / 123) : ℂ) * ζ ^ 28 - ((137 / 123) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((77 / 123) : ℂ) * ζ ^ 2 + ((137 / 82) : ℂ) * ζ ^ 6 - ((142 / 123) : ℂ) * ζ ^ 18 - ((77 / 123) : ℂ) * ζ ^ 22 - ((32 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((74 / 41) : ℂ) * ζ ^ 2 + ((341 / 246) : ℂ) * ζ ^ 6 - ((289 / 246) : ℂ) * ζ ^ 18 - ((74 / 41) : ℂ) * ζ ^ 22 + ((310 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 - ((4 / 123) : ℂ) * ζ ^ 8 - ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 + ((14 / 41) : ℂ) * ζ ^ 24 + ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 3 3) = 0 := by
  have previous :=
    row17_reducedY33_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation03
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((2 / 3) : ℂ) + (2 : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 + ((2 / 3) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28 + ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((179 / 246) : ℂ) - ((2 / 41) : ℂ) * ζ ^ 2 - ((7 / 6) : ℂ) * ζ ^ 4 + ((18 / 41) : ℂ) * ζ ^ 6 + ((62 / 123) : ℂ) * ζ ^ 8 - ((71 / 82) : ℂ) * ζ ^ 10 + ((73 / 246) : ℂ) * ζ ^ 12 + ((193 / 246) : ℂ) * ζ ^ 14 - ((34 / 41) : ℂ) * ζ ^ 16 - ((35 / 82) : ℂ) * ζ ^ 18 + ((94 / 123) : ℂ) * ζ ^ 20 - ((79 / 246) : ℂ) * ζ ^ 24 + ((13 / 41) : ℂ) * ζ ^ 26 + ((28 / 123) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((7 / 123) : ℂ) + ((1 / 82) : ℂ) * ζ ^ 2 + ((1 / 6) : ℂ) * ζ ^ 4 + ((55 / 246) : ℂ) * ζ ^ 6 - ((31 / 246) : ℂ) * ζ ^ 8 + ((1 / 123) : ℂ) * ζ ^ 10 - ((49 / 246) : ℂ) * ζ ^ 12 - ((20 / 41) : ℂ) * ζ ^ 14 + ((46 / 123) : ℂ) * ζ ^ 16 + ((19 / 82) : ℂ) * ζ ^ 18 - ((44 / 123) : ℂ) * ζ ^ 20 + ((56 / 123) : ℂ) * ζ ^ 24 - ((20 / 123) : ℂ) * ζ ^ 26 - ((16 / 41) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((8 / 123) : ℂ) - ((103 / 246) : ℂ) * ζ ^ 2 - ((1 / 3) : ℂ) * ζ ^ 4 + ((63 / 82) : ℂ) * ζ ^ 6 + ((2 / 41) : ℂ) * ζ ^ 8 - ((301 / 246) : ℂ) * ζ ^ 10 + ((23 / 41) : ℂ) * ζ ^ 12 + ((143 / 246) : ℂ) * ζ ^ 14 - ((39 / 41) : ℂ) * ζ ^ 16 + ((26 / 123) : ℂ) * ζ ^ 18 + ((55 / 82) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 - ((23 / 123) : ℂ) * ζ ^ 24 + ((58 / 123) : ℂ) * ζ ^ 26 + ((8 / 123) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((179 / 246) : ℂ) + ((2 / 41) : ℂ) * ζ ^ 2 + ((7 / 6) : ℂ) * ζ ^ 4 - ((18 / 41) : ℂ) * ζ ^ 6 - ((62 / 123) : ℂ) * ζ ^ 8 + ((71 / 82) : ℂ) * ζ ^ 10 - ((73 / 246) : ℂ) * ζ ^ 12 - ((193 / 246) : ℂ) * ζ ^ 14 + ((34 / 41) : ℂ) * ζ ^ 16 + ((35 / 82) : ℂ) * ζ ^ 18 - ((94 / 123) : ℂ) * ζ ^ 20 + ((79 / 246) : ℂ) * ζ ^ 24 - ((13 / 41) : ℂ) * ζ ^ 26 - ((28 / 123) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY33_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((10 / 123) : ℂ) + ((16 / 41) : ℂ) * ζ ^ 2 + ((97 / 246) : ℂ) * ζ ^ 6 - ((17 / 123) : ℂ) * ζ ^ 8 + ((91 / 246) : ℂ) * ζ ^ 12 - ((119 / 246) : ℂ) * ζ ^ 18 - ((16 / 41) : ℂ) * ζ ^ 22 - ((53 / 246) : ℂ) * ζ ^ 24 + ((17 / 123) : ℂ) * ζ ^ 28 + ((359 / 246) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((77 / 123) : ℂ) * ζ ^ 2 + ((137 / 82) : ℂ) * ζ ^ 6 - ((142 / 123) : ℂ) * ζ ^ 18 - ((77 / 123) : ℂ) * ζ ^ 22 - ((32 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((74 / 41) : ℂ) * ζ ^ 2 + ((341 / 246) : ℂ) * ζ ^ 6 - ((289 / 246) : ℂ) * ζ ^ 18 - ((74 / 41) : ℂ) * ζ ^ 22 + ((310 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 - ((4 / 123) : ℂ) * ζ ^ 8 - ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 + ((14 / 41) : ℂ) * ζ ^ 24 + ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((-((69 / 41) : ℂ) * ζ ^ 2 - ((183 / 82) : ℂ) * ζ ^ 6 + ((107 / 82) : ℂ) * ζ ^ 18 + ((69 / 41) : ℂ) * ζ ^ 22 - ((62 / 41) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((120 / 451) : ℂ) * ζ ^ 2 - ((639 / 902) : ℂ) * ζ ^ 6 - ((687 / 902) : ℂ) * ζ ^ 18 - ((120 / 451) : ℂ) * ζ ^ 22 - ((197 / 451) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY33_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((3622 / 1353) : ℂ) * ζ ^ 2 - ((1778 / 1353) : ℂ) * ζ ^ 6 + ((2374 / 1353) : ℂ) * ζ ^ 18 + ((3622 / 1353) : ℂ) * ζ ^ 22 - ((2450 / 1353) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1105 / 4961) : ℂ) * ζ ^ 2 - ((12821 / 9922) : ℂ) * ζ ^ 6 + ((9199 / 9922) : ℂ) * ζ ^ 10 - ((255 / 4961) : ℂ) * ζ ^ 14 - ((4847 / 9922) : ℂ) * ζ ^ 18 + ((1225 / 9922) : ℂ) * ζ ^ 22 + ((1225 / 4961) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((27141 / 9922) : ℂ) * ζ ^ 2 - ((17305 / 9922) : ℂ) * ζ ^ 6 - ((8552 / 4961) : ℂ) * ζ ^ 10 - ((811 / 4961) : ℂ) * ζ ^ 14 - ((39309 / 9922) : ℂ) * ζ ^ 18 + ((2450 / 4961) : ℂ) * ζ ^ 22 + ((23275 / 9922) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((1105 / 4961) : ℂ) * ζ ^ 2 + ((12821 / 9922) : ℂ) * ζ ^ 6 - ((9199 / 9922) : ℂ) * ζ ^ 10 + ((255 / 4961) : ℂ) * ζ ^ 14 + ((4847 / 9922) : ℂ) * ζ ^ 18 - ((1225 / 9922) : ℂ) * ζ ^ 22 - ((1225 / 4961) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((3131 / 4961) : ℂ) * ζ ^ 2 + ((11513 / 9922) : ℂ) * ζ ^ 6 - ((647 / 9922) : ℂ) * ζ ^ 10 + ((765 / 4961) : ℂ) * ζ ^ 14 + ((14541 / 9922) : ℂ) * ζ ^ 18 - ((3675 / 9922) : ℂ) * ζ ^ 22 - ((3675 / 4961) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY33_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((77 / 123) : ℂ) * ζ ^ 2 + ((137 / 82) : ℂ) * ζ ^ 6 - ((142 / 123) : ℂ) * ζ ^ 18 - ((77 / 123) : ℂ) * ζ ^ 22 - ((32 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((74 / 41) : ℂ) * ζ ^ 2 + ((341 / 246) : ℂ) * ζ ^ 6 - ((289 / 246) : ℂ) * ζ ^ 18 - ((74 / 41) : ℂ) * ζ ^ 22 + ((310 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 - ((4 / 123) : ℂ) * ζ ^ 8 - ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 + ((14 / 41) : ℂ) * ζ ^ 24 + ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((-((69 / 41) : ℂ) * ζ ^ 2 - ((183 / 82) : ℂ) * ζ ^ 6 + ((107 / 82) : ℂ) * ζ ^ 18 + ((69 / 41) : ℂ) * ζ ^ 22 - ((62 / 41) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((120 / 451) : ℂ) * ζ ^ 2 - ((639 / 902) : ℂ) * ζ ^ 6 - ((687 / 902) : ℂ) * ζ ^ 18 - ((120 / 451) : ℂ) * ζ ^ 22 - ((197 / 451) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY33_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) + (2 : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 + ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((179 / 246) : ℂ) - ((2 / 41) : ℂ) * ζ ^ 2 + ((7 / 6) : ℂ) * ζ ^ 4 + ((18 / 41) : ℂ) * ζ ^ 6 - ((62 / 123) : ℂ) * ζ ^ 8 - ((71 / 82) : ℂ) * ζ ^ 10 - ((73 / 246) : ℂ) * ζ ^ 12 + ((193 / 246) : ℂ) * ζ ^ 14 + ((34 / 41) : ℂ) * ζ ^ 16 - ((35 / 82) : ℂ) * ζ ^ 18 - ((94 / 123) : ℂ) * ζ ^ 20 + ((79 / 246) : ℂ) * ζ ^ 24 + ((13 / 41) : ℂ) * ζ ^ 26 - ((28 / 123) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((7 / 123) : ℂ) + ((1 / 82) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 4 + ((55 / 246) : ℂ) * ζ ^ 6 + ((31 / 246) : ℂ) * ζ ^ 8 + ((1 / 123) : ℂ) * ζ ^ 10 + ((49 / 246) : ℂ) * ζ ^ 12 - ((20 / 41) : ℂ) * ζ ^ 14 - ((46 / 123) : ℂ) * ζ ^ 16 + ((19 / 82) : ℂ) * ζ ^ 18 + ((44 / 123) : ℂ) * ζ ^ 20 - ((56 / 123) : ℂ) * ζ ^ 24 - ((20 / 123) : ℂ) * ζ ^ 26 + ((16 / 41) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((8 / 123) : ℂ) - ((103 / 246) : ℂ) * ζ ^ 2 + ((1 / 3) : ℂ) * ζ ^ 4 + ((63 / 82) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 - ((301 / 246) : ℂ) * ζ ^ 10 - ((23 / 41) : ℂ) * ζ ^ 12 + ((143 / 246) : ℂ) * ζ ^ 14 + ((39 / 41) : ℂ) * ζ ^ 16 + ((26 / 123) : ℂ) * ζ ^ 18 - ((55 / 82) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((23 / 123) : ℂ) * ζ ^ 24 + ((58 / 123) : ℂ) * ζ ^ 26 - ((8 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((179 / 246) : ℂ) + ((2 / 41) : ℂ) * ζ ^ 2 - ((7 / 6) : ℂ) * ζ ^ 4 - ((18 / 41) : ℂ) * ζ ^ 6 + ((62 / 123) : ℂ) * ζ ^ 8 + ((71 / 82) : ℂ) * ζ ^ 10 + ((73 / 246) : ℂ) * ζ ^ 12 - ((193 / 246) : ℂ) * ζ ^ 14 - ((34 / 41) : ℂ) * ζ ^ 16 + ((35 / 82) : ℂ) * ζ ^ 18 + ((94 / 123) : ℂ) * ζ ^ 20 - ((79 / 246) : ℂ) * ζ ^ 24 - ((13 / 41) : ℂ) * ζ ^ 26 + ((28 / 123) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY33_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((15 / 41) : ℂ) + ((173 / 246) : ℂ) * ζ ^ 2 + ((47 / 41) : ℂ) * ζ ^ 6 + ((31 / 82) : ℂ) * ζ ^ 8 + ((10 / 123) : ℂ) * ζ ^ 12 - ((110 / 123) : ℂ) * ζ ^ 18 - ((173 / 246) : ℂ) * ζ ^ 22 - ((13 / 246) : ℂ) * ζ ^ 24 - ((31 / 82) : ℂ) * ζ ^ 28 - ((49 / 82) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((40 / 123) : ℂ) + ((143 / 82) : ℂ) * ζ ^ 2 + ((445 / 246) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 - ((305 / 246) : ℂ) * ζ ^ 18 - ((143 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 + ((248 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + (((1 : ℂ))) * Y 3 3
      + ((-((69 / 41) : ℂ) * ζ ^ 2 - ((183 / 82) : ℂ) * ζ ^ 6 + ((107 / 82) : ℂ) * ζ ^ 18 + ((69 / 41) : ℂ) * ζ ^ 22 - ((62 / 41) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((120 / 451) : ℂ) * ζ ^ 2 - ((639 / 902) : ℂ) * ζ ^ 6 - ((687 / 902) : ℂ) * ζ ^ 18 - ((120 / 451) : ℂ) * ζ ^ 22 - ((197 / 451) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY33_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation13
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 - ((15 / 41) : ℂ) * ζ ^ 4 + ((45 / 82) : ℂ) * ζ ^ 6 + ((59 / 246) : ℂ) * ζ ^ 8 - ((69 / 82) : ℂ) * ζ ^ 10 + ((19 / 246) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 - ((65 / 246) : ℂ) * ζ ^ 16 - ((107 / 246) : ℂ) * ζ ^ 18 + ((29 / 82) : ℂ) * ζ ^ 20 + ((35 / 246) : ℂ) * ζ ^ 22 - ((10 / 41) : ℂ) * ζ ^ 24 - ((5 / 246) : ℂ) * ζ ^ 26 + ((7 / 123) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((40 / 123) : ℂ) * ζ ^ 4 - ((85 / 246) : ℂ) * ζ ^ 6 + ((19 / 82) : ℂ) * ζ ^ 8 + ((103 / 246) : ℂ) * ζ ^ 10 - ((5 / 82) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 + ((47 / 246) : ℂ) * ζ ^ 16 + ((13 / 41) : ℂ) * ζ ^ 18 - ((73 / 246) : ℂ) * ζ ^ 20 - ((10 / 41) : ℂ) * ζ ^ 22 + ((28 / 123) : ℂ) * ζ ^ 24 + ((16 / 123) : ℂ) * ζ ^ 26 - ((4 / 41) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 + ((4 / 41) : ℂ) * ζ ^ 4 - ((53 / 82) : ℂ) * ζ ^ 6 - ((68 / 123) : ℂ) * ζ ^ 8 + ((125 / 82) : ℂ) * ζ ^ 10 - ((49 / 123) : ℂ) * ζ ^ 12 - ((5 / 3) : ℂ) * ζ ^ 14 + ((53 / 41) : ℂ) * ζ ^ 16 + ((17 / 123) : ℂ) * ζ ^ 18 - ((151 / 123) : ℂ) * ζ ^ 20 + ((91 / 123) : ℂ) * ζ ^ 22 + ((30 / 41) : ℂ) * ζ ^ 24 - ((95 / 123) : ℂ) * ζ ^ 26 + ((20 / 123) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((40 / 123) : ℂ) * ζ ^ 4 + ((85 / 246) : ℂ) * ζ ^ 6 - ((19 / 82) : ℂ) * ζ ^ 8 - ((103 / 246) : ℂ) * ζ ^ 10 + ((5 / 82) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 - ((47 / 246) : ℂ) * ζ ^ 16 - ((13 / 41) : ℂ) * ζ ^ 18 + ((73 / 246) : ℂ) * ζ ^ 20 + ((10 / 41) : ℂ) * ζ ^ 22 - ((28 / 123) : ℂ) * ζ ^ 24 - ((16 / 123) : ℂ) * ζ ^ 26 + ((4 / 41) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY33_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((43 / 82) : ℂ) * ζ ^ 6 + ((31 / 82) : ℂ) * ζ ^ 8 + ((10 / 123) : ℂ) * ζ ^ 12 - ((32 / 123) : ℂ) * ζ ^ 18 + ((19 / 246) : ℂ) * ζ ^ 22 - ((13 / 246) : ℂ) * ζ ^ 24 - ((31 / 82) : ℂ) * ζ ^ 28 - ((15 / 82) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + (((1 : ℂ))) * Y 3 3
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY33_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((508 / 1353) : ℂ) * ζ ^ 2 + ((158 / 451) : ℂ) * ζ ^ 6 - ((1612 / 1353) : ℂ) * ζ ^ 18 - ((508 / 1353) : ℂ) * ζ ^ 22 - ((398 / 1353) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((2856 / 4961) : ℂ) * ζ ^ 2 - ((1437 / 9922) : ℂ) * ζ ^ 6 + ((1945 / 9922) : ℂ) * ζ ^ 10 + ((2463 / 9922) : ℂ) * ζ ^ 14 + ((309 / 9922) : ℂ) * ζ ^ 18 + ((199 / 9922) : ℂ) * ζ ^ 22 + ((199 / 4961) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((5682 / 4961) : ℂ) * ζ ^ 2 + ((2901 / 4961) : ℂ) * ζ ^ 6 - ((488 / 4961) : ℂ) * ζ ^ 10 + ((20907 / 9922) : ℂ) * ζ ^ 14 + ((2015 / 4961) : ℂ) * ζ ^ 18 + ((398 / 4961) : ℂ) * ζ ^ 22 + ((3781 / 9922) : ℂ) * ζ ^ 26)) * Y 1 1
        + ((-((5682 / 4961) : ℂ) * ζ ^ 2 - ((2901 / 4961) : ℂ) * ζ ^ 6 + ((488 / 4961) : ℂ) * ζ ^ 10 - ((20907 / 9922) : ℂ) * ζ ^ 14 - ((2015 / 4961) : ℂ) * ζ ^ 18 - ((398 / 4961) : ℂ) * ζ ^ 22 - ((3781 / 9922) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((939 / 4961) : ℂ) * ζ ^ 2 - ((4809 / 4961) : ℂ) * ζ ^ 6 + ((3158 / 4961) : ℂ) * ζ ^ 10 - ((8535 / 9922) : ℂ) * ζ ^ 14 - ((2646 / 4961) : ℂ) * ζ ^ 18 + ((995 / 4961) : ℂ) * ζ ^ 22 - ((2587 / 9922) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY33_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 3 3
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY33_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((15 / 41) : ℂ) * ζ ^ 4 + ((45 / 82) : ℂ) * ζ ^ 6 - ((59 / 246) : ℂ) * ζ ^ 8 - ((69 / 82) : ℂ) * ζ ^ 10 - ((19 / 246) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ((65 / 246) : ℂ) * ζ ^ 16 - ((107 / 246) : ℂ) * ζ ^ 18 - ((29 / 82) : ℂ) * ζ ^ 20 + ((35 / 246) : ℂ) * ζ ^ 22 + ((10 / 41) : ℂ) * ζ ^ 24 - ((5 / 246) : ℂ) * ζ ^ 26 - ((7 / 123) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 + ((40 / 123) : ℂ) * ζ ^ 4 - ((85 / 246) : ℂ) * ζ ^ 6 - ((19 / 82) : ℂ) * ζ ^ 8 + ((103 / 246) : ℂ) * ζ ^ 10 + ((5 / 82) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ((47 / 246) : ℂ) * ζ ^ 16 + ((13 / 41) : ℂ) * ζ ^ 18 + ((73 / 246) : ℂ) * ζ ^ 20 - ((10 / 41) : ℂ) * ζ ^ 22 - ((28 / 123) : ℂ) * ζ ^ 24 + ((16 / 123) : ℂ) * ζ ^ 26 + ((4 / 41) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((4 / 41) : ℂ) * ζ ^ 4 - ((53 / 82) : ℂ) * ζ ^ 6 + ((68 / 123) : ℂ) * ζ ^ 8 + ((125 / 82) : ℂ) * ζ ^ 10 + ((49 / 123) : ℂ) * ζ ^ 12 - ((5 / 3) : ℂ) * ζ ^ 14 - ((53 / 41) : ℂ) * ζ ^ 16 + ((17 / 123) : ℂ) * ζ ^ 18 + ((151 / 123) : ℂ) * ζ ^ 20 + ((91 / 123) : ℂ) * ζ ^ 22 - ((30 / 41) : ℂ) * ζ ^ 24 - ((95 / 123) : ℂ) * ζ ^ 26 - ((20 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 - ((40 / 123) : ℂ) * ζ ^ 4 + ((85 / 246) : ℂ) * ζ ^ 6 + ((19 / 82) : ℂ) * ζ ^ 8 - ((103 / 246) : ℂ) * ζ ^ 10 - ((5 / 82) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((47 / 246) : ℂ) * ζ ^ 16 - ((13 / 41) : ℂ) * ζ ^ 18 - ((73 / 246) : ℂ) * ζ ^ 20 + ((10 / 41) : ℂ) * ζ ^ 22 + ((28 / 123) : ℂ) * ζ ^ 24 - ((16 / 123) : ℂ) * ζ ^ 26 - ((4 / 41) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY33
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 3 3 = Y 7 7 := by
  have reduced :=
    row17_reducedY33_combinationStep07 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row17_reducedY44_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((328223 / 102828) : ℂ) - ((99217 / 25707) : ℂ) * ζ ^ 2 - ((286993 / 102828) : ℂ) * ζ ^ 6 + ((309679 / 102828) : ℂ) * ζ ^ 8 + ((136269 / 34276) : ℂ) * ζ ^ 12 + ((6777 / 8569) : ℂ) * ζ ^ 18 + ((99217 / 25707) : ℂ) * ζ ^ 22 + ((152785 / 102828) : ℂ) * ζ ^ 24 - ((309679 / 102828) : ℂ) * ζ ^ 28 - ((196873 / 102828) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((24159 / 17138) : ℂ) + ((5023 / 51414) : ℂ) * ζ ^ 2 + ((34537 / 34276) : ℂ) * ζ ^ 6 + ((35185 / 34276) : ℂ) * ζ ^ 8 - ((20473 / 102828) : ℂ) * ζ ^ 12 + ((17273 / 102828) : ℂ) * ζ ^ 18 - ((5023 / 51414) : ℂ) * ζ ^ 22 - ((51382 / 25707) : ℂ) * ζ ^ 24 - ((35185 / 34276) : ℂ) * ζ ^ 28 + ((8687 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((165427 / 25707) : ℂ) - ((19783 / 8569) : ℂ) * ζ ^ 2 + ((61535 / 25707) : ℂ) * ζ ^ 6 + ((331556 / 25707) : ℂ) * ζ ^ 8 + ((35185 / 8569) : ℂ) * ζ ^ 12 + ((69395 / 25707) : ℂ) * ζ ^ 18 + ((19783 / 8569) : ℂ) * ζ ^ 22 - ((370955 / 25707) : ℂ) * ζ ^ 24 - ((331556 / 25707) : ℂ) * ζ ^ 28 + ((34537 / 8569) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((82275 / 17138) : ℂ) + ((337519 / 102828) : ℂ) * ζ ^ 2 + ((82275 / 17138) : ℂ) * ζ ^ 4 + ((11009 / 102828) : ℂ) * ζ ^ 6 + ((557 / 2337) : ℂ) * ζ ^ 8 + ((83519 / 51414) : ℂ) * ζ ^ 10 - ((2342 / 209) : ℂ) * ζ ^ 12 - ((22137 / 17138) : ℂ) * ζ ^ 14 + ((13133 / 8569) : ℂ) * ζ ^ 16 + ((4817 / 836) : ℂ) * ζ ^ 18 + ((213359 / 102828) : ℂ) * ζ ^ 20 - ((34537 / 8569) : ℂ) * ζ ^ 22 - ((82889 / 8569) : ℂ) * ζ ^ 24 + ((103611 / 34276) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((24159 / 17138) : ℂ) - ((5023 / 51414) : ℂ) * ζ ^ 2 - ((24159 / 17138) : ℂ) * ζ ^ 4 - ((93565 / 102828) : ℂ) * ζ ^ 6 + ((13133 / 34276) : ℂ) * ζ ^ 8 + ((93565 / 102828) : ℂ) * ζ ^ 10 - ((13133 / 34276) : ℂ) * ζ ^ 12 - ((13580 / 8569) : ℂ) * ζ ^ 14 + ((13133 / 34276) : ℂ) * ζ ^ 16 + ((34537 / 34276) : ℂ) * ζ ^ 18 + ((82889 / 25707) : ℂ) * ζ ^ 20 - ((34537 / 34276) : ℂ) * ζ ^ 22)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY44_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((36983 / 102828) : ℂ) + ((6494 / 8569) : ℂ) * ζ ^ 2 + ((33527 / 102828) : ℂ) * ζ ^ 6 - ((72579 / 34276) : ℂ) * ζ ^ 8 - ((139013 / 102828) : ℂ) * ζ ^ 12 - ((7501 / 25707) : ℂ) * ζ ^ 18 - ((6494 / 8569) : ℂ) * ζ ^ 22 + ((62927 / 34276) : ℂ) * ζ ^ 24 + ((72579 / 34276) : ℂ) * ζ ^ 28 - ((83701 / 102828) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((36671 / 102828) : ℂ) + ((105143 / 34276) : ℂ) * ζ ^ 2 + ((270049 / 102828) : ℂ) * ζ ^ 6 - ((89050 / 25707) : ℂ) * ζ ^ 8 - ((204035 / 102828) : ℂ) * ζ ^ 12 - ((219281 / 102828) : ℂ) * ζ ^ 18 - ((105143 / 34276) : ℂ) * ζ ^ 22 + ((98029 / 102828) : ℂ) * ζ ^ 24 + ((89050 / 25707) : ℂ) * ζ ^ 28 + ((9545 / 5412) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((24159 / 17138) : ℂ) + ((5023 / 51414) : ℂ) * ζ ^ 2 + ((34537 / 34276) : ℂ) * ζ ^ 6 + ((35185 / 34276) : ℂ) * ζ ^ 8 - ((20473 / 102828) : ℂ) * ζ ^ 12 + ((17273 / 102828) : ℂ) * ζ ^ 18 - ((5023 / 51414) : ℂ) * ζ ^ 22 - ((51382 / 25707) : ℂ) * ζ ^ 24 - ((35185 / 34276) : ℂ) * ζ ^ 28 + ((8687 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((36983 / 102828) : ℂ) - ((6494 / 8569) : ℂ) * ζ ^ 2 - ((33527 / 102828) : ℂ) * ζ ^ 6 + ((72579 / 34276) : ℂ) * ζ ^ 8 + ((139013 / 102828) : ℂ) * ζ ^ 12 + ((7501 / 25707) : ℂ) * ζ ^ 18 + ((6494 / 8569) : ℂ) * ζ ^ 22 - ((62927 / 34276) : ℂ) * ζ ^ 24 - ((72579 / 34276) : ℂ) * ζ ^ 28 + ((83701 / 102828) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY44_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((1790 / 451) : ℂ) - ((191633 / 25707) : ℂ) * ζ ^ 2 - ((65052 / 8569) : ℂ) * ζ ^ 6 + ((267505 / 25707) : ℂ) * ζ ^ 8 + ((72579 / 8569) : ℂ) * ζ ^ 12 + ((113705 / 25707) : ℂ) * ζ ^ 18 + ((191633 / 25707) : ℂ) * ζ ^ 22 - ((28917 / 8569) : ℂ) * ζ ^ 24 - ((267505 / 25707) : ℂ) * ζ ^ 28 - ((33527 / 25707) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((36983 / 102828) : ℂ) - ((6494 / 8569) : ℂ) * ζ ^ 2 + ((36983 / 102828) : ℂ) * ζ ^ 4 + ((44401 / 102828) : ℂ) * ζ ^ 6 + ((90377 / 51414) : ℂ) * ζ ^ 8 - ((44401 / 102828) : ℂ) * ζ ^ 10 - ((90377 / 51414) : ℂ) * ζ ^ 12 + ((26351 / 17138) : ℂ) * ζ ^ 14 + ((90377 / 51414) : ℂ) * ζ ^ 16 + ((33527 / 102828) : ℂ) * ζ ^ 18 - ((267505 / 102828) : ℂ) * ζ ^ 20 - ((33527 / 102828) : ℂ) * ζ ^ 22)) * Y 0 0
        + ((((116731 / 25707) : ℂ) - ((150655 / 17138) : ℂ) * ζ ^ 2 - ((116731 / 25707) : ℂ) * ζ ^ 4 + ((37933 / 25707) : ℂ) * ζ ^ 6 + ((547109 / 51414) : ℂ) * ζ ^ 8 + ((423167 / 102828) : ℂ) * ζ ^ 10 + ((9205 / 9348) : ℂ) * ζ ^ 12 - ((45833 / 8569) : ℂ) * ζ ^ 14 - ((451885 / 51414) : ℂ) * ζ ^ 16 + ((9256 / 2337) : ℂ) * ζ ^ 18 + ((269318 / 25707) : ℂ) * ζ ^ 20 + ((167635 / 102828) : ℂ) * ζ ^ 22 - ((267505 / 34276) : ℂ) * ζ ^ 24 - ((33527 / 34276) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((36983 / 102828) : ℂ) + ((6494 / 8569) : ℂ) * ζ ^ 2 - ((36983 / 102828) : ℂ) * ζ ^ 4 - ((44401 / 102828) : ℂ) * ζ ^ 6 - ((90377 / 51414) : ℂ) * ζ ^ 8 + ((44401 / 102828) : ℂ) * ζ ^ 10 + ((90377 / 51414) : ℂ) * ζ ^ 12 - ((26351 / 17138) : ℂ) * ζ ^ 14 - ((90377 / 51414) : ℂ) * ζ ^ 16 - ((33527 / 102828) : ℂ) * ζ ^ 18 + ((267505 / 102828) : ℂ) * ζ ^ 20 + ((33527 / 102828) : ℂ) * ζ ^ 22)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY44_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((21349 / 102828) : ℂ) + ((15987 / 17138) : ℂ) * ζ ^ 2 + ((18467 / 34276) : ℂ) * ζ ^ 6 - ((226693 / 102828) : ℂ) * ζ ^ 8 - ((44557 / 34276) : ℂ) * ζ ^ 12 + ((479 / 25707) : ℂ) * ζ ^ 18 - ((15987 / 17138) : ℂ) * ζ ^ 22 + ((186551 / 102828) : ℂ) * ζ ^ 24 + ((226693 / 102828) : ℂ) * ζ ^ 28 - ((112333 / 102828) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((29339 / 102828) : ℂ) + ((84107 / 34276) : ℂ) * ζ ^ 2 + ((14017 / 5412) : ℂ) * ζ ^ 6 - ((182003 / 51414) : ℂ) * ζ ^ 8 - ((259511 / 102828) : ℂ) * ζ ^ 12 - ((230623 / 102828) : ℂ) * ζ ^ 18 - ((84107 / 34276) : ℂ) * ζ ^ 22 + ((36231 / 34276) : ℂ) * ζ ^ 24 + ((182003 / 51414) : ℂ) * ζ ^ 28 + ((71065 / 34276) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((24159 / 17138) : ℂ) + ((5023 / 51414) : ℂ) * ζ ^ 2 + ((34537 / 34276) : ℂ) * ζ ^ 6 + ((35185 / 34276) : ℂ) * ζ ^ 8 - ((20473 / 102828) : ℂ) * ζ ^ 12 + ((17273 / 102828) : ℂ) * ζ ^ 18 - ((5023 / 51414) : ℂ) * ζ ^ 22 - ((51382 / 25707) : ℂ) * ζ ^ 24 - ((35185 / 34276) : ℂ) * ζ ^ 28 + ((8687 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((36983 / 102828) : ℂ) - ((6494 / 8569) : ℂ) * ζ ^ 2 - ((33527 / 102828) : ℂ) * ζ ^ 6 + ((72579 / 34276) : ℂ) * ζ ^ 8 + ((139013 / 102828) : ℂ) * ζ ^ 12 + ((7501 / 25707) : ℂ) * ζ ^ 18 + ((6494 / 8569) : ℂ) * ζ ^ 22 - ((62927 / 34276) : ℂ) * ζ ^ 24 - ((72579 / 34276) : ℂ) * ζ ^ 28 + ((83701 / 102828) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((7817 / 51414) : ℂ) - ((2999 / 17138) : ℂ) * ζ ^ 2 - ((10937 / 51414) : ℂ) * ζ ^ 6 + ((2239 / 25707) : ℂ) * ζ ^ 8 - ((2671 / 51414) : ℂ) * ζ ^ 12 - ((140 / 451) : ℂ) * ζ ^ 18 + ((2999 / 17138) : ℂ) * ζ ^ 22 + ((1115 / 51414) : ℂ) * ζ ^ 24 - ((2239 / 25707) : ℂ) * ζ ^ 28 + ((2386 / 8569) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((227 / 2706) : ℂ) - ((1559 / 2706) : ℂ) * ζ ^ 2 - ((494 / 1353) : ℂ) * ζ ^ 6 + ((523 / 1353) : ℂ) * ζ ^ 8 + ((485 / 1353) : ℂ) * ζ ^ 12 + ((529 / 902) : ℂ) * ζ ^ 18 + ((1559 / 2706) : ℂ) * ζ ^ 22 - ((592 / 1353) : ℂ) * ζ ^ 24 - ((523 / 1353) : ℂ) * ζ ^ 28 - ((523 / 902) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have previous :=
    row17_reducedY44_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation02
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((344 / 209) : ℂ) + ((490 / 209) : ℂ) * ζ ^ 2 + ((716 / 627) : ℂ) * ζ ^ 6 - ((416 / 209) : ℂ) * ζ ^ 8 - ((1396 / 627) : ℂ) * ζ ^ 12 - ((620 / 627) : ℂ) * ζ ^ 18 - ((490 / 209) : ℂ) * ζ ^ 22 + ((970 / 627) : ℂ) * ζ ^ 24 + ((416 / 209) : ℂ) * ζ ^ 28 + ((574 / 627) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((11945 / 51414) : ℂ) + ((2745 / 17138) : ℂ) * ζ ^ 2 + ((4225 / 51414) : ℂ) * ζ ^ 4 - ((2202 / 8569) : ℂ) * ζ ^ 6 + ((23027 / 51414) : ℂ) * ζ ^ 8 + ((3589 / 8569) : ℂ) * ζ ^ 10 - ((6353 / 51414) : ℂ) * ζ ^ 12 - ((3112 / 25707) : ℂ) * ζ ^ 14 + ((3803 / 51414) : ℂ) * ζ ^ 16 - ((1525 / 17138) : ℂ) * ζ ^ 18 + ((3880 / 25707) : ℂ) * ζ ^ 20 + ((4299 / 17138) : ℂ) * ζ ^ 22 - ((8786 / 25707) : ℂ) * ζ ^ 24 - ((1851 / 8569) : ℂ) * ζ ^ 26 - ((14 / 627) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((783 / 8569) : ℂ) - ((4274 / 8569) : ℂ) * ζ ^ 2 - ((12447 / 8569) : ℂ) * ζ ^ 4 - ((5717 / 51414) : ℂ) * ζ ^ 6 - ((10316 / 8569) : ℂ) * ζ ^ 8 - ((7741 / 51414) : ℂ) * ζ ^ 10 + ((1093 / 2337) : ℂ) * ζ ^ 12 + ((409 / 25707) : ℂ) * ζ ^ 14 - ((17393 / 25707) : ℂ) * ζ ^ 16 - ((204 / 8569) : ℂ) * ζ ^ 18 + ((31789 / 25707) : ℂ) * ζ ^ 20 - ((2039 / 8569) : ℂ) * ζ ^ 22 + ((40060 / 25707) : ℂ) * ζ ^ 24 + ((3305 / 25707) : ℂ) * ζ ^ 26 - ((140 / 627) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((11945 / 51414) : ℂ) - ((2745 / 17138) : ℂ) * ζ ^ 2 - ((4225 / 51414) : ℂ) * ζ ^ 4 + ((2202 / 8569) : ℂ) * ζ ^ 6 - ((23027 / 51414) : ℂ) * ζ ^ 8 - ((3589 / 8569) : ℂ) * ζ ^ 10 + ((6353 / 51414) : ℂ) * ζ ^ 12 + ((3112 / 25707) : ℂ) * ζ ^ 14 - ((3803 / 51414) : ℂ) * ζ ^ 16 + ((1525 / 17138) : ℂ) * ζ ^ 18 - ((3880 / 25707) : ℂ) * ζ ^ 20 - ((4299 / 17138) : ℂ) * ζ ^ 22 + ((8786 / 25707) : ℂ) * ζ ^ 24 + ((1851 / 8569) : ℂ) * ζ ^ 26 + ((14 / 627) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((11021 / 51414) : ℂ) + ((19321 / 25707) : ℂ) * ζ ^ 2 + ((37481 / 51414) : ℂ) * ζ ^ 4 - ((6844 / 25707) : ℂ) * ζ ^ 6 - ((4526 / 25707) : ℂ) * ζ ^ 8 + ((739 / 4674) : ℂ) * ζ ^ 10 + ((795 / 17138) : ℂ) * ζ ^ 12 + ((9335 / 51414) : ℂ) * ζ ^ 14 + ((3241 / 17138) : ℂ) * ζ ^ 16 - ((4757 / 25707) : ℂ) * ζ ^ 18 - ((10847 / 51414) : ℂ) * ζ ^ 20 + ((3955 / 51414) : ℂ) * ζ ^ 22 - ((5167 / 25707) : ℂ) * ζ ^ 24 - ((15337 / 51414) : ℂ) * ζ ^ 26 - ((49 / 627) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY44_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((22223 / 102828) : ℂ) + ((1177 / 1558) : ℂ) * ζ ^ 2 + ((3361 / 9348) : ℂ) * ζ ^ 6 - ((87585 / 34276) : ℂ) * ζ ^ 8 - ((139751 / 102828) : ℂ) * ζ ^ 12 - ((2851 / 4674) : ℂ) * ζ ^ 18 - ((1177 / 1558) : ℂ) * ζ ^ 22 + ((75965 / 34276) : ℂ) * ζ ^ 24 + ((87585 / 34276) : ℂ) * ζ ^ 28 - ((10181 / 9348) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((54383 / 102828) : ℂ) + ((6435 / 3116) : ℂ) * ζ ^ 2 + ((21665 / 9348) : ℂ) * ζ ^ 6 - ((73060 / 25707) : ℂ) * ζ ^ 8 - ((308831 / 102828) : ℂ) * ζ ^ 12 - ((649 / 492) : ℂ) * ζ ^ 18 - ((6435 / 3116) : ℂ) * ζ ^ 22 + ((53503 / 102828) : ℂ) * ζ ^ 24 + ((73060 / 25707) : ℂ) * ζ ^ 28 + ((15391 / 9348) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((24159 / 17138) : ℂ) + ((5023 / 51414) : ℂ) * ζ ^ 2 + ((34537 / 34276) : ℂ) * ζ ^ 6 + ((35185 / 34276) : ℂ) * ζ ^ 8 - ((20473 / 102828) : ℂ) * ζ ^ 12 + ((17273 / 102828) : ℂ) * ζ ^ 18 - ((5023 / 51414) : ℂ) * ζ ^ 22 - ((51382 / 25707) : ℂ) * ζ ^ 24 - ((35185 / 34276) : ℂ) * ζ ^ 28 + ((8687 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((36983 / 102828) : ℂ) - ((6494 / 8569) : ℂ) * ζ ^ 2 - ((33527 / 102828) : ℂ) * ζ ^ 6 + ((72579 / 34276) : ℂ) * ζ ^ 8 + ((139013 / 102828) : ℂ) * ζ ^ 12 + ((7501 / 25707) : ℂ) * ζ ^ 18 + ((6494 / 8569) : ℂ) * ζ ^ 22 - ((62927 / 34276) : ℂ) * ζ ^ 24 - ((72579 / 34276) : ℂ) * ζ ^ 28 + ((83701 / 102828) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((7817 / 51414) : ℂ) - ((2999 / 17138) : ℂ) * ζ ^ 2 - ((10937 / 51414) : ℂ) * ζ ^ 6 + ((2239 / 25707) : ℂ) * ζ ^ 8 - ((2671 / 51414) : ℂ) * ζ ^ 12 - ((140 / 451) : ℂ) * ζ ^ 18 + ((2999 / 17138) : ℂ) * ζ ^ 22 + ((1115 / 51414) : ℂ) * ζ ^ 24 - ((2239 / 25707) : ℂ) * ζ ^ 28 + ((2386 / 8569) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((3226 / 8569) : ℂ) - ((5525 / 17138) : ℂ) * ζ ^ 2 - ((2236 / 25707) : ℂ) * ζ ^ 6 + ((2678 / 25707) : ℂ) * ζ ^ 8 + ((538 / 25707) : ℂ) * ζ ^ 12 - ((12637 / 51414) : ℂ) * ζ ^ 18 + ((5525 / 17138) : ℂ) * ζ ^ 22 - ((25447 / 51414) : ℂ) * ζ ^ 24 - ((2678 / 25707) : ℂ) * ζ ^ 28 + ((5455 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((227 / 2706) : ℂ) - ((1559 / 2706) : ℂ) * ζ ^ 2 - ((494 / 1353) : ℂ) * ζ ^ 6 + ((523 / 1353) : ℂ) * ζ ^ 8 + ((485 / 1353) : ℂ) * ζ ^ 12 + ((529 / 902) : ℂ) * ζ ^ 18 + ((1559 / 2706) : ℂ) * ζ ^ 22 - ((592 / 1353) : ℂ) * ζ ^ 24 - ((523 / 1353) : ℂ) * ζ ^ 28 - ((523 / 902) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((-((23 / 2706) : ℂ) + ((80 / 451) : ℂ) * ζ ^ 2 + ((485 / 2706) : ℂ) * ζ ^ 6 + ((949 / 2706) : ℂ) * ζ ^ 8 + ((80 / 1353) : ℂ) * ζ ^ 12 + ((567 / 902) : ℂ) * ζ ^ 18 - ((80 / 451) : ℂ) * ζ ^ 22 - ((544 / 1353) : ℂ) * ζ ^ 24 - ((949 / 2706) : ℂ) * ζ ^ 28 - ((3 / 902) : ℂ) * ζ ^ 30)) * Y 3 3) = 0 := by
  have previous :=
    row17_reducedY44_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation03
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((1820 / 627) : ℂ) + ((614 / 627) : ℂ) * ζ ^ 2 - ((108 / 209) : ℂ) * ζ ^ 6 - ((346 / 209) : ℂ) * ζ ^ 8 - ((140 / 627) : ℂ) * ζ ^ 12 - ((200 / 627) : ℂ) * ζ ^ 18 - ((614 / 627) : ℂ) * ζ ^ 22 + ((842 / 627) : ℂ) * ζ ^ 24 + ((346 / 209) : ℂ) * ζ ^ 28 - ((40 / 209) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((11393 / 51414) : ℂ) - ((19649 / 51414) : ℂ) * ζ ^ 2 - ((22445 / 51414) : ℂ) * ζ ^ 4 + ((3824 / 25707) : ℂ) * ζ ^ 6 + ((6092 / 25707) : ℂ) * ζ ^ 8 + ((1325 / 17138) : ℂ) * ζ ^ 10 - ((6179 / 51414) : ℂ) * ζ ^ 12 - ((10163 / 51414) : ℂ) * ζ ^ 14 + ((3532 / 25707) : ℂ) * ζ ^ 16 + ((12575 / 51414) : ℂ) * ζ ^ 18 - ((208 / 8569) : ℂ) * ζ ^ 20 - ((476 / 25707) : ℂ) * ζ ^ 22 + ((4259 / 17138) : ℂ) * ζ ^ 24 + ((981 / 8569) : ℂ) * ζ ^ 26 - ((140 / 8569) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((9209 / 25707) : ℂ) + ((17735 / 51414) : ℂ) * ζ ^ 2 + ((21181 / 51414) : ℂ) * ζ ^ 4 - ((2773 / 51414) : ℂ) * ζ ^ 6 - ((27851 / 51414) : ℂ) * ζ ^ 8 + ((137 / 2337) : ℂ) * ζ ^ 10 + ((901 / 17138) : ℂ) * ζ ^ 12 + ((1214 / 25707) : ℂ) * ζ ^ 14 - ((1374 / 8569) : ℂ) * ζ ^ 16 - ((1391 / 51414) : ℂ) * ζ ^ 18 + ((4420 / 25707) : ℂ) * ζ ^ 20 + ((272 / 8569) : ℂ) * ζ ^ 22 - ((1624 / 8569) : ℂ) * ζ ^ 24 - ((1916 / 8569) : ℂ) * ζ ^ 26 + ((240 / 8569) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((6038 / 25707) : ℂ) - ((1967 / 17138) : ℂ) * ζ ^ 2 - ((9415 / 25707) : ℂ) * ζ ^ 4 + ((6209 / 51414) : ℂ) * ζ ^ 6 - ((3976 / 25707) : ℂ) * ζ ^ 8 - ((4001 / 51414) : ℂ) * ζ ^ 10 + ((229 / 8569) : ℂ) * ζ ^ 12 + ((389 / 17138) : ℂ) * ζ ^ 14 + ((3721 / 25707) : ℂ) * ζ ^ 16 + ((10 / 25707) : ℂ) * ζ ^ 18 - ((12475 / 51414) : ℂ) * ζ ^ 20 + ((1094 / 25707) : ℂ) * ζ ^ 22 + ((2635 / 8569) : ℂ) * ζ ^ 24 + ((46 / 8569) : ℂ) * ζ ^ 26 - ((40 / 8569) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((11393 / 51414) : ℂ) + ((19649 / 51414) : ℂ) * ζ ^ 2 + ((22445 / 51414) : ℂ) * ζ ^ 4 - ((3824 / 25707) : ℂ) * ζ ^ 6 - ((6092 / 25707) : ℂ) * ζ ^ 8 - ((1325 / 17138) : ℂ) * ζ ^ 10 + ((6179 / 51414) : ℂ) * ζ ^ 12 + ((10163 / 51414) : ℂ) * ζ ^ 14 - ((3532 / 25707) : ℂ) * ζ ^ 16 - ((12575 / 51414) : ℂ) * ζ ^ 18 + ((208 / 8569) : ℂ) * ζ ^ 20 + ((476 / 25707) : ℂ) * ζ ^ 22 - ((4259 / 17138) : ℂ) * ζ ^ 24 - ((981 / 8569) : ℂ) * ζ ^ 26 + ((140 / 8569) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY44_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((10 / 123) : ℂ) + ((16 / 41) : ℂ) * ζ ^ 2 + ((97 / 246) : ℂ) * ζ ^ 6 - ((17 / 123) : ℂ) * ζ ^ 8 + ((91 / 246) : ℂ) * ζ ^ 12 - ((119 / 246) : ℂ) * ζ ^ 18 - ((16 / 41) : ℂ) * ζ ^ 22 - ((53 / 246) : ℂ) * ζ ^ 24 + ((17 / 123) : ℂ) * ζ ^ 28 + ((359 / 246) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((24159 / 17138) : ℂ) + ((5023 / 51414) : ℂ) * ζ ^ 2 + ((34537 / 34276) : ℂ) * ζ ^ 6 + ((35185 / 34276) : ℂ) * ζ ^ 8 - ((20473 / 102828) : ℂ) * ζ ^ 12 + ((17273 / 102828) : ℂ) * ζ ^ 18 - ((5023 / 51414) : ℂ) * ζ ^ 22 - ((51382 / 25707) : ℂ) * ζ ^ 24 - ((35185 / 34276) : ℂ) * ζ ^ 28 + ((8687 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((36983 / 102828) : ℂ) - ((6494 / 8569) : ℂ) * ζ ^ 2 - ((33527 / 102828) : ℂ) * ζ ^ 6 + ((72579 / 34276) : ℂ) * ζ ^ 8 + ((139013 / 102828) : ℂ) * ζ ^ 12 + ((7501 / 25707) : ℂ) * ζ ^ 18 + ((6494 / 8569) : ℂ) * ζ ^ 22 - ((62927 / 34276) : ℂ) * ζ ^ 24 - ((72579 / 34276) : ℂ) * ζ ^ 28 + ((83701 / 102828) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((7817 / 51414) : ℂ) - ((2999 / 17138) : ℂ) * ζ ^ 2 - ((10937 / 51414) : ℂ) * ζ ^ 6 + ((2239 / 25707) : ℂ) * ζ ^ 8 - ((2671 / 51414) : ℂ) * ζ ^ 12 - ((140 / 451) : ℂ) * ζ ^ 18 + ((2999 / 17138) : ℂ) * ζ ^ 22 + ((1115 / 51414) : ℂ) * ζ ^ 24 - ((2239 / 25707) : ℂ) * ζ ^ 28 + ((2386 / 8569) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((3226 / 8569) : ℂ) - ((5525 / 17138) : ℂ) * ζ ^ 2 - ((2236 / 25707) : ℂ) * ζ ^ 6 + ((2678 / 25707) : ℂ) * ζ ^ 8 + ((538 / 25707) : ℂ) * ζ ^ 12 - ((12637 / 51414) : ℂ) * ζ ^ 18 + ((5525 / 17138) : ℂ) * ζ ^ 22 - ((25447 / 51414) : ℂ) * ζ ^ 24 - ((2678 / 25707) : ℂ) * ζ ^ 28 + ((5455 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((227 / 2706) : ℂ) - ((1559 / 2706) : ℂ) * ζ ^ 2 - ((494 / 1353) : ℂ) * ζ ^ 6 + ((523 / 1353) : ℂ) * ζ ^ 8 + ((485 / 1353) : ℂ) * ζ ^ 12 + ((529 / 902) : ℂ) * ζ ^ 18 + ((1559 / 2706) : ℂ) * ζ ^ 22 - ((592 / 1353) : ℂ) * ζ ^ 24 - ((523 / 1353) : ℂ) * ζ ^ 28 - ((523 / 902) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((-((23 / 2706) : ℂ) + ((80 / 451) : ℂ) * ζ ^ 2 + ((485 / 2706) : ℂ) * ζ ^ 6 + ((949 / 2706) : ℂ) * ζ ^ 8 + ((80 / 1353) : ℂ) * ζ ^ 12 + ((567 / 902) : ℂ) * ζ ^ 18 - ((80 / 451) : ℂ) * ζ ^ 22 - ((544 / 1353) : ℂ) * ζ ^ 24 - ((949 / 2706) : ℂ) * ζ ^ 28 - ((3 / 902) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((30537 / 34276) : ℂ) + ((636 / 779) : ℂ) * ζ ^ 2 - ((197 / 3116) : ℂ) * ζ ^ 6 - ((95109 / 34276) : ℂ) * ζ ^ 8 - ((35855 / 34276) : ℂ) * ζ ^ 12 - ((849 / 1558) : ℂ) * ζ ^ 18 - ((636 / 779) : ℂ) * ζ ^ 22 + ((69277 / 34276) : ℂ) * ζ ^ 24 + ((95109 / 34276) : ℂ) * ζ ^ 28 - ((1823 / 3116) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((30429 / 34276) : ℂ) + ((17245 / 17138) : ℂ) * ζ ^ 2 + ((31237 / 34276) : ℂ) * ζ ^ 6 - ((34251 / 34276) : ℂ) * ζ ^ 8 - ((34197 / 34276) : ℂ) * ζ ^ 12 - ((8351 / 17138) : ℂ) * ζ ^ 18 - ((17245 / 17138) : ℂ) * ζ ^ 22 - ((775 / 34276) : ℂ) * ζ ^ 24 + ((34251 / 34276) : ℂ) * ζ ^ 28 + ((713 / 1804) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY44_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((55540 / 25707) : ℂ) - ((755 / 8569) : ℂ) * ζ ^ 2 - ((16604 / 25707) : ℂ) * ζ ^ 6 - ((60029 / 25707) : ℂ) * ζ ^ 8 - ((8905 / 8569) : ℂ) * ζ ^ 12 - ((5327 / 25707) : ℂ) * ζ ^ 18 + ((755 / 8569) : ℂ) * ζ ^ 22 + ((65509 / 25707) : ℂ) * ζ ^ 24 + ((60029 / 25707) : ℂ) * ζ ^ 28 - ((29261 / 25707) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((108413 / 377036) : ℂ) + ((81486 / 94259) : ℂ) * ζ ^ 2 + ((108413 / 377036) : ℂ) * ζ ^ 4 - ((216949 / 377036) : ℂ) * ζ ^ 6 - ((140825 / 94259) : ℂ) * ζ ^ 8 + ((212419 / 377036) : ℂ) * ζ ^ 10 - ((57289 / 188518) : ℂ) * ζ ^ 12 + ((24043 / 94259) : ℂ) * ζ ^ 14 - ((1370 / 94259) : ℂ) * ζ ^ 16 - ((33791 / 377036) : ℂ) * ζ ^ 18 - ((191047 / 377036) : ℂ) * ζ ^ 20 + ((29261 / 377036) : ℂ) * ζ ^ 22 - ((60029 / 188518) : ℂ) * ζ ^ 24 + ((29261 / 188518) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((1335091 / 377036) : ℂ) + ((169766 / 94259) : ℂ) * ζ ^ 2 + ((1335091 / 377036) : ℂ) * ζ ^ 4 + ((394773 / 377036) : ℂ) * ζ ^ 6 - ((19329 / 188518) : ℂ) * ζ ^ 8 - ((109452 / 94259) : ℂ) * ζ ^ 10 - ((1118631 / 377036) : ℂ) * ζ ^ 12 + ((191289 / 94259) : ℂ) * ζ ^ 14 - ((5480 / 94259) : ℂ) * ζ ^ 16 - ((160079 / 377036) : ℂ) * ζ ^ 18 - ((1484787 / 377036) : ℂ) * ζ ^ 20 + ((29261 / 94259) : ℂ) * ζ ^ 22 - ((60029 / 19844) : ℂ) * ζ ^ 24 + ((29261 / 19844) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((108413 / 377036) : ℂ) - ((81486 / 94259) : ℂ) * ζ ^ 2 - ((108413 / 377036) : ℂ) * ζ ^ 4 + ((216949 / 377036) : ℂ) * ζ ^ 6 + ((140825 / 94259) : ℂ) * ζ ^ 8 - ((212419 / 377036) : ℂ) * ζ ^ 10 + ((57289 / 188518) : ℂ) * ζ ^ 12 - ((24043 / 94259) : ℂ) * ζ ^ 14 + ((1370 / 94259) : ℂ) * ζ ^ 16 + ((33791 / 377036) : ℂ) * ζ ^ 18 + ((191047 / 377036) : ℂ) * ζ ^ 20 - ((29261 / 377036) : ℂ) * ζ ^ 22 + ((60029 / 188518) : ℂ) * ζ ^ 24 - ((29261 / 188518) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((445799 / 377036) : ℂ) - ((95980 / 94259) : ℂ) * ζ ^ 2 - ((445799 / 377036) : ℂ) * ζ ^ 4 + ((7105 / 377036) : ℂ) * ζ ^ 6 + ((184631 / 188518) : ℂ) * ζ ^ 8 + ((6485 / 377036) : ℂ) * ζ ^ 10 + ((171867 / 188518) : ℂ) * ζ ^ 12 - ((72129 / 94259) : ℂ) * ζ ^ 14 + ((4110 / 94259) : ℂ) * ζ ^ 16 + ((101373 / 377036) : ℂ) * ζ ^ 18 + ((573141 / 377036) : ℂ) * ζ ^ 20 - ((87783 / 377036) : ℂ) * ζ ^ 22 + ((180087 / 188518) : ℂ) * ζ ^ 24 - ((87783 / 188518) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY44_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((24159 / 17138) : ℂ) + ((5023 / 51414) : ℂ) * ζ ^ 2 + ((34537 / 34276) : ℂ) * ζ ^ 6 + ((35185 / 34276) : ℂ) * ζ ^ 8 - ((20473 / 102828) : ℂ) * ζ ^ 12 + ((17273 / 102828) : ℂ) * ζ ^ 18 - ((5023 / 51414) : ℂ) * ζ ^ 22 - ((51382 / 25707) : ℂ) * ζ ^ 24 - ((35185 / 34276) : ℂ) * ζ ^ 28 + ((8687 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((36983 / 102828) : ℂ) - ((6494 / 8569) : ℂ) * ζ ^ 2 - ((33527 / 102828) : ℂ) * ζ ^ 6 + ((72579 / 34276) : ℂ) * ζ ^ 8 + ((139013 / 102828) : ℂ) * ζ ^ 12 + ((7501 / 25707) : ℂ) * ζ ^ 18 + ((6494 / 8569) : ℂ) * ζ ^ 22 - ((62927 / 34276) : ℂ) * ζ ^ 24 - ((72579 / 34276) : ℂ) * ζ ^ 28 + ((83701 / 102828) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((7817 / 51414) : ℂ) - ((2999 / 17138) : ℂ) * ζ ^ 2 - ((10937 / 51414) : ℂ) * ζ ^ 6 + ((2239 / 25707) : ℂ) * ζ ^ 8 - ((2671 / 51414) : ℂ) * ζ ^ 12 - ((140 / 451) : ℂ) * ζ ^ 18 + ((2999 / 17138) : ℂ) * ζ ^ 22 + ((1115 / 51414) : ℂ) * ζ ^ 24 - ((2239 / 25707) : ℂ) * ζ ^ 28 + ((2386 / 8569) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((3226 / 8569) : ℂ) - ((5525 / 17138) : ℂ) * ζ ^ 2 - ((2236 / 25707) : ℂ) * ζ ^ 6 + ((2678 / 25707) : ℂ) * ζ ^ 8 + ((538 / 25707) : ℂ) * ζ ^ 12 - ((12637 / 51414) : ℂ) * ζ ^ 18 + ((5525 / 17138) : ℂ) * ζ ^ 22 - ((25447 / 51414) : ℂ) * ζ ^ 24 - ((2678 / 25707) : ℂ) * ζ ^ 28 + ((5455 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((227 / 2706) : ℂ) - ((1559 / 2706) : ℂ) * ζ ^ 2 - ((494 / 1353) : ℂ) * ζ ^ 6 + ((523 / 1353) : ℂ) * ζ ^ 8 + ((485 / 1353) : ℂ) * ζ ^ 12 + ((529 / 902) : ℂ) * ζ ^ 18 + ((1559 / 2706) : ℂ) * ζ ^ 22 - ((592 / 1353) : ℂ) * ζ ^ 24 - ((523 / 1353) : ℂ) * ζ ^ 28 - ((523 / 902) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((-((23 / 2706) : ℂ) + ((80 / 451) : ℂ) * ζ ^ 2 + ((485 / 2706) : ℂ) * ζ ^ 6 + ((949 / 2706) : ℂ) * ζ ^ 8 + ((80 / 1353) : ℂ) * ζ ^ 12 + ((567 / 902) : ℂ) * ζ ^ 18 - ((80 / 451) : ℂ) * ζ ^ 22 - ((544 / 1353) : ℂ) * ζ ^ 24 - ((949 / 2706) : ℂ) * ζ ^ 28 - ((3 / 902) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((30537 / 34276) : ℂ) + ((636 / 779) : ℂ) * ζ ^ 2 - ((197 / 3116) : ℂ) * ζ ^ 6 - ((95109 / 34276) : ℂ) * ζ ^ 8 - ((35855 / 34276) : ℂ) * ζ ^ 12 - ((849 / 1558) : ℂ) * ζ ^ 18 - ((636 / 779) : ℂ) * ζ ^ 22 + ((69277 / 34276) : ℂ) * ζ ^ 24 + ((95109 / 34276) : ℂ) * ζ ^ 28 - ((1823 / 3116) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((30429 / 34276) : ℂ) + ((17245 / 17138) : ℂ) * ζ ^ 2 + ((31237 / 34276) : ℂ) * ζ ^ 6 - ((34251 / 34276) : ℂ) * ζ ^ 8 - ((34197 / 34276) : ℂ) * ζ ^ 12 - ((8351 / 17138) : ℂ) * ζ ^ 18 - ((17245 / 17138) : ℂ) * ζ ^ 22 - ((775 / 34276) : ℂ) * ζ ^ 24 + ((34251 / 34276) : ℂ) * ζ ^ 28 + ((713 / 1804) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY44_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) + (2 : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 + ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((179 / 246) : ℂ) - ((2 / 41) : ℂ) * ζ ^ 2 + ((7 / 6) : ℂ) * ζ ^ 4 + ((18 / 41) : ℂ) * ζ ^ 6 - ((62 / 123) : ℂ) * ζ ^ 8 - ((71 / 82) : ℂ) * ζ ^ 10 - ((73 / 246) : ℂ) * ζ ^ 12 + ((193 / 246) : ℂ) * ζ ^ 14 + ((34 / 41) : ℂ) * ζ ^ 16 - ((35 / 82) : ℂ) * ζ ^ 18 - ((94 / 123) : ℂ) * ζ ^ 20 + ((79 / 246) : ℂ) * ζ ^ 24 + ((13 / 41) : ℂ) * ζ ^ 26 - ((28 / 123) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((7 / 123) : ℂ) + ((1 / 82) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 4 + ((55 / 246) : ℂ) * ζ ^ 6 + ((31 / 246) : ℂ) * ζ ^ 8 + ((1 / 123) : ℂ) * ζ ^ 10 + ((49 / 246) : ℂ) * ζ ^ 12 - ((20 / 41) : ℂ) * ζ ^ 14 - ((46 / 123) : ℂ) * ζ ^ 16 + ((19 / 82) : ℂ) * ζ ^ 18 + ((44 / 123) : ℂ) * ζ ^ 20 - ((56 / 123) : ℂ) * ζ ^ 24 - ((20 / 123) : ℂ) * ζ ^ 26 + ((16 / 41) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((8 / 123) : ℂ) - ((103 / 246) : ℂ) * ζ ^ 2 + ((1 / 3) : ℂ) * ζ ^ 4 + ((63 / 82) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 - ((301 / 246) : ℂ) * ζ ^ 10 - ((23 / 41) : ℂ) * ζ ^ 12 + ((143 / 246) : ℂ) * ζ ^ 14 + ((39 / 41) : ℂ) * ζ ^ 16 + ((26 / 123) : ℂ) * ζ ^ 18 - ((55 / 82) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((23 / 123) : ℂ) * ζ ^ 24 + ((58 / 123) : ℂ) * ζ ^ 26 - ((8 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((179 / 246) : ℂ) + ((2 / 41) : ℂ) * ζ ^ 2 - ((7 / 6) : ℂ) * ζ ^ 4 - ((18 / 41) : ℂ) * ζ ^ 6 + ((62 / 123) : ℂ) * ζ ^ 8 + ((71 / 82) : ℂ) * ζ ^ 10 + ((73 / 246) : ℂ) * ζ ^ 12 - ((193 / 246) : ℂ) * ζ ^ 14 - ((34 / 41) : ℂ) * ζ ^ 16 + ((35 / 82) : ℂ) * ζ ^ 18 + ((94 / 123) : ℂ) * ζ ^ 20 - ((79 / 246) : ℂ) * ζ ^ 24 - ((13 / 41) : ℂ) * ζ ^ 26 + ((28 / 123) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY44_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((22145 / 17138) : ℂ) + ((36 / 8569) : ℂ) * ζ ^ 2 + ((116569 / 102828) : ℂ) * ζ ^ 6 + ((65959 / 102828) : ℂ) * ζ ^ 8 - ((7027 / 34276) : ℂ) * ζ ^ 12 + ((13003 / 34276) : ℂ) * ζ ^ 18 - ((36 / 8569) : ℂ) * ζ ^ 22 - ((98983 / 51414) : ℂ) * ζ ^ 24 - ((65959 / 102828) : ℂ) * ζ ^ 28 + ((5343 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((64153 / 102828) : ℂ) - ((10575 / 17138) : ℂ) * ζ ^ 2 - ((15761 / 34276) : ℂ) * ζ ^ 6 + ((265807 / 102828) : ℂ) * ζ ^ 8 + ((31847 / 34276) : ℂ) * ζ ^ 12 - ((479 / 25707) : ℂ) * ζ ^ 18 + ((10575 / 17138) : ℂ) * ζ ^ 22 - ((222221 / 102828) : ℂ) * ζ ^ 24 - ((265807 / 102828) : ℂ) * ζ ^ 28 + ((93391 / 102828) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((87 / 209) : ℂ) - ((6 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 - ((159 / 418) : ℂ) * ζ ^ 8 + ((155 / 418) : ℂ) * ζ ^ 12 + ((6 / 19) : ℂ) * ζ ^ 22 + ((145 / 418) : ℂ) * ζ ^ 24 + ((159 / 418) : ℂ) * ζ ^ 28 + ((7 / 38) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((3226 / 8569) : ℂ) - ((5525 / 17138) : ℂ) * ζ ^ 2 - ((2236 / 25707) : ℂ) * ζ ^ 6 + ((2678 / 25707) : ℂ) * ζ ^ 8 + ((538 / 25707) : ℂ) * ζ ^ 12 - ((12637 / 51414) : ℂ) * ζ ^ 18 + ((5525 / 17138) : ℂ) * ζ ^ 22 - ((25447 / 51414) : ℂ) * ζ ^ 24 - ((2678 / 25707) : ℂ) * ζ ^ 28 + ((5455 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((23 / 2706) : ℂ) + ((80 / 451) : ℂ) * ζ ^ 2 + ((485 / 2706) : ℂ) * ζ ^ 6 + ((949 / 2706) : ℂ) * ζ ^ 8 + ((80 / 1353) : ℂ) * ζ ^ 12 + ((567 / 902) : ℂ) * ζ ^ 18 - ((80 / 451) : ℂ) * ζ ^ 22 - ((544 / 1353) : ℂ) * ζ ^ 24 - ((949 / 2706) : ℂ) * ζ ^ 28 - ((3 / 902) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((30537 / 34276) : ℂ) + ((636 / 779) : ℂ) * ζ ^ 2 - ((197 / 3116) : ℂ) * ζ ^ 6 - ((95109 / 34276) : ℂ) * ζ ^ 8 - ((35855 / 34276) : ℂ) * ζ ^ 12 - ((849 / 1558) : ℂ) * ζ ^ 18 - ((636 / 779) : ℂ) * ζ ^ 22 + ((69277 / 34276) : ℂ) * ζ ^ 24 + ((95109 / 34276) : ℂ) * ζ ^ 28 - ((1823 / 3116) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((30429 / 34276) : ℂ) + ((17245 / 17138) : ℂ) * ζ ^ 2 + ((31237 / 34276) : ℂ) * ζ ^ 6 - ((34251 / 34276) : ℂ) * ζ ^ 8 - ((34197 / 34276) : ℂ) * ζ ^ 12 - ((8351 / 17138) : ℂ) * ζ ^ 18 - ((17245 / 17138) : ℂ) * ζ ^ 22 - ((775 / 34276) : ℂ) * ζ ^ 24 + ((34251 / 34276) : ℂ) * ζ ^ 28 + ((713 / 1804) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY44_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation12
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((20 / 33) : ℂ) + ((50 / 33) : ℂ) * ζ ^ 2 + ((4 / 33) : ℂ) * ζ ^ 6 - ((38 / 33) : ℂ) * ζ ^ 8 - ((32 / 33) : ℂ) * ζ ^ 12 - ((16 / 33) : ℂ) * ζ ^ 18 - ((50 / 33) : ℂ) * ζ ^ 22 + ((46 / 33) : ℂ) * ζ ^ 24 + ((38 / 33) : ℂ) * ζ ^ 28 + ((10 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((119 / 1353) : ℂ) + ((673 / 2706) : ℂ) * ζ ^ 2 + ((394 / 1353) : ℂ) * ζ ^ 4 - ((469 / 1353) : ℂ) * ζ ^ 6 + ((298 / 1353) : ℂ) * ζ ^ 8 + ((635 / 1353) : ℂ) * ζ ^ 10 - ((362 / 1353) : ℂ) * ζ ^ 12 - ((239 / 1353) : ℂ) * ζ ^ 14 + ((32 / 123) : ℂ) * ζ ^ 16 - ((9 / 82) : ℂ) * ζ ^ 18 - ((163 / 2706) : ℂ) * ζ ^ 20 + ((629 / 2706) : ℂ) * ζ ^ 22 - ((85 / 451) : ℂ) * ζ ^ 24 - ((263 / 1353) : ℂ) * ζ ^ 26 - ((10 / 451) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((695 / 2706) : ℂ) - ((1511 / 2706) : ℂ) * ζ ^ 2 - ((3395 / 2706) : ℂ) * ζ ^ 4 + ((413 / 902) : ℂ) * ζ ^ 6 - ((241 / 902) : ℂ) * ζ ^ 8 - ((1937 / 2706) : ℂ) * ζ ^ 10 + ((283 / 451) : ℂ) * ζ ^ 12 + ((201 / 451) : ℂ) * ζ ^ 14 - ((1154 / 1353) : ℂ) * ζ ^ 16 + ((196 / 1353) : ℂ) * ζ ^ 18 + ((562 / 451) : ℂ) * ζ ^ 20 - ((545 / 1353) : ℂ) * ζ ^ 22 + ((1345 / 1353) : ℂ) * ζ ^ 24 + ((445 / 1353) : ℂ) * ζ ^ 26 - ((100 / 451) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((695 / 2706) : ℂ) + ((1511 / 2706) : ℂ) * ζ ^ 2 + ((3395 / 2706) : ℂ) * ζ ^ 4 - ((413 / 902) : ℂ) * ζ ^ 6 + ((241 / 902) : ℂ) * ζ ^ 8 + ((1937 / 2706) : ℂ) * ζ ^ 10 - ((283 / 451) : ℂ) * ζ ^ 12 - ((201 / 451) : ℂ) * ζ ^ 14 + ((1154 / 1353) : ℂ) * ζ ^ 16 - ((196 / 1353) : ℂ) * ζ ^ 18 - ((562 / 451) : ℂ) * ζ ^ 20 + ((545 / 1353) : ℂ) * ζ ^ 22 - ((1345 / 1353) : ℂ) * ζ ^ 24 - ((445 / 1353) : ℂ) * ζ ^ 26 + ((100 / 451) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((((189 / 902) : ℂ) - ((799 / 2706) : ℂ) * ζ ^ 2 - ((12 / 41) : ℂ) * ζ ^ 4 - ((71 / 2706) : ℂ) * ζ ^ 6 + ((1139 / 2706) : ℂ) * ζ ^ 8 - ((79 / 1353) : ℂ) * ζ ^ 10 + ((122 / 1353) : ℂ) * ζ ^ 12 + ((163 / 1353) : ℂ) * ζ ^ 14 - ((5 / 82) : ℂ) * ζ ^ 16 - ((145 / 2706) : ℂ) * ζ ^ 18 + ((35 / 2706) : ℂ) * ζ ^ 20 - ((14 / 451) : ℂ) * ζ ^ 22 - ((28 / 1353) : ℂ) * ζ ^ 24 + ((116 / 451) : ℂ) * ζ ^ 26 + ((60 / 451) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY44_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((24159 / 17138) : ℂ) + ((547 / 2337) : ℂ) * ζ ^ 2 + ((3423 / 3116) : ℂ) * ζ ^ 6 + ((35185 / 34276) : ℂ) * ζ ^ 8 - ((20473 / 102828) : ℂ) * ζ ^ 12 - ((1829 / 9348) : ℂ) * ζ ^ 18 - ((547 / 2337) : ℂ) * ζ ^ 22 - ((51382 / 25707) : ℂ) * ζ ^ 24 - ((35185 / 34276) : ℂ) * ζ ^ 28 + ((147 / 779) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((65027 / 102828) : ℂ) - ((685 / 1558) : ℂ) * ζ ^ 2 - ((2623 / 9348) : ℂ) * ζ ^ 6 + ((100623 / 34276) : ℂ) * ζ ^ 8 + ((101621 / 102828) : ℂ) * ζ ^ 12 + ((2851 / 4674) : ℂ) * ζ ^ 18 + ((685 / 1558) : ℂ) * ζ ^ 22 - ((87855 / 34276) : ℂ) * ζ ^ 24 - ((100623 / 34276) : ℂ) * ζ ^ 28 + ((8459 / 9348) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((87 / 209) : ℂ) - ((6 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 - ((159 / 418) : ℂ) * ζ ^ 8 + ((155 / 418) : ℂ) * ζ ^ 12 + ((6 / 19) : ℂ) * ζ ^ 22 + ((145 / 418) : ℂ) * ζ ^ 24 + ((159 / 418) : ℂ) * ζ ^ 28 + ((7 / 38) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((14 / 209) : ℂ) - ((575 / 418) : ℂ) * ζ ^ 2 - ((233 / 418) : ℂ) * ζ ^ 6 - ((207 / 209) : ℂ) * ζ ^ 8 + ((26 / 209) : ℂ) * ζ ^ 12 + ((327 / 418) : ℂ) * ζ ^ 18 + ((575 / 418) : ℂ) * ζ ^ 22 + ((335 / 418) : ℂ) * ζ ^ 24 + ((207 / 209) : ℂ) * ζ ^ 28 + ((205 / 418) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((30537 / 34276) : ℂ) + ((636 / 779) : ℂ) * ζ ^ 2 - ((197 / 3116) : ℂ) * ζ ^ 6 - ((95109 / 34276) : ℂ) * ζ ^ 8 - ((35855 / 34276) : ℂ) * ζ ^ 12 - ((849 / 1558) : ℂ) * ζ ^ 18 - ((636 / 779) : ℂ) * ζ ^ 22 + ((69277 / 34276) : ℂ) * ζ ^ 24 + ((95109 / 34276) : ℂ) * ζ ^ 28 - ((1823 / 3116) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((30429 / 34276) : ℂ) + ((17245 / 17138) : ℂ) * ζ ^ 2 + ((31237 / 34276) : ℂ) * ζ ^ 6 - ((34251 / 34276) : ℂ) * ζ ^ 8 - ((34197 / 34276) : ℂ) * ζ ^ 12 - ((8351 / 17138) : ℂ) * ζ ^ 18 - ((17245 / 17138) : ℂ) * ζ ^ 22 - ((775 / 34276) : ℂ) * ζ ^ 24 + ((34251 / 34276) : ℂ) * ζ ^ 28 + ((713 / 1804) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY44_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation13
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((46 / 33) : ℂ) - ((10 / 33) : ℂ) * ζ ^ 2 - ((12 / 11) : ℂ) * ζ ^ 6 - ((50 / 33) : ℂ) * ζ ^ 8 - ((4 / 11) : ℂ) * ζ ^ 12 - ((10 / 33) : ℂ) * ζ ^ 18 + ((10 / 33) : ℂ) * ζ ^ 22 + ((14 / 11) : ℂ) * ζ ^ 24 + ((50 / 33) : ℂ) * ζ ^ 28 + ((16 / 33) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((617 / 2706) : ℂ) - ((505 / 902) : ℂ) * ζ ^ 2 - ((437 / 2706) : ℂ) * ζ ^ 4 + ((893 / 2706) : ℂ) * ζ ^ 6 - ((353 / 1353) : ℂ) * ζ ^ 8 + ((61 / 1353) : ℂ) * ζ ^ 10 + ((121 / 246) : ℂ) * ζ ^ 12 - ((211 / 1353) : ℂ) * ζ ^ 14 - ((96 / 451) : ℂ) * ζ ^ 16 + ((1127 / 2706) : ℂ) * ζ ^ 18 + ((389 / 1353) : ℂ) * ζ ^ 20 - ((56 / 1353) : ℂ) * ζ ^ 22 + ((463 / 2706) : ℂ) * ζ ^ 24 + ((89 / 451) : ℂ) * ζ ^ 26 + ((56 / 1353) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((23 / 82) : ℂ) - ((103 / 2706) : ℂ) * ζ ^ 2 + ((119 / 451) : ℂ) * ζ ^ 4 + ((115 / 2706) : ℂ) * ζ ^ 6 - ((97 / 451) : ℂ) * ζ ^ 8 - ((70 / 451) : ℂ) * ζ ^ 10 - ((917 / 2706) : ℂ) * ζ ^ 12 + ((145 / 1353) : ℂ) * ζ ^ 14 + ((236 / 1353) : ℂ) * ζ ^ 16 - ((497 / 2706) : ℂ) * ζ ^ 18 - ((70 / 451) : ℂ) * ζ ^ 20 + ((32 / 451) : ℂ) * ζ ^ 22 - ((104 / 1353) : ℂ) * ζ ^ 24 - ((364 / 1353) : ℂ) * ζ ^ 26 - ((32 / 451) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((577 / 1353) : ℂ) + ((242 / 123) : ℂ) * ζ ^ 2 + ((307 / 1353) : ℂ) * ζ ^ 4 - ((1319 / 1353) : ℂ) * ζ ^ 6 + ((2569 / 2706) : ℂ) * ζ ^ 8 - ((102 / 451) : ℂ) * ζ ^ 10 - ((563 / 451) : ℂ) * ζ ^ 12 + ((674 / 1353) : ℂ) * ζ ^ 14 + ((4 / 123) : ℂ) * ζ ^ 16 - ((163 / 123) : ℂ) * ζ ^ 18 - ((184 / 451) : ℂ) * ζ ^ 20 + ((56 / 451) : ℂ) * ζ ^ 22 - ((1535 / 1353) : ℂ) * ζ ^ 24 + ((20 / 451) : ℂ) * ζ ^ 26 + ((160 / 1353) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((((23 / 82) : ℂ) + ((103 / 2706) : ℂ) * ζ ^ 2 - ((119 / 451) : ℂ) * ζ ^ 4 - ((115 / 2706) : ℂ) * ζ ^ 6 + ((97 / 451) : ℂ) * ζ ^ 8 + ((70 / 451) : ℂ) * ζ ^ 10 + ((917 / 2706) : ℂ) * ζ ^ 12 - ((145 / 1353) : ℂ) * ζ ^ 14 - ((236 / 1353) : ℂ) * ζ ^ 16 + ((497 / 2706) : ℂ) * ζ ^ 18 + ((70 / 451) : ℂ) * ζ ^ 20 - ((32 / 451) : ℂ) * ζ ^ 22 + ((104 / 1353) : ℂ) * ζ ^ 24 + ((364 / 1353) : ℂ) * ζ ^ 26 + ((32 / 451) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY44_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((43 / 82) : ℂ) * ζ ^ 6 + ((31 / 82) : ℂ) * ζ ^ 8 + ((10 / 123) : ℂ) * ζ ^ 12 - ((32 / 123) : ℂ) * ζ ^ 18 + ((19 / 246) : ℂ) * ζ ^ 22 - ((13 / 246) : ℂ) * ζ ^ 24 - ((31 / 82) : ℂ) * ζ ^ 28 - ((15 / 82) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((87 / 209) : ℂ) - ((6 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 - ((159 / 418) : ℂ) * ζ ^ 8 + ((155 / 418) : ℂ) * ζ ^ 12 + ((6 / 19) : ℂ) * ζ ^ 22 + ((145 / 418) : ℂ) * ζ ^ 24 + ((159 / 418) : ℂ) * ζ ^ 28 + ((7 / 38) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((14 / 209) : ℂ) - ((575 / 418) : ℂ) * ζ ^ 2 - ((233 / 418) : ℂ) * ζ ^ 6 - ((207 / 209) : ℂ) * ζ ^ 8 + ((26 / 209) : ℂ) * ζ ^ 12 + ((327 / 418) : ℂ) * ζ ^ 18 + ((575 / 418) : ℂ) * ζ ^ 22 + ((335 / 418) : ℂ) * ζ ^ 24 + ((207 / 209) : ℂ) * ζ ^ 28 + ((205 / 418) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((122 / 209) : ℂ) + ((6 / 19) : ℂ) * ζ ^ 2 + ((3 / 38) : ℂ) * ζ ^ 6 + ((159 / 418) : ℂ) * ζ ^ 8 - ((155 / 418) : ℂ) * ζ ^ 12 - ((6 / 19) : ℂ) * ζ ^ 22 - ((145 / 418) : ℂ) * ζ ^ 24 - ((159 / 418) : ℂ) * ζ ^ 28 - ((7 / 38) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((14 / 209) : ℂ) + ((5 / 19) : ℂ) * ζ ^ 2 + ((11 / 38) : ℂ) * ζ ^ 6 + ((103 / 418) : ℂ) * ζ ^ 8 + ((239 / 418) : ℂ) * ζ ^ 12 - ((2 / 19) : ℂ) * ζ ^ 18 - ((5 / 19) : ℂ) * ζ ^ 22 - ((61 / 418) : ℂ) * ζ ^ 24 - ((103 / 418) : ℂ) * ζ ^ 28 + ((9 / 38) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY44_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((11129 / 25707) : ℂ) + ((13313 / 25707) : ℂ) * ζ ^ 2 + ((15737 / 25707) : ℂ) * ζ ^ 6 - ((14438 / 25707) : ℂ) * ζ ^ 8 - ((12613 / 8569) : ℂ) * ζ ^ 12 - ((3793 / 25707) : ℂ) * ζ ^ 18 - ((13313 / 25707) : ℂ) * ζ ^ 22 - ((19535 / 25707) : ℂ) * ζ ^ 24 + ((14438 / 25707) : ℂ) * ζ ^ 28 + ((6223 / 25707) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((152263 / 188518) : ℂ) + ((5433 / 188518) : ℂ) * ζ ^ 2 + ((152263 / 188518) : ℂ) * ζ ^ 4 + ((79707 / 377036) : ℂ) * ζ ^ 6 + ((33217 / 377036) : ℂ) * ζ ^ 8 - ((53081 / 377036) : ℂ) * ζ ^ 10 - ((62849 / 377036) : ℂ) * ζ ^ 12 + ((1115 / 188518) : ℂ) * ζ ^ 14 + ((33973 / 377036) : ℂ) * ζ ^ 16 + ((32849 / 377036) : ℂ) * ζ ^ 18 + ((6158 / 94259) : ℂ) * ζ ^ 20 - ((6223 / 377036) : ℂ) * ζ ^ 22 - ((7219 / 94259) : ℂ) * ζ ^ 24 - ((6223 / 188518) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((58945 / 188518) : ℂ) - ((468333 / 377036) : ℂ) * ζ ^ 2 - ((58945 / 188518) : ℂ) * ζ ^ 4 + ((191459 / 377036) : ℂ) * ζ ^ 6 + ((699627 / 188518) : ℂ) * ζ ^ 8 + ((15372 / 94259) : ℂ) * ζ ^ 10 - ((205107 / 188518) : ℂ) * ζ ^ 12 - ((8905 / 188518) : ℂ) * ζ ^ 14 + ((33973 / 94259) : ℂ) * ζ ^ 16 + ((277839 / 377036) : ℂ) * ζ ^ 18 + ((313413 / 377036) : ℂ) * ζ ^ 20 - ((6223 / 94259) : ℂ) * ζ ^ 22 - ((7219 / 9922) : ℂ) * ζ ^ 24 - ((6223 / 19844) : ℂ) * ζ ^ 26)) * Y 1 1
        + ((-((58945 / 188518) : ℂ) + ((468333 / 377036) : ℂ) * ζ ^ 2 + ((58945 / 188518) : ℂ) * ζ ^ 4 - ((191459 / 377036) : ℂ) * ζ ^ 6 - ((699627 / 188518) : ℂ) * ζ ^ 8 - ((15372 / 94259) : ℂ) * ζ ^ 10 + ((205107 / 188518) : ℂ) * ζ ^ 12 + ((8905 / 188518) : ℂ) * ζ ^ 14 - ((33973 / 94259) : ℂ) * ζ ^ 16 - ((277839 / 377036) : ℂ) * ζ ^ 18 - ((313413 / 377036) : ℂ) * ζ ^ 20 + ((6223 / 94259) : ℂ) * ζ ^ 22 + ((7219 / 9922) : ℂ) * ζ ^ 24 + ((6223 / 19844) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((81647 / 94259) : ℂ) + ((240231 / 377036) : ℂ) * ζ ^ 2 + ((81647 / 94259) : ℂ) * ζ ^ 4 - ((52977 / 377036) : ℂ) * ζ ^ 6 - ((152066 / 94259) : ℂ) * ζ ^ 8 - ((30023 / 94259) : ℂ) * ζ ^ 10 - ((38009 / 94259) : ℂ) * ζ ^ 12 + ((51245 / 188518) : ℂ) * ζ ^ 14 + ((169865 / 188518) : ℂ) * ζ ^ 16 - ((110839 / 377036) : ℂ) * ζ ^ 18 - ((20965 / 19844) : ℂ) * ζ ^ 20 - ((31115 / 188518) : ℂ) * ζ ^ 22 + ((93847 / 188518) : ℂ) * ζ ^ 24 + ((80899 / 377036) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY44_combinationStep09
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((87 / 209) : ℂ) - ((6 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 - ((159 / 418) : ℂ) * ζ ^ 8 + ((155 / 418) : ℂ) * ζ ^ 12 + ((6 / 19) : ℂ) * ζ ^ 22 + ((145 / 418) : ℂ) * ζ ^ 24 + ((159 / 418) : ℂ) * ζ ^ 28 + ((7 / 38) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((14 / 209) : ℂ) - ((575 / 418) : ℂ) * ζ ^ 2 - ((233 / 418) : ℂ) * ζ ^ 6 - ((207 / 209) : ℂ) * ζ ^ 8 + ((26 / 209) : ℂ) * ζ ^ 12 + ((327 / 418) : ℂ) * ζ ^ 18 + ((575 / 418) : ℂ) * ζ ^ 22 + ((335 / 418) : ℂ) * ζ ^ 24 + ((207 / 209) : ℂ) * ζ ^ 28 + ((205 / 418) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((122 / 209) : ℂ) + ((6 / 19) : ℂ) * ζ ^ 2 + ((3 / 38) : ℂ) * ζ ^ 6 + ((159 / 418) : ℂ) * ζ ^ 8 - ((155 / 418) : ℂ) * ζ ^ 12 - ((6 / 19) : ℂ) * ζ ^ 22 - ((145 / 418) : ℂ) * ζ ^ 24 - ((159 / 418) : ℂ) * ζ ^ 28 - ((7 / 38) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((14 / 209) : ℂ) + ((5 / 19) : ℂ) * ζ ^ 2 + ((11 / 38) : ℂ) * ζ ^ 6 + ((103 / 418) : ℂ) * ζ ^ 8 + ((239 / 418) : ℂ) * ζ ^ 12 - ((2 / 19) : ℂ) * ζ ^ 18 - ((5 / 19) : ℂ) * ζ ^ 22 - ((61 / 418) : ℂ) * ζ ^ 24 - ((103 / 418) : ℂ) * ζ ^ 28 + ((9 / 38) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY44_combinationStep08 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((15 / 41) : ℂ) * ζ ^ 4 + ((45 / 82) : ℂ) * ζ ^ 6 - ((59 / 246) : ℂ) * ζ ^ 8 - ((69 / 82) : ℂ) * ζ ^ 10 - ((19 / 246) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ((65 / 246) : ℂ) * ζ ^ 16 - ((107 / 246) : ℂ) * ζ ^ 18 - ((29 / 82) : ℂ) * ζ ^ 20 + ((35 / 246) : ℂ) * ζ ^ 22 + ((10 / 41) : ℂ) * ζ ^ 24 - ((5 / 246) : ℂ) * ζ ^ 26 - ((7 / 123) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 + ((40 / 123) : ℂ) * ζ ^ 4 - ((85 / 246) : ℂ) * ζ ^ 6 - ((19 / 82) : ℂ) * ζ ^ 8 + ((103 / 246) : ℂ) * ζ ^ 10 + ((5 / 82) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ((47 / 246) : ℂ) * ζ ^ 16 + ((13 / 41) : ℂ) * ζ ^ 18 + ((73 / 246) : ℂ) * ζ ^ 20 - ((10 / 41) : ℂ) * ζ ^ 22 - ((28 / 123) : ℂ) * ζ ^ 24 + ((16 / 123) : ℂ) * ζ ^ 26 + ((4 / 41) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((4 / 41) : ℂ) * ζ ^ 4 - ((53 / 82) : ℂ) * ζ ^ 6 + ((68 / 123) : ℂ) * ζ ^ 8 + ((125 / 82) : ℂ) * ζ ^ 10 + ((49 / 123) : ℂ) * ζ ^ 12 - ((5 / 3) : ℂ) * ζ ^ 14 - ((53 / 41) : ℂ) * ζ ^ 16 + ((17 / 123) : ℂ) * ζ ^ 18 + ((151 / 123) : ℂ) * ζ ^ 20 + ((91 / 123) : ℂ) * ζ ^ 22 - ((30 / 41) : ℂ) * ζ ^ 24 - ((95 / 123) : ℂ) * ζ ^ 26 - ((20 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 - ((40 / 123) : ℂ) * ζ ^ 4 + ((85 / 246) : ℂ) * ζ ^ 6 + ((19 / 82) : ℂ) * ζ ^ 8 - ((103 / 246) : ℂ) * ζ ^ 10 - ((5 / 82) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((47 / 246) : ℂ) * ζ ^ 16 - ((13 / 41) : ℂ) * ζ ^ 18 - ((73 / 246) : ℂ) * ζ ^ 20 + ((10 / 41) : ℂ) * ζ ^ 22 + ((28 / 123) : ℂ) * ζ ^ 24 - ((16 / 123) : ℂ) * ζ ^ 26 - ((4 / 41) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY44_combinationStep10
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 4 4
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY44_combinationStep09 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation24
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((26 / 19) : ℂ) + ((14 / 19) : ℂ) * ζ ^ 2 + ((44 / 19) : ℂ) * ζ ^ 6 - ((14 / 19) : ℂ) * ζ ^ 8 + ((10 / 19) : ℂ) * ζ ^ 12 + ((10 / 19) : ℂ) * ζ ^ 18 - ((14 / 19) : ℂ) * ζ ^ 22 + ((44 / 19) : ℂ) * ζ ^ 24 + ((14 / 19) : ℂ) * ζ ^ 28 + ((26 / 19) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((100 / 209) : ℂ) - ((85 / 209) : ℂ) * ζ ^ 2 - ((6 / 11) : ℂ) * ζ ^ 4 + ((51 / 418) : ℂ) * ζ ^ 6 - ((162 / 209) : ℂ) * ζ ^ 8 - ((71 / 209) : ℂ) * ζ ^ 10 + ((371 / 209) : ℂ) * ζ ^ 12 - ((205 / 418) : ℂ) * ζ ^ 14 - ((651 / 418) : ℂ) * ζ ^ 16 + ((599 / 418) : ℂ) * ζ ^ 18 + ((48 / 209) : ℂ) * ζ ^ 20 - ((345 / 209) : ℂ) * ζ ^ 22 + ((379 / 418) : ℂ) * ζ ^ 24 + ((81 / 418) : ℂ) * ζ ^ 26 - ((130 / 209) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((103 / 209) : ℂ) - ((59 / 38) : ℂ) * ζ ^ 2 + ((117 / 209) : ℂ) * ζ ^ 4 - ((279 / 418) : ℂ) * ζ ^ 6 - ((465 / 418) : ℂ) * ζ ^ 8 + ((321 / 418) : ℂ) * ζ ^ 10 + ((59 / 209) : ℂ) * ζ ^ 12 - ((16 / 19) : ℂ) * ζ ^ 14 - ((80 / 209) : ℂ) * ζ ^ 16 + ((140 / 209) : ℂ) * ζ ^ 18 - ((18 / 19) : ℂ) * ζ ^ 20 - ((119 / 209) : ℂ) * ζ ^ 22 - ((2 / 19) : ℂ) * ζ ^ 24 - ((72 / 209) : ℂ) * ζ ^ 26 - ((13 / 209) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((100 / 209) : ℂ) + ((85 / 209) : ℂ) * ζ ^ 2 + ((6 / 11) : ℂ) * ζ ^ 4 - ((51 / 418) : ℂ) * ζ ^ 6 + ((162 / 209) : ℂ) * ζ ^ 8 + ((71 / 209) : ℂ) * ζ ^ 10 - ((371 / 209) : ℂ) * ζ ^ 12 + ((205 / 418) : ℂ) * ζ ^ 14 + ((651 / 418) : ℂ) * ζ ^ 16 - ((599 / 418) : ℂ) * ζ ^ 18 - ((48 / 209) : ℂ) * ζ ^ 20 + ((345 / 209) : ℂ) * ζ ^ 22 - ((379 / 418) : ℂ) * ζ ^ 24 - ((81 / 418) : ℂ) * ζ ^ 26 + ((130 / 209) : ℂ) * ζ ^ 28)) * Y 4 4
        + ((-((25 / 209) : ℂ) + ((81 / 418) : ℂ) * ζ ^ 2 + ((3 / 22) : ℂ) * ζ ^ 4 - ((137 / 209) : ℂ) * ζ ^ 6 - ((20 / 209) : ℂ) * ζ ^ 8 + ((239 / 418) : ℂ) * ζ ^ 10 + ((73 / 418) : ℂ) * ζ ^ 12 - ((45 / 418) : ℂ) * ζ ^ 14 - ((1 / 11) : ℂ) * ζ ^ 16 + ((86 / 209) : ℂ) * ζ ^ 18 - ((12 / 209) : ℂ) * ζ ^ 20 - ((207 / 418) : ℂ) * ζ ^ 22 + ((53 / 209) : ℂ) * ζ ^ 24 + ((5 / 209) : ℂ) * ζ ^ 26 - ((39 / 209) : ℂ) * ζ ^ 28)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY44
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 4 4 = Y 7 7 := by
  have reduced :=
    row17_reducedY44_combinationStep10 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row17_reducedY45_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((1377 / 836) : ℂ) + ((1043 / 418) : ℂ) * ζ ^ 2 + ((168 / 209) : ℂ) * ζ ^ 6 - ((1763 / 418) : ℂ) * ζ ^ 8 - ((749 / 836) : ℂ) * ζ ^ 12 - ((562 / 209) : ℂ) * ζ ^ 18 - ((1043 / 418) : ℂ) * ζ ^ 22 + ((4233 / 836) : ℂ) * ζ ^ 24 + ((1763 / 418) : ℂ) * ζ ^ 28 - ((170 / 209) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((93 / 836) : ℂ) - ((479 / 418) : ℂ) * ζ ^ 2 - ((367 / 418) : ℂ) * ζ ^ 6 + ((1335 / 836) : ℂ) * ζ ^ 8 + ((921 / 836) : ℂ) * ζ ^ 12 + ((85 / 209) : ℂ) * ζ ^ 18 + ((479 / 418) : ℂ) * ζ ^ 22 - ((721 / 836) : ℂ) * ζ ^ 24 - ((1335 / 836) : ℂ) * ζ ^ 28 - ((85 / 418) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((((828 / 209) : ℂ) - ((1128 / 209) : ℂ) * ζ ^ 2 - ((1522 / 209) : ℂ) * ζ ^ 6 + ((1135 / 209) : ℂ) * ζ ^ 8 + ((1335 / 209) : ℂ) * ζ ^ 12 + ((170 / 209) : ℂ) * ζ ^ 18 + ((1128 / 209) : ℂ) * ζ ^ 22 + ((107 / 209) : ℂ) * ζ ^ 24 - ((1135 / 209) : ℂ) * ζ ^ 28 - ((734 / 209) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((549 / 836) : ℂ) - ((1607 / 418) : ℂ) * ζ ^ 2 + ((549 / 836) : ℂ) * ζ ^ 4 + ((255 / 209) : ℂ) * ζ ^ 6 + ((37 / 19) : ℂ) * ζ ^ 8 + ((591 / 209) : ℂ) * ζ ^ 10 + ((1563 / 836) : ℂ) * ζ ^ 12 - ((43 / 11) : ℂ) * ζ ^ 14 - ((1242 / 209) : ℂ) * ζ ^ 16 + ((112 / 209) : ℂ) * ζ ^ 18 + ((4861 / 836) : ℂ) * ζ ^ 20 + ((734 / 209) : ℂ) * ζ ^ 22 - ((3405 / 836) : ℂ) * ζ ^ 24 - ((1101 / 418) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((93 / 836) : ℂ) + ((479 / 418) : ℂ) * ζ ^ 2 - ((93 / 836) : ℂ) * ζ ^ 4 - ((56 / 209) : ℂ) * ζ ^ 6 - ((621 / 418) : ℂ) * ζ ^ 8 + ((56 / 209) : ℂ) * ζ ^ 10 + ((621 / 418) : ℂ) * ζ ^ 12 - ((197 / 418) : ℂ) * ζ ^ 14 - ((621 / 418) : ℂ) * ζ ^ 16 - ((367 / 418) : ℂ) * ζ ^ 18 + ((1135 / 836) : ℂ) * ζ ^ 20 + ((367 / 418) : ℂ) * ζ ^ 22)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY45_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((983 / 836) : ℂ) + ((179 / 418) : ℂ) * ζ ^ 2 + ((243 / 209) : ℂ) * ζ ^ 6 + ((83 / 418) : ℂ) * ζ ^ 8 - ((19 / 44) : ℂ) * ζ ^ 12 + ((18 / 209) : ℂ) * ζ ^ 18 - ((179 / 418) : ℂ) * ζ ^ 22 - ((887 / 836) : ℂ) * ζ ^ 24 - ((83 / 418) : ℂ) * ζ ^ 28 + ((189 / 209) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((377 / 209) : ℂ) - ((191 / 209) : ℂ) * ζ ^ 2 + ((25 / 22) : ℂ) * ζ ^ 6 + ((1631 / 836) : ℂ) * ζ ^ 8 + ((17 / 836) : ℂ) * ζ ^ 12 + ((553 / 418) : ℂ) * ζ ^ 18 + ((191 / 209) : ℂ) * ζ ^ 22 - ((2199 / 836) : ℂ) * ζ ^ 24 - ((1631 / 836) : ℂ) * ζ ^ 28 + ((521 / 418) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((93 / 836) : ℂ) - ((479 / 418) : ℂ) * ζ ^ 2 - ((367 / 418) : ℂ) * ζ ^ 6 + ((1335 / 836) : ℂ) * ζ ^ 8 + ((921 / 836) : ℂ) * ζ ^ 12 + ((85 / 209) : ℂ) * ζ ^ 18 + ((479 / 418) : ℂ) * ζ ^ 22 - ((721 / 836) : ℂ) * ζ ^ 24 - ((1335 / 836) : ℂ) * ζ ^ 28 - ((85 / 418) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((983 / 836) : ℂ) - ((179 / 418) : ℂ) * ζ ^ 2 - ((243 / 209) : ℂ) * ζ ^ 6 - ((83 / 418) : ℂ) * ζ ^ 8 + ((19 / 44) : ℂ) * ζ ^ 12 - ((18 / 209) : ℂ) * ζ ^ 18 + ((179 / 418) : ℂ) * ζ ^ 22 + ((887 / 836) : ℂ) * ζ ^ 24 + ((83 / 418) : ℂ) * ζ ^ 28 - ((189 / 209) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY45_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((1344 / 209) : ℂ) + ((470 / 209) : ℂ) * ζ ^ 2 - ((574 / 209) : ℂ) * ζ ^ 6 - ((1414 / 209) : ℂ) * ζ ^ 8 - ((166 / 209) : ℂ) * ζ ^ 12 - ((828 / 209) : ℂ) * ζ ^ 18 - ((470 / 209) : ℂ) * ζ ^ 22 + ((2231 / 209) : ℂ) * ζ ^ 24 + ((1414 / 209) : ℂ) * ζ ^ 28 - ((972 / 209) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((983 / 836) : ℂ) - ((179 / 418) : ℂ) * ζ ^ 2 - ((983 / 836) : ℂ) * ζ ^ 4 - ((307 / 418) : ℂ) * ζ ^ 6 + ((43 / 44) : ℂ) * ζ ^ 8 + ((307 / 418) : ℂ) * ζ ^ 10 - ((43 / 44) : ℂ) * ζ ^ 12 - ((721 / 418) : ℂ) * ζ ^ 14 + ((43 / 44) : ℂ) * ζ ^ 16 + ((243 / 209) : ℂ) * ζ ^ 18 + ((707 / 418) : ℂ) * ζ ^ 20 - ((243 / 209) : ℂ) * ζ ^ 22)) * Y 0 0
        + ((((4229 / 836) : ℂ) + ((830 / 209) : ℂ) * ζ ^ 2 - ((4229 / 836) : ℂ) * ζ ^ 4 - ((1043 / 209) : ℂ) * ζ ^ 6 - ((3187 / 418) : ℂ) * ζ ^ 8 + ((1381 / 418) : ℂ) * ζ ^ 10 + ((757 / 76) : ℂ) * ζ ^ 12 + ((905 / 418) : ℂ) * ζ ^ 14 - ((215 / 44) : ℂ) * ζ ^ 16 - ((15 / 2) : ℂ) * ζ ^ 18 - ((377 / 836) : ℂ) * ζ ^ 20 + ((1215 / 209) : ℂ) * ζ ^ 22 + ((2121 / 418) : ℂ) * ζ ^ 24 - ((729 / 209) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((983 / 836) : ℂ) + ((179 / 418) : ℂ) * ζ ^ 2 + ((983 / 836) : ℂ) * ζ ^ 4 + ((307 / 418) : ℂ) * ζ ^ 6 - ((43 / 44) : ℂ) * ζ ^ 8 - ((307 / 418) : ℂ) * ζ ^ 10 + ((43 / 44) : ℂ) * ζ ^ 12 + ((721 / 418) : ℂ) * ζ ^ 14 - ((43 / 44) : ℂ) * ζ ^ 16 - ((243 / 209) : ℂ) * ζ ^ 18 - ((707 / 418) : ℂ) * ζ ^ 20 + ((243 / 209) : ℂ) * ζ ^ 22)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY45_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((36753 / 34276) : ℂ) + ((14039 / 51414) : ℂ) * ζ ^ 2 + ((61855 / 51414) : ℂ) * ζ ^ 6 + ((6367 / 51414) : ℂ) * ζ ^ 8 - ((37859 / 102828) : ℂ) * ζ ^ 12 - ((335 / 8569) : ℂ) * ζ ^ 18 - ((14039 / 51414) : ℂ) * ζ ^ 22 - ((37189 / 34276) : ℂ) * ζ ^ 24 - ((6367 / 51414) : ℂ) * ζ ^ 28 + ((27502 / 25707) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((17078 / 8569) : ℂ) - ((15208 / 25707) : ℂ) * ζ ^ 2 + ((40901 / 51414) : ℂ) * ζ ^ 6 + ((217499 / 102828) : ℂ) * ζ ^ 8 + ((8737 / 102828) : ℂ) * ζ ^ 12 + ((65713 / 51414) : ℂ) * ζ ^ 18 + ((15208 / 25707) : ℂ) * ζ ^ 22 - ((292759 / 102828) : ℂ) * ζ ^ 24 - ((217499 / 102828) : ℂ) * ζ ^ 28 + ((27503 / 25707) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((93 / 836) : ℂ) - ((479 / 418) : ℂ) * ζ ^ 2 - ((367 / 418) : ℂ) * ζ ^ 6 + ((1335 / 836) : ℂ) * ζ ^ 8 + ((921 / 836) : ℂ) * ζ ^ 12 + ((85 / 209) : ℂ) * ζ ^ 18 + ((479 / 418) : ℂ) * ζ ^ 22 - ((721 / 836) : ℂ) * ζ ^ 24 - ((1335 / 836) : ℂ) * ζ ^ 28 - ((85 / 418) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((983 / 836) : ℂ) - ((179 / 418) : ℂ) * ζ ^ 2 - ((243 / 209) : ℂ) * ζ ^ 6 - ((83 / 418) : ℂ) * ζ ^ 8 + ((19 / 44) : ℂ) * ζ ^ 12 - ((18 / 209) : ℂ) * ζ ^ 18 + ((179 / 418) : ℂ) * ζ ^ 22 + ((887 / 836) : ℂ) * ζ ^ 24 + ((83 / 418) : ℂ) * ζ ^ 28 - ((189 / 209) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((1775 / 17138) : ℂ) + ((3989 / 25707) : ℂ) * ζ ^ 2 - ((2077 / 51414) : ℂ) * ζ ^ 6 + ((1921 / 25707) : ℂ) * ζ ^ 8 - ((1636 / 25707) : ℂ) * ζ ^ 12 + ((1073 / 8569) : ℂ) * ζ ^ 18 - ((3989 / 25707) : ℂ) * ζ ^ 22 + ((411 / 17138) : ℂ) * ζ ^ 24 - ((1921 / 25707) : ℂ) * ζ ^ 28 - ((4255 / 25707) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((95 / 902) : ℂ) + ((274 / 1353) : ℂ) * ζ ^ 2 + ((133 / 451) : ℂ) * ζ ^ 6 - ((301 / 1353) : ℂ) * ζ ^ 8 - ((53 / 902) : ℂ) * ζ ^ 12 - ((1091 / 2706) : ℂ) * ζ ^ 18 - ((274 / 1353) : ℂ) * ζ ^ 22 + ((90 / 451) : ℂ) * ζ ^ 24 + ((301 / 1353) : ℂ) * ζ ^ 28 + ((301 / 902) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have previous :=
    row17_reducedY45_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation02
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((754 / 627) : ℂ) - ((452 / 627) : ℂ) * ζ ^ 2 - ((118 / 627) : ℂ) * ζ ^ 6 + ((226 / 209) : ℂ) * ζ ^ 8 + ((32 / 33) : ℂ) * ζ ^ 12 + ((208 / 627) : ℂ) * ζ ^ 18 + ((452 / 627) : ℂ) * ζ ^ 22 - ((236 / 627) : ℂ) * ζ ^ 24 - ((226 / 209) : ℂ) * ζ ^ 28 + ((94 / 627) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((439 / 2706) : ℂ) - ((354 / 8569) : ℂ) * ζ ^ 2 + ((1123 / 17138) : ℂ) * ζ ^ 4 - ((2687 / 51414) : ℂ) * ζ ^ 6 - ((3593 / 17138) : ℂ) * ζ ^ 8 + ((3365 / 51414) : ℂ) * ζ ^ 10 - ((6673 / 51414) : ℂ) * ζ ^ 12 - ((3283 / 51414) : ℂ) * ζ ^ 14 + ((3957 / 17138) : ℂ) * ζ ^ 16 - ((153 / 17138) : ℂ) * ζ ^ 18 - ((13163 / 51414) : ℂ) * ζ ^ 20 + ((379 / 17138) : ℂ) * ζ ^ 22 + ((5179 / 25707) : ℂ) * ζ ^ 24 - ((9 / 8569) : ℂ) * ζ ^ 26 - ((94 / 25707) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((5240 / 25707) : ℂ) + ((12299 / 25707) : ℂ) * ζ ^ 2 + ((6964 / 25707) : ℂ) * ζ ^ 4 + ((16795 / 51414) : ℂ) * ζ ^ 6 + ((39031 / 51414) : ℂ) * ζ ^ 8 - ((28547 / 51414) : ℂ) * ζ ^ 10 + ((4 / 779) : ℂ) * ζ ^ 12 + ((3808 / 8569) : ℂ) * ζ ^ 14 - ((2191 / 8569) : ℂ) * ζ ^ 16 + ((1 / 25707) : ℂ) * ζ ^ 18 + ((1097 / 25707) : ℂ) * ζ ^ 20 - ((1959 / 8569) : ℂ) * ζ ^ 22 - ((17705 / 25707) : ℂ) * ζ ^ 24 + ((9365 / 25707) : ℂ) * ζ ^ 26 - ((940 / 25707) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((439 / 2706) : ℂ) + ((354 / 8569) : ℂ) * ζ ^ 2 - ((1123 / 17138) : ℂ) * ζ ^ 4 + ((2687 / 51414) : ℂ) * ζ ^ 6 + ((3593 / 17138) : ℂ) * ζ ^ 8 - ((3365 / 51414) : ℂ) * ζ ^ 10 + ((6673 / 51414) : ℂ) * ζ ^ 12 + ((3283 / 51414) : ℂ) * ζ ^ 14 - ((3957 / 17138) : ℂ) * ζ ^ 16 + ((153 / 17138) : ℂ) * ζ ^ 18 + ((13163 / 51414) : ℂ) * ζ ^ 20 - ((379 / 17138) : ℂ) * ζ ^ 22 - ((5179 / 25707) : ℂ) * ζ ^ 24 + ((9 / 8569) : ℂ) * ζ ^ 26 + ((94 / 25707) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((257 / 25707) : ℂ) - ((10523 / 25707) : ℂ) * ζ ^ 2 - ((3811 / 25707) : ℂ) * ζ ^ 4 - ((211 / 8569) : ℂ) * ζ ^ 6 - ((148 / 8569) : ℂ) * ζ ^ 8 + ((376 / 2337) : ℂ) * ζ ^ 10 - ((3160 / 25707) : ℂ) * ζ ^ 12 - ((2554 / 8569) : ℂ) * ζ ^ 14 + ((5981 / 51414) : ℂ) * ζ ^ 16 + ((3257 / 17138) : ℂ) * ζ ^ 18 - ((5173 / 51414) : ℂ) * ζ ^ 20 - ((2765 / 51414) : ℂ) * ζ ^ 22 + ((445 / 2706) : ℂ) * ζ ^ 24 + ((3665 / 51414) : ℂ) * ζ ^ 26 - ((329 / 25707) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY45_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((1079 / 836) : ℂ) + ((14 / 19) : ℂ) * ζ ^ 2 + ((25 / 19) : ℂ) * ζ ^ 6 - ((2 / 209) : ℂ) * ζ ^ 8 - ((643 / 836) : ℂ) * ζ ^ 12 + ((1 / 38) : ℂ) * ζ ^ 18 - ((14 / 19) : ℂ) * ζ ^ 22 - ((857 / 836) : ℂ) * ζ ^ 24 + ((2 / 209) : ℂ) * ζ ^ 28 + ((33 / 38) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((375 / 209) : ℂ) - ((35 / 38) : ℂ) * ζ ^ 2 + ((6 / 19) : ℂ) * ζ ^ 6 + ((2135 / 836) : ℂ) * ζ ^ 8 + ((849 / 836) : ℂ) * ζ ^ 12 + ((45 / 38) : ℂ) * ζ ^ 18 + ((35 / 38) : ℂ) * ζ ^ 22 - ((2801 / 836) : ℂ) * ζ ^ 24 - ((2135 / 836) : ℂ) * ζ ^ 28 + ζ ^ 30)) * Y 0 1
      + ((-((93 / 836) : ℂ) - ((479 / 418) : ℂ) * ζ ^ 2 - ((367 / 418) : ℂ) * ζ ^ 6 + ((1335 / 836) : ℂ) * ζ ^ 8 + ((921 / 836) : ℂ) * ζ ^ 12 + ((85 / 209) : ℂ) * ζ ^ 18 + ((479 / 418) : ℂ) * ζ ^ 22 - ((721 / 836) : ℂ) * ζ ^ 24 - ((1335 / 836) : ℂ) * ζ ^ 28 - ((85 / 418) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((983 / 836) : ℂ) - ((179 / 418) : ℂ) * ζ ^ 2 - ((243 / 209) : ℂ) * ζ ^ 6 - ((83 / 418) : ℂ) * ζ ^ 8 + ((19 / 44) : ℂ) * ζ ^ 12 - ((18 / 209) : ℂ) * ζ ^ 18 + ((179 / 418) : ℂ) * ζ ^ 22 + ((887 / 836) : ℂ) * ζ ^ 24 + ((83 / 418) : ℂ) * ζ ^ 28 - ((189 / 209) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((1775 / 17138) : ℂ) + ((3989 / 25707) : ℂ) * ζ ^ 2 - ((2077 / 51414) : ℂ) * ζ ^ 6 + ((1921 / 25707) : ℂ) * ζ ^ 8 - ((1636 / 25707) : ℂ) * ζ ^ 12 + ((1073 / 8569) : ℂ) * ζ ^ 18 - ((3989 / 25707) : ℂ) * ζ ^ 22 + ((411 / 17138) : ℂ) * ζ ^ 24 - ((1921 / 25707) : ℂ) * ζ ^ 28 - ((4255 / 25707) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((358 / 25707) : ℂ) + ((718 / 25707) : ℂ) * ζ ^ 2 - ((8116 / 25707) : ℂ) * ζ ^ 6 + ((12269 / 25707) : ℂ) * ζ ^ 8 + ((2843 / 51414) : ℂ) * ζ ^ 12 + ((1447 / 51414) : ℂ) * ζ ^ 18 - ((718 / 25707) : ℂ) * ζ ^ 22 - ((3367 / 51414) : ℂ) * ζ ^ 24 - ((12269 / 25707) : ℂ) * ζ ^ 28 - ((13027 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((95 / 902) : ℂ) + ((274 / 1353) : ℂ) * ζ ^ 2 + ((133 / 451) : ℂ) * ζ ^ 6 - ((301 / 1353) : ℂ) * ζ ^ 8 - ((53 / 902) : ℂ) * ζ ^ 12 - ((1091 / 2706) : ℂ) * ζ ^ 18 - ((274 / 1353) : ℂ) * ζ ^ 22 + ((90 / 451) : ℂ) * ζ ^ 24 + ((301 / 1353) : ℂ) * ζ ^ 28 + ((301 / 902) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((197 / 902) : ℂ) - ((1255 / 2706) : ℂ) * ζ ^ 2 - ((305 / 2706) : ℂ) * ζ ^ 6 + ((361 / 2706) : ℂ) * ζ ^ 8 + ((1085 / 2706) : ℂ) * ζ ^ 12 - ((59 / 902) : ℂ) * ζ ^ 18 + ((1255 / 2706) : ℂ) * ζ ^ 22 - ((27 / 451) : ℂ) * ζ ^ 24 - ((361 / 2706) : ℂ) * ζ ^ 28 + ((545 / 2706) : ℂ) * ζ ^ 30)) * Y 3 3) = 0 := by
  have previous :=
    row17_reducedY45_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation03
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((38 / 33) : ℂ) + ((896 / 627) : ℂ) * ζ ^ 2 + ((986 / 627) : ℂ) * ζ ^ 6 - ((224 / 209) : ℂ) * ζ ^ 8 - ((332 / 627) : ℂ) * ζ ^ 12 - ((200 / 209) : ℂ) * ζ ^ 18 - ((896 / 627) : ℂ) * ζ ^ 22 + ((788 / 627) : ℂ) * ζ ^ 24 + ((224 / 209) : ℂ) * ζ ^ 28 + ((784 / 627) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((172 / 1353) : ℂ) - ((1675 / 17138) : ℂ) * ζ ^ 2 - ((11332 / 25707) : ℂ) * ζ ^ 4 + ((6610 / 25707) : ℂ) * ζ ^ 6 + ((3151 / 25707) : ℂ) * ζ ^ 8 - ((5714 / 25707) : ℂ) * ζ ^ 10 + ((6335 / 25707) : ℂ) * ζ ^ 12 + ((1360 / 25707) : ℂ) * ζ ^ 14 - ((10535 / 25707) : ℂ) * ζ ^ 16 + ((98 / 1353) : ℂ) * ζ ^ 18 + ((10019 / 25707) : ℂ) * ζ ^ 20 - ((322 / 8569) : ℂ) * ζ ^ 22 + ((1120 / 25707) : ℂ) * ζ ^ 24 + ((6860 / 25707) : ℂ) * ζ ^ 26 + ((2744 / 25707) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((1028 / 25707) : ℂ) - ((257 / 8569) : ℂ) * ζ ^ 2 + ((52 / 1353) : ℂ) * ζ ^ 4 + ((1875 / 8569) : ℂ) * ζ ^ 6 - ((8342 / 25707) : ℂ) * ζ ^ 8 - ((17 / 123) : ℂ) * ζ ^ 10 - ((6104 / 25707) : ℂ) * ζ ^ 12 - ((1693 / 25707) : ℂ) * ζ ^ 14 + ((5432 / 25707) : ℂ) * ζ ^ 16 + ((416 / 25707) : ℂ) * ζ ^ 18 - ((2228 / 25707) : ℂ) * ζ ^ 20 + ((552 / 8569) : ℂ) * ζ ^ 22 + ((672 / 8569) : ℂ) * ζ ^ 24 - ((7168 / 25707) : ℂ) * ζ ^ 26 - ((1568 / 8569) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((362 / 8569) : ℂ) + ((487 / 8569) : ℂ) * ζ ^ 2 - ((6014 / 25707) : ℂ) * ζ ^ 4 + ((1922 / 8569) : ℂ) * ζ ^ 6 - ((6263 / 25707) : ℂ) * ζ ^ 8 - ((2930 / 8569) : ℂ) * ζ ^ 10 + ((8903 / 25707) : ℂ) * ζ ^ 12 + ((986 / 25707) : ℂ) * ζ ^ 14 - ((8791 / 25707) : ℂ) * ζ ^ 16 + ((5288 / 25707) : ℂ) * ζ ^ 18 + ((962 / 8569) : ℂ) * ζ ^ 20 - ((8312 / 25707) : ℂ) * ζ ^ 22 + ((224 / 1353) : ℂ) * ζ ^ 24 + ((2184 / 8569) : ℂ) * ζ ^ 26 + ((784 / 25707) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((172 / 1353) : ℂ) + ((1675 / 17138) : ℂ) * ζ ^ 2 + ((11332 / 25707) : ℂ) * ζ ^ 4 - ((6610 / 25707) : ℂ) * ζ ^ 6 - ((3151 / 25707) : ℂ) * ζ ^ 8 + ((5714 / 25707) : ℂ) * ζ ^ 10 - ((6335 / 25707) : ℂ) * ζ ^ 12 - ((1360 / 25707) : ℂ) * ζ ^ 14 + ((10535 / 25707) : ℂ) * ζ ^ 16 - ((98 / 1353) : ℂ) * ζ ^ 18 - ((10019 / 25707) : ℂ) * ζ ^ 20 + ((322 / 8569) : ℂ) * ζ ^ 22 - ((1120 / 25707) : ℂ) * ζ ^ 24 - ((6860 / 25707) : ℂ) * ζ ^ 26 - ((2744 / 25707) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY45_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((14 / 209) : ℂ) + ((5 / 19) : ℂ) * ζ ^ 2 + ((11 / 38) : ℂ) * ζ ^ 6 + ((103 / 418) : ℂ) * ζ ^ 8 + ((239 / 418) : ℂ) * ζ ^ 12 - ((2 / 19) : ℂ) * ζ ^ 18 - ((5 / 19) : ℂ) * ζ ^ 22 - ((61 / 418) : ℂ) * ζ ^ 24 - ((103 / 418) : ℂ) * ζ ^ 28 + ((9 / 38) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((((232 / 209) : ℂ) - ((1 / 38) : ℂ) * ζ ^ 2 + ((3 / 38) : ℂ) * ζ ^ 6 - ((157 / 209) : ℂ) * ζ ^ 8 - ((61 / 209) : ℂ) * ζ ^ 12 + ((13 / 38) : ℂ) * ζ ^ 18 + ((1 / 38) : ℂ) * ζ ^ 22 + ((295 / 418) : ℂ) * ζ ^ 24 + ((157 / 209) : ℂ) * ζ ^ 28 + ((7 / 38) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((93 / 836) : ℂ) - ((479 / 418) : ℂ) * ζ ^ 2 - ((367 / 418) : ℂ) * ζ ^ 6 + ((1335 / 836) : ℂ) * ζ ^ 8 + ((921 / 836) : ℂ) * ζ ^ 12 + ((85 / 209) : ℂ) * ζ ^ 18 + ((479 / 418) : ℂ) * ζ ^ 22 - ((721 / 836) : ℂ) * ζ ^ 24 - ((1335 / 836) : ℂ) * ζ ^ 28 - ((85 / 418) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((983 / 836) : ℂ) - ((179 / 418) : ℂ) * ζ ^ 2 - ((243 / 209) : ℂ) * ζ ^ 6 - ((83 / 418) : ℂ) * ζ ^ 8 + ((19 / 44) : ℂ) * ζ ^ 12 - ((18 / 209) : ℂ) * ζ ^ 18 + ((179 / 418) : ℂ) * ζ ^ 22 + ((887 / 836) : ℂ) * ζ ^ 24 + ((83 / 418) : ℂ) * ζ ^ 28 - ((189 / 209) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((1775 / 17138) : ℂ) + ((3989 / 25707) : ℂ) * ζ ^ 2 - ((2077 / 51414) : ℂ) * ζ ^ 6 + ((1921 / 25707) : ℂ) * ζ ^ 8 - ((1636 / 25707) : ℂ) * ζ ^ 12 + ((1073 / 8569) : ℂ) * ζ ^ 18 - ((3989 / 25707) : ℂ) * ζ ^ 22 + ((411 / 17138) : ℂ) * ζ ^ 24 - ((1921 / 25707) : ℂ) * ζ ^ 28 - ((4255 / 25707) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((358 / 25707) : ℂ) + ((718 / 25707) : ℂ) * ζ ^ 2 - ((8116 / 25707) : ℂ) * ζ ^ 6 + ((12269 / 25707) : ℂ) * ζ ^ 8 + ((2843 / 51414) : ℂ) * ζ ^ 12 + ((1447 / 51414) : ℂ) * ζ ^ 18 - ((718 / 25707) : ℂ) * ζ ^ 22 - ((3367 / 51414) : ℂ) * ζ ^ 24 - ((12269 / 25707) : ℂ) * ζ ^ 28 - ((13027 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((95 / 902) : ℂ) + ((274 / 1353) : ℂ) * ζ ^ 2 + ((133 / 451) : ℂ) * ζ ^ 6 - ((301 / 1353) : ℂ) * ζ ^ 8 - ((53 / 902) : ℂ) * ζ ^ 12 - ((1091 / 2706) : ℂ) * ζ ^ 18 - ((274 / 1353) : ℂ) * ζ ^ 22 + ((90 / 451) : ℂ) * ζ ^ 24 + ((301 / 1353) : ℂ) * ζ ^ 28 + ((301 / 902) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((197 / 902) : ℂ) - ((1255 / 2706) : ℂ) * ζ ^ 2 - ((305 / 2706) : ℂ) * ζ ^ 6 + ((361 / 2706) : ℂ) * ζ ^ 8 + ((1085 / 2706) : ℂ) * ζ ^ 12 - ((59 / 902) : ℂ) * ζ ^ 18 + ((1255 / 2706) : ℂ) * ζ ^ 22 - ((27 / 451) : ℂ) * ζ ^ 24 - ((361 / 2706) : ℂ) * ζ ^ 28 + ((545 / 2706) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((-((1135 / 836) : ℂ) + ((9 / 19) : ℂ) * ζ ^ 2 + ((39 / 38) : ℂ) * ζ ^ 6 - ((107 / 418) : ℂ) * ζ ^ 8 - ((59 / 44) : ℂ) * ζ ^ 12 + ((5 / 38) : ℂ) * ζ ^ 18 - ((9 / 19) : ℂ) * ζ ^ 22 - ((735 / 836) : ℂ) * ζ ^ 24 + ((107 / 418) : ℂ) * ζ ^ 28 + ((12 / 19) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((691 / 836) : ℂ) - ((100 / 209) : ℂ) * ζ ^ 2 - ((1 / 418) : ℂ) * ζ ^ 6 + ((292 / 209) : ℂ) * ζ ^ 8 + ((255 / 836) : ℂ) * ζ ^ 12 + ((215 / 418) : ℂ) * ζ ^ 18 + ((100 / 209) : ℂ) * ζ ^ 22 - ((1601 / 836) : ℂ) * ζ ^ 24 - ((292 / 209) : ℂ) * ζ ^ 28 + ((67 / 209) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY45_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((46 / 33) : ℂ) + ((186 / 209) : ℂ) * ζ ^ 2 + ((730 / 627) : ℂ) * ζ ^ 6 - ((694 / 627) : ℂ) * ζ ^ 8 - ((724 / 627) : ℂ) * ζ ^ 12 - ((74 / 209) : ℂ) * ζ ^ 18 - ((186 / 209) : ℂ) * ζ ^ 22 + ((211 / 627) : ℂ) * ζ ^ 24 + ((694 / 627) : ℂ) * ζ ^ 28 + ((322 / 627) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((5493 / 9196) : ℂ) - ((27 / 2299) : ℂ) * ζ ^ 2 + ((5493 / 9196) : ℂ) * ζ ^ 4 + ((1853 / 4598) : ℂ) * ζ ^ 6 - ((4043 / 9196) : ℂ) * ζ ^ 8 - ((1295 / 4598) : ℂ) * ζ ^ 10 - ((1871 / 9196) : ℂ) * ζ ^ 12 + ((9 / 2299) : ℂ) * ζ ^ 14 + ((483 / 9196) : ℂ) * ζ ^ 16 + ((719 / 4598) : ℂ) * ζ ^ 18 - ((279 / 2299) : ℂ) * ζ ^ 20 - ((161 / 4598) : ℂ) * ζ ^ 22 - ((347 / 2299) : ℂ) * ζ ^ 24 - ((161 / 2299) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((4177 / 4598) : ℂ) - ((9973 / 4598) : ℂ) * ζ ^ 2 + ((4177 / 4598) : ℂ) * ζ ^ 4 + ((3397 / 4598) : ℂ) * ζ ^ 6 + ((1053 / 484) : ℂ) * ζ ^ 8 + ((952 / 2299) : ℂ) * ζ ^ 10 - ((7559 / 4598) : ℂ) * ζ ^ 12 - ((239 / 2299) : ℂ) * ζ ^ 14 + ((483 / 2299) : ℂ) * ζ ^ 16 + ((5945 / 4598) : ℂ) * ζ ^ 18 - ((6785 / 9196) : ℂ) * ζ ^ 20 - ((322 / 2299) : ℂ) * ζ ^ 22 - ((347 / 242) : ℂ) * ζ ^ 24 - ((161 / 242) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((5493 / 9196) : ℂ) + ((27 / 2299) : ℂ) * ζ ^ 2 - ((5493 / 9196) : ℂ) * ζ ^ 4 - ((1853 / 4598) : ℂ) * ζ ^ 6 + ((4043 / 9196) : ℂ) * ζ ^ 8 + ((1295 / 4598) : ℂ) * ζ ^ 10 + ((1871 / 9196) : ℂ) * ζ ^ 12 - ((9 / 2299) : ℂ) * ζ ^ 14 - ((483 / 9196) : ℂ) * ζ ^ 16 - ((719 / 4598) : ℂ) * ζ ^ 18 + ((279 / 2299) : ℂ) * ζ ^ 20 + ((161 / 4598) : ℂ) * ζ ^ 22 + ((347 / 2299) : ℂ) * ζ ^ 24 + ((161 / 2299) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((5853 / 9196) : ℂ) + ((1379 / 2299) : ℂ) * ζ ^ 2 - ((5853 / 9196) : ℂ) * ζ ^ 4 - ((2017 / 4598) : ℂ) * ζ ^ 6 - ((3139 / 9196) : ℂ) * ζ ^ 8 + ((343 / 4598) : ℂ) * ζ ^ 10 + ((5613 / 9196) : ℂ) * ζ ^ 12 - ((27 / 2299) : ℂ) * ζ ^ 14 - ((1449 / 9196) : ℂ) * ζ ^ 16 - ((2157 / 4598) : ℂ) * ζ ^ 18 + ((837 / 2299) : ℂ) * ζ ^ 20 + ((483 / 4598) : ℂ) * ζ ^ 22 + ((1041 / 2299) : ℂ) * ζ ^ 24 + ((483 / 2299) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY45_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((93 / 836) : ℂ) - ((479 / 418) : ℂ) * ζ ^ 2 - ((367 / 418) : ℂ) * ζ ^ 6 + ((1335 / 836) : ℂ) * ζ ^ 8 + ((921 / 836) : ℂ) * ζ ^ 12 + ((85 / 209) : ℂ) * ζ ^ 18 + ((479 / 418) : ℂ) * ζ ^ 22 - ((721 / 836) : ℂ) * ζ ^ 24 - ((1335 / 836) : ℂ) * ζ ^ 28 - ((85 / 418) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((983 / 836) : ℂ) - ((179 / 418) : ℂ) * ζ ^ 2 - ((243 / 209) : ℂ) * ζ ^ 6 - ((83 / 418) : ℂ) * ζ ^ 8 + ((19 / 44) : ℂ) * ζ ^ 12 - ((18 / 209) : ℂ) * ζ ^ 18 + ((179 / 418) : ℂ) * ζ ^ 22 + ((887 / 836) : ℂ) * ζ ^ 24 + ((83 / 418) : ℂ) * ζ ^ 28 - ((189 / 209) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((1775 / 17138) : ℂ) + ((3989 / 25707) : ℂ) * ζ ^ 2 - ((2077 / 51414) : ℂ) * ζ ^ 6 + ((1921 / 25707) : ℂ) * ζ ^ 8 - ((1636 / 25707) : ℂ) * ζ ^ 12 + ((1073 / 8569) : ℂ) * ζ ^ 18 - ((3989 / 25707) : ℂ) * ζ ^ 22 + ((411 / 17138) : ℂ) * ζ ^ 24 - ((1921 / 25707) : ℂ) * ζ ^ 28 - ((4255 / 25707) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((358 / 25707) : ℂ) + ((718 / 25707) : ℂ) * ζ ^ 2 - ((8116 / 25707) : ℂ) * ζ ^ 6 + ((12269 / 25707) : ℂ) * ζ ^ 8 + ((2843 / 51414) : ℂ) * ζ ^ 12 + ((1447 / 51414) : ℂ) * ζ ^ 18 - ((718 / 25707) : ℂ) * ζ ^ 22 - ((3367 / 51414) : ℂ) * ζ ^ 24 - ((12269 / 25707) : ℂ) * ζ ^ 28 - ((13027 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((95 / 902) : ℂ) + ((274 / 1353) : ℂ) * ζ ^ 2 + ((133 / 451) : ℂ) * ζ ^ 6 - ((301 / 1353) : ℂ) * ζ ^ 8 - ((53 / 902) : ℂ) * ζ ^ 12 - ((1091 / 2706) : ℂ) * ζ ^ 18 - ((274 / 1353) : ℂ) * ζ ^ 22 + ((90 / 451) : ℂ) * ζ ^ 24 + ((301 / 1353) : ℂ) * ζ ^ 28 + ((301 / 902) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((197 / 902) : ℂ) - ((1255 / 2706) : ℂ) * ζ ^ 2 - ((305 / 2706) : ℂ) * ζ ^ 6 + ((361 / 2706) : ℂ) * ζ ^ 8 + ((1085 / 2706) : ℂ) * ζ ^ 12 - ((59 / 902) : ℂ) * ζ ^ 18 + ((1255 / 2706) : ℂ) * ζ ^ 22 - ((27 / 451) : ℂ) * ζ ^ 24 - ((361 / 2706) : ℂ) * ζ ^ 28 + ((545 / 2706) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((-((1135 / 836) : ℂ) + ((9 / 19) : ℂ) * ζ ^ 2 + ((39 / 38) : ℂ) * ζ ^ 6 - ((107 / 418) : ℂ) * ζ ^ 8 - ((59 / 44) : ℂ) * ζ ^ 12 + ((5 / 38) : ℂ) * ζ ^ 18 - ((9 / 19) : ℂ) * ζ ^ 22 - ((735 / 836) : ℂ) * ζ ^ 24 + ((107 / 418) : ℂ) * ζ ^ 28 + ((12 / 19) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((122 / 209) : ℂ) + ((6 / 19) : ℂ) * ζ ^ 2 + ((3 / 38) : ℂ) * ζ ^ 6 + ((159 / 418) : ℂ) * ζ ^ 8 - ((155 / 418) : ℂ) * ζ ^ 12 - ((6 / 19) : ℂ) * ζ ^ 22 - ((145 / 418) : ℂ) * ζ ^ 24 - ((159 / 418) : ℂ) * ζ ^ 28 - ((7 / 38) : ℂ) * ζ ^ 30)) * Y 4 5
      + ((-((691 / 836) : ℂ) - ((100 / 209) : ℂ) * ζ ^ 2 - ((1 / 418) : ℂ) * ζ ^ 6 + ((292 / 209) : ℂ) * ζ ^ 8 + ((255 / 836) : ℂ) * ζ ^ 12 + ((215 / 418) : ℂ) * ζ ^ 18 + ((100 / 209) : ℂ) * ζ ^ 22 - ((1601 / 836) : ℂ) * ζ ^ 24 - ((292 / 209) : ℂ) * ζ ^ 28 + ((67 / 209) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((14 / 209) : ℂ) + ((5 / 19) : ℂ) * ζ ^ 2 + ((11 / 38) : ℂ) * ζ ^ 6 + ((103 / 418) : ℂ) * ζ ^ 8 + ((239 / 418) : ℂ) * ζ ^ 12 - ((2 / 19) : ℂ) * ζ ^ 18 - ((5 / 19) : ℂ) * ζ ^ 22 - ((61 / 418) : ℂ) * ζ ^ 24 - ((103 / 418) : ℂ) * ζ ^ 28 + ((9 / 38) : ℂ) * ζ ^ 30)) * Y 5 5) = 0 := by
  have previous :=
    row17_reducedY45_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation05
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((2 / 19) : ℂ) - ((2 / 57) : ℂ) * ζ ^ 2 + ((46 / 57) : ℂ) * ζ ^ 8 - ((58 / 57) : ℂ) * ζ ^ 12 + ((2 / 57) : ℂ) * ζ ^ 18 + ((2 / 57) : ℂ) * ζ ^ 22 + ((4 / 19) : ℂ) * ζ ^ 24 - ((46 / 57) : ℂ) * ζ ^ 28 - ((10 / 19) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((1 / 19) : ℂ) + ((56 / 209) : ℂ) * ζ ^ 2 - ((1 / 19) : ℂ) * ζ ^ 4 + ((9 / 418) : ℂ) * ζ ^ 6 + ((97 / 418) : ℂ) * ζ ^ 8 - ((15 / 418) : ℂ) * ζ ^ 10 + ((225 / 418) : ℂ) * ζ ^ 12 + ((63 / 209) : ℂ) * ζ ^ 14 - ((87 / 418) : ℂ) * ζ ^ 16 - ((51 / 418) : ℂ) * ζ ^ 18 + ((3 / 38) : ℂ) * ζ ^ 20 + ((45 / 418) : ℂ) * ζ ^ 22 + ((69 / 209) : ℂ) * ζ ^ 24 + ((45 / 209) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((43 / 38) : ℂ) - ((7 / 209) : ℂ) * ζ ^ 2 - ((43 / 38) : ℂ) * ζ ^ 4 + ((47 / 418) : ℂ) * ζ ^ 6 + ((267 / 418) : ℂ) * ζ ^ 8 - ((30 / 209) : ℂ) * ζ ^ 10 + ((9 / 418) : ℂ) * ζ ^ 12 + ((21 / 209) : ℂ) * ζ ^ 14 + ((145 / 209) : ℂ) * ζ ^ 16 + ((137 / 418) : ℂ) * ζ ^ 18 - ((14 / 19) : ℂ) * ζ ^ 20 - ((75 / 209) : ℂ) * ζ ^ 22 + ((299 / 418) : ℂ) * ζ ^ 24 + ((195 / 418) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((10 / 19) : ℂ) - ((70 / 209) : ℂ) * ζ ^ 2 + ((10 / 19) : ℂ) * ζ ^ 4 + ((107 / 418) : ℂ) * ζ ^ 6 - ((201 / 418) : ℂ) * ζ ^ 8 - ((105 / 418) : ℂ) * ζ ^ 10 - ((75 / 418) : ℂ) * ζ ^ 12 - ((21 / 209) : ℂ) * ζ ^ 14 + ((29 / 418) : ℂ) * ζ ^ 16 + ((17 / 418) : ℂ) * ζ ^ 18 - ((1 / 38) : ℂ) * ζ ^ 20 - ((15 / 418) : ℂ) * ζ ^ 22 - ((23 / 209) : ℂ) * ζ ^ 24 - ((15 / 209) : ℂ) * ζ ^ 26)) * Y 4 5
        + ((-((1 / 19) : ℂ) - ((56 / 209) : ℂ) * ζ ^ 2 + ((1 / 19) : ℂ) * ζ ^ 4 - ((9 / 418) : ℂ) * ζ ^ 6 - ((97 / 418) : ℂ) * ζ ^ 8 + ((15 / 418) : ℂ) * ζ ^ 10 - ((225 / 418) : ℂ) * ζ ^ 12 - ((63 / 209) : ℂ) * ζ ^ 14 + ((87 / 418) : ℂ) * ζ ^ 16 + ((51 / 418) : ℂ) * ζ ^ 18 - ((3 / 38) : ℂ) * ζ ^ 20 - ((45 / 418) : ℂ) * ζ ^ 22 - ((69 / 209) : ℂ) * ζ ^ 24 - ((45 / 209) : ℂ) * ζ ^ 26)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY45_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((11971 / 102828) : ℂ) - ((21311 / 17138) : ℂ) * ζ ^ 2 - ((48067 / 51414) : ℂ) * ζ ^ 6 + ((54849 / 34276) : ℂ) * ζ ^ 8 + ((100591 / 102828) : ℂ) * ζ ^ 12 + ((2022 / 8569) : ℂ) * ζ ^ 18 + ((21311 / 17138) : ℂ) * ζ ^ 22 - ((91495 / 102828) : ℂ) * ζ ^ 24 - ((54849 / 34276) : ℂ) * ζ ^ 28 - ((2824 / 25707) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((39049 / 34276) : ℂ) - ((509 / 51414) : ℂ) * ζ ^ 2 - ((23486 / 25707) : ℂ) * ζ ^ 6 + ((3151 / 25707) : ℂ) * ζ ^ 8 + ((5087 / 5412) : ℂ) * ζ ^ 12 - ((567 / 8569) : ℂ) * ζ ^ 18 + ((509 / 51414) : ℂ) * ζ ^ 22 + ((32187 / 34276) : ℂ) * ζ ^ 24 - ((3151 / 25707) : ℂ) * ζ ^ 28 - ((42827 / 51414) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((14 / 209) : ℂ) - ((5 / 19) : ℂ) * ζ ^ 2 - ((11 / 38) : ℂ) * ζ ^ 6 - ((103 / 418) : ℂ) * ζ ^ 8 - ((239 / 418) : ℂ) * ζ ^ 12 + ((2 / 19) : ℂ) * ζ ^ 18 + ((5 / 19) : ℂ) * ζ ^ 22 + ((61 / 418) : ℂ) * ζ ^ 24 + ((103 / 418) : ℂ) * ζ ^ 28 - ((9 / 38) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((358 / 25707) : ℂ) + ((718 / 25707) : ℂ) * ζ ^ 2 - ((8116 / 25707) : ℂ) * ζ ^ 6 + ((12269 / 25707) : ℂ) * ζ ^ 8 + ((2843 / 51414) : ℂ) * ζ ^ 12 + ((1447 / 51414) : ℂ) * ζ ^ 18 - ((718 / 25707) : ℂ) * ζ ^ 22 - ((3367 / 51414) : ℂ) * ζ ^ 24 - ((12269 / 25707) : ℂ) * ζ ^ 28 - ((13027 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((197 / 902) : ℂ) - ((1255 / 2706) : ℂ) * ζ ^ 2 - ((305 / 2706) : ℂ) * ζ ^ 6 + ((361 / 2706) : ℂ) * ζ ^ 8 + ((1085 / 2706) : ℂ) * ζ ^ 12 - ((59 / 902) : ℂ) * ζ ^ 18 + ((1255 / 2706) : ℂ) * ζ ^ 22 - ((27 / 451) : ℂ) * ζ ^ 24 - ((361 / 2706) : ℂ) * ζ ^ 28 + ((545 / 2706) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((-((1135 / 836) : ℂ) + ((9 / 19) : ℂ) * ζ ^ 2 + ((39 / 38) : ℂ) * ζ ^ 6 - ((107 / 418) : ℂ) * ζ ^ 8 - ((59 / 44) : ℂ) * ζ ^ 12 + ((5 / 38) : ℂ) * ζ ^ 18 - ((9 / 19) : ℂ) * ζ ^ 22 - ((735 / 836) : ℂ) * ζ ^ 24 + ((107 / 418) : ℂ) * ζ ^ 28 + ((12 / 19) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((122 / 209) : ℂ) + ((6 / 19) : ℂ) * ζ ^ 2 + ((3 / 38) : ℂ) * ζ ^ 6 + ((159 / 418) : ℂ) * ζ ^ 8 - ((155 / 418) : ℂ) * ζ ^ 12 - ((6 / 19) : ℂ) * ζ ^ 22 - ((145 / 418) : ℂ) * ζ ^ 24 - ((159 / 418) : ℂ) * ζ ^ 28 - ((7 / 38) : ℂ) * ζ ^ 30)) * Y 4 5
      + ((-((691 / 836) : ℂ) - ((100 / 209) : ℂ) * ζ ^ 2 - ((1 / 418) : ℂ) * ζ ^ 6 + ((292 / 209) : ℂ) * ζ ^ 8 + ((255 / 836) : ℂ) * ζ ^ 12 + ((215 / 418) : ℂ) * ζ ^ 18 + ((100 / 209) : ℂ) * ζ ^ 22 - ((1601 / 836) : ℂ) * ζ ^ 24 - ((292 / 209) : ℂ) * ζ ^ 28 + ((67 / 209) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((14 / 209) : ℂ) + ((5 / 19) : ℂ) * ζ ^ 2 + ((11 / 38) : ℂ) * ζ ^ 6 + ((103 / 418) : ℂ) * ζ ^ 8 + ((239 / 418) : ℂ) * ζ ^ 12 - ((2 / 19) : ℂ) * ζ ^ 18 - ((5 / 19) : ℂ) * ζ ^ 22 - ((61 / 418) : ℂ) * ζ ^ 24 - ((103 / 418) : ℂ) * ζ ^ 28 + ((9 / 38) : ℂ) * ζ ^ 30)) * Y 5 5) = 0 := by
  have previous :=
    row17_reducedY45_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation12
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((28 / 33) : ℂ) - ((26 / 33) : ℂ) * ζ ^ 2 - ((10 / 33) : ℂ) * ζ ^ 6 + ((6 / 11) : ℂ) * ζ ^ 8 + ((14 / 33) : ℂ) * ζ ^ 12 + ((6 / 11) : ℂ) * ζ ^ 18 + ((26 / 33) : ℂ) * ζ ^ 22 - ((16 / 33) : ℂ) * ζ ^ 24 - ((6 / 11) : ℂ) * ζ ^ 28 - ((20 / 33) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((49 / 1353) : ℂ) - ((74 / 1353) : ℂ) * ζ ^ 2 - ((94 / 1353) : ℂ) * ζ ^ 4 + ((89 / 1353) : ℂ) * ζ ^ 6 - ((119 / 902) : ℂ) * ζ ^ 8 - ((185 / 1353) : ℂ) * ζ ^ 10 + ((325 / 2706) : ℂ) * ζ ^ 12 + ((7 / 2706) : ℂ) * ζ ^ 14 - ((31 / 246) : ℂ) * ζ ^ 16 + ((11 / 123) : ℂ) * ζ ^ 18 + ((61 / 2706) : ℂ) * ζ ^ 20 - ((217 / 1353) : ℂ) * ζ ^ 22 + ((115 / 1353) : ℂ) * ζ ^ 24 + ((56 / 451) : ℂ) * ζ ^ 26 + ((20 / 1353) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((127 / 2706) : ℂ) + ((203 / 1353) : ℂ) * ζ ^ 2 + ((1277 / 2706) : ℂ) * ζ ^ 4 - ((94 / 1353) : ℂ) * ζ ^ 6 + ((245 / 902) : ℂ) * ζ ^ 8 + ((323 / 1353) : ℂ) * ζ ^ 10 - ((302 / 1353) : ℂ) * ζ ^ 12 - ((2 / 451) : ℂ) * ζ ^ 14 + ((509 / 1353) : ℂ) * ζ ^ 16 - ((61 / 1353) : ℂ) * ζ ^ 18 - ((761 / 1353) : ℂ) * ζ ^ 20 + ((290 / 1353) : ℂ) * ζ ^ 22 - ((695 / 1353) : ℂ) * ζ ^ 24 - ((370 / 1353) : ℂ) * ζ ^ 26 + ((200 / 1353) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((127 / 2706) : ℂ) - ((203 / 1353) : ℂ) * ζ ^ 2 - ((1277 / 2706) : ℂ) * ζ ^ 4 + ((94 / 1353) : ℂ) * ζ ^ 6 - ((245 / 902) : ℂ) * ζ ^ 8 - ((323 / 1353) : ℂ) * ζ ^ 10 + ((302 / 1353) : ℂ) * ζ ^ 12 + ((2 / 451) : ℂ) * ζ ^ 14 - ((509 / 1353) : ℂ) * ζ ^ 16 + ((61 / 1353) : ℂ) * ζ ^ 18 + ((761 / 1353) : ℂ) * ζ ^ 20 - ((290 / 1353) : ℂ) * ζ ^ 22 + ((695 / 1353) : ℂ) * ζ ^ 24 + ((370 / 1353) : ℂ) * ζ ^ 26 - ((200 / 1353) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((191 / 2706) : ℂ) + ((116 / 1353) : ℂ) * ζ ^ 2 + ((14 / 123) : ℂ) * ζ ^ 4 + ((163 / 1353) : ℂ) * ζ ^ 6 - ((200 / 1353) : ℂ) * ζ ^ 8 - ((199 / 2706) : ℂ) * ζ ^ 10 - ((269 / 2706) : ℂ) * ζ ^ 12 - ((1 / 2706) : ℂ) * ζ ^ 14 + ((11 / 123) : ℂ) * ζ ^ 16 - ((17 / 2706) : ℂ) * ζ ^ 18 - ((19 / 1353) : ℂ) * ζ ^ 20 + ((24 / 451) : ℂ) * ζ ^ 22 + ((16 / 451) : ℂ) * ζ ^ 24 - ((188 / 1353) : ℂ) * ζ ^ 26 - ((40 / 451) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY45_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((93 / 836) : ℂ) - ((14 / 19) : ℂ) * ζ ^ 2 - ((23 / 38) : ℂ) * ζ ^ 6 + ((1335 / 836) : ℂ) * ζ ^ 8 + ((921 / 836) : ℂ) * ζ ^ 12 + ((6 / 19) : ℂ) * ζ ^ 18 + ((14 / 19) : ℂ) * ζ ^ 22 - ((721 / 836) : ℂ) * ζ ^ 24 - ((1335 / 836) : ℂ) * ζ ^ 28 - ((3 / 19) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((1135 / 836) : ℂ) - ((9 / 19) : ℂ) * ζ ^ 2 - ((39 / 38) : ℂ) * ζ ^ 6 + ((107 / 418) : ℂ) * ζ ^ 8 + ((59 / 44) : ℂ) * ζ ^ 12 - ((5 / 38) : ℂ) * ζ ^ 18 + ((9 / 19) : ℂ) * ζ ^ 22 + ((735 / 836) : ℂ) * ζ ^ 24 - ((107 / 418) : ℂ) * ζ ^ 28 - ((12 / 19) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((14 / 209) : ℂ) - ((5 / 19) : ℂ) * ζ ^ 2 - ((11 / 38) : ℂ) * ζ ^ 6 - ((103 / 418) : ℂ) * ζ ^ 8 - ((239 / 418) : ℂ) * ζ ^ 12 + ((2 / 19) : ℂ) * ζ ^ 18 + ((5 / 19) : ℂ) * ζ ^ 22 + ((61 / 418) : ℂ) * ζ ^ 24 + ((103 / 418) : ℂ) * ζ ^ 28 - ((9 / 38) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((13 / 209) : ℂ) - ((383 / 418) : ℂ) * ζ ^ 2 - ((501 / 418) : ℂ) * ζ ^ 6 - ((104 / 209) : ℂ) * ζ ^ 8 - ((164 / 209) : ℂ) * ζ ^ 12 + ((13 / 418) : ℂ) * ζ ^ 18 + ((383 / 418) : ℂ) * ζ ^ 22 + ((103 / 418) : ℂ) * ζ ^ 24 + ((104 / 209) : ℂ) * ζ ^ 28 - ((375 / 418) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((1135 / 836) : ℂ) + ((9 / 19) : ℂ) * ζ ^ 2 + ((39 / 38) : ℂ) * ζ ^ 6 - ((107 / 418) : ℂ) * ζ ^ 8 - ((59 / 44) : ℂ) * ζ ^ 12 + ((5 / 38) : ℂ) * ζ ^ 18 - ((9 / 19) : ℂ) * ζ ^ 22 - ((735 / 836) : ℂ) * ζ ^ 24 + ((107 / 418) : ℂ) * ζ ^ 28 + ((12 / 19) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((122 / 209) : ℂ) + ((6 / 19) : ℂ) * ζ ^ 2 + ((3 / 38) : ℂ) * ζ ^ 6 + ((159 / 418) : ℂ) * ζ ^ 8 - ((155 / 418) : ℂ) * ζ ^ 12 - ((6 / 19) : ℂ) * ζ ^ 22 - ((145 / 418) : ℂ) * ζ ^ 24 - ((159 / 418) : ℂ) * ζ ^ 28 - ((7 / 38) : ℂ) * ζ ^ 30)) * Y 4 5
      + ((-((691 / 836) : ℂ) - ((100 / 209) : ℂ) * ζ ^ 2 - ((1 / 418) : ℂ) * ζ ^ 6 + ((292 / 209) : ℂ) * ζ ^ 8 + ((255 / 836) : ℂ) * ζ ^ 12 + ((215 / 418) : ℂ) * ζ ^ 18 + ((100 / 209) : ℂ) * ζ ^ 22 - ((1601 / 836) : ℂ) * ζ ^ 24 - ((292 / 209) : ℂ) * ζ ^ 28 + ((67 / 209) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((14 / 209) : ℂ) + ((5 / 19) : ℂ) * ζ ^ 2 + ((11 / 38) : ℂ) * ζ ^ 6 + ((103 / 418) : ℂ) * ζ ^ 8 + ((239 / 418) : ℂ) * ζ ^ 12 - ((2 / 19) : ℂ) * ζ ^ 18 - ((5 / 19) : ℂ) * ζ ^ 22 - ((61 / 418) : ℂ) * ζ ^ 24 - ((103 / 418) : ℂ) * ζ ^ 28 + ((9 / 38) : ℂ) * ζ ^ 30)) * Y 5 5) = 0 := by
  have previous :=
    row17_reducedY45_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation13
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((38 / 33) : ℂ) + ((14 / 33) : ℂ) * ζ ^ 2 + ((2 / 33) : ℂ) * ζ ^ 6 - ((6 / 11) : ℂ) * ζ ^ 8 - ((14 / 33) : ℂ) * ζ ^ 12 - ((8 / 33) : ℂ) * ζ ^ 18 - ((14 / 33) : ℂ) * ζ ^ 22 + ((16 / 33) : ℂ) * ζ ^ 24 + ((6 / 11) : ℂ) * ζ ^ 28 - ((6 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((87 / 902) : ℂ) - ((298 / 1353) : ℂ) * ζ ^ 2 + ((3 / 902) : ℂ) * ζ ^ 4 + ((58 / 1353) : ℂ) * ζ ^ 6 + ((137 / 2706) : ℂ) * ζ ^ 8 + ((47 / 2706) : ℂ) * ζ ^ 10 - ((28 / 123) : ℂ) * ζ ^ 12 - ((103 / 902) : ℂ) * ζ ^ 14 + ((571 / 2706) : ℂ) * ζ ^ 16 + ((19 / 451) : ℂ) * ζ ^ 18 - ((427 / 2706) : ℂ) * ζ ^ 20 + ((49 / 2706) : ℂ) * ζ ^ 22 + ((111 / 902) : ℂ) * ζ ^ 24 - ((27 / 902) : ℂ) * ζ ^ 26 - ((21 / 451) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((5 / 246) : ℂ) + ((141 / 451) : ℂ) * ζ ^ 2 + ((4 / 1353) : ℂ) * ζ ^ 4 - ((80 / 451) : ℂ) * ζ ^ 6 - ((131 / 902) : ℂ) * ζ ^ 8 + ((511 / 2706) : ℂ) * ζ ^ 10 + ((53 / 451) : ℂ) * ζ ^ 12 + ((67 / 2706) : ℂ) * ζ ^ 14 - ((133 / 902) : ℂ) * ζ ^ 16 + ((115 / 2706) : ℂ) * ζ ^ 18 + ((445 / 2706) : ℂ) * ζ ^ 20 - ((14 / 451) : ℂ) * ζ ^ 22 - ((60 / 451) : ℂ) * ζ ^ 24 - ((12 / 451) : ℂ) * ζ ^ 26 + ((36 / 451) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((28 / 451) : ℂ) + ((47 / 246) : ℂ) * ζ ^ 2 + ((98 / 451) : ℂ) * ζ ^ 4 + ((677 / 2706) : ℂ) * ζ ^ 6 + ((491 / 2706) : ℂ) * ζ ^ 8 - ((293 / 902) : ℂ) * ζ ^ 10 + ((268 / 1353) : ℂ) * ζ ^ 12 + ((361 / 1353) : ℂ) * ζ ^ 14 - ((35 / 123) : ℂ) * ζ ^ 16 + ((6 / 41) : ℂ) * ζ ^ 18 + ((5 / 1353) : ℂ) * ζ ^ 20 - ((299 / 1353) : ℂ) * ζ ^ 22 - ((105 / 451) : ℂ) * ζ ^ 24 + ((225 / 451) : ℂ) * ζ ^ 26 - ((60 / 451) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((5 / 246) : ℂ) - ((141 / 451) : ℂ) * ζ ^ 2 - ((4 / 1353) : ℂ) * ζ ^ 4 + ((80 / 451) : ℂ) * ζ ^ 6 + ((131 / 902) : ℂ) * ζ ^ 8 - ((511 / 2706) : ℂ) * ζ ^ 10 - ((53 / 451) : ℂ) * ζ ^ 12 - ((67 / 2706) : ℂ) * ζ ^ 14 + ((133 / 902) : ℂ) * ζ ^ 16 - ((115 / 2706) : ℂ) * ζ ^ 18 - ((445 / 2706) : ℂ) * ζ ^ 20 + ((14 / 451) : ℂ) * ζ ^ 22 + ((60 / 451) : ℂ) * ζ ^ 24 + ((12 / 451) : ℂ) * ζ ^ 26 - ((36 / 451) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY45_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((14 / 209) : ℂ) - ((5 / 19) : ℂ) * ζ ^ 2 - ((11 / 38) : ℂ) * ζ ^ 6 - ((103 / 418) : ℂ) * ζ ^ 8 - ((239 / 418) : ℂ) * ζ ^ 12 + ((2 / 19) : ℂ) * ζ ^ 18 + ((5 / 19) : ℂ) * ζ ^ 22 + ((61 / 418) : ℂ) * ζ ^ 24 + ((103 / 418) : ℂ) * ζ ^ 28 - ((9 / 38) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((13 / 209) : ℂ) - ((383 / 418) : ℂ) * ζ ^ 2 - ((501 / 418) : ℂ) * ζ ^ 6 - ((104 / 209) : ℂ) * ζ ^ 8 - ((164 / 209) : ℂ) * ζ ^ 12 + ((13 / 418) : ℂ) * ζ ^ 18 + ((383 / 418) : ℂ) * ζ ^ 22 + ((103 / 418) : ℂ) * ζ ^ 24 + ((104 / 209) : ℂ) * ζ ^ 28 - ((375 / 418) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((122 / 209) : ℂ) + ((6 / 19) : ℂ) * ζ ^ 2 + ((3 / 38) : ℂ) * ζ ^ 6 + ((159 / 418) : ℂ) * ζ ^ 8 - ((155 / 418) : ℂ) * ζ ^ 12 - ((6 / 19) : ℂ) * ζ ^ 22 - ((145 / 418) : ℂ) * ζ ^ 24 - ((159 / 418) : ℂ) * ζ ^ 28 - ((7 / 38) : ℂ) * ζ ^ 30)) * Y 4 5
      + ((((14 / 209) : ℂ) + ((5 / 19) : ℂ) * ζ ^ 2 + ((11 / 38) : ℂ) * ζ ^ 6 + ((103 / 418) : ℂ) * ζ ^ 8 + ((239 / 418) : ℂ) * ζ ^ 12 - ((2 / 19) : ℂ) * ζ ^ 18 - ((5 / 19) : ℂ) * ζ ^ 22 - ((61 / 418) : ℂ) * ζ ^ 24 - ((103 / 418) : ℂ) * ζ ^ 28 + ((9 / 38) : ℂ) * ζ ^ 30)) * Y 5 5) = 0 := by
  have previous :=
    row17_reducedY45_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((422 / 627) : ℂ) - ((124 / 209) : ℂ) * ζ ^ 2 - ((62 / 209) : ℂ) * ζ ^ 6 + ((965 / 627) : ℂ) * ζ ^ 8 + ((211 / 209) : ℂ) * ζ ^ 12 + ((236 / 627) : ℂ) * ζ ^ 18 + ((124 / 209) : ℂ) * ζ ^ 22 - ((995 / 627) : ℂ) * ζ ^ 24 - ((965 / 627) : ℂ) * ζ ^ 28 + ((86 / 627) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((2353 / 9196) : ℂ) - ((50 / 121) : ℂ) * ζ ^ 2 - ((2353 / 9196) : ℂ) * ζ ^ 4 - ((139 / 4598) : ℂ) * ζ ^ 6 + ((223 / 242) : ℂ) * ζ ^ 8 - ((233 / 4598) : ℂ) * ζ ^ 10 + ((25 / 121) : ℂ) * ζ ^ 12 - ((29 / 242) : ℂ) * ζ ^ 14 + ((15 / 4598) : ℂ) * ζ ^ 16 - ((329 / 4598) : ℂ) * ζ ^ 18 + ((2955 / 9196) : ℂ) * ζ ^ 20 - ((43 / 4598) : ℂ) * ζ ^ 22 + ((965 / 4598) : ℂ) * ζ ^ 24 - ((43 / 2299) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((21347 / 9196) : ℂ) + ((864 / 2299) : ℂ) * ζ ^ 2 - ((21347 / 9196) : ℂ) * ζ ^ 4 - ((2247 / 2299) : ℂ) * ζ ^ 6 - ((2291 / 4598) : ℂ) * ζ ^ 8 + ((480 / 2299) : ℂ) * ζ ^ 10 + ((18215 / 9196) : ℂ) * ζ ^ 12 - ((3975 / 4598) : ℂ) * ζ ^ 14 + ((30 / 2299) : ℂ) * ζ ^ 16 - ((1681 / 2299) : ℂ) * ζ ^ 18 + ((22765 / 9196) : ℂ) * ζ ^ 20 - ((86 / 2299) : ℂ) * ζ ^ 22 + ((965 / 484) : ℂ) * ζ ^ 24 - ((43 / 242) : ℂ) * ζ ^ 26)) * Y 1 1
        + ((-((21347 / 9196) : ℂ) - ((864 / 2299) : ℂ) * ζ ^ 2 + ((21347 / 9196) : ℂ) * ζ ^ 4 + ((2247 / 2299) : ℂ) * ζ ^ 6 + ((2291 / 4598) : ℂ) * ζ ^ 8 - ((480 / 2299) : ℂ) * ζ ^ 10 - ((18215 / 9196) : ℂ) * ζ ^ 12 + ((3975 / 4598) : ℂ) * ζ ^ 14 - ((30 / 2299) : ℂ) * ζ ^ 16 + ((1681 / 2299) : ℂ) * ζ ^ 18 - ((22765 / 9196) : ℂ) * ζ ^ 20 + ((86 / 2299) : ℂ) * ζ ^ 22 - ((965 / 484) : ℂ) * ζ ^ 24 + ((43 / 242) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((6335 / 9196) : ℂ) - ((821 / 2299) : ℂ) * ζ ^ 2 + ((6335 / 9196) : ℂ) * ζ ^ 4 + ((955 / 2299) : ℂ) * ζ ^ 6 + ((2276 / 2299) : ℂ) * ζ ^ 8 + ((254 / 2299) : ℂ) * ζ ^ 10 - ((12845 / 9196) : ℂ) * ζ ^ 12 - ((197 / 4598) : ℂ) * ζ ^ 14 + ((75 / 2299) : ℂ) * ζ ^ 16 + ((1424 / 2299) : ℂ) * ζ ^ 18 - ((3285 / 9196) : ℂ) * ζ ^ 20 - ((215 / 2299) : ℂ) * ζ ^ 22 - ((12545 / 9196) : ℂ) * ζ ^ 24 + ((559 / 4598) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY45_combinationStep09
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 4 5) = 0 := by
  have previous :=
    row17_reducedY45_combinationStep08 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation25
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((26 / 19) : ℂ) + ((14 / 19) : ℂ) * ζ ^ 2 + ((44 / 19) : ℂ) * ζ ^ 6 - ((14 / 19) : ℂ) * ζ ^ 8 + ((10 / 19) : ℂ) * ζ ^ 12 + ((10 / 19) : ℂ) * ζ ^ 18 - ((14 / 19) : ℂ) * ζ ^ 22 + ((44 / 19) : ℂ) * ζ ^ 24 + ((14 / 19) : ℂ) * ζ ^ 28 + ((26 / 19) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((25 / 209) : ℂ) - ((81 / 418) : ℂ) * ζ ^ 2 - ((3 / 22) : ℂ) * ζ ^ 4 + ((137 / 209) : ℂ) * ζ ^ 6 + ((20 / 209) : ℂ) * ζ ^ 8 - ((239 / 418) : ℂ) * ζ ^ 10 - ((73 / 418) : ℂ) * ζ ^ 12 + ((45 / 418) : ℂ) * ζ ^ 14 + ((1 / 11) : ℂ) * ζ ^ 16 - ((86 / 209) : ℂ) * ζ ^ 18 + ((12 / 209) : ℂ) * ζ ^ 20 + ((207 / 418) : ℂ) * ζ ^ 22 - ((53 / 209) : ℂ) * ζ ^ 24 - ((5 / 209) : ℂ) * ζ ^ 26 + ((39 / 209) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((((65 / 209) : ℂ) - ((13 / 19) : ℂ) * ζ ^ 2 - ((123 / 418) : ℂ) * ζ ^ 4 + ((148 / 209) : ℂ) * ζ ^ 6 - ((53 / 418) : ℂ) * ζ ^ 8 - ((162 / 209) : ℂ) * ζ ^ 10 + ((255 / 418) : ℂ) * ζ ^ 12 - ((9 / 19) : ℂ) * ζ ^ 14 - ((227 / 418) : ℂ) * ζ ^ 16 - ((29 / 418) : ℂ) * ζ ^ 18 + ((3 / 19) : ℂ) * ζ ^ 20 + ((1 / 418) : ℂ) * ζ ^ 22 + ((9 / 38) : ℂ) * ζ ^ 24 - ((3 / 418) : ℂ) * ζ ^ 26 - ((39 / 209) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((100 / 209) : ℂ) + ((85 / 209) : ℂ) * ζ ^ 2 + ((6 / 11) : ℂ) * ζ ^ 4 - ((51 / 418) : ℂ) * ζ ^ 6 + ((162 / 209) : ℂ) * ζ ^ 8 + ((71 / 209) : ℂ) * ζ ^ 10 - ((371 / 209) : ℂ) * ζ ^ 12 + ((205 / 418) : ℂ) * ζ ^ 14 + ((651 / 418) : ℂ) * ζ ^ 16 - ((599 / 418) : ℂ) * ζ ^ 18 - ((48 / 209) : ℂ) * ζ ^ 20 + ((345 / 209) : ℂ) * ζ ^ 22 - ((379 / 418) : ℂ) * ζ ^ 24 - ((81 / 418) : ℂ) * ζ ^ 26 + ((130 / 209) : ℂ) * ζ ^ 28)) * Y 4 5
        + ((-((25 / 209) : ℂ) + ((81 / 418) : ℂ) * ζ ^ 2 + ((3 / 22) : ℂ) * ζ ^ 4 - ((137 / 209) : ℂ) * ζ ^ 6 - ((20 / 209) : ℂ) * ζ ^ 8 + ((239 / 418) : ℂ) * ζ ^ 10 + ((73 / 418) : ℂ) * ζ ^ 12 - ((45 / 418) : ℂ) * ζ ^ 14 - ((1 / 11) : ℂ) * ζ ^ 16 + ((86 / 209) : ℂ) * ζ ^ 18 - ((12 / 209) : ℂ) * ζ ^ 20 - ((207 / 418) : ℂ) * ζ ^ 22 + ((53 / 209) : ℂ) * ζ ^ 24 + ((5 / 209) : ℂ) * ζ ^ 26 - ((39 / 209) : ℂ) * ζ ^ 28)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY45
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 4 5 = 0 := by
  have reduced :=
    row17_reducedY45_combinationStep09 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row17_reducedY54_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((1513 / 418) : ℂ) + ((90 / 11) : ℂ) * ζ ^ 2 + ((2005 / 418) : ℂ) * ζ ^ 6 - ((7593 / 836) : ℂ) * ζ ^ 8 - ((3581 / 836) : ℂ) * ζ ^ 12 - ((4765 / 836) : ℂ) * ζ ^ 18 - ((90 / 11) : ℂ) * ζ ^ 22 + ((2601 / 418) : ℂ) * ζ ^ 24 + ((7593 / 836) : ℂ) * ζ ^ 28 + ((4181 / 836) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((971 / 836) : ℂ) - ((117 / 209) : ℂ) * ζ ^ 2 - ((695 / 418) : ℂ) * ζ ^ 6 + ((1091 / 836) : ℂ) * ζ ^ 8 + ((276 / 209) : ℂ) * ζ ^ 12 - ((31 / 44) : ℂ) * ζ ^ 18 + ((117 / 209) : ℂ) * ζ ^ 22 - ((205 / 418) : ℂ) * ζ ^ 24 - ((1091 / 836) : ℂ) * ζ ^ 28 + ((51 / 418) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((((2075 / 209) : ℂ) + ((1 / 11) : ℂ) * ζ ^ 2 - ((1960 / 209) : ℂ) * ζ ^ 6 + ((397 / 209) : ℂ) * ζ ^ 8 + ((1091 / 209) : ℂ) * ζ ^ 12 - ((487 / 209) : ℂ) * ζ ^ 18 - ((1 / 11) : ℂ) * ζ ^ 22 + ((1665 / 209) : ℂ) * ζ ^ 24 - ((397 / 209) : ℂ) * ζ ^ 28 - ((1390 / 209) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((951 / 836) : ℂ) - ((359 / 44) : ℂ) * ζ ^ 2 + ((951 / 836) : ℂ) * ζ ^ 4 + ((851 / 836) : ℂ) * ζ ^ 6 + ((37 / 38) : ℂ) * ζ ^ 8 - ((227 / 209) : ℂ) * ζ ^ 10 + ((7057 / 836) : ℂ) * ζ ^ 12 + ((5 / 836) : ℂ) * ζ ^ 14 - ((2062 / 209) : ℂ) * ζ ^ 16 - ((5617 / 836) : ℂ) * ζ ^ 18 + ((6583 / 836) : ℂ) * ζ ^ 20 + ((1390 / 209) : ℂ) * ζ ^ 22 - ((1191 / 836) : ℂ) * ζ ^ 24 - ((2085 / 418) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((971 / 836) : ℂ) + ((117 / 209) : ℂ) * ζ ^ 2 + ((971 / 836) : ℂ) * ζ ^ 4 + ((461 / 418) : ℂ) * ζ ^ 6 - ((1031 / 418) : ℂ) * ζ ^ 8 - ((461 / 418) : ℂ) * ζ ^ 10 + ((1031 / 418) : ℂ) * ζ ^ 12 + ((1409 / 836) : ℂ) * ζ ^ 14 - ((1031 / 418) : ℂ) * ζ ^ 16 - ((695 / 418) : ℂ) * ζ ^ 18 + ((397 / 836) : ℂ) * ζ ^ 20 + ((695 / 418) : ℂ) * ζ ^ 22)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY54_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((375 / 418) : ℂ) - ((79 / 209) : ℂ) * ζ ^ 2 + ((309 / 418) : ℂ) * ζ ^ 6 + ((479 / 836) : ℂ) * ζ ^ 8 - ((153 / 836) : ℂ) * ζ ^ 12 + ((223 / 836) : ℂ) * ζ ^ 18 + ((79 / 209) : ℂ) * ζ ^ 22 - ((1143 / 418) : ℂ) * ζ ^ 24 - ((479 / 836) : ℂ) * ζ ^ 28 + ((1445 / 836) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((2701 / 836) : ℂ) - ((1779 / 836) : ℂ) * ζ ^ 2 - ((115 / 209) : ℂ) * ζ ^ 6 + ((4143 / 836) : ℂ) * ζ ^ 8 + ((2291 / 836) : ℂ) * ζ ^ 12 + ((927 / 836) : ℂ) * ζ ^ 18 + ((1779 / 836) : ℂ) * ζ ^ 22 - ((3921 / 836) : ℂ) * ζ ^ 24 - ((4143 / 836) : ℂ) * ζ ^ 28 + ((562 / 209) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((971 / 836) : ℂ) - ((117 / 209) : ℂ) * ζ ^ 2 - ((695 / 418) : ℂ) * ζ ^ 6 + ((1091 / 836) : ℂ) * ζ ^ 8 + ((276 / 209) : ℂ) * ζ ^ 12 - ((31 / 44) : ℂ) * ζ ^ 18 + ((117 / 209) : ℂ) * ζ ^ 22 - ((205 / 418) : ℂ) * ζ ^ 24 - ((1091 / 836) : ℂ) * ζ ^ 28 + ((51 / 418) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((375 / 418) : ℂ) + ((79 / 209) : ℂ) * ζ ^ 2 - ((309 / 418) : ℂ) * ζ ^ 6 - ((479 / 836) : ℂ) * ζ ^ 8 + ((153 / 836) : ℂ) * ζ ^ 12 - ((223 / 836) : ℂ) * ζ ^ 18 - ((79 / 209) : ℂ) * ζ ^ 22 + ((1143 / 418) : ℂ) * ζ ^ 24 + ((479 / 836) : ℂ) * ζ ^ 28 - ((1445 / 836) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY54_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((903 / 209) : ℂ) + ((1984 / 209) : ℂ) * ζ ^ 2 + ((1143 / 209) : ℂ) * ζ ^ 6 - ((2918 / 209) : ℂ) * ζ ^ 8 - ((479 / 209) : ℂ) * ζ ^ 12 - ((1668 / 209) : ℂ) * ζ ^ 18 - ((1984 / 209) : ℂ) * ζ ^ 22 + ((3189 / 209) : ℂ) * ζ ^ 24 + ((2918 / 209) : ℂ) * ζ ^ 28 - ((618 / 209) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((375 / 418) : ℂ) + ((79 / 209) : ℂ) * ζ ^ 2 - ((375 / 418) : ℂ) * ζ ^ 4 - ((467 / 418) : ℂ) * ζ ^ 6 + ((271 / 836) : ℂ) * ζ ^ 8 + ((467 / 418) : ℂ) * ζ ^ 10 - ((271 / 836) : ℂ) * ζ ^ 12 - ((1301 / 418) : ℂ) * ζ ^ 14 + ((271 / 836) : ℂ) * ζ ^ 16 + ((309 / 418) : ℂ) * ζ ^ 18 + ((1459 / 418) : ℂ) * ζ ^ 20 - ((309 / 418) : ℂ) * ζ ^ 22)) * Y 0 0
        + ((((3315 / 418) : ℂ) + ((10603 / 836) : ℂ) * ζ ^ 2 - ((3315 / 418) : ℂ) * ζ ^ 4 - ((2495 / 418) : ℂ) * ζ ^ 6 - ((10733 / 836) : ℂ) * ζ ^ 8 - ((481 / 418) : ℂ) * ζ ^ 10 + ((919 / 76) : ℂ) * ζ ^ 12 + ((1538 / 209) : ℂ) * ζ ^ 14 - ((1355 / 836) : ℂ) * ζ ^ 16 - ((411 / 38) : ℂ) * ζ ^ 18 - ((5023 / 836) : ℂ) * ζ ^ 20 + ((1545 / 418) : ℂ) * ζ ^ 22 + ((4377 / 418) : ℂ) * ζ ^ 24 - ((927 / 418) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((375 / 418) : ℂ) - ((79 / 209) : ℂ) * ζ ^ 2 + ((375 / 418) : ℂ) * ζ ^ 4 + ((467 / 418) : ℂ) * ζ ^ 6 - ((271 / 836) : ℂ) * ζ ^ 8 - ((467 / 418) : ℂ) * ζ ^ 10 + ((271 / 836) : ℂ) * ζ ^ 12 + ((1301 / 418) : ℂ) * ζ ^ 14 - ((271 / 836) : ℂ) * ζ ^ 16 - ((309 / 418) : ℂ) * ζ ^ 18 - ((1459 / 418) : ℂ) * ζ ^ 20 + ((309 / 418) : ℂ) * ζ ^ 22)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY54_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((34120 / 25707) : ℂ) - ((32311 / 51414) : ℂ) * ζ ^ 2 - ((2425 / 25707) : ℂ) * ζ ^ 6 + ((33047 / 34276) : ℂ) * ζ ^ 8 + ((2965 / 34276) : ℂ) * ζ ^ 12 + ((160361 / 102828) : ℂ) * ζ ^ 18 + ((32311 / 51414) : ℂ) * ζ ^ 22 - ((25110 / 8569) : ℂ) * ζ ^ 24 - ((33047 / 34276) : ℂ) * ζ ^ 28 + ((141343 / 102828) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((76517 / 34276) : ℂ) - ((91491 / 34276) : ℂ) * ζ ^ 2 - ((15085 / 51414) : ℂ) * ζ ^ 6 + ((167577 / 34276) : ℂ) * ζ ^ 8 + ((220601 / 102828) : ℂ) * ζ ^ 12 + ((31547 / 102828) : ℂ) * ζ ^ 18 + ((91491 / 34276) : ℂ) * ζ ^ 22 - ((487231 / 102828) : ℂ) * ζ ^ 24 - ((167577 / 34276) : ℂ) * ζ ^ 28 + ((47395 / 25707) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((971 / 836) : ℂ) - ((117 / 209) : ℂ) * ζ ^ 2 - ((695 / 418) : ℂ) * ζ ^ 6 + ((1091 / 836) : ℂ) * ζ ^ 8 + ((276 / 209) : ℂ) * ζ ^ 12 - ((31 / 44) : ℂ) * ζ ^ 18 + ((117 / 209) : ℂ) * ζ ^ 22 - ((205 / 418) : ℂ) * ζ ^ 24 - ((1091 / 836) : ℂ) * ζ ^ 28 + ((51 / 418) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((375 / 418) : ℂ) + ((79 / 209) : ℂ) * ζ ^ 2 - ((309 / 418) : ℂ) * ζ ^ 6 - ((479 / 836) : ℂ) * ζ ^ 8 + ((153 / 836) : ℂ) * ζ ^ 12 - ((223 / 836) : ℂ) * ζ ^ 18 - ((79 / 209) : ℂ) * ζ ^ 22 + ((1143 / 418) : ℂ) * ζ ^ 24 + ((479 / 836) : ℂ) * ζ ^ 28 - ((1445 / 836) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((22115 / 51414) : ℂ) + ((12877 / 51414) : ℂ) * ζ ^ 2 + ((42857 / 51414) : ℂ) * ζ ^ 6 - ((3352 / 8569) : ℂ) * ζ ^ 8 - ((4619 / 17138) : ℂ) * ζ ^ 12 - ((33233 / 25707) : ℂ) * ζ ^ 18 - ((12877 / 51414) : ℂ) * ζ ^ 22 + ((3357 / 17138) : ℂ) * ζ ^ 24 + ((3352 / 8569) : ℂ) * ζ ^ 28 + ((9098 / 25707) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((379 / 2706) : ℂ) + ((139 / 902) : ℂ) * ζ ^ 2 - ((1093 / 1353) : ℂ) * ζ ^ 6 - ((250 / 451) : ℂ) * ζ ^ 8 + ((623 / 1353) : ℂ) * ζ ^ 12 + ((2749 / 2706) : ℂ) * ζ ^ 18 - ((139 / 902) : ℂ) * ζ ^ 22 + ((454 / 1353) : ℂ) * ζ ^ 24 + ((250 / 451) : ℂ) * ζ ^ 28 - ((2711 / 2706) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have previous :=
    row17_reducedY54_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation02
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((1328 / 627) : ℂ) + ((2 / 33) : ℂ) * ζ ^ 2 + ((524 / 627) : ℂ) * ζ ^ 6 - ((272 / 209) : ℂ) * ζ ^ 8 - ((280 / 209) : ℂ) * ζ ^ 12 - ((112 / 209) : ℂ) * ζ ^ 18 - ((2 / 33) : ℂ) * ζ ^ 22 - ((1526 / 627) : ℂ) * ζ ^ 24 + ((272 / 209) : ℂ) * ζ ^ 28 + ((694 / 209) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((27427 / 51414) : ℂ) + ((27637 / 51414) : ℂ) * ζ ^ 2 - ((9003 / 17138) : ℂ) * ζ ^ 4 + ((3550 / 8569) : ℂ) * ζ ^ 6 + ((1549 / 2706) : ℂ) * ζ ^ 8 - ((4951 / 8569) : ℂ) * ζ ^ 10 - ((65 / 902) : ℂ) * ζ ^ 12 + ((26957 / 25707) : ℂ) * ζ ^ 14 - ((8117 / 51414) : ℂ) * ζ ^ 16 - ((57853 / 51414) : ℂ) * ζ ^ 18 + ((6722 / 25707) : ℂ) * ζ ^ 20 + ((49447 / 51414) : ℂ) * ζ ^ 22 - ((1346 / 8569) : ℂ) * ζ ^ 24 - ((5477 / 8569) : ℂ) * ζ ^ 26 - ((694 / 8569) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((26332 / 25707) : ℂ) - ((21961 / 25707) : ℂ) * ζ ^ 2 + ((25306 / 25707) : ℂ) * ζ ^ 4 - ((11639 / 51414) : ℂ) * ζ ^ 6 - ((74450 / 25707) : ℂ) * ζ ^ 8 + ((17871 / 17138) : ℂ) * ζ ^ 10 + ((2729 / 2337) : ℂ) * ζ ^ 12 - ((9459 / 8569) : ℂ) * ζ ^ 14 - ((8605 / 25707) : ℂ) * ζ ^ 16 + ((9946 / 8569) : ℂ) * ζ ^ 18 - ((18839 / 25707) : ℂ) * ζ ^ 20 - ((8851 / 25707) : ℂ) * ζ ^ 22 + ((14420 / 8569) : ℂ) * ζ ^ 24 + ((16365 / 8569) : ℂ) * ζ ^ 26 - ((6940 / 8569) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((27427 / 51414) : ℂ) - ((27637 / 51414) : ℂ) * ζ ^ 2 + ((9003 / 17138) : ℂ) * ζ ^ 4 - ((3550 / 8569) : ℂ) * ζ ^ 6 - ((1549 / 2706) : ℂ) * ζ ^ 8 + ((4951 / 8569) : ℂ) * ζ ^ 10 + ((65 / 902) : ℂ) * ζ ^ 12 - ((26957 / 25707) : ℂ) * ζ ^ 14 + ((8117 / 51414) : ℂ) * ζ ^ 16 + ((57853 / 51414) : ℂ) * ζ ^ 18 - ((6722 / 25707) : ℂ) * ζ ^ 20 - ((49447 / 51414) : ℂ) * ζ ^ 22 + ((1346 / 8569) : ℂ) * ζ ^ 24 + ((5477 / 8569) : ℂ) * ζ ^ 26 + ((694 / 8569) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((15833 / 51414) : ℂ) + ((7867 / 25707) : ℂ) * ζ ^ 2 + ((16517 / 51414) : ℂ) * ζ ^ 4 + ((18169 / 25707) : ℂ) * ζ ^ 6 + ((7065 / 8569) : ℂ) * ζ ^ 8 - ((1533 / 1558) : ℂ) * ζ ^ 10 - ((20989 / 17138) : ℂ) * ζ ^ 12 + ((48889 / 51414) : ℂ) * ζ ^ 14 + ((18089 / 17138) : ℂ) * ζ ^ 16 - ((6322 / 8569) : ℂ) * ζ ^ 18 - ((31379 / 51414) : ℂ) * ζ ^ 20 + ((23681 / 51414) : ℂ) * ζ ^ 22 + ((865 / 8569) : ℂ) * ζ ^ 24 - ((9885 / 17138) : ℂ) * ζ ^ 26 - ((2429 / 8569) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY54_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((795 / 418) : ℂ) - ((17 / 38) : ℂ) * ζ ^ 2 + ((51 / 38) : ℂ) * ζ ^ 6 + ((1085 / 836) : ℂ) * ζ ^ 8 - ((63 / 836) : ℂ) * ζ ^ 12 + ((43 / 76) : ℂ) * ζ ^ 18 + ((17 / 38) : ℂ) * ζ ^ 22 - ((675 / 209) : ℂ) * ζ ^ 24 - ((1085 / 836) : ℂ) * ζ ^ 28 + ((105 / 76) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((101 / 836) : ℂ) - ((191 / 76) : ℂ) * ζ ^ 2 - ((71 / 38) : ℂ) * ζ ^ 6 + ((3911 / 836) : ℂ) * ζ ^ 8 + ((1123 / 836) : ℂ) * ζ ^ 12 + ((117 / 76) : ℂ) * ζ ^ 18 + ((191 / 76) : ℂ) * ζ ^ 22 - ((3243 / 836) : ℂ) * ζ ^ 24 - ((3911 / 836) : ℂ) * ζ ^ 28 + ((45 / 38) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((971 / 836) : ℂ) - ((117 / 209) : ℂ) * ζ ^ 2 - ((695 / 418) : ℂ) * ζ ^ 6 + ((1091 / 836) : ℂ) * ζ ^ 8 + ((276 / 209) : ℂ) * ζ ^ 12 - ((31 / 44) : ℂ) * ζ ^ 18 + ((117 / 209) : ℂ) * ζ ^ 22 - ((205 / 418) : ℂ) * ζ ^ 24 - ((1091 / 836) : ℂ) * ζ ^ 28 + ((51 / 418) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((375 / 418) : ℂ) + ((79 / 209) : ℂ) * ζ ^ 2 - ((309 / 418) : ℂ) * ζ ^ 6 - ((479 / 836) : ℂ) * ζ ^ 8 + ((153 / 836) : ℂ) * ζ ^ 12 - ((223 / 836) : ℂ) * ζ ^ 18 - ((79 / 209) : ℂ) * ζ ^ 22 + ((1143 / 418) : ℂ) * ζ ^ 24 + ((479 / 836) : ℂ) * ζ ^ 28 - ((1445 / 836) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((22115 / 51414) : ℂ) + ((12877 / 51414) : ℂ) * ζ ^ 2 + ((42857 / 51414) : ℂ) * ζ ^ 6 - ((3352 / 8569) : ℂ) * ζ ^ 8 - ((4619 / 17138) : ℂ) * ζ ^ 12 - ((33233 / 25707) : ℂ) * ζ ^ 18 - ((12877 / 51414) : ℂ) * ζ ^ 22 + ((3357 / 17138) : ℂ) * ζ ^ 24 + ((3352 / 8569) : ℂ) * ζ ^ 28 + ((9098 / 25707) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((5398 / 25707) : ℂ) - ((7631 / 51414) : ℂ) * ζ ^ 2 + ((14873 / 25707) : ℂ) * ζ ^ 6 + ((16678 / 25707) : ℂ) * ζ ^ 8 + ((20629 / 25707) : ℂ) * ζ ^ 12 - ((32491 / 51414) : ℂ) * ζ ^ 18 + ((7631 / 51414) : ℂ) * ζ ^ 22 - ((14735 / 51414) : ℂ) * ζ ^ 24 - ((16678 / 25707) : ℂ) * ζ ^ 28 - ((18751 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((379 / 2706) : ℂ) + ((139 / 902) : ℂ) * ζ ^ 2 - ((1093 / 1353) : ℂ) * ζ ^ 6 - ((250 / 451) : ℂ) * ζ ^ 8 + ((623 / 1353) : ℂ) * ζ ^ 12 + ((2749 / 2706) : ℂ) * ζ ^ 18 - ((139 / 902) : ℂ) * ζ ^ 22 + ((454 / 1353) : ℂ) * ζ ^ 24 + ((250 / 451) : ℂ) * ζ ^ 28 - ((2711 / 2706) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((1555 / 2706) : ℂ) - ((245 / 1353) : ℂ) * ζ ^ 2 - ((3887 / 2706) : ℂ) * ζ ^ 6 - ((301 / 902) : ℂ) * ζ ^ 8 + ((73 / 451) : ℂ) * ζ ^ 12 + ((2689 / 2706) : ℂ) * ζ ^ 18 + ((245 / 1353) : ℂ) * ζ ^ 22 + ((135 / 451) : ℂ) * ζ ^ 24 + ((301 / 902) : ℂ) * ζ ^ 28 - ((19 / 2706) : ℂ) * ζ ^ 30)) * Y 3 3) = 0 := by
  have previous :=
    row17_reducedY54_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation03
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((8 / 209) : ℂ) + ((1262 / 627) : ℂ) * ζ ^ 2 + ((724 / 627) : ℂ) * ζ ^ 6 - ((2602 / 627) : ℂ) * ζ ^ 8 + ((84 / 209) : ℂ) * ζ ^ 12 - ((32 / 33) : ℂ) * ζ ^ 18 - ((1262 / 627) : ℂ) * ζ ^ 22 - ((1234 / 627) : ℂ) * ζ ^ 24 + ((2602 / 627) : ℂ) * ζ ^ 28 + ((1756 / 627) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((29701 / 51414) : ℂ) - ((27 / 902) : ℂ) * ζ ^ 2 - ((52417 / 51414) : ℂ) * ζ ^ 4 - ((11310 / 8569) : ℂ) * ζ ^ 6 - ((4106 / 25707) : ℂ) * ζ ^ 8 + ((100183 / 51414) : ℂ) * ζ ^ 10 + ((40127 / 51414) : ℂ) * ζ ^ 12 - ((94835 / 51414) : ℂ) * ζ ^ 14 - ((16460 / 25707) : ℂ) * ζ ^ 16 + ((65321 / 51414) : ℂ) * ζ ^ 18 + ((5884 / 25707) : ℂ) * ζ ^ 20 - ((16499 / 25707) : ℂ) * ζ ^ 22 + ((5877 / 17138) : ℂ) * ζ ^ 24 + ((19204 / 25707) : ℂ) * ζ ^ 26 + ((6146 / 25707) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((-((18162 / 8569) : ℂ) - ((29371 / 51414) : ℂ) * ζ ^ 2 + ((38217 / 17138) : ℂ) * ζ ^ 4 + ((97981 / 51414) : ℂ) * ζ ^ 6 - ((19761 / 17138) : ℂ) * ζ ^ 8 - ((1509 / 779) : ℂ) * ζ ^ 10 - ((5001 / 17138) : ℂ) * ζ ^ 12 + ((9946 / 8569) : ℂ) * ζ ^ 14 - ((67 / 25707) : ℂ) * ζ ^ 16 - ((58181 / 51414) : ℂ) * ζ ^ 18 + ((5827 / 25707) : ℂ) * ζ ^ 20 + ((9428 / 8569) : ℂ) * ζ ^ 22 + ((128 / 25707) : ℂ) * ζ ^ 24 - ((22636 / 25707) : ℂ) * ζ ^ 26 - ((3512 / 8569) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((5350 / 25707) : ℂ) + ((773 / 17138) : ℂ) * ζ ^ 2 - ((4097 / 8569) : ℂ) * ζ ^ 4 - ((35033 / 51414) : ℂ) * ζ ^ 6 - ((1746 / 8569) : ℂ) * ζ ^ 8 + ((44725 / 51414) : ℂ) * ζ ^ 10 - ((3919 / 8569) : ℂ) * ζ ^ 12 - ((61483 / 51414) : ℂ) * ζ ^ 14 + ((24331 / 25707) : ℂ) * ζ ^ 16 + ((27559 / 25707) : ℂ) * ζ ^ 18 - ((54149 / 51414) : ℂ) * ζ ^ 20 - ((7571 / 8569) : ℂ) * ζ ^ 22 + ((17759 / 25707) : ℂ) * ζ ^ 24 + ((15772 / 25707) : ℂ) * ζ ^ 26 + ((1756 / 25707) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((29701 / 51414) : ℂ) + ((27 / 902) : ℂ) * ζ ^ 2 + ((52417 / 51414) : ℂ) * ζ ^ 4 + ((11310 / 8569) : ℂ) * ζ ^ 6 + ((4106 / 25707) : ℂ) * ζ ^ 8 - ((100183 / 51414) : ℂ) * ζ ^ 10 - ((40127 / 51414) : ℂ) * ζ ^ 12 + ((94835 / 51414) : ℂ) * ζ ^ 14 + ((16460 / 25707) : ℂ) * ζ ^ 16 - ((65321 / 51414) : ℂ) * ζ ^ 18 - ((5884 / 25707) : ℂ) * ζ ^ 20 + ((16499 / 25707) : ℂ) * ζ ^ 22 - ((5877 / 17138) : ℂ) * ζ ^ 24 - ((19204 / 25707) : ℂ) * ζ ^ 26 - ((6146 / 25707) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY54_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((971 / 836) : ℂ) - ((117 / 209) : ℂ) * ζ ^ 2 - ((695 / 418) : ℂ) * ζ ^ 6 + ((1091 / 836) : ℂ) * ζ ^ 8 + ((276 / 209) : ℂ) * ζ ^ 12 - ((31 / 44) : ℂ) * ζ ^ 18 + ((117 / 209) : ℂ) * ζ ^ 22 - ((205 / 418) : ℂ) * ζ ^ 24 - ((1091 / 836) : ℂ) * ζ ^ 28 + ((51 / 418) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((375 / 418) : ℂ) + ((79 / 209) : ℂ) * ζ ^ 2 - ((309 / 418) : ℂ) * ζ ^ 6 - ((479 / 836) : ℂ) * ζ ^ 8 + ((153 / 836) : ℂ) * ζ ^ 12 - ((223 / 836) : ℂ) * ζ ^ 18 - ((79 / 209) : ℂ) * ζ ^ 22 + ((1143 / 418) : ℂ) * ζ ^ 24 + ((479 / 836) : ℂ) * ζ ^ 28 - ((1445 / 836) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((22115 / 51414) : ℂ) + ((12877 / 51414) : ℂ) * ζ ^ 2 + ((42857 / 51414) : ℂ) * ζ ^ 6 - ((3352 / 8569) : ℂ) * ζ ^ 8 - ((4619 / 17138) : ℂ) * ζ ^ 12 - ((33233 / 25707) : ℂ) * ζ ^ 18 - ((12877 / 51414) : ℂ) * ζ ^ 22 + ((3357 / 17138) : ℂ) * ζ ^ 24 + ((3352 / 8569) : ℂ) * ζ ^ 28 + ((9098 / 25707) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((5398 / 25707) : ℂ) - ((7631 / 51414) : ℂ) * ζ ^ 2 + ((14873 / 25707) : ℂ) * ζ ^ 6 + ((16678 / 25707) : ℂ) * ζ ^ 8 + ((20629 / 25707) : ℂ) * ζ ^ 12 - ((32491 / 51414) : ℂ) * ζ ^ 18 + ((7631 / 51414) : ℂ) * ζ ^ 22 - ((14735 / 51414) : ℂ) * ζ ^ 24 - ((16678 / 25707) : ℂ) * ζ ^ 28 - ((18751 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((379 / 2706) : ℂ) + ((139 / 902) : ℂ) * ζ ^ 2 - ((1093 / 1353) : ℂ) * ζ ^ 6 - ((250 / 451) : ℂ) * ζ ^ 8 + ((623 / 1353) : ℂ) * ζ ^ 12 + ((2749 / 2706) : ℂ) * ζ ^ 18 - ((139 / 902) : ℂ) * ζ ^ 22 + ((454 / 1353) : ℂ) * ζ ^ 24 + ((250 / 451) : ℂ) * ζ ^ 28 - ((2711 / 2706) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((((1555 / 2706) : ℂ) - ((245 / 1353) : ℂ) * ζ ^ 2 - ((3887 / 2706) : ℂ) * ζ ^ 6 - ((301 / 902) : ℂ) * ζ ^ 8 + ((73 / 451) : ℂ) * ζ ^ 12 + ((2689 / 2706) : ℂ) * ζ ^ 18 + ((245 / 1353) : ℂ) * ζ ^ 22 + ((135 / 451) : ℂ) * ζ ^ 24 + ((301 / 902) : ℂ) * ζ ^ 28 - ((19 / 2706) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((-((795 / 418) : ℂ) - ((17 / 38) : ℂ) * ζ ^ 2 + ((51 / 38) : ℂ) * ζ ^ 6 + ((1085 / 836) : ℂ) * ζ ^ 8 - ((63 / 836) : ℂ) * ζ ^ 12 + ((43 / 76) : ℂ) * ζ ^ 18 + ((17 / 38) : ℂ) * ζ ^ 22 - ((675 / 209) : ℂ) * ζ ^ 24 - ((1085 / 836) : ℂ) * ζ ^ 28 + ((105 / 76) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((273 / 418) : ℂ) - ((63 / 38) : ℂ) * ζ ^ 2 - ((20 / 19) : ℂ) * ζ ^ 6 + ((2177 / 836) : ℂ) * ζ ^ 8 + ((1109 / 836) : ℂ) * ζ ^ 12 + ((91 / 76) : ℂ) * ζ ^ 18 + ((63 / 38) : ℂ) * ζ ^ 22 - ((827 / 418) : ℂ) * ζ ^ 24 - ((2177 / 836) : ℂ) * ζ ^ 28 - ((13 / 76) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY54_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((17 / 19) : ℂ) + ((70 / 57) : ℂ) * ζ ^ 2 + ((41 / 19) : ℂ) * ζ ^ 6 - ((46 / 57) : ℂ) * ζ ^ 8 - ((103 / 57) : ℂ) * ζ ^ 12 - ((34 / 57) : ℂ) * ζ ^ 18 - ((70 / 57) : ℂ) * ζ ^ 22 - ((5 / 3) : ℂ) * ζ ^ 24 + ((46 / 57) : ℂ) * ζ ^ 28 + ((128 / 57) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((591 / 418) : ℂ) - ((467 / 418) : ℂ) * ζ ^ 2 + ((591 / 418) : ℂ) * ζ ^ 4 + ((268 / 209) : ℂ) * ζ ^ 6 + ((169 / 836) : ℂ) * ζ ^ 8 - ((233 / 209) : ℂ) * ζ ^ 10 - ((233 / 836) : ℂ) * ζ ^ 12 - ((123 / 418) : ℂ) * ζ ^ 14 + ((141 / 836) : ℂ) * ζ ^ 16 + ((67 / 209) : ℂ) * ζ ^ 18 + ((36 / 209) : ℂ) * ζ ^ 20 - ((32 / 209) : ℂ) * ζ ^ 22 - ((23 / 209) : ℂ) * ζ ^ 24 - ((64 / 209) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((485 / 418) : ℂ) - ((3571 / 836) : ℂ) * ζ ^ 2 - ((485 / 418) : ℂ) * ζ ^ 4 - ((287 / 418) : ℂ) * ζ ^ 6 + ((2439 / 418) : ℂ) * ζ ^ 8 + ((476 / 209) : ℂ) * ζ ^ 10 - ((719 / 418) : ℂ) * ζ ^ 12 - ((1009 / 418) : ℂ) * ζ ^ 14 + ((141 / 209) : ℂ) * ζ ^ 16 + ((921 / 418) : ℂ) * ζ ^ 18 + ((1621 / 836) : ℂ) * ζ ^ 20 - ((128 / 209) : ℂ) * ζ ^ 22 - ((23 / 22) : ℂ) * ζ ^ 24 - ((32 / 11) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((591 / 418) : ℂ) + ((467 / 418) : ℂ) * ζ ^ 2 - ((591 / 418) : ℂ) * ζ ^ 4 - ((268 / 209) : ℂ) * ζ ^ 6 - ((169 / 836) : ℂ) * ζ ^ 8 + ((233 / 209) : ℂ) * ζ ^ 10 + ((233 / 836) : ℂ) * ζ ^ 12 + ((123 / 418) : ℂ) * ζ ^ 14 - ((141 / 836) : ℂ) * ζ ^ 16 - ((67 / 209) : ℂ) * ζ ^ 18 - ((36 / 209) : ℂ) * ζ ^ 20 + ((32 / 209) : ℂ) * ζ ^ 22 + ((23 / 209) : ℂ) * ζ ^ 24 + ((64 / 209) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((111 / 209) : ℂ) + ((763 / 418) : ℂ) * ζ ^ 2 - ((111 / 209) : ℂ) * ζ ^ 4 - ((100 / 209) : ℂ) * ζ ^ 6 - ((1519 / 836) : ℂ) * ζ ^ 8 - ((5 / 209) : ℂ) * ζ ^ 10 + ((699 / 836) : ℂ) * ζ ^ 12 + ((369 / 418) : ℂ) * ζ ^ 14 - ((423 / 836) : ℂ) * ζ ^ 16 - ((201 / 209) : ℂ) * ζ ^ 18 - ((108 / 209) : ℂ) * ζ ^ 20 + ((96 / 209) : ℂ) * ζ ^ 22 + ((69 / 209) : ℂ) * ζ ^ 24 + ((192 / 209) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY54_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((17847 / 34276) : ℂ) - ((46547 / 51414) : ℂ) * ζ ^ 2 - ((18950 / 8569) : ℂ) * ζ ^ 6 + ((149621 / 102828) : ℂ) * ζ ^ 8 + ((49813 / 25707) : ℂ) * ζ ^ 12 + ((269 / 1804) : ℂ) * ζ ^ 18 + ((46547 / 51414) : ℂ) * ζ ^ 22 - ((30515 / 25707) : ℂ) * ζ ^ 24 - ((149621 / 102828) : ℂ) * ζ ^ 28 - ((8777 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((62041 / 25707) : ℂ) + ((40429 / 51414) : ℂ) * ζ ^ 2 + ((791 / 51414) : ℂ) * ζ ^ 6 - ((17549 / 34276) : ℂ) * ζ ^ 8 - ((17971 / 34276) : ℂ) * ζ ^ 12 - ((106241 / 102828) : ℂ) * ζ ^ 18 - ((40429 / 51414) : ℂ) * ζ ^ 22 + ((57313 / 17138) : ℂ) * ζ ^ 24 + ((17549 / 34276) : ℂ) * ζ ^ 28 - ((111577 / 102828) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((227 / 209) : ℂ) - ((3 / 19) : ℂ) * ζ ^ 2 + ((3 / 38) : ℂ) * ζ ^ 6 - ((189 / 418) : ℂ) * ζ ^ 8 + ((183 / 418) : ℂ) * ζ ^ 12 - ((10 / 19) : ℂ) * ζ ^ 18 + ((3 / 19) : ℂ) * ζ ^ 22 - ((173 / 418) : ℂ) * ζ ^ 24 + ((189 / 418) : ℂ) * ζ ^ 28 - ((11 / 38) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((5398 / 25707) : ℂ) - ((7631 / 51414) : ℂ) * ζ ^ 2 + ((14873 / 25707) : ℂ) * ζ ^ 6 + ((16678 / 25707) : ℂ) * ζ ^ 8 + ((20629 / 25707) : ℂ) * ζ ^ 12 - ((32491 / 51414) : ℂ) * ζ ^ 18 + ((7631 / 51414) : ℂ) * ζ ^ 22 - ((14735 / 51414) : ℂ) * ζ ^ 24 - ((16678 / 25707) : ℂ) * ζ ^ 28 - ((18751 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((1555 / 2706) : ℂ) - ((245 / 1353) : ℂ) * ζ ^ 2 - ((3887 / 2706) : ℂ) * ζ ^ 6 - ((301 / 902) : ℂ) * ζ ^ 8 + ((73 / 451) : ℂ) * ζ ^ 12 + ((2689 / 2706) : ℂ) * ζ ^ 18 + ((245 / 1353) : ℂ) * ζ ^ 22 + ((135 / 451) : ℂ) * ζ ^ 24 + ((301 / 902) : ℂ) * ζ ^ 28 - ((19 / 2706) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((-((795 / 418) : ℂ) - ((17 / 38) : ℂ) * ζ ^ 2 + ((51 / 38) : ℂ) * ζ ^ 6 + ((1085 / 836) : ℂ) * ζ ^ 8 - ((63 / 836) : ℂ) * ζ ^ 12 + ((43 / 76) : ℂ) * ζ ^ 18 + ((17 / 38) : ℂ) * ζ ^ 22 - ((675 / 209) : ℂ) * ζ ^ 24 - ((1085 / 836) : ℂ) * ζ ^ 28 + ((105 / 76) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((273 / 418) : ℂ) - ((63 / 38) : ℂ) * ζ ^ 2 - ((20 / 19) : ℂ) * ζ ^ 6 + ((2177 / 836) : ℂ) * ζ ^ 8 + ((1109 / 836) : ℂ) * ζ ^ 12 + ((91 / 76) : ℂ) * ζ ^ 18 + ((63 / 38) : ℂ) * ζ ^ 22 - ((827 / 418) : ℂ) * ζ ^ 24 - ((2177 / 836) : ℂ) * ζ ^ 28 - ((13 / 76) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY54_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation12
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((8 / 33) : ℂ) + ((14 / 11) : ℂ) * ζ ^ 2 + ((28 / 33) : ℂ) * ζ ^ 6 - ((2 / 33) : ℂ) * ζ ^ 8 - ((16 / 11) : ℂ) * ζ ^ 12 - ((68 / 33) : ℂ) * ζ ^ 18 - ((14 / 11) : ℂ) * ζ ^ 22 - ((10 / 11) : ℂ) * ζ ^ 24 + ((2 / 33) : ℂ) * ζ ^ 28 + ((122 / 33) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((883 / 1353) : ℂ) + ((397 / 902) : ℂ) * ζ ^ 2 - ((652 / 1353) : ℂ) * ζ ^ 4 + ((215 / 1353) : ℂ) * ζ ^ 6 + ((722 / 1353) : ℂ) * ζ ^ 8 + ((89 / 1353) : ℂ) * ζ ^ 10 - ((686 / 1353) : ℂ) * ζ ^ 12 + ((670 / 1353) : ℂ) * ζ ^ 14 + ((2 / 3) : ℂ) * ζ ^ 16 - ((63 / 82) : ℂ) * ζ ^ 18 - ((1009 / 2706) : ℂ) * ζ ^ 20 + ((2687 / 2706) : ℂ) * ζ ^ 22 + ((107 / 1353) : ℂ) * ζ ^ 24 - ((917 / 1353) : ℂ) * ζ ^ 26 - ((122 / 1353) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((4111 / 2706) : ℂ) - ((1579 / 2706) : ℂ) * ζ ^ 2 + ((1843 / 2706) : ℂ) * ζ ^ 4 - ((743 / 2706) : ℂ) * ζ ^ 6 - ((5281 / 2706) : ℂ) * ζ ^ 8 - ((1459 / 2706) : ℂ) * ζ ^ 10 + ((971 / 1353) : ℂ) * ζ ^ 12 - ((311 / 1353) : ℂ) * ζ ^ 14 - ((50 / 33) : ℂ) * ζ ^ 16 + ((470 / 1353) : ℂ) * ζ ^ 18 + ((546 / 451) : ℂ) * ζ ^ 20 - ((1571 / 1353) : ℂ) * ζ ^ 22 + ((425 / 451) : ℂ) * ζ ^ 24 + ((3335 / 1353) : ℂ) * ζ ^ 26 - ((1220 / 1353) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((4111 / 2706) : ℂ) + ((1579 / 2706) : ℂ) * ζ ^ 2 - ((1843 / 2706) : ℂ) * ζ ^ 4 + ((743 / 2706) : ℂ) * ζ ^ 6 + ((5281 / 2706) : ℂ) * ζ ^ 8 + ((1459 / 2706) : ℂ) * ζ ^ 10 - ((971 / 1353) : ℂ) * ζ ^ 12 + ((311 / 1353) : ℂ) * ζ ^ 14 + ((50 / 33) : ℂ) * ζ ^ 16 - ((470 / 1353) : ℂ) * ζ ^ 18 - ((546 / 451) : ℂ) * ζ ^ 20 + ((1571 / 1353) : ℂ) * ζ ^ 22 - ((425 / 451) : ℂ) * ζ ^ 24 - ((3335 / 1353) : ℂ) * ζ ^ 26 + ((1220 / 1353) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((((515 / 2706) : ℂ) + ((365 / 902) : ℂ) * ζ ^ 2 - ((32 / 123) : ℂ) * ζ ^ 4 - ((2785 / 2706) : ℂ) * ζ ^ 6 - ((305 / 902) : ℂ) * ζ ^ 8 + ((1229 / 1353) : ℂ) * ζ ^ 10 + ((347 / 451) : ℂ) * ζ ^ 12 - ((289 / 1353) : ℂ) * ζ ^ 14 - ((5 / 6) : ℂ) * ζ ^ 16 + ((263 / 902) : ℂ) * ζ ^ 18 + ((419 / 902) : ℂ) * ζ ^ 20 - ((186 / 451) : ℂ) * ζ ^ 22 - ((724 / 1353) : ℂ) * ζ ^ 24 + ((500 / 1353) : ℂ) * ζ ^ 26 + ((244 / 451) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY54_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((971 / 836) : ℂ) - ((23 / 38) : ℂ) * ζ ^ 2 - ((39 / 38) : ℂ) * ζ ^ 6 + ((1091 / 836) : ℂ) * ζ ^ 8 + ((276 / 209) : ℂ) * ζ ^ 12 - ((1 / 4) : ℂ) * ζ ^ 18 + ((23 / 38) : ℂ) * ζ ^ 22 - ((205 / 418) : ℂ) * ζ ^ 24 - ((1091 / 836) : ℂ) * ζ ^ 28 - ((2 / 19) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((1249 / 418) : ℂ) + ((23 / 38) : ℂ) * ζ ^ 2 - ((27 / 19) : ℂ) * ζ ^ 6 - ((707 / 836) : ℂ) * ζ ^ 8 - ((303 / 836) : ℂ) * ζ ^ 12 - ((3 / 76) : ℂ) * ζ ^ 18 - ((23 / 38) : ℂ) * ζ ^ 22 + ((1523 / 418) : ℂ) * ζ ^ 24 + ((707 / 836) : ℂ) * ζ ^ 28 - ((83 / 76) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((227 / 209) : ℂ) - ((3 / 19) : ℂ) * ζ ^ 2 + ((3 / 38) : ℂ) * ζ ^ 6 - ((189 / 418) : ℂ) * ζ ^ 8 + ((183 / 418) : ℂ) * ζ ^ 12 - ((10 / 19) : ℂ) * ζ ^ 18 + ((3 / 19) : ℂ) * ζ ^ 22 - ((173 / 418) : ℂ) * ζ ^ 24 + ((189 / 418) : ℂ) * ζ ^ 28 - ((11 / 38) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((452 / 209) : ℂ) - ((109 / 418) : ℂ) * ζ ^ 2 - ((421 / 418) : ℂ) * ζ ^ 6 + ((179 / 209) : ℂ) * ζ ^ 8 + ((105 / 209) : ℂ) * ζ ^ 12 - ((549 / 418) : ℂ) * ζ ^ 18 + ((109 / 418) : ℂ) * ζ ^ 22 - ((493 / 418) : ℂ) * ζ ^ 24 - ((179 / 209) : ℂ) * ζ ^ 28 - ((479 / 418) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((795 / 418) : ℂ) - ((17 / 38) : ℂ) * ζ ^ 2 + ((51 / 38) : ℂ) * ζ ^ 6 + ((1085 / 836) : ℂ) * ζ ^ 8 - ((63 / 836) : ℂ) * ζ ^ 12 + ((43 / 76) : ℂ) * ζ ^ 18 + ((17 / 38) : ℂ) * ζ ^ 22 - ((675 / 209) : ℂ) * ζ ^ 24 - ((1085 / 836) : ℂ) * ζ ^ 28 + ((105 / 76) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((273 / 418) : ℂ) - ((63 / 38) : ℂ) * ζ ^ 2 - ((20 / 19) : ℂ) * ζ ^ 6 + ((2177 / 836) : ℂ) * ζ ^ 8 + ((1109 / 836) : ℂ) * ζ ^ 12 + ((91 / 76) : ℂ) * ζ ^ 18 + ((63 / 38) : ℂ) * ζ ^ 22 - ((827 / 418) : ℂ) * ζ ^ 24 - ((2177 / 836) : ℂ) * ζ ^ 28 - ((13 / 76) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY54_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation13
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((10 / 11) : ℂ) + ((62 / 33) : ℂ) * ζ ^ 2 + ((56 / 33) : ℂ) * ζ ^ 6 - ((14 / 11) : ℂ) * ζ ^ 8 + ((4 / 33) : ℂ) * ζ ^ 12 - ((38 / 11) : ℂ) * ζ ^ 18 - ((62 / 33) : ℂ) * ζ ^ 22 - ((58 / 33) : ℂ) * ζ ^ 24 + ((14 / 11) : ℂ) * ζ ^ 28 + ((68 / 33) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((643 / 902) : ℂ) + ((131 / 2706) : ℂ) * ζ ^ 2 + ((271 / 902) : ℂ) * ζ ^ 4 - ((2659 / 2706) : ℂ) * ζ ^ 6 - ((997 / 1353) : ℂ) * ζ ^ 8 + ((1351 / 1353) : ℂ) * ζ ^ 10 + ((1 / 2) : ℂ) * ζ ^ 12 - ((1609 / 1353) : ℂ) * ζ ^ 14 - ((331 / 451) : ℂ) * ζ ^ 16 + ((327 / 902) : ℂ) * ζ ^ 18 + ((226 / 1353) : ℂ) * ζ ^ 20 - ((469 / 1353) : ℂ) * ζ ^ 22 + ((7 / 2706) : ℂ) * ζ ^ 24 + ((538 / 1353) : ℂ) * ζ ^ 26 + ((238 / 1353) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((95 / 246) : ℂ) - ((233 / 902) : ℂ) * ζ ^ 2 + ((662 / 1353) : ℂ) * ζ ^ 4 + ((3709 / 2706) : ℂ) * ζ ^ 6 + ((25 / 451) : ℂ) * ζ ^ 8 - ((567 / 451) : ℂ) * ζ ^ 10 - ((31 / 66) : ℂ) * ζ ^ 12 + ((1048 / 1353) : ℂ) * ζ ^ 14 + ((607 / 1353) : ℂ) * ζ ^ 16 - ((1301 / 2706) : ℂ) * ζ ^ 18 + ((169 / 1353) : ℂ) * ζ ^ 20 + ((268 / 451) : ℂ) * ζ ^ 22 + ((80 / 451) : ℂ) * ζ ^ 24 - ((524 / 1353) : ℂ) * ζ ^ 26 - ((136 / 451) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((2627 / 1353) : ℂ) - ((19 / 41) : ℂ) * ζ ^ 2 - ((953 / 1353) : ℂ) * ζ ^ 4 + ((776 / 451) : ℂ) * ζ ^ 6 + ((1543 / 902) : ℂ) * ζ ^ 8 - ((1757 / 1353) : ℂ) * ζ ^ 10 + ((25 / 33) : ℂ) * ζ ^ 12 + ((3310 / 1353) : ℂ) * ζ ^ 14 - ((46 / 123) : ℂ) * ζ ^ 16 + ((47 / 123) : ℂ) * ζ ^ 18 + ((470 / 1353) : ℂ) * ζ ^ 20 + ((18 / 451) : ℂ) * ζ ^ 22 - ((1835 / 1353) : ℂ) * ζ ^ 24 - ((1450 / 1353) : ℂ) * ζ ^ 26 + ((680 / 1353) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((((95 / 246) : ℂ) + ((233 / 902) : ℂ) * ζ ^ 2 - ((662 / 1353) : ℂ) * ζ ^ 4 - ((3709 / 2706) : ℂ) * ζ ^ 6 - ((25 / 451) : ℂ) * ζ ^ 8 + ((567 / 451) : ℂ) * ζ ^ 10 + ((31 / 66) : ℂ) * ζ ^ 12 - ((1048 / 1353) : ℂ) * ζ ^ 14 - ((607 / 1353) : ℂ) * ζ ^ 16 + ((1301 / 2706) : ℂ) * ζ ^ 18 - ((169 / 1353) : ℂ) * ζ ^ 20 - ((268 / 451) : ℂ) * ζ ^ 22 - ((80 / 451) : ℂ) * ζ ^ 24 + ((524 / 1353) : ℂ) * ζ ^ 26 + ((136 / 451) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY54_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((227 / 209) : ℂ) - ((3 / 19) : ℂ) * ζ ^ 2 + ((3 / 38) : ℂ) * ζ ^ 6 - ((189 / 418) : ℂ) * ζ ^ 8 + ((183 / 418) : ℂ) * ζ ^ 12 - ((10 / 19) : ℂ) * ζ ^ 18 + ((3 / 19) : ℂ) * ζ ^ 22 - ((173 / 418) : ℂ) * ζ ^ 24 + ((189 / 418) : ℂ) * ζ ^ 28 - ((11 / 38) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((452 / 209) : ℂ) - ((109 / 418) : ℂ) * ζ ^ 2 - ((421 / 418) : ℂ) * ζ ^ 6 + ((179 / 209) : ℂ) * ζ ^ 8 + ((105 / 209) : ℂ) * ζ ^ 12 - ((549 / 418) : ℂ) * ζ ^ 18 + ((109 / 418) : ℂ) * ζ ^ 22 - ((493 / 418) : ℂ) * ζ ^ 24 - ((179 / 209) : ℂ) * ζ ^ 28 - ((479 / 418) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((227 / 209) : ℂ) + ((3 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 + ((189 / 418) : ℂ) * ζ ^ 8 - ((183 / 418) : ℂ) * ζ ^ 12 + ((10 / 19) : ℂ) * ζ ^ 18 - ((3 / 19) : ℂ) * ζ ^ 22 + ((173 / 418) : ℂ) * ζ ^ 24 - ((189 / 418) : ℂ) * ζ ^ 28 + ((11 / 38) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((87 / 209) : ℂ) - ((6 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 - ((159 / 418) : ℂ) * ζ ^ 8 + ((155 / 418) : ℂ) * ζ ^ 12 + ((6 / 19) : ℂ) * ζ ^ 22 + ((145 / 418) : ℂ) * ζ ^ 24 + ((159 / 418) : ℂ) * ζ ^ 28 + ((7 / 38) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY54_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((55 / 57) : ℂ) - ((31 / 57) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 6 + ((35 / 19) : ℂ) * ζ ^ 8 + ((13 / 57) : ℂ) * ζ ^ 12 + ((31 / 57) : ℂ) * ζ ^ 18 + ((31 / 57) : ℂ) * ζ ^ 22 - ((61 / 57) : ℂ) * ζ ^ 24 - ((35 / 19) : ℂ) * ζ ^ 28 + ((10 / 57) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((531 / 836) : ℂ) - ((129 / 418) : ℂ) * ζ ^ 2 - ((531 / 836) : ℂ) * ζ ^ 4 + ((2 / 209) : ℂ) * ζ ^ 6 + ((223 / 209) : ℂ) * ζ ^ 8 - ((35 / 418) : ℂ) * ζ ^ 10 + ((127 / 418) : ℂ) * ζ ^ 12 - ((123 / 836) : ℂ) * ζ ^ 14 - ((1 / 19) : ℂ) * ζ ^ 16 - ((13 / 209) : ℂ) * ζ ^ 18 + ((227 / 836) : ℂ) * ζ ^ 20 - ((5 / 418) : ℂ) * ζ ^ 22 + ((105 / 418) : ℂ) * ζ ^ 24 - ((5 / 209) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((1343 / 836) : ℂ) + ((1157 / 836) : ℂ) * ζ ^ 2 - ((1343 / 836) : ℂ) * ζ ^ 4 - ((749 / 836) : ℂ) * ζ ^ 6 - ((131 / 209) : ℂ) * ζ ^ 8 + ((40 / 209) : ℂ) * ζ ^ 10 + ((2171 / 836) : ℂ) * ζ ^ 12 - ((943 / 836) : ℂ) * ζ ^ 14 - ((4 / 19) : ℂ) * ζ ^ 16 - ((549 / 836) : ℂ) * ζ ^ 18 + ((1579 / 836) : ℂ) * ζ ^ 20 - ((10 / 209) : ℂ) * ζ ^ 22 + ((105 / 44) : ℂ) * ζ ^ 24 - ((5 / 22) : ℂ) * ζ ^ 26)) * Y 1 1
        + ((-((1343 / 836) : ℂ) - ((1157 / 836) : ℂ) * ζ ^ 2 + ((1343 / 836) : ℂ) * ζ ^ 4 + ((749 / 836) : ℂ) * ζ ^ 6 + ((131 / 209) : ℂ) * ζ ^ 8 - ((40 / 209) : ℂ) * ζ ^ 10 - ((2171 / 836) : ℂ) * ζ ^ 12 + ((943 / 836) : ℂ) * ζ ^ 14 + ((4 / 19) : ℂ) * ζ ^ 16 + ((549 / 836) : ℂ) * ζ ^ 18 - ((1579 / 836) : ℂ) * ζ ^ 20 + ((10 / 209) : ℂ) * ζ ^ 22 - ((105 / 44) : ℂ) * ζ ^ 24 + ((5 / 22) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((1059 / 836) : ℂ) - ((1029 / 836) : ℂ) * ζ ^ 2 + ((1059 / 836) : ℂ) * ζ ^ 4 + ((443 / 836) : ℂ) * ζ ^ 6 + ((203 / 418) : ℂ) * ζ ^ 8 - ((10 / 209) : ℂ) * ζ ^ 10 - ((925 / 836) : ℂ) * ζ ^ 12 + ((123 / 836) : ℂ) * ζ ^ 14 - ((10 / 19) : ℂ) * ζ ^ 16 + ((503 / 836) : ℂ) * ζ ^ 18 + ((257 / 836) : ℂ) * ζ ^ 20 - ((25 / 209) : ℂ) * ζ ^ 22 - ((1365 / 836) : ℂ) * ζ ^ 24 + ((65 / 418) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY54_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY54_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation24
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((22 / 19) : ℂ) - ((74 / 19) : ℂ) * ζ ^ 2 - ((64 / 19) : ℂ) * ζ ^ 6 - (2 : ℂ) * ζ ^ 8 - ((50 / 19) : ℂ) * ζ ^ 12 + ((46 / 19) : ℂ) * ζ ^ 18 + ((74 / 19) : ℂ) * ζ ^ 22 + ((16 / 19) : ℂ) * ζ ^ 24 + (2 : ℂ) * ζ ^ 28 - ((34 / 19) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((238 / 209) : ℂ) - ((48 / 209) : ℂ) * ζ ^ 2 + ((312 / 209) : ℂ) * ζ ^ 4 + ((175 / 418) : ℂ) * ζ ^ 6 - ((83 / 209) : ℂ) * ζ ^ 8 + ((265 / 209) : ℂ) * ζ ^ 10 - ((4 / 19) : ℂ) * ζ ^ 12 - ((569 / 418) : ℂ) * ζ ^ 14 + ((559 / 418) : ℂ) * ζ ^ 16 - ((25 / 418) : ℂ) * ζ ^ 18 - ((41 / 19) : ℂ) * ζ ^ 20 + ((365 / 209) : ℂ) * ζ ^ 22 - ((17 / 418) : ℂ) * ζ ^ 24 - ((669 / 418) : ℂ) * ζ ^ 26 + ((170 / 209) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((353 / 209) : ℂ) + ((27 / 22) : ℂ) * ζ ^ 2 + ((279 / 209) : ℂ) * ζ ^ 4 - ((105 / 418) : ℂ) * ζ ^ 6 + ((755 / 418) : ℂ) * ζ ^ 8 - ((31 / 38) : ℂ) * ζ ^ 10 - ((203 / 209) : ℂ) * ζ ^ 12 - ((138 / 209) : ℂ) * ζ ^ 14 + ((34 / 209) : ℂ) * ζ ^ 16 - ((370 / 209) : ℂ) * ζ ^ 18 - ((178 / 209) : ℂ) * ζ ^ 20 + ((147 / 209) : ℂ) * ζ ^ 22 - ((112 / 209) : ℂ) * ζ ^ 24 + ((6 / 19) : ℂ) * ζ ^ 26 + ((17 / 209) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((((238 / 209) : ℂ) + ((48 / 209) : ℂ) * ζ ^ 2 - ((312 / 209) : ℂ) * ζ ^ 4 - ((175 / 418) : ℂ) * ζ ^ 6 + ((83 / 209) : ℂ) * ζ ^ 8 - ((265 / 209) : ℂ) * ζ ^ 10 + ((4 / 19) : ℂ) * ζ ^ 12 + ((569 / 418) : ℂ) * ζ ^ 14 - ((559 / 418) : ℂ) * ζ ^ 16 + ((25 / 418) : ℂ) * ζ ^ 18 + ((41 / 19) : ℂ) * ζ ^ 20 - ((365 / 209) : ℂ) * ζ ^ 22 + ((17 / 418) : ℂ) * ζ ^ 24 + ((669 / 418) : ℂ) * ζ ^ 26 - ((170 / 209) : ℂ) * ζ ^ 28)) * Y 4 4
        + ((-((89 / 209) : ℂ) + ((79 / 418) : ℂ) * ζ ^ 2 + ((141 / 418) : ℂ) * ζ ^ 4 + ((117 / 209) : ℂ) * ζ ^ 6 + ((172 / 209) : ℂ) * ζ ^ 8 - ((105 / 418) : ℂ) * ζ ^ 10 + ((7 / 38) : ℂ) * ζ ^ 12 + ((35 / 418) : ℂ) * ζ ^ 14 - ((1 / 11) : ℂ) * ζ ^ 16 - ((45 / 209) : ℂ) * ζ ^ 18 - ((11 / 19) : ℂ) * ζ ^ 20 + ((219 / 418) : ℂ) * ζ ^ 22 - ((13 / 209) : ℂ) * ζ ^ 24 - ((91 / 209) : ℂ) * ζ ^ 26 + ((51 / 209) : ℂ) * ζ ^ 28)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY54
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 5 4 = 0 := by
  have reduced :=
    row17_reducedY54_combinationStep08 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row17_reducedY55_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((254273 / 51414) : ℂ) - ((86873 / 51414) : ℂ) * ζ ^ 2 + ((669947 / 102828) : ℂ) * ζ ^ 6 + ((29173 / 25707) : ℂ) * ζ ^ 8 - ((40195 / 34276) : ℂ) * ζ ^ 12 + ((2469 / 1804) : ℂ) * ζ ^ 18 + ((86873 / 51414) : ℂ) * ζ ^ 22 - ((64478 / 25707) : ℂ) * ζ ^ 24 - ((29173 / 25707) : ℂ) * ζ ^ 28 + ((65633 / 25707) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((2988 / 8569) : ℂ) + ((23729 / 25707) : ℂ) * ζ ^ 2 + ((30847 / 34276) : ℂ) * ζ ^ 6 - ((27463 / 34276) : ℂ) * ζ ^ 8 + ((17 / 25707) : ℂ) * ζ ^ 12 - ((39070 / 25707) : ℂ) * ζ ^ 18 - ((23729 / 25707) : ℂ) * ζ ^ 22 + ((177863 / 102828) : ℂ) * ζ ^ 24 + ((27463 / 34276) : ℂ) * ζ ^ 28 - ((19357 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((((35924 / 25707) : ℂ) + ((122446 / 8569) : ℂ) * ζ ^ 2 + ((303599 / 25707) : ℂ) * ζ ^ 6 - ((260320 / 25707) : ℂ) * ζ ^ 8 - ((27463 / 8569) : ℂ) * ζ ^ 12 - ((14338 / 1353) : ℂ) * ζ ^ 18 - ((122446 / 8569) : ℂ) * ζ ^ 22 + ((213787 / 25707) : ℂ) * ζ ^ 24 + ((260320 / 25707) : ℂ) * ζ ^ 28 + ((30847 / 8569) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((90745 / 17138) : ℂ) + ((135271 / 25707) : ℂ) * ζ ^ 2 - ((90745 / 17138) : ℂ) * ζ ^ 4 - ((226858 / 25707) : ℂ) * ζ ^ 6 + ((2713 / 4674) : ℂ) * ζ ^ 8 - ((97291 / 51414) : ℂ) * ζ ^ 10 + ((1209 / 209) : ℂ) * ζ ^ 12 + ((186515 / 34276) : ℂ) * ζ ^ 14 + ((15511 / 8569) : ℂ) * ζ ^ 16 - ((2975 / 418) : ℂ) * ζ ^ 18 - ((399919 / 102828) : ℂ) * ζ ^ 20 - ((30847 / 8569) : ℂ) * ζ ^ 22 + ((65080 / 8569) : ℂ) * ζ ^ 24 + ((92541 / 34276) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((2988 / 8569) : ℂ) - ((23729 / 25707) : ℂ) * ζ ^ 2 + ((2988 / 8569) : ℂ) * ζ ^ 4 + ((125 / 5412) : ℂ) * ζ ^ 6 + ((15511 / 34276) : ℂ) * ζ ^ 8 - ((125 / 5412) : ℂ) * ζ ^ 10 - ((15511 / 34276) : ℂ) * ζ ^ 12 + ((4821 / 1804) : ℂ) * ζ ^ 14 + ((15511 / 34276) : ℂ) * ζ ^ 16 + ((30847 / 34276) : ℂ) * ζ ^ 18 - ((65080 / 25707) : ℂ) * ζ ^ 20 - ((30847 / 34276) : ℂ) * ζ ^ 22)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY55_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((18101 / 51414) : ℂ) - ((47979 / 17138) : ℂ) * ζ ^ 2 - ((208537 / 102828) : ℂ) * ζ ^ 6 + ((18868 / 8569) : ℂ) * ζ ^ 8 + ((129619 / 102828) : ℂ) * ζ ^ 12 + ((122393 / 102828) : ℂ) * ζ ^ 18 + ((47979 / 17138) : ℂ) * ζ ^ 22 - ((3651 / 8569) : ℂ) * ζ ^ 24 - ((18868 / 8569) : ℂ) * ζ ^ 28 - ((46909 / 25707) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((((74626 / 25707) : ℂ) - ((57329 / 17138) : ℂ) * ζ ^ 2 - ((394151 / 102828) : ℂ) * ζ ^ 6 + ((38257 / 51414) : ℂ) * ζ ^ 8 + ((95839 / 102828) : ℂ) * ζ ^ 12 + ((868 / 25707) : ℂ) * ζ ^ 18 + ((57329 / 17138) : ℂ) * ζ ^ 22 + ((186343 / 102828) : ℂ) * ζ ^ 24 - ((38257 / 51414) : ℂ) * ζ ^ 28 - ((275713 / 102828) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((2988 / 8569) : ℂ) + ((23729 / 25707) : ℂ) * ζ ^ 2 + ((30847 / 34276) : ℂ) * ζ ^ 6 - ((27463 / 34276) : ℂ) * ζ ^ 8 + ((17 / 25707) : ℂ) * ζ ^ 12 - ((39070 / 25707) : ℂ) * ζ ^ 18 - ((23729 / 25707) : ℂ) * ζ ^ 22 + ((177863 / 102828) : ℂ) * ζ ^ 24 + ((27463 / 34276) : ℂ) * ζ ^ 28 - ((19357 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((18101 / 51414) : ℂ) + ((47979 / 17138) : ℂ) * ζ ^ 2 + ((208537 / 102828) : ℂ) * ζ ^ 6 - ((18868 / 8569) : ℂ) * ζ ^ 8 - ((129619 / 102828) : ℂ) * ζ ^ 12 - ((122393 / 102828) : ℂ) * ζ ^ 18 - ((47979 / 17138) : ℂ) * ζ ^ 22 + ((3651 / 8569) : ℂ) * ζ ^ 24 + ((18868 / 8569) : ℂ) * ζ ^ 28 + ((46909 / 25707) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY55_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((31139 / 8569) : ℂ) + ((222631 / 25707) : ℂ) * ζ ^ 2 + ((102925 / 8569) : ℂ) * ζ ^ 6 - ((140609 / 25707) : ℂ) * ζ ^ 8 - ((75472 / 8569) : ℂ) * ζ ^ 12 + ((65243 / 25707) : ℂ) * ζ ^ 18 - ((222631 / 25707) : ℂ) * ζ ^ 22 - ((16535 / 8569) : ℂ) * ζ ^ 24 + ((140609 / 25707) : ℂ) * ζ ^ 28 + ((208537 / 25707) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((18101 / 51414) : ℂ) + ((47979 / 17138) : ℂ) * ζ ^ 2 - ((18101 / 51414) : ℂ) * ζ ^ 4 - ((79337 / 102828) : ℂ) * ζ ^ 6 - ((95107 / 51414) : ℂ) * ζ ^ 8 + ((79337 / 102828) : ℂ) * ζ ^ 10 + ((95107 / 51414) : ℂ) * ζ ^ 12 - ((2349 / 17138) : ℂ) * ζ ^ 14 - ((95107 / 51414) : ℂ) * ζ ^ 16 - ((208537 / 102828) : ℂ) * ζ ^ 18 + ((140609 / 102828) : ℂ) * ζ ^ 20 + ((208537 / 102828) : ℂ) * ζ ^ 22)) * Y 0 0
        + ((-((47393 / 5412) : ℂ) + ((130953 / 34276) : ℂ) * ζ ^ 2 + ((47393 / 5412) : ℂ) * ζ ^ 4 + ((490007 / 51414) : ℂ) * ζ ^ 6 - ((720647 / 102828) : ℂ) * ζ ^ 8 - ((1647907 / 102828) : ℂ) * ζ ^ 10 - ((48113 / 9348) : ℂ) * ζ ^ 12 + ((148635 / 17138) : ℂ) * ζ ^ 14 + ((475535 / 51414) : ℂ) * ζ ^ 16 + ((8518 / 2337) : ℂ) * ζ ^ 18 - ((212965 / 25707) : ℂ) * ζ ^ 20 - ((1042685 / 102828) : ℂ) * ζ ^ 22 + ((140609 / 34276) : ℂ) * ζ ^ 24 + ((208537 / 34276) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((18101 / 51414) : ℂ) - ((47979 / 17138) : ℂ) * ζ ^ 2 + ((18101 / 51414) : ℂ) * ζ ^ 4 + ((79337 / 102828) : ℂ) * ζ ^ 6 + ((95107 / 51414) : ℂ) * ζ ^ 8 - ((79337 / 102828) : ℂ) * ζ ^ 10 - ((95107 / 51414) : ℂ) * ζ ^ 12 + ((2349 / 17138) : ℂ) * ζ ^ 14 + ((95107 / 51414) : ℂ) * ζ ^ 16 + ((208537 / 102828) : ℂ) * ζ ^ 18 - ((140609 / 102828) : ℂ) * ζ ^ 20 - ((208537 / 102828) : ℂ) * ζ ^ 22)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY55_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((13502 / 25707) : ℂ) - ((52023 / 17138) : ℂ) * ζ ^ 2 - ((62313 / 34276) : ℂ) * ζ ^ 6 + ((2800 / 1353) : ℂ) * ζ ^ 8 + ((156463 / 102828) : ℂ) * ζ ^ 12 + ((83785 / 102828) : ℂ) * ζ ^ 18 + ((52023 / 17138) : ℂ) * ζ ^ 22 - ((30823 / 51414) : ℂ) * ζ ^ 24 - ((2800 / 1353) : ℂ) * ζ ^ 28 - ((52709 / 25707) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((((24961 / 8569) : ℂ) - ((40123 / 17138) : ℂ) * ζ ^ 2 - ((349879 / 102828) : ℂ) * ζ ^ 6 + ((8211 / 8569) : ℂ) * ζ ^ 8 + ((37759 / 34276) : ℂ) * ζ ^ 12 - ((8732 / 25707) : ℂ) * ζ ^ 18 + ((40123 / 17138) : ℂ) * ζ ^ 22 + ((197833 / 102828) : ℂ) * ζ ^ 24 - ((8211 / 8569) : ℂ) * ζ ^ 28 - ((2763 / 1804) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((2988 / 8569) : ℂ) + ((23729 / 25707) : ℂ) * ζ ^ 2 + ((30847 / 34276) : ℂ) * ζ ^ 6 - ((27463 / 34276) : ℂ) * ζ ^ 8 + ((17 / 25707) : ℂ) * ζ ^ 12 - ((39070 / 25707) : ℂ) * ζ ^ 18 - ((23729 / 25707) : ℂ) * ζ ^ 22 + ((177863 / 102828) : ℂ) * ζ ^ 24 + ((27463 / 34276) : ℂ) * ζ ^ 28 - ((19357 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((18101 / 51414) : ℂ) + ((47979 / 17138) : ℂ) * ζ ^ 2 + ((208537 / 102828) : ℂ) * ζ ^ 6 - ((18868 / 8569) : ℂ) * ζ ^ 8 - ((129619 / 102828) : ℂ) * ζ ^ 12 - ((122393 / 102828) : ℂ) * ζ ^ 18 - ((47979 / 17138) : ℂ) * ζ ^ 22 + ((3651 / 8569) : ℂ) * ζ ^ 24 + ((18868 / 8569) : ℂ) * ζ ^ 28 + ((46909 / 25707) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((8903 / 51414) : ℂ) + ((2022 / 8569) : ℂ) * ζ ^ 2 - ((10799 / 51414) : ℂ) * ζ ^ 6 + ((3404 / 25707) : ℂ) * ζ ^ 8 - ((2237 / 8569) : ℂ) * ζ ^ 12 + ((508 / 1353) : ℂ) * ζ ^ 18 - ((2022 / 8569) : ℂ) * ζ ^ 22 + ((8917 / 51414) : ℂ) * ζ ^ 24 - ((3404 / 25707) : ℂ) * ζ ^ 28 + ((5800 / 25707) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((-((601 / 2706) : ℂ) - ((524 / 1353) : ℂ) * ζ ^ 2 + ((692 / 1353) : ℂ) * ζ ^ 6 + ((16 / 1353) : ℂ) * ζ ^ 8 - ((35 / 2706) : ℂ) * ζ ^ 12 - ((1301 / 2706) : ℂ) * ζ ^ 18 + ((524 / 1353) : ℂ) * ζ ^ 22 - ((332 / 1353) : ℂ) * ζ ^ 24 - ((16 / 1353) : ℂ) * ζ ^ 28 + ((403 / 2706) : ℂ) * ζ ^ 30)) * Y 3 2) = 0 := by
  have previous :=
    row17_reducedY55_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation02
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((614 / 627) : ℂ) - ((72 / 209) : ℂ) * ζ ^ 2 - ((298 / 627) : ℂ) * ζ ^ 6 + ((830 / 627) : ℂ) * ζ ^ 8 - ((92 / 209) : ℂ) * ζ ^ 12 - ((72 / 209) : ℂ) * ζ ^ 18 + ((72 / 209) : ℂ) * ζ ^ 22 + ((1120 / 627) : ℂ) * ζ ^ 24 - ((830 / 627) : ℂ) * ζ ^ 28 - ((574 / 627) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((2149 / 17138) : ℂ) + ((2257 / 25707) : ℂ) * ζ ^ 2 - ((2941 / 17138) : ℂ) * ζ ^ 4 - ((18347 / 51414) : ℂ) * ζ ^ 6 + ((5815 / 51414) : ℂ) * ζ ^ 8 + ((8079 / 17138) : ℂ) * ζ ^ 10 - ((21235 / 51414) : ℂ) * ζ ^ 12 - ((27007 / 51414) : ℂ) * ζ ^ 14 + ((31309 / 51414) : ℂ) * ζ ^ 16 + ((7377 / 17138) : ℂ) * ζ ^ 18 - ((9205 / 17138) : ℂ) * ζ ^ 20 - ((16241 / 51414) : ℂ) * ζ ^ 22 + ((5651 / 25707) : ℂ) * ζ ^ 24 + ((5135 / 25707) : ℂ) * ζ ^ 26 + ((14 / 627) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((50 / 25707) : ℂ) - ((3041 / 8569) : ℂ) * ζ ^ 2 + ((5782 / 25707) : ℂ) * ζ ^ 4 + ((15749 / 51414) : ℂ) * ζ ^ 6 + ((33263 / 51414) : ℂ) * ζ ^ 8 - ((48689 / 51414) : ℂ) * ζ ^ 10 - ((130 / 779) : ℂ) * ζ ^ 12 + ((7318 / 8569) : ℂ) * ζ ^ 14 - ((12703 / 25707) : ℂ) * ζ ^ 16 - ((5867 / 25707) : ℂ) * ζ ^ 18 + ((31747 / 25707) : ℂ) * ζ ^ 20 - ((10603 / 25707) : ℂ) * ζ ^ 22 - ((28565 / 25707) : ℂ) * ζ ^ 24 - ((2495 / 8569) : ℂ) * ζ ^ 26 + ((140 / 627) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((2149 / 17138) : ℂ) - ((2257 / 25707) : ℂ) * ζ ^ 2 + ((2941 / 17138) : ℂ) * ζ ^ 4 + ((18347 / 51414) : ℂ) * ζ ^ 6 - ((5815 / 51414) : ℂ) * ζ ^ 8 - ((8079 / 17138) : ℂ) * ζ ^ 10 + ((21235 / 51414) : ℂ) * ζ ^ 12 + ((27007 / 51414) : ℂ) * ζ ^ 14 - ((31309 / 51414) : ℂ) * ζ ^ 16 - ((7377 / 17138) : ℂ) * ζ ^ 18 + ((9205 / 17138) : ℂ) * ζ ^ 20 + ((16241 / 51414) : ℂ) * ζ ^ 22 - ((5651 / 25707) : ℂ) * ζ ^ 24 - ((5135 / 25707) : ℂ) * ζ ^ 26 - ((14 / 627) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((((7705 / 25707) : ℂ) + ((5132 / 25707) : ℂ) * ζ ^ 2 - ((9649 / 25707) : ℂ) * ζ ^ 4 - ((6845 / 8569) : ℂ) * ζ ^ 6 - ((233 / 8569) : ℂ) * ζ ^ 8 + ((811 / 779) : ℂ) * ζ ^ 10 + ((6227 / 25707) : ℂ) * ζ ^ 12 - ((7373 / 8569) : ℂ) * ζ ^ 14 - ((6797 / 51414) : ℂ) * ζ ^ 16 + ((28115 / 51414) : ℂ) * ζ ^ 18 - ((2947 / 51414) : ℂ) * ζ ^ 20 - ((15659 / 51414) : ℂ) * ζ ^ 22 + ((5527 / 51414) : ℂ) * ζ ^ 24 + ((4137 / 17138) : ℂ) * ζ ^ 26 + ((49 / 627) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY55_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((10721 / 51414) : ℂ) - ((2179 / 779) : ℂ) * ζ ^ 2 - ((19271 / 9348) : ℂ) * ζ ^ 6 + ((2381 / 902) : ℂ) * ζ ^ 8 + ((130357 / 102828) : ℂ) * ζ ^ 12 + ((14101 / 9348) : ℂ) * ζ ^ 18 + ((2179 / 779) : ℂ) * ζ ^ 22 - ((13821 / 17138) : ℂ) * ζ ^ 24 - ((2381 / 902) : ℂ) * ζ ^ 28 - ((7243 / 4674) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((((54700 / 25707) : ℂ) - ((1333 / 779) : ℂ) * ζ ^ 2 - ((25567 / 9348) : ℂ) * ζ ^ 6 + ((6277 / 51414) : ℂ) * ζ ^ 8 + ((222283 / 102828) : ℂ) * ζ ^ 12 - ((2929 / 2337) : ℂ) * ζ ^ 18 + ((1333 / 779) : ℂ) * ζ ^ 22 + ((236281 / 102828) : ℂ) * ζ ^ 24 - ((6277 / 51414) : ℂ) * ζ ^ 28 - ((12161 / 9348) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((2988 / 8569) : ℂ) + ((23729 / 25707) : ℂ) * ζ ^ 2 + ((30847 / 34276) : ℂ) * ζ ^ 6 - ((27463 / 34276) : ℂ) * ζ ^ 8 + ((17 / 25707) : ℂ) * ζ ^ 12 - ((39070 / 25707) : ℂ) * ζ ^ 18 - ((23729 / 25707) : ℂ) * ζ ^ 22 + ((177863 / 102828) : ℂ) * ζ ^ 24 + ((27463 / 34276) : ℂ) * ζ ^ 28 - ((19357 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((18101 / 51414) : ℂ) + ((47979 / 17138) : ℂ) * ζ ^ 2 + ((208537 / 102828) : ℂ) * ζ ^ 6 - ((18868 / 8569) : ℂ) * ζ ^ 8 - ((129619 / 102828) : ℂ) * ζ ^ 12 - ((122393 / 102828) : ℂ) * ζ ^ 18 - ((47979 / 17138) : ℂ) * ζ ^ 22 + ((3651 / 8569) : ℂ) * ζ ^ 24 + ((18868 / 8569) : ℂ) * ζ ^ 28 + ((46909 / 25707) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((8903 / 51414) : ℂ) + ((2022 / 8569) : ℂ) * ζ ^ 2 - ((10799 / 51414) : ℂ) * ζ ^ 6 + ((3404 / 25707) : ℂ) * ζ ^ 8 - ((2237 / 8569) : ℂ) * ζ ^ 12 + ((508 / 1353) : ℂ) * ζ ^ 18 - ((2022 / 8569) : ℂ) * ζ ^ 22 + ((8917 / 51414) : ℂ) * ζ ^ 24 - ((3404 / 25707) : ℂ) * ζ ^ 28 + ((5800 / 25707) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((7351 / 8569) : ℂ) + ((5650 / 8569) : ℂ) * ζ ^ 2 + ((117 / 451) : ℂ) * ζ ^ 6 - ((12985 / 25707) : ℂ) * ζ ^ 8 - ((39499 / 51414) : ℂ) * ζ ^ 12 - ((4963 / 51414) : ℂ) * ζ ^ 18 - ((5650 / 8569) : ℂ) * ζ ^ 22 + ((45709 / 51414) : ℂ) * ζ ^ 24 + ((12985 / 25707) : ℂ) * ζ ^ 28 + ((22309 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((601 / 2706) : ℂ) - ((524 / 1353) : ℂ) * ζ ^ 2 + ((692 / 1353) : ℂ) * ζ ^ 6 + ((16 / 1353) : ℂ) * ζ ^ 8 - ((35 / 2706) : ℂ) * ζ ^ 12 - ((1301 / 2706) : ℂ) * ζ ^ 18 + ((524 / 1353) : ℂ) * ζ ^ 22 - ((332 / 1353) : ℂ) * ζ ^ 24 - ((16 / 1353) : ℂ) * ζ ^ 28 + ((403 / 2706) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((-((857 / 2706) : ℂ) - ((215 / 902) : ℂ) * ζ ^ 2 + ((659 / 2706) : ℂ) * ζ ^ 6 - ((1543 / 2706) : ℂ) * ζ ^ 8 + ((229 / 902) : ℂ) * ζ ^ 12 - ((1877 / 2706) : ℂ) * ζ ^ 18 + ((215 / 902) : ℂ) * ζ ^ 22 + ((280 / 1353) : ℂ) * ζ ^ 24 + ((1543 / 2706) : ℂ) * ζ ^ 28 - ((1355 / 2706) : ℂ) * ζ ^ 30)) * Y 3 3) = 0 := by
  have previous :=
    row17_reducedY55_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation03
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((1402 / 627) : ℂ) - ((1076 / 627) : ℂ) * ζ ^ 2 + ((214 / 627) : ℂ) * ζ ^ 6 + ((2116 / 627) : ℂ) * ζ ^ 8 - ((188 / 209) : ℂ) * ζ ^ 12 - ((196 / 627) : ℂ) * ζ ^ 18 + ((1076 / 627) : ℂ) * ζ ^ 22 - ((556 / 627) : ℂ) * ζ ^ 24 - ((2116 / 627) : ℂ) * ζ ^ 28 + ((604 / 627) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((12698 / 25707) : ℂ) + ((5987 / 51414) : ℂ) * ζ ^ 2 + ((1178 / 1353) : ℂ) * ζ ^ 4 + ((11323 / 25707) : ℂ) * ζ ^ 6 - ((18379 / 25707) : ℂ) * ζ ^ 8 - ((8060 / 8569) : ℂ) * ζ ^ 10 + ((13457 / 25707) : ℂ) * ζ ^ 12 + ((23138 / 25707) : ℂ) * ζ ^ 14 - ((15940 / 25707) : ℂ) * ζ ^ 16 - ((17260 / 25707) : ℂ) * ζ ^ 18 + ((11822 / 25707) : ℂ) * ζ ^ 20 + ((4403 / 25707) : ℂ) * ζ ^ 22 - ((14281 / 25707) : ℂ) * ζ ^ 24 - ((69 / 451) : ℂ) * ζ ^ 26 + ((2114 / 25707) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((10700 / 8569) : ℂ) - ((10204 / 25707) : ℂ) * ζ ^ 2 - ((11507 / 8569) : ℂ) * ζ ^ 4 - ((2341 / 8569) : ℂ) * ζ ^ 6 + ((11416 / 8569) : ℂ) * ζ ^ 8 + ((680 / 2337) : ℂ) * ζ ^ 10 - ((11554 / 25707) : ℂ) * ζ ^ 12 - ((10520 / 25707) : ℂ) * ζ ^ 14 + ((17597 / 25707) : ℂ) * ζ ^ 16 + ((8005 / 25707) : ℂ) * ζ ^ 18 - ((15563 / 25707) : ℂ) * ζ ^ 20 - ((2516 / 8569) : ℂ) * ζ ^ 22 + ((12088 / 25707) : ℂ) * ζ ^ 24 + ((10280 / 25707) : ℂ) * ζ ^ 26 - ((1208 / 8569) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((19249 / 25707) : ℂ) - ((373 / 1353) : ℂ) * ζ ^ 2 + ((8389 / 8569) : ℂ) * ζ ^ 4 + ((2093 / 25707) : ℂ) * ζ ^ 6 - ((5462 / 25707) : ℂ) * ζ ^ 8 - ((1887 / 8569) : ℂ) * ζ ^ 10 + ((4710 / 8569) : ℂ) * ζ ^ 12 + ((134 / 1353) : ℂ) * ζ ^ 14 - ((24082 / 25707) : ℂ) * ζ ^ 16 + ((455 / 8569) : ℂ) * ζ ^ 18 + ((1241 / 1353) : ℂ) * ζ ^ 20 - ((4933 / 25707) : ℂ) * ζ ^ 22 - ((16474 / 25707) : ℂ) * ζ ^ 24 + ((2414 / 25707) : ℂ) * ζ ^ 26 + ((604 / 25707) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((((12698 / 25707) : ℂ) - ((5987 / 51414) : ℂ) * ζ ^ 2 - ((1178 / 1353) : ℂ) * ζ ^ 4 - ((11323 / 25707) : ℂ) * ζ ^ 6 + ((18379 / 25707) : ℂ) * ζ ^ 8 + ((8060 / 8569) : ℂ) * ζ ^ 10 - ((13457 / 25707) : ℂ) * ζ ^ 12 - ((23138 / 25707) : ℂ) * ζ ^ 14 + ((15940 / 25707) : ℂ) * ζ ^ 16 + ((17260 / 25707) : ℂ) * ζ ^ 18 - ((11822 / 25707) : ℂ) * ζ ^ 20 - ((4403 / 25707) : ℂ) * ζ ^ 22 + ((14281 / 25707) : ℂ) * ζ ^ 24 + ((69 / 451) : ℂ) * ζ ^ 26 - ((2114 / 25707) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY55_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((6646 / 25707) : ℂ) - ((587 / 1558) : ℂ) * ζ ^ 2 + ((1607 / 4674) : ℂ) * ζ ^ 6 - ((2757 / 17138) : ℂ) * ζ ^ 8 + ((1486 / 25707) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((587 / 1558) : ℂ) * ζ ^ 22 + ((9289 / 17138) : ℂ) * ζ ^ 24 + ((2757 / 17138) : ℂ) * ζ ^ 28 - ((1495 / 4674) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((((28537 / 25707) : ℂ) + ((321 / 1558) : ℂ) * ζ ^ 2 - ((862 / 2337) : ℂ) * ζ ^ 6 - ((41314 / 25707) : ℂ) * ζ ^ 8 - ((42727 / 51414) : ℂ) * ζ ^ 12 - ((823 / 2337) : ℂ) * ζ ^ 18 - ((321 / 1558) : ℂ) * ζ ^ 22 + ((25396 / 25707) : ℂ) * ζ ^ 24 + ((41314 / 25707) : ℂ) * ζ ^ 28 + ((3349 / 2337) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((2988 / 8569) : ℂ) + ((23729 / 25707) : ℂ) * ζ ^ 2 + ((30847 / 34276) : ℂ) * ζ ^ 6 - ((27463 / 34276) : ℂ) * ζ ^ 8 + ((17 / 25707) : ℂ) * ζ ^ 12 - ((39070 / 25707) : ℂ) * ζ ^ 18 - ((23729 / 25707) : ℂ) * ζ ^ 22 + ((177863 / 102828) : ℂ) * ζ ^ 24 + ((27463 / 34276) : ℂ) * ζ ^ 28 - ((19357 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((18101 / 51414) : ℂ) + ((47979 / 17138) : ℂ) * ζ ^ 2 + ((208537 / 102828) : ℂ) * ζ ^ 6 - ((18868 / 8569) : ℂ) * ζ ^ 8 - ((129619 / 102828) : ℂ) * ζ ^ 12 - ((122393 / 102828) : ℂ) * ζ ^ 18 - ((47979 / 17138) : ℂ) * ζ ^ 22 + ((3651 / 8569) : ℂ) * ζ ^ 24 + ((18868 / 8569) : ℂ) * ζ ^ 28 + ((46909 / 25707) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((8903 / 51414) : ℂ) + ((2022 / 8569) : ℂ) * ζ ^ 2 - ((10799 / 51414) : ℂ) * ζ ^ 6 + ((3404 / 25707) : ℂ) * ζ ^ 8 - ((2237 / 8569) : ℂ) * ζ ^ 12 + ((508 / 1353) : ℂ) * ζ ^ 18 - ((2022 / 8569) : ℂ) * ζ ^ 22 + ((8917 / 51414) : ℂ) * ζ ^ 24 - ((3404 / 25707) : ℂ) * ζ ^ 28 + ((5800 / 25707) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((7351 / 8569) : ℂ) + ((5650 / 8569) : ℂ) * ζ ^ 2 + ((117 / 451) : ℂ) * ζ ^ 6 - ((12985 / 25707) : ℂ) * ζ ^ 8 - ((39499 / 51414) : ℂ) * ζ ^ 12 - ((4963 / 51414) : ℂ) * ζ ^ 18 - ((5650 / 8569) : ℂ) * ζ ^ 22 + ((45709 / 51414) : ℂ) * ζ ^ 24 + ((12985 / 25707) : ℂ) * ζ ^ 28 + ((22309 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((601 / 2706) : ℂ) - ((524 / 1353) : ℂ) * ζ ^ 2 + ((692 / 1353) : ℂ) * ζ ^ 6 + ((16 / 1353) : ℂ) * ζ ^ 8 - ((35 / 2706) : ℂ) * ζ ^ 12 - ((1301 / 2706) : ℂ) * ζ ^ 18 + ((524 / 1353) : ℂ) * ζ ^ 22 - ((332 / 1353) : ℂ) * ζ ^ 24 - ((16 / 1353) : ℂ) * ζ ^ 28 + ((403 / 2706) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((-((857 / 2706) : ℂ) - ((215 / 902) : ℂ) * ζ ^ 2 + ((659 / 2706) : ℂ) * ζ ^ 6 - ((1543 / 2706) : ℂ) * ζ ^ 8 + ((229 / 902) : ℂ) * ζ ^ 12 - ((1877 / 2706) : ℂ) * ζ ^ 18 + ((215 / 902) : ℂ) * ζ ^ 22 + ((280 / 1353) : ℂ) * ζ ^ 24 + ((1543 / 2706) : ℂ) * ζ ^ 28 - ((1355 / 2706) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((857 / 17138) : ℂ) - ((3771 / 1558) : ℂ) * ζ ^ 2 - ((7495 / 3116) : ℂ) * ζ ^ 6 + ((23998 / 8569) : ℂ) * ζ ^ 8 + ((41471 / 34276) : ℂ) * ζ ^ 12 + ((4903 / 3116) : ℂ) * ζ ^ 18 + ((3771 / 1558) : ℂ) * ζ ^ 22 - ((11555 / 8569) : ℂ) * ζ ^ 24 - ((23998 / 8569) : ℂ) * ζ ^ 28 - ((958 / 779) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((10812 / 8569) : ℂ) - ((2919 / 8569) : ℂ) * ζ ^ 2 - ((47319 / 34276) : ℂ) * ζ ^ 6 + ((2374 / 8569) : ℂ) * ζ ^ 8 + ((153 / 164) : ℂ) * ζ ^ 12 - ((17563 / 34276) : ℂ) * ζ ^ 18 + ((2919 / 8569) : ℂ) * ζ ^ 22 + ((6807 / 8569) : ℂ) * ζ ^ 24 - ((2374 / 8569) : ℂ) * ζ ^ 28 - ((14567 / 17138) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY55_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((14437 / 8569) : ℂ) - ((23797 / 8569) : ℂ) * ζ ^ 2 - ((9539 / 8569) : ℂ) * ζ ^ 6 + ((81749 / 25707) : ℂ) * ζ ^ 8 + ((32038 / 25707) : ℂ) * ζ ^ 12 + ((46907 / 25707) : ℂ) * ζ ^ 18 + ((23797 / 8569) : ℂ) * ζ ^ 22 - ((57491 / 25707) : ℂ) * ζ ^ 24 - ((81749 / 25707) : ℂ) * ζ ^ 28 - ((8059 / 8569) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((182671 / 188518) : ℂ) - ((170727 / 188518) : ℂ) * ζ ^ 2 - ((182671 / 188518) : ℂ) * ζ ^ 4 - ((336505 / 377036) : ℂ) * ζ ^ 6 + ((170160 / 94259) : ℂ) * ζ ^ 8 + ((193723 / 377036) : ℂ) * ζ ^ 10 + ((46939 / 94259) : ℂ) * ζ ^ 12 - ((46337 / 188518) : ℂ) * ζ ^ 14 - ((12129 / 188518) : ℂ) * ζ ^ 16 - ((166959 / 377036) : ℂ) * ζ ^ 18 + ((196731 / 377036) : ℂ) * ζ ^ 20 + ((24177 / 377036) : ℂ) * ζ ^ 22 + ((81749 / 188518) : ℂ) * ζ ^ 24 + ((24177 / 188518) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((1293255 / 377036) : ℂ) + ((776357 / 377036) : ℂ) * ζ ^ 2 - ((1293255 / 377036) : ℂ) * ζ ^ 4 - ((1067533 / 377036) : ℂ) * ζ ^ 6 - ((594413 / 377036) : ℂ) * ζ ^ 8 - ((72224 / 94259) : ℂ) * ζ ^ 10 + ((1650263 / 377036) : ℂ) * ζ ^ 12 - ((310363 / 188518) : ℂ) * ζ ^ 14 - ((24258 / 94259) : ℂ) * ζ ^ 16 - ((1453137 / 377036) : ℂ) * ζ ^ 18 + ((1419325 / 377036) : ℂ) * ζ ^ 20 + ((24177 / 94259) : ℂ) * ζ ^ 22 + ((81749 / 19844) : ℂ) * ζ ^ 24 + ((24177 / 19844) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((182671 / 188518) : ℂ) + ((170727 / 188518) : ℂ) * ζ ^ 2 + ((182671 / 188518) : ℂ) * ζ ^ 4 + ((336505 / 377036) : ℂ) * ζ ^ 6 - ((170160 / 94259) : ℂ) * ζ ^ 8 - ((193723 / 377036) : ℂ) * ζ ^ 10 - ((46939 / 94259) : ℂ) * ζ ^ 12 + ((46337 / 188518) : ℂ) * ζ ^ 14 + ((12129 / 188518) : ℂ) * ζ ^ 16 + ((166959 / 377036) : ℂ) * ζ ^ 18 - ((196731 / 377036) : ℂ) * ζ ^ 20 - ((24177 / 377036) : ℂ) * ζ ^ 22 - ((81749 / 188518) : ℂ) * ζ ^ 24 - ((24177 / 188518) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((281175 / 188518) : ℂ) - ((7173 / 188518) : ℂ) * ζ ^ 2 + ((281175 / 188518) : ℂ) * ζ ^ 4 + ((477621 / 377036) : ℂ) * ζ ^ 6 - ((121721 / 188518) : ℂ) * ζ ^ 8 - ((49275 / 377036) : ℂ) * ζ ^ 10 - ((140817 / 94259) : ℂ) * ζ ^ 12 + ((139011 / 188518) : ℂ) * ζ ^ 14 + ((36387 / 188518) : ℂ) * ζ ^ 16 + ((500877 / 377036) : ℂ) * ζ ^ 18 - ((590193 / 377036) : ℂ) * ζ ^ 20 - ((72531 / 377036) : ℂ) * ζ ^ 22 - ((245247 / 188518) : ℂ) * ζ ^ 24 - ((72531 / 188518) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY55_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((10 / 123) : ℂ) + ((16 / 41) : ℂ) * ζ ^ 2 + ((97 / 246) : ℂ) * ζ ^ 6 - ((17 / 123) : ℂ) * ζ ^ 8 + ((91 / 246) : ℂ) * ζ ^ 12 - ((119 / 246) : ℂ) * ζ ^ 18 - ((16 / 41) : ℂ) * ζ ^ 22 - ((53 / 246) : ℂ) * ζ ^ 24 + ((17 / 123) : ℂ) * ζ ^ 28 + ((359 / 246) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((((2988 / 8569) : ℂ) + ((23729 / 25707) : ℂ) * ζ ^ 2 + ((30847 / 34276) : ℂ) * ζ ^ 6 - ((27463 / 34276) : ℂ) * ζ ^ 8 + ((17 / 25707) : ℂ) * ζ ^ 12 - ((39070 / 25707) : ℂ) * ζ ^ 18 - ((23729 / 25707) : ℂ) * ζ ^ 22 + ((177863 / 102828) : ℂ) * ζ ^ 24 + ((27463 / 34276) : ℂ) * ζ ^ 28 - ((19357 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((18101 / 51414) : ℂ) + ((47979 / 17138) : ℂ) * ζ ^ 2 + ((208537 / 102828) : ℂ) * ζ ^ 6 - ((18868 / 8569) : ℂ) * ζ ^ 8 - ((129619 / 102828) : ℂ) * ζ ^ 12 - ((122393 / 102828) : ℂ) * ζ ^ 18 - ((47979 / 17138) : ℂ) * ζ ^ 22 + ((3651 / 8569) : ℂ) * ζ ^ 24 + ((18868 / 8569) : ℂ) * ζ ^ 28 + ((46909 / 25707) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((8903 / 51414) : ℂ) + ((2022 / 8569) : ℂ) * ζ ^ 2 - ((10799 / 51414) : ℂ) * ζ ^ 6 + ((3404 / 25707) : ℂ) * ζ ^ 8 - ((2237 / 8569) : ℂ) * ζ ^ 12 + ((508 / 1353) : ℂ) * ζ ^ 18 - ((2022 / 8569) : ℂ) * ζ ^ 22 + ((8917 / 51414) : ℂ) * ζ ^ 24 - ((3404 / 25707) : ℂ) * ζ ^ 28 + ((5800 / 25707) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((7351 / 8569) : ℂ) + ((5650 / 8569) : ℂ) * ζ ^ 2 + ((117 / 451) : ℂ) * ζ ^ 6 - ((12985 / 25707) : ℂ) * ζ ^ 8 - ((39499 / 51414) : ℂ) * ζ ^ 12 - ((4963 / 51414) : ℂ) * ζ ^ 18 - ((5650 / 8569) : ℂ) * ζ ^ 22 + ((45709 / 51414) : ℂ) * ζ ^ 24 + ((12985 / 25707) : ℂ) * ζ ^ 28 + ((22309 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((601 / 2706) : ℂ) - ((524 / 1353) : ℂ) * ζ ^ 2 + ((692 / 1353) : ℂ) * ζ ^ 6 + ((16 / 1353) : ℂ) * ζ ^ 8 - ((35 / 2706) : ℂ) * ζ ^ 12 - ((1301 / 2706) : ℂ) * ζ ^ 18 + ((524 / 1353) : ℂ) * ζ ^ 22 - ((332 / 1353) : ℂ) * ζ ^ 24 - ((16 / 1353) : ℂ) * ζ ^ 28 + ((403 / 2706) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((-((857 / 2706) : ℂ) - ((215 / 902) : ℂ) * ζ ^ 2 + ((659 / 2706) : ℂ) * ζ ^ 6 - ((1543 / 2706) : ℂ) * ζ ^ 8 + ((229 / 902) : ℂ) * ζ ^ 12 - ((1877 / 2706) : ℂ) * ζ ^ 18 + ((215 / 902) : ℂ) * ζ ^ 22 + ((280 / 1353) : ℂ) * ζ ^ 24 + ((1543 / 2706) : ℂ) * ζ ^ 28 - ((1355 / 2706) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((857 / 17138) : ℂ) - ((3771 / 1558) : ℂ) * ζ ^ 2 - ((7495 / 3116) : ℂ) * ζ ^ 6 + ((23998 / 8569) : ℂ) * ζ ^ 8 + ((41471 / 34276) : ℂ) * ζ ^ 12 + ((4903 / 3116) : ℂ) * ζ ^ 18 + ((3771 / 1558) : ℂ) * ζ ^ 22 - ((11555 / 8569) : ℂ) * ζ ^ 24 - ((23998 / 8569) : ℂ) * ζ ^ 28 - ((958 / 779) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((227 / 209) : ℂ) + ((3 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 + ((189 / 418) : ℂ) * ζ ^ 8 - ((183 / 418) : ℂ) * ζ ^ 12 + ((10 / 19) : ℂ) * ζ ^ 18 - ((3 / 19) : ℂ) * ζ ^ 22 + ((173 / 418) : ℂ) * ζ ^ 24 - ((189 / 418) : ℂ) * ζ ^ 28 + ((11 / 38) : ℂ) * ζ ^ 30)) * Y 4 5
      + ((((10812 / 8569) : ℂ) - ((2919 / 8569) : ℂ) * ζ ^ 2 - ((47319 / 34276) : ℂ) * ζ ^ 6 + ((2374 / 8569) : ℂ) * ζ ^ 8 + ((153 / 164) : ℂ) * ζ ^ 12 - ((17563 / 34276) : ℂ) * ζ ^ 18 + ((2919 / 8569) : ℂ) * ζ ^ 22 + ((6807 / 8569) : ℂ) * ζ ^ 24 - ((2374 / 8569) : ℂ) * ζ ^ 28 - ((14567 / 17138) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((87 / 209) : ℂ) - ((6 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 - ((159 / 418) : ℂ) * ζ ^ 8 + ((155 / 418) : ℂ) * ζ ^ 12 + ((6 / 19) : ℂ) * ζ ^ 22 + ((145 / 418) : ℂ) * ζ ^ 24 + ((159 / 418) : ℂ) * ζ ^ 28 + ((7 / 38) : ℂ) * ζ ^ 30)) * Y 5 5) = 0 := by
  have previous :=
    row17_reducedY55_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation05
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((14 / 57) : ℂ) - ((2 / 57) : ℂ) * ζ ^ 2 - ((4 / 57) : ℂ) * ζ ^ 6 + ((94 / 57) : ℂ) * ζ ^ 8 - ((22 / 57) : ℂ) * ζ ^ 12 + ((62 / 57) : ℂ) * ζ ^ 18 + ((2 / 57) : ℂ) * ζ ^ 22 + ((28 / 57) : ℂ) * ζ ^ 24 - ((94 / 57) : ℂ) * ζ ^ 28 - ((34 / 57) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((94 / 209) : ℂ) - ((65 / 209) : ℂ) * ζ ^ 2 - ((94 / 209) : ℂ) * ζ ^ 4 + ((101 / 418) : ℂ) * ζ ^ 6 - ((107 / 418) : ℂ) * ζ ^ 8 - ((107 / 418) : ℂ) * ζ ^ 10 + ((465 / 418) : ℂ) * ζ ^ 12 - ((18 / 209) : ℂ) * ζ ^ 14 - ((183 / 418) : ℂ) * ζ ^ 16 - ((3 / 22) : ℂ) * ζ ^ 18 + ((3 / 22) : ℂ) * ζ ^ 20 + ((51 / 418) : ℂ) * ζ ^ 22 + ((141 / 209) : ℂ) * ζ ^ 24 + ((51 / 209) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((477 / 418) : ℂ) - ((40 / 209) : ℂ) * ζ ^ 2 - ((477 / 418) : ℂ) * ζ ^ 4 - ((245 / 418) : ℂ) * ζ ^ 6 - ((87 / 418) : ℂ) * ζ ^ 8 + ((116 / 209) : ℂ) * ζ ^ 10 + ((1 / 418) : ℂ) * ζ ^ 12 - ((9 / 11) : ℂ) * ζ ^ 14 + ((305 / 209) : ℂ) * ζ ^ 16 + ((157 / 418) : ℂ) * ζ ^ 18 - ((326 / 209) : ℂ) * ζ ^ 20 - ((85 / 209) : ℂ) * ζ ^ 22 + ((611 / 418) : ℂ) * ζ ^ 24 + ((221 / 418) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((255 / 209) : ℂ) - ((37 / 209) : ℂ) * ζ ^ 2 + ((255 / 209) : ℂ) * ζ ^ 4 + ((91 / 418) : ℂ) * ζ ^ 6 - ((309 / 418) : ℂ) * ζ ^ 8 - ((89 / 418) : ℂ) * ζ ^ 10 - ((155 / 418) : ℂ) * ζ ^ 12 + ((6 / 209) : ℂ) * ζ ^ 14 + ((61 / 418) : ℂ) * ζ ^ 16 + ((1 / 22) : ℂ) * ζ ^ 18 - ((1 / 22) : ℂ) * ζ ^ 20 - ((17 / 418) : ℂ) * ζ ^ 22 - ((47 / 209) : ℂ) * ζ ^ 24 - ((17 / 209) : ℂ) * ζ ^ 26)) * Y 4 5
        + ((-((94 / 209) : ℂ) + ((65 / 209) : ℂ) * ζ ^ 2 + ((94 / 209) : ℂ) * ζ ^ 4 - ((101 / 418) : ℂ) * ζ ^ 6 + ((107 / 418) : ℂ) * ζ ^ 8 + ((107 / 418) : ℂ) * ζ ^ 10 - ((465 / 418) : ℂ) * ζ ^ 12 + ((18 / 209) : ℂ) * ζ ^ 14 + ((183 / 418) : ℂ) * ζ ^ 16 + ((3 / 22) : ℂ) * ζ ^ 18 - ((3 / 22) : ℂ) * ζ ^ 20 - ((51 / 418) : ℂ) * ζ ^ 22 - ((141 / 209) : ℂ) * ζ ^ 24 - ((51 / 209) : ℂ) * ζ ^ 26)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY55_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((2988 / 8569) : ℂ) + ((23729 / 25707) : ℂ) * ζ ^ 2 + ((30847 / 34276) : ℂ) * ζ ^ 6 - ((27463 / 34276) : ℂ) * ζ ^ 8 + ((17 / 25707) : ℂ) * ζ ^ 12 - ((39070 / 25707) : ℂ) * ζ ^ 18 - ((23729 / 25707) : ℂ) * ζ ^ 22 + ((177863 / 102828) : ℂ) * ζ ^ 24 + ((27463 / 34276) : ℂ) * ζ ^ 28 - ((19357 / 17138) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((18101 / 51414) : ℂ) + ((47979 / 17138) : ℂ) * ζ ^ 2 + ((208537 / 102828) : ℂ) * ζ ^ 6 - ((18868 / 8569) : ℂ) * ζ ^ 8 - ((129619 / 102828) : ℂ) * ζ ^ 12 - ((122393 / 102828) : ℂ) * ζ ^ 18 - ((47979 / 17138) : ℂ) * ζ ^ 22 + ((3651 / 8569) : ℂ) * ζ ^ 24 + ((18868 / 8569) : ℂ) * ζ ^ 28 + ((46909 / 25707) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((8903 / 51414) : ℂ) + ((2022 / 8569) : ℂ) * ζ ^ 2 - ((10799 / 51414) : ℂ) * ζ ^ 6 + ((3404 / 25707) : ℂ) * ζ ^ 8 - ((2237 / 8569) : ℂ) * ζ ^ 12 + ((508 / 1353) : ℂ) * ζ ^ 18 - ((2022 / 8569) : ℂ) * ζ ^ 22 + ((8917 / 51414) : ℂ) * ζ ^ 24 - ((3404 / 25707) : ℂ) * ζ ^ 28 + ((5800 / 25707) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((7351 / 8569) : ℂ) + ((5650 / 8569) : ℂ) * ζ ^ 2 + ((117 / 451) : ℂ) * ζ ^ 6 - ((12985 / 25707) : ℂ) * ζ ^ 8 - ((39499 / 51414) : ℂ) * ζ ^ 12 - ((4963 / 51414) : ℂ) * ζ ^ 18 - ((5650 / 8569) : ℂ) * ζ ^ 22 + ((45709 / 51414) : ℂ) * ζ ^ 24 + ((12985 / 25707) : ℂ) * ζ ^ 28 + ((22309 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((601 / 2706) : ℂ) - ((524 / 1353) : ℂ) * ζ ^ 2 + ((692 / 1353) : ℂ) * ζ ^ 6 + ((16 / 1353) : ℂ) * ζ ^ 8 - ((35 / 2706) : ℂ) * ζ ^ 12 - ((1301 / 2706) : ℂ) * ζ ^ 18 + ((524 / 1353) : ℂ) * ζ ^ 22 - ((332 / 1353) : ℂ) * ζ ^ 24 - ((16 / 1353) : ℂ) * ζ ^ 28 + ((403 / 2706) : ℂ) * ζ ^ 30)) * Y 3 2
      + ((-((857 / 2706) : ℂ) - ((215 / 902) : ℂ) * ζ ^ 2 + ((659 / 2706) : ℂ) * ζ ^ 6 - ((1543 / 2706) : ℂ) * ζ ^ 8 + ((229 / 902) : ℂ) * ζ ^ 12 - ((1877 / 2706) : ℂ) * ζ ^ 18 + ((215 / 902) : ℂ) * ζ ^ 22 + ((280 / 1353) : ℂ) * ζ ^ 24 + ((1543 / 2706) : ℂ) * ζ ^ 28 - ((1355 / 2706) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((857 / 17138) : ℂ) - ((3771 / 1558) : ℂ) * ζ ^ 2 - ((7495 / 3116) : ℂ) * ζ ^ 6 + ((23998 / 8569) : ℂ) * ζ ^ 8 + ((41471 / 34276) : ℂ) * ζ ^ 12 + ((4903 / 3116) : ℂ) * ζ ^ 18 + ((3771 / 1558) : ℂ) * ζ ^ 22 - ((11555 / 8569) : ℂ) * ζ ^ 24 - ((23998 / 8569) : ℂ) * ζ ^ 28 - ((958 / 779) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((227 / 209) : ℂ) + ((3 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 + ((189 / 418) : ℂ) * ζ ^ 8 - ((183 / 418) : ℂ) * ζ ^ 12 + ((10 / 19) : ℂ) * ζ ^ 18 - ((3 / 19) : ℂ) * ζ ^ 22 + ((173 / 418) : ℂ) * ζ ^ 24 - ((189 / 418) : ℂ) * ζ ^ 28 + ((11 / 38) : ℂ) * ζ ^ 30)) * Y 4 5
      + ((((10812 / 8569) : ℂ) - ((2919 / 8569) : ℂ) * ζ ^ 2 - ((47319 / 34276) : ℂ) * ζ ^ 6 + ((2374 / 8569) : ℂ) * ζ ^ 8 + ((153 / 164) : ℂ) * ζ ^ 12 - ((17563 / 34276) : ℂ) * ζ ^ 18 + ((2919 / 8569) : ℂ) * ζ ^ 22 + ((6807 / 8569) : ℂ) * ζ ^ 24 - ((2374 / 8569) : ℂ) * ζ ^ 28 - ((14567 / 17138) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((87 / 209) : ℂ) - ((6 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 - ((159 / 418) : ℂ) * ζ ^ 8 + ((155 / 418) : ℂ) * ζ ^ 12 + ((6 / 19) : ℂ) * ζ ^ 22 + ((145 / 418) : ℂ) * ζ ^ 24 + ((159 / 418) : ℂ) * ζ ^ 28 + ((7 / 38) : ℂ) * ζ ^ 30)) * Y 5 5
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY55_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) + (2 : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 + ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((179 / 246) : ℂ) - ((2 / 41) : ℂ) * ζ ^ 2 + ((7 / 6) : ℂ) * ζ ^ 4 + ((18 / 41) : ℂ) * ζ ^ 6 - ((62 / 123) : ℂ) * ζ ^ 8 - ((71 / 82) : ℂ) * ζ ^ 10 - ((73 / 246) : ℂ) * ζ ^ 12 + ((193 / 246) : ℂ) * ζ ^ 14 + ((34 / 41) : ℂ) * ζ ^ 16 - ((35 / 82) : ℂ) * ζ ^ 18 - ((94 / 123) : ℂ) * ζ ^ 20 + ((79 / 246) : ℂ) * ζ ^ 24 + ((13 / 41) : ℂ) * ζ ^ 26 - ((28 / 123) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((7 / 123) : ℂ) + ((1 / 82) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 4 + ((55 / 246) : ℂ) * ζ ^ 6 + ((31 / 246) : ℂ) * ζ ^ 8 + ((1 / 123) : ℂ) * ζ ^ 10 + ((49 / 246) : ℂ) * ζ ^ 12 - ((20 / 41) : ℂ) * ζ ^ 14 - ((46 / 123) : ℂ) * ζ ^ 16 + ((19 / 82) : ℂ) * ζ ^ 18 + ((44 / 123) : ℂ) * ζ ^ 20 - ((56 / 123) : ℂ) * ζ ^ 24 - ((20 / 123) : ℂ) * ζ ^ 26 + ((16 / 41) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((8 / 123) : ℂ) - ((103 / 246) : ℂ) * ζ ^ 2 + ((1 / 3) : ℂ) * ζ ^ 4 + ((63 / 82) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 - ((301 / 246) : ℂ) * ζ ^ 10 - ((23 / 41) : ℂ) * ζ ^ 12 + ((143 / 246) : ℂ) * ζ ^ 14 + ((39 / 41) : ℂ) * ζ ^ 16 + ((26 / 123) : ℂ) * ζ ^ 18 - ((55 / 82) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((23 / 123) : ℂ) * ζ ^ 24 + ((58 / 123) : ℂ) * ζ ^ 26 - ((8 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((179 / 246) : ℂ) + ((2 / 41) : ℂ) * ζ ^ 2 - ((7 / 6) : ℂ) * ζ ^ 4 - ((18 / 41) : ℂ) * ζ ^ 6 + ((62 / 123) : ℂ) * ζ ^ 8 + ((71 / 82) : ℂ) * ζ ^ 10 + ((73 / 246) : ℂ) * ζ ^ 12 - ((193 / 246) : ℂ) * ζ ^ 14 - ((34 / 41) : ℂ) * ζ ^ 16 + ((35 / 82) : ℂ) * ζ ^ 18 + ((94 / 123) : ℂ) * ζ ^ 20 - ((79 / 246) : ℂ) * ζ ^ 24 - ((13 / 41) : ℂ) * ζ ^ 26 + ((28 / 123) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY55_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((5116 / 8569) : ℂ) + ((8049 / 8569) : ℂ) * ζ ^ 2 + ((133505 / 102828) : ℂ) * ζ ^ 6 - ((81667 / 102828) : ℂ) * ζ ^ 8 - ((1921 / 25707) : ℂ) * ζ ^ 12 - ((17064 / 8569) : ℂ) * ζ ^ 18 - ((8049 / 8569) : ℂ) * ζ ^ 22 + ((175735 / 102828) : ℂ) * ζ ^ 24 + ((81667 / 102828) : ℂ) * ζ ^ 28 - ((9574 / 8569) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((1504 / 25707) : ℂ) + ((46611 / 17138) : ℂ) * ζ ^ 2 + ((59607 / 34276) : ℂ) * ζ ^ 6 - ((125957 / 51414) : ℂ) * ζ ^ 8 - ((118333 / 102828) : ℂ) * ζ ^ 12 - ((83785 / 102828) : ℂ) * ζ ^ 18 - ((46611 / 17138) : ℂ) * ζ ^ 22 + ((24329 / 25707) : ℂ) * ζ ^ 24 + ((125957 / 51414) : ℂ) * ζ ^ 28 + ((114889 / 51414) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((122 / 209) : ℂ) + ((6 / 19) : ℂ) * ζ ^ 2 + ((3 / 38) : ℂ) * ζ ^ 6 + ((159 / 418) : ℂ) * ζ ^ 8 - ((155 / 418) : ℂ) * ζ ^ 12 - ((6 / 19) : ℂ) * ζ ^ 22 - ((145 / 418) : ℂ) * ζ ^ 24 - ((159 / 418) : ℂ) * ζ ^ 28 - ((7 / 38) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((7351 / 8569) : ℂ) + ((5650 / 8569) : ℂ) * ζ ^ 2 + ((117 / 451) : ℂ) * ζ ^ 6 - ((12985 / 25707) : ℂ) * ζ ^ 8 - ((39499 / 51414) : ℂ) * ζ ^ 12 - ((4963 / 51414) : ℂ) * ζ ^ 18 - ((5650 / 8569) : ℂ) * ζ ^ 22 + ((45709 / 51414) : ℂ) * ζ ^ 24 + ((12985 / 25707) : ℂ) * ζ ^ 28 + ((22309 / 51414) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((-((857 / 2706) : ℂ) - ((215 / 902) : ℂ) * ζ ^ 2 + ((659 / 2706) : ℂ) * ζ ^ 6 - ((1543 / 2706) : ℂ) * ζ ^ 8 + ((229 / 902) : ℂ) * ζ ^ 12 - ((1877 / 2706) : ℂ) * ζ ^ 18 + ((215 / 902) : ℂ) * ζ ^ 22 + ((280 / 1353) : ℂ) * ζ ^ 24 + ((1543 / 2706) : ℂ) * ζ ^ 28 - ((1355 / 2706) : ℂ) * ζ ^ 30)) * Y 3 3
      + ((((857 / 17138) : ℂ) - ((3771 / 1558) : ℂ) * ζ ^ 2 - ((7495 / 3116) : ℂ) * ζ ^ 6 + ((23998 / 8569) : ℂ) * ζ ^ 8 + ((41471 / 34276) : ℂ) * ζ ^ 12 + ((4903 / 3116) : ℂ) * ζ ^ 18 + ((3771 / 1558) : ℂ) * ζ ^ 22 - ((11555 / 8569) : ℂ) * ζ ^ 24 - ((23998 / 8569) : ℂ) * ζ ^ 28 - ((958 / 779) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((227 / 209) : ℂ) + ((3 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 + ((189 / 418) : ℂ) * ζ ^ 8 - ((183 / 418) : ℂ) * ζ ^ 12 + ((10 / 19) : ℂ) * ζ ^ 18 - ((3 / 19) : ℂ) * ζ ^ 22 + ((173 / 418) : ℂ) * ζ ^ 24 - ((189 / 418) : ℂ) * ζ ^ 28 + ((11 / 38) : ℂ) * ζ ^ 30)) * Y 4 5
      + ((((10812 / 8569) : ℂ) - ((2919 / 8569) : ℂ) * ζ ^ 2 - ((47319 / 34276) : ℂ) * ζ ^ 6 + ((2374 / 8569) : ℂ) * ζ ^ 8 + ((153 / 164) : ℂ) * ζ ^ 12 - ((17563 / 34276) : ℂ) * ζ ^ 18 + ((2919 / 8569) : ℂ) * ζ ^ 22 + ((6807 / 8569) : ℂ) * ζ ^ 24 - ((2374 / 8569) : ℂ) * ζ ^ 28 - ((14567 / 17138) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((87 / 209) : ℂ) - ((6 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 - ((159 / 418) : ℂ) * ζ ^ 8 + ((155 / 418) : ℂ) * ζ ^ 12 + ((6 / 19) : ℂ) * ζ ^ 22 + ((145 / 418) : ℂ) * ζ ^ 24 + ((159 / 418) : ℂ) * ζ ^ 28 + ((7 / 38) : ℂ) * ζ ^ 30)) * Y 5 5
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY55_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation12
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((20 / 33) : ℂ) - ((2 / 11) : ℂ) * ζ ^ 2 - ((26 / 33) : ℂ) * ζ ^ 6 + ((38 / 33) : ℂ) * ζ ^ 8 + ((10 / 33) : ℂ) * ζ ^ 12 + ((38 / 33) : ℂ) * ζ ^ 18 + ((2 / 11) : ℂ) * ζ ^ 22 + ((20 / 33) : ℂ) * ζ ^ 24 - ((38 / 33) : ℂ) * ζ ^ 28 - ((52 / 33) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((376 / 1353) : ℂ) - ((48 / 451) : ℂ) * ζ ^ 2 + ((343 / 1353) : ℂ) * ζ ^ 4 - ((159 / 451) : ℂ) * ζ ^ 6 - ((1157 / 2706) : ℂ) * ζ ^ 8 + ((641 / 1353) : ℂ) * ζ ^ 10 + ((361 / 2706) : ℂ) * ζ ^ 12 - ((1799 / 2706) : ℂ) * ζ ^ 14 + ((13 / 246) : ℂ) * ζ ^ 16 + ((71 / 123) : ℂ) * ζ ^ 18 - ((151 / 902) : ℂ) * ζ ^ 20 - ((617 / 1353) : ℂ) * ζ ^ 22 + ((233 / 1353) : ℂ) * ζ ^ 24 + ((428 / 1353) : ℂ) * ζ ^ 26 + ((52 / 1353) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((377 / 902) : ℂ) + ((217 / 451) : ℂ) * ζ ^ 2 - ((269 / 902) : ℂ) * ζ ^ 4 + ((68 / 1353) : ℂ) * ζ ^ 6 + ((4133 / 2706) : ℂ) * ζ ^ 8 - ((929 / 1353) : ℂ) * ζ ^ 10 - ((860 / 1353) : ℂ) * ζ ^ 12 + ((514 / 451) : ℂ) * ζ ^ 14 - ((23 / 1353) : ℂ) * ζ ^ 16 - ((1087 / 1353) : ℂ) * ζ ^ 18 + ((65 / 451) : ℂ) * ζ ^ 20 + ((226 / 1353) : ℂ) * ζ ^ 22 - ((1565 / 1353) : ℂ) * ζ ^ 24 - ((350 / 451) : ℂ) * ζ ^ 26 + ((520 / 1353) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((377 / 902) : ℂ) - ((217 / 451) : ℂ) * ζ ^ 2 + ((269 / 902) : ℂ) * ζ ^ 4 - ((68 / 1353) : ℂ) * ζ ^ 6 - ((4133 / 2706) : ℂ) * ζ ^ 8 + ((929 / 1353) : ℂ) * ζ ^ 10 + ((860 / 1353) : ℂ) * ζ ^ 12 - ((514 / 451) : ℂ) * ζ ^ 14 + ((23 / 1353) : ℂ) * ζ ^ 16 + ((1087 / 1353) : ℂ) * ζ ^ 18 - ((65 / 451) : ℂ) * ζ ^ 20 - ((226 / 1353) : ℂ) * ζ ^ 22 + ((1565 / 1353) : ℂ) * ζ ^ 24 + ((350 / 451) : ℂ) * ζ ^ 26 - ((520 / 1353) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((-((941 / 2706) : ℂ) - ((530 / 1353) : ℂ) * ζ ^ 2 + ((44 / 123) : ℂ) * ζ ^ 4 + ((976 / 1353) : ℂ) * ζ ^ 6 - ((14 / 1353) : ℂ) * ζ ^ 8 - ((2075 / 2706) : ℂ) * ζ ^ 10 - ((1223 / 2706) : ℂ) * ζ ^ 12 + ((1159 / 2706) : ℂ) * ζ ^ 14 + ((43 / 123) : ℂ) * ζ ^ 16 - ((377 / 902) : ℂ) * ζ ^ 18 - ((199 / 1353) : ℂ) * ζ ^ 20 + ((168 / 451) : ℂ) * ζ ^ 22 + ((160 / 1353) : ℂ) * ζ ^ 24 - ((436 / 1353) : ℂ) * ζ ^ 26 - ((104 / 451) : ℂ) * ζ ^ 28)) * Y 3 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY55_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((2988 / 8569) : ℂ) + ((3677 / 4674) : ℂ) * ζ ^ 2 + ((2521 / 3116) : ℂ) * ζ ^ 6 - ((27463 / 34276) : ℂ) * ζ ^ 8 + ((17 / 25707) : ℂ) * ζ ^ 12 - ((2702 / 2337) : ℂ) * ζ ^ 18 - ((3677 / 4674) : ℂ) * ζ ^ 22 + ((177863 / 102828) : ℂ) * ζ ^ 24 + ((27463 / 34276) : ℂ) * ζ ^ 28 - ((632 / 779) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((19291 / 51414) : ℂ) + ((1933 / 779) : ℂ) * ζ ^ 2 + ((18533 / 9348) : ℂ) * ζ ^ 6 - ((25879 / 8569) : ℂ) * ζ ^ 8 - ((92227 / 102828) : ℂ) * ζ ^ 12 - ((14101 / 9348) : ℂ) * ζ ^ 18 - ((1933 / 779) : ℂ) * ζ ^ 22 + ((9883 / 8569) : ℂ) * ζ ^ 24 + ((25879 / 8569) : ℂ) * ζ ^ 28 + ((4052 / 2337) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((122 / 209) : ℂ) + ((6 / 19) : ℂ) * ζ ^ 2 + ((3 / 38) : ℂ) * ζ ^ 6 + ((159 / 418) : ℂ) * ζ ^ 8 - ((155 / 418) : ℂ) * ζ ^ 12 - ((6 / 19) : ℂ) * ζ ^ 22 - ((145 / 418) : ℂ) * ζ ^ 24 - ((159 / 418) : ℂ) * ζ ^ 28 - ((7 / 38) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((107 / 209) : ℂ) + ((619 / 418) : ℂ) * ζ ^ 2 + ((25 / 22) : ℂ) * ζ ^ 6 + ((130 / 209) : ℂ) * ζ ^ 8 - ((59 / 209) : ℂ) * ζ ^ 12 - ((239 / 418) : ℂ) * ζ ^ 18 - ((619 / 418) : ℂ) * ζ ^ 22 - ((313 / 418) : ℂ) * ζ ^ 24 - ((130 / 209) : ℂ) * ζ ^ 28 - ((139 / 418) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((857 / 17138) : ℂ) - ((3771 / 1558) : ℂ) * ζ ^ 2 - ((7495 / 3116) : ℂ) * ζ ^ 6 + ((23998 / 8569) : ℂ) * ζ ^ 8 + ((41471 / 34276) : ℂ) * ζ ^ 12 + ((4903 / 3116) : ℂ) * ζ ^ 18 + ((3771 / 1558) : ℂ) * ζ ^ 22 - ((11555 / 8569) : ℂ) * ζ ^ 24 - ((23998 / 8569) : ℂ) * ζ ^ 28 - ((958 / 779) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((227 / 209) : ℂ) + ((3 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 + ((189 / 418) : ℂ) * ζ ^ 8 - ((183 / 418) : ℂ) * ζ ^ 12 + ((10 / 19) : ℂ) * ζ ^ 18 - ((3 / 19) : ℂ) * ζ ^ 22 + ((173 / 418) : ℂ) * ζ ^ 24 - ((189 / 418) : ℂ) * ζ ^ 28 + ((11 / 38) : ℂ) * ζ ^ 30)) * Y 4 5
      + ((((10812 / 8569) : ℂ) - ((2919 / 8569) : ℂ) * ζ ^ 2 - ((47319 / 34276) : ℂ) * ζ ^ 6 + ((2374 / 8569) : ℂ) * ζ ^ 8 + ((153 / 164) : ℂ) * ζ ^ 12 - ((17563 / 34276) : ℂ) * ζ ^ 18 + ((2919 / 8569) : ℂ) * ζ ^ 22 + ((6807 / 8569) : ℂ) * ζ ^ 24 - ((2374 / 8569) : ℂ) * ζ ^ 28 - ((14567 / 17138) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((87 / 209) : ℂ) - ((6 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 - ((159 / 418) : ℂ) * ζ ^ 8 + ((155 / 418) : ℂ) * ζ ^ 12 + ((6 / 19) : ℂ) * ζ ^ 22 + ((145 / 418) : ℂ) * ζ ^ 24 + ((159 / 418) : ℂ) * ζ ^ 28 + ((7 / 38) : ℂ) * ζ ^ 30)) * Y 5 5
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY55_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation13
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((46 / 33) : ℂ) + ((10 / 33) : ℂ) * ζ ^ 2 + ((14 / 33) : ℂ) * ζ ^ 6 + ((94 / 33) : ℂ) * ζ ^ 8 - ((10 / 33) : ℂ) * ζ ^ 12 + ((32 / 33) : ℂ) * ζ ^ 18 - ((10 / 33) : ℂ) * ζ ^ 22 - ((20 / 33) : ℂ) * ζ ^ 24 - ((94 / 33) : ℂ) * ζ ^ 28 + ((2 / 11) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((373 / 2706) : ℂ) + ((653 / 1353) : ℂ) * ζ ^ 2 - ((553 / 2706) : ℂ) * ζ ^ 4 + ((296 / 1353) : ℂ) * ζ ^ 6 + ((1355 / 2706) : ℂ) * ζ ^ 8 - ((2399 / 2706) : ℂ) * ζ ^ 10 - ((17 / 41) : ℂ) * ζ ^ 12 + ((2677 / 2706) : ℂ) * ζ ^ 14 - ((139 / 2706) : ℂ) * ζ ^ 16 - ((384 / 451) : ℂ) * ζ ^ 18 + ((179 / 2706) : ℂ) * ζ ^ 20 + ((497 / 2706) : ℂ) * ζ ^ 22 - ((1123 / 2706) : ℂ) * ζ ^ 24 - ((589 / 2706) : ℂ) * ζ ^ 26 + ((7 / 451) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((149 / 246) : ℂ) + ((134 / 1353) : ℂ) * ζ ^ 2 - ((797 / 1353) : ℂ) * ζ ^ 4 - ((175 / 451) : ℂ) * ζ ^ 6 + ((403 / 902) : ℂ) * ζ ^ 8 + ((1553 / 2706) : ℂ) * ζ ^ 10 + ((376 / 1353) : ℂ) * ζ ^ 12 - ((1643 / 2706) : ℂ) * ζ ^ 14 + ((15 / 902) : ℂ) * ζ ^ 16 + ((1355 / 2706) : ℂ) * ζ ^ 18 - ((383 / 2706) : ℂ) * ζ ^ 20 - ((142 / 451) : ℂ) * ζ ^ 22 + ((412 / 1353) : ℂ) * ζ ^ 24 + ((180 / 451) : ℂ) * ζ ^ 26 - ((12 / 451) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((445 / 1353) : ℂ) - ((427 / 246) : ℂ) * ζ ^ 2 - ((175 / 1353) : ℂ) * ζ ^ 4 + ((889 / 2706) : ℂ) * ζ ^ 6 - ((1355 / 902) : ℂ) * ζ ^ 8 + ((1579 / 902) : ℂ) * ζ ^ 10 + ((1150 / 1353) : ℂ) * ζ ^ 12 - ((2929 / 1353) : ℂ) * ζ ^ 14 + ((155 / 123) : ℂ) * ζ ^ 16 + ((60 / 41) : ℂ) * ζ ^ 18 - ((1109 / 1353) : ℂ) * ζ ^ 20 + ((833 / 1353) : ℂ) * ζ ^ 22 + ((2525 / 1353) : ℂ) * ζ ^ 24 - ((1105 / 1353) : ℂ) * ζ ^ 26 + ((20 / 451) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((-((149 / 246) : ℂ) - ((134 / 1353) : ℂ) * ζ ^ 2 + ((797 / 1353) : ℂ) * ζ ^ 4 + ((175 / 451) : ℂ) * ζ ^ 6 - ((403 / 902) : ℂ) * ζ ^ 8 - ((1553 / 2706) : ℂ) * ζ ^ 10 - ((376 / 1353) : ℂ) * ζ ^ 12 + ((1643 / 2706) : ℂ) * ζ ^ 14 - ((15 / 902) : ℂ) * ζ ^ 16 - ((1355 / 2706) : ℂ) * ζ ^ 18 + ((383 / 2706) : ℂ) * ζ ^ 20 + ((142 / 451) : ℂ) * ζ ^ 22 - ((412 / 1353) : ℂ) * ζ ^ 24 - ((180 / 451) : ℂ) * ζ ^ 26 + ((12 / 451) : ℂ) * ζ ^ 28)) * Y 3 3)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY55_combinationStep09
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((43 / 82) : ℂ) * ζ ^ 6 + ((31 / 82) : ℂ) * ζ ^ 8 + ((10 / 123) : ℂ) * ζ ^ 12 - ((32 / 123) : ℂ) * ζ ^ 18 + ((19 / 246) : ℂ) * ζ ^ 22 - ((13 / 246) : ℂ) * ζ ^ 24 - ((31 / 82) : ℂ) * ζ ^ 28 - ((15 / 82) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((122 / 209) : ℂ) + ((6 / 19) : ℂ) * ζ ^ 2 + ((3 / 38) : ℂ) * ζ ^ 6 + ((159 / 418) : ℂ) * ζ ^ 8 - ((155 / 418) : ℂ) * ζ ^ 12 - ((6 / 19) : ℂ) * ζ ^ 22 - ((145 / 418) : ℂ) * ζ ^ 24 - ((159 / 418) : ℂ) * ζ ^ 28 - ((7 / 38) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((107 / 209) : ℂ) + ((619 / 418) : ℂ) * ζ ^ 2 + ((25 / 22) : ℂ) * ζ ^ 6 + ((130 / 209) : ℂ) * ζ ^ 8 - ((59 / 209) : ℂ) * ζ ^ 12 - ((239 / 418) : ℂ) * ζ ^ 18 - ((619 / 418) : ℂ) * ζ ^ 22 - ((313 / 418) : ℂ) * ζ ^ 24 - ((130 / 209) : ℂ) * ζ ^ 28 - ((139 / 418) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((227 / 209) : ℂ) + ((3 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 + ((189 / 418) : ℂ) * ζ ^ 8 - ((183 / 418) : ℂ) * ζ ^ 12 + ((10 / 19) : ℂ) * ζ ^ 18 - ((3 / 19) : ℂ) * ζ ^ 22 + ((173 / 418) : ℂ) * ζ ^ 24 - ((189 / 418) : ℂ) * ζ ^ 28 + ((11 / 38) : ℂ) * ζ ^ 30)) * Y 4 5
      + ((((87 / 209) : ℂ) - ((6 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 - ((159 / 418) : ℂ) * ζ ^ 8 + ((155 / 418) : ℂ) * ζ ^ 12 + ((6 / 19) : ℂ) * ζ ^ 22 + ((145 / 418) : ℂ) * ζ ^ 24 + ((159 / 418) : ℂ) * ζ ^ 28 + ((7 / 38) : ℂ) * ζ ^ 30)) * Y 5 5
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY55_combinationStep08 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((5980 / 8569) : ℂ) + ((254 / 1353) : ℂ) * ζ ^ 2 - ((7223 / 25707) : ℂ) * ζ ^ 6 - ((3446 / 8569) : ℂ) * ζ ^ 8 + ((21611 / 25707) : ℂ) * ζ ^ 12 - ((9314 / 8569) : ℂ) * ζ ^ 18 - ((254 / 1353) : ℂ) * ζ ^ 22 + ((28189 / 25707) : ℂ) * ζ ^ 24 + ((3446 / 8569) : ℂ) * ζ ^ 28 - ((5169 / 8569) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((31473 / 94259) : ℂ) + ((71781 / 94259) : ℂ) * ζ ^ 2 - ((31473 / 94259) : ℂ) * ζ ^ 4 - ((122013 / 377036) : ℂ) * ζ ^ 6 - ((200155 / 377036) : ℂ) * ζ ^ 8 + ((131665 / 377036) : ℂ) * ζ ^ 10 - ((2825 / 377036) : ℂ) * ζ ^ 12 + ((107231 / 377036) : ℂ) * ζ ^ 14 - ((17851 / 377036) : ℂ) * ζ ^ 16 - ((5855 / 377036) : ℂ) * ζ ^ 18 - ((16679 / 94259) : ℂ) * ζ ^ 20 + ((15507 / 377036) : ℂ) * ζ ^ 22 - ((5169 / 94259) : ℂ) * ζ ^ 24 + ((15507 / 188518) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((197797 / 188518) : ℂ) + ((202809 / 94259) : ℂ) * ζ ^ 2 + ((197797 / 188518) : ℂ) * ζ ^ 4 + ((6509 / 9922) : ℂ) * ζ ^ 6 - ((223387 / 94259) : ℂ) * ζ ^ 8 - ((2048 / 4961) : ℂ) * ζ ^ 10 - ((62509 / 188518) : ℂ) * ζ ^ 12 + ((906863 / 377036) : ℂ) * ζ ^ 14 - ((17851 / 94259) : ℂ) * ζ ^ 16 + ((14833 / 188518) : ℂ) * ζ ^ 18 - ((576943 / 377036) : ℂ) * ζ ^ 20 + ((15507 / 94259) : ℂ) * ζ ^ 22 - ((5169 / 9922) : ℂ) * ζ ^ 24 + ((15507 / 19844) : ℂ) * ζ ^ 26)) * Y 1 1
        + ((((197797 / 188518) : ℂ) - ((202809 / 94259) : ℂ) * ζ ^ 2 - ((197797 / 188518) : ℂ) * ζ ^ 4 - ((6509 / 9922) : ℂ) * ζ ^ 6 + ((223387 / 94259) : ℂ) * ζ ^ 8 + ((2048 / 4961) : ℂ) * ζ ^ 10 + ((62509 / 188518) : ℂ) * ζ ^ 12 - ((906863 / 377036) : ℂ) * ζ ^ 14 + ((17851 / 94259) : ℂ) * ζ ^ 16 - ((14833 / 188518) : ℂ) * ζ ^ 18 + ((576943 / 377036) : ℂ) * ζ ^ 20 - ((15507 / 94259) : ℂ) * ζ ^ 22 + ((5169 / 9922) : ℂ) * ζ ^ 24 - ((15507 / 19844) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((105477 / 94259) : ℂ) - ((71457 / 188518) : ℂ) * ζ ^ 2 - ((105477 / 94259) : ℂ) * ζ ^ 4 - ((177963 / 188518) : ℂ) * ζ ^ 6 + ((162079 / 188518) : ℂ) * ζ ^ 8 + ((73297 / 94259) : ℂ) * ζ ^ 10 + ((78226 / 94259) : ℂ) * ζ ^ 12 - ((361507 / 377036) : ℂ) * ζ ^ 14 - ((89255 / 188518) : ℂ) * ζ ^ 16 - ((54452 / 94259) : ℂ) * ζ ^ 18 + ((263077 / 377036) : ℂ) * ζ ^ 20 + ((77535 / 188518) : ℂ) * ζ ^ 22 + ((67197 / 188518) : ℂ) * ζ ^ 24 - ((201591 / 377036) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY55_combinationStep10
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((122 / 209) : ℂ) + ((6 / 19) : ℂ) * ζ ^ 2 + ((3 / 38) : ℂ) * ζ ^ 6 + ((159 / 418) : ℂ) * ζ ^ 8 - ((155 / 418) : ℂ) * ζ ^ 12 - ((6 / 19) : ℂ) * ζ ^ 22 - ((145 / 418) : ℂ) * ζ ^ 24 - ((159 / 418) : ℂ) * ζ ^ 28 - ((7 / 38) : ℂ) * ζ ^ 30)) * Y 2 2
      + ((((107 / 209) : ℂ) + ((619 / 418) : ℂ) * ζ ^ 2 + ((25 / 22) : ℂ) * ζ ^ 6 + ((130 / 209) : ℂ) * ζ ^ 8 - ((59 / 209) : ℂ) * ζ ^ 12 - ((239 / 418) : ℂ) * ζ ^ 18 - ((619 / 418) : ℂ) * ζ ^ 22 - ((313 / 418) : ℂ) * ζ ^ 24 - ((130 / 209) : ℂ) * ζ ^ 28 - ((139 / 418) : ℂ) * ζ ^ 30)) * Y 2 3
      + ((((227 / 209) : ℂ) + ((3 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 + ((189 / 418) : ℂ) * ζ ^ 8 - ((183 / 418) : ℂ) * ζ ^ 12 + ((10 / 19) : ℂ) * ζ ^ 18 - ((3 / 19) : ℂ) * ζ ^ 22 + ((173 / 418) : ℂ) * ζ ^ 24 - ((189 / 418) : ℂ) * ζ ^ 28 + ((11 / 38) : ℂ) * ζ ^ 30)) * Y 4 5
      + ((((87 / 209) : ℂ) - ((6 / 19) : ℂ) * ζ ^ 2 - ((3 / 38) : ℂ) * ζ ^ 6 - ((159 / 418) : ℂ) * ζ ^ 8 + ((155 / 418) : ℂ) * ζ ^ 12 + ((6 / 19) : ℂ) * ζ ^ 22 + ((145 / 418) : ℂ) * ζ ^ 24 + ((159 / 418) : ℂ) * ζ ^ 28 + ((7 / 38) : ℂ) * ζ ^ 30)) * Y 5 5
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY55_combinationStep09 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((15 / 41) : ℂ) * ζ ^ 4 + ((45 / 82) : ℂ) * ζ ^ 6 - ((59 / 246) : ℂ) * ζ ^ 8 - ((69 / 82) : ℂ) * ζ ^ 10 - ((19 / 246) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ((65 / 246) : ℂ) * ζ ^ 16 - ((107 / 246) : ℂ) * ζ ^ 18 - ((29 / 82) : ℂ) * ζ ^ 20 + ((35 / 246) : ℂ) * ζ ^ 22 + ((10 / 41) : ℂ) * ζ ^ 24 - ((5 / 246) : ℂ) * ζ ^ 26 - ((7 / 123) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 + ((40 / 123) : ℂ) * ζ ^ 4 - ((85 / 246) : ℂ) * ζ ^ 6 - ((19 / 82) : ℂ) * ζ ^ 8 + ((103 / 246) : ℂ) * ζ ^ 10 + ((5 / 82) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ((47 / 246) : ℂ) * ζ ^ 16 + ((13 / 41) : ℂ) * ζ ^ 18 + ((73 / 246) : ℂ) * ζ ^ 20 - ((10 / 41) : ℂ) * ζ ^ 22 - ((28 / 123) : ℂ) * ζ ^ 24 + ((16 / 123) : ℂ) * ζ ^ 26 + ((4 / 41) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((4 / 41) : ℂ) * ζ ^ 4 - ((53 / 82) : ℂ) * ζ ^ 6 + ((68 / 123) : ℂ) * ζ ^ 8 + ((125 / 82) : ℂ) * ζ ^ 10 + ((49 / 123) : ℂ) * ζ ^ 12 - ((5 / 3) : ℂ) * ζ ^ 14 - ((53 / 41) : ℂ) * ζ ^ 16 + ((17 / 123) : ℂ) * ζ ^ 18 + ((151 / 123) : ℂ) * ζ ^ 20 + ((91 / 123) : ℂ) * ζ ^ 22 - ((30 / 41) : ℂ) * ζ ^ 24 - ((95 / 123) : ℂ) * ζ ^ 26 - ((20 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 - ((40 / 123) : ℂ) * ζ ^ 4 + ((85 / 246) : ℂ) * ζ ^ 6 + ((19 / 82) : ℂ) * ζ ^ 8 - ((103 / 246) : ℂ) * ζ ^ 10 - ((5 / 82) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((47 / 246) : ℂ) * ζ ^ 16 - ((13 / 41) : ℂ) * ζ ^ 18 - ((73 / 246) : ℂ) * ζ ^ 20 + ((10 / 41) : ℂ) * ζ ^ 22 + ((28 / 123) : ℂ) * ζ ^ 24 - ((16 / 123) : ℂ) * ζ ^ 26 - ((4 / 41) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY55_combinationStep11
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 5 5
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY55_combinationStep10 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation25
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((22 / 19) : ℂ) - ((74 / 19) : ℂ) * ζ ^ 2 - ((64 / 19) : ℂ) * ζ ^ 6 - (2 : ℂ) * ζ ^ 8 - ((50 / 19) : ℂ) * ζ ^ 12 + ((46 / 19) : ℂ) * ζ ^ 18 + ((74 / 19) : ℂ) * ζ ^ 22 + ((16 / 19) : ℂ) * ζ ^ 24 + (2 : ℂ) * ζ ^ 28 - ((34 / 19) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((89 / 209) : ℂ) - ((79 / 418) : ℂ) * ζ ^ 2 - ((141 / 418) : ℂ) * ζ ^ 4 - ((117 / 209) : ℂ) * ζ ^ 6 - ((172 / 209) : ℂ) * ζ ^ 8 + ((105 / 418) : ℂ) * ζ ^ 10 - ((7 / 38) : ℂ) * ζ ^ 12 - ((35 / 418) : ℂ) * ζ ^ 14 + ((1 / 11) : ℂ) * ζ ^ 16 + ((45 / 209) : ℂ) * ζ ^ 18 + ((11 / 19) : ℂ) * ζ ^ 20 - ((219 / 418) : ℂ) * ζ ^ 22 + ((13 / 209) : ℂ) * ζ ^ 24 + ((91 / 209) : ℂ) * ζ ^ 26 - ((51 / 209) : ℂ) * ζ ^ 28)) * Y 2 2
        + ((((41 / 209) : ℂ) + ((82 / 209) : ℂ) * ζ ^ 2 - ((119 / 418) : ℂ) * ζ ^ 4 - ((141 / 209) : ℂ) * ζ ^ 6 - ((29 / 22) : ℂ) * ζ ^ 8 + ((17 / 19) : ℂ) * ζ ^ 10 - ((327 / 418) : ℂ) * ζ ^ 12 - ((139 / 209) : ℂ) * ζ ^ 14 + ((347 / 418) : ℂ) * ζ ^ 16 + ((145 / 418) : ℂ) * ζ ^ 18 + ((27 / 209) : ℂ) * ζ ^ 20 - ((53 / 418) : ℂ) * ζ ^ 22 - ((45 / 418) : ℂ) * ζ ^ 24 - ((15 / 38) : ℂ) * ζ ^ 26 + ((51 / 209) : ℂ) * ζ ^ 28)) * Y 2 3
        + ((((238 / 209) : ℂ) + ((48 / 209) : ℂ) * ζ ^ 2 - ((312 / 209) : ℂ) * ζ ^ 4 - ((175 / 418) : ℂ) * ζ ^ 6 + ((83 / 209) : ℂ) * ζ ^ 8 - ((265 / 209) : ℂ) * ζ ^ 10 + ((4 / 19) : ℂ) * ζ ^ 12 + ((569 / 418) : ℂ) * ζ ^ 14 - ((559 / 418) : ℂ) * ζ ^ 16 + ((25 / 418) : ℂ) * ζ ^ 18 + ((41 / 19) : ℂ) * ζ ^ 20 - ((365 / 209) : ℂ) * ζ ^ 22 + ((17 / 418) : ℂ) * ζ ^ 24 + ((669 / 418) : ℂ) * ζ ^ 26 - ((170 / 209) : ℂ) * ζ ^ 28)) * Y 4 5
        + ((-((89 / 209) : ℂ) + ((79 / 418) : ℂ) * ζ ^ 2 + ((141 / 418) : ℂ) * ζ ^ 4 + ((117 / 209) : ℂ) * ζ ^ 6 + ((172 / 209) : ℂ) * ζ ^ 8 - ((105 / 418) : ℂ) * ζ ^ 10 + ((7 / 38) : ℂ) * ζ ^ 12 + ((35 / 418) : ℂ) * ζ ^ 14 - ((1 / 11) : ℂ) * ζ ^ 16 - ((45 / 209) : ℂ) * ζ ^ 18 - ((11 / 19) : ℂ) * ζ ^ 20 + ((219 / 418) : ℂ) * ζ ^ 22 - ((13 / 209) : ℂ) * ζ ^ 24 - ((91 / 209) : ℂ) * ζ ^ 26 + ((51 / 209) : ℂ) * ζ ^ 28)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY55
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 5 5 = Y 7 7 := by
  have reduced :=
    row17_reducedY55_combinationStep11 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row17_reducedY66_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((221 / 246) : ℂ) - ((634 / 123) : ℂ) * ζ ^ 2 + ((955 / 246) : ℂ) * ζ ^ 6 + ((719 / 246) : ℂ) * ζ ^ 8 + ((75 / 41) : ℂ) * ζ ^ 12 + ((135 / 82) : ℂ) * ζ ^ 18 + ((634 / 123) : ℂ) * ζ ^ 22 + ((727 / 492) : ℂ) * ζ ^ 24 - ((719 / 246) : ℂ) * ζ ^ 28 - ((4 / 123) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((87 / 82) : ℂ) + ((77 / 123) : ℂ) * ζ ^ 2 + ((137 / 82) : ℂ) * ζ ^ 6 + ((147 / 164) : ℂ) * ζ ^ 8 - ((7 / 492) : ℂ) * ζ ^ 12 - ((142 / 123) : ℂ) * ζ ^ 18 - ((77 / 123) : ℂ) * ζ ^ 22 - ((223 / 492) : ℂ) * ζ ^ 24 - ((147 / 164) : ℂ) * ζ ^ 28 - ((32 / 41) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((529 / 123) : ℂ) + ((420 / 41) : ℂ) * ζ ^ 2 + ((1514 / 123) : ℂ) * ζ ^ 6 + ((671 / 123) : ℂ) * ζ ^ 8 + ((147 / 41) : ℂ) * ζ ^ 12 - ((952 / 123) : ℂ) * ζ ^ 18 - ((420 / 41) : ℂ) * ζ ^ 22 - ((752 / 123) : ℂ) * ζ ^ 24 - ((671 / 123) : ℂ) * ζ ^ 28 + ((274 / 41) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((29 / 164) : ℂ) + ((949 / 123) : ℂ) * ζ ^ 2 + ((29 / 164) : ℂ) * ζ ^ 4 - ((1048 / 123) : ℂ) * ζ ^ 6 + ((733 / 492) : ℂ) * ζ ^ 8 + ((103 / 123) : ℂ) * ζ ^ 10 - ((19 / 4) : ℂ) * ζ ^ 12 + ((227 / 82) : ℂ) * ζ ^ 14 + ((27 / 41) : ℂ) * ζ ^ 16 - ζ ^ 18 + ((107 / 123) : ℂ) * ζ ^ 20 - ((274 / 41) : ℂ) * ζ ^ 22 - ((671 / 164) : ℂ) * ζ ^ 24 + ((411 / 82) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((87 / 82) : ℂ) - ((77 / 123) : ℂ) * ζ ^ 2 - ((87 / 82) : ℂ) * ζ ^ 4 - ((257 / 246) : ℂ) * ζ ^ 6 + ((27 / 164) : ℂ) * ζ ^ 8 + ((257 / 246) : ℂ) * ζ ^ 10 - ((27 / 164) : ℂ) * ζ ^ 12 + ((73 / 82) : ℂ) * ζ ^ 14 + ((27 / 164) : ℂ) * ζ ^ 16 + ((137 / 82) : ℂ) * ζ ^ 18 + ((671 / 492) : ℂ) * ζ ^ 20 - ((137 / 82) : ℂ) * ζ ^ 22)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY66_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((31 / 246) : ℂ) - ((74 / 41) : ℂ) * ζ ^ 2 - ((341 / 246) : ℂ) * ζ ^ 6 - ((33 / 82) : ℂ) * ζ ^ 8 - ((131 / 123) : ℂ) * ζ ^ 12 + ((289 / 246) : ℂ) * ζ ^ 18 + ((74 / 41) : ℂ) * ζ ^ 22 + ((201 / 164) : ℂ) * ζ ^ 24 + ((33 / 82) : ℂ) * ζ ^ 28 - ((310 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((275 / 492) : ℂ) - ((13 / 41) : ℂ) * ζ ^ 2 - ((25 / 246) : ℂ) * ζ ^ 6 - ((529 / 492) : ℂ) * ζ ^ 8 - ((71 / 492) : ℂ) * ζ ^ 12 - ((263 / 123) : ℂ) * ζ ^ 18 + ((13 / 41) : ℂ) * ζ ^ 22 + ((10 / 123) : ℂ) * ζ ^ 24 + ((529 / 492) : ℂ) * ζ ^ 28 + ((85 / 246) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((87 / 82) : ℂ) + ((77 / 123) : ℂ) * ζ ^ 2 + ((137 / 82) : ℂ) * ζ ^ 6 + ((147 / 164) : ℂ) * ζ ^ 8 - ((7 / 492) : ℂ) * ζ ^ 12 - ((142 / 123) : ℂ) * ζ ^ 18 - ((77 / 123) : ℂ) * ζ ^ 22 - ((223 / 492) : ℂ) * ζ ^ 24 - ((147 / 164) : ℂ) * ζ ^ 28 - ((32 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((31 / 246) : ℂ) + ((74 / 41) : ℂ) * ζ ^ 2 + ((341 / 246) : ℂ) * ζ ^ 6 + ((33 / 82) : ℂ) * ζ ^ 8 + ((131 / 123) : ℂ) * ζ ^ 12 - ((289 / 246) : ℂ) * ζ ^ 18 - ((74 / 41) : ℂ) * ζ ^ 22 - ((201 / 164) : ℂ) * ζ ^ 24 - ((33 / 82) : ℂ) * ζ ^ 28 + ((310 / 123) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY66_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((154 / 41) : ℂ) + ((226 / 123) : ℂ) * ζ ^ 2 + ((110 / 41) : ℂ) * ζ ^ 6 + ((277 / 123) : ℂ) * ζ ^ 8 + ((66 / 41) : ℂ) * ζ ^ 12 + ((662 / 123) : ℂ) * ζ ^ 18 - ((226 / 123) : ℂ) * ζ ^ 22 - ((47 / 41) : ℂ) * ζ ^ 24 - ((277 / 123) : ℂ) * ζ ^ 28 + ((682 / 123) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((31 / 246) : ℂ) + ((74 / 41) : ℂ) * ζ ^ 2 + ((31 / 246) : ℂ) * ζ ^ 4 - ((103 / 246) : ℂ) * ζ ^ 6 + ((34 / 123) : ℂ) * ζ ^ 8 + ((103 / 246) : ℂ) * ζ ^ 10 - ((34 / 123) : ℂ) * ζ ^ 12 + ((38 / 41) : ℂ) * ζ ^ 14 + ((34 / 123) : ℂ) * ζ ^ 16 - ((341 / 246) : ℂ) * ζ ^ 18 - ((277 / 492) : ℂ) * ζ ^ 20 + ((341 / 246) : ℂ) * ζ ^ 22)) * Y 0 0
        + ((((295 / 492) : ℂ) - ((359 / 82) : ℂ) * ζ ^ 2 - ((295 / 492) : ℂ) * ζ ^ 4 + ((1111 / 123) : ℂ) * ζ ^ 6 + ((1153 / 492) : ℂ) * ζ ^ 8 - ((2561 / 246) : ℂ) * ζ ^ 10 - ((151 / 492) : ℂ) * ζ ^ 12 + ((146 / 41) : ℂ) * ζ ^ 14 - ((170 / 123) : ℂ) * ζ ^ 16 + ((683 / 123) : ℂ) * ζ ^ 18 + ((481 / 246) : ℂ) * ζ ^ 20 - ((1705 / 246) : ℂ) * ζ ^ 22 - ((277 / 164) : ℂ) * ζ ^ 24 + ((341 / 82) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((31 / 246) : ℂ) - ((74 / 41) : ℂ) * ζ ^ 2 - ((31 / 246) : ℂ) * ζ ^ 4 + ((103 / 246) : ℂ) * ζ ^ 6 - ((34 / 123) : ℂ) * ζ ^ 8 - ((103 / 246) : ℂ) * ζ ^ 10 + ((34 / 123) : ℂ) * ζ ^ 12 - ((38 / 41) : ℂ) * ζ ^ 14 - ((34 / 123) : ℂ) * ζ ^ 16 + ((341 / 246) : ℂ) * ζ ^ 18 + ((277 / 492) : ℂ) * ζ ^ 20 - ((341 / 246) : ℂ) * ζ ^ 22)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY66_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((43 / 123) : ℂ) - ((5 / 41) : ℂ) * ζ ^ 2 + ((104 / 123) : ℂ) * ζ ^ 6 + ((18 / 41) : ℂ) * ζ ^ 8 - ((77 / 123) : ℂ) * ζ ^ 12 - ((16 / 123) : ℂ) * ζ ^ 18 + ((5 / 41) : ℂ) * ζ ^ 22 + ((16 / 41) : ℂ) * ζ ^ 24 - ((18 / 41) : ℂ) * ζ ^ 28 - ((124 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((20 / 123) : ℂ) + ((32 / 41) : ℂ) * ζ ^ 2 + ((97 / 123) : ℂ) * ζ ^ 6 - ((34 / 123) : ℂ) * ζ ^ 8 + ((91 / 123) : ℂ) * ζ ^ 12 - ((119 / 123) : ℂ) * ζ ^ 18 - ((32 / 41) : ℂ) * ζ ^ 22 - ((53 / 123) : ℂ) * ζ ^ 24 + ((34 / 123) : ℂ) * ζ ^ 28 + ((359 / 123) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((87 / 82) : ℂ) + ((77 / 123) : ℂ) * ζ ^ 2 + ((137 / 82) : ℂ) * ζ ^ 6 + ((147 / 164) : ℂ) * ζ ^ 8 - ((7 / 492) : ℂ) * ζ ^ 12 - ((142 / 123) : ℂ) * ζ ^ 18 - ((77 / 123) : ℂ) * ζ ^ 22 - ((223 / 492) : ℂ) * ζ ^ 24 - ((147 / 164) : ℂ) * ζ ^ 28 - ((32 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((31 / 246) : ℂ) + ((74 / 41) : ℂ) * ζ ^ 2 + ((341 / 246) : ℂ) * ζ ^ 6 + ((33 / 82) : ℂ) * ζ ^ 8 + ((131 / 123) : ℂ) * ζ ^ 12 - ((289 / 246) : ℂ) * ζ ^ 18 - ((74 / 41) : ℂ) * ζ ^ 22 - ((201 / 164) : ℂ) * ζ ^ 24 - ((33 / 82) : ℂ) * ζ ^ 28 + ((310 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((39 / 82) : ℂ) - ((69 / 41) : ℂ) * ζ ^ 2 - ((183 / 82) : ℂ) * ζ ^ 6 - ((69 / 82) : ℂ) * ζ ^ 8 - ((18 / 41) : ℂ) * ζ ^ 12 + ((107 / 82) : ℂ) * ζ ^ 18 + ((69 / 41) : ℂ) * ζ ^ 22 + ((137 / 164) : ℂ) * ζ ^ 24 + ((69 / 82) : ℂ) * ζ ^ 28 - ((62 / 41) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((173 / 902) : ℂ) + ((120 / 451) : ℂ) * ζ ^ 2 - ((639 / 902) : ℂ) * ζ ^ 6 - ((413 / 902) : ℂ) * ζ ^ 8 - ((285 / 902) : ℂ) * ζ ^ 12 - ((687 / 902) : ℂ) * ζ ^ 18 - ((120 / 451) : ℂ) * ζ ^ 22 + ((145 / 1804) : ℂ) * ζ ^ 24 + ((413 / 902) : ℂ) * ζ ^ 28 - ((197 / 451) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY66_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((758 / 1353) : ℂ) - ((3622 / 1353) : ℂ) * ζ ^ 2 - ((1778 / 1353) : ℂ) * ζ ^ 6 - ((581 / 1353) : ℂ) * ζ ^ 8 - ((126 / 451) : ℂ) * ζ ^ 12 + ((2374 / 1353) : ℂ) * ζ ^ 18 + ((3622 / 1353) : ℂ) * ζ ^ 22 + ((1283 / 1353) : ℂ) * ζ ^ 24 + ((581 / 1353) : ℂ) * ζ ^ 28 - ((2450 / 1353) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((1687 / 9922) : ℂ) - ((1105 / 4961) : ℂ) * ζ ^ 2 - ((1687 / 9922) : ℂ) * ζ ^ 4 - ((12821 / 9922) : ℂ) * ζ ^ 6 - ((1790 / 4961) : ℂ) * ζ ^ 8 + ((9199 / 9922) : ℂ) * ζ ^ 10 - ((115 / 4961) : ℂ) * ζ ^ 12 - ((255 / 4961) : ℂ) * ζ ^ 14 - ((351 / 9922) : ℂ) * ζ ^ 16 - ((4847 / 9922) : ℂ) * ζ ^ 18 - ((3147 / 19844) : ℂ) * ζ ^ 20 + ((1225 / 9922) : ℂ) * ζ ^ 22 - ((581 / 9922) : ℂ) * ζ ^ 24 + ((1225 / 4961) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((23783 / 19844) : ℂ) + ((27141 / 9922) : ℂ) * ζ ^ 2 + ((23783 / 19844) : ℂ) * ζ ^ 4 - ((17305 / 9922) : ℂ) * ζ ^ 6 - ((13031 / 19844) : ℂ) * ζ ^ 8 - ((8552 / 4961) : ℂ) * ζ ^ 10 - ((8231 / 19844) : ℂ) * ζ ^ 12 - ((811 / 4961) : ℂ) * ζ ^ 14 - ((702 / 4961) : ℂ) * ζ ^ 16 - ((39309 / 9922) : ℂ) * ζ ^ 18 - ((26701 / 19844) : ℂ) * ζ ^ 20 + ((2450 / 4961) : ℂ) * ζ ^ 22 - ((11039 / 19844) : ℂ) * ζ ^ 24 + ((23275 / 9922) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((1687 / 9922) : ℂ) + ((1105 / 4961) : ℂ) * ζ ^ 2 + ((1687 / 9922) : ℂ) * ζ ^ 4 + ((12821 / 9922) : ℂ) * ζ ^ 6 + ((1790 / 4961) : ℂ) * ζ ^ 8 - ((9199 / 9922) : ℂ) * ζ ^ 10 + ((115 / 4961) : ℂ) * ζ ^ 12 + ((255 / 4961) : ℂ) * ζ ^ 14 + ((351 / 9922) : ℂ) * ζ ^ 16 + ((4847 / 9922) : ℂ) * ζ ^ 18 + ((3147 / 19844) : ℂ) * ζ ^ 20 - ((1225 / 9922) : ℂ) * ζ ^ 22 + ((581 / 9922) : ℂ) * ζ ^ 24 - ((1225 / 4961) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((2661 / 9922) : ℂ) - ((3131 / 4961) : ℂ) * ζ ^ 2 - ((2661 / 9922) : ℂ) * ζ ^ 4 + ((11513 / 9922) : ℂ) * ζ ^ 6 + ((4349 / 9922) : ℂ) * ζ ^ 8 - ((647 / 9922) : ℂ) * ζ ^ 10 + ((345 / 4961) : ℂ) * ζ ^ 12 + ((765 / 4961) : ℂ) * ζ ^ 14 + ((1053 / 9922) : ℂ) * ζ ^ 16 + ((14541 / 9922) : ℂ) * ζ ^ 18 + ((9441 / 19844) : ℂ) * ζ ^ 20 - ((3675 / 9922) : ℂ) * ζ ^ 22 + ((1743 / 9922) : ℂ) * ζ ^ 24 - ((3675 / 4961) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY66_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((10 / 123) : ℂ) + ((16 / 41) : ℂ) * ζ ^ 2 + ((97 / 246) : ℂ) * ζ ^ 6 - ((17 / 123) : ℂ) * ζ ^ 8 + ((91 / 246) : ℂ) * ζ ^ 12 - ((119 / 246) : ℂ) * ζ ^ 18 - ((16 / 41) : ℂ) * ζ ^ 22 - ((53 / 246) : ℂ) * ζ ^ 24 + ((17 / 123) : ℂ) * ζ ^ 28 + ((359 / 246) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((87 / 82) : ℂ) + ((77 / 123) : ℂ) * ζ ^ 2 + ((137 / 82) : ℂ) * ζ ^ 6 + ((147 / 164) : ℂ) * ζ ^ 8 - ((7 / 492) : ℂ) * ζ ^ 12 - ((142 / 123) : ℂ) * ζ ^ 18 - ((77 / 123) : ℂ) * ζ ^ 22 - ((223 / 492) : ℂ) * ζ ^ 24 - ((147 / 164) : ℂ) * ζ ^ 28 - ((32 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((31 / 246) : ℂ) + ((74 / 41) : ℂ) * ζ ^ 2 + ((341 / 246) : ℂ) * ζ ^ 6 + ((33 / 82) : ℂ) * ζ ^ 8 + ((131 / 123) : ℂ) * ζ ^ 12 - ((289 / 246) : ℂ) * ζ ^ 18 - ((74 / 41) : ℂ) * ζ ^ 22 - ((201 / 164) : ℂ) * ζ ^ 24 - ((33 / 82) : ℂ) * ζ ^ 28 + ((310 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((39 / 82) : ℂ) - ((69 / 41) : ℂ) * ζ ^ 2 - ((183 / 82) : ℂ) * ζ ^ 6 - ((69 / 82) : ℂ) * ζ ^ 8 - ((18 / 41) : ℂ) * ζ ^ 12 + ((107 / 82) : ℂ) * ζ ^ 18 + ((69 / 41) : ℂ) * ζ ^ 22 + ((137 / 164) : ℂ) * ζ ^ 24 + ((69 / 82) : ℂ) * ζ ^ 28 - ((62 / 41) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((173 / 902) : ℂ) + ((120 / 451) : ℂ) * ζ ^ 2 - ((639 / 902) : ℂ) * ζ ^ 6 - ((413 / 902) : ℂ) * ζ ^ 8 - ((285 / 902) : ℂ) * ζ ^ 12 - ((687 / 902) : ℂ) * ζ ^ 18 - ((120 / 451) : ℂ) * ζ ^ 22 + ((145 / 1804) : ℂ) * ζ ^ 24 + ((413 / 902) : ℂ) * ζ ^ 28 - ((197 / 451) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 6 6
      + ((-((17 / 123) : ℂ) + ((79 / 82) : ℂ) * ζ ^ 2 - ((6 / 41) : ℂ) * ζ ^ 6 + ((49 / 123) : ℂ) * ζ ^ 8 + ((85 / 246) : ℂ) * ζ ^ 12 - ((13 / 123) : ℂ) * ζ ^ 18 - ((79 / 82) : ℂ) * ζ ^ 22 - ((28 / 41) : ℂ) * ζ ^ 24 - ((49 / 123) : ℂ) * ζ ^ 28 + ((53 / 123) : ℂ) * ζ ^ 30)) * Y 7 6) = 0 := by
  have previous :=
    row17_reducedY66_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation06
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((2 / 3) : ℂ) - (2 : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 - ((8 / 3) : ℂ) * ζ ^ 12 + ((4 / 3) : ℂ) * ζ ^ 18 + (2 : ℂ) * ζ ^ 22 + ((10 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28)) * equation
      - (
        ((((44 / 123) : ℂ) - ((61 / 246) : ℂ) * ζ ^ 2 - ((11 / 123) : ℂ) * ζ ^ 4 + ((151 / 246) : ℂ) * ζ ^ 6 + ((23 / 41) : ℂ) * ζ ^ 8 - ((73 / 82) : ℂ) * ζ ^ 10 - ((22 / 41) : ℂ) * ζ ^ 12 + ((53 / 82) : ℂ) * ζ ^ 14 + ((28 / 41) : ℂ) * ζ ^ 16 - ((14 / 41) : ℂ) * ζ ^ 18 - ((95 / 246) : ℂ) * ζ ^ 20 + ((8 / 123) : ℂ) * ζ ^ 22 - ((5 / 41) : ℂ) * ζ ^ 24 + ((2 / 123) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((11 / 123) : ℂ) + ((35 / 41) : ℂ) * ζ ^ 2 - ((151 / 123) : ℂ) * ζ ^ 4 - ((8 / 41) : ℂ) * ζ ^ 6 - ((137 / 246) : ℂ) * ζ ^ 8 + ((45 / 41) : ℂ) * ζ ^ 10 + ((37 / 123) : ℂ) * ζ ^ 12 - ((107 / 123) : ℂ) * ζ ^ 14 - ((48 / 41) : ℂ) * ζ ^ 16 + ((31 / 123) : ℂ) * ζ ^ 18 + ((304 / 123) : ℂ) * ζ ^ 20 + ((80 / 123) : ℂ) * ζ ^ 22 + ((55 / 123) : ℂ) * ζ ^ 24 + ((20 / 123) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((44 / 123) : ℂ) + ((61 / 246) : ℂ) * ζ ^ 2 + ((11 / 123) : ℂ) * ζ ^ 4 - ((151 / 246) : ℂ) * ζ ^ 6 - ((23 / 41) : ℂ) * ζ ^ 8 + ((73 / 82) : ℂ) * ζ ^ 10 + ((22 / 41) : ℂ) * ζ ^ 12 - ((53 / 82) : ℂ) * ζ ^ 14 - ((28 / 41) : ℂ) * ζ ^ 16 + ((14 / 41) : ℂ) * ζ ^ 18 + ((95 / 246) : ℂ) * ζ ^ 20 - ((8 / 123) : ℂ) * ζ ^ 22 + ((5 / 41) : ℂ) * ζ ^ 24 - ((2 / 123) : ℂ) * ζ ^ 26)) * Y 6 6
        + ((((7 / 82) : ℂ) - ((39 / 41) : ℂ) * ζ ^ 2 + ((29 / 82) : ℂ) * ζ ^ 4 + ((131 / 123) : ℂ) * ζ ^ 6 - ((25 / 123) : ℂ) * ζ ^ 8 - ((295 / 246) : ℂ) * ζ ^ 10 + ((71 / 246) : ℂ) * ζ ^ 12 + ((167 / 246) : ℂ) * ζ ^ 14 + ((7 / 123) : ℂ) * ζ ^ 16 - ((89 / 246) : ℂ) * ζ ^ 18 - ((11 / 41) : ℂ) * ζ ^ 20 + ((28 / 123) : ℂ) * ζ ^ 22 - ((23 / 246) : ℂ) * ζ ^ 24 + ((7 / 123) : ℂ) * ζ ^ 26)) * Y 7 6)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY66_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((87 / 82) : ℂ) + ((77 / 123) : ℂ) * ζ ^ 2 + ((137 / 82) : ℂ) * ζ ^ 6 + ((147 / 164) : ℂ) * ζ ^ 8 - ((7 / 492) : ℂ) * ζ ^ 12 - ((142 / 123) : ℂ) * ζ ^ 18 - ((77 / 123) : ℂ) * ζ ^ 22 - ((223 / 492) : ℂ) * ζ ^ 24 - ((147 / 164) : ℂ) * ζ ^ 28 - ((32 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((31 / 246) : ℂ) + ((74 / 41) : ℂ) * ζ ^ 2 + ((341 / 246) : ℂ) * ζ ^ 6 + ((33 / 82) : ℂ) * ζ ^ 8 + ((131 / 123) : ℂ) * ζ ^ 12 - ((289 / 246) : ℂ) * ζ ^ 18 - ((74 / 41) : ℂ) * ζ ^ 22 - ((201 / 164) : ℂ) * ζ ^ 24 - ((33 / 82) : ℂ) * ζ ^ 28 + ((310 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((39 / 82) : ℂ) - ((69 / 41) : ℂ) * ζ ^ 2 - ((183 / 82) : ℂ) * ζ ^ 6 - ((69 / 82) : ℂ) * ζ ^ 8 - ((18 / 41) : ℂ) * ζ ^ 12 + ((107 / 82) : ℂ) * ζ ^ 18 + ((69 / 41) : ℂ) * ζ ^ 22 + ((137 / 164) : ℂ) * ζ ^ 24 + ((69 / 82) : ℂ) * ζ ^ 28 - ((62 / 41) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((173 / 902) : ℂ) + ((120 / 451) : ℂ) * ζ ^ 2 - ((639 / 902) : ℂ) * ζ ^ 6 - ((413 / 902) : ℂ) * ζ ^ 8 - ((285 / 902) : ℂ) * ζ ^ 12 - ((687 / 902) : ℂ) * ζ ^ 18 - ((120 / 451) : ℂ) * ζ ^ 22 + ((145 / 1804) : ℂ) * ζ ^ 24 + ((413 / 902) : ℂ) * ζ ^ 28 - ((197 / 451) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 6 6
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((17 / 123) : ℂ) + ((79 / 82) : ℂ) * ζ ^ 2 - ((6 / 41) : ℂ) * ζ ^ 6 + ((49 / 123) : ℂ) * ζ ^ 8 + ((85 / 246) : ℂ) * ζ ^ 12 - ((13 / 123) : ℂ) * ζ ^ 18 - ((79 / 82) : ℂ) * ζ ^ 22 - ((28 / 41) : ℂ) * ζ ^ 24 - ((49 / 123) : ℂ) * ζ ^ 28 + ((53 / 123) : ℂ) * ζ ^ 30)) * Y 7 6
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY66_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) + (2 : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 + ((4 / 3) : ℂ) * ζ ^ 12 - (2 : ℂ) * ζ ^ 22 - ((2 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28 + ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((179 / 246) : ℂ) - ((2 / 41) : ℂ) * ζ ^ 2 + ((7 / 6) : ℂ) * ζ ^ 4 + ((18 / 41) : ℂ) * ζ ^ 6 - ((62 / 123) : ℂ) * ζ ^ 8 - ((71 / 82) : ℂ) * ζ ^ 10 - ((73 / 246) : ℂ) * ζ ^ 12 + ((193 / 246) : ℂ) * ζ ^ 14 + ((34 / 41) : ℂ) * ζ ^ 16 - ((35 / 82) : ℂ) * ζ ^ 18 - ((94 / 123) : ℂ) * ζ ^ 20 + ((79 / 246) : ℂ) * ζ ^ 24 + ((13 / 41) : ℂ) * ζ ^ 26 - ((28 / 123) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((7 / 123) : ℂ) + ((1 / 82) : ℂ) * ζ ^ 2 - ((1 / 6) : ℂ) * ζ ^ 4 + ((55 / 246) : ℂ) * ζ ^ 6 + ((31 / 246) : ℂ) * ζ ^ 8 + ((1 / 123) : ℂ) * ζ ^ 10 + ((49 / 246) : ℂ) * ζ ^ 12 - ((20 / 41) : ℂ) * ζ ^ 14 - ((46 / 123) : ℂ) * ζ ^ 16 + ((19 / 82) : ℂ) * ζ ^ 18 + ((44 / 123) : ℂ) * ζ ^ 20 - ((56 / 123) : ℂ) * ζ ^ 24 - ((20 / 123) : ℂ) * ζ ^ 26 + ((16 / 41) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((-((8 / 123) : ℂ) - ((103 / 246) : ℂ) * ζ ^ 2 + ((1 / 3) : ℂ) * ζ ^ 4 + ((63 / 82) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 - ((301 / 246) : ℂ) * ζ ^ 10 - ((23 / 41) : ℂ) * ζ ^ 12 + ((143 / 246) : ℂ) * ζ ^ 14 + ((39 / 41) : ℂ) * ζ ^ 16 + ((26 / 123) : ℂ) * ζ ^ 18 - ((55 / 82) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((23 / 123) : ℂ) * ζ ^ 24 + ((58 / 123) : ℂ) * ζ ^ 26 - ((8 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((179 / 246) : ℂ) + ((2 / 41) : ℂ) * ζ ^ 2 - ((7 / 6) : ℂ) * ζ ^ 4 - ((18 / 41) : ℂ) * ζ ^ 6 + ((62 / 123) : ℂ) * ζ ^ 8 + ((71 / 82) : ℂ) * ζ ^ 10 + ((73 / 246) : ℂ) * ζ ^ 12 - ((193 / 246) : ℂ) * ζ ^ 14 - ((34 / 41) : ℂ) * ζ ^ 16 + ((35 / 82) : ℂ) * ζ ^ 18 + ((94 / 123) : ℂ) * ζ ^ 20 - ((79 / 246) : ℂ) * ζ ^ 24 - ((13 / 41) : ℂ) * ζ ^ 26 + ((28 / 123) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY66_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((30 / 41) : ℂ) - ((19 / 123) : ℂ) * ζ ^ 2 + ((43 / 41) : ℂ) * ζ ^ 6 + ((31 / 41) : ℂ) * ζ ^ 8 + ((20 / 123) : ℂ) * ζ ^ 12 - ((64 / 123) : ℂ) * ζ ^ 18 + ((19 / 123) : ℂ) * ζ ^ 22 - ((13 / 123) : ℂ) * ζ ^ 24 - ((31 / 41) : ℂ) * ζ ^ 28 - ((15 / 41) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((43 / 123) : ℂ) + ((5 / 41) : ℂ) * ζ ^ 2 - ((104 / 123) : ℂ) * ζ ^ 6 - ((18 / 41) : ℂ) * ζ ^ 8 + ((77 / 123) : ℂ) * ζ ^ 12 + ((16 / 123) : ℂ) * ζ ^ 18 - ((5 / 41) : ℂ) * ζ ^ 22 - ((16 / 41) : ℂ) * ζ ^ 24 + ((18 / 41) : ℂ) * ζ ^ 28 + ((124 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 6 6
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((17 / 123) : ℂ) + ((79 / 82) : ℂ) * ζ ^ 2 - ((6 / 41) : ℂ) * ζ ^ 6 + ((49 / 123) : ℂ) * ζ ^ 8 + ((85 / 246) : ℂ) * ζ ^ 12 - ((13 / 123) : ℂ) * ζ ^ 18 - ((79 / 82) : ℂ) * ζ ^ 22 - ((28 / 41) : ℂ) * ζ ^ 24 - ((49 / 123) : ℂ) * ζ ^ 28 + ((53 / 123) : ℂ) * ζ ^ 30)) * Y 7 6
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY66_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((509 / 1353) : ℂ) + ((508 / 1353) : ℂ) * ζ ^ 2 + ((158 / 451) : ℂ) * ζ ^ 6 - ((115 / 1353) : ℂ) * ζ ^ 8 - ((265 / 1353) : ℂ) * ζ ^ 12 - ((1612 / 1353) : ℂ) * ζ ^ 18 - ((508 / 1353) : ℂ) * ζ ^ 22 - ((166 / 1353) : ℂ) * ζ ^ 24 + ((115 / 1353) : ℂ) * ζ ^ 28 - ((398 / 1353) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((1231 / 9922) : ℂ) + ((2856 / 4961) : ℂ) * ζ ^ 2 + ((1231 / 9922) : ℂ) * ζ ^ 4 - ((1437 / 9922) : ℂ) * ζ ^ 6 + ((223 / 19844) : ℂ) * ζ ^ 8 + ((1945 / 9922) : ℂ) * ζ ^ 10 - ((511 / 19844) : ℂ) * ζ ^ 12 + ((2463 / 9922) : ℂ) * ζ ^ 14 + ((281 / 19844) : ℂ) * ζ ^ 16 + ((309 / 9922) : ℂ) * ζ ^ 18 + ((217 / 19844) : ℂ) * ζ ^ 20 + ((199 / 9922) : ℂ) * ζ ^ 22 - ((115 / 9922) : ℂ) * ζ ^ 24 + ((199 / 4961) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((1251 / 19844) : ℂ) + ((5682 / 4961) : ℂ) * ζ ^ 2 - ((1251 / 19844) : ℂ) * ζ ^ 4 + ((2901 / 4961) : ℂ) * ζ ^ 6 + ((10693 / 19844) : ℂ) * ζ ^ 8 - ((488 / 4961) : ℂ) * ζ ^ 10 - ((3309 / 19844) : ℂ) * ζ ^ 12 + ((20907 / 9922) : ℂ) * ζ ^ 14 + ((281 / 4961) : ℂ) * ζ ^ 16 + ((2015 / 4961) : ℂ) * ζ ^ 18 + ((1347 / 9922) : ℂ) * ζ ^ 20 + ((398 / 4961) : ℂ) * ζ ^ 22 - ((2185 / 19844) : ℂ) * ζ ^ 24 + ((3781 / 9922) : ℂ) * ζ ^ 26)) * Y 1 1
        + ((-((1251 / 19844) : ℂ) - ((5682 / 4961) : ℂ) * ζ ^ 2 + ((1251 / 19844) : ℂ) * ζ ^ 4 - ((2901 / 4961) : ℂ) * ζ ^ 6 - ((10693 / 19844) : ℂ) * ζ ^ 8 + ((488 / 4961) : ℂ) * ζ ^ 10 + ((3309 / 19844) : ℂ) * ζ ^ 12 - ((20907 / 9922) : ℂ) * ζ ^ 14 - ((281 / 4961) : ℂ) * ζ ^ 16 - ((2015 / 4961) : ℂ) * ζ ^ 18 - ((1347 / 9922) : ℂ) * ζ ^ 20 - ((398 / 4961) : ℂ) * ζ ^ 22 + ((2185 / 19844) : ℂ) * ζ ^ 24 - ((3781 / 9922) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((2279 / 19844) : ℂ) + ((939 / 4961) : ℂ) * ζ ^ 2 + ((2279 / 19844) : ℂ) * ζ ^ 4 - ((4809 / 4961) : ℂ) * ζ ^ 6 - ((4403 / 19844) : ℂ) * ζ ^ 8 + ((3158 / 4961) : ℂ) * ζ ^ 10 - ((1315 / 19844) : ℂ) * ζ ^ 12 - ((8535 / 9922) : ℂ) * ζ ^ 14 + ((1405 / 9922) : ℂ) * ζ ^ 16 - ((2646 / 4961) : ℂ) * ζ ^ 18 - ((827 / 4961) : ℂ) * ζ ^ 20 + ((995 / 4961) : ℂ) * ζ ^ 22 + ((1495 / 19844) : ℂ) * ζ ^ 24 - ((2587 / 9922) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY66_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((43 / 82) : ℂ) * ζ ^ 6 + ((31 / 82) : ℂ) * ζ ^ 8 + ((10 / 123) : ℂ) * ζ ^ 12 - ((32 / 123) : ℂ) * ζ ^ 18 + ((19 / 246) : ℂ) * ζ ^ 22 - ((13 / 246) : ℂ) * ζ ^ 24 - ((31 / 82) : ℂ) * ζ ^ 28 - ((15 / 82) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + (((1 : ℂ))) * Y 6 6
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((83 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY66_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation16
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((4 / 3) : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 18 + ((4 / 3) : ℂ) * ζ ^ 22 + (2 : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((15 / 41) : ℂ) - ((35 / 246) : ℂ) * ζ ^ 2 + ((67 / 123) : ℂ) * ζ ^ 4 + ((86 / 123) : ℂ) * ζ ^ 6 - ((17 / 82) : ℂ) * ζ ^ 8 - ((116 / 123) : ℂ) * ζ ^ 10 - ((11 / 82) : ℂ) * ζ ^ 12 + ((69 / 82) : ℂ) * ζ ^ 14 + ((77 / 246) : ℂ) * ζ ^ 16 - ((115 / 246) : ℂ) * ζ ^ 18 - ((28 / 123) : ℂ) * ζ ^ 20 + ((55 / 246) : ℂ) * ζ ^ 22 - ((2 / 123) : ℂ) * ζ ^ 24 - ((5 / 41) : ℂ) * ζ ^ 26 + ((2 / 123) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((83 / 123) : ℂ) + ((19 / 246) : ℂ) * ζ ^ 2 - ((191 / 123) : ℂ) * ζ ^ 4 - ((125 / 246) : ℂ) * ζ ^ 6 + ((155 / 123) : ℂ) * ζ ^ 8 + ((115 / 82) : ℂ) * ζ ^ 10 - ((1 / 123) : ℂ) * ζ ^ 12 - ((65 / 41) : ℂ) * ζ ^ 14 - ((107 / 123) : ℂ) * ζ ^ 16 + ((27 / 41) : ℂ) * ζ ^ 18 + ((57 / 41) : ℂ) * ζ ^ 20 + ((29 / 123) : ℂ) * ζ ^ 22 - ((20 / 123) : ℂ) * ζ ^ 24 + ((55 / 123) : ℂ) * ζ ^ 26 + ((20 / 123) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((83 / 123) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((191 / 123) : ℂ) * ζ ^ 4 + ((125 / 246) : ℂ) * ζ ^ 6 - ((155 / 123) : ℂ) * ζ ^ 8 - ((115 / 82) : ℂ) * ζ ^ 10 + ((1 / 123) : ℂ) * ζ ^ 12 + ((65 / 41) : ℂ) * ζ ^ 14 + ((107 / 123) : ℂ) * ζ ^ 16 - ((27 / 41) : ℂ) * ζ ^ 18 - ((57 / 41) : ℂ) * ζ ^ 20 - ((29 / 123) : ℂ) * ζ ^ 22 + ((20 / 123) : ℂ) * ζ ^ 24 - ((55 / 123) : ℂ) * ζ ^ 26 - ((20 / 123) : ℂ) * ζ ^ 28)) * Y 6 6
        + ((-((17 / 123) : ℂ) + ((169 / 246) : ℂ) * ζ ^ 2 + ((8 / 123) : ℂ) * ζ ^ 4 - ((57 / 82) : ℂ) * ζ ^ 6 + ((101 / 246) : ℂ) * ζ ^ 8 + ((203 / 246) : ℂ) * ζ ^ 10 - ((89 / 246) : ℂ) * ζ ^ 12 - ((45 / 82) : ℂ) * ζ ^ 14 + ((71 / 246) : ℂ) * ζ ^ 16 + ((58 / 123) : ℂ) * ζ ^ 18 - ((11 / 82) : ℂ) * ζ ^ 20 - ((14 / 41) : ℂ) * ζ ^ 22 + ((4 / 41) : ℂ) * ζ ^ 24 + ((8 / 123) : ℂ) * ζ ^ 26 - ((4 / 41) : ℂ) * ζ ^ 28)) * Y 7 6)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY66_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 6 6
      + ((-(1 : ℂ))) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY66_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((2 / 3) : ℂ) * ζ ^ 6 - ((4 / 3) : ℂ) * ζ ^ 8 + ((2 / 3) : ℂ) * ζ ^ 12 + ((2 / 3) : ℂ) * ζ ^ 18 - ((2 / 3) : ℂ) * ζ ^ 24 + ((4 / 3) : ℂ) * ζ ^ 28 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((15 / 41) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((15 / 41) : ℂ) * ζ ^ 4 + ((45 / 82) : ℂ) * ζ ^ 6 - ((59 / 246) : ℂ) * ζ ^ 8 - ((69 / 82) : ℂ) * ζ ^ 10 - ((19 / 246) : ℂ) * ζ ^ 12 + ((5 / 6) : ℂ) * ζ ^ 14 + ((65 / 246) : ℂ) * ζ ^ 16 - ((107 / 246) : ℂ) * ζ ^ 18 - ((29 / 82) : ℂ) * ζ ^ 20 + ((35 / 246) : ℂ) * ζ ^ 22 + ((10 / 41) : ℂ) * ζ ^ 24 - ((5 / 246) : ℂ) * ζ ^ 26 - ((7 / 123) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((-((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 + ((40 / 123) : ℂ) * ζ ^ 4 - ((85 / 246) : ℂ) * ζ ^ 6 - ((19 / 82) : ℂ) * ζ ^ 8 + ((103 / 246) : ℂ) * ζ ^ 10 + ((5 / 82) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ((47 / 246) : ℂ) * ζ ^ 16 + ((13 / 41) : ℂ) * ζ ^ 18 + ((73 / 246) : ℂ) * ζ ^ 20 - ((10 / 41) : ℂ) * ζ ^ 22 - ((28 / 123) : ℂ) * ζ ^ 24 + ((16 / 123) : ℂ) * ζ ^ 26 + ((4 / 41) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((4 / 41) : ℂ) * ζ ^ 4 - ((53 / 82) : ℂ) * ζ ^ 6 + ((68 / 123) : ℂ) * ζ ^ 8 + ((125 / 82) : ℂ) * ζ ^ 10 + ((49 / 123) : ℂ) * ζ ^ 12 - ((5 / 3) : ℂ) * ζ ^ 14 - ((53 / 41) : ℂ) * ζ ^ 16 + ((17 / 123) : ℂ) * ζ ^ 18 + ((151 / 123) : ℂ) * ζ ^ 20 + ((91 / 123) : ℂ) * ζ ^ 22 - ((30 / 41) : ℂ) * ζ ^ 24 - ((95 / 123) : ℂ) * ζ ^ 26 - ((20 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 - ((40 / 123) : ℂ) * ζ ^ 4 + ((85 / 246) : ℂ) * ζ ^ 6 + ((19 / 82) : ℂ) * ζ ^ 8 - ((103 / 246) : ℂ) * ζ ^ 10 - ((5 / 82) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((47 / 246) : ℂ) * ζ ^ 16 - ((13 / 41) : ℂ) * ζ ^ 18 - ((73 / 246) : ℂ) * ζ ^ 20 + ((10 / 41) : ℂ) * ζ ^ 22 + ((28 / 123) : ℂ) * ζ ^ 24 - ((16 / 123) : ℂ) * ζ ^ 26 - ((4 / 41) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY66
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 6 6 = Y 7 7 := by
  have reduced :=
    row17_reducedY66_combinationStep07 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row17_reducedY67_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((1381 / 246) : ℂ) + ((707 / 492) : ℂ) * ζ ^ 2 + ((983 / 492) : ℂ) * ζ ^ 6 - ((337 / 123) : ℂ) * ζ ^ 8 - ((427 / 492) : ℂ) * ζ ^ 12 + ((1555 / 492) : ℂ) * ζ ^ 18 - ((707 / 492) : ℂ) * ζ ^ 22 + ((2633 / 492) : ℂ) * ζ ^ 24 + ((337 / 123) : ℂ) * ζ ^ 28 + ((1627 / 492) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((25 / 246) : ℂ) + ((61 / 41) : ℂ) * ζ ^ 2 - ((65 / 492) : ℂ) * ζ ^ 6 + ((347 / 246) : ℂ) * ζ ^ 8 + ((43 / 492) : ℂ) * ζ ^ 12 - ((53 / 82) : ℂ) * ζ ^ 18 - ((61 / 41) : ℂ) * ζ ^ 22 - ((64 / 41) : ℂ) * ζ ^ 24 - ((347 / 246) : ℂ) * ζ ^ 28 - ((63 / 164) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((7 / 123) : ℂ) + ((413 / 41) : ℂ) * ζ ^ 2 + ((856 / 123) : ℂ) * ζ ^ 6 + ((473 / 41) : ℂ) * ζ ^ 8 + ((694 / 123) : ℂ) * ζ ^ 12 - ((169 / 41) : ℂ) * ζ ^ 18 - ((413 / 41) : ℂ) * ζ ^ 22 - ((775 / 123) : ℂ) * ζ ^ 24 - ((473 / 41) : ℂ) * ζ ^ 28 - ((65 / 123) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((923 / 164) : ℂ) + ((133 / 123) : ℂ) * ζ ^ 2 + ((923 / 164) : ℂ) * ζ ^ 4 - ((659 / 492) : ℂ) * ζ ^ 6 + ((19 / 492) : ℂ) * ζ ^ 8 - ((1529 / 246) : ℂ) * ζ ^ 10 - ((41 / 12) : ℂ) * ζ ^ 12 + ((875 / 123) : ℂ) * ζ ^ 14 - ((644 / 123) : ℂ) * ζ ^ 16 - ((97 / 12) : ℂ) * ζ ^ 18 + ((1117 / 164) : ℂ) * ζ ^ 20 + ((65 / 123) : ℂ) * ζ ^ 22 - ((1419 / 164) : ℂ) * ζ ^ 24 - ((65 / 164) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((25 / 246) : ℂ) - ((61 / 41) : ℂ) * ζ ^ 2 - ((25 / 246) : ℂ) * ζ ^ 4 + ((797 / 492) : ℂ) * ζ ^ 6 - ((161 / 123) : ℂ) * ζ ^ 8 - ((797 / 492) : ℂ) * ζ ^ 10 + ((161 / 123) : ℂ) * ζ ^ 12 + ((326 / 123) : ℂ) * ζ ^ 14 - ((161 / 123) : ℂ) * ζ ^ 16 - ((65 / 492) : ℂ) * ζ ^ 18 + ((473 / 164) : ℂ) * ζ ^ 20 + ((65 / 492) : ℂ) * ζ ^ 22)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY67_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((85 / 246) : ℂ) - ((179 / 164) : ℂ) * ζ ^ 2 - ((347 / 164) : ℂ) * ζ ^ 6 - ((185 / 123) : ℂ) * ζ ^ 8 - ((559 / 492) : ℂ) * ζ ^ 12 + ((239 / 492) : ℂ) * ζ ^ 18 + ((179 / 164) : ℂ) * ζ ^ 22 + ((7 / 164) : ℂ) * ζ ^ 24 + ((185 / 123) : ℂ) * ζ ^ 28 - ((85 / 492) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((-((171 / 164) : ℂ) - ((319 / 164) : ℂ) * ζ ^ 2 - ((383 / 123) : ℂ) * ζ ^ 6 - ((335 / 492) : ℂ) * ζ ^ 8 - ((227 / 82) : ℂ) * ζ ^ 12 - ((127 / 492) : ℂ) * ζ ^ 18 + ((319 / 164) : ℂ) * ζ ^ 22 - ((439 / 492) : ℂ) * ζ ^ 24 + ((335 / 492) : ℂ) * ζ ^ 28 - ((393 / 164) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((25 / 246) : ℂ) + ((61 / 41) : ℂ) * ζ ^ 2 - ((65 / 492) : ℂ) * ζ ^ 6 + ((347 / 246) : ℂ) * ζ ^ 8 + ((43 / 492) : ℂ) * ζ ^ 12 - ((53 / 82) : ℂ) * ζ ^ 18 - ((61 / 41) : ℂ) * ζ ^ 22 - ((64 / 41) : ℂ) * ζ ^ 24 - ((347 / 246) : ℂ) * ζ ^ 28 - ((63 / 164) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((85 / 246) : ℂ) + ((179 / 164) : ℂ) * ζ ^ 2 + ((347 / 164) : ℂ) * ζ ^ 6 + ((185 / 123) : ℂ) * ζ ^ 8 + ((559 / 492) : ℂ) * ζ ^ 12 - ((239 / 492) : ℂ) * ζ ^ 18 - ((179 / 164) : ℂ) * ζ ^ 22 - ((7 / 164) : ℂ) * ζ ^ 24 - ((185 / 123) : ℂ) * ζ ^ 28 + ((85 / 492) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY67_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((243 / 41) : ℂ) + ((691 / 123) : ℂ) * ζ ^ 2 + ((1493 / 123) : ℂ) * ζ ^ 6 + ((202 / 123) : ℂ) * ζ ^ 8 + ((740 / 123) : ℂ) * ζ ^ 12 - ((154 / 123) : ℂ) * ζ ^ 18 - ((691 / 123) : ℂ) * ζ ^ 22 + ((236 / 41) : ℂ) * ζ ^ 24 - ((202 / 123) : ℂ) * ζ ^ 28 + ((347 / 41) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((85 / 246) : ℂ) + ((179 / 164) : ℂ) * ζ ^ 2 - ((85 / 246) : ℂ) * ζ ^ 4 + ((42 / 41) : ℂ) * ζ ^ 6 + ((455 / 246) : ℂ) * ζ ^ 8 - ((42 / 41) : ℂ) * ζ ^ 10 - ((455 / 246) : ℂ) * ζ ^ 12 + ((175 / 246) : ℂ) * ζ ^ 14 + ((455 / 246) : ℂ) * ζ ^ 16 - ((347 / 164) : ℂ) * ζ ^ 18 - ((101 / 246) : ℂ) * ζ ^ 20 + ((347 / 164) : ℂ) * ζ ^ 22)) * Y 0 0
        + ((((1001 / 123) : ℂ) + ((785 / 164) : ℂ) * ζ ^ 2 - ((1001 / 123) : ℂ) * ζ ^ 4 + ((551 / 164) : ℂ) * ζ ^ 6 + ((503 / 246) : ℂ) * ζ ^ 8 - ((621 / 82) : ℂ) * ζ ^ 10 + ((986 / 123) : ℂ) * ζ ^ 12 + ((911 / 492) : ℂ) * ζ ^ 14 - ((2275 / 246) : ℂ) * ζ ^ 16 + ((261 / 41) : ℂ) * ζ ^ 18 + ((1567 / 246) : ℂ) * ζ ^ 20 - ((1735 / 164) : ℂ) * ζ ^ 22 - ((101 / 82) : ℂ) * ζ ^ 24 + ((1041 / 164) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((85 / 246) : ℂ) - ((179 / 164) : ℂ) * ζ ^ 2 + ((85 / 246) : ℂ) * ζ ^ 4 - ((42 / 41) : ℂ) * ζ ^ 6 - ((455 / 246) : ℂ) * ζ ^ 8 + ((42 / 41) : ℂ) * ζ ^ 10 + ((455 / 246) : ℂ) * ζ ^ 12 - ((175 / 246) : ℂ) * ζ ^ 14 - ((455 / 246) : ℂ) * ζ ^ 16 + ((347 / 164) : ℂ) * ζ ^ 18 + ((101 / 246) : ℂ) * ζ ^ 20 - ((347 / 164) : ℂ) * ζ ^ 22)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY67_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((17 / 123) : ℂ) + ((79 / 82) : ℂ) * ζ ^ 2 - ((6 / 41) : ℂ) * ζ ^ 6 + ((49 / 123) : ℂ) * ζ ^ 8 + ((85 / 246) : ℂ) * ζ ^ 12 - ((13 / 123) : ℂ) * ζ ^ 18 - ((79 / 82) : ℂ) * ζ ^ 22 - ((28 / 41) : ℂ) * ζ ^ 24 - ((49 / 123) : ℂ) * ζ ^ 28 + ((53 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((((39 / 41) : ℂ) - ((56 / 41) : ℂ) * ζ ^ 2 - ((73 / 246) : ℂ) * ζ ^ 6 - ((125 / 123) : ℂ) * ζ ^ 8 - ((113 / 82) : ℂ) * ζ ^ 12 + ((109 / 246) : ℂ) * ζ ^ 18 + ((56 / 41) : ℂ) * ζ ^ 22 + ((247 / 246) : ℂ) * ζ ^ 24 + ((125 / 123) : ℂ) * ζ ^ 28 - ((43 / 82) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((25 / 246) : ℂ) + ((61 / 41) : ℂ) * ζ ^ 2 - ((65 / 492) : ℂ) * ζ ^ 6 + ((347 / 246) : ℂ) * ζ ^ 8 + ((43 / 492) : ℂ) * ζ ^ 12 - ((53 / 82) : ℂ) * ζ ^ 18 - ((61 / 41) : ℂ) * ζ ^ 22 - ((64 / 41) : ℂ) * ζ ^ 24 - ((347 / 246) : ℂ) * ζ ^ 28 - ((63 / 164) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((85 / 246) : ℂ) + ((179 / 164) : ℂ) * ζ ^ 2 + ((347 / 164) : ℂ) * ζ ^ 6 + ((185 / 123) : ℂ) * ζ ^ 8 + ((559 / 492) : ℂ) * ζ ^ 12 - ((239 / 492) : ℂ) * ζ ^ 18 - ((179 / 164) : ℂ) * ζ ^ 22 - ((7 / 164) : ℂ) * ζ ^ 24 - ((185 / 123) : ℂ) * ζ ^ 28 + ((85 / 492) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((17 / 82) : ℂ) - ((337 / 164) : ℂ) * ζ ^ 2 - ((323 / 164) : ℂ) * ζ ^ 6 - ((78 / 41) : ℂ) * ζ ^ 8 - ((243 / 164) : ℂ) * ζ ^ 12 + ((97 / 164) : ℂ) * ζ ^ 18 + ((337 / 164) : ℂ) * ζ ^ 22 + ((119 / 164) : ℂ) * ζ ^ 24 + ((78 / 41) : ℂ) * ζ ^ 28 - ((99 / 164) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((479 / 451) : ℂ) - ((635 / 1804) : ℂ) * ζ ^ 2 - ((2171 / 1804) : ℂ) * ζ ^ 6 + ((100 / 451) : ℂ) * ζ ^ 8 - ((745 / 1804) : ℂ) * ζ ^ 12 - ((691 / 1804) : ℂ) * ζ ^ 18 + ((635 / 1804) : ℂ) * ζ ^ 22 - ((2109 / 1804) : ℂ) * ζ ^ 24 - ((100 / 451) : ℂ) * ζ ^ 28 - ((1983 / 1804) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY67_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((785 / 1353) : ℂ) - ((805 / 451) : ℂ) * ζ ^ 2 - ((1829 / 1353) : ℂ) * ζ ^ 6 - ((956 / 451) : ℂ) * ζ ^ 8 - ((1942 / 1353) : ℂ) * ζ ^ 12 + ((1360 / 1353) : ℂ) * ζ ^ 18 + ((805 / 451) : ℂ) * ζ ^ 22 + ((2480 / 1353) : ℂ) * ζ ^ 24 + ((956 / 451) : ℂ) * ζ ^ 28 + ((413 / 1353) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((5197 / 9922) : ℂ) - ((21457 / 19844) : ℂ) * ζ ^ 2 + ((5197 / 9922) : ℂ) * ζ ^ 4 - ((1497 / 9922) : ℂ) * ζ ^ 6 - ((5908 / 4961) : ℂ) * ζ ^ 8 - ((459 / 4961) : ℂ) * ζ ^ 10 - ((1531 / 4961) : ℂ) * ζ ^ 12 - ((3187 / 9922) : ℂ) * ζ ^ 14 + ((97 / 4961) : ℂ) * ζ ^ 16 - ((4417 / 19844) : ℂ) * ζ ^ 18 - ((1957 / 4961) : ℂ) * ζ ^ 20 - ((413 / 19844) : ℂ) * ζ ^ 22 - ((1434 / 4961) : ℂ) * ζ ^ 24 - ((413 / 9922) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((14013 / 4961) : ℂ) + ((9805 / 4961) : ℂ) * ζ ^ 2 + ((14013 / 4961) : ℂ) * ζ ^ 4 - ((56713 / 19844) : ℂ) * ζ ^ 6 + ((12873 / 9922) : ℂ) * ζ ^ 8 + ((2707 / 4961) : ℂ) * ζ ^ 10 - ((14011 / 4961) : ℂ) * ζ ^ 12 - ((44999 / 19844) : ℂ) * ζ ^ 14 + ((388 / 4961) : ℂ) * ζ ^ 16 - ((44233 / 19844) : ℂ) * ζ ^ 18 - ((14648 / 4961) : ℂ) * ζ ^ 20 - ((413 / 4961) : ℂ) * ζ ^ 22 - ((13623 / 4961) : ℂ) * ζ ^ 24 - ((7847 / 19844) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((5197 / 9922) : ℂ) + ((21457 / 19844) : ℂ) * ζ ^ 2 - ((5197 / 9922) : ℂ) * ζ ^ 4 + ((1497 / 9922) : ℂ) * ζ ^ 6 + ((5908 / 4961) : ℂ) * ζ ^ 8 + ((459 / 4961) : ℂ) * ζ ^ 10 + ((1531 / 4961) : ℂ) * ζ ^ 12 + ((3187 / 9922) : ℂ) * ζ ^ 14 - ((97 / 4961) : ℂ) * ζ ^ 16 + ((4417 / 19844) : ℂ) * ζ ^ 18 + ((1957 / 4961) : ℂ) * ζ ^ 20 + ((413 / 19844) : ℂ) * ζ ^ 22 + ((1434 / 4961) : ℂ) * ζ ^ 24 + ((413 / 9922) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((11323 / 9922) : ℂ) + ((2155 / 19844) : ℂ) * ζ ^ 2 - ((11323 / 9922) : ℂ) * ζ ^ 4 + ((4517 / 4961) : ℂ) * ζ ^ 6 + ((1950 / 4961) : ℂ) * ζ ^ 8 - ((1789 / 9922) : ℂ) * ζ ^ 10 + ((4593 / 4961) : ℂ) * ζ ^ 12 + ((9561 / 9922) : ℂ) * ζ ^ 14 - ((291 / 4961) : ℂ) * ζ ^ 16 + ((13251 / 19844) : ℂ) * ζ ^ 18 + ((5871 / 4961) : ℂ) * ζ ^ 20 + ((1239 / 19844) : ℂ) * ζ ^ 22 + ((4302 / 4961) : ℂ) * ζ ^ 24 + ((1239 / 9922) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY67_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((25 / 246) : ℂ) + ((61 / 41) : ℂ) * ζ ^ 2 - ((65 / 492) : ℂ) * ζ ^ 6 + ((347 / 246) : ℂ) * ζ ^ 8 + ((43 / 492) : ℂ) * ζ ^ 12 - ((53 / 82) : ℂ) * ζ ^ 18 - ((61 / 41) : ℂ) * ζ ^ 22 - ((64 / 41) : ℂ) * ζ ^ 24 - ((347 / 246) : ℂ) * ζ ^ 28 - ((63 / 164) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((85 / 246) : ℂ) + ((179 / 164) : ℂ) * ζ ^ 2 + ((347 / 164) : ℂ) * ζ ^ 6 + ((185 / 123) : ℂ) * ζ ^ 8 + ((559 / 492) : ℂ) * ζ ^ 12 - ((239 / 492) : ℂ) * ζ ^ 18 - ((179 / 164) : ℂ) * ζ ^ 22 - ((7 / 164) : ℂ) * ζ ^ 24 - ((185 / 123) : ℂ) * ζ ^ 28 + ((85 / 492) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((17 / 82) : ℂ) - ((337 / 164) : ℂ) * ζ ^ 2 - ((323 / 164) : ℂ) * ζ ^ 6 - ((78 / 41) : ℂ) * ζ ^ 8 - ((243 / 164) : ℂ) * ζ ^ 12 + ((97 / 164) : ℂ) * ζ ^ 18 + ((337 / 164) : ℂ) * ζ ^ 22 + ((119 / 164) : ℂ) * ζ ^ 24 + ((78 / 41) : ℂ) * ζ ^ 28 - ((99 / 164) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((-((479 / 451) : ℂ) - ((635 / 1804) : ℂ) * ζ ^ 2 - ((2171 / 1804) : ℂ) * ζ ^ 6 + ((100 / 451) : ℂ) * ζ ^ 8 - ((745 / 1804) : ℂ) * ζ ^ 12 - ((691 / 1804) : ℂ) * ζ ^ 18 + ((635 / 1804) : ℂ) * ζ ^ 22 - ((2109 / 1804) : ℂ) * ζ ^ 24 - ((100 / 451) : ℂ) * ζ ^ 28 - ((1983 / 1804) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((17 / 123) : ℂ) + ((79 / 82) : ℂ) * ζ ^ 2 - ((6 / 41) : ℂ) * ζ ^ 6 + ((49 / 123) : ℂ) * ζ ^ 8 + ((85 / 246) : ℂ) * ζ ^ 12 - ((13 / 123) : ℂ) * ζ ^ 18 - ((79 / 82) : ℂ) * ζ ^ 22 - ((28 / 41) : ℂ) * ζ ^ 24 - ((49 / 123) : ℂ) * ζ ^ 28 + ((53 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY67_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation07
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((2 / 3) : ℂ) - (2 : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 8 - ((8 / 3) : ℂ) * ζ ^ 12 + ((4 / 3) : ℂ) * ζ ^ 18 + (2 : ℂ) * ζ ^ 22 + ((10 / 3) : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 28)) * equation
      - (
        ((-((7 / 82) : ℂ) + ((39 / 41) : ℂ) * ζ ^ 2 - ((29 / 82) : ℂ) * ζ ^ 4 - ((131 / 123) : ℂ) * ζ ^ 6 + ((25 / 123) : ℂ) * ζ ^ 8 + ((295 / 246) : ℂ) * ζ ^ 10 - ((71 / 246) : ℂ) * ζ ^ 12 - ((167 / 246) : ℂ) * ζ ^ 14 - ((7 / 123) : ℂ) * ζ ^ 16 + ((89 / 246) : ℂ) * ζ ^ 18 + ((11 / 41) : ℂ) * ζ ^ 20 - ((28 / 123) : ℂ) * ζ ^ 22 + ((23 / 246) : ℂ) * ζ ^ 24 - ((7 / 123) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((((100 / 123) : ℂ) - ((81 / 82) : ℂ) * ζ ^ 2 - ((173 / 246) : ℂ) * ζ ^ 4 + ((209 / 246) : ℂ) * ζ ^ 6 - ((11 / 82) : ℂ) * ζ ^ 8 - ((124 / 123) : ℂ) * ζ ^ 10 - ((13 / 246) : ℂ) * ζ ^ 12 + ((67 / 123) : ℂ) * ζ ^ 14 + ((4 / 41) : ℂ) * ζ ^ 16 - ((45 / 82) : ℂ) * ζ ^ 18 + ((2 / 123) : ℂ) * ζ ^ 20 + ((16 / 41) : ℂ) * ζ ^ 22 - ((8 / 123) : ℂ) * ζ ^ 24 + ((4 / 41) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((44 / 123) : ℂ) + ((61 / 246) : ℂ) * ζ ^ 2 + ((11 / 123) : ℂ) * ζ ^ 4 - ((151 / 246) : ℂ) * ζ ^ 6 - ((23 / 41) : ℂ) * ζ ^ 8 + ((73 / 82) : ℂ) * ζ ^ 10 + ((22 / 41) : ℂ) * ζ ^ 12 - ((53 / 82) : ℂ) * ζ ^ 14 - ((28 / 41) : ℂ) * ζ ^ 16 + ((14 / 41) : ℂ) * ζ ^ 18 + ((95 / 246) : ℂ) * ζ ^ 20 - ((8 / 123) : ℂ) * ζ ^ 22 + ((5 / 41) : ℂ) * ζ ^ 24 - ((2 / 123) : ℂ) * ζ ^ 26)) * Y 6 7
        + ((((7 / 82) : ℂ) - ((39 / 41) : ℂ) * ζ ^ 2 + ((29 / 82) : ℂ) * ζ ^ 4 + ((131 / 123) : ℂ) * ζ ^ 6 - ((25 / 123) : ℂ) * ζ ^ 8 - ((295 / 246) : ℂ) * ζ ^ 10 + ((71 / 246) : ℂ) * ζ ^ 12 + ((167 / 246) : ℂ) * ζ ^ 14 + ((7 / 123) : ℂ) * ζ ^ 16 - ((89 / 246) : ℂ) * ζ ^ 18 - ((11 / 41) : ℂ) * ζ ^ 20 + ((28 / 123) : ℂ) * ζ ^ 22 - ((23 / 246) : ℂ) * ζ ^ 24 + ((7 / 123) : ℂ) * ζ ^ 26)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY67_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((55 / 123) : ℂ) + ((29 / 82) : ℂ) * ζ ^ 2 - ((103 / 246) : ℂ) * ζ ^ 6 + ((23 / 246) : ℂ) * ζ ^ 8 - ((35 / 123) : ℂ) * ζ ^ 12 + ((10 / 41) : ℂ) * ζ ^ 18 - ((29 / 82) : ℂ) * ζ ^ 22 - ((19 / 82) : ℂ) * ζ ^ 24 - ((23 / 246) : ℂ) * ζ ^ 28 - ((9 / 82) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((17 / 123) : ℂ) - ((79 / 82) : ℂ) * ζ ^ 2 + ((6 / 41) : ℂ) * ζ ^ 6 - ((49 / 123) : ℂ) * ζ ^ 8 - ((85 / 246) : ℂ) * ζ ^ 12 + ((13 / 123) : ℂ) * ζ ^ 18 + ((79 / 82) : ℂ) * ζ ^ 22 + ((28 / 41) : ℂ) * ζ ^ 24 + ((49 / 123) : ℂ) * ζ ^ 28 - ((53 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((40 / 123) : ℂ) - ((5 / 82) : ℂ) * ζ ^ 2 + ((52 / 123) : ℂ) * ζ ^ 6 + ((9 / 41) : ℂ) * ζ ^ 8 - ((77 / 246) : ℂ) * ζ ^ 12 - ((8 / 123) : ℂ) * ζ ^ 18 + ((5 / 82) : ℂ) * ζ ^ 22 + ((8 / 41) : ℂ) * ζ ^ 24 - ((9 / 41) : ℂ) * ζ ^ 28 - ((62 / 123) : ℂ) * ζ ^ 30)) * Y 6 7
      + ((-((17 / 123) : ℂ) + ((79 / 82) : ℂ) * ζ ^ 2 - ((6 / 41) : ℂ) * ζ ^ 6 + ((49 / 123) : ℂ) * ζ ^ 8 + ((85 / 246) : ℂ) * ζ ^ 12 - ((13 / 123) : ℂ) * ζ ^ 18 - ((79 / 82) : ℂ) * ζ ^ 22 - ((28 / 41) : ℂ) * ζ ^ 24 - ((49 / 123) : ℂ) * ζ ^ 28 + ((53 / 123) : ℂ) * ζ ^ 30)) * Y 7 7) = 0 := by
  have previous :=
    row17_reducedY67_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((1231 / 1353) : ℂ) + ((587 / 1353) : ℂ) * ζ ^ 2 - ((256 / 451) : ℂ) * ζ ^ 6 + ((1175 / 1353) : ℂ) * ζ ^ 8 - ((6 / 451) : ℂ) * ζ ^ 12 - ((235 / 451) : ℂ) * ζ ^ 18 - ((587 / 1353) : ℂ) * ζ ^ 22 - ((1657 / 1353) : ℂ) * ζ ^ 24 - ((1175 / 1353) : ℂ) * ζ ^ 28 - ((335 / 451) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((521 / 9922) : ℂ) + ((8905 / 9922) : ℂ) * ζ ^ 2 + ((521 / 9922) : ℂ) * ζ ^ 4 - ((5979 / 19844) : ℂ) * ζ ^ 6 + ((3308 / 4961) : ℂ) * ζ ^ 8 + ((7153 / 19844) : ℂ) * ζ ^ 10 + ((467 / 4961) : ℂ) * ζ ^ 12 + ((1253 / 4961) : ℂ) * ζ ^ 14 + ((241 / 9922) : ℂ) * ζ ^ 16 + ((169 / 19844) : ℂ) * ζ ^ 18 + ((4489 / 19844) : ℂ) * ζ ^ 20 + ((1005 / 19844) : ℂ) * ζ ^ 22 + ((1175 / 9922) : ℂ) * ζ ^ 24 + ((1005 / 9922) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((((29965 / 19844) : ℂ) + ((14225 / 9922) : ℂ) * ζ ^ 2 - ((29965 / 19844) : ℂ) * ζ ^ 4 + ((26761 / 19844) : ℂ) * ζ ^ 6 + ((19653 / 19844) : ℂ) * ζ ^ 8 - ((3902 / 4961) : ℂ) * ζ ^ 10 + ((20397 / 19844) : ℂ) * ζ ^ 12 + ((19429 / 9922) : ℂ) * ζ ^ 14 + ((482 / 4961) : ℂ) * ζ ^ 16 + ((7133 / 19844) : ℂ) * ζ ^ 18 + ((36183 / 19844) : ℂ) * ζ ^ 20 + ((1005 / 4961) : ℂ) * ζ ^ 22 + ((22325 / 19844) : ℂ) * ζ ^ 24 + ((19095 / 19844) : ℂ) * ζ ^ 26)) * Y 1 1
        + ((-((29965 / 19844) : ℂ) - ((14225 / 9922) : ℂ) * ζ ^ 2 + ((29965 / 19844) : ℂ) * ζ ^ 4 - ((26761 / 19844) : ℂ) * ζ ^ 6 - ((19653 / 19844) : ℂ) * ζ ^ 8 + ((3902 / 4961) : ℂ) * ζ ^ 10 - ((20397 / 19844) : ℂ) * ζ ^ 12 - ((19429 / 9922) : ℂ) * ζ ^ 14 - ((482 / 4961) : ℂ) * ζ ^ 16 - ((7133 / 19844) : ℂ) * ζ ^ 18 - ((36183 / 19844) : ℂ) * ζ ^ 20 - ((1005 / 4961) : ℂ) * ζ ^ 22 - ((22325 / 19844) : ℂ) * ζ ^ 24 - ((19095 / 19844) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((17383 / 19844) : ℂ) - ((4373 / 9922) : ℂ) * ζ ^ 2 + ((17383 / 19844) : ℂ) * ζ ^ 4 - ((12831 / 19844) : ℂ) * ζ ^ 6 - ((505 / 19844) : ℂ) * ζ ^ 8 + ((1300 / 4961) : ℂ) * ζ ^ 10 - ((20095 / 19844) : ℂ) * ζ ^ 12 - ((3155 / 9922) : ℂ) * ζ ^ 14 + ((1205 / 4961) : ℂ) * ζ ^ 16 - ((17681 / 19844) : ℂ) * ζ ^ 18 - ((9791 / 19844) : ℂ) * ζ ^ 20 + ((5025 / 9922) : ℂ) * ζ ^ 22 - ((15275 / 19844) : ℂ) * ζ ^ 24 - ((13065 / 19844) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY67_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 6 7) = 0 := by
  have previous :=
    row17_reducedY67_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation17
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((4 / 3) : ℂ) * ζ ^ 2 + ((2 / 3) : ℂ) * ζ ^ 6 - ((2 / 3) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 18 + ((4 / 3) : ℂ) * ζ ^ 22 + (2 : ℂ) * ζ ^ 24 + ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((55 / 123) : ℂ) + ((61 / 246) : ℂ) * ζ ^ 2 - ((91 / 123) : ℂ) * ζ ^ 4 - ((151 / 246) : ℂ) * ζ ^ 6 + ((199 / 246) : ℂ) * ζ ^ 8 + ((197 / 246) : ℂ) * ζ ^ 10 - ((151 / 246) : ℂ) * ζ ^ 12 - ((57 / 82) : ℂ) * ζ ^ 14 + ((79 / 246) : ℂ) * ζ ^ 16 + ((95 / 246) : ℂ) * ζ ^ 18 - ((3 / 82) : ℂ) * ζ ^ 20 - ((49 / 246) : ℂ) * ζ ^ 22 + ((7 / 123) : ℂ) * ζ ^ 24 + ((23 / 246) : ℂ) * ζ ^ 26 - ((7 / 123) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((17 / 123) : ℂ) - ((169 / 246) : ℂ) * ζ ^ 2 - ((8 / 123) : ℂ) * ζ ^ 4 + ((57 / 82) : ℂ) * ζ ^ 6 - ((101 / 246) : ℂ) * ζ ^ 8 - ((203 / 246) : ℂ) * ζ ^ 10 + ((89 / 246) : ℂ) * ζ ^ 12 + ((45 / 82) : ℂ) * ζ ^ 14 - ((71 / 246) : ℂ) * ζ ^ 16 - ((58 / 123) : ℂ) * ζ ^ 18 + ((11 / 82) : ℂ) * ζ ^ 20 + ((14 / 41) : ℂ) * ζ ^ 22 - ((4 / 41) : ℂ) * ζ ^ 24 - ((8 / 123) : ℂ) * ζ ^ 26 + ((4 / 41) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((83 / 123) : ℂ) - ((19 / 246) : ℂ) * ζ ^ 2 + ((191 / 123) : ℂ) * ζ ^ 4 + ((125 / 246) : ℂ) * ζ ^ 6 - ((155 / 123) : ℂ) * ζ ^ 8 - ((115 / 82) : ℂ) * ζ ^ 10 + ((1 / 123) : ℂ) * ζ ^ 12 + ((65 / 41) : ℂ) * ζ ^ 14 + ((107 / 123) : ℂ) * ζ ^ 16 - ((27 / 41) : ℂ) * ζ ^ 18 - ((57 / 41) : ℂ) * ζ ^ 20 - ((29 / 123) : ℂ) * ζ ^ 22 + ((20 / 123) : ℂ) * ζ ^ 24 - ((55 / 123) : ℂ) * ζ ^ 26 - ((20 / 123) : ℂ) * ζ ^ 28)) * Y 6 7
        + ((-((17 / 123) : ℂ) + ((169 / 246) : ℂ) * ζ ^ 2 + ((8 / 123) : ℂ) * ζ ^ 4 - ((57 / 82) : ℂ) * ζ ^ 6 + ((101 / 246) : ℂ) * ζ ^ 8 + ((203 / 246) : ℂ) * ζ ^ 10 - ((89 / 246) : ℂ) * ζ ^ 12 - ((45 / 82) : ℂ) * ζ ^ 14 + ((71 / 246) : ℂ) * ζ ^ 16 + ((58 / 123) : ℂ) * ζ ^ 18 - ((11 / 82) : ℂ) * ζ ^ 20 - ((14 / 41) : ℂ) * ζ ^ 22 + ((4 / 41) : ℂ) * ζ ^ 24 + ((8 / 123) : ℂ) * ζ ^ 26 - ((4 / 41) : ℂ) * ζ ^ 28)) * Y 7 7)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY67
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 6 7 = 0 := by
  have reduced :=
    row17_reducedY67_combinationStep05 Y commutesA commutesDiagonal
  linear_combination reduced

private theorem row17_reducedY76_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((301 / 246) : ℂ) - ((2137 / 492) : ℂ) * ζ ^ 2 - ((128 / 123) : ℂ) * ζ ^ 6 + ((517 / 123) : ℂ) * ζ ^ 8 - ((47 / 246) : ℂ) * ζ ^ 12 + ((313 / 123) : ℂ) * ζ ^ 18 + ((2137 / 492) : ℂ) * ζ ^ 22 - ((391 / 164) : ℂ) * ζ ^ 24 - ((517 / 123) : ℂ) * ζ ^ 28 - ((188 / 123) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((4 / 123) : ℂ) + ((83 / 164) : ℂ) * ζ ^ 2 + ((545 / 492) : ℂ) * ζ ^ 6 - ((143 / 164) : ℂ) * ζ ^ 8 - ((575 / 492) : ℂ) * ζ ^ 12 - ((23 / 246) : ℂ) * ζ ^ 18 - ((83 / 164) : ℂ) * ζ ^ 22 + ((425 / 492) : ℂ) * ζ ^ 24 + ((143 / 164) : ℂ) * ζ ^ 28 - ((49 / 492) : ℂ) * ζ ^ 30)) * Y 1 0) = 0 := by
  have equation :=
    row17_commutatorEquation00
      Y commutesA commutesDiagonal
  linear_combination
    ((-((197 / 41) : ℂ) + ((344 / 123) : ℂ) * ζ ^ 2 + ((281 / 41) : ℂ) * ζ ^ 6 - ((93 / 41) : ℂ) * ζ ^ 8 - ((143 / 41) : ℂ) * ζ ^ 12 - ((95 / 123) : ℂ) * ζ ^ 18 - ((344 / 123) : ℂ) * ζ ^ 22 - ((166 / 123) : ℂ) * ζ ^ 24 + ((93 / 41) : ℂ) * ζ ^ 28 + ((545 / 123) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((11 / 492) : ℂ) + ((827 / 164) : ℂ) * ζ ^ 2 - ((11 / 492) : ℂ) * ζ ^ 4 - ((563 / 246) : ℂ) * ζ ^ 6 - ((563 / 492) : ℂ) * ζ ^ 8 + ((47 / 246) : ℂ) * ζ ^ 10 - ((23 / 12) : ℂ) * ζ ^ 12 + ((91 / 82) : ℂ) * ζ ^ 14 + ((445 / 123) : ℂ) * ζ ^ 16 + ((7 / 3) : ℂ) * ζ ^ 18 - ((269 / 82) : ℂ) * ζ ^ 20 - ((545 / 123) : ℂ) * ζ ^ 22 + ((279 / 164) : ℂ) * ζ ^ 24 + ((545 / 164) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((4 / 123) : ℂ) - ((83 / 164) : ℂ) * ζ ^ 2 - ((4 / 123) : ℂ) * ζ ^ 4 - ((74 / 123) : ℂ) * ζ ^ 6 + ((445 / 492) : ℂ) * ζ ^ 8 + ((74 / 123) : ℂ) * ζ ^ 10 - ((445 / 492) : ℂ) * ζ ^ 12 - ((67 / 164) : ℂ) * ζ ^ 14 + ((445 / 492) : ℂ) * ζ ^ 16 + ((545 / 492) : ℂ) * ζ ^ 18 - ((93 / 164) : ℂ) * ζ ^ 20 - ((545 / 492) : ℂ) * ζ ^ 22)) * Y 1 0)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY76_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((((103 / 82) : ℂ) - ((95 / 164) : ℂ) * ζ ^ 2 - ((121 / 123) : ℂ) * ζ ^ 6 - ((10 / 123) : ℂ) * ζ ^ 8 - ((55 / 246) : ℂ) * ζ ^ 12 + ((47 / 123) : ℂ) * ζ ^ 18 + ((95 / 164) : ℂ) * ζ ^ 22 + ((181 / 164) : ℂ) * ζ ^ 24 + ((10 / 123) : ℂ) * ζ ^ 28 - ((179 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((((229 / 164) : ℂ) + ((53 / 123) : ℂ) * ζ ^ 2 - ((505 / 492) : ℂ) * ζ ^ 6 - ((427 / 492) : ℂ) * ζ ^ 8 + ((271 / 492) : ℂ) * ζ ^ 12 - ((259 / 164) : ℂ) * ζ ^ 18 - ((53 / 123) : ℂ) * ζ ^ 22 + ((571 / 246) : ℂ) * ζ ^ 24 + ((427 / 492) : ℂ) * ζ ^ 28 - ((193 / 164) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((4 / 123) : ℂ) + ((83 / 164) : ℂ) * ζ ^ 2 + ((545 / 492) : ℂ) * ζ ^ 6 - ((143 / 164) : ℂ) * ζ ^ 8 - ((575 / 492) : ℂ) * ζ ^ 12 - ((23 / 246) : ℂ) * ζ ^ 18 - ((83 / 164) : ℂ) * ζ ^ 22 + ((425 / 492) : ℂ) * ζ ^ 24 + ((143 / 164) : ℂ) * ζ ^ 28 - ((49 / 492) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((103 / 82) : ℂ) + ((95 / 164) : ℂ) * ζ ^ 2 + ((121 / 123) : ℂ) * ζ ^ 6 + ((10 / 123) : ℂ) * ζ ^ 8 + ((55 / 246) : ℂ) * ζ ^ 12 - ((47 / 123) : ℂ) * ζ ^ 18 - ((95 / 164) : ℂ) * ζ ^ 22 - ((181 / 164) : ℂ) * ζ ^ 24 - ((10 / 123) : ℂ) * ζ ^ 28 + ((179 / 123) : ℂ) * ζ ^ 30)) * Y 1 1) = 0 := by
  have previous :=
    row17_reducedY76_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation01
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((-((508 / 123) : ℂ) - ((81 / 41) : ℂ) * ζ ^ 2 + ((53 / 123) : ℂ) * ζ ^ 6 + ((473 / 123) : ℂ) * ζ ^ 8 + ((40 / 123) : ℂ) * ζ ^ 12 + ((176 / 41) : ℂ) * ζ ^ 18 + ((81 / 41) : ℂ) * ζ ^ 22 - ((1051 / 123) : ℂ) * ζ ^ 24 - ((473 / 123) : ℂ) * ζ ^ 28 + ((484 / 123) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((103 / 82) : ℂ) + ((95 / 164) : ℂ) * ζ ^ 2 + ((103 / 82) : ℂ) * ζ ^ 4 + ((199 / 492) : ℂ) * ζ ^ 6 - ((289 / 246) : ℂ) * ζ ^ 8 - ((199 / 492) : ℂ) * ζ ^ 10 + ((289 / 246) : ℂ) * ζ ^ 12 + ((727 / 492) : ℂ) * ζ ^ 14 - ((289 / 246) : ℂ) * ζ ^ 16 - ((121 / 123) : ℂ) * ζ ^ 18 - ((473 / 492) : ℂ) * ζ ^ 20 + ((121 / 123) : ℂ) * ζ ^ 22)) * Y 0 0
        + ((-((599 / 164) : ℂ) - ((216 / 41) : ℂ) * ζ ^ 2 + ((599 / 164) : ℂ) * ζ ^ 4 + ((1319 / 246) : ℂ) * ζ ^ 6 + ((2695 / 492) : ℂ) * ζ ^ 8 - ((1909 / 492) : ℂ) * ζ ^ 10 - ((4309 / 492) : ℂ) * ζ ^ 12 - ((599 / 492) : ℂ) * ζ ^ 14 + ((1445 / 246) : ℂ) * ζ ^ 16 + ((3149 / 492) : ℂ) * ζ ^ 18 - ((197 / 123) : ℂ) * ζ ^ 20 - ((605 / 123) : ℂ) * ζ ^ 22 - ((473 / 164) : ℂ) * ζ ^ 24 + ((121 / 41) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((((103 / 82) : ℂ) - ((95 / 164) : ℂ) * ζ ^ 2 - ((103 / 82) : ℂ) * ζ ^ 4 - ((199 / 492) : ℂ) * ζ ^ 6 + ((289 / 246) : ℂ) * ζ ^ 8 + ((199 / 492) : ℂ) * ζ ^ 10 - ((289 / 246) : ℂ) * ζ ^ 12 - ((727 / 492) : ℂ) * ζ ^ 14 + ((289 / 246) : ℂ) * ζ ^ 16 + ((121 / 123) : ℂ) * ζ ^ 18 + ((473 / 492) : ℂ) * ζ ^ 20 - ((121 / 123) : ℂ) * ζ ^ 22)) * Y 1 1)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY76_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((4 / 41) : ℂ) - ((19 / 82) : ℂ) * ζ ^ 2 + ((50 / 123) : ℂ) * ζ ^ 6 - ((4 / 123) : ℂ) * ζ ^ 8 - ((145 / 246) : ℂ) * ζ ^ 12 + ((68 / 123) : ℂ) * ζ ^ 18 + ((19 / 82) : ℂ) * ζ ^ 22 + ((14 / 41) : ℂ) * ζ ^ 24 + ((4 / 123) : ℂ) * ζ ^ 28 - ((47 / 123) : ℂ) * ζ ^ 30)) * Y 0 0
      + ((((1 / 41) : ℂ) - ((121 / 123) : ℂ) * ζ ^ 2 - ((353 / 246) : ℂ) * ζ ^ 6 + ((83 / 123) : ℂ) * ζ ^ 8 + ((395 / 246) : ℂ) * ζ ^ 12 - ((25 / 82) : ℂ) * ζ ^ 18 + ((121 / 123) : ℂ) * ζ ^ 22 - ((185 / 246) : ℂ) * ζ ^ 24 - ((83 / 123) : ℂ) * ζ ^ 28 + ((1 / 82) : ℂ) * ζ ^ 30)) * Y 0 1
      + ((-((4 / 123) : ℂ) + ((83 / 164) : ℂ) * ζ ^ 2 + ((545 / 492) : ℂ) * ζ ^ 6 - ((143 / 164) : ℂ) * ζ ^ 8 - ((575 / 492) : ℂ) * ζ ^ 12 - ((23 / 246) : ℂ) * ζ ^ 18 - ((83 / 164) : ℂ) * ζ ^ 22 + ((425 / 492) : ℂ) * ζ ^ 24 + ((143 / 164) : ℂ) * ζ ^ 28 - ((49 / 492) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((103 / 82) : ℂ) + ((95 / 164) : ℂ) * ζ ^ 2 + ((121 / 123) : ℂ) * ζ ^ 6 + ((10 / 123) : ℂ) * ζ ^ 8 + ((55 / 246) : ℂ) * ζ ^ 12 - ((47 / 123) : ℂ) * ζ ^ 18 - ((95 / 164) : ℂ) * ζ ^ 22 - ((181 / 164) : ℂ) * ζ ^ 24 - ((10 / 123) : ℂ) * ζ ^ 28 + ((179 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((111 / 82) : ℂ) - ((57 / 164) : ℂ) * ζ ^ 2 - ((57 / 41) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 + ((15 / 41) : ℂ) * ζ ^ 12 - ((7 / 41) : ℂ) * ζ ^ 18 + ((57 / 164) : ℂ) * ζ ^ 22 + ((125 / 164) : ℂ) * ζ ^ 24 + ((2 / 41) : ℂ) * ζ ^ 28 - ((44 / 41) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((397 / 902) : ℂ) + ((1691 / 1804) : ℂ) * ζ ^ 2 + ((133 / 451) : ℂ) * ζ ^ 6 - ((419 / 451) : ℂ) * ζ ^ 8 - ((29 / 902) : ℂ) * ζ ^ 12 - ((380 / 451) : ℂ) * ζ ^ 18 - ((1691 / 1804) : ℂ) * ζ ^ 22 + ((1977 / 1804) : ℂ) * ζ ^ 24 + ((419 / 451) : ℂ) * ζ ^ 28 - ((191 / 902) : ℂ) * ζ ^ 30)) * Y 5 4) = 0 := by
  have previous :=
    row17_reducedY76_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation04
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((1514 / 1353) : ℂ) - ((1765 / 1353) : ℂ) * ζ ^ 2 - ((2263 / 1353) : ℂ) * ζ ^ 6 + ((1229 / 1353) : ℂ) * ζ ^ 8 + ((28 / 1353) : ℂ) * ζ ^ 12 + ((796 / 1353) : ℂ) * ζ ^ 18 + ((1765 / 1353) : ℂ) * ζ ^ 22 + ((523 / 1353) : ℂ) * ζ ^ 24 - ((1229 / 1353) : ℂ) * ζ ^ 28 - ((1744 / 1353) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((7375 / 9922) : ℂ) + ((7223 / 19844) : ℂ) * ζ ^ 2 - ((7375 / 9922) : ℂ) * ζ ^ 4 - ((16707 / 19844) : ℂ) * ζ ^ 6 + ((3489 / 9922) : ℂ) * ζ ^ 8 + ((13177 / 19844) : ℂ) * ζ ^ 10 + ((2105 / 9922) : ℂ) * ζ ^ 12 + ((1875 / 19844) : ℂ) * ζ ^ 14 - ((438 / 4961) : ℂ) * ζ ^ 16 - ((2637 / 9922) : ℂ) * ζ ^ 18 + ((183 / 19844) : ℂ) * ζ ^ 20 + ((436 / 4961) : ℂ) * ζ ^ 22 + ((1229 / 9922) : ℂ) * ζ ^ 24 + ((872 / 4961) : ℂ) * ζ ^ 26)) * Y 0 0
        + ((-((4569 / 19844) : ℂ) + ((65137 / 19844) : ℂ) * ζ ^ 2 + ((4569 / 19844) : ℂ) * ζ ^ 4 - ((9507 / 19844) : ℂ) * ζ ^ 6 - ((32225 / 19844) : ℂ) * ζ ^ 8 - ((6007 / 4961) : ℂ) * ζ ^ 10 + ((30359 / 19844) : ℂ) * ζ ^ 12 + ((4482 / 4961) : ℂ) * ζ ^ 14 - ((1752 / 4961) : ℂ) * ζ ^ 16 - ((40511 / 19844) : ℂ) * ζ ^ 18 - ((5021 / 19844) : ℂ) * ζ ^ 20 + ((1744 / 4961) : ℂ) * ζ ^ 22 + ((23351 / 19844) : ℂ) * ζ ^ 24 + ((8284 / 4961) : ℂ) * ζ ^ 26)) * Y 0 1
        + ((-((7375 / 9922) : ℂ) - ((7223 / 19844) : ℂ) * ζ ^ 2 + ((7375 / 9922) : ℂ) * ζ ^ 4 + ((16707 / 19844) : ℂ) * ζ ^ 6 - ((3489 / 9922) : ℂ) * ζ ^ 8 - ((13177 / 19844) : ℂ) * ζ ^ 10 - ((2105 / 9922) : ℂ) * ζ ^ 12 - ((1875 / 19844) : ℂ) * ζ ^ 14 + ((438 / 4961) : ℂ) * ζ ^ 16 + ((2637 / 9922) : ℂ) * ζ ^ 18 - ((183 / 19844) : ℂ) * ζ ^ 20 - ((436 / 4961) : ℂ) * ζ ^ 22 - ((1229 / 9922) : ℂ) * ζ ^ 24 - ((872 / 4961) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((-((2853 / 9922) : ℂ) - ((22131 / 19844) : ℂ) * ζ ^ 2 + ((2853 / 9922) : ℂ) * ζ ^ 4 + ((11753 / 19844) : ℂ) * ζ ^ 6 + ((1526 / 4961) : ℂ) * ζ ^ 8 - ((1163 / 19844) : ℂ) * ζ ^ 10 - ((6315 / 9922) : ℂ) * ζ ^ 12 - ((5625 / 19844) : ℂ) * ζ ^ 14 + ((1314 / 4961) : ℂ) * ζ ^ 16 + ((7911 / 9922) : ℂ) * ζ ^ 18 - ((549 / 19844) : ℂ) * ζ ^ 20 - ((1308 / 4961) : ℂ) * ζ ^ 22 - ((3687 / 9922) : ℂ) * ζ ^ 24 - ((2616 / 4961) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY76_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((4 / 123) : ℂ) + ((83 / 164) : ℂ) * ζ ^ 2 + ((545 / 492) : ℂ) * ζ ^ 6 - ((143 / 164) : ℂ) * ζ ^ 8 - ((575 / 492) : ℂ) * ζ ^ 12 - ((23 / 246) : ℂ) * ζ ^ 18 - ((83 / 164) : ℂ) * ζ ^ 22 + ((425 / 492) : ℂ) * ζ ^ 24 + ((143 / 164) : ℂ) * ζ ^ 28 - ((49 / 492) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((-((103 / 82) : ℂ) + ((95 / 164) : ℂ) * ζ ^ 2 + ((121 / 123) : ℂ) * ζ ^ 6 + ((10 / 123) : ℂ) * ζ ^ 8 + ((55 / 246) : ℂ) * ζ ^ 12 - ((47 / 123) : ℂ) * ζ ^ 18 - ((95 / 164) : ℂ) * ζ ^ 22 - ((181 / 164) : ℂ) * ζ ^ 24 - ((10 / 123) : ℂ) * ζ ^ 28 + ((179 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((((111 / 82) : ℂ) - ((57 / 164) : ℂ) * ζ ^ 2 - ((57 / 41) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 + ((15 / 41) : ℂ) * ζ ^ 12 - ((7 / 41) : ℂ) * ζ ^ 18 + ((57 / 164) : ℂ) * ζ ^ 22 + ((125 / 164) : ℂ) * ζ ^ 24 + ((2 / 41) : ℂ) * ζ ^ 28 - ((44 / 41) : ℂ) * ζ ^ 30)) * Y 4 4
      + ((((397 / 902) : ℂ) + ((1691 / 1804) : ℂ) * ζ ^ 2 + ((133 / 451) : ℂ) * ζ ^ 6 - ((419 / 451) : ℂ) * ζ ^ 8 - ((29 / 902) : ℂ) * ζ ^ 12 - ((380 / 451) : ℂ) * ζ ^ 18 - ((1691 / 1804) : ℂ) * ζ ^ 22 + ((1977 / 1804) : ℂ) * ζ ^ 24 + ((419 / 451) : ℂ) * ζ ^ 28 - ((191 / 902) : ℂ) * ζ ^ 30)) * Y 5 4
      + ((-((4 / 41) : ℂ) - ((19 / 82) : ℂ) * ζ ^ 2 + ((50 / 123) : ℂ) * ζ ^ 6 - ((4 / 123) : ℂ) * ζ ^ 8 - ((145 / 246) : ℂ) * ζ ^ 12 + ((68 / 123) : ℂ) * ζ ^ 18 + ((19 / 82) : ℂ) * ζ ^ 22 + ((14 / 41) : ℂ) * ζ ^ 24 + ((4 / 123) : ℂ) * ζ ^ 28 - ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 6
      + ((((83 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 6) = 0 := by
  have previous :=
    row17_reducedY76_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation06
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((2 / 3) : ℂ) - (2 : ℂ) * ζ ^ 2 - ((2 / 3) : ℂ) * ζ ^ 6 + ((2 / 3) : ℂ) * ζ ^ 8 - ((4 / 3) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 22 + ((2 / 3) : ℂ) * ζ ^ 24 - ((2 / 3) : ℂ) * ζ ^ 28 - ((8 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((8 / 123) : ℂ) - ((103 / 246) : ℂ) * ζ ^ 2 + ((1 / 3) : ℂ) * ζ ^ 4 + ((63 / 82) : ℂ) * ζ ^ 6 - ((2 / 41) : ℂ) * ζ ^ 8 - ((301 / 246) : ℂ) * ζ ^ 10 - ((23 / 41) : ℂ) * ζ ^ 12 + ((143 / 246) : ℂ) * ζ ^ 14 + ((39 / 41) : ℂ) * ζ ^ 16 + ((26 / 123) : ℂ) * ζ ^ 18 - ((55 / 82) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 22 + ((23 / 123) : ℂ) * ζ ^ 24 + ((58 / 123) : ℂ) * ζ ^ 26 - ((8 / 123) : ℂ) * ζ ^ 28)) * Y 0 0
        + ((((2 / 123) : ℂ) - ((64 / 123) : ℂ) * ζ ^ 2 - ((4 / 3) : ℂ) * ζ ^ 4 - ((80 / 123) : ℂ) * ζ ^ 6 + ((85 / 246) : ℂ) * ζ ^ 8 + ((299 / 123) : ℂ) * ζ ^ 10 + ((89 / 123) : ℂ) * ζ ^ 12 - ((269 / 123) : ℂ) * ζ ^ 14 - ((102 / 41) : ℂ) * ζ ^ 16 + ((55 / 123) : ℂ) * ζ ^ 18 + ((94 / 41) : ℂ) * ζ ^ 20 + ((4 / 3) : ℂ) * ζ ^ 22 + ((25 / 123) : ℂ) * ζ ^ 24 - ((80 / 41) : ℂ) * ζ ^ 26 - ((80 / 123) : ℂ) * ζ ^ 28)) * Y 0 1
        + ((((8 / 123) : ℂ) + ((103 / 246) : ℂ) * ζ ^ 2 - ((1 / 3) : ℂ) * ζ ^ 4 - ((63 / 82) : ℂ) * ζ ^ 6 + ((2 / 41) : ℂ) * ζ ^ 8 + ((301 / 246) : ℂ) * ζ ^ 10 + ((23 / 41) : ℂ) * ζ ^ 12 - ((143 / 246) : ℂ) * ζ ^ 14 - ((39 / 41) : ℂ) * ζ ^ 16 - ((26 / 123) : ℂ) * ζ ^ 18 + ((55 / 82) : ℂ) * ζ ^ 20 + ((2 / 3) : ℂ) * ζ ^ 22 - ((23 / 123) : ℂ) * ζ ^ 24 - ((58 / 123) : ℂ) * ζ ^ 26 + ((8 / 123) : ℂ) * ζ ^ 28)) * Y 6 6
        + ((-((179 / 246) : ℂ) - ((2 / 41) : ℂ) * ζ ^ 2 + ((7 / 6) : ℂ) * ζ ^ 4 + ((18 / 41) : ℂ) * ζ ^ 6 - ((62 / 123) : ℂ) * ζ ^ 8 - ((71 / 82) : ℂ) * ζ ^ 10 - ((73 / 246) : ℂ) * ζ ^ 12 + ((193 / 246) : ℂ) * ζ ^ 14 + ((34 / 41) : ℂ) * ζ ^ 16 - ((35 / 82) : ℂ) * ζ ^ 18 - ((94 / 123) : ℂ) * ζ ^ 20 + ((79 / 246) : ℂ) * ζ ^ 24 + ((13 / 41) : ℂ) * ζ ^ 26 - ((28 / 123) : ℂ) * ζ ^ 28)) * Y 7 6)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY76_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      ((-((7 / 123) : ℂ) - ((35 / 82) : ℂ) * ζ ^ 2 + ((31 / 246) : ℂ) * ζ ^ 6 + ((3 / 82) : ℂ) * ζ ^ 8 - ((44 / 123) : ℂ) * ζ ^ 12 + ((26 / 123) : ℂ) * ζ ^ 18 + ((35 / 82) : ℂ) * ζ ^ 22 + ((49 / 246) : ℂ) * ζ ^ 24 - ((3 / 82) : ℂ) * ζ ^ 28 - ((89 / 246) : ℂ) * ζ ^ 30)) * Y 1 0
      + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((50 / 123) : ℂ) * ζ ^ 6 + ((4 / 123) : ℂ) * ζ ^ 8 + ((145 / 246) : ℂ) * ζ ^ 12 - ((68 / 123) : ℂ) * ζ ^ 18 - ((19 / 82) : ℂ) * ζ ^ 22 - ((14 / 41) : ℂ) * ζ ^ 24 - ((4 / 123) : ℂ) * ζ ^ 28 + ((47 / 123) : ℂ) * ζ ^ 30)) * Y 1 1
      + ((-((4 / 41) : ℂ) - ((19 / 82) : ℂ) * ζ ^ 2 + ((50 / 123) : ℂ) * ζ ^ 6 - ((4 / 123) : ℂ) * ζ ^ 8 - ((145 / 246) : ℂ) * ζ ^ 12 + ((68 / 123) : ℂ) * ζ ^ 18 + ((19 / 82) : ℂ) * ζ ^ 22 + ((14 / 41) : ℂ) * ζ ^ 24 + ((4 / 123) : ℂ) * ζ ^ 28 - ((47 / 123) : ℂ) * ζ ^ 30)) * Y 6 6
      + ((((83 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 - ((52 / 123) : ℂ) * ζ ^ 6 - ((9 / 41) : ℂ) * ζ ^ 8 + ((77 / 246) : ℂ) * ζ ^ 12 + ((8 / 123) : ℂ) * ζ ^ 18 - ((5 / 82) : ℂ) * ζ ^ 22 - ((8 / 41) : ℂ) * ζ ^ 24 + ((9 / 41) : ℂ) * ζ ^ 28 + ((62 / 123) : ℂ) * ζ ^ 30)) * Y 7 6) = 0 := by
  have previous :=
    row17_reducedY76_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation14
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((7 / 451) : ℂ) + ((1162 / 1353) : ℂ) * ζ ^ 2 + ((333 / 451) : ℂ) * ζ ^ 6 - ((977 / 1353) : ℂ) * ζ ^ 8 - ((565 / 1353) : ℂ) * ζ ^ 12 - ((857 / 1353) : ℂ) * ζ ^ 18 - ((1162 / 1353) : ℂ) * ζ ^ 22 + ((1382 / 1353) : ℂ) * ζ ^ 24 + ((977 / 1353) : ℂ) * ζ ^ 28 - ((17 / 451) : ℂ) * ζ ^ 30)) * equation
      - (
        ((((79 / 4961) : ℂ) + ((9217 / 19844) : ℂ) * ζ ^ 2 - ((79 / 4961) : ℂ) * ζ ^ 4 + ((568 / 4961) : ℂ) * ζ ^ 6 - ((9855 / 19844) : ℂ) * ζ ^ 8 + ((13 / 4961) : ℂ) * ζ ^ 10 - ((1549 / 19844) : ℂ) * ζ ^ 12 + ((3029 / 19844) : ℂ) * ζ ^ 14 - ((405 / 19844) : ℂ) * ζ ^ 16 + ((2273 / 19844) : ℂ) * ζ ^ 18 - ((3741 / 19844) : ℂ) * ζ ^ 20 + ((51 / 19844) : ℂ) * ζ ^ 22 - ((977 / 9922) : ℂ) * ζ ^ 24 + ((51 / 9922) : ℂ) * ζ ^ 26)) * Y 1 0
        + ((-((27303 / 19844) : ℂ) - ((17505 / 19844) : ℂ) * ζ ^ 2 + ((27303 / 19844) : ℂ) * ζ ^ 4 + ((12057 / 9922) : ℂ) * ζ ^ 6 - ((5419 / 19844) : ℂ) * ζ ^ 8 - ((509 / 4961) : ℂ) * ζ ^ 10 - ((16943 / 19844) : ℂ) * ζ ^ 12 + ((5526 / 4961) : ℂ) * ζ ^ 14 - ((405 / 4961) : ℂ) * ζ ^ 16 + ((10937 / 9922) : ℂ) * ζ ^ 18 - ((15083 / 9922) : ℂ) * ζ ^ 20 + ((51 / 4961) : ℂ) * ζ ^ 22 - ((18563 / 19844) : ℂ) * ζ ^ 24 + ((969 / 19844) : ℂ) * ζ ^ 26)) * Y 1 1
        + ((((27303 / 19844) : ℂ) + ((17505 / 19844) : ℂ) * ζ ^ 2 - ((27303 / 19844) : ℂ) * ζ ^ 4 - ((12057 / 9922) : ℂ) * ζ ^ 6 + ((5419 / 19844) : ℂ) * ζ ^ 8 + ((509 / 4961) : ℂ) * ζ ^ 10 + ((16943 / 19844) : ℂ) * ζ ^ 12 - ((5526 / 4961) : ℂ) * ζ ^ 14 + ((405 / 4961) : ℂ) * ζ ^ 16 - ((10937 / 9922) : ℂ) * ζ ^ 18 + ((15083 / 9922) : ℂ) * ζ ^ 20 - ((51 / 4961) : ℂ) * ζ ^ 22 + ((18563 / 19844) : ℂ) * ζ ^ 24 - ((969 / 19844) : ℂ) * ζ ^ 26)) * Y 4 4
        + ((((8671 / 19844) : ℂ) + ((15115 / 19844) : ℂ) * ζ ^ 2 - ((8671 / 19844) : ℂ) * ζ ^ 4 - ((3065 / 4961) : ℂ) * ζ ^ 6 - ((7107 / 19844) : ℂ) * ζ ^ 8 - ((1423 / 9922) : ℂ) * ζ ^ 10 + ((16751 / 19844) : ℂ) * ζ ^ 12 + ((163 / 9922) : ℂ) * ζ ^ 14 - ((2025 / 9922) : ℂ) * ζ ^ 16 - ((3904 / 4961) : ℂ) * ζ ^ 18 + ((2049 / 4961) : ℂ) * ζ ^ 20 + ((255 / 9922) : ℂ) * ζ ^ 22 + ((12701 / 19844) : ℂ) * ζ ^ 24 - ((663 / 19844) : ℂ) * ζ ^ 26)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY76_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    (
      (((1 : ℂ))) * Y 7 6) = 0 := by
  have previous :=
    row17_reducedY76_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row17_commutatorEquation16
      Y commutesA commutesDiagonal
  linear_combination
    previous
      + ((((2 / 3) : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 - ((2 / 3) : ℂ) * ζ ^ 12 - ((2 / 3) : ℂ) * ζ ^ 18 + ((2 / 3) : ℂ) * ζ ^ 24 - ((4 / 3) : ℂ) * ζ ^ 28 - ((2 / 3) : ℂ) * ζ ^ 30)) * equation
      - (
        ((-((7 / 123) : ℂ) - ((35 / 82) : ℂ) * ζ ^ 2 + ((7 / 123) : ℂ) * ζ ^ 4 + ((24 / 41) : ℂ) * ζ ^ 6 - ((11 / 246) : ℂ) * ζ ^ 8 - ((94 / 123) : ℂ) * ζ ^ 10 - ((35 / 82) : ℂ) * ζ ^ 12 + ((1 / 2) : ℂ) * ζ ^ 14 + ((55 / 82) : ℂ) * ζ ^ 16 - ((13 / 246) : ℂ) * ζ ^ 18 - ((71 / 123) : ℂ) * ζ ^ 20 - ((31 / 246) : ℂ) * ζ ^ 22 + ((32 / 123) : ℂ) * ζ ^ 24 + ((11 / 123) : ℂ) * ζ ^ 26 - ((2 / 123) : ℂ) * ζ ^ 28)) * Y 1 0
        + ((((4 / 41) : ℂ) + ((19 / 82) : ℂ) * ζ ^ 2 - ((4 / 41) : ℂ) * ζ ^ 4 - ((53 / 82) : ℂ) * ζ ^ 6 + ((68 / 123) : ℂ) * ζ ^ 8 + ((125 / 82) : ℂ) * ζ ^ 10 + ((49 / 123) : ℂ) * ζ ^ 12 - ((5 / 3) : ℂ) * ζ ^ 14 - ((53 / 41) : ℂ) * ζ ^ 16 + ((17 / 123) : ℂ) * ζ ^ 18 + ((151 / 123) : ℂ) * ζ ^ 20 + ((91 / 123) : ℂ) * ζ ^ 22 - ((30 / 41) : ℂ) * ζ ^ 24 - ((95 / 123) : ℂ) * ζ ^ 26 - ((20 / 123) : ℂ) * ζ ^ 28)) * Y 1 1
        + ((-((4 / 41) : ℂ) - ((19 / 82) : ℂ) * ζ ^ 2 + ((4 / 41) : ℂ) * ζ ^ 4 + ((53 / 82) : ℂ) * ζ ^ 6 - ((68 / 123) : ℂ) * ζ ^ 8 - ((125 / 82) : ℂ) * ζ ^ 10 - ((49 / 123) : ℂ) * ζ ^ 12 + ((5 / 3) : ℂ) * ζ ^ 14 + ((53 / 41) : ℂ) * ζ ^ 16 - ((17 / 123) : ℂ) * ζ ^ 18 - ((151 / 123) : ℂ) * ζ ^ 20 - ((91 / 123) : ℂ) * ζ ^ 22 + ((30 / 41) : ℂ) * ζ ^ 24 + ((95 / 123) : ℂ) * ζ ^ 26 + ((20 / 123) : ℂ) * ζ ^ 28)) * Y 6 6
        + ((-((40 / 123) : ℂ) + ((5 / 82) : ℂ) * ζ ^ 2 + ((40 / 123) : ℂ) * ζ ^ 4 - ((85 / 246) : ℂ) * ζ ^ 6 - ((19 / 82) : ℂ) * ζ ^ 8 + ((103 / 246) : ℂ) * ζ ^ 10 + ((5 / 82) : ℂ) * ζ ^ 12 - ((1 / 2) : ℂ) * ζ ^ 14 - ((47 / 246) : ℂ) * ζ ^ 16 + ((13 / 41) : ℂ) * ζ ^ 18 + ((73 / 246) : ℂ) * ζ ^ 20 - ((10 / 41) : ℂ) * ζ ^ 22 - ((28 / 123) : ℂ) * ζ ^ 24 + ((16 / 123) : ℂ) * ζ ^ 26 + ((4 / 41) : ℂ) * ζ ^ 28)) * Y 7 6)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row17_reducedY76
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    Y 7 6 = 0 := by
  have reduced :=
    row17_reducedY76_combinationStep05 Y commutesA commutesDiagonal
  linear_combination reduced


/-- A matrix commuting with both transformed row 17 generators is
scalar. -/
theorem alternatingSixAmbientRow17Transformed_scalar_commutant
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow17TransformedGeneratorA =
        alternatingSixAmbientRow17TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow17GeneratorBDiagonal =
        alternatingSixAmbientRow17GeneratorBDiagonal * Y) :
    ∃ c : ℂ,
      Y = c • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY26 :
      Y 2 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 6 (by decide)
  have hY27 :
      Y 2 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 2 7 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY36 :
      Y 3 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 6 (by decide)
  have hY37 :
      Y 3 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 3 7 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 3 (by decide)
  have hY46 :
      Y 4 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 6 (by decide)
  have hY47 :
      Y 4 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 4 7 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 3 (by decide)
  have hY56 :
      Y 5 6 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 6 (by decide)
  have hY57 :
      Y 5 7 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 5 7 (by decide)
  have hY60 :
      Y 6 0 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 0 (by decide)
  have hY61 :
      Y 6 1 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 1 (by decide)
  have hY62 :
      Y 6 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 2 (by decide)
  have hY63 :
      Y 6 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 3 (by decide)
  have hY64 :
      Y 6 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 4 (by decide)
  have hY65 :
      Y 6 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 6 5 (by decide)
  have hY70 :
      Y 7 0 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 0 (by decide)
  have hY71 :
      Y 7 1 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 1 (by decide)
  have hY72 :
      Y 7 2 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 2 (by decide)
  have hY73 :
      Y 7 3 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 3 (by decide)
  have hY74 :
      Y 7 4 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 4 (by decide)
  have hY75 :
      Y 7 5 = 0 :=
    alternatingSixAmbientRow17_off_block
      Y commutesDiagonal 7 5 (by decide)

  have reducedY00 : Y 0 0 = Y 7 7 :=
    row17_reducedY00 Y commutesA commutesDiagonal
  have reducedY01 : Y 0 1 = 0 :=
    row17_reducedY01 Y commutesA commutesDiagonal
  have reducedY10 : Y 1 0 = 0 :=
    row17_reducedY10 Y commutesA commutesDiagonal
  have reducedY11 : Y 1 1 = Y 7 7 :=
    row17_reducedY11 Y commutesA commutesDiagonal
  have reducedY22 : Y 2 2 = Y 7 7 :=
    row17_reducedY22 Y commutesA commutesDiagonal
  have reducedY23 : Y 2 3 = 0 :=
    row17_reducedY23 Y commutesA commutesDiagonal
  have reducedY32 : Y 3 2 = 0 :=
    row17_reducedY32 Y commutesA commutesDiagonal
  have reducedY33 : Y 3 3 = Y 7 7 :=
    row17_reducedY33 Y commutesA commutesDiagonal
  have reducedY44 : Y 4 4 = Y 7 7 :=
    row17_reducedY44 Y commutesA commutesDiagonal
  have reducedY45 : Y 4 5 = 0 :=
    row17_reducedY45 Y commutesA commutesDiagonal
  have reducedY54 : Y 5 4 = 0 :=
    row17_reducedY54 Y commutesA commutesDiagonal
  have reducedY55 : Y 5 5 = Y 7 7 :=
    row17_reducedY55 Y commutesA commutesDiagonal
  have reducedY66 : Y 6 6 = Y 7 7 :=
    row17_reducedY66 Y commutesA commutesDiagonal
  have reducedY67 : Y 6 7 = 0 :=
    row17_reducedY67 Y commutesA commutesDiagonal
  have reducedY76 : Y 7 6 = 0 :=
    row17_reducedY76 Y commutesA commutesDiagonal
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

/-- Every matrix commuting with both original row 17 presentation
generators is scalar. -/
theorem alternatingSixAmbientRow17_scalar_commutant
    (X : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      X * alternatingSixFiveAmbient_row17_matrixA =
        alternatingSixFiveAmbient_row17_matrixA * X)
    (commutesB :
      X * alternatingSixFiveAmbient_row17_matrixB =
        alternatingSixFiveAmbient_row17_matrixB * X) :
    ∃ c : ℂ,
      X = c • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  apply Matrix.scalar_commutant_of_diagonal_basis
    alternatingSixFiveAmbient_row17_matrixA
    alternatingSixFiveAmbient_row17_matrixB
    alternatingSixAmbientRow17Eigenbasis
    alternatingSixAmbientRow17EigenbasisInverse
    alternatingSixAmbientRow17TransformedGeneratorA
    alternatingSixAmbientRow17GeneratorBEigenvalue
    alternatingSixAmbientRow17EigenbasisInverse_mul
    alternatingSixAmbientRow17Eigenbasis_mul_inverse
    alternatingSixAmbientRow17GeneratorB_mul_eigenbasis
    alternatingSixAmbientRow17TransformedGeneratorA_eq
    alternatingSixAmbientRow17Transformed_scalar_commutant
    X commutesA commutesB

end InductiveMcKay
end McKayConjecture
