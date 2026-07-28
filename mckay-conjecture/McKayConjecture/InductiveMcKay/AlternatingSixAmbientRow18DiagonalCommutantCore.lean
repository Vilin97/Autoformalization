/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DiagonalBasisMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalData

/-!
# Commutator equations for ambient row 18

This generated core records off-block vanishing and the exact commutator
equations used by the chained row-reduction certificates.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Entries between distinct second-generator eigenspaces
vanish in its commutant. -/
theorem alternatingSixAmbientRow18_off_block
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y)
    (i j : Fin 8)
    (different :
      alternatingSixAmbientRow18EigenvalueLabel i ≠
        alternatingSixAmbientRow18EigenvalueLabel j) :
    Y i j = 0 := by
  apply Matrix.entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
    Y alternatingSixAmbientRow18GeneratorBEigenvalue
  · exact commutesDiagonal
  · intro equalEigenvalues
    apply different
    apply alternatingSixOrderEightOddEigenvalue_injective
    simpa [
      alternatingSixAmbientRow18GeneratorBEigenvalue] using
      equalEigenvalues.symm


theorem row18_commutatorEquation00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31)) * Y 0 1
      + ((((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31)) * Y 1 0) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY60 :
      Y 6 0 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 6 0 (by decide)
  have hY70 :
      Y 7 0 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 7 0 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (0 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
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

theorem row18_commutatorEquation01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31)) * Y 0 0
      + ((-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31)) * Y 0 1
      + ((((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31)) * Y 1 1) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY61 :
      Y 6 1 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 6 1 (by decide)
  have hY71 :
      Y 7 1 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 7 1 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (1 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
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

theorem row18_commutatorEquation02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31)) * Y 0 0
      + ((((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31)) * Y 0 1
      + ((((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31)) * Y 2 2
      + ((-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31)) * Y 3 2) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY62 :
      Y 6 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 6 2 (by decide)
  have hY72 :
      Y 7 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 7 2 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (2 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
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

theorem row18_commutatorEquation03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31)) * Y 0 0
      + ((((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31)) * Y 0 1
      + ((((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31)) * Y 2 3
      + ((-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31)) * Y 3 3) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 4 3 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 5 3 (by decide)
  have hY63 :
      Y 6 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 6 3 (by decide)
  have hY73 :
      Y 7 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 7 3 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (3 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
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

theorem row18_commutatorEquation04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((-((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((57 / 158) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((57 / 158) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((57 / 158) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31)) * Y 0 0
      + ((-((5 / 79) : ℂ) - ((43 / 316) : ℂ) * ζ ^ 1 - ((9 / 158) : ℂ) * ζ ^ 2 - ((63 / 316) : ℂ) * ζ ^ 5 + ((1 / 158) : ℂ) * ζ ^ 6 + ((1 / 158) : ℂ) * ζ ^ 8 - ((63 / 316) : ℂ) * ζ ^ 9 + ((57 / 158) : ℂ) * ζ ^ 11 + ((31 / 316) : ℂ) * ζ ^ 12 + ((43 / 316) : ℂ) * ζ ^ 13 - ((3 / 79) : ℂ) * ζ ^ 15 + ((43 / 316) : ℂ) * ζ ^ 17 - ((3 / 316) : ℂ) * ζ ^ 18 + ((53 / 316) : ℂ) * ζ ^ 21 + ((9 / 158) : ℂ) * ζ ^ 22 + ((1 / 316) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((1 / 158) : ℂ) * ζ ^ 28 - ((43 / 316) : ℂ) * ζ ^ 29 - ((29 / 316) : ℂ) * ζ ^ 30 - ((57 / 158) : ℂ) * ζ ^ 31)) * Y 0 1
      + ((((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((57 / 158) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((57 / 158) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((57 / 158) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31)) * Y 4 4
      + ((-((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31)) * Y 5 4) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY64 :
      Y 6 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 6 4 (by decide)
  have hY74 :
      Y 7 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 7 4 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (4 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
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

theorem row18_commutatorEquation05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31)) * Y 0 0
      + ((((16 / 79) : ℂ) + ((35 / 316) : ℂ) * ζ ^ 1 - ((61 / 316) : ℂ) * ζ ^ 2 + ((87 / 316) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 - ((6 / 79) : ℂ) * ζ ^ 8 - ((31 / 316) : ℂ) * ζ ^ 9 - ((14 / 79) : ℂ) * ζ ^ 11 - ((26 / 79) : ℂ) * ζ ^ 12 - ((35 / 316) : ℂ) * ζ ^ 13 - ((49 / 316) : ℂ) * ζ ^ 15 - ((35 / 316) : ℂ) * ζ ^ 17 + ((61 / 316) : ℂ) * ζ ^ 18 + ((13 / 79) : ℂ) * ζ ^ 21 + ((61 / 316) : ℂ) * ζ ^ 22 + ((32 / 79) : ℂ) * ζ ^ 24 + ((19 / 158) : ℂ) * ζ ^ 25 + ((13 / 79) : ℂ) * ζ ^ 27 + ((6 / 79) : ℂ) * ζ ^ 28 + ((35 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((14 / 79) : ℂ) * ζ ^ 31)) * Y 0 1
      + ((((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((57 / 158) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((57 / 158) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((57 / 158) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31)) * Y 4 5
      + ((-((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31)) * Y 5 5) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY65 :
      Y 6 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 6 5 (by decide)
  have hY75 :
      Y 7 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 7 5 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (5 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
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

theorem row18_commutatorEquation06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((73 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((105 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((73 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31)) * Y 0 0
      + ((-((5 / 316) : ℂ) + ((3 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((33 / 158) : ℂ) * ζ ^ 3 + ((3 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 + ((10 / 79) : ℂ) * ζ ^ 8 - ((3 / 316) : ℂ) * ζ ^ 9 - ((33 / 316) : ℂ) * ζ ^ 11 - ((3 / 79) : ℂ) * ζ ^ 12 - ((3 / 316) : ℂ) * ζ ^ 13 - ((35 / 158) : ℂ) * ζ ^ 15 - ((3 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 - ((45 / 158) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((59 / 316) : ℂ) * ζ ^ 24 - ((1 / 79) : ℂ) * ζ ^ 27 - ((10 / 79) : ℂ) * ζ ^ 28 + ((3 / 316) : ℂ) * ζ ^ 29 - ((13 / 79) : ℂ) * ζ ^ 30 + ((33 / 316) : ℂ) * ζ ^ 31)) * Y 0 1
      + ((-((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((73 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((105 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((73 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31)) * Y 6 6
      + ((((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31)) * Y 7 6) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY26 :
      Y 2 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 6 (by decide)
  have hY36 :
      Y 3 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 3 6 (by decide)
  have hY46 :
      Y 4 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 4 6 (by decide)
  have hY56 :
      Y 5 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 5 6 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (6 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
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

theorem row18_commutatorEquation07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31)) * Y 0 0
      + ((((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31)) * Y 0 1
      + ((-((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((73 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((105 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((73 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31)) * Y 6 7
      + ((((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31)) * Y 7 7) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY27 :
      Y 2 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 7 (by decide)
  have hY37 :
      Y 3 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 3 7 (by decide)
  have hY47 :
      Y 4 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 4 7 (by decide)
  have hY57 :
      Y 5 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 5 7 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (0 : Fin 8))
      (7 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
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

theorem row18_commutatorEquation12
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31)) * Y 1 0
      + ((((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31)) * Y 1 1
      + ((-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31)) * Y 2 2
      + ((-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31)) * Y 3 2) = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY62 :
      Y 6 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 6 2 (by decide)
  have hY72 :
      Y 7 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 7 2 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (2 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
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

theorem row18_commutatorEquation13
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31)) * Y 1 0
      + ((((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31)) * Y 1 1
      + ((-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31)) * Y 2 3
      + ((-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31)) * Y 3 3) = 0 := by
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 4 3 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 5 3 (by decide)
  have hY63 :
      Y 6 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 6 3 (by decide)
  have hY73 :
      Y 7 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 7 3 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (3 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
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

theorem row18_commutatorEquation14
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((-((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((57 / 158) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((57 / 158) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((57 / 158) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31)) * Y 1 0
      + ((-((5 / 79) : ℂ) - ((43 / 316) : ℂ) * ζ ^ 1 - ((9 / 158) : ℂ) * ζ ^ 2 - ((63 / 316) : ℂ) * ζ ^ 5 + ((1 / 158) : ℂ) * ζ ^ 6 + ((1 / 158) : ℂ) * ζ ^ 8 - ((63 / 316) : ℂ) * ζ ^ 9 + ((57 / 158) : ℂ) * ζ ^ 11 + ((31 / 316) : ℂ) * ζ ^ 12 + ((43 / 316) : ℂ) * ζ ^ 13 - ((3 / 79) : ℂ) * ζ ^ 15 + ((43 / 316) : ℂ) * ζ ^ 17 - ((3 / 316) : ℂ) * ζ ^ 18 + ((53 / 316) : ℂ) * ζ ^ 21 + ((9 / 158) : ℂ) * ζ ^ 22 + ((1 / 316) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((1 / 158) : ℂ) * ζ ^ 28 - ((43 / 316) : ℂ) * ζ ^ 29 - ((29 / 316) : ℂ) * ζ ^ 30 - ((57 / 158) : ℂ) * ζ ^ 31)) * Y 1 1
      + ((((5 / 79) : ℂ) + ((43 / 316) : ℂ) * ζ ^ 1 + ((9 / 158) : ℂ) * ζ ^ 2 + ((63 / 316) : ℂ) * ζ ^ 5 - ((1 / 158) : ℂ) * ζ ^ 6 - ((1 / 158) : ℂ) * ζ ^ 8 + ((63 / 316) : ℂ) * ζ ^ 9 - ((57 / 158) : ℂ) * ζ ^ 11 - ((31 / 316) : ℂ) * ζ ^ 12 - ((43 / 316) : ℂ) * ζ ^ 13 + ((3 / 79) : ℂ) * ζ ^ 15 - ((43 / 316) : ℂ) * ζ ^ 17 + ((3 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 - ((9 / 158) : ℂ) * ζ ^ 22 - ((1 / 316) : ℂ) * ζ ^ 24 - ((5 / 79) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((1 / 158) : ℂ) * ζ ^ 28 + ((43 / 316) : ℂ) * ζ ^ 29 + ((29 / 316) : ℂ) * ζ ^ 30 + ((57 / 158) : ℂ) * ζ ^ 31)) * Y 4 4
      + ((-((16 / 79) : ℂ) - ((35 / 316) : ℂ) * ζ ^ 1 + ((61 / 316) : ℂ) * ζ ^ 2 - ((87 / 316) : ℂ) * ζ ^ 3 + ((3 / 316) : ℂ) * ζ ^ 5 + ((6 / 79) : ℂ) * ζ ^ 8 + ((31 / 316) : ℂ) * ζ ^ 9 + ((14 / 79) : ℂ) * ζ ^ 11 + ((26 / 79) : ℂ) * ζ ^ 12 + ((35 / 316) : ℂ) * ζ ^ 13 + ((49 / 316) : ℂ) * ζ ^ 15 + ((35 / 316) : ℂ) * ζ ^ 17 - ((61 / 316) : ℂ) * ζ ^ 18 - ((13 / 79) : ℂ) * ζ ^ 21 - ((61 / 316) : ℂ) * ζ ^ 22 - ((32 / 79) : ℂ) * ζ ^ 24 - ((19 / 158) : ℂ) * ζ ^ 25 - ((13 / 79) : ℂ) * ζ ^ 27 - ((6 / 79) : ℂ) * ζ ^ 28 - ((35 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((14 / 79) : ℂ) * ζ ^ 31)) * Y 5 4) = 0 := by
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY64 :
      Y 6 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 6 4 (by decide)
  have hY74 :
      Y 7 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 7 4 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (4 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
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

theorem row18_commutatorEquation15
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31)) * Y 1 0
      + ((((16 / 79) : ℂ) + ((35 / 316) : ℂ) * ζ ^ 1 - ((61 / 316) : ℂ) * ζ ^ 2 + ((87 / 316) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 - ((6 / 79) : ℂ) * ζ ^ 8 - ((31 / 316) : ℂ) * ζ ^ 9 - ((14 / 79) : ℂ) * ζ ^ 11 - ((26 / 79) : ℂ) * ζ ^ 12 - ((35 / 316) : ℂ) * ζ ^ 13 - ((49 / 316) : ℂ) * ζ ^ 15 - ((35 / 316) : ℂ) * ζ ^ 17 + ((61 / 316) : ℂ) * ζ ^ 18 + ((13 / 79) : ℂ) * ζ ^ 21 + ((61 / 316) : ℂ) * ζ ^ 22 + ((32 / 79) : ℂ) * ζ ^ 24 + ((19 / 158) : ℂ) * ζ ^ 25 + ((13 / 79) : ℂ) * ζ ^ 27 + ((6 / 79) : ℂ) * ζ ^ 28 + ((35 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((14 / 79) : ℂ) * ζ ^ 31)) * Y 1 1
      + ((((5 / 79) : ℂ) + ((43 / 316) : ℂ) * ζ ^ 1 + ((9 / 158) : ℂ) * ζ ^ 2 + ((63 / 316) : ℂ) * ζ ^ 5 - ((1 / 158) : ℂ) * ζ ^ 6 - ((1 / 158) : ℂ) * ζ ^ 8 + ((63 / 316) : ℂ) * ζ ^ 9 - ((57 / 158) : ℂ) * ζ ^ 11 - ((31 / 316) : ℂ) * ζ ^ 12 - ((43 / 316) : ℂ) * ζ ^ 13 + ((3 / 79) : ℂ) * ζ ^ 15 - ((43 / 316) : ℂ) * ζ ^ 17 + ((3 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 - ((9 / 158) : ℂ) * ζ ^ 22 - ((1 / 316) : ℂ) * ζ ^ 24 - ((5 / 79) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((1 / 158) : ℂ) * ζ ^ 28 + ((43 / 316) : ℂ) * ζ ^ 29 + ((29 / 316) : ℂ) * ζ ^ 30 + ((57 / 158) : ℂ) * ζ ^ 31)) * Y 4 5
      + ((-((16 / 79) : ℂ) - ((35 / 316) : ℂ) * ζ ^ 1 + ((61 / 316) : ℂ) * ζ ^ 2 - ((87 / 316) : ℂ) * ζ ^ 3 + ((3 / 316) : ℂ) * ζ ^ 5 + ((6 / 79) : ℂ) * ζ ^ 8 + ((31 / 316) : ℂ) * ζ ^ 9 + ((14 / 79) : ℂ) * ζ ^ 11 + ((26 / 79) : ℂ) * ζ ^ 12 + ((35 / 316) : ℂ) * ζ ^ 13 + ((49 / 316) : ℂ) * ζ ^ 15 + ((35 / 316) : ℂ) * ζ ^ 17 - ((61 / 316) : ℂ) * ζ ^ 18 - ((13 / 79) : ℂ) * ζ ^ 21 - ((61 / 316) : ℂ) * ζ ^ 22 - ((32 / 79) : ℂ) * ζ ^ 24 - ((19 / 158) : ℂ) * ζ ^ 25 - ((13 / 79) : ℂ) * ζ ^ 27 - ((6 / 79) : ℂ) * ζ ^ 28 - ((35 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((14 / 79) : ℂ) * ζ ^ 31)) * Y 5 5) = 0 := by
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY65 :
      Y 6 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 6 5 (by decide)
  have hY75 :
      Y 7 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 7 5 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (5 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY05,
      hY12,
      hY13,
      hY14,
      hY15,
      hY16,
      hY17,
      hY25,
      hY35,
      hY65,
      hY75] at equation
  linear_combination equation

theorem row18_commutatorEquation16
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((73 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((105 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((73 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31)) * Y 1 0
      + ((-((5 / 316) : ℂ) + ((3 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((33 / 158) : ℂ) * ζ ^ 3 + ((3 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 + ((10 / 79) : ℂ) * ζ ^ 8 - ((3 / 316) : ℂ) * ζ ^ 9 - ((33 / 316) : ℂ) * ζ ^ 11 - ((3 / 79) : ℂ) * ζ ^ 12 - ((3 / 316) : ℂ) * ζ ^ 13 - ((35 / 158) : ℂ) * ζ ^ 15 - ((3 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 - ((45 / 158) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((59 / 316) : ℂ) * ζ ^ 24 - ((1 / 79) : ℂ) * ζ ^ 27 - ((10 / 79) : ℂ) * ζ ^ 28 + ((3 / 316) : ℂ) * ζ ^ 29 - ((13 / 79) : ℂ) * ζ ^ 30 + ((33 / 316) : ℂ) * ζ ^ 31)) * Y 1 1
      + ((((5 / 316) : ℂ) - ((3 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((33 / 158) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 + ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 + ((3 / 316) : ℂ) * ζ ^ 9 + ((33 / 316) : ℂ) * ζ ^ 11 + ((3 / 79) : ℂ) * ζ ^ 12 + ((3 / 316) : ℂ) * ζ ^ 13 + ((35 / 158) : ℂ) * ζ ^ 15 + ((3 / 316) : ℂ) * ζ ^ 17 + ((19 / 316) : ℂ) * ζ ^ 18 + ((45 / 158) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((1 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 - ((3 / 316) : ℂ) * ζ ^ 29 + ((13 / 79) : ℂ) * ζ ^ 30 - ((33 / 316) : ℂ) * ζ ^ 31)) * Y 6 6
      + ((-((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((35 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31)) * Y 7 6) = 0 := by
  have hY06 :
      Y 0 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 6 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY26 :
      Y 2 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 6 (by decide)
  have hY36 :
      Y 3 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 3 6 (by decide)
  have hY46 :
      Y 4 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 4 6 (by decide)
  have hY56 :
      Y 5 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 5 6 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (6 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
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

theorem row18_commutatorEquation17
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31)) * Y 1 0
      + ((((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31)) * Y 1 1
      + ((((5 / 316) : ℂ) - ((3 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((33 / 158) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 + ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 + ((3 / 316) : ℂ) * ζ ^ 9 + ((33 / 316) : ℂ) * ζ ^ 11 + ((3 / 79) : ℂ) * ζ ^ 12 + ((3 / 316) : ℂ) * ζ ^ 13 + ((35 / 158) : ℂ) * ζ ^ 15 + ((3 / 316) : ℂ) * ζ ^ 17 + ((19 / 316) : ℂ) * ζ ^ 18 + ((45 / 158) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((1 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 - ((3 / 316) : ℂ) * ζ ^ 29 + ((13 / 79) : ℂ) * ζ ^ 30 - ((33 / 316) : ℂ) * ζ ^ 31)) * Y 6 7
      + ((-((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((35 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31)) * Y 7 7) = 0 := by
  have hY07 :
      Y 0 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 0 7 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY16 :
      Y 1 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 6 (by decide)
  have hY17 :
      Y 1 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 1 7 (by decide)
  have hY27 :
      Y 2 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 7 (by decide)
  have hY37 :
      Y 3 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 3 7 (by decide)
  have hY47 :
      Y 4 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 4 7 (by decide)
  have hY57 :
      Y 5 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 5 7 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (1 : Fin 8))
      (7 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
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

theorem row18_commutatorEquation20
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      ((((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31)) * Y 0 0
      + ((-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31)) * Y 1 0
      + ((-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31)) * Y 2 2
      + ((((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31)) * Y 2 3) = 0 := by
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY26 :
      Y 2 6 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 6 (by decide)
  have hY27 :
      Y 2 7 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 2 7 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY60 :
      Y 6 0 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 6 0 (by decide)
  have hY70 :
      Y 7 0 = 0 :=
    alternatingSixAmbientRow18_off_block
      Y commutesDiagonal 7 0 (by decide)
  have equation :=
    congrFun (congrFun commutesA
      (2 : Fin 8))
      (0 : Fin 8)
  rw [Matrix.mul_apply, Matrix.mul_apply] at equation
  simp only [Fin.sum_univ_succ] at equation
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue] at equation
  simp only [
      hY20,
      hY21,
      hY24,
      hY25,
      hY26,
      hY27,
      hY30,
      hY40,
      hY50,
      hY60,
      hY70] at equation
  linear_combination equation


end InductiveMcKay
end McKayConjecture
