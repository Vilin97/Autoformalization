/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DiagonalBasisMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow15DiagonalData

/-!
# Scalar common commutant for ambient row 15

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
private theorem alternatingSixAmbientRow15_off_block
    (Y : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow15GeneratorBDiagonal =
        alternatingSixAmbientRow15GeneratorBDiagonal * Y)
    (i j : Fin 6)
    (different :
      alternatingSixAmbientRow15EigenvalueLabel i ≠
        alternatingSixAmbientRow15EigenvalueLabel j) :
    Y i j = 0 := by
  apply Matrix.entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
    Y alternatingSixAmbientRow15GeneratorBEigenvalue
  · exact commutesDiagonal
  · intro equalEigenvalues
    apply different
    apply alternatingSixOrderEightOddEigenvalue_injective
    simpa [
      alternatingSixAmbientRow15GeneratorBEigenvalue] using
      equalEigenvalues.symm

private theorem row15_reducedY00
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow15TransformedGeneratorA =
        alternatingSixAmbientRow15TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow15GeneratorBDiagonal =
        alternatingSixAmbientRow15GeneratorBDiagonal * Y) :
    Y 0 0 = Y 5 5 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA00
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA00
  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
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
      alternatingSixAmbientRow15TransformedGeneratorA,
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
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA05
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY15,
      hY25,
      hY35] at commutesA05
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
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
  have commutesA15 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA15
  simp only [Fin.sum_univ_succ] at commutesA15
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA15
  simp only [
      hY05,
      hY12,
      hY13,
      hY14,
      hY15,
      hY25,
      hY35] at commutesA15

  linear_combination
    ((-((893625 / 152497) : ℂ) - ((728910 / 152497) : ℂ) * ζ ^ 3 + ((503247 / 152497) : ℂ) * ζ ^ 5 - ((728910 / 152497) : ℂ) * ζ ^ 7 + ((791881 / 152497) : ℂ) * ζ ^ 10 + ((490301 / 152497) : ℂ) * ζ ^ 15 + ((728910 / 152497) : ℂ) * ζ ^ 19 + ((24345 / 152497) : ℂ) * ζ ^ 20 + ((728910 / 152497) : ℂ) * ζ ^ 23 - ((624343 / 152497) : ℂ) * ζ ^ 25 - ((661564 / 152497) : ℂ) * ζ ^ 30 - ((728910 / 152497) : ℂ) * ζ ^ 31)) * commutesA00
      + ((((889069 / 152497) : ℂ) + ((557369 / 152497) : ℂ) * ζ ^ 3 - ((119459 / 152497) : ℂ) * ζ ^ 5 + ((557369 / 152497) : ℂ) * ζ ^ 7 - ((1119376 / 152497) : ℂ) * ζ ^ 10 - ((1129709 / 152497) : ℂ) * ζ ^ 15 - ((557369 / 152497) : ℂ) * ζ ^ 19 + ((350708 / 152497) : ℂ) * ζ ^ 20 - ((557369 / 152497) : ℂ) * ζ ^ 23 + ((1030658 / 152497) : ℂ) * ζ ^ 25 + ((285551 / 152497) : ℂ) * ζ ^ 30 + ((557369 / 152497) : ℂ) * ζ ^ 31)) * commutesA01
      + ((-((597 / 73) : ℂ) + ((128 / 73) : ℂ) * ζ ^ 3 + ((311 / 73) : ℂ) * ζ ^ 5 + ((128 / 73) : ℂ) * ζ ^ 7 + ((691 / 73) : ℂ) * ζ ^ 10 - ((655 / 73) : ℂ) * ζ ^ 15 - ((128 / 73) : ℂ) * ζ ^ 19 - ((177 / 73) : ℂ) * ζ ^ 20 - ((128 / 73) : ℂ) * ζ ^ 23 + ((371 / 73) : ℂ) * ζ ^ 25 - ((20 / 73) : ℂ) * ζ ^ 30 + ((128 / 73) : ℂ) * ζ ^ 31)) * commutesA02
      + (((3 : ℂ) * ζ ^ 3 - ζ ^ 5 + (3 : ℂ) * ζ ^ 7 + ζ ^ 10 - ζ ^ 15 - (3 : ℂ) * ζ ^ 19 + ζ ^ 20 - (3 : ℂ) * ζ ^ 23 - (3 : ℂ) * ζ ^ 30 + (3 : ℂ) * ζ ^ 31)) * commutesA05
      + ((((264 / 73) : ℂ) - ((707 / 73) : ℂ) * ζ ^ 3 + ((872 / 73) : ℂ) * ζ ^ 5 - ((707 / 73) : ℂ) * ζ ^ 7 - ((595 / 73) : ℂ) * ζ ^ 10 + ((330 / 73) : ℂ) * ζ ^ 15 + ((707 / 73) : ℂ) * ζ ^ 19 + ((287 / 73) : ℂ) * ζ ^ 20 + ((707 / 73) : ℂ) * ζ ^ 23 - ((835 / 73) : ℂ) * ζ ^ 25 + ((277 / 73) : ℂ) * ζ ^ 30 - ((707 / 73) : ℂ) * ζ ^ 31)) * commutesA12
      + (((3 : ℂ) - ζ ^ 5 - (4 : ℂ) * ζ ^ 10 + ζ ^ 15 - (3 : ℂ) * ζ ^ 25 + ζ ^ 30)) * commutesA15
      - (
        ((-((1499057 / 609988) : ℂ) + ((180447 / 609988) : ℂ) * ζ ^ 3 + ((1499057 / 609988) : ℂ) * ζ ^ 4 - ((431904 / 152497) : ℂ) * ζ ^ 5 + ((728667 / 304994) : ℂ) * ζ ^ 6 - ((1001245 / 304994) : ℂ) * ζ ^ 8 + ((431904 / 152497) : ℂ) * ζ ^ 9 + ((4587499 / 609988) : ℂ) * ζ ^ 10 - ((1220121 / 609988) : ℂ) * ζ ^ 13 - ((3130165 / 609988) : ℂ) * ζ ^ 14 + ((1007405 / 304994) : ℂ) * ζ ^ 15 + ((222190 / 152497) : ℂ) * ζ ^ 18 - ((1007405 / 304994) : ℂ) * ζ ^ 19 - ((2419425 / 609988) : ℂ) * ζ ^ 20 - ((728667 / 304994) : ℂ) * ζ ^ 22 + ((2096187 / 609988) : ℂ) * ζ ^ 23 + ((2419425 / 609988) : ℂ) * ζ ^ 24 - ((845009 / 304994) : ℂ) * ζ ^ 25 - ((728667 / 304994) : ℂ) * ζ ^ 26 + ((56082 / 152497) : ℂ) * ζ ^ 28 + ((845009 / 304994) : ℂ) * ζ ^ 29 + ((728667 / 304994) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((-((3034383 / 609988) : ℂ) + ((5528993 / 609988) : ℂ) * ζ ^ 3 + ((3034383 / 609988) : ℂ) * ζ ^ 4 + ((362851 / 304994) : ℂ) * ζ ^ 5 + ((2669467 / 609988) : ℂ) * ζ ^ 6 - ((2478971 / 304994) : ℂ) * ζ ^ 8 - ((362851 / 304994) : ℂ) * ζ ^ 9 + ((6530223 / 304994) : ℂ) * ζ ^ 10 - ((1818217 / 304994) : ℂ) * ζ ^ 13 - ((10390979 / 609988) : ℂ) * ζ ^ 14 - ((784455 / 609988) : ℂ) * ζ ^ 15 + ((3675303 / 609988) : ℂ) * ζ ^ 18 + ((784455 / 609988) : ℂ) * ζ ^ 19 - ((10463791 / 609988) : ℂ) * ζ ^ 20 - ((2669467 / 609988) : ℂ) * ζ ^ 22 - ((182621 / 304994) : ℂ) * ζ ^ 23 + ((10463791 / 609988) : ℂ) * ζ ^ 24 + ((13686 / 152497) : ℂ) * ζ ^ 25 - ((2669467 / 609988) : ℂ) * ζ ^ 26 - ((1250825 / 609988) : ℂ) * ζ ^ 28 - ((13686 / 152497) : ℂ) * ζ ^ 29 + ((2669467 / 609988) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((-((343407 / 304994) : ℂ) + ((421260 / 152497) : ℂ) * ζ ^ 3 + ((343407 / 304994) : ℂ) * ζ ^ 4 - ((281832 / 152497) : ℂ) * ζ ^ 5 - ((19103 / 609988) : ℂ) * ζ ^ 6 - ((4639 / 2089) : ℂ) * ζ ^ 8 + ((281832 / 152497) : ℂ) * ζ ^ 9 + ((844628 / 152497) : ℂ) * ζ ^ 10 - ((2596497 / 609988) : ℂ) * ζ ^ 13 - ((3397615 / 609988) : ℂ) * ζ ^ 14 + ((1352281 / 304994) : ℂ) * ζ ^ 15 + ((1635425 / 609988) : ℂ) * ζ ^ 18 - ((1352281 / 304994) : ℂ) * ζ ^ 19 - ((761007 / 609988) : ℂ) * ζ ^ 20 + ((19103 / 609988) : ℂ) * ζ ^ 22 + ((2526505 / 609988) : ℂ) * ζ ^ 23 + ((761007 / 609988) : ℂ) * ζ ^ 24 - ((1215398 / 152497) : ℂ) * ζ ^ 25 + ((19103 / 609988) : ℂ) * ζ ^ 26 + ((873993 / 609988) : ℂ) * ζ ^ 28 + ((1215398 / 152497) : ℂ) * ζ ^ 29 - ((19103 / 609988) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((((1578439 / 609988) : ℂ) - ((3656543 / 609988) : ℂ) * ζ ^ 3 - ((1578439 / 609988) : ℂ) * ζ ^ 4 + ((1563623 / 304994) : ℂ) * ζ ^ 5 + ((362185 / 609988) : ℂ) * ζ ^ 6 + ((311568 / 152497) : ℂ) * ζ ^ 8 - ((1563623 / 304994) : ℂ) * ζ ^ 9 - ((2347019 / 304994) : ℂ) * ζ ^ 10 + ((3757139 / 304994) : ℂ) * ζ ^ 13 + ((5056223 / 609988) : ℂ) * ζ ^ 14 - ((7598707 / 609988) : ℂ) * ζ ^ 15 - ((445713 / 152497) : ℂ) * ζ ^ 18 + ((7598707 / 609988) : ℂ) * ζ ^ 19 + ((936235 / 609988) : ℂ) * ζ ^ 20 - ((362185 / 609988) : ℂ) * ζ ^ 22 - ((5388451 / 609988) : ℂ) * ζ ^ 23 - ((936235 / 609988) : ℂ) * ζ ^ 24 + ((1338531 / 152497) : ℂ) * ζ ^ 25 - ((362185 / 609988) : ℂ) * ζ ^ 26 + ((117305 / 152497) : ℂ) * ζ ^ 28 - ((1338531 / 152497) : ℂ) * ζ ^ 29 + ((362185 / 609988) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((66 / 73) : ℂ) + ((392 / 73) : ℂ) * ζ ^ 3 + ((66 / 73) : ℂ) * ζ ^ 4 - ((218 / 73) : ℂ) * ζ ^ 5 - ((835 / 292) : ℂ) * ζ ^ 6 + ((297 / 292) : ℂ) * ζ ^ 8 + ((218 / 73) : ℂ) * ζ ^ 9 + ((6 / 73) : ℂ) * ζ ^ 10 - ((2865 / 292) : ℂ) * ζ ^ 13 - ((859 / 292) : ℂ) * ζ ^ 14 + ((2971 / 292) : ℂ) * ζ ^ 15 + ((87 / 146) : ℂ) * ζ ^ 18 - ((2971 / 292) : ℂ) * ζ ^ 19 + ((126 / 73) : ℂ) * ζ ^ 20 + ((835 / 292) : ℂ) * ζ ^ 22 + ((2021 / 292) : ℂ) * ζ ^ 23 - ((126 / 73) : ℂ) * ζ ^ 24 - ((1839 / 292) : ℂ) * ζ ^ 25 + ((835 / 292) : ℂ) * ζ ^ 26 - ((287 / 146) : ℂ) * ζ ^ 28 + ((1839 / 292) : ℂ) * ζ ^ 29 - ((835 / 292) : ℂ) * ζ ^ 30)) * Y 2 2
        + ((-((39 / 73) : ℂ) - ((225 / 146) : ℂ) * ζ ^ 3 + ((39 / 73) : ℂ) * ζ ^ 4 + ((285 / 292) : ℂ) * ζ ^ 5 + ((333 / 292) : ℂ) * ζ ^ 6 - ((109 / 146) : ℂ) * ζ ^ 8 - ((285 / 292) : ℂ) * ζ ^ 9 + ((681 / 292) : ℂ) * ζ ^ 10 + ((178 / 73) : ℂ) * ζ ^ 13 - ((87 / 73) : ℂ) * ζ ^ 14 - ((565 / 292) : ℂ) * ζ ^ 15 + ((23 / 292) : ℂ) * ζ ^ 18 + ((565 / 292) : ℂ) * ζ ^ 19 - ((555 / 292) : ℂ) * ζ ^ 20 - ((333 / 292) : ℂ) * ζ ^ 22 - ((355 / 292) : ℂ) * ζ ^ 23 + ((555 / 292) : ℂ) * ζ ^ 24 + ((100 / 73) : ℂ) * ζ ^ 25 - ((333 / 292) : ℂ) * ζ ^ 26 - ((3 / 73) : ℂ) * ζ ^ 28 - ((100 / 73) : ℂ) * ζ ^ 29 + ((333 / 292) : ℂ) * ζ ^ 30)) * Y 4 5
        + ((((113 / 146) : ℂ) + ((24 / 73) : ℂ) * ζ ^ 3 - ((113 / 146) : ℂ) * ζ ^ 4 + ((101 / 146) : ℂ) * ζ ^ 5 - ((9 / 73) : ℂ) * ζ ^ 6 + ((65 / 292) : ℂ) * ζ ^ 8 - ((101 / 146) : ℂ) * ζ ^ 9 + ((27 / 292) : ℂ) * ζ ^ 10 - ((37 / 73) : ℂ) * ζ ^ 13 - ((63 / 292) : ℂ) * ζ ^ 14 - ((149 / 146) : ℂ) * ζ ^ 15 + ((127 / 146) : ℂ) * ζ ^ 18 + ((149 / 146) : ℂ) * ζ ^ 19 + ((103 / 146) : ℂ) * ζ ^ 20 + ((9 / 73) : ℂ) * ζ ^ 22 - ((445 / 292) : ℂ) * ζ ^ 23 - ((103 / 146) : ℂ) * ζ ^ 24 + ((85 / 292) : ℂ) * ζ ^ 25 + ((9 / 73) : ℂ) * ζ ^ 26 + ((121 / 146) : ℂ) * ζ ^ 28 - ((85 / 292) : ℂ) * ζ ^ 29 - ((9 / 73) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row15_reducedY01
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow15TransformedGeneratorA =
        alternatingSixAmbientRow15TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow15GeneratorBDiagonal =
        alternatingSixAmbientRow15GeneratorBDiagonal * Y) :
    Y 0 1 = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA00
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA00
  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
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
      alternatingSixAmbientRow15TransformedGeneratorA,
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
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
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
    ((-(4 : ℂ) - ζ ^ 5 + ζ ^ 10 + (5 : ℂ) * ζ ^ 15 + ζ ^ 20 - (3 : ℂ) * ζ ^ 25 - ζ ^ 30)) * commutesA00
      + (((7 : ℂ) + ζ ^ 3 + ζ ^ 5 + ζ ^ 7 - (3 : ℂ) * ζ ^ 10 - (5 : ℂ) * ζ ^ 15 - ζ ^ 19 - (5 : ℂ) * ζ ^ 20 - ζ ^ 23 + (4 : ℂ) * ζ ^ 25 + (6 : ℂ) * ζ ^ 30 + ζ ^ 31)) * commutesA01
      + (((4 : ℂ) - (7 : ℂ) * ζ ^ 3 + (4 : ℂ) * ζ ^ 5 - (7 : ℂ) * ζ ^ 7 - (2 : ℂ) * ζ ^ 10 + (8 : ℂ) * ζ ^ 15 + (7 : ℂ) * ζ ^ 19 - (2 : ℂ) * ζ ^ 20 + (7 : ℂ) * ζ ^ 23 - (11 : ℂ) * ζ ^ 25 + (4 : ℂ) * ζ ^ 30 - (7 : ℂ) * ζ ^ 31)) * commutesA02
      + ((-(4 : ℂ) + (5 : ℂ) * ζ ^ 3 - (3 : ℂ) * ζ ^ 5 + (5 : ℂ) * ζ ^ 7 + (8 : ℂ) * ζ ^ 10 - (5 : ℂ) * ζ ^ 15 - (5 : ℂ) * ζ ^ 19 - (4 : ℂ) * ζ ^ 20 - (5 : ℂ) * ζ ^ 23 + (2 : ℂ) * ζ ^ 25 + (2 : ℂ) * ζ ^ 30 + (5 : ℂ) * ζ ^ 31)) * commutesA12
      - (
        ((-((7 / 4) : ℂ) + ((17 / 4) : ℂ) * ζ ^ 3 + ((7 / 4) : ℂ) * ζ ^ 4 - ((15 / 4) : ℂ) * ζ ^ 5 - ((5 / 4) : ℂ) * ζ ^ 6 - ((3 / 4) : ℂ) * ζ ^ 8 + ((15 / 4) : ℂ) * ζ ^ 9 + ((5 / 2) : ℂ) * ζ ^ 10 - ((21 / 4) : ℂ) * ζ ^ 13 - ((15 / 4) : ℂ) * ζ ^ 14 + ((17 / 2) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 18 - ((17 / 2) : ℂ) * ζ ^ 19 + ((3 / 4) : ℂ) * ζ ^ 20 + ((5 / 4) : ℂ) * ζ ^ 22 + ((21 / 4) : ℂ) * ζ ^ 23 - ((3 / 4) : ℂ) * ζ ^ 24 - ((25 / 4) : ℂ) * ζ ^ 25 + ((5 / 4) : ℂ) * ζ ^ 26 + (2 : ℂ) * ζ ^ 28 + ((25 / 4) : ℂ) * ζ ^ 29 - ((5 / 4) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((-(2 : ℂ) + ((31 / 4) : ℂ) * ζ ^ 3 + (2 : ℂ) * ζ ^ 4 - (2 : ℂ) * ζ ^ 5 + ((13 / 4) : ℂ) * ζ ^ 6 - (2 : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 9 + ((51 / 4) : ℂ) * ζ ^ 10 - (3 : ℂ) * ζ ^ 13 - ((19 / 2) : ℂ) * ζ ^ 14 + ((5 / 2) : ℂ) * ζ ^ 15 + ((15 / 4) : ℂ) * ζ ^ 18 - ((5 / 2) : ℂ) * ζ ^ 19 - ((51 / 4) : ℂ) * ζ ^ 20 - ((13 / 4) : ℂ) * ζ ^ 22 - ((3 / 2) : ℂ) * ζ ^ 23 + ((51 / 4) : ℂ) * ζ ^ 24 - ((15 / 4) : ℂ) * ζ ^ 25 - ((13 / 4) : ℂ) * ζ ^ 26 - ((11 / 4) : ℂ) * ζ ^ 28 + ((15 / 4) : ℂ) * ζ ^ 29 + ((13 / 4) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((-(1 : ℂ) + ζ ^ 3 + ζ ^ 4 - ((9 / 4) : ℂ) * ζ ^ 5 + ((5 / 4) : ℂ) * ζ ^ 6 - ((5 / 4) : ℂ) * ζ ^ 8 + ((9 / 4) : ℂ) * ζ ^ 9 + (3 : ℂ) * ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 13 - ((7 / 4) : ℂ) * ζ ^ 14 + ((9 / 4) : ℂ) * ζ ^ 15 + ((1 / 2) : ℂ) * ζ ^ 18 - ((9 / 4) : ℂ) * ζ ^ 19 - ((3 / 4) : ℂ) * ζ ^ 20 - ((5 / 4) : ℂ) * ζ ^ 22 + ((3 / 4) : ℂ) * ζ ^ 23 + ((3 / 4) : ℂ) * ζ ^ 24 + ((1 / 4) : ℂ) * ζ ^ 25 - ((5 / 4) : ℂ) * ζ ^ 26 - ((1 / 4) : ℂ) * ζ ^ 29 + ((5 / 4) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((((3 / 4) : ℂ) - ζ ^ 3 - ((3 / 4) : ℂ) * ζ ^ 4 + (3 : ℂ) * ζ ^ 5 - ((7 / 4) : ℂ) * ζ ^ 6 + ((3 / 2) : ℂ) * ζ ^ 8 - (3 : ℂ) * ζ ^ 9 - ((5 / 2) : ℂ) * ζ ^ 10 + ((3 / 4) : ℂ) * ζ ^ 13 + ((3 / 4) : ℂ) * ζ ^ 14 - ((15 / 4) : ℂ) * ζ ^ 15 + ((15 / 4) : ℂ) * ζ ^ 19 + ((3 / 4) : ℂ) * ζ ^ 20 + ((7 / 4) : ℂ) * ζ ^ 22 - ((5 / 2) : ℂ) * ζ ^ 23 - ((3 / 4) : ℂ) * ζ ^ 24 + ((3 / 2) : ℂ) * ζ ^ 25 + ((7 / 4) : ℂ) * ζ ^ 26 - (2 : ℂ) * ζ ^ 28 - ((3 / 2) : ℂ) * ζ ^ 29 - ((7 / 4) : ℂ) * ζ ^ 30)) * Y 1 1
        + (((1 : ℂ) - ((13 / 4) : ℂ) * ζ ^ 3 - ζ ^ 4 + ((3 / 4) : ℂ) * ζ ^ 5 + (3 : ℂ) * ζ ^ 6 - ((3 / 4) : ℂ) * ζ ^ 8 - ((3 / 4) : ℂ) * ζ ^ 9 + ((9 / 2) : ℂ) * ζ ^ 13 + (3 : ℂ) * ζ ^ 14 - ((19 / 4) : ℂ) * ζ ^ 15 - ((1 / 4) : ℂ) * ζ ^ 18 + ((19 / 4) : ℂ) * ζ ^ 19 - ((3 / 2) : ℂ) * ζ ^ 20 - (3 : ℂ) * ζ ^ 22 - ((11 / 4) : ℂ) * ζ ^ 23 + ((3 / 2) : ℂ) * ζ ^ 24 + ((19 / 4) : ℂ) * ζ ^ 25 - (3 : ℂ) * ζ ^ 26 - ((19 / 4) : ℂ) * ζ ^ 29 + (3 : ℂ) * ζ ^ 30)) * Y 2 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row15_reducedY10
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow15TransformedGeneratorA =
        alternatingSixAmbientRow15TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow15GeneratorBDiagonal =
        alternatingSixAmbientRow15GeneratorBDiagonal * Y) :
    Y 1 0 = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA00
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA00
  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
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
      alternatingSixAmbientRow15TransformedGeneratorA,
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
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
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
    ((((5708 / 2089) : ℂ) + ((7549 / 2089) : ℂ) * ζ ^ 3 - ((5976 / 2089) : ℂ) * ζ ^ 5 + ((7549 / 2089) : ℂ) * ζ ^ 7 - ((11385 / 2089) : ℂ) * ζ ^ 10 - ((6458 / 2089) : ℂ) * ζ ^ 15 - ((7549 / 2089) : ℂ) * ζ ^ 19 + ((8291 / 2089) : ℂ) * ζ ^ 20 - ((7549 / 2089) : ℂ) * ζ ^ 23 + ((8487 / 2089) : ℂ) * ζ ^ 25 + ((2757 / 2089) : ℂ) * ζ ^ 30 + ((7549 / 2089) : ℂ) * ζ ^ 31)) * commutesA00
      + ((-((7935 / 2089) : ℂ) - ((14800 / 2089) : ℂ) * ζ ^ 3 + ((9243 / 2089) : ℂ) * ζ ^ 5 - ((14800 / 2089) : ℂ) * ζ ^ 7 + ((12289 / 2089) : ℂ) * ζ ^ 10 + ((14651 / 2089) : ℂ) * ζ ^ 15 + ((14800 / 2089) : ℂ) * ζ ^ 19 - ((5295 / 2089) : ℂ) * ζ ^ 20 + ((14800 / 2089) : ℂ) * ζ ^ 23 - ((17289 / 2089) : ℂ) * ζ ^ 25 - ((1826 / 2089) : ℂ) * ζ ^ 30 - ((14800 / 2089) : ℂ) * ζ ^ 31)) * commutesA01
      + ((-(5 : ℂ) + (10 : ℂ) * ζ ^ 20 - (9 : ℂ) * ζ ^ 30)) * commutesA02
      + (((3 : ℂ) + (2 : ℂ) * ζ ^ 3 - (6 : ℂ) * ζ ^ 5 + (2 : ℂ) * ζ ^ 7 - (3 : ℂ) * ζ ^ 10 + (6 : ℂ) * ζ ^ 15 - (2 : ℂ) * ζ ^ 19 - ζ ^ 20 - (2 : ℂ) * ζ ^ 23 - (2 : ℂ) * ζ ^ 25 + (2 : ℂ) * ζ ^ 30 + (2 : ℂ) * ζ ^ 31)) * commutesA12
      - (
        ((((7935 / 8356) : ℂ) - ((11515 / 8356) : ℂ) * ζ ^ 3 - ((7935 / 8356) : ℂ) * ζ ^ 4 + ((6627 / 8356) : ℂ) * ζ ^ 5 - ((7400 / 2089) : ℂ) * ζ ^ 6 + ((56021 / 8356) : ℂ) * ζ ^ 8 - ((6627 / 8356) : ℂ) * ζ ^ 9 - ((76245 / 8356) : ℂ) * ζ ^ 10 + ((1605 / 8356) : ℂ) * ζ ^ 13 + ((46645 / 8356) : ℂ) * ζ ^ 14 - ((42703 / 8356) : ℂ) * ζ ^ 15 - ((46943 / 8356) : ℂ) * ζ ^ 18 + ((42703 / 8356) : ℂ) * ζ ^ 19 + ((64527 / 8356) : ℂ) * ζ ^ 20 + ((7400 / 2089) : ℂ) * ζ ^ 22 - ((17603 / 8356) : ℂ) * ζ ^ 23 - ((64527 / 8356) : ℂ) * ζ ^ 24 + ((52053 / 8356) : ℂ) * ζ ^ 25 + ((7400 / 2089) : ℂ) * ζ ^ 26 + ((15149 / 8356) : ℂ) * ζ ^ 28 - ((52053 / 8356) : ℂ) * ζ ^ 29 - ((7400 / 2089) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((971 / 8356) : ℂ) - ((22067 / 8356) : ℂ) * ζ ^ 3 - ((971 / 8356) : ℂ) * ζ ^ 4 - ((895 / 4178) : ℂ) * ζ ^ 5 - ((22200 / 2089) : ℂ) * ζ ^ 6 + ((19620 / 2089) : ℂ) * ζ ^ 8 + ((895 / 4178) : ℂ) * ζ ^ 9 - ((82363 / 4178) : ℂ) * ζ ^ 10 - ((8577 / 4178) : ℂ) * ζ ^ 13 + ((37963 / 4178) : ℂ) * ζ ^ 14 + ((71527 / 8356) : ℂ) * ζ ^ 15 + ((6139 / 4178) : ℂ) * ζ ^ 18 - ((71527 / 8356) : ℂ) * ζ ^ 19 + ((38979 / 2089) : ℂ) * ζ ^ 20 + ((22200 / 2089) : ℂ) * ζ ^ 22 + ((48467 / 8356) : ℂ) * ζ ^ 23 - ((38979 / 2089) : ℂ) * ζ ^ 24 - ((29897 / 4178) : ℂ) * ζ ^ 25 + ((22200 / 2089) : ℂ) * ζ ^ 26 - ((29367 / 8356) : ℂ) * ζ ^ 28 + ((29897 / 4178) : ℂ) * ζ ^ 29 - ((22200 / 2089) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((-((662 / 2089) : ℂ) + ((600 / 2089) : ℂ) * ζ ^ 3 + ((662 / 2089) : ℂ) * ζ ^ 4 + ((1360 / 2089) : ℂ) * ζ ^ 5 - ((2730 / 2089) : ℂ) * ζ ^ 6 + ((2967 / 2089) : ℂ) * ζ ^ 8 - ((1360 / 2089) : ℂ) * ζ ^ 9 - ((45673 / 8356) : ℂ) * ζ ^ 10 + ((6845 / 8356) : ℂ) * ζ ^ 13 + ((34753 / 8356) : ℂ) * ζ ^ 14 - ((8609 / 8356) : ℂ) * ζ ^ 15 - ((16045 / 8356) : ℂ) * ζ ^ 18 + ((8609 / 8356) : ℂ) * ζ ^ 19 + ((23187 / 8356) : ℂ) * ζ ^ 20 + ((2730 / 2089) : ℂ) * ζ ^ 22 - ((19731 / 8356) : ℂ) * ζ ^ 23 - ((23187 / 8356) : ℂ) * ζ ^ 24 + ((5153 / 2089) : ℂ) * ζ ^ 25 + ((2730 / 2089) : ℂ) * ζ ^ 26 - ((2423 / 2089) : ℂ) * ζ ^ 28 - ((5153 / 2089) : ℂ) * ζ ^ 29 - ((2730 / 2089) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((-((417 / 2089) : ℂ) - ((1019 / 8356) : ℂ) * ζ ^ 3 + ((417 / 2089) : ℂ) * ζ ^ 4 - ((19161 / 8356) : ℂ) * ζ ^ 5 + ((12711 / 4178) : ℂ) * ζ ^ 6 - ((9305 / 2089) : ℂ) * ζ ^ 8 + ((19161 / 8356) : ℂ) * ζ ^ 9 + ((59533 / 8356) : ℂ) * ζ ^ 10 - ((6025 / 4178) : ℂ) * ζ ^ 13 - ((34111 / 8356) : ℂ) * ζ ^ 14 + ((38525 / 8356) : ℂ) * ζ ^ 15 + ((13519 / 8356) : ℂ) * ζ ^ 18 - ((38525 / 8356) : ℂ) * ζ ^ 19 - ((10387 / 2089) : ℂ) * ζ ^ 20 - ((12711 / 4178) : ℂ) * ζ ^ 22 + ((7012 / 2089) : ℂ) * ζ ^ 23 + ((10387 / 2089) : ℂ) * ζ ^ 24 - ((18715 / 4178) : ℂ) * ζ ^ 25 - ((12711 / 4178) : ℂ) * ζ ^ 26 + ((3002 / 2089) : ℂ) * ζ ^ 28 + ((18715 / 4178) : ℂ) * ζ ^ 29 + ((12711 / 4178) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((3 / 4) : ℂ) + ((3 / 2) : ℂ) * ζ ^ 3 + ((3 / 4) : ℂ) * ζ ^ 4 + ((3 / 2) : ℂ) * ζ ^ 5 + ((1 / 2) : ℂ) * ζ ^ 6 - ((9 / 4) : ℂ) * ζ ^ 8 - ((3 / 2) : ℂ) * ζ ^ 9 + (2 : ℂ) * ζ ^ 10 + ((5 / 4) : ℂ) * ζ ^ 13 - ((3 / 2) : ℂ) * ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 15 + (4 : ℂ) * ζ ^ 18 - ((1 / 2) : ℂ) * ζ ^ 19 - ((11 / 4) : ℂ) * ζ ^ 20 - ((1 / 2) : ℂ) * ζ ^ 22 - ((5 / 4) : ℂ) * ζ ^ 23 + ((11 / 4) : ℂ) * ζ ^ 24 - ((7 / 4) : ℂ) * ζ ^ 25 - ((1 / 2) : ℂ) * ζ ^ 26 - ((13 / 4) : ℂ) * ζ ^ 28 + ((7 / 4) : ℂ) * ζ ^ 29 + ((1 / 2) : ℂ) * ζ ^ 30)) * Y 2 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row15_reducedY11
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow15TransformedGeneratorA =
        alternatingSixAmbientRow15TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow15GeneratorBDiagonal =
        alternatingSixAmbientRow15GeneratorBDiagonal * Y) :
    Y 1 1 = Y 5 5 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA00
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA00
  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
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
      alternatingSixAmbientRow15TransformedGeneratorA,
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
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA05
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY15,
      hY25,
      hY35] at commutesA05
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
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
  have commutesA15 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA15
  simp only [Fin.sum_univ_succ] at commutesA15
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA15
  simp only [
      hY05,
      hY12,
      hY13,
      hY14,
      hY15,
      hY25,
      hY35] at commutesA15

  linear_combination
    ((((366647 / 152497) : ℂ) + ((168406 / 152497) : ℂ) * ζ ^ 3 + ((159271 / 152497) : ℂ) * ζ ^ 5 + ((168406 / 152497) : ℂ) * ζ ^ 7 + ((70422 / 152497) : ℂ) * ζ ^ 10 - ((682079 / 152497) : ℂ) * ζ ^ 15 - ((168406 / 152497) : ℂ) * ζ ^ 19 - ((392996 / 152497) : ℂ) * ζ ^ 20 - ((168406 / 152497) : ℂ) * ζ ^ 23 + ((420871 / 152497) : ℂ) * ζ ^ 25 + ((439057 / 152497) : ℂ) * ζ ^ 30 + ((168406 / 152497) : ℂ) * ζ ^ 31)) * commutesA00
      + ((-((907680 / 152497) : ℂ) + ((502473 / 152497) : ℂ) * ζ ^ 3 - ((643891 / 152497) : ℂ) * ζ ^ 5 + ((502473 / 152497) : ℂ) * ζ ^ 7 + ((521737 / 152497) : ℂ) * ζ ^ 10 + ((190277 / 152497) : ℂ) * ζ ^ 15 - ((502473 / 152497) : ℂ) * ζ ^ 19 + ((794329 / 152497) : ℂ) * ζ ^ 20 - ((502473 / 152497) : ℂ) * ζ ^ 23 + ((26324 / 152497) : ℂ) * ζ ^ 25 - ((1073417 / 152497) : ℂ) * ζ ^ 30 + ((502473 / 152497) : ℂ) * ζ ^ 31)) * commutesA01
      + ((((352 / 73) : ℂ) + ((712 / 73) : ℂ) * ζ ^ 3 - ((784 / 73) : ℂ) * ζ ^ 5 + ((712 / 73) : ℂ) * ζ ^ 7 - ((258 / 73) : ℂ) * ζ ^ 10 - ((290 / 73) : ℂ) * ζ ^ 15 - ((712 / 73) : ℂ) * ζ ^ 19 - ((542 / 73) : ℂ) * ζ ^ 20 - ((712 / 73) : ℂ) * ζ ^ 23 + ((590 / 73) : ℂ) * ζ ^ 25 + ((564 / 73) : ℂ) * ζ ^ 30 + ((712 / 73) : ℂ) * ζ ^ 31)) * commutesA02
      + (((3 : ℂ) * ζ ^ 3 - ζ ^ 5 + (3 : ℂ) * ζ ^ 7 + ζ ^ 10 - ζ ^ 15 - (3 : ℂ) * ζ ^ 19 + ζ ^ 20 - (3 : ℂ) * ζ ^ 23 - (3 : ℂ) * ζ ^ 30 + (3 : ℂ) * ζ ^ 31)) * commutesA05
      + ((-((466 / 73) : ℂ) - ((50 / 73) : ℂ) * ζ ^ 3 + ((288 / 73) : ℂ) * ζ ^ 5 - ((50 / 73) : ℂ) * ζ ^ 7 + ((62 / 73) : ℂ) * ζ ^ 10 - ((546 / 73) : ℂ) * ζ ^ 15 + ((50 / 73) : ℂ) * ζ ^ 19 + ((652 / 73) : ℂ) * ζ ^ 20 + ((50 / 73) : ℂ) * ζ ^ 23 + ((406 / 73) : ℂ) * ζ ^ 25 - ((526 / 73) : ℂ) * ζ ^ 30 - ((50 / 73) : ℂ) * ζ ^ 31)) * commutesA12
      + (((3 : ℂ) - ζ ^ 5 - (4 : ℂ) * ζ ^ 10 + ζ ^ 15 - (3 : ℂ) * ζ ^ 25 + ζ ^ 30)) * commutesA15
      - (
        ((((226920 / 152497) : ℂ) - ((687847 / 304994) : ℂ) * ζ ^ 3 - ((226920 / 152497) : ℂ) * ζ ^ 4 + ((1195157 / 304994) : ℂ) * ζ ^ 5 + ((1283759 / 304994) : ℂ) * ζ ^ 6 - ((705570 / 152497) : ℂ) * ζ ^ 8 - ((1195157 / 304994) : ℂ) * ζ ^ 9 + ((377984 / 152497) : ℂ) * ζ ^ 10 + ((2043891 / 304994) : ℂ) * ζ ^ 13 + ((527791 / 304994) : ℂ) * ζ ^ 14 - ((1604973 / 304994) : ℂ) * ζ ^ 15 + ((1217815 / 304994) : ℂ) * ζ ^ 18 + ((1604973 / 304994) : ℂ) * ζ ^ 19 - ((882822 / 152497) : ℂ) * ζ ^ 20 - ((1283759 / 304994) : ℂ) * ζ ^ 22 - ((737229 / 152497) : ℂ) * ζ ^ 23 + ((882822 / 152497) : ℂ) * ζ ^ 24 + ((568855 / 304994) : ℂ) * ζ ^ 25 - ((1283759 / 304994) : ℂ) * ζ ^ 26 - ((928396 / 152497) : ℂ) * ζ ^ 28 - ((568855 / 304994) : ℂ) * ζ ^ 29 + ((1283759 / 304994) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((734311 / 304994) : ℂ) - ((2109677 / 304994) : ℂ) * ζ ^ 3 - ((734311 / 304994) : ℂ) * ζ ^ 4 + ((83521 / 609988) : ℂ) * ζ ^ 5 + ((1120115 / 609988) : ℂ) * ζ ^ 6 - ((1050799 / 304994) : ℂ) * ζ ^ 8 - ((83521 / 609988) : ℂ) * ζ ^ 9 - ((4008195 / 609988) : ℂ) * ζ ^ 10 + ((1065359 / 152497) : ℂ) * ζ ^ 13 + ((2564155 / 304994) : ℂ) * ζ ^ 14 - ((4800769 / 609988) : ℂ) * ζ ^ 15 - ((5386771 / 609988) : ℂ) * ζ ^ 18 + ((4800769 / 609988) : ℂ) * ζ ^ 19 + ((4808977 / 609988) : ℂ) * ζ ^ 20 - ((1120115 / 609988) : ℂ) * ζ ^ 22 - ((3287505 / 609988) : ℂ) * ζ ^ 23 - ((4808977 / 609988) : ℂ) * ζ ^ 24 + ((1481643 / 152497) : ℂ) * ζ ^ 25 - ((1120115 / 609988) : ℂ) * ζ ^ 26 + ((1591663 / 152497) : ℂ) * ζ ^ 28 - ((1481643 / 152497) : ℂ) * ζ ^ 29 + ((1120115 / 609988) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((((286729 / 304994) : ℂ) - ((731579 / 304994) : ℂ) * ζ ^ 3 - ((286729 / 304994) : ℂ) * ζ ^ 4 + ((262310 / 152497) : ℂ) * ζ ^ 5 - ((220631 / 304994) : ℂ) * ζ ^ 6 + ((4001 / 2089) : ℂ) * ζ ^ 8 - ((262310 / 152497) : ℂ) * ζ ^ 9 - ((486801 / 304994) : ℂ) * ζ ^ 10 + ((300415 / 304994) : ℂ) * ζ ^ 13 + ((133085 / 152497) : ℂ) * ζ ^ 14 - ((973988 / 152497) : ℂ) * ζ ^ 15 - ((207355 / 152497) : ℂ) * ζ ^ 18 + ((973988 / 152497) : ℂ) * ζ ^ 19 + ((241493 / 304994) : ℂ) * ζ ^ 20 + ((220631 / 304994) : ℂ) * ζ ^ 22 - ((789763 / 304994) : ℂ) * ζ ^ 23 - ((241493 / 304994) : ℂ) * ζ ^ 24 + ((1092111 / 304994) : ℂ) * ζ ^ 25 + ((220631 / 304994) : ℂ) * ζ ^ 26 + ((175109 / 304994) : ℂ) * ζ ^ 28 - ((1092111 / 304994) : ℂ) * ζ ^ 29 - ((220631 / 304994) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((-((588317 / 152497) : ℂ) + ((1389751 / 304994) : ℂ) * ζ ^ 3 + ((588317 / 152497) : ℂ) * ζ ^ 4 - ((552665 / 152497) : ℂ) * ζ ^ 5 - ((225124 / 152497) : ℂ) * ζ ^ 6 - ((526387 / 609988) : ℂ) * ζ ^ 8 + ((552665 / 152497) : ℂ) * ζ ^ 9 + ((1126471 / 609988) : ℂ) * ζ ^ 10 - ((935252 / 152497) : ℂ) * ζ ^ 13 - ((2026967 / 609988) : ℂ) * ζ ^ 14 + ((1350849 / 152497) : ℂ) * ζ ^ 15 + ((463794 / 152497) : ℂ) * ζ ^ 18 - ((1350849 / 152497) : ℂ) * ζ ^ 19 + ((414061 / 304994) : ℂ) * ζ ^ 20 + ((225124 / 152497) : ℂ) * ζ ^ 22 + ((3164083 / 609988) : ℂ) * ζ ^ 23 - ((414061 / 304994) : ℂ) * ζ ^ 24 - ((1896017 / 609988) : ℂ) * ζ ^ 25 + ((225124 / 152497) : ℂ) * ζ ^ 26 - ((83889 / 304994) : ℂ) * ζ ^ 28 + ((1896017 / 609988) : ℂ) * ζ ^ 29 - ((225124 / 152497) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((((233 / 146) : ℂ) - ((192 / 73) : ℂ) * ζ ^ 3 - ((233 / 146) : ℂ) * ζ ^ 4 - ((72 / 73) : ℂ) * ζ ^ 5 - ((381 / 146) : ℂ) * ζ ^ 6 + ((769 / 146) : ℂ) * ζ ^ 8 + ((72 / 73) : ℂ) * ζ ^ 9 - ((645 / 146) : ℂ) * ζ ^ 10 - ((9 / 146) : ℂ) * ζ ^ 13 + ((132 / 73) : ℂ) * ζ ^ 14 - ((188 / 73) : ℂ) * ζ ^ 15 - ((577 / 73) : ℂ) * ζ ^ 18 + ((188 / 73) : ℂ) * ζ ^ 19 + ((272 / 73) : ℂ) * ζ ^ 20 + ((381 / 146) : ℂ) * ζ ^ 22 + ((171 / 146) : ℂ) * ζ ^ 23 - ((272 / 73) : ℂ) * ζ ^ 24 + ((139 / 146) : ℂ) * ζ ^ 25 + ((381 / 146) : ℂ) * ζ ^ 26 + ((404 / 73) : ℂ) * ζ ^ 28 - ((139 / 146) : ℂ) * ζ ^ 29 - ((381 / 146) : ℂ) * ζ ^ 30)) * Y 2 2
        + ((-((39 / 73) : ℂ) - ((225 / 146) : ℂ) * ζ ^ 3 + ((39 / 73) : ℂ) * ζ ^ 4 + ((285 / 292) : ℂ) * ζ ^ 5 + ((333 / 292) : ℂ) * ζ ^ 6 - ((109 / 146) : ℂ) * ζ ^ 8 - ((285 / 292) : ℂ) * ζ ^ 9 + ((681 / 292) : ℂ) * ζ ^ 10 + ((178 / 73) : ℂ) * ζ ^ 13 - ((87 / 73) : ℂ) * ζ ^ 14 - ((565 / 292) : ℂ) * ζ ^ 15 + ((23 / 292) : ℂ) * ζ ^ 18 + ((565 / 292) : ℂ) * ζ ^ 19 - ((555 / 292) : ℂ) * ζ ^ 20 - ((333 / 292) : ℂ) * ζ ^ 22 - ((355 / 292) : ℂ) * ζ ^ 23 + ((555 / 292) : ℂ) * ζ ^ 24 + ((100 / 73) : ℂ) * ζ ^ 25 - ((333 / 292) : ℂ) * ζ ^ 26 - ((3 / 73) : ℂ) * ζ ^ 28 - ((100 / 73) : ℂ) * ζ ^ 29 + ((333 / 292) : ℂ) * ζ ^ 30)) * Y 4 5
        + ((((113 / 146) : ℂ) + ((24 / 73) : ℂ) * ζ ^ 3 - ((113 / 146) : ℂ) * ζ ^ 4 + ((101 / 146) : ℂ) * ζ ^ 5 - ((9 / 73) : ℂ) * ζ ^ 6 + ((65 / 292) : ℂ) * ζ ^ 8 - ((101 / 146) : ℂ) * ζ ^ 9 + ((27 / 292) : ℂ) * ζ ^ 10 - ((37 / 73) : ℂ) * ζ ^ 13 - ((63 / 292) : ℂ) * ζ ^ 14 - ((149 / 146) : ℂ) * ζ ^ 15 + ((127 / 146) : ℂ) * ζ ^ 18 + ((149 / 146) : ℂ) * ζ ^ 19 + ((103 / 146) : ℂ) * ζ ^ 20 + ((9 / 73) : ℂ) * ζ ^ 22 - ((445 / 292) : ℂ) * ζ ^ 23 - ((103 / 146) : ℂ) * ζ ^ 24 + ((85 / 292) : ℂ) * ζ ^ 25 + ((9 / 73) : ℂ) * ζ ^ 26 + ((121 / 146) : ℂ) * ζ ^ 28 - ((85 / 292) : ℂ) * ζ ^ 29 - ((9 / 73) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row15_reducedY22
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow15TransformedGeneratorA =
        alternatingSixAmbientRow15TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow15GeneratorBDiagonal =
        alternatingSixAmbientRow15GeneratorBDiagonal * Y) :
    Y 2 2 = Y 5 5 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA00
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA00
  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
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
      alternatingSixAmbientRow15TransformedGeneratorA,
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
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA05
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY15,
      hY25,
      hY35] at commutesA05
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
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
  have commutesA15 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA15
  simp only [Fin.sum_univ_succ] at commutesA15
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA15
  simp only [
      hY05,
      hY12,
      hY13,
      hY14,
      hY15,
      hY25,
      hY35] at commutesA15

  linear_combination
    ((((173854 / 152497) : ℂ) - ((576413 / 152497) : ℂ) * ζ ^ 3 + ((655744 / 152497) : ℂ) * ζ ^ 5 - ((576413 / 152497) : ℂ) * ζ ^ 7 + ((334390 / 152497) : ℂ) * ζ ^ 10 - ((272184 / 152497) : ℂ) * ζ ^ 15 + ((576413 / 152497) : ℂ) * ζ ^ 19 - ((738140 / 152497) : ℂ) * ζ ^ 20 + ((576413 / 152497) : ℂ) * ζ ^ 23 - ((14355 / 152497) : ℂ) * ζ ^ 25 + ((253418 / 152497) : ℂ) * ζ ^ 30 - ((576413 / 152497) : ℂ) * ζ ^ 31)) * commutesA00
      + ((-((483404 / 152497) : ℂ) + ((1014860 / 152497) : ℂ) * ζ ^ 3 - ((1034441 / 152497) : ℂ) * ζ ^ 5 + ((1014860 / 152497) : ℂ) * ζ ^ 7 - ((204394 / 152497) : ℂ) * ζ ^ 10 - ((214727 / 152497) : ℂ) * ζ ^ 15 - ((1014860 / 152497) : ℂ) * ζ ^ 19 + ((1265690 / 152497) : ℂ) * ζ ^ 20 - ((1014860 / 152497) : ℂ) * ζ ^ 23 + ((573167 / 152497) : ℂ) * ζ ^ 25 - ((1086922 / 152497) : ℂ) * ζ ^ 30 + ((1014860 / 152497) : ℂ) * ζ ^ 31)) * commutesA01
      + ((((133 / 73) : ℂ) + ((566 / 73) : ℂ) * ζ ^ 3 - ((346 / 73) : ℂ) * ζ ^ 5 + ((566 / 73) : ℂ) * ζ ^ 7 - ((39 / 73) : ℂ) * ζ ^ 10 - ((728 / 73) : ℂ) * ζ ^ 15 - ((566 / 73) : ℂ) * ζ ^ 19 - ((469 / 73) : ℂ) * ζ ^ 20 - ((566 / 73) : ℂ) * ζ ^ 23 + ((736 / 73) : ℂ) * ζ ^ 25 + ((418 / 73) : ℂ) * ζ ^ 30 + ((566 / 73) : ℂ) * ζ ^ 31)) * commutesA02
      + (((3 : ℂ) * ζ ^ 3 - ζ ^ 5 + (3 : ℂ) * ζ ^ 7 + ζ ^ 10 - ζ ^ 15 - (3 : ℂ) * ζ ^ 19 + ζ ^ 20 - (3 : ℂ) * ζ ^ 23 - (3 : ℂ) * ζ ^ 30 + (3 : ℂ) * ζ ^ 31)) * commutesA05
      + ((-((28 / 73) : ℂ) - ((196 / 73) : ℂ) * ζ ^ 3 + ((580 / 73) : ℂ) * ζ ^ 5 - ((196 / 73) : ℂ) * ζ ^ 7 - ((449 / 73) : ℂ) * ζ ^ 10 - ((254 / 73) : ℂ) * ζ ^ 15 + ((196 / 73) : ℂ) * ζ ^ 19 + ((433 / 73) : ℂ) * ζ ^ 20 + ((196 / 73) : ℂ) * ζ ^ 23 - ((32 / 73) : ℂ) * ζ ^ 25 - ((15 / 73) : ℂ) * ζ ^ 30 - ((196 / 73) : ℂ) * ζ ^ 31)) * commutesA12
      + (((3 : ℂ) - ζ ^ 5 - (4 : ℂ) * ζ ^ 10 + ζ ^ 15 - (3 : ℂ) * ζ ^ 25 + ζ ^ 30)) * commutesA15
      - (
        ((((120851 / 152497) : ℂ) - ((374255 / 152497) : ℂ) * ζ ^ 3 - ((120851 / 152497) : ℂ) * ζ ^ 4 + ((483078 / 152497) : ℂ) * ζ ^ 5 + ((1643649 / 304994) : ℂ) * ζ ^ 6 - ((1034362 / 152497) : ℂ) * ζ ^ 8 - ((483078 / 152497) : ℂ) * ζ ^ 9 + ((4587499 / 609988) : ℂ) * ζ ^ 10 + ((3659783 / 609988) : ℂ) * ζ ^ 13 - ((1300201 / 609988) : ℂ) * ζ ^ 14 - ((2712597 / 609988) : ℂ) * ζ ^ 15 + ((3481209 / 609988) : ℂ) * ζ ^ 18 + ((2712597 / 609988) : ℂ) * ζ ^ 19 - ((5469365 / 609988) : ℂ) * ζ ^ 20 - ((1643649 / 304994) : ℂ) * ζ ^ 22 - ((1868735 / 609988) : ℂ) * ζ ^ 23 + ((5469365 / 609988) : ℂ) * ζ ^ 24 + ((69973 / 304994) : ℂ) * ζ ^ 25 - ((1643649 / 304994) : ℂ) * ζ ^ 26 - ((858900 / 152497) : ℂ) * ζ ^ 28 - ((69973 / 304994) : ℂ) * ζ ^ 29 + ((1643649 / 304994) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((625545 / 609988) : ℂ) - ((3010839 / 609988) : ℂ) * ζ ^ 3 - ((625545 / 609988) : ℂ) * ζ ^ 4 + ((667845 / 304994) : ℂ) * ζ ^ 5 + ((4499431 / 609988) : ℂ) * ζ ^ 6 - ((1620728 / 152497) : ℂ) * ζ ^ 8 - ((667845 / 304994) : ℂ) * ζ ^ 9 + ((901408 / 152497) : ℂ) * ζ ^ 10 + ((5055895 / 609988) : ℂ) * ζ ^ 13 + ((893799 / 609988) : ℂ) * ζ ^ 14 - ((8409305 / 609988) : ℂ) * ζ ^ 15 - ((3034565 / 609988) : ℂ) * ζ ^ 18 + ((8409305 / 609988) : ℂ) * ζ ^ 19 - ((2228953 / 609988) : ℂ) * ζ ^ 20 - ((4499431 / 609988) : ℂ) * ζ ^ 22 - ((2317579 / 304994) : ℂ) * ζ ^ 23 + ((2228953 / 609988) : ℂ) * ζ ^ 24 + ((2148644 / 152497) : ℂ) * ζ ^ 25 - ((4499431 / 609988) : ℂ) * ζ ^ 26 + ((1402885 / 152497) : ℂ) * ζ ^ 28 - ((2148644 / 152497) : ℂ) * ζ ^ 29 + ((4499431 / 609988) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((((380665 / 609988) : ℂ) - ((907409 / 609988) : ℂ) * ζ ^ 3 - ((380665 / 609988) : ℂ) * ζ ^ 4 + ((1160127 / 609988) : ℂ) * ζ ^ 5 + ((371691 / 304994) : ℂ) * ζ ^ 6 - ((12289 / 8356) : ℂ) * ζ ^ 8 - ((1160127 / 609988) : ℂ) * ζ ^ 9 + ((926771 / 304994) : ℂ) * ζ ^ 10 + ((151485 / 152497) : ℂ) * ζ ^ 13 - ((277540 / 152497) : ℂ) * ζ ^ 14 - ((620084 / 152497) : ℂ) * ζ ^ 15 + ((370732 / 152497) : ℂ) * ζ ^ 18 + ((620084 / 152497) : ℂ) * ζ ^ 19 - ((609249 / 304994) : ℂ) * ζ ^ 20 - ((371691 / 304994) : ℂ) * ζ ^ 22 - ((168983 / 152497) : ℂ) * ζ ^ 23 + ((609249 / 304994) : ℂ) * ζ ^ 24 - ((1049167 / 609988) : ℂ) * ζ ^ 25 - ((371691 / 304994) : ℂ) * ζ ^ 26 - ((345983 / 609988) : ℂ) * ζ ^ 28 + ((1049167 / 609988) : ℂ) * ζ ^ 29 + ((371691 / 304994) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((-((202011 / 304994) : ℂ) + ((1223361 / 609988) : ℂ) * ζ ^ 3 + ((202011 / 304994) : ℂ) * ζ ^ 4 - ((571335 / 304994) : ℂ) * ζ ^ 5 - ((405069 / 152497) : ℂ) * ζ ^ 6 + ((2618745 / 609988) : ℂ) * ζ ^ 8 + ((571335 / 304994) : ℂ) * ζ ^ 9 - ((3931553 / 609988) : ℂ) * ζ ^ 10 - ((873057 / 609988) : ℂ) * ζ ^ 13 + ((2311277 / 609988) : ℂ) * ζ ^ 14 + ((1856107 / 609988) : ℂ) * ζ ^ 15 - ((1348917 / 304994) : ℂ) * ζ ^ 18 - ((1856107 / 609988) : ℂ) * ζ ^ 19 + ((3681181 / 609988) : ℂ) * ζ ^ 20 + ((405069 / 152497) : ℂ) * ζ ^ 22 + ((126969 / 304994) : ℂ) * ζ ^ 23 - ((3681181 / 609988) : ℂ) * ζ ^ 24 + ((389607 / 304994) : ℂ) * ζ ^ 25 + ((405069 / 152497) : ℂ) * ζ ^ 26 + ((997095 / 304994) : ℂ) * ζ ^ 28 - ((389607 / 304994) : ℂ) * ζ ^ 29 - ((405069 / 152497) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((66 / 73) : ℂ) + ((35 / 292) : ℂ) * ζ ^ 3 + ((66 / 73) : ℂ) * ζ ^ 4 - ((145 / 73) : ℂ) * ζ ^ 5 - ((381 / 146) : ℂ) * ζ ^ 6 + ((331 / 146) : ℂ) * ζ ^ 8 + ((145 / 73) : ℂ) * ζ ^ 9 - ((341 / 292) : ℂ) * ζ ^ 10 - ((593 / 146) : ℂ) * ζ ^ 13 - ((421 / 292) : ℂ) * ζ ^ 14 + ((177 / 73) : ℂ) * ζ ^ 15 - ((629 / 292) : ℂ) * ζ ^ 18 - ((177 / 73) : ℂ) * ζ ^ 19 + ((325 / 146) : ℂ) * ζ ^ 20 + ((381 / 146) : ℂ) * ζ ^ 22 + ((609 / 146) : ℂ) * ζ ^ 23 - ((325 / 146) : ℂ) * ζ ^ 24 - ((525 / 292) : ℂ) * ζ ^ 25 + ((381 / 146) : ℂ) * ζ ^ 26 + ((112 / 73) : ℂ) * ζ ^ 28 + ((525 / 292) : ℂ) * ζ ^ 29 - ((381 / 146) : ℂ) * ζ ^ 30)) * Y 2 2
        + ((-((39 / 73) : ℂ) - ((225 / 146) : ℂ) * ζ ^ 3 + ((39 / 73) : ℂ) * ζ ^ 4 + ((285 / 292) : ℂ) * ζ ^ 5 + ((333 / 292) : ℂ) * ζ ^ 6 - ((109 / 146) : ℂ) * ζ ^ 8 - ((285 / 292) : ℂ) * ζ ^ 9 + ((681 / 292) : ℂ) * ζ ^ 10 + ((178 / 73) : ℂ) * ζ ^ 13 - ((87 / 73) : ℂ) * ζ ^ 14 - ((565 / 292) : ℂ) * ζ ^ 15 + ((23 / 292) : ℂ) * ζ ^ 18 + ((565 / 292) : ℂ) * ζ ^ 19 - ((555 / 292) : ℂ) * ζ ^ 20 - ((333 / 292) : ℂ) * ζ ^ 22 - ((355 / 292) : ℂ) * ζ ^ 23 + ((555 / 292) : ℂ) * ζ ^ 24 + ((100 / 73) : ℂ) * ζ ^ 25 - ((333 / 292) : ℂ) * ζ ^ 26 - ((3 / 73) : ℂ) * ζ ^ 28 - ((100 / 73) : ℂ) * ζ ^ 29 + ((333 / 292) : ℂ) * ζ ^ 30)) * Y 4 5
        + ((((113 / 146) : ℂ) + ((24 / 73) : ℂ) * ζ ^ 3 - ((113 / 146) : ℂ) * ζ ^ 4 + ((101 / 146) : ℂ) * ζ ^ 5 - ((9 / 73) : ℂ) * ζ ^ 6 + ((65 / 292) : ℂ) * ζ ^ 8 - ((101 / 146) : ℂ) * ζ ^ 9 + ((27 / 292) : ℂ) * ζ ^ 10 - ((37 / 73) : ℂ) * ζ ^ 13 - ((63 / 292) : ℂ) * ζ ^ 14 - ((149 / 146) : ℂ) * ζ ^ 15 + ((127 / 146) : ℂ) * ζ ^ 18 + ((149 / 146) : ℂ) * ζ ^ 19 + ((103 / 146) : ℂ) * ζ ^ 20 + ((9 / 73) : ℂ) * ζ ^ 22 - ((445 / 292) : ℂ) * ζ ^ 23 - ((103 / 146) : ℂ) * ζ ^ 24 + ((85 / 292) : ℂ) * ζ ^ 25 + ((9 / 73) : ℂ) * ζ ^ 26 + ((121 / 146) : ℂ) * ζ ^ 28 - ((85 / 292) : ℂ) * ζ ^ 29 - ((9 / 73) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row15_y33Coefficient_ne_zero :
    (-((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 7 + ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 + ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 4) : ℂ) * ζ ^ 31) ≠ 0 := by
  intro h
  have hunit :
      (-((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 7 + ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 + ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 4) : ℂ) * ζ ^ 31) *
          (-(2 : ℂ) + (2 : ℂ) * ζ ^ 3 + (2 : ℂ) * ζ ^ 7 + (2 : ℂ) * ζ ^ 10 - (4 : ℂ) * ζ ^ 15 - (2 : ℂ) * ζ ^ 19 + (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 23 - (2 : ℂ) * ζ ^ 25 + (2 : ℂ) * ζ ^ 31) = 1 := by
    close_cyclotomic_row15
      (-((1 / 2) : ℂ) + ((1 / 2) : ℂ) * ζ ^ 4 - ((1 / 2) : ℂ) * ζ ^ 6 - ((1 / 2) : ℂ) * ζ ^ 8 - ((3 / 2) : ℂ) * ζ ^ 10 + ζ ^ 14 + ((1 / 2) : ℂ) * ζ ^ 15 - ((1 / 2) : ℂ) * ζ ^ 19 - ((1 / 2) : ℂ) * ζ ^ 20 + ((1 / 2) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 24 + ((1 / 2) : ℂ) * ζ ^ 26 - ((1 / 2) : ℂ) * ζ ^ 30)
  rw [h, zero_mul] at hunit
  exact zero_ne_one hunit

private theorem row15_reducedY33
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow15TransformedGeneratorA =
        alternatingSixAmbientRow15TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow15GeneratorBDiagonal =
        alternatingSixAmbientRow15GeneratorBDiagonal * Y) :
    Y 3 3 = Y 5 5 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA32 :=
    congrFun (congrFun commutesA
      (3 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA32
  simp only [Fin.sum_univ_succ] at commutesA32
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA32
  simp only [
      hY02,
      hY12,
      hY30,
      hY31,
      hY32,
      hY34,
      hY35,
      hY42,
      hY52] at commutesA32

  have reducedY22 : Y 2 2 = Y 5 5 :=
    row15_reducedY22 Y commutesA commutesDiagonal

  rw [reducedY22] at commutesA32
  have hscaled :
      (-((1 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 7 + ((1 / 4) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 + ((1 / 4) : ℂ) * ζ ^ 23 - ((1 / 4) : ℂ) * ζ ^ 31) *
          (Y 3 3 - Y 5 5) = 0 := by
    linear_combination commutesA32
  rcases mul_eq_zero.mp hscaled with hcoefficient | hdifference
  · exact
      (row15_y33Coefficient_ne_zero
        hcoefficient).elim
  · exact sub_eq_zero.mp hdifference

private theorem row15_reducedY45
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow15TransformedGeneratorA =
        alternatingSixAmbientRow15TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow15GeneratorBDiagonal =
        alternatingSixAmbientRow15GeneratorBDiagonal * Y) :
    Y 4 5 = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA00
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA00
  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
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
      alternatingSixAmbientRow15TransformedGeneratorA,
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
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA05
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY15,
      hY25,
      hY35] at commutesA05
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
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
  have commutesA15 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA15
  simp only [Fin.sum_univ_succ] at commutesA15
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA15
  simp only [
      hY05,
      hY12,
      hY13,
      hY14,
      hY15,
      hY25,
      hY35] at commutesA15

  linear_combination
    ((-((294737 / 152497) : ℂ) + ((54790 / 152497) : ℂ) * ζ ^ 3 + ((322342 / 152497) : ℂ) * ζ ^ 5 + ((54790 / 152497) : ℂ) * ζ ^ 7 - ((62377 / 152497) : ℂ) * ζ ^ 10 - ((317084 / 152497) : ℂ) * ζ ^ 15 - ((54790 / 152497) : ℂ) * ζ ^ 19 + ((110015 / 152497) : ℂ) * ζ ^ 20 - ((54790 / 152497) : ℂ) * ζ ^ 23 - ((88830 / 152497) : ℂ) * ζ ^ 25 + ((95788 / 152497) : ℂ) * ζ ^ 30 + ((54790 / 152497) : ℂ) * ζ ^ 31)) * commutesA00
      + ((-((171347 / 152497) : ℂ) - ((51212 / 152497) : ℂ) * ζ ^ 3 - ((141664 / 152497) : ℂ) * ζ ^ 5 - ((51212 / 152497) : ℂ) * ζ ^ 7 + ((97626 / 152497) : ℂ) * ζ ^ 10 - ((32286 / 152497) : ℂ) * ζ ^ 15 + ((51212 / 152497) : ℂ) * ζ ^ 19 + ((402394 / 152497) : ℂ) * ζ ^ 20 + ((51212 / 152497) : ℂ) * ζ ^ 23 + ((32206 / 152497) : ℂ) * ζ ^ 25 - ((303407 / 152497) : ℂ) * ζ ^ 30 - ((51212 / 152497) : ℂ) * ζ ^ 31)) * commutesA01
      + ((-((188 / 73) : ℂ) + ((217 / 73) : ℂ) * ζ ^ 3 - ((152 / 73) : ℂ) * ζ ^ 5 + ((217 / 73) : ℂ) * ζ ^ 7 + ((312 / 73) : ℂ) * ζ ^ 10 - ((308 / 73) : ℂ) * ζ ^ 15 - ((217 / 73) : ℂ) * ζ ^ 19 - ((44 / 73) : ℂ) * ζ ^ 20 - ((217 / 73) : ℂ) * ζ ^ 23 + ((463 / 73) : ℂ) * ζ ^ 25 - ((132 / 73) : ℂ) * ζ ^ 30 + ((217 / 73) : ℂ) * ζ ^ 31)) * commutesA02
      + ((-(2 : ℂ) + ζ ^ 3 - ζ ^ 5 + ζ ^ 7 + ζ ^ 10 - ζ ^ 15 - ζ ^ 19 - ζ ^ 20 - ζ ^ 23 + (2 : ℂ) * ζ ^ 25 - ζ ^ 30 + ζ ^ 31)) * commutesA05
      + ((((224 / 73) : ℂ) - ((403 / 73) : ℂ) * ζ ^ 3 + ((251 / 73) : ℂ) * ζ ^ 5 - ((403 / 73) : ℂ) * ζ ^ 7 - ((204 / 73) : ℂ) * ζ ^ 10 + ((207 / 73) : ℂ) * ζ ^ 15 + ((403 / 73) : ℂ) * ζ ^ 19 + ((186 / 73) : ℂ) * ζ ^ 20 + ((403 / 73) : ℂ) * ζ ^ 23 - ((182 / 73) : ℂ) * ζ ^ 25 - ((172 / 73) : ℂ) * ζ ^ 30 - ((403 / 73) : ℂ) * ζ ^ 31)) * commutesA12
      + (((1 : ℂ) - (2 : ℂ) * ζ ^ 3 + ζ ^ 5 - (2 : ℂ) * ζ ^ 7 - (4 : ℂ) * ζ ^ 10 + (3 : ℂ) * ζ ^ 15 + (2 : ℂ) * ζ ^ 19 + (2 : ℂ) * ζ ^ 23 - (3 : ℂ) * ζ ^ 25 + ζ ^ 30 - (2 : ℂ) * ζ ^ 31)) * commutesA15
      - (
        ((((33473 / 609988) : ℂ) - ((665413 / 609988) : ℂ) * ζ ^ 3 - ((33473 / 609988) : ℂ) * ζ ^ 4 + ((265013 / 609988) : ℂ) * ζ ^ 5 + ((375957 / 609988) : ℂ) * ζ ^ 6 - ((414823 / 609988) : ℂ) * ζ ^ 8 - ((265013 / 609988) : ℂ) * ζ ^ 9 + ((52035 / 304994) : ℂ) * ζ ^ 10 + ((1088991 / 609988) : ℂ) * ζ ^ 13 + ((271887 / 609988) : ℂ) * ζ ^ 14 - ((671793 / 304994) : ℂ) * ζ ^ 15 - ((280119 / 609988) : ℂ) * ζ ^ 18 + ((671793 / 304994) : ℂ) * ζ ^ 19 - ((876961 / 609988) : ℂ) * ζ ^ 20 - ((375957 / 609988) : ℂ) * ζ ^ 22 - ((510565 / 609988) : ℂ) * ζ ^ 23 + ((876961 / 609988) : ℂ) * ζ ^ 24 + ((1333849 / 609988) : ℂ) * ζ ^ 25 - ((375957 / 609988) : ℂ) * ζ ^ 26 - ((115146 / 152497) : ℂ) * ζ ^ 28 - ((1333849 / 609988) : ℂ) * ζ ^ 29 + ((375957 / 609988) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((-((7357 / 4178) : ℂ) + ((245071 / 609988) : ℂ) * ζ ^ 3 + ((7357 / 4178) : ℂ) * ζ ^ 4 + ((1123351 / 609988) : ℂ) * ζ ^ 5 - ((448185 / 304994) : ℂ) * ζ ^ 6 - ((381380 / 152497) : ℂ) * ζ ^ 8 - ((1123351 / 609988) : ℂ) * ζ ^ 9 - ((52667 / 304994) : ℂ) * ζ ^ 10 + ((43989 / 304994) : ℂ) * ζ ^ 13 - ((197759 / 152497) : ℂ) * ζ ^ 14 - ((1941955 / 609988) : ℂ) * ζ ^ 15 + ((263085 / 304994) : ℂ) * ζ ^ 18 + ((1941955 / 609988) : ℂ) * ζ ^ 19 + ((915897 / 304994) : ℂ) * ζ ^ 20 + ((448185 / 304994) : ℂ) * ζ ^ 22 - ((193919 / 609988) : ℂ) * ζ ^ 23 - ((915897 / 304994) : ℂ) * ζ ^ 24 + ((410841 / 609988) : ℂ) * ζ ^ 25 + ((448185 / 304994) : ℂ) * ζ ^ 26 + ((571497 / 609988) : ℂ) * ζ ^ 28 - ((410841 / 609988) : ℂ) * ζ ^ 29 - ((448185 / 304994) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((-((56450 / 152497) : ℂ) + ((499697 / 304994) : ℂ) * ζ ^ 3 + ((56450 / 152497) : ℂ) * ζ ^ 4 - ((122991 / 609988) : ℂ) * ζ ^ 5 - ((1001583 / 609988) : ℂ) * ζ ^ 6 - ((361905 / 609988) : ℂ) * ζ ^ 8 + ((122991 / 609988) : ℂ) * ζ ^ 9 + ((5992 / 152497) : ℂ) * ζ ^ 10 - ((742873 / 609988) : ℂ) * ζ ^ 13 - ((1025551 / 609988) : ℂ) * ζ ^ 14 + ((236667 / 609988) : ℂ) * ζ ^ 15 + ((133199 / 152497) : ℂ) * ζ ^ 18 - ((236667 / 609988) : ℂ) * ζ ^ 19 - ((533791 / 609988) : ℂ) * ζ ^ 20 + ((1001583 / 609988) : ℂ) * ζ ^ 22 + ((271971 / 609988) : ℂ) * ζ ^ 23 + ((533791 / 609988) : ℂ) * ζ ^ 24 + ((52565 / 609988) : ℂ) * ζ ^ 25 + ((1001583 / 609988) : ℂ) * ζ ^ 26 + ((148625 / 304994) : ℂ) * ζ ^ 28 - ((52565 / 609988) : ℂ) * ζ ^ 29 - ((1001583 / 609988) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((((342547 / 609988) : ℂ) - ((623011 / 304994) : ℂ) * ζ ^ 3 - ((342547 / 609988) : ℂ) * ζ ^ 4 - ((8211 / 304994) : ℂ) * ζ ^ 5 + ((1215861 / 609988) : ℂ) * ζ ^ 6 + ((68049 / 609988) : ℂ) * ζ ^ 8 + ((8211 / 304994) : ℂ) * ζ ^ 9 + ((177945 / 609988) : ℂ) * ζ ^ 10 + ((1731159 / 609988) : ℂ) * ζ ^ 13 + ((259479 / 152497) : ℂ) * ζ ^ 14 - ((693189 / 609988) : ℂ) * ζ ^ 15 - ((11393 / 304994) : ℂ) * ζ ^ 18 + ((693189 / 609988) : ℂ) * ζ ^ 19 - ((810951 / 609988) : ℂ) * ζ ^ 20 - ((1215861 / 609988) : ℂ) * ζ ^ 22 - ((74355 / 609988) : ℂ) * ζ ^ 23 + ((810951 / 609988) : ℂ) * ζ ^ 24 + ((517005 / 609988) : ℂ) * ζ ^ 25 - ((1215861 / 609988) : ℂ) * ζ ^ 26 - ((114393 / 304994) : ℂ) * ζ ^ 28 - ((517005 / 609988) : ℂ) * ζ ^ 29 + ((1215861 / 609988) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((56 / 73) : ℂ) + ((815 / 292) : ℂ) * ζ ^ 3 + ((56 / 73) : ℂ) * ζ ^ 4 - ((251 / 292) : ℂ) * ζ ^ 5 - ((155 / 73) : ℂ) * ζ ^ 6 + ((179 / 292) : ℂ) * ζ ^ 8 + ((251 / 292) : ℂ) * ζ ^ 9 - ((48 / 73) : ℂ) * ζ ^ 10 - ((585 / 146) : ℂ) * ζ ^ 13 - ((107 / 73) : ℂ) * ζ ^ 14 + ((1271 / 292) : ℂ) * ζ ^ 15 - ((297 / 292) : ℂ) * ζ ^ 18 - ((1271 / 292) : ℂ) * ζ ^ 19 + ((160 / 73) : ℂ) * ζ ^ 20 + ((155 / 73) : ℂ) * ζ ^ 22 + ((695 / 292) : ℂ) * ζ ^ 23 - ((160 / 73) : ℂ) * ζ ^ 24 - ((983 / 292) : ℂ) * ζ ^ 25 + ((155 / 73) : ℂ) * ζ ^ 26 + ((53 / 73) : ℂ) * ζ ^ 28 + ((983 / 292) : ℂ) * ζ ^ 29 - ((155 / 73) : ℂ) * ζ ^ 30)) * Y 2 2
        + ((-((167 / 146) : ℂ) - ((67 / 73) : ℂ) * ζ ^ 3 + ((167 / 146) : ℂ) * ζ ^ 4 + ((93 / 292) : ℂ) * ζ ^ 5 + ((401 / 292) : ℂ) * ζ ^ 6 - ((387 / 146) : ℂ) * ζ ^ 8 - ((93 / 292) : ℂ) * ζ ^ 9 + ((951 / 292) : ℂ) * ζ ^ 10 + ((285 / 146) : ℂ) * ζ ^ 13 - ((275 / 146) : ℂ) * ζ ^ 14 - ((255 / 292) : ℂ) * ζ ^ 15 + ((109 / 292) : ℂ) * ζ ^ 18 + ((255 / 292) : ℂ) * ζ ^ 19 - ((751 / 292) : ℂ) * ζ ^ 20 - ((401 / 292) : ℂ) * ζ ^ 22 - ((231 / 292) : ℂ) * ζ ^ 23 + ((751 / 292) : ℂ) * ζ ^ 24 + ((181 / 146) : ℂ) * ζ ^ 25 - ((401 / 292) : ℂ) * ζ ^ 26 + ((10 / 73) : ℂ) * ζ ^ 28 - ((181 / 146) : ℂ) * ζ ^ 29 + ((401 / 292) : ℂ) * ζ ^ 30)) * Y 4 5
        + ((((11 / 73) : ℂ) + ((25 / 73) : ℂ) * ζ ^ 3 - ((11 / 73) : ℂ) * ζ ^ 4 + ((33 / 73) : ℂ) * ζ ^ 5 - ((71 / 146) : ℂ) * ζ ^ 6 - ((13 / 292) : ℂ) * ζ ^ 8 - ((33 / 73) : ℂ) * ζ ^ 9 + ((57 / 292) : ℂ) * ζ ^ 10 - ((45 / 73) : ℂ) * ζ ^ 13 - ((199 / 292) : ℂ) * ζ ^ 14 - ((74 / 73) : ℂ) * ζ ^ 15 + ((221 / 146) : ℂ) * ζ ^ 18 + ((74 / 73) : ℂ) * ζ ^ 19 + ((42 / 73) : ℂ) * ζ ^ 20 + ((71 / 146) : ℂ) * ζ ^ 22 - ((415 / 292) : ℂ) * ζ ^ 23 - ((42 / 73) : ℂ) * ζ ^ 24 + ((97 / 292) : ℂ) * ζ ^ 25 + ((71 / 146) : ℂ) * ζ ^ 26 + ((59 / 146) : ℂ) * ζ ^ 28 - ((97 / 292) : ℂ) * ζ ^ 29 - ((71 / 146) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row15_y44Coefficient_ne_zero :
    (((3 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 3 + ((1 / 4) : ℂ) * ζ ^ 5 - ((1 / 4) : ℂ) * ζ ^ 7 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 23 - ((3 / 4) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 31) ≠ 0 := by
  intro h
  have hunit :
      (((3 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 3 + ((1 / 4) : ℂ) * ζ ^ 5 - ((1 / 4) : ℂ) * ζ ^ 7 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 23 - ((3 / 4) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 31) *
          (((140 / 73) : ℂ) + ((42 / 73) : ℂ) * ζ ^ 3 - ((166 / 73) : ℂ) * ζ ^ 5 + ((42 / 73) : ℂ) * ζ ^ 7 - ((18 / 73) : ℂ) * ζ ^ 10 - ((102 / 73) : ℂ) * ζ ^ 15 - ((42 / 73) : ℂ) * ζ ^ 19 + ((98 / 73) : ℂ) * ζ ^ 20 - ((42 / 73) : ℂ) * ζ ^ 23 + ((132 / 73) : ℂ) * ζ ^ 25 + ((2 / 73) : ℂ) * ζ ^ 30 + ((42 / 73) : ℂ) * ζ ^ 31) = 1 := by
    close_cyclotomic_row15
      (((32 / 73) : ℂ) - ((7 / 146) : ℂ) * ζ ^ 3 - ((32 / 73) : ℂ) * ζ ^ 4 - ((179 / 146) : ℂ) * ζ ^ 5 - ((21 / 146) : ℂ) * ζ ^ 6 + ((84 / 73) : ℂ) * ζ ^ 8 + ((179 / 146) : ℂ) * ζ ^ 9 - ((271 / 146) : ℂ) * ζ ^ 10 - ((106 / 73) : ℂ) * ζ ^ 13 + ((125 / 73) : ℂ) * ζ ^ 14 + ((67 / 146) : ℂ) * ζ ^ 15 - ((199 / 146) : ℂ) * ζ ^ 18 - ((67 / 146) : ℂ) * ζ ^ 19 + ((129 / 146) : ℂ) * ζ ^ 20 + ((21 / 146) : ℂ) * ζ ^ 22 - ((3 / 146) : ℂ) * ζ ^ 23 - ((129 / 146) : ℂ) * ζ ^ 24 + ((1 / 146) : ℂ) * ζ ^ 25 + ((21 / 146) : ℂ) * ζ ^ 26 - ((1 / 146) : ℂ) * ζ ^ 29 - ((21 / 146) : ℂ) * ζ ^ 30)
  rw [h, zero_mul] at hunit
  exact zero_ne_one hunit

private theorem row15_reducedY44
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow15TransformedGeneratorA =
        alternatingSixAmbientRow15TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow15GeneratorBDiagonal =
        alternatingSixAmbientRow15GeneratorBDiagonal * Y) :
    Y 4 4 = Y 5 5 := by
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 3 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 0 (by decide)

  have commutesA40 :=
    congrFun (congrFun commutesA
      (4 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA40
  simp only [Fin.sum_univ_succ] at commutesA40
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA40
  simp only [
      hY20,
      hY30,
      hY40,
      hY41,
      hY42,
      hY43,
      hY50] at commutesA40

  have reducedY00 : Y 0 0 = Y 5 5 :=
    row15_reducedY00 Y commutesA commutesDiagonal
  have reducedY10 : Y 1 0 = 0 :=
    row15_reducedY10 Y commutesA commutesDiagonal
  have reducedY45 : Y 4 5 = 0 :=
    row15_reducedY45 Y commutesA commutesDiagonal

  rw [reducedY00, reducedY10, reducedY45] at commutesA40
  have hscaled :
      (((3 / 4) : ℂ) - ((1 / 4) : ℂ) * ζ ^ 3 + ((1 / 4) : ℂ) * ζ ^ 5 - ((1 / 4) : ℂ) * ζ ^ 7 - ((1 / 2) : ℂ) * ζ ^ 10 + ((1 / 4) : ℂ) * ζ ^ 15 + ((1 / 4) : ℂ) * ζ ^ 19 - ((1 / 4) : ℂ) * ζ ^ 20 + ((1 / 4) : ℂ) * ζ ^ 23 - ((3 / 4) : ℂ) * ζ ^ 25 - ((1 / 4) : ℂ) * ζ ^ 31) *
          (Y 4 4 - Y 5 5) = 0 := by
    linear_combination commutesA40
  rcases mul_eq_zero.mp hscaled with hcoefficient | hdifference
  · exact
      (row15_y44Coefficient_ne_zero
        hcoefficient).elim
  · exact sub_eq_zero.mp hdifference

private theorem row15_reducedY54
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow15TransformedGeneratorA =
        alternatingSixAmbientRow15TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow15GeneratorBDiagonal =
        alternatingSixAmbientRow15GeneratorBDiagonal * Y) :
    Y 5 4 = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA00
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY20,
      hY30,
      hY40,
      hY50] at commutesA00
  have commutesA01 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (1 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA01
  simp only [Fin.sum_univ_succ] at commutesA01
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
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
      alternatingSixAmbientRow15TransformedGeneratorA,
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
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA04
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY14,
      hY24,
      hY34] at commutesA04
  have commutesA12 :=
    congrFun (congrFun commutesA
      (1 : Fin 6))
      (2 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA12
  simp only [Fin.sum_univ_succ] at commutesA12
  simp [
      alternatingSixAmbientRow15TransformedGeneratorA,
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
      alternatingSixAmbientRow15TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA14
  simp only [
      hY04,
      hY12,
      hY13,
      hY14,
      hY15,
      hY24,
      hY34] at commutesA14

  linear_combination
    ((((2427903 / 152497) : ℂ) - ((12073 / 152497) : ℂ) * ζ ^ 3 + ((1071483 / 152497) : ℂ) * ζ ^ 5 - ((12073 / 152497) : ℂ) * ζ ^ 7 - ((1972983 / 152497) : ℂ) * ζ ^ 10 - ((1768795 / 152497) : ℂ) * ζ ^ 15 + ((12073 / 152497) : ℂ) * ζ ^ 19 - ((1460689 / 152497) : ℂ) * ζ ^ 20 + ((12073 / 152497) : ℂ) * ζ ^ 23 + ((925844 / 152497) : ℂ) * ζ ^ 25 + ((2347292 / 152497) : ℂ) * ζ ^ 30 - ((12073 / 152497) : ℂ) * ζ ^ 31)) * commutesA00
      + ((-((3272681 / 152497) : ℂ) + ((245811 / 152497) : ℂ) * ζ ^ 3 - ((2226586 / 152497) : ℂ) * ζ ^ 5 + ((245811 / 152497) : ℂ) * ζ ^ 7 + ((2227322 / 152497) : ℂ) * ζ ^ 10 + ((3356554 / 152497) : ℂ) * ζ ^ 15 - ((245811 / 152497) : ℂ) * ζ ^ 19 + ((2684796 / 152497) : ℂ) * ζ ^ 20 - ((245811 / 152497) : ℂ) * ζ ^ 23 - ((1765463 / 152497) : ℂ) * ζ ^ 25 - ((3425665 / 152497) : ℂ) * ζ ^ 30 + ((245811 / 152497) : ℂ) * ζ ^ 31)) * commutesA01
      + ((((701 / 73) : ℂ) + ((454 / 73) : ℂ) * ζ ^ 3 - ((98 / 73) : ℂ) * ζ ^ 5 + ((454 / 73) : ℂ) * ζ ^ 7 - ((1328 / 73) : ℂ) * ζ ^ 10 - ((602 / 73) : ℂ) * ζ ^ 15 - ((454 / 73) : ℂ) * ζ ^ 19 + ((1082 / 73) : ℂ) * ζ ^ 20 - ((454 / 73) : ℂ) * ζ ^ 23 + ((676 / 73) : ℂ) * ζ ^ 25 - ((185 / 73) : ℂ) * ζ ^ 30 + ((454 / 73) : ℂ) * ζ ^ 31)) * commutesA02
      + ((-(3 : ℂ) * ζ ^ 3 + ζ ^ 5 - (3 : ℂ) * ζ ^ 7 - ζ ^ 10 + ζ ^ 15 + (3 : ℂ) * ζ ^ 19 - ζ ^ 20 + (3 : ℂ) * ζ ^ 23 + (3 : ℂ) * ζ ^ 30 - (3 : ℂ) * ζ ^ 31)) * commutesA04
      + ((((763 / 73) : ℂ) + ((1180 / 73) : ℂ) * ζ ^ 3 - ((1132 / 73) : ℂ) * ζ ^ 5 + ((1180 / 73) : ℂ) * ζ ^ 7 - ((631 / 73) : ℂ) * ζ ^ 10 - ((196 / 73) : ℂ) * ζ ^ 15 - ((1180 / 73) : ℂ) * ζ ^ 19 - ((247 / 73) : ℂ) * ζ ^ 20 - ((1180 / 73) : ℂ) * ζ ^ 23 + ((726 / 73) : ℂ) * ζ ^ 25 + ((500 / 73) : ℂ) * ζ ^ 30 + ((1180 / 73) : ℂ) * ζ ^ 31)) * commutesA12
      + ((-(3 : ℂ) + ζ ^ 5 + (4 : ℂ) * ζ ^ 10 - ζ ^ 15 + (3 : ℂ) * ζ ^ 25 - ζ ^ 30)) * commutesA14
      - (
        ((((3272681 / 609988) : ℂ) - ((5358119 / 609988) : ℂ) * ζ ^ 3 - ((3272681 / 609988) : ℂ) * ζ ^ 4 + ((8782393 / 609988) : ℂ) * ζ ^ 5 + ((2135665 / 609988) : ℂ) * ζ ^ 6 - ((1154629 / 304994) : ℂ) * ζ ^ 8 - ((8782393 / 609988) : ℂ) * ζ ^ 9 - ((531861 / 152497) : ℂ) * ζ ^ 10 + ((5317425 / 304994) : ℂ) * ζ ^ 13 + ((4263109 / 609988) : ℂ) * ζ ^ 14 - ((16030671 / 609988) : ℂ) * ζ ^ 15 + ((3204835 / 609988) : ℂ) * ζ ^ 18 + ((16030671 / 609988) : ℂ) * ζ ^ 19 - ((2016031 / 304994) : ℂ) * ζ ^ 20 - ((2135665 / 609988) : ℂ) * ζ ^ 22 - ((4103951 / 304994) : ℂ) * ζ ^ 23 + ((2016031 / 304994) : ℂ) * ζ ^ 24 + ((4113637 / 304994) : ℂ) * ζ ^ 25 - ((2135665 / 609988) : ℂ) * ζ ^ 26 - ((6627807 / 609988) : ℂ) * ζ ^ 28 - ((4113637 / 304994) : ℂ) * ζ ^ 29 + ((2135665 / 609988) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((6320195 / 609988) : ℂ) - ((20502099 / 609988) : ℂ) * ζ ^ 3 - ((6320195 / 609988) : ℂ) * ζ ^ 4 + ((6164331 / 609988) : ℂ) * ζ ^ 5 - ((382255 / 609988) : ℂ) * ζ ^ 6 - ((6534951 / 609988) : ℂ) * ζ ^ 8 - ((6164331 / 609988) : ℂ) * ζ ^ 9 - ((6667929 / 152497) : ℂ) * ζ ^ 10 + ((11349583 / 304994) : ℂ) * ζ ^ 13 + ((26289461 / 609988) : ℂ) * ζ ^ 14 - ((20959495 / 609988) : ℂ) * ζ ^ 15 - ((6665889 / 609988) : ℂ) * ζ ^ 18 + ((20959495 / 609988) : ℂ) * ζ ^ 19 + ((5627158 / 152497) : ℂ) * ζ ^ 20 + ((382255 / 609988) : ℂ) * ζ ^ 22 - ((10121973 / 609988) : ℂ) * ζ ^ 23 - ((5627158 / 152497) : ℂ) * ζ ^ 24 + ((8848941 / 304994) : ℂ) * ζ ^ 25 + ((382255 / 609988) : ℂ) * ζ ^ 26 + ((11437735 / 609988) : ℂ) * ζ ^ 28 - ((8848941 / 304994) : ℂ) * ζ ^ 29 - ((382255 / 609988) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((((599142 / 152497) : ℂ) - ((2578335 / 609988) : ℂ) * ζ ^ 3 - ((599142 / 152497) : ℂ) * ζ ^ 4 + ((2868595 / 304994) : ℂ) * ζ ^ 5 + ((1244583 / 304994) : ℂ) * ζ ^ 6 - ((32427 / 8356) : ℂ) * ζ ^ 8 - ((2868595 / 304994) : ℂ) * ζ ^ 9 - ((2639525 / 609988) : ℂ) * ζ ^ 10 + ((7461627 / 609988) : ℂ) * ζ ^ 13 + ((5128691 / 609988) : ℂ) * ζ ^ 14 - ((4620577 / 304994) : ℂ) * ζ ^ 15 + ((796380 / 152497) : ℂ) * ζ ^ 18 + ((4620577 / 304994) : ℂ) * ζ ^ 19 - ((550278 / 152497) : ℂ) * ζ ^ 20 - ((1244583 / 304994) : ℂ) * ζ ^ 22 - ((1711958 / 152497) : ℂ) * ζ ^ 23 + ((550278 / 152497) : ℂ) * ζ ^ 24 + ((5859079 / 609988) : ℂ) * ζ ^ 25 - ((1244583 / 304994) : ℂ) * ζ ^ 26 - ((2842385 / 304994) : ℂ) * ζ ^ 28 - ((5859079 / 609988) : ℂ) * ζ ^ 29 + ((1244583 / 304994) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((-((1002329 / 304994) : ℂ) + ((6753571 / 609988) : ℂ) * ζ ^ 3 + ((1002329 / 304994) : ℂ) * ζ ^ 4 - ((2637944 / 152497) : ℂ) * ζ ^ 5 - ((1478321 / 304994) : ℂ) * ζ ^ 6 + ((5607789 / 609988) : ℂ) * ζ ^ 8 + ((2637944 / 152497) : ℂ) * ζ ^ 9 - ((878627 / 609988) : ℂ) * ζ ^ 10 - ((15433283 / 609988) : ℂ) * ζ ^ 13 - ((2078015 / 609988) : ℂ) * ζ ^ 14 + ((9505837 / 304994) : ℂ) * ζ ^ 15 - ((2487554 / 152497) : ℂ) * ζ ^ 18 - ((9505837 / 304994) : ℂ) * ζ ^ 19 + ((1600247 / 152497) : ℂ) * ζ ^ 20 + ((1478321 / 304994) : ℂ) * ζ ^ 22 + ((2368459 / 152497) : ℂ) * ζ ^ 23 - ((1600247 / 152497) : ℂ) * ζ ^ 24 - ((9942343 / 609988) : ℂ) * ζ ^ 25 + ((1478321 / 304994) : ℂ) * ζ ^ 26 + ((2269551 / 152497) : ℂ) * ζ ^ 28 + ((9942343 / 609988) : ℂ) * ζ ^ 29 - ((1478321 / 304994) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((763 / 292) : ℂ) - ((559 / 146) : ℂ) * ζ ^ 3 + ((763 / 292) : ℂ) * ζ ^ 4 + ((283 / 73) : ℂ) * ζ ^ 5 + ((363 / 146) : ℂ) * ζ ^ 6 - ((1797 / 292) : ℂ) * ζ ^ 8 - ((283 / 73) : ℂ) * ζ ^ 9 + ((530 / 73) : ℂ) * ζ ^ 10 + ((3009 / 292) : ℂ) * ζ ^ 13 - ((697 / 146) : ℂ) * ζ ^ 14 - ((498 / 73) : ℂ) * ζ ^ 15 + ((813 / 73) : ℂ) * ζ ^ 18 + ((498 / 73) : ℂ) * ζ ^ 19 - ((1689 / 292) : ℂ) * ζ ^ 20 - ((363 / 146) : ℂ) * ζ ^ 22 - ((961 / 292) : ℂ) * ζ ^ 23 + ((1689 / 292) : ℂ) * ζ ^ 24 + ((1221 / 292) : ℂ) * ζ ^ 25 - ((363 / 146) : ℂ) * ζ ^ 26 - ((1185 / 292) : ℂ) * ζ ^ 28 - ((1221 / 292) : ℂ) * ζ ^ 29 + ((363 / 146) : ℂ) * ζ ^ 30)) * Y 2 2
        + ((((39 / 73) : ℂ) + ((225 / 146) : ℂ) * ζ ^ 3 - ((39 / 73) : ℂ) * ζ ^ 4 - ((285 / 292) : ℂ) * ζ ^ 5 - ((333 / 292) : ℂ) * ζ ^ 6 + ((109 / 146) : ℂ) * ζ ^ 8 + ((285 / 292) : ℂ) * ζ ^ 9 - ((681 / 292) : ℂ) * ζ ^ 10 - ((178 / 73) : ℂ) * ζ ^ 13 + ((87 / 73) : ℂ) * ζ ^ 14 + ((565 / 292) : ℂ) * ζ ^ 15 - ((23 / 292) : ℂ) * ζ ^ 18 - ((565 / 292) : ℂ) * ζ ^ 19 + ((555 / 292) : ℂ) * ζ ^ 20 + ((333 / 292) : ℂ) * ζ ^ 22 + ((355 / 292) : ℂ) * ζ ^ 23 - ((555 / 292) : ℂ) * ζ ^ 24 - ((100 / 73) : ℂ) * ζ ^ 25 + ((333 / 292) : ℂ) * ζ ^ 26 + ((3 / 73) : ℂ) * ζ ^ 28 + ((100 / 73) : ℂ) * ζ ^ 29 - ((333 / 292) : ℂ) * ζ ^ 30)) * Y 4 4
        + ((-((113 / 146) : ℂ) - ((24 / 73) : ℂ) * ζ ^ 3 + ((113 / 146) : ℂ) * ζ ^ 4 - ((101 / 146) : ℂ) * ζ ^ 5 + ((9 / 73) : ℂ) * ζ ^ 6 - ((65 / 292) : ℂ) * ζ ^ 8 + ((101 / 146) : ℂ) * ζ ^ 9 - ((27 / 292) : ℂ) * ζ ^ 10 + ((37 / 73) : ℂ) * ζ ^ 13 + ((63 / 292) : ℂ) * ζ ^ 14 + ((149 / 146) : ℂ) * ζ ^ 15 - ((127 / 146) : ℂ) * ζ ^ 18 - ((149 / 146) : ℂ) * ζ ^ 19 - ((103 / 146) : ℂ) * ζ ^ 20 - ((9 / 73) : ℂ) * ζ ^ 22 + ((445 / 292) : ℂ) * ζ ^ 23 + ((103 / 146) : ℂ) * ζ ^ 24 - ((85 / 292) : ℂ) * ζ ^ 25 - ((9 / 73) : ℂ) * ζ ^ 26 - ((121 / 146) : ℂ) * ζ ^ 28 + ((85 / 292) : ℂ) * ζ ^ 29 + ((9 / 73) : ℂ) * ζ ^ 30)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation


/-- A matrix commuting with both transformed row 15 generators is
scalar. -/
theorem alternatingSixAmbientRow15Transformed_scalar_commutant
    (Y : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow15TransformedGeneratorA =
        alternatingSixAmbientRow15TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow15GeneratorBDiagonal =
        alternatingSixAmbientRow15GeneratorBDiagonal * Y) :
    ∃ c : ℂ,
      Y = c • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 4 3 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow15_off_block
      Y commutesDiagonal 5 3 (by decide)

  have reducedY00 : Y 0 0 = Y 5 5 :=
    row15_reducedY00 Y commutesA commutesDiagonal
  have reducedY01 : Y 0 1 = 0 :=
    row15_reducedY01 Y commutesA commutesDiagonal
  have reducedY10 : Y 1 0 = 0 :=
    row15_reducedY10 Y commutesA commutesDiagonal
  have reducedY11 : Y 1 1 = Y 5 5 :=
    row15_reducedY11 Y commutesA commutesDiagonal
  have reducedY22 : Y 2 2 = Y 5 5 :=
    row15_reducedY22 Y commutesA commutesDiagonal
  have reducedY33 : Y 3 3 = Y 5 5 :=
    row15_reducedY33 Y commutesA commutesDiagonal
  have reducedY45 : Y 4 5 = 0 :=
    row15_reducedY45 Y commutesA commutesDiagonal
  have reducedY44 : Y 4 4 = Y 5 5 :=
    row15_reducedY44 Y commutesA commutesDiagonal
  have reducedY54 : Y 5 4 = 0 :=
    row15_reducedY54 Y commutesA commutesDiagonal

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
      hY34,
      hY35,
      hY40,
      hY41,
      hY42,
      hY43,
      hY50,
      hY51,
      hY52,
      hY53,
      reducedY00,
      reducedY01,
      reducedY10,
      reducedY11,
      reducedY22,
      reducedY33,
      reducedY45,
      reducedY44,
      reducedY54]

/-- Every matrix commuting with both original row 15 presentation
generators is scalar. -/
theorem alternatingSixAmbientRow15_scalar_commutant
    (X : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesA :
      X * alternatingSixFiveAmbient_row15_matrixA =
        alternatingSixFiveAmbient_row15_matrixA * X)
    (commutesB :
      X * alternatingSixFiveAmbient_row15_matrixB =
        alternatingSixFiveAmbient_row15_matrixB * X) :
    ∃ c : ℂ,
      X = c • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  apply Matrix.scalar_commutant_of_diagonal_basis
    alternatingSixFiveAmbient_row15_matrixA
    alternatingSixFiveAmbient_row15_matrixB
    alternatingSixAmbientRow15Eigenbasis
    alternatingSixAmbientRow15EigenbasisInverse
    alternatingSixAmbientRow15TransformedGeneratorA
    alternatingSixAmbientRow15GeneratorBEigenvalue
    alternatingSixAmbientRow15EigenbasisInverse_mul
    alternatingSixAmbientRow15Eigenbasis_mul_inverse
    alternatingSixAmbientRow15GeneratorB_mul_eigenbasis
    alternatingSixAmbientRow15TransformedGeneratorA_eq
    alternatingSixAmbientRow15Transformed_scalar_commutant
    X commutesA commutesB

end InductiveMcKay
end McKayConjecture
