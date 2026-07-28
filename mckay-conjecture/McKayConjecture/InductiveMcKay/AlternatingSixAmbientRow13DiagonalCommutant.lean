/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DiagonalBasisMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow13DiagonalData

/-!
# Scalar common commutant for ambient row 13

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
private theorem alternatingSixAmbientRow13_off_block
    (Y : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow13GeneratorBDiagonal =
        alternatingSixAmbientRow13GeneratorBDiagonal * Y)
    (i j : Fin 6)
    (different :
      alternatingSixAmbientRow13EigenvalueLabel i ≠
        alternatingSixAmbientRow13EigenvalueLabel j) :
    Y i j = 0 := by
  apply Matrix.entry_eq_zero_of_mul_diagonal_eq_diagonal_mul
    Y alternatingSixAmbientRow13GeneratorBEigenvalue
  · exact commutesDiagonal
  · intro equalEigenvalues
    apply different
    apply alternatingSixOrderEightOddEigenvalue_injective
    simpa [
      alternatingSixAmbientRow13GeneratorBEigenvalue] using
      equalEigenvalues.symm

private theorem row13_reducedY00
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow13TransformedGeneratorA =
        alternatingSixAmbientRow13TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow13GeneratorBDiagonal =
        alternatingSixAmbientRow13GeneratorBDiagonal * Y) :
    Y 0 0 = Y 5 5 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
    ((-((23249 / 1067) : ℂ) + ((79027 / 5335) : ℂ) * ζ ^ 3 + ((116751 / 5335) : ℂ) * ζ ^ 5 + ((79027 / 5335) : ℂ) * ζ ^ 7 - ((100256 / 5335) : ℂ) * ζ ^ 10 + ((52127 / 5335) : ℂ) * ζ ^ 15 - ((79027 / 5335) : ℂ) * ζ ^ 19 + ((18088 / 5335) : ℂ) * ζ ^ 20 - ((79027 / 5335) : ℂ) * ζ ^ 23 - ((43482 / 5335) : ℂ) * ζ ^ 25 + ((48831 / 5335) : ℂ) * ζ ^ 30 + ((79027 / 5335) : ℂ) * ζ ^ 31)) * commutesA00
      + ((-((29287 / 5335) : ℂ) + ((38034 / 5335) : ℂ) * ζ ^ 3 + ((2459 / 5335) : ℂ) * ζ ^ 5 + ((38034 / 5335) : ℂ) * ζ ^ 7 + ((8339 / 1067) : ℂ) * ζ ^ 10 - ((11417 / 485) : ℂ) * ζ ^ 15 - ((38034 / 5335) : ℂ) * ζ ^ 19 + ((24219 / 1067) : ℂ) * ζ ^ 20 - ((38034 / 5335) : ℂ) * ζ ^ 23 - ((108991 / 5335) : ℂ) * ζ ^ 25 + ((100256 / 5335) : ℂ) * ζ ^ 30 + ((38034 / 5335) : ℂ) * ζ ^ 31)) * commutesA01
      + ((-((730 / 11) : ℂ) + ((731 / 11) : ℂ) * ζ ^ 3 + ((629 / 11) : ℂ) * ζ ^ 5 + ((731 / 11) : ℂ) * ζ ^ 7 - ((525 / 11) : ℂ) * ζ ^ 10 - ((383 / 11) : ℂ) * ζ ^ 15 - ((731 / 11) : ℂ) * ζ ^ 19 + ((543 / 11) : ℂ) * ζ ^ 20 - ((731 / 11) : ℂ) * ζ ^ 23 - ((644 / 11) : ℂ) * ζ ^ 25 + ((731 / 11) : ℂ) * ζ ^ 30 + ((731 / 11) : ℂ) * ζ ^ 31)) * commutesA02
      + (((3 : ℂ) - (2 : ℂ) * ζ ^ 3 - (3 : ℂ) * ζ ^ 5 - (2 : ℂ) * ζ ^ 7 + (4 : ℂ) * ζ ^ 10 - ζ ^ 15 + (2 : ℂ) * ζ ^ 19 - (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 23 - ζ ^ 25 - (3 : ℂ) * ζ ^ 30 - (2 : ℂ) * ζ ^ 31)) * commutesA05
      + ((-((29 / 33) : ℂ) + ((587 / 33) : ℂ) * ζ ^ 3 - ((488 / 33) : ℂ) * ζ ^ 5 + ((587 / 33) : ℂ) * ζ ^ 7 + ((323 / 11) : ℂ) * ζ ^ 10 - ((1990 / 33) : ℂ) * ζ ^ 15 - ((587 / 33) : ℂ) * ζ ^ 19 + ((1747 / 33) : ℂ) * ζ ^ 20 - ((587 / 33) : ℂ) * ζ ^ 23 - ((1469 / 33) : ℂ) * ζ ^ 25 + ((348 / 11) : ℂ) * ζ ^ 30 + ((587 / 33) : ℂ) * ζ ^ 31)) * commutesA12
      + (((2 : ℂ) - ((7 / 3) : ℂ) * ζ ^ 3 + ((5 / 3) : ℂ) * ζ ^ 5 - ((7 / 3) : ℂ) * ζ ^ 7 + ((7 / 3) : ℂ) * ζ ^ 10 + ((11 / 3) : ℂ) * ζ ^ 15 + ((7 / 3) : ℂ) * ζ ^ 19 - ζ ^ 20 + ((7 / 3) : ℂ) * ζ ^ 23 + ((8 / 3) : ℂ) * ζ ^ 25 - ((5 / 3) : ℂ) * ζ ^ 30 - ((7 / 3) : ℂ) * ζ ^ 31)) * commutesA15
      - (
        ((-((213355 / 6402) : ℂ) + ((923041 / 32010) : ℂ) * ζ ^ 3 + ((213355 / 6402) : ℂ) * ζ ^ 4 + ((186611 / 6402) : ℂ) * ζ ^ 5 + ((14618 / 5335) : ℂ) * ζ ^ 6 - ((1029847 / 32010) : ℂ) * ζ ^ 8 - ((186611 / 6402) : ℂ) * ζ ^ 9 - ((113043 / 21340) : ℂ) * ζ ^ 10 + ((44763 / 4268) : ℂ) * ζ ^ 13 + ((34303 / 4268) : ℂ) * ζ ^ 14 + ((33751 / 5820) : ℂ) * ζ ^ 15 - ((16471 / 1164) : ℂ) * ζ ^ 18 - ((33751 / 5820) : ℂ) * ζ ^ 19 - ((59049 / 21340) : ℂ) * ζ ^ 20 - ((14618 / 5335) : ℂ) * ζ ^ 22 + ((680021 / 64020) : ℂ) * ζ ^ 23 + ((59049 / 21340) : ℂ) * ζ ^ 24 - ((32023 / 3201) : ℂ) * ζ ^ 25 - ((14618 / 5335) : ℂ) * ζ ^ 26 + ((239797 / 32010) : ℂ) * ζ ^ 28 + ((32023 / 3201) : ℂ) * ζ ^ 29 + ((14618 / 5335) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((83067 / 2134) : ℂ) - ((339653 / 10670) : ℂ) * ζ ^ 3 - ((83067 / 2134) : ℂ) * ζ ^ 4 - ((186423 / 5335) : ℂ) * ζ ^ 5 + ((73109 / 21340) : ℂ) * ζ ^ 6 + ((679901 / 21340) : ℂ) * ζ ^ 8 + ((186423 / 5335) : ℂ) * ζ ^ 9 + ((310714 / 5335) : ℂ) * ζ ^ 10 - ((478521 / 10670) : ℂ) * ζ ^ 13 - ((1169747 / 21340) : ℂ) * ζ ^ 14 - ((752977 / 10670) : ℂ) * ζ ^ 15 + ((939533 / 21340) : ℂ) * ζ ^ 18 + ((752977 / 10670) : ℂ) * ζ ^ 19 + ((282827 / 21340) : ℂ) * ζ ^ 20 - ((73109 / 21340) : ℂ) * ζ ^ 22 - ((55119 / 5335) : ℂ) * ζ ^ 23 - ((282827 / 21340) : ℂ) * ζ ^ 24 - ((252189 / 10670) : ℂ) * ζ ^ 25 - ((73109 / 21340) : ℂ) * ζ ^ 26 + ((122489 / 10670) : ℂ) * ζ ^ 28 + ((252189 / 10670) : ℂ) * ζ ^ 29 + ((73109 / 21340) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((-((134093 / 12804) : ℂ) + ((6716 / 291) : ℂ) * ζ ^ 3 + ((134093 / 12804) : ℂ) * ζ ^ 4 + ((3037 / 6402) : ℂ) * ζ ^ 5 - ((2189 / 485) : ℂ) * ζ ^ 6 - ((1122919 / 64020) : ℂ) * ζ ^ 8 - ((3037 / 6402) : ℂ) * ζ ^ 9 - ((150631 / 21340) : ℂ) * ζ ^ 10 + ((147793 / 21340) : ℂ) * ζ ^ 13 + ((10863 / 4268) : ℂ) * ζ ^ 14 + ((1367 / 291) : ℂ) * ζ ^ 15 - ((545027 / 64020) : ℂ) * ζ ^ 18 - ((1367 / 291) : ℂ) * ζ ^ 19 - ((599627 / 64020) : ℂ) * ζ ^ 20 + ((2189 / 485) : ℂ) * ζ ^ 22 + ((104163 / 10670) : ℂ) * ζ ^ 23 + ((599627 / 64020) : ℂ) * ζ ^ 24 + ((215461 / 32010) : ℂ) * ζ ^ 25 + ((2189 / 485) : ℂ) * ζ ^ 26 - ((25279 / 10670) : ℂ) * ζ ^ 28 - ((215461 / 32010) : ℂ) * ζ ^ 29 - ((2189 / 485) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((-((10909 / 6402) : ℂ) - ((4537 / 64020) : ℂ) * ζ ^ 3 + ((10909 / 6402) : ℂ) * ζ ^ 4 + ((5197 / 1164) : ℂ) * ζ ^ 5 - ((12678 / 5335) : ℂ) * ζ ^ 6 - ((11608 / 5335) : ℂ) * ζ ^ 8 - ((5197 / 1164) : ℂ) * ζ ^ 9 - ((120979 / 16005) : ℂ) * ζ ^ 10 + ((51 / 4268) : ℂ) * ζ ^ 13 + ((16589 / 3201) : ℂ) * ζ ^ 14 + ((565759 / 64020) : ℂ) * ζ ^ 15 + ((81271 / 12804) : ℂ) * ζ ^ 18 - ((565759 / 64020) : ℂ) * ζ ^ 19 - ((277147 / 16005) : ℂ) * ζ ^ 20 + ((12678 / 5335) : ℂ) * ζ ^ 22 + ((469697 / 32010) : ℂ) * ζ ^ 23 + ((277147 / 16005) : ℂ) * ζ ^ 24 + ((112669 / 12804) : ℂ) * ζ ^ 25 + ((12678 / 5335) : ℂ) * ζ ^ 26 - ((408299 / 64020) : ℂ) * ζ ^ 28 - ((112669 / 12804) : ℂ) * ζ ^ 29 - ((12678 / 5335) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((((4351 / 132) : ℂ) - ((3799 / 132) : ℂ) * ζ ^ 3 - ((4351 / 132) : ℂ) * ζ ^ 4 - ((2131 / 66) : ℂ) * ζ ^ 5 + ((4351 / 132) : ℂ) * ζ ^ 8 + ((2131 / 66) : ℂ) * ζ ^ 9 + ((475 / 33) : ℂ) * ζ ^ 10 - ((247 / 22) : ℂ) * ζ ^ 13 - ((475 / 33) : ℂ) * ζ ^ 14 - ((2063 / 132) : ℂ) * ζ ^ 15 + ((1313 / 132) : ℂ) * ζ ^ 18 + ((2063 / 132) : ℂ) * ζ ^ 19 + ((695 / 33) : ℂ) * ζ ^ 20 - ((1079 / 44) : ℂ) * ζ ^ 23 - ((695 / 33) : ℂ) * ζ ^ 24)) * Y 2 2
        + ((((43 / 22) : ℂ) - ((307 / 132) : ℂ) * ζ ^ 3 - ((43 / 22) : ℂ) * ζ ^ 4 + ((17 / 132) : ℂ) * ζ ^ 5 + ((16 / 33) : ℂ) * ζ ^ 6 + ((11 / 6) : ℂ) * ζ ^ 8 - ((17 / 132) : ℂ) * ζ ^ 9 + ((73 / 22) : ℂ) * ζ ^ 10 - ((31 / 33) : ℂ) * ζ ^ 13 - ((17 / 6) : ℂ) * ζ ^ 14 - ((35 / 33) : ℂ) * ζ ^ 15 + ((325 / 132) : ℂ) * ζ ^ 18 + ((35 / 33) : ℂ) * ζ ^ 19 + ((7 / 12) : ℂ) * ζ ^ 20 - ((16 / 33) : ℂ) * ζ ^ 22 + ((9 / 22) : ℂ) * ζ ^ 23 - ((7 / 12) : ℂ) * ζ ^ 24 - ((49 / 66) : ℂ) * ζ ^ 25 - ((16 / 33) : ℂ) * ζ ^ 26 + ((3 / 11) : ℂ) * ζ ^ 28 + ((49 / 66) : ℂ) * ζ ^ 29 + ((16 / 33) : ℂ) * ζ ^ 30)) * Y 4 5
        + ((((91 / 44) : ℂ) + ((1 / 66) : ℂ) * ζ ^ 3 - ((91 / 44) : ℂ) * ζ ^ 4 - ((175 / 132) : ℂ) * ζ ^ 5 - ((4 / 11) : ℂ) * ζ ^ 6 + ((61 / 44) : ℂ) * ζ ^ 8 + ((175 / 132) : ℂ) * ζ ^ 9 - ((203 / 132) : ℂ) * ζ ^ 10 + ((8 / 11) : ℂ) * ζ ^ 13 + ((155 / 132) : ℂ) * ζ ^ 14 + ((131 / 132) : ℂ) * ζ ^ 15 - ((283 / 132) : ℂ) * ζ ^ 18 - ((131 / 132) : ℂ) * ζ ^ 19 - ((43 / 44) : ℂ) * ζ ^ 20 + ((4 / 11) : ℂ) * ζ ^ 22 - ((17 / 22) : ℂ) * ζ ^ 23 + ((43 / 44) : ℂ) * ζ ^ 24 + ((53 / 44) : ℂ) * ζ ^ 25 + ((4 / 11) : ℂ) * ζ ^ 26 - ((49 / 44) : ℂ) * ζ ^ 28 - ((53 / 44) : ℂ) * ζ ^ 29 - ((4 / 11) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row13_reducedY01
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow13TransformedGeneratorA =
        alternatingSixAmbientRow13TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow13GeneratorBDiagonal =
        alternatingSixAmbientRow13GeneratorBDiagonal * Y) :
    Y 0 1 = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
    ((-((31 / 3) : ℂ) + (11 : ℂ) * ζ ^ 3 + ((16 / 3) : ℂ) * ζ ^ 5 + (11 : ℂ) * ζ ^ 7 + ((1 / 3) : ℂ) * ζ ^ 10 - (14 : ℂ) * ζ ^ 15 - (11 : ℂ) * ζ ^ 19 + ((47 / 3) : ℂ) * ζ ^ 20 - (11 : ℂ) * ζ ^ 23 - ((47 / 3) : ℂ) * ζ ^ 25 + ((40 / 3) : ℂ) * ζ ^ 30 + (11 : ℂ) * ζ ^ 31)) * commutesA00
      + (((16 : ℂ) - (15 : ℂ) * ζ ^ 3 - (17 : ℂ) * ζ ^ 5 - (15 : ℂ) * ζ ^ 7 + (17 : ℂ) * ζ ^ 10 - ζ ^ 15 + (15 : ℂ) * ζ ^ 19 - (5 : ℂ) * ζ ^ 20 + (15 : ℂ) * ζ ^ 23 + (8 : ℂ) * ζ ^ 25 - (11 : ℂ) * ζ ^ 30 - (15 : ℂ) * ζ ^ 31)) * commutesA01
      + (((10 : ℂ) + ((8 / 3) : ℂ) * ζ ^ 3 - ((70 / 3) : ℂ) * ζ ^ 5 + ((8 / 3) : ℂ) * ζ ^ 7 + ((94 / 3) : ℂ) * ζ ^ 10 - ((130 / 3) : ℂ) * ζ ^ 15 - ((8 / 3) : ℂ) * ζ ^ 19 + (34 : ℂ) * ζ ^ 20 - ((8 / 3) : ℂ) * ζ ^ 23 - ((76 / 3) : ℂ) * ζ ^ 25 + ((46 / 3) : ℂ) * ζ ^ 30 + ((8 / 3) : ℂ) * ζ ^ 31)) * commutesA02
      + (((44 : ℂ) - ((122 / 3) : ℂ) * ζ ^ 3 - (42 : ℂ) * ζ ^ 5 - ((122 / 3) : ℂ) * ζ ^ 7 + ((116 / 3) : ℂ) * ζ ^ 10 + (8 : ℂ) * ζ ^ 15 + ((122 / 3) : ℂ) * ζ ^ 19 - (18 : ℂ) * ζ ^ 20 + ((122 / 3) : ℂ) * ζ ^ 23 + ((80 / 3) : ℂ) * ζ ^ 25 - (36 : ℂ) * ζ ^ 30 - ((122 / 3) : ℂ) * ζ ^ 31)) * commutesA12
      - (
        ((-((5 / 3) : ℂ) + ((155 / 12) : ℂ) * ζ ^ 3 + ((5 / 3) : ℂ) * ζ ^ 4 - ((55 / 12) : ℂ) * ζ ^ 5 - (5 : ℂ) * ζ ^ 6 - ((22 / 3) : ℂ) * ζ ^ 8 + ((55 / 12) : ℂ) * ζ ^ 9 - ((67 / 12) : ℂ) * ζ ^ 10 + ((20 / 3) : ℂ) * ζ ^ 13 + ((7 / 12) : ℂ) * ζ ^ 14 + ((23 / 12) : ℂ) * ζ ^ 15 - ((41 / 12) : ℂ) * ζ ^ 18 - ((23 / 12) : ℂ) * ζ ^ 19 - (7 : ℂ) * ζ ^ 20 + (5 : ℂ) * ζ ^ 22 + ((13 / 2) : ℂ) * ζ ^ 23 + (7 : ℂ) * ζ ^ 24 + ((26 / 3) : ℂ) * ζ ^ 25 + (5 : ℂ) * ζ ^ 26 - ((11 / 3) : ℂ) * ζ ^ 28 - ((26 / 3) : ℂ) * ζ ^ 29 - (5 : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((41 / 6) : ℂ) + ((83 / 12) : ℂ) * ζ ^ 3 - ((41 / 6) : ℂ) * ζ ^ 4 - ((7 / 2) : ℂ) * ζ ^ 5 - ((71 / 4) : ℂ) * ζ ^ 6 - ((31 / 4) : ℂ) * ζ ^ 8 + ((7 / 2) : ℂ) * ζ ^ 9 - ((307 / 12) : ℂ) * ζ ^ 10 + ((55 / 4) : ℂ) * ζ ^ 13 + ((47 / 6) : ℂ) * ζ ^ 14 + ((97 / 6) : ℂ) * ζ ^ 15 - ((11 / 12) : ℂ) * ζ ^ 18 - ((97 / 6) : ℂ) * ζ ^ 19 - ((141 / 4) : ℂ) * ζ ^ 20 + ((71 / 4) : ℂ) * ζ ^ 22 + ((259 / 12) : ℂ) * ζ ^ 23 + ((141 / 4) : ℂ) * ζ ^ 24 + ((229 / 12) : ℂ) * ζ ^ 25 + ((71 / 4) : ℂ) * ζ ^ 26 - ((13 / 6) : ℂ) * ζ ^ 28 - ((229 / 12) : ℂ) * ζ ^ 29 - ((71 / 4) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((((637 / 36) : ℂ) - ((443 / 36) : ℂ) * ζ ^ 3 - ((637 / 36) : ℂ) * ζ ^ 4 - ((169 / 9) : ℂ) * ζ ^ 5 - ((11 / 3) : ℂ) * ζ ^ 6 + ((191 / 12) : ℂ) * ζ ^ 8 + ((169 / 9) : ℂ) * ζ ^ 9 + ((1 / 2) : ℂ) * ζ ^ 10 - ((149 / 36) : ℂ) * ζ ^ 13 - ((25 / 6) : ℂ) * ζ ^ 14 - ((113 / 36) : ℂ) * ζ ^ 15 + (7 : ℂ) * ζ ^ 18 + ((113 / 36) : ℂ) * ζ ^ 19 + ((1 / 2) : ℂ) * ζ ^ 20 + ((11 / 3) : ℂ) * ζ ^ 22 - ((34 / 9) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 24 + ((73 / 9) : ℂ) * ζ ^ 25 + ((11 / 3) : ℂ) * ζ ^ 26 - ((40 / 9) : ℂ) * ζ ^ 28 - ((73 / 9) : ℂ) * ζ ^ 29 - ((11 / 3) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((-((13 / 3) : ℂ) - ((17 / 12) : ℂ) * ζ ^ 3 + ((13 / 3) : ℂ) * ζ ^ 4 + ((41 / 12) : ℂ) * ζ ^ 5 + (5 : ℂ) * ζ ^ 6 + ((4 / 3) : ℂ) * ζ ^ 8 - ((41 / 12) : ℂ) * ζ ^ 9 - ((23 / 12) : ℂ) * ζ ^ 10 + ((5 / 3) : ℂ) * ζ ^ 13 + ((83 / 12) : ℂ) * ζ ^ 14 + ((53 / 4) : ℂ) * ζ ^ 15 - ((57 / 4) : ℂ) * ζ ^ 18 - ((53 / 4) : ℂ) * ζ ^ 19 + ((33 / 2) : ℂ) * ζ ^ 20 - (5 : ℂ) * ζ ^ 22 - ((35 / 3) : ℂ) * ζ ^ 23 - ((33 / 2) : ℂ) * ζ ^ 24 - ((26 / 3) : ℂ) * ζ ^ 25 - (5 : ℂ) * ζ ^ 26 + ((11 / 3) : ℂ) * ζ ^ 28 + ((26 / 3) : ℂ) * ζ ^ 29 + (5 : ℂ) * ζ ^ 30)) * Y 1 1
        + (((6 : ℂ) - ((23 / 2) : ℂ) * ζ ^ 3 - (6 : ℂ) * ζ ^ 4 + ((7 / 6) : ℂ) * ζ ^ 5 + (6 : ℂ) * ζ ^ 8 - ((7 / 6) : ℂ) * ζ ^ 9 + ((15 / 2) : ℂ) * ζ ^ 10 - ((25 / 3) : ℂ) * ζ ^ 13 - ((15 / 2) : ℂ) * ζ ^ 14 - ((91 / 6) : ℂ) * ζ ^ 15 + ((53 / 3) : ℂ) * ζ ^ 18 + ((91 / 6) : ℂ) * ζ ^ 19 - ((19 / 2) : ℂ) * ζ ^ 20 + ((31 / 6) : ℂ) * ζ ^ 23 + ((19 / 2) : ℂ) * ζ ^ 24)) * Y 2 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row13_reducedY10
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow13TransformedGeneratorA =
        alternatingSixAmbientRow13TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow13GeneratorBDiagonal =
        alternatingSixAmbientRow13GeneratorBDiagonal * Y) :
    Y 1 0 = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
    ((-((3951 / 485) : ℂ) + ((1116 / 97) : ℂ) * ζ ^ 3 + ((3161 / 485) : ℂ) * ζ ^ 5 + ((1116 / 97) : ℂ) * ζ ^ 7 - ((1289 / 485) : ℂ) * ζ ^ 10 - ((5813 / 485) : ℂ) * ζ ^ 15 - ((1116 / 97) : ℂ) * ζ ^ 19 + ((6727 / 485) : ℂ) * ζ ^ 20 - ((1116 / 97) : ℂ) * ζ ^ 23 - ((6611 / 485) : ℂ) * ζ ^ 25 + ((6052 / 485) : ℂ) * ζ ^ 30 + ((1116 / 97) : ℂ) * ζ ^ 31)) * commutesA00
      + ((((5686 / 485) : ℂ) - ((6053 / 485) : ℂ) * ζ ^ 3 - ((1466 / 97) : ℂ) * ζ ^ 5 - ((6053 / 485) : ℂ) * ζ ^ 7 + ((7673 / 485) : ℂ) * ζ ^ 10 - ((146 / 97) : ℂ) * ζ ^ 15 + ((6053 / 485) : ℂ) * ζ ^ 19 + ((71 / 485) : ℂ) * ζ ^ 20 + ((6053 / 485) : ℂ) * ζ ^ 23 + ((2659 / 485) : ℂ) * ζ ^ 25 - ((4531 / 485) : ℂ) * ζ ^ 30 - ((6053 / 485) : ℂ) * ζ ^ 31)) * commutesA01
      + (((1 : ℂ) + (6 : ℂ) * ζ ^ 3 - (15 : ℂ) * ζ ^ 5 + (6 : ℂ) * ζ ^ 7 + (24 : ℂ) * ζ ^ 10 - (39 : ℂ) * ζ ^ 15 - (6 : ℂ) * ζ ^ 19 + (36 : ℂ) * ζ ^ 20 - (6 : ℂ) * ζ ^ 23 - (25 : ℂ) * ζ ^ 25 + (19 : ℂ) * ζ ^ 30 + (6 : ℂ) * ζ ^ 31)) * commutesA02
      + (((38 : ℂ) - (33 : ℂ) * ζ ^ 3 - (39 : ℂ) * ζ ^ 5 - (33 : ℂ) * ζ ^ 7 + (35 : ℂ) * ζ ^ 10 + ζ ^ 15 + (33 : ℂ) * ζ ^ 19 - (13 : ℂ) * ζ ^ 20 + (33 : ℂ) * ζ ^ 23 + (20 : ℂ) * ζ ^ 25 - (27 : ℂ) * ζ ^ 30 - (33 : ℂ) * ζ ^ 31)) * commutesA12
      - (
        ((-((1276 / 291) : ℂ) + ((70469 / 5820) : ℂ) * ζ ^ 3 + ((1276 / 291) : ℂ) * ζ ^ 4 - ((350 / 291) : ℂ) * ζ ^ 5 - ((6053 / 1455) : ℂ) * ζ ^ 6 - ((914 / 97) : ℂ) * ζ ^ 8 + ((350 / 291) : ℂ) * ζ ^ 9 - ((11311 / 2910) : ℂ) * ζ ^ 10 + ((45227 / 5820) : ℂ) * ζ ^ 13 - ((53 / 194) : ℂ) * ζ ^ 14 + ((1933 / 1455) : ℂ) * ζ ^ 15 - ((3359 / 1455) : ℂ) * ζ ^ 18 - ((1933 / 1455) : ℂ) * ζ ^ 19 - ((3749 / 582) : ℂ) * ζ ^ 20 + ((6053 / 1455) : ℂ) * ζ ^ 22 + ((38281 / 5820) : ℂ) * ζ ^ 23 + ((3749 / 582) : ℂ) * ζ ^ 24 + ((3528 / 485) : ℂ) * ζ ^ 25 + ((6053 / 1455) : ℂ) * ζ ^ 26 - ((4531 / 1455) : ℂ) * ζ ^ 28 - ((3528 / 485) : ℂ) * ζ ^ 29 - ((6053 / 1455) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((15319 / 1940) : ℂ) + ((293 / 388) : ℂ) * ζ ^ 3 - ((15319 / 1940) : ℂ) * ζ ^ 4 - ((2211 / 388) : ℂ) * ζ ^ 5 - ((7448 / 485) : ℂ) * ζ ^ 6 - ((11109 / 1940) : ℂ) * ζ ^ 8 + ((2211 / 388) : ℂ) * ζ ^ 9 - ((15583 / 970) : ℂ) * ζ ^ 10 + ((18489 / 1940) : ℂ) * ζ ^ 13 + ((687 / 970) : ℂ) * ζ ^ 14 + ((15507 / 1940) : ℂ) * ζ ^ 15 + ((5241 / 970) : ℂ) * ζ ^ 18 - ((15507 / 1940) : ℂ) * ζ ^ 19 - ((58539 / 1940) : ℂ) * ζ ^ 20 + ((7448 / 485) : ℂ) * ζ ^ 22 + ((3815 / 194) : ℂ) * ζ ^ 23 + ((58539 / 1940) : ℂ) * ζ ^ 24 + ((15351 / 970) : ℂ) * ζ ^ 25 + ((7448 / 485) : ℂ) * ζ ^ 26 - ((301 / 194) : ℂ) * ζ ^ 28 - ((15351 / 970) : ℂ) * ζ ^ 29 - ((7448 / 485) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((((5667 / 388) : ℂ) - ((8721 / 970) : ℂ) * ζ ^ 3 - ((5667 / 388) : ℂ) * ζ ^ 4 - ((19537 / 1164) : ℂ) * ζ ^ 5 - ((372 / 97) : ℂ) * ζ ^ 6 + ((72361 / 5820) : ℂ) * ζ ^ 8 + ((19537 / 1164) : ℂ) * ζ ^ 9 - ((98 / 291) : ℂ) * ζ ^ 10 - ((2769 / 970) : ℂ) * ζ ^ 13 - ((1018 / 291) : ℂ) * ζ ^ 14 - ((4611 / 1940) : ℂ) * ζ ^ 15 + ((8113 / 1455) : ℂ) * ζ ^ 18 + ((4611 / 1940) : ℂ) * ζ ^ 19 - ((879 / 1940) : ℂ) * ζ ^ 20 + ((372 / 97) : ℂ) * ζ ^ 22 - ((12841 / 5820) : ℂ) * ζ ^ 23 + ((879 / 1940) : ℂ) * ζ ^ 24 + ((11632 / 1455) : ℂ) * ζ ^ 25 + ((372 / 97) : ℂ) * ζ ^ 26 - ((6052 / 1455) : ℂ) * ζ ^ 28 - ((11632 / 1455) : ℂ) * ζ ^ 29 - ((372 / 97) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((-((1343 / 291) : ℂ) - ((2497 / 2910) : ℂ) * ζ ^ 3 + ((1343 / 291) : ℂ) * ζ ^ 4 + ((4019 / 1164) : ℂ) * ζ ^ 5 + ((6053 / 1455) : ℂ) * ζ ^ 6 + ((41 / 97) : ℂ) * ζ ^ 8 - ((4019 / 1164) : ℂ) * ζ ^ 9 - ((3802 / 1455) : ℂ) * ζ ^ 10 + ((7153 / 5820) : ℂ) * ζ ^ 13 + ((657 / 97) : ℂ) * ζ ^ 14 + ((38329 / 2910) : ℂ) * ζ ^ 15 - ((72409 / 5820) : ℂ) * ζ ^ 18 - ((38329 / 2910) : ℂ) * ζ ^ 19 + ((15355 / 1164) : ℂ) * ζ ^ 20 - ((6053 / 1455) : ℂ) * ζ ^ 22 - ((49921 / 5820) : ℂ) * ζ ^ 23 - ((15355 / 1164) : ℂ) * ζ ^ 24 - ((3528 / 485) : ℂ) * ζ ^ 25 - ((6053 / 1455) : ℂ) * ζ ^ 26 + ((4531 / 1455) : ℂ) * ζ ^ 28 + ((3528 / 485) : ℂ) * ζ ^ 29 + ((6053 / 1455) : ℂ) * ζ ^ 30)) * Y 1 1
        + (((9 : ℂ) - ((45 / 4) : ℂ) * ζ ^ 3 - (9 : ℂ) * ζ ^ 4 - ((9 / 4) : ℂ) * ζ ^ 5 + (9 : ℂ) * ζ ^ 8 + ((9 / 4) : ℂ) * ζ ^ 9 + ((13 / 2) : ℂ) * ζ ^ 10 - (9 : ℂ) * ζ ^ 13 - ((13 / 2) : ℂ) * ζ ^ 14 - ((29 / 2) : ℂ) * ζ ^ 15 + ((59 / 4) : ℂ) * ζ ^ 18 + ((29 / 2) : ℂ) * ζ ^ 19 - ((27 / 4) : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 23 + ((27 / 4) : ℂ) * ζ ^ 24)) * Y 2 2)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row13_reducedY11
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow13TransformedGeneratorA =
        alternatingSixAmbientRow13TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow13GeneratorBDiagonal =
        alternatingSixAmbientRow13GeneratorBDiagonal * Y) :
    Y 1 1 = Y 5 5 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
    ((-((2604 / 5335) : ℂ) - ((20501 / 5335) : ℂ) * ζ ^ 3 - ((23609 / 5335) : ℂ) * ζ ^ 5 - ((20501 / 5335) : ℂ) * ζ ^ 7 + ((52237 / 5335) : ℂ) * ζ ^ 10 + ((3067 / 5335) : ℂ) * ζ ^ 15 + ((20501 / 5335) : ℂ) * ζ ^ 19 + ((25359 / 5335) : ℂ) * ζ ^ 20 + ((20501 / 5335) : ℂ) * ζ ^ 23 - ((13958 / 5335) : ℂ) * ζ ^ 25 - ((2831 / 1067) : ℂ) * ζ ^ 30 - ((20501 / 5335) : ℂ) * ζ ^ 31)) * commutesA00
      + ((((5521 / 1067) : ℂ) - ((46534 / 5335) : ℂ) * ζ ^ 3 - ((1677 / 5335) : ℂ) * ζ ^ 5 - ((46534 / 5335) : ℂ) * ζ ^ 7 + ((3162 / 5335) : ℂ) * ζ ^ 10 + ((2481 / 485) : ℂ) * ζ ^ 15 + ((46534 / 5335) : ℂ) * ζ ^ 19 - ((56566 / 5335) : ℂ) * ζ ^ 20 + ((46534 / 5335) : ℂ) * ζ ^ 23 + ((31369 / 5335) : ℂ) * ζ ^ 25 - ((9557 / 5335) : ℂ) * ζ ^ 30 - ((46534 / 5335) : ℂ) * ζ ^ 31)) * commutesA01
      + ((((194 / 11) : ℂ) - ((182 / 11) : ℂ) * ζ ^ 3 - ((218 / 11) : ℂ) * ζ ^ 5 - ((182 / 11) : ℂ) * ζ ^ 7 + ((146 / 11) : ℂ) * ζ ^ 10 + ((24 / 11) : ℂ) * ζ ^ 15 + ((182 / 11) : ℂ) * ζ ^ 19 - ((128 / 11) : ℂ) * ζ ^ 20 + ((182 / 11) : ℂ) * ζ ^ 23 + ((126 / 11) : ℂ) * ζ ^ 25 - ((160 / 11) : ℂ) * ζ ^ 30 - ((182 / 11) : ℂ) * ζ ^ 31)) * commutesA02
      + (((3 : ℂ) - (2 : ℂ) * ζ ^ 3 - (3 : ℂ) * ζ ^ 5 - (2 : ℂ) * ζ ^ 7 + (4 : ℂ) * ζ ^ 10 - ζ ^ 15 + (2 : ℂ) * ζ ^ 19 - (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 23 - ζ ^ 25 - (3 : ℂ) * ζ ^ 30 - (2 : ℂ) * ζ ^ 31)) * commutesA05
      + ((((224 / 33) : ℂ) - ((94 / 11) : ℂ) * ζ ^ 3 + ((40 / 33) : ℂ) * ζ ^ 5 - ((94 / 11) : ℂ) * ζ ^ 7 - ((98 / 33) : ℂ) * ζ ^ 10 + ((180 / 11) : ℂ) * ζ ^ 15 + ((94 / 11) : ℂ) * ζ ^ 19 - ((508 / 33) : ℂ) * ζ ^ 20 + ((94 / 11) : ℂ) * ζ ^ 23 + ((412 / 33) : ℂ) * ζ ^ 25 - ((452 / 33) : ℂ) * ζ ^ 30 - ((94 / 11) : ℂ) * ζ ^ 31)) * commutesA12
      + (((2 : ℂ) - ((7 / 3) : ℂ) * ζ ^ 3 + ((5 / 3) : ℂ) * ζ ^ 5 - ((7 / 3) : ℂ) * ζ ^ 7 + ((7 / 3) : ℂ) * ζ ^ 10 + ((11 / 3) : ℂ) * ζ ^ 15 + ((7 / 3) : ℂ) * ζ ^ 19 - ζ ^ 20 + ((7 / 3) : ℂ) * ζ ^ 23 + ((8 / 3) : ℂ) * ζ ^ 25 - ((5 / 3) : ℂ) * ζ ^ 30 - ((7 / 3) : ℂ) * ζ ^ 31)) * commutesA15
      - (
        ((((33485 / 6402) : ℂ) - ((8017 / 3201) : ℂ) * ζ ^ 3 - ((33485 / 6402) : ℂ) * ζ ^ 4 - ((9633 / 1067) : ℂ) * ζ ^ 5 - ((40714 / 16005) : ℂ) * ζ ^ 6 + ((196081 / 32010) : ℂ) * ζ ^ 8 + ((9633 / 1067) : ℂ) * ζ ^ 9 - ((80503 / 32010) : ℂ) * ζ ^ 10 - ((87761 / 32010) : ℂ) * ζ ^ 13 - ((185 / 6402) : ℂ) * ζ ^ 14 - ((115 / 97) : ℂ) * ζ ^ 15 + ((801 / 970) : ℂ) * ζ ^ 18 + ((115 / 97) : ℂ) * ζ ^ 19 + ((12548 / 5335) : ℂ) * ζ ^ 20 + ((40714 / 16005) : ℂ) * ζ ^ 22 - ((13736 / 16005) : ℂ) * ζ ^ 23 - ((12548 / 5335) : ℂ) * ζ ^ 24 + ((11422 / 5335) : ℂ) * ζ ^ 25 + ((40714 / 16005) : ℂ) * ζ ^ 26 + ((20171 / 32010) : ℂ) * ζ ^ 28 - ((11422 / 5335) : ℂ) * ζ ^ 29 - ((40714 / 16005) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((-((36017 / 10670) : ℂ) + ((137769 / 10670) : ℂ) * ζ ^ 3 + ((36017 / 10670) : ℂ) * ζ ^ 4 + ((169651 / 21340) : ℂ) * ζ ^ 5 - ((33127 / 4268) : ℂ) * ζ ^ 6 - ((14419 / 21340) : ℂ) * ζ ^ 8 - ((169651 / 21340) : ℂ) * ζ ^ 9 - ((136458 / 5335) : ℂ) * ζ ^ 10 + ((278577 / 21340) : ℂ) * ζ ^ 13 + ((380197 / 21340) : ℂ) * ζ ^ 14 + ((15944 / 1067) : ℂ) * ζ ^ 15 - ((77019 / 5335) : ℂ) * ζ ^ 18 - ((15944 / 1067) : ℂ) * ζ ^ 19 - ((57028 / 5335) : ℂ) * ζ ^ 20 + ((33127 / 4268) : ℂ) * ζ ^ 22 - ((29087 / 21340) : ℂ) * ζ ^ 23 + ((57028 / 5335) : ℂ) * ζ ^ 24 + ((35138 / 5335) : ℂ) * ζ ^ 25 + ((33127 / 4268) : ℂ) * ζ ^ 26 - ((18817 / 10670) : ℂ) * ζ ^ 28 - ((35138 / 5335) : ℂ) * ζ ^ 29 - ((33127 / 4268) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((((14315 / 6402) : ℂ) - ((14437 / 2910) : ℂ) * ζ ^ 3 - ((14315 / 6402) : ℂ) * ζ ^ 4 - ((5309 / 2134) : ℂ) * ζ ^ 5 + ((827 / 485) : ℂ) * ζ ^ 6 + ((63034 / 16005) : ℂ) * ζ ^ 8 + ((5309 / 2134) : ℂ) * ζ ^ 9 + ((59597 / 32010) : ℂ) * ζ ^ 10 - ((36034 / 5335) : ℂ) * ζ ^ 13 - ((1003 / 6402) : ℂ) * ζ ^ 14 - ((368 / 1455) : ℂ) * ζ ^ 15 + ((1937 / 5335) : ℂ) * ζ ^ 18 + ((368 / 1455) : ℂ) * ζ ^ 19 + ((95939 / 32010) : ℂ) * ζ ^ 20 - ((827 / 485) : ℂ) * ζ ^ 22 - ((109339 / 32010) : ℂ) * ζ ^ 23 - ((95939 / 32010) : ℂ) * ζ ^ 24 - ((109567 / 32010) : ℂ) * ζ ^ 25 - ((827 / 485) : ℂ) * ζ ^ 26 + ((10027 / 6402) : ℂ) * ζ ^ 28 + ((109567 / 32010) : ℂ) * ζ ^ 29 + ((827 / 485) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((-((757 / 4268) : ℂ) - ((11674 / 3201) : ℂ) * ζ ^ 3 + ((757 / 4268) : ℂ) * ζ ^ 4 + ((55 / 388) : ℂ) * ζ ^ 5 + ((46534 / 16005) : ℂ) * ζ ^ 6 - ((8339 / 21340) : ℂ) * ζ ^ 8 - ((55 / 388) : ℂ) * ζ ^ 9 + ((113647 / 21340) : ℂ) * ζ ^ 10 - ((61619 / 32010) : ℂ) * ζ ^ 13 - ((30961 / 12804) : ℂ) * ζ ^ 14 - ((33223 / 12804) : ℂ) * ζ ^ 15 + ((29099 / 64020) : ℂ) * ζ ^ 18 + ((33223 / 12804) : ℂ) * ζ ^ 19 + ((104523 / 21340) : ℂ) * ζ ^ 20 - ((46534 / 16005) : ℂ) * ζ ^ 22 - ((173803 / 32010) : ℂ) * ζ ^ 23 - ((104523 / 21340) : ℂ) * ζ ^ 24 - ((71393 / 21340) : ℂ) * ζ ^ 25 - ((46534 / 16005) : ℂ) * ζ ^ 26 + ((30953 / 64020) : ℂ) * ζ ^ 28 + ((71393 / 21340) : ℂ) * ζ ^ 29 + ((46534 / 16005) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((235 / 33) : ℂ) + ((135 / 22) : ℂ) * ζ ^ 3 + ((235 / 33) : ℂ) * ζ ^ 4 + ((337 / 33) : ℂ) * ζ ^ 5 - ((235 / 33) : ℂ) * ζ ^ 8 - ((337 / 33) : ℂ) * ζ ^ 9 - ((14 / 11) : ℂ) * ζ ^ 10 + ((130 / 33) : ℂ) * ζ ^ 13 + ((14 / 11) : ℂ) * ζ ^ 14 + ((92 / 33) : ℂ) * ζ ^ 15 + ((19 / 22) : ℂ) * ζ ^ 18 - ((92 / 33) : ℂ) * ζ ^ 19 - ((69 / 11) : ℂ) * ζ ^ 20 + ((233 / 33) : ℂ) * ζ ^ 23 + ((69 / 11) : ℂ) * ζ ^ 24)) * Y 2 2
        + ((((43 / 22) : ℂ) - ((307 / 132) : ℂ) * ζ ^ 3 - ((43 / 22) : ℂ) * ζ ^ 4 + ((17 / 132) : ℂ) * ζ ^ 5 + ((16 / 33) : ℂ) * ζ ^ 6 + ((11 / 6) : ℂ) * ζ ^ 8 - ((17 / 132) : ℂ) * ζ ^ 9 + ((73 / 22) : ℂ) * ζ ^ 10 - ((31 / 33) : ℂ) * ζ ^ 13 - ((17 / 6) : ℂ) * ζ ^ 14 - ((35 / 33) : ℂ) * ζ ^ 15 + ((325 / 132) : ℂ) * ζ ^ 18 + ((35 / 33) : ℂ) * ζ ^ 19 + ((7 / 12) : ℂ) * ζ ^ 20 - ((16 / 33) : ℂ) * ζ ^ 22 + ((9 / 22) : ℂ) * ζ ^ 23 - ((7 / 12) : ℂ) * ζ ^ 24 - ((49 / 66) : ℂ) * ζ ^ 25 - ((16 / 33) : ℂ) * ζ ^ 26 + ((3 / 11) : ℂ) * ζ ^ 28 + ((49 / 66) : ℂ) * ζ ^ 29 + ((16 / 33) : ℂ) * ζ ^ 30)) * Y 4 5
        + ((((91 / 44) : ℂ) + ((1 / 66) : ℂ) * ζ ^ 3 - ((91 / 44) : ℂ) * ζ ^ 4 - ((175 / 132) : ℂ) * ζ ^ 5 - ((4 / 11) : ℂ) * ζ ^ 6 + ((61 / 44) : ℂ) * ζ ^ 8 + ((175 / 132) : ℂ) * ζ ^ 9 - ((203 / 132) : ℂ) * ζ ^ 10 + ((8 / 11) : ℂ) * ζ ^ 13 + ((155 / 132) : ℂ) * ζ ^ 14 + ((131 / 132) : ℂ) * ζ ^ 15 - ((283 / 132) : ℂ) * ζ ^ 18 - ((131 / 132) : ℂ) * ζ ^ 19 - ((43 / 44) : ℂ) * ζ ^ 20 + ((4 / 11) : ℂ) * ζ ^ 22 - ((17 / 22) : ℂ) * ζ ^ 23 + ((43 / 44) : ℂ) * ζ ^ 24 + ((53 / 44) : ℂ) * ζ ^ 25 + ((4 / 11) : ℂ) * ζ ^ 26 - ((49 / 44) : ℂ) * ζ ^ 28 - ((53 / 44) : ℂ) * ζ ^ 29 - ((4 / 11) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row13_reducedY22
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow13TransformedGeneratorA =
        alternatingSixAmbientRow13TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow13GeneratorBDiagonal =
        alternatingSixAmbientRow13GeneratorBDiagonal * Y) :
    Y 2 2 = Y 5 5 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
    ((-((6177 / 1067) : ℂ) - ((998 / 5335) : ℂ) * ζ ^ 3 + ((26056 / 5335) : ℂ) * ζ ^ 5 - ((998 / 5335) : ℂ) * ζ ^ 7 - ((9561 / 5335) : ℂ) * ζ ^ 10 + ((46792 / 5335) : ℂ) * ζ ^ 15 + ((998 / 5335) : ℂ) * ζ ^ 19 - ((8587 / 5335) : ℂ) * ζ ^ 20 + ((998 / 5335) : ℂ) * ζ ^ 23 - ((802 / 5335) : ℂ) * ζ ^ 25 - ((9854 / 5335) : ℂ) * ζ ^ 30 - ((998 / 5335) : ℂ) * ζ ^ 31)) * commutesA00
      + ((-((23952 / 5335) : ℂ) + ((16694 / 5335) : ℂ) * ζ ^ 3 + ((29134 / 5335) : ℂ) * ζ ^ 5 + ((16694 / 5335) : ℂ) * ζ ^ 7 - ((2331 / 1067) : ℂ) * ζ ^ 10 - ((3172 / 485) : ℂ) * ζ ^ 15 - ((16694 / 5335) : ℂ) * ζ ^ 19 + ((5013 / 1067) : ℂ) * ζ ^ 20 - ((16694 / 5335) : ℂ) * ζ ^ 23 - ((39636 / 5335) : ℂ) * ζ ^ 25 + ((52241 / 5335) : ℂ) * ζ ^ 30 + ((16694 / 5335) : ℂ) * ζ ^ 31)) * commutesA01
      + ((-((224 / 11) : ℂ) + ((181 / 11) : ℂ) * ζ ^ 3 + ((211 / 11) : ℂ) * ζ ^ 5 + ((181 / 11) : ℂ) * ζ ^ 7 - ((239 / 11) : ℂ) * ζ ^ 10 + ((13 / 11) : ℂ) * ζ ^ 15 - ((181 / 11) : ℂ) * ζ ^ 19 + ((15 / 11) : ℂ) * ζ ^ 20 - ((181 / 11) : ℂ) * ζ ^ 23 - ((94 / 11) : ℂ) * ζ ^ 25 + ((137 / 11) : ℂ) * ζ ^ 30 + ((181 / 11) : ℂ) * ζ ^ 31)) * commutesA02
      + (((3 : ℂ) - (2 : ℂ) * ζ ^ 3 - (3 : ℂ) * ζ ^ 5 - (2 : ℂ) * ζ ^ 7 + (4 : ℂ) * ζ ^ 10 - ζ ^ 15 + (2 : ℂ) * ζ ^ 19 - (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 23 - ζ ^ 25 - (3 : ℂ) * ζ ^ 30 - (2 : ℂ) * ζ ^ 31)) * commutesA05
      + ((-((359 / 33) : ℂ) + ((499 / 33) : ℂ) * ζ ^ 3 + ((94 / 11) : ℂ) * ζ ^ 5 + ((499 / 33) : ℂ) * ζ ^ 7 - ((65 / 33) : ℂ) * ζ ^ 10 - ((560 / 33) : ℂ) * ζ ^ 15 - ((499 / 33) : ℂ) * ζ ^ 19 + ((625 / 33) : ℂ) * ζ ^ 20 - ((499 / 33) : ℂ) * ζ ^ 23 - ((211 / 11) : ℂ) * ζ ^ 25 + ((538 / 33) : ℂ) * ζ ^ 30 + ((499 / 33) : ℂ) * ζ ^ 31)) * commutesA12
      + (((2 : ℂ) - ((7 / 3) : ℂ) * ζ ^ 3 + ((5 / 3) : ℂ) * ζ ^ 5 - ((7 / 3) : ℂ) * ζ ^ 7 + ((7 / 3) : ℂ) * ζ ^ 10 + ((11 / 3) : ℂ) * ζ ^ 15 + ((7 / 3) : ℂ) * ζ ^ 19 - ζ ^ 20 + ((7 / 3) : ℂ) * ζ ^ 23 + ((8 / 3) : ℂ) * ζ ^ 25 - ((5 / 3) : ℂ) * ζ ^ 30 - ((7 / 3) : ℂ) * ζ ^ 31)) * commutesA15
      - (
        ((-((41583 / 4268) : ℂ) + ((186811 / 32010) : ℂ) * ζ ^ 3 + ((41583 / 4268) : ℂ) * ζ ^ 4 + ((103271 / 12804) : ℂ) * ζ ^ 5 + ((22514 / 16005) : ℂ) * ζ ^ 6 - ((443189 / 64020) : ℂ) * ζ ^ 8 - ((103271 / 12804) : ℂ) * ζ ^ 9 - ((22096 / 16005) : ℂ) * ζ ^ 10 + ((254 / 1067) : ℂ) * ζ ^ 13 + ((2974 / 1067) : ℂ) * ζ ^ 14 + ((5621 / 5820) : ℂ) * ζ ^ 15 - ((1135 / 291) : ℂ) * ζ ^ 18 - ((5621 / 5820) : ℂ) * ζ ^ 19 + ((153623 / 64020) : ℂ) * ζ ^ 20 - ((22514 / 16005) : ℂ) * ζ ^ 22 + ((31057 / 21340) : ℂ) * ζ ^ 23 - ((153623 / 64020) : ℂ) * ζ ^ 24 - ((18152 / 3201) : ℂ) * ζ ^ 25 - ((22514 / 16005) : ℂ) * ζ ^ 26 + ((143767 / 32010) : ℂ) * ζ ^ 28 + ((18152 / 3201) : ℂ) * ζ ^ 29 + ((22514 / 16005) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((12191 / 1067) : ℂ) - ((39119 / 5335) : ℂ) * ζ ^ 3 - ((12191 / 1067) : ℂ) * ζ ^ 4 - ((185517 / 21340) : ℂ) * ζ ^ 5 + ((33887 / 10670) : ℂ) * ζ ^ 6 + ((155893 / 10670) : ℂ) * ζ ^ 8 + ((185517 / 21340) : ℂ) * ζ ^ 9 + ((373251 / 21340) : ℂ) * ζ ^ 10 - ((332847 / 21340) : ℂ) * ζ ^ 13 - ((305477 / 21340) : ℂ) * ζ ^ 14 - ((529649 / 21340) : ℂ) * ζ ^ 15 + ((49492 / 5335) : ℂ) * ζ ^ 18 + ((529649 / 21340) : ℂ) * ζ ^ 19 + ((58703 / 5335) : ℂ) * ζ ^ 20 - ((33887 / 10670) : ℂ) * ζ ^ 22 - ((126243 / 10670) : ℂ) * ζ ^ 23 - ((58703 / 5335) : ℂ) * ζ ^ 24 - ((124149 / 10670) : ℂ) * ζ ^ 25 - ((33887 / 10670) : ℂ) * ζ ^ 26 + ((90263 / 21340) : ℂ) * ζ ^ 28 + ((124149 / 10670) : ℂ) * ζ ^ 29 + ((33887 / 10670) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((-((112753 / 12804) : ℂ) + ((3943 / 388) : ℂ) * ζ ^ 3 + ((112753 / 12804) : ℂ) * ζ ^ 4 + ((64759 / 12804) : ℂ) * ζ ^ 5 + ((236 / 485) : ℂ) * ζ ^ 6 - ((217813 / 21340) : ℂ) * ζ ^ 8 - ((64759 / 12804) : ℂ) * ζ ^ 9 - ((23612 / 16005) : ℂ) * ζ ^ 10 + ((16579 / 64020) : ℂ) * ζ ^ 13 + ((6280 / 3201) : ℂ) * ζ ^ 14 + ((1079 / 388) : ℂ) * ζ ^ 15 - ((27191 / 5335) : ℂ) * ζ ^ 18 - ((1079 / 388) : ℂ) * ζ ^ 19 - ((151487 / 64020) : ℂ) * ζ ^ 20 - ((236 / 485) : ℂ) * ζ ^ 22 + ((17404 / 5335) : ℂ) * ζ ^ 23 + ((151487 / 64020) : ℂ) * ζ ^ 24 - ((20653 / 10670) : ℂ) * ζ ^ 25 - ((236 / 485) : ℂ) * ζ ^ 26 + ((41533 / 32010) : ℂ) * ζ ^ 28 + ((20653 / 10670) : ℂ) * ζ ^ 29 + ((236 / 485) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((((15527 / 12804) : ℂ) - ((89897 / 64020) : ℂ) * ζ ^ 3 - ((15527 / 12804) : ℂ) * ζ ^ 4 + ((208 / 291) : ℂ) * ζ ^ 5 - ((16694 / 16005) : ℂ) * ζ ^ 6 - ((19757 / 21340) : ℂ) * ζ ^ 8 - ((208 / 291) : ℂ) * ζ ^ 9 + ((22909 / 64020) : ℂ) * ζ ^ 10 - ((8993 / 6402) : ℂ) * ζ ^ 13 - ((5979 / 4268) : ℂ) * ζ ^ 14 - ((149131 / 64020) : ℂ) * ζ ^ 15 + ((23252 / 3201) : ℂ) * ζ ^ 18 + ((149131 / 64020) : ℂ) * ζ ^ 19 - ((149107 / 16005) : ℂ) * ζ ^ 20 + ((16694 / 16005) : ℂ) * ζ ^ 22 + ((104141 / 16005) : ℂ) * ζ ^ 23 + ((149107 / 16005) : ℂ) * ζ ^ 24 + ((57185 / 12804) : ℂ) * ζ ^ 25 + ((16694 / 16005) : ℂ) * ζ ^ 26 - ((216239 / 64020) : ℂ) * ζ ^ 28 - ((57185 / 12804) : ℂ) * ζ ^ 29 - ((16694 / 16005) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((((853 / 132) : ℂ) - ((587 / 132) : ℂ) * ζ ^ 3 - ((853 / 132) : ℂ) * ζ ^ 4 - ((82 / 11) : ℂ) * ζ ^ 5 + ((853 / 132) : ℂ) * ζ ^ 8 + ((82 / 11) : ℂ) * ζ ^ 9 + ((169 / 66) : ℂ) * ζ ^ 10 + ((29 / 66) : ℂ) * ζ ^ 13 - ((169 / 66) : ℂ) * ζ ^ 14 + ((49 / 132) : ℂ) * ζ ^ 15 - ((161 / 132) : ℂ) * ζ ^ 18 - ((49 / 132) : ℂ) * ζ ^ 19 + ((521 / 66) : ℂ) * ζ ^ 20 - ((949 / 132) : ℂ) * ζ ^ 23 - ((521 / 66) : ℂ) * ζ ^ 24)) * Y 2 2
        + ((((43 / 22) : ℂ) - ((307 / 132) : ℂ) * ζ ^ 3 - ((43 / 22) : ℂ) * ζ ^ 4 + ((17 / 132) : ℂ) * ζ ^ 5 + ((16 / 33) : ℂ) * ζ ^ 6 + ((11 / 6) : ℂ) * ζ ^ 8 - ((17 / 132) : ℂ) * ζ ^ 9 + ((73 / 22) : ℂ) * ζ ^ 10 - ((31 / 33) : ℂ) * ζ ^ 13 - ((17 / 6) : ℂ) * ζ ^ 14 - ((35 / 33) : ℂ) * ζ ^ 15 + ((325 / 132) : ℂ) * ζ ^ 18 + ((35 / 33) : ℂ) * ζ ^ 19 + ((7 / 12) : ℂ) * ζ ^ 20 - ((16 / 33) : ℂ) * ζ ^ 22 + ((9 / 22) : ℂ) * ζ ^ 23 - ((7 / 12) : ℂ) * ζ ^ 24 - ((49 / 66) : ℂ) * ζ ^ 25 - ((16 / 33) : ℂ) * ζ ^ 26 + ((3 / 11) : ℂ) * ζ ^ 28 + ((49 / 66) : ℂ) * ζ ^ 29 + ((16 / 33) : ℂ) * ζ ^ 30)) * Y 4 5
        + ((((91 / 44) : ℂ) + ((1 / 66) : ℂ) * ζ ^ 3 - ((91 / 44) : ℂ) * ζ ^ 4 - ((175 / 132) : ℂ) * ζ ^ 5 - ((4 / 11) : ℂ) * ζ ^ 6 + ((61 / 44) : ℂ) * ζ ^ 8 + ((175 / 132) : ℂ) * ζ ^ 9 - ((203 / 132) : ℂ) * ζ ^ 10 + ((8 / 11) : ℂ) * ζ ^ 13 + ((155 / 132) : ℂ) * ζ ^ 14 + ((131 / 132) : ℂ) * ζ ^ 15 - ((283 / 132) : ℂ) * ζ ^ 18 - ((131 / 132) : ℂ) * ζ ^ 19 - ((43 / 44) : ℂ) * ζ ^ 20 + ((4 / 11) : ℂ) * ζ ^ 22 - ((17 / 22) : ℂ) * ζ ^ 23 + ((43 / 44) : ℂ) * ζ ^ 24 + ((53 / 44) : ℂ) * ζ ^ 25 + ((4 / 11) : ℂ) * ζ ^ 26 - ((49 / 44) : ℂ) * ζ ^ 28 - ((53 / 44) : ℂ) * ζ ^ 29 - ((4 / 11) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row13_reducedY33
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow13TransformedGeneratorA =
        alternatingSixAmbientRow13TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow13GeneratorBDiagonal =
        alternatingSixAmbientRow13GeneratorBDiagonal * Y) :
    Y 3 3 = Y 5 5 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 3 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 3 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
      alternatingSixCyclotomicValue] at commutesA03
  simp only [
      hY02,
      hY03,
      hY04,
      hY05,
      hY13,
      hY23,
      hY43,
      hY53] at commutesA03
  have commutesA05 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (5 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA05
  simp only [Fin.sum_univ_succ] at commutesA05
  simp [
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
    ((-((60761 / 5335) : ℂ) + ((22476 / 5335) : ℂ) * ζ ^ 3 + ((40994 / 5335) : ℂ) * ζ ^ 5 + ((22476 / 5335) : ℂ) * ζ ^ 7 - ((28767 / 5335) : ℂ) * ζ ^ 10 + ((44658 / 5335) : ℂ) * ζ ^ 15 - ((22476 / 5335) : ℂ) * ζ ^ 19 + ((27691 / 5335) : ℂ) * ζ ^ 20 - ((22476 / 5335) : ℂ) * ζ ^ 23 - ((22142 / 5335) : ℂ) * ζ ^ 25 - ((1544 / 1067) : ℂ) * ζ ^ 30 + ((22476 / 5335) : ℂ) * ζ ^ 31)) * commutesA00
      + ((-((30354 / 5335) : ℂ) + ((778 / 1067) : ℂ) * ζ ^ 3 + ((18464 / 5335) : ℂ) * ζ ^ 5 + ((778 / 1067) : ℂ) * ζ ^ 7 + ((22489 / 5335) : ℂ) * ζ ^ 10 - ((4142 / 485) : ℂ) * ζ ^ 15 - ((778 / 1067) : ℂ) * ζ ^ 19 + ((50673 / 5335) : ℂ) * ζ ^ 20 - ((778 / 1067) : ℂ) * ζ ^ 23 - ((54574 / 5335) : ℂ) * ζ ^ 25 + ((37303 / 5335) : ℂ) * ζ ^ 30 + ((778 / 1067) : ℂ) * ζ ^ 31)) * commutesA01
      + ((-((312 / 11) : ℂ) + ((291 / 11) : ℂ) * ζ ^ 3 + ((277 / 11) : ℂ) * ζ ^ 5 + ((291 / 11) : ℂ) * ζ ^ 7 - ((217 / 11) : ℂ) * ζ ^ 10 - ((141 / 11) : ℂ) * ζ ^ 15 - ((291 / 11) : ℂ) * ζ ^ 19 + ((169 / 11) : ℂ) * ζ ^ 20 - ((291 / 11) : ℂ) * ζ ^ 23 - ((226 / 11) : ℂ) * ζ ^ 25 + ((247 / 11) : ℂ) * ζ ^ 30 + ((291 / 11) : ℂ) * ζ ^ 31)) * commutesA02
      + ((-(2 : ℂ) + ((4 / 5) : ℂ) * ζ ^ 3 + ((2 / 5) : ℂ) * ζ ^ 5 + ((4 / 5) : ℂ) * ζ ^ 7 + ((8 / 5) : ℂ) * ζ ^ 10 - ((6 / 5) : ℂ) * ζ ^ 15 - ((4 / 5) : ℂ) * ζ ^ 19 + ((16 / 5) : ℂ) * ζ ^ 20 - ((4 / 5) : ℂ) * ζ ^ 23 + ((6 / 5) : ℂ) * ζ ^ 25 - ((18 / 5) : ℂ) * ζ ^ 30 + ((4 / 5) : ℂ) * ζ ^ 31)) * commutesA03
      + (((3 : ℂ) - (2 : ℂ) * ζ ^ 3 - (3 : ℂ) * ζ ^ 5 - (2 : ℂ) * ζ ^ 7 + (4 : ℂ) * ζ ^ 10 - ζ ^ 15 + (2 : ℂ) * ζ ^ 19 - (2 : ℂ) * ζ ^ 20 + (2 : ℂ) * ζ ^ 23 - ζ ^ 25 - (3 : ℂ) * ζ ^ 30 - (2 : ℂ) * ζ ^ 31)) * commutesA05
      + ((-((17 / 11) : ℂ) + ((137 / 11) : ℂ) * ζ ^ 3 - ((38 / 11) : ℂ) * ζ ^ 5 + ((137 / 11) : ℂ) * ζ ^ 7 + ((81 / 11) : ℂ) * ζ ^ 10 - ((260 / 11) : ℂ) * ζ ^ 15 - ((137 / 11) : ℂ) * ζ ^ 19 + ((223 / 11) : ℂ) * ζ ^ 20 - ((137 / 11) : ℂ) * ζ ^ 23 - ((211 / 11) : ℂ) * ζ ^ 25 + ((194 / 11) : ℂ) * ζ ^ 30 + ((137 / 11) : ℂ) * ζ ^ 31)) * commutesA12
      + (((2 : ℂ) - ((7 / 3) : ℂ) * ζ ^ 3 + ((5 / 3) : ℂ) * ζ ^ 5 - ((7 / 3) : ℂ) * ζ ^ 7 + ((7 / 3) : ℂ) * ζ ^ 10 + ((11 / 3) : ℂ) * ζ ^ 15 + ((7 / 3) : ℂ) * ζ ^ 19 - ζ ^ 20 + ((7 / 3) : ℂ) * ζ ^ 23 + ((8 / 3) : ℂ) * ζ ^ 25 - ((5 / 3) : ℂ) * ζ ^ 30 - ((7 / 3) : ℂ) * ζ ^ 31)) * commutesA15
      - (
        ((-((52253 / 4268) : ℂ) + ((353263 / 32010) : ℂ) * ζ ^ 3 + ((52253 / 4268) : ℂ) * ζ ^ 4 + ((716951 / 64020) : ℂ) * ζ ^ 5 + ((1942 / 3201) : ℂ) * ζ ^ 6 - ((126623 / 12804) : ℂ) * ζ ^ 8 - ((716951 / 64020) : ℂ) * ζ ^ 9 - ((5839 / 10670) : ℂ) * ζ ^ 10 + ((21797 / 6402) : ℂ) * ζ ^ 13 + ((36937 / 32010) : ℂ) * ζ ^ 14 - ((1489 / 1940) : ℂ) * ζ ^ 15 - ((8537 / 2910) : ℂ) * ζ ^ 18 + ((1489 / 1940) : ℂ) * ζ ^ 19 - ((19231 / 64020) : ℂ) * ζ ^ 20 - ((1942 / 3201) : ℂ) * ζ ^ 22 + ((135851 / 64020) : ℂ) * ζ ^ 23 + ((19231 / 64020) : ℂ) * ζ ^ 24 - ((21006 / 5335) : ℂ) * ζ ^ 25 - ((1942 / 3201) : ℂ) * ζ ^ 26 + ((113891 / 32010) : ℂ) * ζ ^ 28 + ((21006 / 5335) : ℂ) * ζ ^ 29 + ((1942 / 3201) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((208337 / 10670) : ℂ) - ((83933 / 5335) : ℂ) * ζ ^ 3 - ((208337 / 10670) : ℂ) * ζ ^ 4 - ((283681 / 21340) : ℂ) * ζ ^ 5 + ((1472 / 5335) : ℂ) * ζ ^ 6 + ((112624 / 5335) : ℂ) * ζ ^ 8 + ((283681 / 21340) : ℂ) * ζ ^ 9 + ((96417 / 4268) : ℂ) * ζ ^ 10 - ((322177 / 21340) : ℂ) * ζ ^ 13 - ((476197 / 21340) : ℂ) * ζ ^ 14 - ((693967 / 21340) : ℂ) * ζ ^ 15 + ((37509 / 2134) : ℂ) * ζ ^ 18 + ((693967 / 21340) : ℂ) * ζ ^ 19 + ((24577 / 10670) : ℂ) * ζ ^ 20 - ((1472 / 5335) : ℂ) * ζ ^ 22 - ((11591 / 2134) : ℂ) * ζ ^ 23 - ((24577 / 10670) : ℂ) * ζ ^ 24 - ((33799 / 5335) : ℂ) * ζ ^ 25 - ((1472 / 5335) : ℂ) * ζ ^ 26 + ((24109 / 21340) : ℂ) * ζ ^ 28 + ((33799 / 5335) : ℂ) * ζ ^ 29 + ((1472 / 5335) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((-((82877 / 12804) : ℂ) + ((72919 / 5820) : ℂ) * ζ ^ 3 + ((82877 / 12804) : ℂ) * ζ ^ 4 + ((2873 / 12804) : ℂ) * ζ ^ 5 - ((1426 / 1455) : ℂ) * ζ ^ 6 - ((187937 / 21340) : ℂ) * ζ ^ 8 - ((2873 / 12804) : ℂ) * ζ ^ 9 - ((142187 / 32010) : ℂ) * ζ ^ 10 - ((18659 / 21340) : ℂ) * ζ ^ 13 + ((22163 / 6402) : ℂ) * ζ ^ 14 + ((9469 / 1940) : ℂ) * ζ ^ 15 - ((76789 / 10670) : ℂ) * ζ ^ 18 - ((9469 / 1940) : ℂ) * ζ ^ 19 - ((202703 / 64020) : ℂ) * ζ ^ 20 + ((1426 / 1455) : ℂ) * ζ ^ 22 + ((78887 / 16005) : ℂ) * ζ ^ 23 + ((202703 / 64020) : ℂ) * ζ ^ 24 - ((3581 / 10670) : ℂ) * ζ ^ 25 + ((1426 / 1455) : ℂ) * ζ ^ 26 + ((7453 / 6402) : ℂ) * ζ ^ 28 + ((3581 / 10670) : ℂ) * ζ ^ 29 - ((1426 / 1455) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((-((6917 / 4268) : ℂ) - ((28543 / 21340) : ℂ) * ζ ^ 3 + ((6917 / 4268) : ℂ) * ζ ^ 4 + ((559 / 194) : ℂ) * ζ ^ 5 - ((778 / 3201) : ℂ) * ζ ^ 6 - ((197981 / 64020) : ℂ) * ζ ^ 8 - ((559 / 194) : ℂ) * ζ ^ 9 - ((17185 / 12804) : ℂ) * ζ ^ 10 - ((27284 / 16005) : ℂ) * ζ ^ 13 + ((4691 / 4268) : ℂ) * ζ ^ 14 + ((183773 / 64020) : ℂ) * ζ ^ 15 + ((165299 / 32010) : ℂ) * ζ ^ 18 - ((183773 / 64020) : ℂ) * ζ ^ 19 - ((138437 / 16005) : ℂ) * ζ ^ 20 + ((778 / 3201) : ℂ) * ζ ^ 22 + ((124414 / 16005) : ℂ) * ζ ^ 23 + ((138437 / 16005) : ℂ) * ζ ^ 24 + ((58319 / 21340) : ℂ) * ζ ^ 25 + ((778 / 3201) : ℂ) * ζ ^ 26 - ((156487 / 64020) : ℂ) * ζ ^ 28 - ((58319 / 21340) : ℂ) * ζ ^ 29 - ((778 / 3201) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((((607 / 44) : ℂ) - ((445 / 44) : ℂ) * ζ ^ 3 - ((607 / 44) : ℂ) * ζ ^ 4 - ((148 / 11) : ℂ) * ζ ^ 5 + ((607 / 44) : ℂ) * ζ ^ 8 + ((148 / 11) : ℂ) * ζ ^ 9 + ((93 / 22) : ℂ) * ζ ^ 10 - ((41 / 11) : ℂ) * ζ ^ 13 - ((93 / 22) : ℂ) * ζ ^ 14 - ((167 / 44) : ℂ) * ζ ^ 15 + ((49 / 44) : ℂ) * ζ ^ 18 + ((167 / 44) : ℂ) * ζ ^ 19 + ((107 / 11) : ℂ) * ζ ^ 20 - ((441 / 44) : ℂ) * ζ ^ 23 - ((107 / 11) : ℂ) * ζ ^ 24)) * Y 2 2
        + ((-(2 : ℂ) + ((2 / 5) : ℂ) * ζ ^ 3 + (2 : ℂ) * ζ ^ 4 + ((7 / 10) : ℂ) * ζ ^ 5 - ((11 / 5) : ℂ) * ζ ^ 8 - ((7 / 10) : ℂ) * ζ ^ 9 - ((4 / 5) : ℂ) * ζ ^ 10 + ((13 / 10) : ℂ) * ζ ^ 13 + ((4 / 5) : ℂ) * ζ ^ 14 + ((7 / 10) : ℂ) * ζ ^ 15 - ((6 / 5) : ℂ) * ζ ^ 18 - ((7 / 10) : ℂ) * ζ ^ 19 + ((1 / 5) : ℂ) * ζ ^ 20 + ((9 / 10) : ℂ) * ζ ^ 23 - ((1 / 5) : ℂ) * ζ ^ 24)) * Y 3 3
        + ((((43 / 22) : ℂ) - ((307 / 132) : ℂ) * ζ ^ 3 - ((43 / 22) : ℂ) * ζ ^ 4 + ((17 / 132) : ℂ) * ζ ^ 5 + ((16 / 33) : ℂ) * ζ ^ 6 + ((11 / 6) : ℂ) * ζ ^ 8 - ((17 / 132) : ℂ) * ζ ^ 9 + ((73 / 22) : ℂ) * ζ ^ 10 - ((31 / 33) : ℂ) * ζ ^ 13 - ((17 / 6) : ℂ) * ζ ^ 14 - ((35 / 33) : ℂ) * ζ ^ 15 + ((325 / 132) : ℂ) * ζ ^ 18 + ((35 / 33) : ℂ) * ζ ^ 19 + ((7 / 12) : ℂ) * ζ ^ 20 - ((16 / 33) : ℂ) * ζ ^ 22 + ((9 / 22) : ℂ) * ζ ^ 23 - ((7 / 12) : ℂ) * ζ ^ 24 - ((49 / 66) : ℂ) * ζ ^ 25 - ((16 / 33) : ℂ) * ζ ^ 26 + ((3 / 11) : ℂ) * ζ ^ 28 + ((49 / 66) : ℂ) * ζ ^ 29 + ((16 / 33) : ℂ) * ζ ^ 30)) * Y 4 5
        + ((((91 / 44) : ℂ) + ((1 / 66) : ℂ) * ζ ^ 3 - ((91 / 44) : ℂ) * ζ ^ 4 - ((175 / 132) : ℂ) * ζ ^ 5 - ((4 / 11) : ℂ) * ζ ^ 6 + ((61 / 44) : ℂ) * ζ ^ 8 + ((175 / 132) : ℂ) * ζ ^ 9 - ((203 / 132) : ℂ) * ζ ^ 10 + ((8 / 11) : ℂ) * ζ ^ 13 + ((155 / 132) : ℂ) * ζ ^ 14 + ((131 / 132) : ℂ) * ζ ^ 15 - ((283 / 132) : ℂ) * ζ ^ 18 - ((131 / 132) : ℂ) * ζ ^ 19 - ((43 / 44) : ℂ) * ζ ^ 20 + ((4 / 11) : ℂ) * ζ ^ 22 - ((17 / 22) : ℂ) * ζ ^ 23 + ((43 / 44) : ℂ) * ζ ^ 24 + ((53 / 44) : ℂ) * ζ ^ 25 + ((4 / 11) : ℂ) * ζ ^ 26 - ((49 / 44) : ℂ) * ζ ^ 28 - ((53 / 44) : ℂ) * ζ ^ 29 - ((4 / 11) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row13_reducedY45
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow13TransformedGeneratorA =
        alternatingSixAmbientRow13TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow13GeneratorBDiagonal =
        alternatingSixAmbientRow13GeneratorBDiagonal * Y) :
    Y 4 5 = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
    ((((5411 / 1067) : ℂ) - ((26437 / 5335) : ℂ) * ζ ^ 3 + ((6474 / 5335) : ℂ) * ζ ^ 5 - ((26437 / 5335) : ℂ) * ζ ^ 7 + ((8761 / 5335) : ℂ) * ζ ^ 10 - ((1502 / 485) : ℂ) * ζ ^ 15 + ((26437 / 5335) : ℂ) * ζ ^ 19 - ((16493 / 5335) : ℂ) * ζ ^ 20 + ((26437 / 5335) : ℂ) * ζ ^ 23 + ((6817 / 5335) : ℂ) * ζ ^ 25 + ((28954 / 5335) : ℂ) * ζ ^ 30 - ((26437 / 5335) : ℂ) * ζ ^ 31)) * commutesA00
      + ((((16382 / 5335) : ℂ) + ((10391 / 5335) : ℂ) * ζ ^ 3 - ((30359 / 5335) : ℂ) * ζ ^ 5 + ((10391 / 5335) : ℂ) * ζ ^ 7 - ((5843 / 1067) : ℂ) * ζ ^ 10 - ((723 / 5335) : ℂ) * ζ ^ 15 - ((10391 / 5335) : ℂ) * ζ ^ 19 - ((51 / 97) : ℂ) * ζ ^ 20 - ((10391 / 5335) : ℂ) * ζ ^ 23 + ((45906 / 5335) : ℂ) * ζ ^ 25 - ((14581 / 5335) : ℂ) * ζ ^ 30 + ((10391 / 5335) : ℂ) * ζ ^ 31)) * commutesA01
      + ((((120 / 11) : ℂ) - ((98 / 11) : ℂ) * ζ ^ 3 - ((118 / 11) : ℂ) * ζ ^ 5 - ((98 / 11) : ℂ) * ζ ^ 7 + ((92 / 11) : ℂ) * ζ ^ 10 + ((16 / 11) : ℂ) * ζ ^ 15 + ((98 / 11) : ℂ) * ζ ^ 19 - ((62 / 11) : ℂ) * ζ ^ 20 + ((98 / 11) : ℂ) * ζ ^ 23 + ((52 / 11) : ℂ) * ζ ^ 25 - ((78 / 11) : ℂ) * ζ ^ 30 - ((98 / 11) : ℂ) * ζ ^ 31)) * commutesA02
      + (((2 : ℂ) + (2 : ℂ) * ζ ^ 3 + (4 : ℂ) * ζ ^ 5 + (2 : ℂ) * ζ ^ 7 - (2 : ℂ) * ζ ^ 10 - (2 : ℂ) * ζ ^ 19 - (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 23 - (2 : ℂ) * ζ ^ 25 + (2 : ℂ) * ζ ^ 30 + (2 : ℂ) * ζ ^ 31)) * commutesA05
      + ((((140 / 33) : ℂ) - ((218 / 33) : ℂ) * ζ ^ 3 + ((8 / 33) : ℂ) * ζ ^ 5 - ((218 / 33) : ℂ) * ζ ^ 7 - ((10 / 11) : ℂ) * ζ ^ 10 + ((26 / 3) : ℂ) * ζ ^ 15 + ((218 / 33) : ℂ) * ζ ^ 19 - ((262 / 33) : ℂ) * ζ ^ 20 + ((218 / 33) : ℂ) * ζ ^ 23 + ((260 / 33) : ℂ) * ζ ^ 25 - ((92 / 11) : ℂ) * ζ ^ 30 - ((218 / 33) : ℂ) * ζ ^ 31)) * commutesA12
      + ((-((4 / 3) : ℂ) + ((2 / 3) : ℂ) * ζ ^ 3 + ((2 / 3) : ℂ) * ζ ^ 7 - ((4 / 3) : ℂ) * ζ ^ 10 - ((4 / 3) : ℂ) * ζ ^ 15 - ((2 / 3) : ℂ) * ζ ^ 19 + ((14 / 3) : ℂ) * ζ ^ 20 - ((2 / 3) : ℂ) * ζ ^ 23 + (2 : ℂ) * ζ ^ 25 + ((8 / 3) : ℂ) * ζ ^ 30 + ((2 / 3) : ℂ) * ζ ^ 31)) * commutesA15
      - (
        ((((10309 / 3201) : ℂ) - ((355997 / 64020) : ℂ) * ζ ^ 3 - ((10309 / 3201) : ℂ) * ζ ^ 4 - ((68581 / 12804) : ℂ) * ζ ^ 5 + ((4571 / 16005) : ℂ) * ζ ^ 6 + ((757 / 5335) : ℂ) * ζ ^ 8 + ((68581 / 12804) : ℂ) * ζ ^ 9 + ((79863 / 21340) : ℂ) * ζ ^ 10 - ((14237 / 3201) : ℂ) * ζ ^ 13 - ((44261 / 12804) : ℂ) * ζ ^ 14 + ((136219 / 64020) : ℂ) * ζ ^ 15 + ((43183 / 12804) : ℂ) * ζ ^ 18 - ((136219 / 64020) : ℂ) * ζ ^ 19 - ((78779 / 32010) : ℂ) * ζ ^ 20 - ((4571 / 16005) : ℂ) * ζ ^ 22 + ((17509 / 10670) : ℂ) * ζ ^ 23 + ((78779 / 32010) : ℂ) * ζ ^ 24 + ((4621 / 3201) : ℂ) * ζ ^ 25 - ((4571 / 16005) : ℂ) * ζ ^ 26 - ((2516 / 1455) : ℂ) * ζ ^ 28 - ((4621 / 3201) : ℂ) * ζ ^ 29 + ((4571 / 16005) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((-((7933 / 1067) : ℂ) + ((199511 / 21340) : ℂ) * ζ ^ 3 + ((7933 / 1067) : ℂ) * ζ ^ 4 + ((9073 / 5335) : ℂ) * ζ ^ 5 + ((68001 / 21340) : ℂ) * ζ ^ 6 - ((291141 / 21340) : ℂ) * ζ ^ 8 - ((9073 / 5335) : ℂ) * ζ ^ 9 - ((72271 / 21340) : ℂ) * ζ ^ 10 - ((18963 / 21340) : ℂ) * ζ ^ 13 + ((3188 / 485) : ℂ) * ζ ^ 14 + ((16887 / 970) : ℂ) * ζ ^ 15 - ((192323 / 21340) : ℂ) * ζ ^ 18 - ((16887 / 970) : ℂ) * ζ ^ 19 - ((37957 / 21340) : ℂ) * ζ ^ 20 - ((68001 / 21340) : ℂ) * ζ ^ 22 + ((179941 / 21340) : ℂ) * ζ ^ 23 + ((37957 / 21340) : ℂ) * ζ ^ 24 + ((90023 / 21340) : ℂ) * ζ ^ 25 - ((68001 / 21340) : ℂ) * ζ ^ 26 + ((1351 / 10670) : ℂ) * ζ ^ 28 - ((90023 / 21340) : ℂ) * ζ ^ 29 + ((68001 / 21340) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((((62363 / 12804) : ℂ) - ((91343 / 12804) : ℂ) * ζ ^ 3 - ((62363 / 12804) : ℂ) * ζ ^ 4 + ((5953 / 6402) : ℂ) * ζ ^ 5 + ((2227 / 1455) : ℂ) * ζ ^ 6 + ((92073 / 21340) : ℂ) * ζ ^ 8 - ((5953 / 6402) : ℂ) * ζ ^ 9 + ((45017 / 16005) : ℂ) * ζ ^ 10 + ((11307 / 21340) : ℂ) * ζ ^ 13 - ((1368 / 1067) : ℂ) * ζ ^ 14 - ((23833 / 12804) : ℂ) * ζ ^ 15 + ((9491 / 2910) : ℂ) * ζ ^ 18 + ((23833 / 12804) : ℂ) * ζ ^ 19 - ((11779 / 32010) : ℂ) * ζ ^ 20 - ((2227 / 1455) : ℂ) * ζ ^ 22 - ((59197 / 16005) : ℂ) * ζ ^ 23 + ((11779 / 32010) : ℂ) * ζ ^ 24 + ((14642 / 16005) : ℂ) * ζ ^ 25 - ((2227 / 1455) : ℂ) * ζ ^ 26 - ((46414 / 16005) : ℂ) * ζ ^ 28 - ((14642 / 16005) : ℂ) * ζ ^ 29 + ((2227 / 1455) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((-((151 / 6402) : ℂ) + ((99917 / 64020) : ℂ) * ζ ^ 3 + ((151 / 6402) : ℂ) * ζ ^ 4 - ((33463 / 12804) : ℂ) * ζ ^ 5 - ((10391 / 16005) : ℂ) * ζ ^ 6 + ((62873 / 32010) : ℂ) * ζ ^ 8 + ((33463 / 12804) : ℂ) * ζ ^ 9 - ((188179 / 64020) : ℂ) * ζ ^ 10 + ((5701 / 3201) : ℂ) * ζ ^ 13 + ((29323 / 12804) : ℂ) * ζ ^ 14 - ((36353 / 21340) : ℂ) * ζ ^ 15 - ((18533 / 4268) : ℂ) * ζ ^ 18 + ((36353 / 21340) : ℂ) * ζ ^ 19 + ((176749 / 32010) : ℂ) * ζ ^ 20 + ((10391 / 16005) : ℂ) * ζ ^ 22 - ((47579 / 10670) : ℂ) * ζ ^ 23 - ((176749 / 32010) : ℂ) * ζ ^ 24 - ((1967 / 6402) : ℂ) * ζ ^ 25 + ((10391 / 16005) : ℂ) * ζ ^ 26 + ((17491 / 16005) : ℂ) * ζ ^ 28 + ((1967 / 6402) : ℂ) * ζ ^ 29 - ((10391 / 16005) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((-((145 / 33) : ℂ) + ((185 / 66) : ℂ) * ζ ^ 3 + ((145 / 33) : ℂ) * ζ ^ 4 + ((179 / 33) : ℂ) * ζ ^ 5 - ((145 / 33) : ℂ) * ζ ^ 8 - ((179 / 33) : ℂ) * ζ ^ 9 - ((41 / 66) : ℂ) * ζ ^ 10 + ((17 / 11) : ℂ) * ζ ^ 13 + ((41 / 66) : ℂ) * ζ ^ 14 + ((37 / 66) : ℂ) * ζ ^ 15 + ((34 / 33) : ℂ) * ζ ^ 18 - ((37 / 66) : ℂ) * ζ ^ 19 - ((128 / 33) : ℂ) * ζ ^ 20 + ((85 / 22) : ℂ) * ζ ^ 23 + ((128 / 33) : ℂ) * ζ ^ 24)) * Y 2 2
        + ((-((28 / 33) : ℂ) + ((19 / 22) : ℂ) * ζ ^ 3 + ((28 / 33) : ℂ) * ζ ^ 4 + ((5 / 3) : ℂ) * ζ ^ 5 - ((1 / 3) : ℂ) * ζ ^ 6 - ((12 / 11) : ℂ) * ζ ^ 8 - ((5 / 3) : ℂ) * ζ ^ 9 - ((13 / 66) : ℂ) * ζ ^ 10 + ((29 / 11) : ℂ) * ζ ^ 13 - ((3 / 22) : ℂ) * ζ ^ 14 + ((27 / 22) : ℂ) * ζ ^ 15 + ((8 / 33) : ℂ) * ζ ^ 18 - ((27 / 22) : ℂ) * ζ ^ 19 + ((1 / 11) : ℂ) * ζ ^ 20 + ((1 / 3) : ℂ) * ζ ^ 22 + ((1 / 2) : ℂ) * ζ ^ 23 - ((1 / 11) : ℂ) * ζ ^ 24 + ((23 / 33) : ℂ) * ζ ^ 25 + ((1 / 3) : ℂ) * ζ ^ 26 - ((2 / 11) : ℂ) * ζ ^ 28 - ((23 / 33) : ℂ) * ζ ^ 29 - ((1 / 3) : ℂ) * ζ ^ 30)) * Y 4 5
        + ((((79 / 66) : ℂ) + ((79 / 66) : ℂ) * ζ ^ 3 - ((79 / 66) : ℂ) * ζ ^ 4 + ((28 / 11) : ℂ) * ζ ^ 5 + ((4 / 11) : ℂ) * ζ ^ 6 + ((151 / 66) : ℂ) * ζ ^ 8 - ((28 / 11) : ℂ) * ζ ^ 9 - ((2 / 11) : ℂ) * ζ ^ 10 + ((37 / 33) : ℂ) * ζ ^ 13 + ((6 / 11) : ℂ) * ζ ^ 14 - ((65 / 66) : ℂ) * ζ ^ 15 - ((2 / 33) : ℂ) * ζ ^ 18 + ((65 / 66) : ℂ) * ζ ^ 19 + ((9 / 11) : ℂ) * ζ ^ 20 - ((4 / 11) : ℂ) * ζ ^ 22 - ((23 / 22) : ℂ) * ζ ^ 23 - ((9 / 11) : ℂ) * ζ ^ 24 - ((25 / 22) : ℂ) * ζ ^ 25 - ((4 / 11) : ℂ) * ζ ^ 26 + ((7 / 11) : ℂ) * ζ ^ 28 + ((25 / 22) : ℂ) * ζ ^ 29 + ((4 / 11) : ℂ) * ζ ^ 30)) * Y 5 5)
        * alternatingSixComplexCyclotomicRoot_relation

private theorem row13_y44Coefficient_ne_zero :
    (((1 / 2) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 5 + ((1 / 2) : ℂ) * ζ ^ 7 + ((1 / 4) : ℂ) * ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 15 - ((1 / 2) : ℂ) * ζ ^ 19 - ((1 / 2) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 25 + ((1 / 2) : ℂ) * ζ ^ 31) ≠ 0 := by
  intro h
  have hunit :
      (((1 / 2) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 5 + ((1 / 2) : ℂ) * ζ ^ 7 + ((1 / 4) : ℂ) * ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 15 - ((1 / 2) : ℂ) * ζ ^ 19 - ((1 / 2) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 25 + ((1 / 2) : ℂ) * ζ ^ 31) *
          (-((292 / 673) : ℂ) - ((1150 / 673) : ℂ) * ζ ^ 3 + ((902 / 673) : ℂ) * ζ ^ 5 - ((1150 / 673) : ℂ) * ζ ^ 7 + ((634 / 673) : ℂ) * ζ ^ 10 + ((178 / 673) : ℂ) * ζ ^ 15 + ((1150 / 673) : ℂ) * ζ ^ 19 - ((430 / 673) : ℂ) * ζ ^ 20 + ((1150 / 673) : ℂ) * ζ ^ 23 - ((156 / 673) : ℂ) * ζ ^ 25 + ((150 / 673) : ℂ) * ζ ^ 30 - ((1150 / 673) : ℂ) * ζ ^ 31) = 1 := by
    close_cyclotomic_row13
      (-(1 : ℂ) - ((146 / 673) : ℂ) * ζ ^ 3 + ζ ^ 4 + ((73 / 673) : ℂ) * ζ ^ 5 - ((575 / 673) : ℂ) * ζ ^ 6 + ((131 / 1346) : ℂ) * ζ ^ 8 - ((73 / 673) : ℂ) * ζ ^ 9 - ((1747 / 1346) : ℂ) * ζ ^ 10 + ((205 / 1346) : ℂ) * ζ ^ 13 + ((597 / 1346) : ℂ) * ζ ^ 14 + ((140 / 673) : ℂ) * ζ ^ 15 + ((78 / 673) : ℂ) * ζ ^ 18 - ((140 / 673) : ℂ) * ζ ^ 19 - ((497 / 673) : ℂ) * ζ ^ 20 + ((575 / 673) : ℂ) * ζ ^ 22 - ((75 / 673) : ℂ) * ζ ^ 23 + ((497 / 673) : ℂ) * ζ ^ 24 - ((75 / 673) : ℂ) * ζ ^ 25 + ((575 / 673) : ℂ) * ζ ^ 26 + ((75 / 673) : ℂ) * ζ ^ 29 - ((575 / 673) : ℂ) * ζ ^ 30)
  rw [h, zero_mul] at hunit
  exact zero_ne_one hunit

private theorem row13_reducedY44
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow13TransformedGeneratorA =
        alternatingSixAmbientRow13TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow13GeneratorBDiagonal =
        alternatingSixAmbientRow13GeneratorBDiagonal * Y) :
    Y 4 4 = Y 5 5 := by
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 3 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 0 (by decide)

  have commutesA40 :=
    congrFun (congrFun commutesA
      (4 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA40
  simp only [Fin.sum_univ_succ] at commutesA40
  simp [
      alternatingSixAmbientRow13TransformedGeneratorA,
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
    row13_reducedY00 Y commutesA commutesDiagonal
  have reducedY10 : Y 1 0 = 0 :=
    row13_reducedY10 Y commutesA commutesDiagonal
  have reducedY45 : Y 4 5 = 0 :=
    row13_reducedY45 Y commutesA commutesDiagonal

  rw [reducedY00, reducedY10, reducedY45] at commutesA40
  have hscaled :
      (((1 / 2) : ℂ) * ζ ^ 3 - ((1 / 4) : ℂ) * ζ ^ 5 + ((1 / 2) : ℂ) * ζ ^ 7 + ((1 / 4) : ℂ) * ζ ^ 10 - ((3 / 4) : ℂ) * ζ ^ 15 - ((1 / 2) : ℂ) * ζ ^ 19 - ((1 / 2) : ℂ) * ζ ^ 23 - ((1 / 2) : ℂ) * ζ ^ 25 + ((1 / 2) : ℂ) * ζ ^ 31) *
          (Y 4 4 - Y 5 5) = 0 := by
    linear_combination commutesA40
  rcases mul_eq_zero.mp hscaled with hcoefficient | hdifference
  · exact
      (row13_y44Coefficient_ne_zero
        hcoefficient).elim
  · exact sub_eq_zero.mp hdifference

private theorem row13_reducedY54
    (Y : Matrix (Fin 6)
      (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow13TransformedGeneratorA =
        alternatingSixAmbientRow13TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow13GeneratorBDiagonal =
        alternatingSixAmbientRow13GeneratorBDiagonal * Y) :
    Y 5 4 = 0 := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 2 (by decide)

  have commutesA00 :=
    congrFun (congrFun commutesA
      (0 : Fin 6))
      (0 : Fin 6)
  rw [Matrix.mul_apply, Matrix.mul_apply] at commutesA00
  simp only [Fin.sum_univ_succ] at commutesA00
  simp [
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
      alternatingSixAmbientRow13TransformedGeneratorA,
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
    ((-((147404 / 5335) : ℂ) + ((104174 / 5335) : ℂ) * ζ ^ 3 + ((141296 / 5335) : ℂ) * ζ ^ 5 + ((104174 / 5335) : ℂ) * ζ ^ 7 - ((135988 / 5335) : ℂ) * ζ ^ 10 + ((8292 / 5335) : ℂ) * ζ ^ 15 - ((104174 / 5335) : ℂ) * ζ ^ 19 + ((26834 / 5335) : ℂ) * ζ ^ 20 - ((104174 / 5335) : ℂ) * ζ ^ 23 - ((77188 / 5335) : ℂ) * ζ ^ 25 + ((20094 / 1067) : ℂ) * ζ ^ 30 + ((104174 / 5335) : ℂ) * ζ ^ 31)) * commutesA00
      + ((((3240 / 1067) : ℂ) + ((40686 / 5335) : ℂ) * ζ ^ 3 - ((35802 / 5335) : ℂ) * ζ ^ 5 + ((40686 / 5335) : ℂ) * ζ ^ 7 + ((77002 / 5335) : ℂ) * ζ ^ 10 - ((165284 / 5335) : ℂ) * ζ ^ 15 - ((40686 / 5335) : ℂ) * ζ ^ 19 + ((122184 / 5335) : ℂ) * ζ ^ 20 - ((40686 / 5335) : ℂ) * ζ ^ 23 - ((109286 / 5335) : ℂ) * ζ ^ 25 + ((78758 / 5335) : ℂ) * ζ ^ 30 + ((40686 / 5335) : ℂ) * ζ ^ 31)) * commutesA01
      + ((-((749 / 11) : ℂ) + ((882 / 11) : ℂ) * ζ ^ 3 + ((675 / 11) : ℂ) * ζ ^ 5 + ((882 / 11) : ℂ) * ζ ^ 7 - ((438 / 11) : ℂ) * ζ ^ 10 - ((607 / 11) : ℂ) * ζ ^ 15 - ((882 / 11) : ℂ) * ζ ^ 19 + ((740 / 11) : ℂ) * ζ ^ 20 - ((882 / 11) : ℂ) * ζ ^ 23 - ((855 / 11) : ℂ) * ζ ^ 25 + ((855 / 11) : ℂ) * ζ ^ 30 + ((882 / 11) : ℂ) * ζ ^ 31)) * commutesA02
      + ((-(3 : ℂ) + (2 : ℂ) * ζ ^ 3 + (3 : ℂ) * ζ ^ 5 + (2 : ℂ) * ζ ^ 7 - (4 : ℂ) * ζ ^ 10 + ζ ^ 15 - (2 : ℂ) * ζ ^ 19 + (2 : ℂ) * ζ ^ 20 - (2 : ℂ) * ζ ^ 23 + ζ ^ 25 + (3 : ℂ) * ζ ^ 30 + (2 : ℂ) * ζ ^ 31)) * commutesA04
      + ((((140 / 11) : ℂ) + ((163 / 33) : ℂ) * ζ ^ 3 - ((1073 / 33) : ℂ) * ζ ^ 5 + ((163 / 33) : ℂ) * ζ ^ 7 + ((1565 / 33) : ℂ) * ζ ^ 10 - ((2111 / 33) : ℂ) * ζ ^ 15 - ((163 / 33) : ℂ) * ζ ^ 19 + ((617 / 11) : ℂ) * ζ ^ 20 - ((163 / 33) : ℂ) * ζ ^ 23 - ((1292 / 33) : ℂ) * ζ ^ 25 + ((827 / 33) : ℂ) * ζ ^ 30 + ((163 / 33) : ℂ) * ζ ^ 31)) * commutesA12
      + ((-(2 : ℂ) + ((7 / 3) : ℂ) * ζ ^ 3 - ((5 / 3) : ℂ) * ζ ^ 5 + ((7 / 3) : ℂ) * ζ ^ 7 - ((7 / 3) : ℂ) * ζ ^ 10 - ((11 / 3) : ℂ) * ζ ^ 15 - ((7 / 3) : ℂ) * ζ ^ 19 + ζ ^ 20 - ((7 / 3) : ℂ) * ζ ^ 23 - ((8 / 3) : ℂ) * ζ ^ 25 + ((5 / 3) : ℂ) * ζ ^ 30 + ((7 / 3) : ℂ) * ζ ^ 31)) * commutesA14
      - (
        ((-((73025 / 2134) : ℂ) + ((39254 / 1067) : ℂ) * ζ ^ 3 + ((73025 / 2134) : ℂ) * ζ ^ 4 + ((69987 / 2134) : ℂ) * ζ ^ 5 + ((15017 / 5335) : ℂ) * ζ ^ 6 - ((193769 / 5335) : ℂ) * ζ ^ 8 - ((69987 / 2134) : ℂ) * ζ ^ 9 - ((169093 / 32010) : ℂ) * ζ ^ 10 + ((210577 / 16005) : ℂ) * ζ ^ 13 + ((51839 / 6402) : ℂ) * ζ ^ 14 + ((2470 / 291) : ℂ) * ζ ^ 15 - ((270901 / 16005) : ℂ) * ζ ^ 18 - ((2470 / 291) : ℂ) * ζ ^ 19 - ((280117 / 32010) : ℂ) * ζ ^ 20 - ((15017 / 5335) : ℂ) * ζ ^ 22 + ((434723 / 32010) : ℂ) * ζ ^ 23 + ((280117 / 32010) : ℂ) * ζ ^ 24 - ((257803 / 32010) : ℂ) * ζ ^ 25 - ((15017 / 5335) : ℂ) * ζ ^ 26 + ((83123 / 16005) : ℂ) * ζ ^ 28 + ((257803 / 32010) : ℂ) * ζ ^ 29 + ((15017 / 5335) : ℂ) * ζ ^ 30)) * Y 0 0
        + ((((490263 / 10670) : ℂ) - ((164128 / 5335) : ℂ) * ζ ^ 3 - ((490263 / 10670) : ℂ) * ζ ^ 4 - ((466747 / 10670) : ℂ) * ζ ^ 5 + ((6245 / 2134) : ℂ) * ζ ^ 6 + ((164804 / 5335) : ℂ) * ζ ^ 8 + ((466747 / 10670) : ℂ) * ζ ^ 9 + ((343217 / 5335) : ℂ) * ζ ^ 10 - ((531549 / 10670) : ℂ) * ζ ^ 13 - ((655209 / 10670) : ℂ) * ζ ^ 14 - ((73944 / 1067) : ℂ) * ζ ^ 15 + ((256291 / 5335) : ℂ) * ζ ^ 18 + ((73944 / 1067) : ℂ) * ζ ^ 19 + ((78589 / 10670) : ℂ) * ζ ^ 20 - ((6245 / 2134) : ℂ) * ζ ^ 22 - ((8501 / 10670) : ℂ) * ζ ^ 23 - ((78589 / 10670) : ℂ) * ζ ^ 24 - ((101482 / 5335) : ℂ) * ζ ^ 25 - ((6245 / 2134) : ℂ) * ζ ^ 26 + ((128993 / 10670) : ℂ) * ζ ^ 28 + ((101482 / 5335) : ℂ) * ζ ^ 29 + ((6245 / 2134) : ℂ) * ζ ^ 30)) * Y 0 1
        + ((-((14153 / 3201) : ℂ) + ((299204 / 16005) : ℂ) * ζ ^ 3 + ((14153 / 3201) : ℂ) * ζ ^ 4 - ((9269 / 2134) : ℂ) * ζ ^ 5 - ((198163 / 32010) : ℂ) * ζ ^ 6 - ((73597 / 5335) : ℂ) * ζ ^ 8 + ((9269 / 2134) : ℂ) * ζ ^ 9 - ((96604 / 16005) : ℂ) * ζ ^ 10 + ((106067 / 10670) : ℂ) * ζ ^ 13 - ((991 / 6402) : ℂ) * ζ ^ 14 + ((69107 / 16005) : ℂ) * ζ ^ 15 - ((128413 / 32010) : ℂ) * ζ ^ 18 - ((69107 / 16005) : ℂ) * ζ ^ 19 - ((400421 / 32010) : ℂ) * ζ ^ 20 + ((198163 / 32010) : ℂ) * ζ ^ 22 + ((181463 / 16005) : ℂ) * ζ ^ 23 + ((400421 / 32010) : ℂ) * ζ ^ 24 + ((131741 / 10670) : ℂ) * ζ ^ 25 + ((198163 / 32010) : ℂ) * ζ ^ 26 - ((19609 / 3201) : ℂ) * ζ ^ 28 - ((131741 / 10670) : ℂ) * ζ ^ 29 - ((198163 / 32010) : ℂ) * ζ ^ 30)) * Y 1 0
        + ((-((2247 / 2134) : ℂ) - ((1657 / 6402) : ℂ) * ζ ^ 3 + ((2247 / 2134) : ℂ) * ζ ^ 4 + ((39329 / 6402) : ℂ) * ζ ^ 5 - ((37291 / 16005) : ℂ) * ζ ^ 6 + ((14827 / 16005) : ℂ) * ζ ^ 8 - ((39329 / 6402) : ℂ) * ζ ^ 9 - ((298447 / 32010) : ℂ) * ζ ^ 10 + ((109921 / 32010) : ℂ) * ζ ^ 13 + ((44773 / 6402) : ℂ) * ζ ^ 14 + ((7961 / 582) : ℂ) * ζ ^ 15 + ((86387 / 32010) : ℂ) * ζ ^ 18 - ((7961 / 582) : ℂ) * ζ ^ 19 - ((34763 / 2910) : ℂ) * ζ ^ 20 + ((37291 / 16005) : ℂ) * ζ ^ 22 + ((66822 / 5335) : ℂ) * ζ ^ 23 + ((34763 / 2910) : ℂ) * ζ ^ 24 + ((117019 / 16005) : ℂ) * ζ ^ 25 + ((37291 / 16005) : ℂ) * ζ ^ 26 - ((78758 / 16005) : ℂ) * ζ ^ 28 - ((117019 / 16005) : ℂ) * ζ ^ 29 - ((37291 / 16005) : ℂ) * ζ ^ 30)) * Y 1 1
        + ((((819 / 22) : ℂ) - ((5129 / 132) : ℂ) * ζ ^ 3 - ((819 / 22) : ℂ) * ζ ^ 4 - ((5123 / 132) : ℂ) * ζ ^ 5 + ((819 / 22) : ℂ) * ζ ^ 8 + ((5123 / 132) : ℂ) * ζ ^ 9 + ((1183 / 66) : ℂ) * ζ ^ 10 - ((1157 / 66) : ℂ) * ζ ^ 13 - ((1183 / 66) : ℂ) * ζ ^ 14 - ((511 / 22) : ℂ) * ζ ^ 15 + ((2203 / 132) : ℂ) * ζ ^ 18 + ((511 / 22) : ℂ) * ζ ^ 19 + ((2809 / 132) : ℂ) * ζ ^ 20 - ((848 / 33) : ℂ) * ζ ^ 23 - ((2809 / 132) : ℂ) * ζ ^ 24)) * Y 2 2
        + ((-((43 / 22) : ℂ) + ((307 / 132) : ℂ) * ζ ^ 3 + ((43 / 22) : ℂ) * ζ ^ 4 - ((17 / 132) : ℂ) * ζ ^ 5 - ((16 / 33) : ℂ) * ζ ^ 6 - ((11 / 6) : ℂ) * ζ ^ 8 + ((17 / 132) : ℂ) * ζ ^ 9 - ((73 / 22) : ℂ) * ζ ^ 10 + ((31 / 33) : ℂ) * ζ ^ 13 + ((17 / 6) : ℂ) * ζ ^ 14 + ((35 / 33) : ℂ) * ζ ^ 15 - ((325 / 132) : ℂ) * ζ ^ 18 - ((35 / 33) : ℂ) * ζ ^ 19 - ((7 / 12) : ℂ) * ζ ^ 20 + ((16 / 33) : ℂ) * ζ ^ 22 - ((9 / 22) : ℂ) * ζ ^ 23 + ((7 / 12) : ℂ) * ζ ^ 24 + ((49 / 66) : ℂ) * ζ ^ 25 + ((16 / 33) : ℂ) * ζ ^ 26 - ((3 / 11) : ℂ) * ζ ^ 28 - ((49 / 66) : ℂ) * ζ ^ 29 - ((16 / 33) : ℂ) * ζ ^ 30)) * Y 4 4
        + ((-((91 / 44) : ℂ) - ((1 / 66) : ℂ) * ζ ^ 3 + ((91 / 44) : ℂ) * ζ ^ 4 + ((175 / 132) : ℂ) * ζ ^ 5 + ((4 / 11) : ℂ) * ζ ^ 6 - ((61 / 44) : ℂ) * ζ ^ 8 - ((175 / 132) : ℂ) * ζ ^ 9 + ((203 / 132) : ℂ) * ζ ^ 10 - ((8 / 11) : ℂ) * ζ ^ 13 - ((155 / 132) : ℂ) * ζ ^ 14 - ((131 / 132) : ℂ) * ζ ^ 15 + ((283 / 132) : ℂ) * ζ ^ 18 + ((131 / 132) : ℂ) * ζ ^ 19 + ((43 / 44) : ℂ) * ζ ^ 20 - ((4 / 11) : ℂ) * ζ ^ 22 + ((17 / 22) : ℂ) * ζ ^ 23 - ((43 / 44) : ℂ) * ζ ^ 24 - ((53 / 44) : ℂ) * ζ ^ 25 - ((4 / 11) : ℂ) * ζ ^ 26 + ((49 / 44) : ℂ) * ζ ^ 28 + ((53 / 44) : ℂ) * ζ ^ 29 + ((4 / 11) : ℂ) * ζ ^ 30)) * Y 5 4)
        * alternatingSixComplexCyclotomicRoot_relation


/-- A matrix commuting with both transformed row 13 generators is
scalar. -/
theorem alternatingSixAmbientRow13Transformed_scalar_commutant
    (Y : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow13TransformedGeneratorA =
        alternatingSixAmbientRow13TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow13GeneratorBDiagonal =
        alternatingSixAmbientRow13GeneratorBDiagonal * Y) :
    ∃ c : ℂ,
      Y = c • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  have hY02 :
      Y 0 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 2 (by decide)
  have hY03 :
      Y 0 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 3 (by decide)
  have hY04 :
      Y 0 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 4 (by decide)
  have hY05 :
      Y 0 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 0 5 (by decide)
  have hY12 :
      Y 1 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 2 (by decide)
  have hY13 :
      Y 1 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 3 (by decide)
  have hY14 :
      Y 1 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 4 (by decide)
  have hY15 :
      Y 1 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 1 5 (by decide)
  have hY20 :
      Y 2 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 0 (by decide)
  have hY21 :
      Y 2 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 1 (by decide)
  have hY23 :
      Y 2 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 3 (by decide)
  have hY24 :
      Y 2 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 4 (by decide)
  have hY25 :
      Y 2 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 2 5 (by decide)
  have hY30 :
      Y 3 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 0 (by decide)
  have hY31 :
      Y 3 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 1 (by decide)
  have hY32 :
      Y 3 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 2 (by decide)
  have hY34 :
      Y 3 4 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 4 (by decide)
  have hY35 :
      Y 3 5 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 3 5 (by decide)
  have hY40 :
      Y 4 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 0 (by decide)
  have hY41 :
      Y 4 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 1 (by decide)
  have hY42 :
      Y 4 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 2 (by decide)
  have hY43 :
      Y 4 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 4 3 (by decide)
  have hY50 :
      Y 5 0 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 0 (by decide)
  have hY51 :
      Y 5 1 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 1 (by decide)
  have hY52 :
      Y 5 2 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 2 (by decide)
  have hY53 :
      Y 5 3 = 0 :=
    alternatingSixAmbientRow13_off_block
      Y commutesDiagonal 5 3 (by decide)

  have reducedY00 : Y 0 0 = Y 5 5 :=
    row13_reducedY00 Y commutesA commutesDiagonal
  have reducedY01 : Y 0 1 = 0 :=
    row13_reducedY01 Y commutesA commutesDiagonal
  have reducedY10 : Y 1 0 = 0 :=
    row13_reducedY10 Y commutesA commutesDiagonal
  have reducedY11 : Y 1 1 = Y 5 5 :=
    row13_reducedY11 Y commutesA commutesDiagonal
  have reducedY22 : Y 2 2 = Y 5 5 :=
    row13_reducedY22 Y commutesA commutesDiagonal
  have reducedY33 : Y 3 3 = Y 5 5 :=
    row13_reducedY33 Y commutesA commutesDiagonal
  have reducedY45 : Y 4 5 = 0 :=
    row13_reducedY45 Y commutesA commutesDiagonal
  have reducedY44 : Y 4 4 = Y 5 5 :=
    row13_reducedY44 Y commutesA commutesDiagonal
  have reducedY54 : Y 5 4 = 0 :=
    row13_reducedY54 Y commutesA commutesDiagonal

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

/-- Every matrix commuting with both original row 13 presentation
generators is scalar. -/
theorem alternatingSixAmbientRow13_scalar_commutant
    (X : Matrix (Fin 6) (Fin 6) ℂ)
    (commutesA :
      X * alternatingSixFiveAmbient_row13_matrixA =
        alternatingSixFiveAmbient_row13_matrixA * X)
    (commutesB :
      X * alternatingSixFiveAmbient_row13_matrixB =
        alternatingSixFiveAmbient_row13_matrixB * X) :
    ∃ c : ℂ,
      X = c • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  apply Matrix.scalar_commutant_of_diagonal_basis
    alternatingSixFiveAmbient_row13_matrixA
    alternatingSixFiveAmbient_row13_matrixB
    alternatingSixAmbientRow13Eigenbasis
    alternatingSixAmbientRow13EigenbasisInverse
    alternatingSixAmbientRow13TransformedGeneratorA
    alternatingSixAmbientRow13GeneratorBEigenvalue
    alternatingSixAmbientRow13EigenbasisInverse_mul
    alternatingSixAmbientRow13Eigenbasis_mul_inverse
    alternatingSixAmbientRow13GeneratorB_mul_eigenbasis
    alternatingSixAmbientRow13TransformedGeneratorA_eq
    alternatingSixAmbientRow13Transformed_scalar_commutant
    X commutesA commutesB

end InductiveMcKay
end McKayConjecture
