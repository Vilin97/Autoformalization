/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction13

/-!
# Ambient row 18 commutant reduction 14

This generated module checks the reduced relation `reducedY76` for
matrix coordinate (7, 6).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY76_combinationStep00Multiplier : ℂ :=
  (((49082 / 1185) : ℂ) - ((22562 / 237) : ℂ) * ζ ^ 1 - ((5606 / 1185) : ℂ) * ζ ^ 2 + ((108748 / 1185) : ℂ) * ζ ^ 3 - ((22562 / 237) : ℂ) * ζ ^ 5 + ((14492 / 395) : ℂ) * ζ ^ 6 - ((14492 / 395) : ℂ) * ζ ^ 8 + ((22562 / 237) : ℂ) * ζ ^ 9 - ((54374 / 1185) : ℂ) * ζ ^ 11 + ((12374 / 395) : ℂ) * ζ ^ 12 + ((22562 / 237) : ℂ) * ζ ^ 13 + ((11698 / 1185) : ℂ) * ζ ^ 15 + ((22562 / 237) : ℂ) * ζ ^ 17 + ((68138 / 1185) : ℂ) * ζ ^ 18 + ((24004 / 237) : ℂ) * ζ ^ 21 + ((5606 / 1185) : ℂ) * ζ ^ 22 + ((111614 / 1185) : ℂ) * ζ ^ 24 + ((120446 / 1185) : ℂ) * ζ ^ 27 + ((14492 / 395) : ℂ) * ζ ^ 28 - ((22562 / 237) : ℂ) * ζ ^ 29 + ((26866 / 395) : ℂ) * ζ ^ 30 + ((54374 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY76_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep00CoefficientIdentity00 :
    row18_reducedY76_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep00Coefficient00 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep00Coefficient01 : ℂ :=
  (-((3533 / 237) : ℂ) - ((3392 / 237) : ℂ) * ζ ^ 1 - ((414 / 79) : ℂ) * ζ ^ 2 - ((1612 / 237) : ℂ) * ζ ^ 3 - ((595 / 79) : ℂ) * ζ ^ 5 - ((1214 / 237) : ℂ) * ζ ^ 6 - ((245 / 158) : ℂ) * ζ ^ 9 + ((595 / 79) : ℂ) * ζ ^ 11 + ((4351 / 237) : ℂ) * ζ ^ 12 + ((3392 / 237) : ℂ) * ζ ^ 13 - ((3949 / 474) : ℂ) * ζ ^ 15 + ((3392 / 237) : ℂ) * ζ ^ 17 + ((1270 / 237) : ℂ) * ζ ^ 18 + ((173 / 237) : ℂ) * ζ ^ 21 + ((414 / 79) : ℂ) * ζ ^ 22 - ((3533 / 237) : ℂ) * ζ ^ 24 - ((1607 / 237) : ℂ) * ζ ^ 25 + ((1607 / 237) : ℂ) * ζ ^ 27 - ((3392 / 237) : ℂ) * ζ ^ 29 - ((828 / 79) : ℂ) * ζ ^ 30 - ((595 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep00CoefficientIdentity01 :
    row18_reducedY76_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep00Coefficient01 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 (((2426257 / 93615) : ℂ) - ((1837471 / 187230) : ℂ) * ζ ^ 1 + ((1317887 / 187230) : ℂ) * ζ ^ 2 + ((1111283 / 62410) : ℂ) * ζ ^ 3 - ((448648 / 18723) : ℂ) * ζ ^ 4 - ((469259 / 93615) : ℂ) * ζ ^ 5 + ((841651 / 37446) : ℂ) * ζ ^ 6 - ((1576801 / 93615) : ℂ) * ζ ^ 7 - ((133061 / 18723) : ℂ) * ζ ^ 8 + ((2005943 / 93615) : ℂ) * ζ ^ 9 + ((1957894 / 93615) : ℂ) * ζ ^ 10 + ((2271467 / 187230) : ℂ) * ζ ^ 11 - ((3183541 / 93615) : ℂ) * ζ ^ 12 + ((1217008 / 93615) : ℂ) * ζ ^ 13 + ((1559653 / 93615) : ℂ) * ζ ^ 14 - ((21946 / 93615) : ℂ) * ζ ^ 15 + ((2284 / 395) : ℂ) * ζ ^ 16 + ((499334 / 93615) : ℂ) * ζ ^ 17 - ((7628 / 1185) : ℂ) * ζ ^ 18 + ((633478 / 93615) : ℂ) * ζ ^ 19 + ((878851 / 187230) : ℂ) * ζ ^ 20 - ((149249 / 31205) : ℂ) * ζ ^ 21 - ((936373 / 62410) : ℂ) * ζ ^ 22 + ((1167351 / 62410) : ℂ) * ζ ^ 23 + ((2813719 / 187230) : ℂ) * ζ ^ 24 - ((745489 / 93615) : ℂ) * ζ ^ 25 - ((2621419 / 187230) : ℂ) * ζ ^ 26 - ((775474 / 93615) : ℂ) * ζ ^ 27 + ((2584148 / 93615) : ℂ) * ζ ^ 28 - ((668761 / 62410) : ℂ) * ζ ^ 29 - ((924358 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep00Coefficient02 : ℂ :=
  (-((490 / 237) : ℂ) + ((523 / 79) : ℂ) * ζ ^ 1 + ((4048 / 237) : ℂ) * ζ ^ 2 - ((767 / 158) : ℂ) * ζ ^ 3 + ((21 / 158) : ℂ) * ζ ^ 5 + ((1505 / 158) : ℂ) * ζ ^ 8 + ((1520 / 237) : ℂ) * ζ ^ 9 - ((739 / 474) : ℂ) * ζ ^ 11 - ((2555 / 474) : ℂ) * ζ ^ 12 - ((523 / 79) : ℂ) * ζ ^ 13 + ((896 / 79) : ℂ) * ζ ^ 15 - ((523 / 79) : ℂ) * ζ ^ 17 - ((4048 / 237) : ℂ) * ζ ^ 18 - ((1813 / 158) : ℂ) * ζ ^ 21 - ((4048 / 237) : ℂ) * ζ ^ 22 - ((980 / 237) : ℂ) * ζ ^ 24 + ((1025 / 158) : ℂ) * ζ ^ 25 - ((1813 / 158) : ℂ) * ζ ^ 27 - ((1505 / 158) : ℂ) * ζ ^ 28 + ((523 / 79) : ℂ) * ζ ^ 29 + ((2345 / 158) : ℂ) * ζ ^ 30 + ((739 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep00CoefficientIdentity02 :
    row18_reducedY76_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep00Coefficient02 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 (((1199731 / 93615) : ℂ) - ((5545687 / 187230) : ℂ) * ζ ^ 1 - ((1108879 / 62410) : ℂ) * ζ ^ 2 + ((282437 / 18723) : ℂ) * ζ ^ 3 - ((217091 / 93615) : ℂ) * ζ ^ 4 + ((281158 / 18723) : ℂ) * ζ ^ 5 + ((1113621 / 62410) : ℂ) * ζ ^ 6 - ((5080001 / 187230) : ℂ) * ζ ^ 7 - ((2566781 / 187230) : ℂ) * ζ ^ 8 + ((677103 / 62410) : ℂ) * ζ ^ 9 + ((998263 / 187230) : ℂ) * ζ ^ 10 + ((1110161 / 93615) : ℂ) * ζ ^ 11 + ((595243 / 187230) : ℂ) * ζ ^ 12 + ((1981601 / 187230) : ℂ) * ζ ^ 13 + ((127607 / 12482) : ℂ) * ζ ^ 14 - ((393142 / 31205) : ℂ) * ζ ^ 15 + ((81277 / 12482) : ℂ) * ζ ^ 16 + ((294176 / 93615) : ℂ) * ζ ^ 17 + ((1554337 / 187230) : ℂ) * ζ ^ 18 + ((97539 / 12482) : ℂ) * ζ ^ 19 + ((24065 / 6241) : ℂ) * ζ ^ 20 + ((64335 / 12482) : ℂ) * ζ ^ 21 - ((169476 / 31205) : ℂ) * ζ ^ 22 + ((615827 / 93615) : ℂ) * ζ ^ 23 + ((150484 / 18723) : ℂ) * ζ ^ 24 - ((2841113 / 187230) : ℂ) * ζ ^ 25 + ((1050313 / 187230) : ℂ) * ζ ^ 26 + ((3379159 / 187230) : ℂ) * ζ ^ 27 + ((111433 / 187230) : ℂ) * ζ ^ 28 - ((223089 / 31205) : ℂ) * ζ ^ 29 - ((27187 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep00CoefficientIdentity03 :
    row18_reducedY76_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep00Coefficient03 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep00CoefficientIdentity04 :
    row18_reducedY76_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep00Coefficient04 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep00CoefficientIdentity05 :
    row18_reducedY76_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep00Coefficient05 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep00CoefficientIdentity06 :
    row18_reducedY76_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep00Coefficient06 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep00CoefficientIdentity07 :
    row18_reducedY76_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep00Coefficient07 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep00CoefficientIdentity08 :
    row18_reducedY76_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep00Coefficient08 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep00CoefficientIdentity09 :
    row18_reducedY76_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep00Coefficient09 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep00CoefficientIdentity10 :
    row18_reducedY76_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep00Coefficient10 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep00CoefficientIdentity11 :
    row18_reducedY76_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep00Coefficient11 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep00CoefficientIdentity12 :
    row18_reducedY76_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep00Coefficient12 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep00CoefficientIdentity13 :
    row18_reducedY76_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep00Coefficient13 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep00CoefficientIdentity14 :
    row18_reducedY76_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep00Coefficient14 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep00CoefficientIdentity15 :
    row18_reducedY76_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY76_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep00Coefficient15 row18_reducedY76_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY76_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY76_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY76_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY76_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY76_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY76_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY76_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY76_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY76_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY76_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY76_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY76_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY76_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY76_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY76_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY76_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY76_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY76_combinationStep00CoefficientIdentity00,
      row18_reducedY76_combinationStep00CoefficientIdentity01,
      row18_reducedY76_combinationStep00CoefficientIdentity02,
      row18_reducedY76_combinationStep00CoefficientIdentity03,
      row18_reducedY76_combinationStep00CoefficientIdentity04,
      row18_reducedY76_combinationStep00CoefficientIdentity05,
      row18_reducedY76_combinationStep00CoefficientIdentity06,
      row18_reducedY76_combinationStep00CoefficientIdentity07,
      row18_reducedY76_combinationStep00CoefficientIdentity08,
      row18_reducedY76_combinationStep00CoefficientIdentity09,
      row18_reducedY76_combinationStep00CoefficientIdentity10,
      row18_reducedY76_combinationStep00CoefficientIdentity11,
      row18_reducedY76_combinationStep00CoefficientIdentity12,
      row18_reducedY76_combinationStep00CoefficientIdentity13,
      row18_reducedY76_combinationStep00CoefficientIdentity14,
      row18_reducedY76_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY76_combinationStep00Multiplier * equation

private def row18_reducedY76_combinationStep01Multiplier : ℂ :=
  (((18172 / 1185) : ℂ) + ((18436 / 1185) : ℂ) * ζ ^ 1 - ((4262 / 237) : ℂ) * ζ ^ 2 - ((22606 / 1185) : ℂ) * ζ ^ 3 + ((8618 / 1185) : ℂ) * ζ ^ 5 + ((3592 / 237) : ℂ) * ζ ^ 6 - ((21296 / 1185) : ℂ) * ζ ^ 8 - ((18442 / 1185) : ℂ) * ζ ^ 9 + ((8618 / 1185) : ℂ) * ζ ^ 11 - ((10648 / 1185) : ℂ) * ζ ^ 12 - ((18436 / 1185) : ℂ) * ζ ^ 13 + ((8624 / 1185) : ℂ) * ζ ^ 15 - ((18436 / 1185) : ℂ) * ζ ^ 17 - ((3592 / 237) : ℂ) * ζ ^ 18 + ((13988 / 1185) : ℂ) * ζ ^ 21 + ((4262 / 237) : ℂ) * ζ ^ 22 + ((3124 / 1185) : ℂ) * ζ ^ 24 + ((9818 / 1185) : ℂ) * ζ ^ 25 + ((9818 / 1185) : ℂ) * ζ ^ 27 + ((21296 / 1185) : ℂ) * ζ ^ 28 + ((18436 / 1185) : ℂ) * ζ ^ 29 - ((8618 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY76_combinationStep01Coefficient00 : ℂ :=
  (((687 / 79) : ℂ) + ((1771 / 237) : ℂ) * ζ ^ 1 + ((1739 / 237) : ℂ) * ζ ^ 2 + ((119 / 79) : ℂ) * ζ ^ 5 - ((322 / 237) : ℂ) * ζ ^ 6 - ((322 / 237) : ℂ) * ζ ^ 8 + ((119 / 79) : ℂ) * ζ ^ 9 - ((2947 / 474) : ℂ) * ζ ^ 11 - ((6025 / 474) : ℂ) * ζ ^ 12 - ((1771 / 237) : ℂ) * ζ ^ 13 + ((2180 / 237) : ℂ) * ζ ^ 15 - ((1771 / 237) : ℂ) * ζ ^ 17 - ((933 / 158) : ℂ) * ζ ^ 18 - ((1064 / 237) : ℂ) * ζ ^ 21 - ((1739 / 237) : ℂ) * ζ ^ 22 + ((3443 / 474) : ℂ) * ζ ^ 24 + ((1414 / 237) : ℂ) * ζ ^ 25 - ((2180 / 237) : ℂ) * ζ ^ 27 + ((322 / 237) : ℂ) * ζ ^ 28 + ((1771 / 237) : ℂ) * ζ ^ 29 + ((5381 / 474) : ℂ) * ζ ^ 30 + ((2947 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep01CoefficientIdentity00 :
    row18_reducedY76_combinationStep01Coefficient00 =
      row18_reducedY76_combinationStep00Coefficient00 +
        row18_reducedY76_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep01Coefficient00 row18_reducedY76_combinationStep00Coefficient00 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 (-((1186621 / 93615) : ℂ) - ((1136542 / 93615) : ℂ) * ζ ^ 1 - ((464429 / 93615) : ℂ) * ζ ^ 2 + ((970013 / 187230) : ℂ) * ζ ^ 3 + ((1034561 / 62410) : ℂ) * ζ ^ 4 + ((294383 / 31205) : ℂ) * ζ ^ 5 + ((19643 / 187230) : ℂ) * ζ ^ 6 - ((1334657 / 187230) : ℂ) * ζ ^ 7 - ((150662 / 18723) : ℂ) * ζ ^ 8 + ((420733 / 187230) : ℂ) * ζ ^ 9 + ((164813 / 62410) : ℂ) * ζ ^ 10 + ((90284 / 31205) : ℂ) * ζ ^ 11 + ((404003 / 93615) : ℂ) * ζ ^ 12 + ((136661 / 187230) : ℂ) * ζ ^ 13 + ((3019 / 62410) : ℂ) * ζ ^ 14 - ((438154 / 93615) : ℂ) * ζ ^ 15 - ((994723 / 187230) : ℂ) * ζ ^ 16 - ((103058 / 93615) : ℂ) * ζ ^ 17 + ((33036 / 31205) : ℂ) * ζ ^ 18 + ((166924 / 31205) : ℂ) * ζ ^ 19 + ((109677 / 31205) : ℂ) * ζ ^ 20 - ((153218 / 93615) : ℂ) * ζ ^ 21 - ((585679 / 187230) : ℂ) * ζ ^ 22 - ((165629 / 37446) : ℂ) * ζ ^ 23 - ((91625 / 18723) : ℂ) * ζ ^ 24 - ((75306 / 31205) : ℂ) * ζ ^ 25 + ((370567 / 187230) : ℂ) * ζ ^ 26 + ((134291 / 37446) : ℂ) * ζ ^ 27 + ((194287 / 187230) : ℂ) * ζ ^ 28 - ((38781 / 62410) : ℂ) * ζ ^ 29 - ((4309 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep01Coefficient01 : ℂ :=
  (-((8765 / 474) : ℂ) - ((1042 / 79) : ℂ) * ζ ^ 1 - ((2419 / 237) : ℂ) * ζ ^ 2 - ((1369 / 237) : ℂ) * ζ ^ 3 - ((1411 / 237) : ℂ) * ζ ^ 5 - ((2309 / 237) : ℂ) * ζ ^ 6 - ((1073 / 158) : ℂ) * ζ ^ 9 + ((1411 / 237) : ℂ) * ζ ^ 11 + ((4561 / 237) : ℂ) * ζ ^ 12 + ((1042 / 79) : ℂ) * ζ ^ 13 - ((6649 / 474) : ℂ) * ζ ^ 15 + ((1042 / 79) : ℂ) * ζ ^ 17 + ((843 / 79) : ℂ) * ζ ^ 18 + ((14 / 79) : ℂ) * ζ ^ 21 + ((2419 / 237) : ℂ) * ζ ^ 22 - ((8765 / 474) : ℂ) * ζ ^ 24 - ((1715 / 237) : ℂ) * ζ ^ 25 + ((1715 / 237) : ℂ) * ζ ^ 27 - ((1042 / 79) : ℂ) * ζ ^ 29 - ((4838 / 237) : ℂ) * ζ ^ 30 - ((1411 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep01CoefficientIdentity01 :
    row18_reducedY76_combinationStep01Coefficient01 =
      row18_reducedY76_combinationStep00Coefficient01 +
        row18_reducedY76_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep01Coefficient01 row18_reducedY76_combinationStep00Coefficient01 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 (((380353 / 187230) : ℂ) - ((352504 / 93615) : ℂ) * ζ ^ 1 - ((224684 / 93615) : ℂ) * ζ ^ 2 - ((181672 / 18723) : ℂ) * ζ ^ 3 + ((478174 / 93615) : ℂ) * ζ ^ 4 + ((550609 / 31205) : ℂ) * ζ ^ 5 + ((2130269 / 187230) : ℂ) * ζ ^ 6 + ((164889 / 62410) : ℂ) * ζ ^ 7 - ((919643 / 62410) : ℂ) * ζ ^ 8 - ((710086 / 93615) : ℂ) * ζ ^ 9 + ((55743 / 12482) : ℂ) * ζ ^ 10 + ((855143 / 187230) : ℂ) * ζ ^ 11 + ((1395343 / 93615) : ℂ) * ζ ^ 12 + ((1242457 / 187230) : ℂ) * ζ ^ 13 - ((70075 / 37446) : ℂ) * ζ ^ 14 + ((434423 / 187230) : ℂ) * ζ ^ 15 - ((1052581 / 187230) : ℂ) * ζ ^ 16 - ((127906 / 93615) : ℂ) * ζ ^ 17 + ((1007873 / 93615) : ℂ) * ζ ^ 18 + ((305483 / 31205) : ℂ) * ζ ^ 19 + ((53117 / 93615) : ℂ) * ζ ^ 20 - ((539909 / 62410) : ℂ) * ζ ^ 21 - ((711502 / 93615) : ℂ) * ζ ^ 22 - ((126168 / 31205) : ℂ) * ζ ^ 23 - ((340619 / 93615) : ℂ) * ζ ^ 24 - ((12364 / 18723) : ℂ) * ζ ^ 25 + ((539237 / 187230) : ℂ) * ζ ^ 26 + ((285542 / 93615) : ℂ) * ζ ^ 27 + ((58817 / 31205) : ℂ) * ζ ^ 28 - ((17236 / 31205) : ℂ) * ζ ^ 29 - ((60326 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep01Coefficient02 : ℂ :=
  (-((490 / 237) : ℂ) + ((523 / 79) : ℂ) * ζ ^ 1 + ((4048 / 237) : ℂ) * ζ ^ 2 - ((767 / 158) : ℂ) * ζ ^ 3 + ((21 / 158) : ℂ) * ζ ^ 5 + ((1505 / 158) : ℂ) * ζ ^ 8 + ((1520 / 237) : ℂ) * ζ ^ 9 - ((739 / 474) : ℂ) * ζ ^ 11 - ((2555 / 474) : ℂ) * ζ ^ 12 - ((523 / 79) : ℂ) * ζ ^ 13 + ((896 / 79) : ℂ) * ζ ^ 15 - ((523 / 79) : ℂ) * ζ ^ 17 - ((4048 / 237) : ℂ) * ζ ^ 18 - ((1813 / 158) : ℂ) * ζ ^ 21 - ((4048 / 237) : ℂ) * ζ ^ 22 - ((980 / 237) : ℂ) * ζ ^ 24 + ((1025 / 158) : ℂ) * ζ ^ 25 - ((1813 / 158) : ℂ) * ζ ^ 27 - ((1505 / 158) : ℂ) * ζ ^ 28 + ((523 / 79) : ℂ) * ζ ^ 29 + ((2345 / 158) : ℂ) * ζ ^ 30 + ((739 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep01CoefficientIdentity02 :
    row18_reducedY76_combinationStep01Coefficient02 =
      row18_reducedY76_combinationStep00Coefficient02 +
        row18_reducedY76_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep01Coefficient02 row18_reducedY76_combinationStep00Coefficient02 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep01Coefficient03 : ℂ :=
  (-((687 / 79) : ℂ) - ((1771 / 237) : ℂ) * ζ ^ 1 - ((1739 / 237) : ℂ) * ζ ^ 2 - ((119 / 79) : ℂ) * ζ ^ 5 + ((322 / 237) : ℂ) * ζ ^ 6 + ((322 / 237) : ℂ) * ζ ^ 8 - ((119 / 79) : ℂ) * ζ ^ 9 + ((2947 / 474) : ℂ) * ζ ^ 11 + ((6025 / 474) : ℂ) * ζ ^ 12 + ((1771 / 237) : ℂ) * ζ ^ 13 - ((2180 / 237) : ℂ) * ζ ^ 15 + ((1771 / 237) : ℂ) * ζ ^ 17 + ((933 / 158) : ℂ) * ζ ^ 18 + ((1064 / 237) : ℂ) * ζ ^ 21 + ((1739 / 237) : ℂ) * ζ ^ 22 - ((3443 / 474) : ℂ) * ζ ^ 24 - ((1414 / 237) : ℂ) * ζ ^ 25 + ((2180 / 237) : ℂ) * ζ ^ 27 - ((322 / 237) : ℂ) * ζ ^ 28 - ((1771 / 237) : ℂ) * ζ ^ 29 - ((5381 / 474) : ℂ) * ζ ^ 30 - ((2947 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep01CoefficientIdentity03 :
    row18_reducedY76_combinationStep01Coefficient03 =
      row18_reducedY76_combinationStep00Coefficient03 +
        row18_reducedY76_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep01Coefficient03 row18_reducedY76_combinationStep00Coefficient03 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 (((1186621 / 93615) : ℂ) + ((1136542 / 93615) : ℂ) * ζ ^ 1 + ((464429 / 93615) : ℂ) * ζ ^ 2 - ((970013 / 187230) : ℂ) * ζ ^ 3 - ((1034561 / 62410) : ℂ) * ζ ^ 4 - ((294383 / 31205) : ℂ) * ζ ^ 5 - ((19643 / 187230) : ℂ) * ζ ^ 6 + ((1334657 / 187230) : ℂ) * ζ ^ 7 + ((150662 / 18723) : ℂ) * ζ ^ 8 - ((420733 / 187230) : ℂ) * ζ ^ 9 - ((164813 / 62410) : ℂ) * ζ ^ 10 - ((90284 / 31205) : ℂ) * ζ ^ 11 - ((404003 / 93615) : ℂ) * ζ ^ 12 - ((136661 / 187230) : ℂ) * ζ ^ 13 - ((3019 / 62410) : ℂ) * ζ ^ 14 + ((438154 / 93615) : ℂ) * ζ ^ 15 + ((994723 / 187230) : ℂ) * ζ ^ 16 + ((103058 / 93615) : ℂ) * ζ ^ 17 - ((33036 / 31205) : ℂ) * ζ ^ 18 - ((166924 / 31205) : ℂ) * ζ ^ 19 - ((109677 / 31205) : ℂ) * ζ ^ 20 + ((153218 / 93615) : ℂ) * ζ ^ 21 + ((585679 / 187230) : ℂ) * ζ ^ 22 + ((165629 / 37446) : ℂ) * ζ ^ 23 + ((91625 / 18723) : ℂ) * ζ ^ 24 + ((75306 / 31205) : ℂ) * ζ ^ 25 - ((370567 / 187230) : ℂ) * ζ ^ 26 - ((134291 / 37446) : ℂ) * ζ ^ 27 - ((194287 / 187230) : ℂ) * ζ ^ 28 + ((38781 / 62410) : ℂ) * ζ ^ 29 + ((4309 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep01CoefficientIdentity04 :
    row18_reducedY76_combinationStep01Coefficient04 =
      row18_reducedY76_combinationStep00Coefficient04 +
        row18_reducedY76_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep01Coefficient04 row18_reducedY76_combinationStep00Coefficient04 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep01CoefficientIdentity05 :
    row18_reducedY76_combinationStep01Coefficient05 =
      row18_reducedY76_combinationStep00Coefficient05 +
        row18_reducedY76_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep01Coefficient05 row18_reducedY76_combinationStep00Coefficient05 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep01CoefficientIdentity06 :
    row18_reducedY76_combinationStep01Coefficient06 =
      row18_reducedY76_combinationStep00Coefficient06 +
        row18_reducedY76_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep01Coefficient06 row18_reducedY76_combinationStep00Coefficient06 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep01CoefficientIdentity07 :
    row18_reducedY76_combinationStep01Coefficient07 =
      row18_reducedY76_combinationStep00Coefficient07 +
        row18_reducedY76_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep01Coefficient07 row18_reducedY76_combinationStep00Coefficient07 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep01CoefficientIdentity08 :
    row18_reducedY76_combinationStep01Coefficient08 =
      row18_reducedY76_combinationStep00Coefficient08 +
        row18_reducedY76_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep01Coefficient08 row18_reducedY76_combinationStep00Coefficient08 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep01CoefficientIdentity09 :
    row18_reducedY76_combinationStep01Coefficient09 =
      row18_reducedY76_combinationStep00Coefficient09 +
        row18_reducedY76_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep01Coefficient09 row18_reducedY76_combinationStep00Coefficient09 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep01CoefficientIdentity10 :
    row18_reducedY76_combinationStep01Coefficient10 =
      row18_reducedY76_combinationStep00Coefficient10 +
        row18_reducedY76_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep01Coefficient10 row18_reducedY76_combinationStep00Coefficient10 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep01CoefficientIdentity11 :
    row18_reducedY76_combinationStep01Coefficient11 =
      row18_reducedY76_combinationStep00Coefficient11 +
        row18_reducedY76_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep01Coefficient11 row18_reducedY76_combinationStep00Coefficient11 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep01CoefficientIdentity12 :
    row18_reducedY76_combinationStep01Coefficient12 =
      row18_reducedY76_combinationStep00Coefficient12 +
        row18_reducedY76_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep01Coefficient12 row18_reducedY76_combinationStep00Coefficient12 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep01CoefficientIdentity13 :
    row18_reducedY76_combinationStep01Coefficient13 =
      row18_reducedY76_combinationStep00Coefficient13 +
        row18_reducedY76_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep01Coefficient13 row18_reducedY76_combinationStep00Coefficient13 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep01CoefficientIdentity14 :
    row18_reducedY76_combinationStep01Coefficient14 =
      row18_reducedY76_combinationStep00Coefficient14 +
        row18_reducedY76_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep01Coefficient14 row18_reducedY76_combinationStep00Coefficient14 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep01CoefficientIdentity15 :
    row18_reducedY76_combinationStep01Coefficient15 =
      row18_reducedY76_combinationStep00Coefficient15 +
        row18_reducedY76_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep01Coefficient15 row18_reducedY76_combinationStep00Coefficient15 row18_reducedY76_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY76_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY76_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY76_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY76_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY76_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY76_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY76_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY76_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY76_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY76_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY76_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY76_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY76_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY76_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY76_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY76_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY76_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY76_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY76_combinationStep01CoefficientIdentity00,
      row18_reducedY76_combinationStep01CoefficientIdentity01,
      row18_reducedY76_combinationStep01CoefficientIdentity02,
      row18_reducedY76_combinationStep01CoefficientIdentity03,
      row18_reducedY76_combinationStep01CoefficientIdentity04,
      row18_reducedY76_combinationStep01CoefficientIdentity05,
      row18_reducedY76_combinationStep01CoefficientIdentity06,
      row18_reducedY76_combinationStep01CoefficientIdentity07,
      row18_reducedY76_combinationStep01CoefficientIdentity08,
      row18_reducedY76_combinationStep01CoefficientIdentity09,
      row18_reducedY76_combinationStep01CoefficientIdentity10,
      row18_reducedY76_combinationStep01CoefficientIdentity11,
      row18_reducedY76_combinationStep01CoefficientIdentity12,
      row18_reducedY76_combinationStep01CoefficientIdentity13,
      row18_reducedY76_combinationStep01CoefficientIdentity14,
      row18_reducedY76_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY76_combinationStep01Multiplier * equation

private def row18_reducedY76_combinationStep02Multiplier : ℂ :=
  (-((10732 / 1185) : ℂ) - ((55642 / 1185) : ℂ) * ζ ^ 1 - ((8996 / 1185) : ℂ) * ζ ^ 2 + ((2534 / 1185) : ℂ) * ζ ^ 5 + ((1736 / 1185) : ℂ) * ζ ^ 6 + ((1736 / 1185) : ℂ) * ζ ^ 8 + ((2534 / 1185) : ℂ) * ζ ^ 9 + ((6350 / 237) : ℂ) * ζ ^ 11 + ((17266 / 395) : ℂ) * ζ ^ 12 + ((55642 / 1185) : ℂ) * ζ ^ 13 - ((816 / 79) : ℂ) * ζ ^ 15 + ((55642 / 1185) : ℂ) * ζ ^ 17 + ((39748 / 1185) : ℂ) * ζ ^ 18 + ((26554 / 1185) : ℂ) * ζ ^ 21 + ((8996 / 1185) : ℂ) * ζ ^ 22 - ((13828 / 395) : ℂ) * ζ ^ 24 - ((19392 / 395) : ℂ) * ζ ^ 25 + ((816 / 79) : ℂ) * ζ ^ 27 - ((1736 / 1185) : ℂ) * ζ ^ 28 - ((55642 / 1185) : ℂ) * ζ ^ 29 - ((50062 / 1185) : ℂ) * ζ ^ 30 - ((6350 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY76_combinationStep02Coefficient00 : ℂ :=
  (-((1703 / 2370) : ℂ) + ((20551 / 2370) : ℂ) * ζ ^ 1 - ((3293 / 790) : ℂ) * ζ ^ 2 - ((2699 / 790) : ℂ) * ζ ^ 5 - ((4088 / 1185) : ℂ) * ζ ^ 6 - ((4088 / 1185) : ℂ) * ζ ^ 8 - ((2699 / 790) : ℂ) * ζ ^ 9 - ((3521 / 474) : ℂ) * ζ ^ 11 - ((5911 / 790) : ℂ) * ζ ^ 12 - ((20551 / 2370) : ℂ) * ζ ^ 13 - ((277 / 158) : ℂ) * ζ ^ 15 - ((20551 / 2370) : ℂ) * ζ ^ 17 - ((1228 / 395) : ℂ) * ζ ^ 18 - ((6227 / 2370) : ℂ) * ζ ^ 21 + ((3293 / 790) : ℂ) * ζ ^ 22 + ((7772 / 1185) : ℂ) * ζ ^ 24 + ((14324 / 1185) : ℂ) * ζ ^ 25 + ((277 / 158) : ℂ) * ζ ^ 27 + ((4088 / 1185) : ℂ) * ζ ^ 28 + ((20551 / 2370) : ℂ) * ζ ^ 29 + ((9557 / 2370) : ℂ) * ζ ^ 30 + ((3521 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep02CoefficientIdentity00 :
    row18_reducedY76_combinationStep02Coefficient00 =
      row18_reducedY76_combinationStep01Coefficient00 +
        row18_reducedY76_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep02Coefficient00 row18_reducedY76_combinationStep01Coefficient00 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 (((1827119 / 187230) : ℂ) + ((50387 / 187230) : ℂ) * ζ ^ 1 + ((393051 / 31205) : ℂ) * ζ ^ 2 + ((460915 / 37446) : ℂ) * ζ ^ 3 - ((1500431 / 187230) : ℂ) * ζ ^ 4 + ((94906 / 18723) : ℂ) * ζ ^ 5 - ((126295 / 18723) : ℂ) * ζ ^ 6 - ((713494 / 93615) : ℂ) * ζ ^ 7 + ((1766419 / 187230) : ℂ) * ζ ^ 8 - ((94063 / 18723) : ℂ) * ζ ^ 9 + ((677728 / 93615) : ℂ) * ζ ^ 10 + ((476441 / 62410) : ℂ) * ζ ^ 11 - ((292663 / 62410) : ℂ) * ζ ^ 12 - ((503383 / 93615) : ℂ) * ζ ^ 13 - ((374428 / 93615) : ℂ) * ζ ^ 14 + ((28546 / 6241) : ℂ) * ζ ^ 15 + ((299048 / 31205) : ℂ) * ζ ^ 16 + ((562001 / 62410) : ℂ) * ζ ^ 17 + ((610283 / 187230) : ℂ) * ζ ^ 18 - ((95732 / 18723) : ℂ) * ζ ^ 19 - ((48682 / 31205) : ℂ) * ζ ^ 20 - ((1159823 / 187230) : ℂ) * ζ ^ 21 - ((476221 / 62410) : ℂ) * ζ ^ 22 - ((757331 / 93615) : ℂ) * ζ ^ 23 - ((163972 / 31205) : ℂ) * ζ ^ 24 + ((318649 / 93615) : ℂ) * ζ ^ 25 + ((228499 / 62410) : ℂ) * ζ ^ 26 + ((118878 / 31205) : ℂ) * ζ ^ 27 - ((54541 / 62410) : ℂ) * ζ ^ 28 - ((48217 / 93615) : ℂ) * ζ ^ 29 - ((22225 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep02Coefficient01 : ℂ :=
  (-((749 / 237) : ℂ) - ((4451 / 158) : ℂ) * ζ ^ 1 - ((444 / 79) : ℂ) * ζ ^ 2 + ((5605 / 474) : ℂ) * ζ ^ 3 - ((3899 / 474) : ℂ) * ζ ^ 5 + ((693 / 79) : ℂ) * ζ ^ 6 + ((2942 / 237) : ℂ) * ζ ^ 9 + ((3899 / 474) : ℂ) * ζ ^ 11 + ((6245 / 237) : ℂ) * ζ ^ 12 + ((4451 / 158) : ℂ) * ζ ^ 13 - ((595 / 79) : ℂ) * ζ ^ 15 + ((4451 / 158) : ℂ) * ζ ^ 17 + ((1581 / 79) : ℂ) * ζ ^ 18 + ((1584 / 79) : ℂ) * ζ ^ 21 + ((444 / 79) : ℂ) * ζ ^ 22 - ((749 / 237) : ℂ) * ζ ^ 24 - ((4727 / 237) : ℂ) * ζ ^ 25 + ((4727 / 237) : ℂ) * ζ ^ 27 - ((4451 / 158) : ℂ) * ζ ^ 29 - ((888 / 79) : ℂ) * ζ ^ 30 - ((3899 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep02CoefficientIdentity01 :
    row18_reducedY76_combinationStep02Coefficient01 =
      row18_reducedY76_combinationStep01Coefficient01 +
        row18_reducedY76_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep02Coefficient01 row18_reducedY76_combinationStep01Coefficient01 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 (-((3240719 / 187230) : ℂ) + ((670678 / 93615) : ℂ) * ζ ^ 1 + ((1147399 / 187230) : ℂ) * ζ ^ 2 - ((110102 / 6241) : ℂ) * ζ ^ 3 + ((2476891 / 187230) : ℂ) * ζ ^ 4 - ((244678 / 93615) : ℂ) * ζ ^ 5 - ((543097 / 37446) : ℂ) * ζ ^ 6 + ((96865 / 12482) : ℂ) * ζ ^ 7 - ((2308541 / 187230) : ℂ) * ζ ^ 8 - ((135619 / 18723) : ℂ) * ζ ^ 9 + ((246983 / 93615) : ℂ) * ζ ^ 10 - ((103657 / 18723) : ℂ) * ζ ^ 11 - ((1233779 / 187230) : ℂ) * ζ ^ 12 - ((74389 / 93615) : ℂ) * ζ ^ 13 - ((553724 / 31205) : ℂ) * ζ ^ 14 - ((1547174 / 93615) : ℂ) * ζ ^ 15 + ((156145 / 37446) : ℂ) * ζ ^ 16 - ((448199 / 62410) : ℂ) * ζ ^ 17 - ((16381 / 790) : ℂ) * ζ ^ 18 - ((48223 / 12482) : ℂ) * ζ ^ 19 - ((1672978 / 93615) : ℂ) * ζ ^ 20 - ((2831771 / 187230) : ℂ) * ζ ^ 21 - ((2101747 / 187230) : ℂ) * ζ ^ 22 - ((1317437 / 93615) : ℂ) * ζ ^ 23 - ((412322 / 93615) : ℂ) * ζ ^ 24 - ((783373 / 187230) : ℂ) * ζ ^ 25 + ((17481 / 6241) : ℂ) * ζ ^ 26 - ((624233 / 187230) : ℂ) * ζ ^ 27 - ((60662 / 31205) : ℂ) * ζ ^ 28 - ((1182653 / 187230) : ℂ) * ζ ^ 29 - ((41275 / 37446) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep02Coefficient02 : ℂ :=
  (-((490 / 237) : ℂ) + ((523 / 79) : ℂ) * ζ ^ 1 + ((4048 / 237) : ℂ) * ζ ^ 2 - ((767 / 158) : ℂ) * ζ ^ 3 + ((21 / 158) : ℂ) * ζ ^ 5 + ((1505 / 158) : ℂ) * ζ ^ 8 + ((1520 / 237) : ℂ) * ζ ^ 9 - ((739 / 474) : ℂ) * ζ ^ 11 - ((2555 / 474) : ℂ) * ζ ^ 12 - ((523 / 79) : ℂ) * ζ ^ 13 + ((896 / 79) : ℂ) * ζ ^ 15 - ((523 / 79) : ℂ) * ζ ^ 17 - ((4048 / 237) : ℂ) * ζ ^ 18 - ((1813 / 158) : ℂ) * ζ ^ 21 - ((4048 / 237) : ℂ) * ζ ^ 22 - ((980 / 237) : ℂ) * ζ ^ 24 + ((1025 / 158) : ℂ) * ζ ^ 25 - ((1813 / 158) : ℂ) * ζ ^ 27 - ((1505 / 158) : ℂ) * ζ ^ 28 + ((523 / 79) : ℂ) * ζ ^ 29 + ((2345 / 158) : ℂ) * ζ ^ 30 + ((739 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep02CoefficientIdentity02 :
    row18_reducedY76_combinationStep02Coefficient02 =
      row18_reducedY76_combinationStep01Coefficient02 +
        row18_reducedY76_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep02Coefficient02 row18_reducedY76_combinationStep01Coefficient02 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep02Coefficient03 : ℂ :=
  (-((687 / 79) : ℂ) - ((1771 / 237) : ℂ) * ζ ^ 1 - ((1739 / 237) : ℂ) * ζ ^ 2 - ((119 / 79) : ℂ) * ζ ^ 5 + ((322 / 237) : ℂ) * ζ ^ 6 + ((322 / 237) : ℂ) * ζ ^ 8 - ((119 / 79) : ℂ) * ζ ^ 9 + ((2947 / 474) : ℂ) * ζ ^ 11 + ((6025 / 474) : ℂ) * ζ ^ 12 + ((1771 / 237) : ℂ) * ζ ^ 13 - ((2180 / 237) : ℂ) * ζ ^ 15 + ((1771 / 237) : ℂ) * ζ ^ 17 + ((933 / 158) : ℂ) * ζ ^ 18 + ((1064 / 237) : ℂ) * ζ ^ 21 + ((1739 / 237) : ℂ) * ζ ^ 22 - ((3443 / 474) : ℂ) * ζ ^ 24 - ((1414 / 237) : ℂ) * ζ ^ 25 + ((2180 / 237) : ℂ) * ζ ^ 27 - ((322 / 237) : ℂ) * ζ ^ 28 - ((1771 / 237) : ℂ) * ζ ^ 29 - ((5381 / 474) : ℂ) * ζ ^ 30 - ((2947 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep02CoefficientIdentity03 :
    row18_reducedY76_combinationStep02Coefficient03 =
      row18_reducedY76_combinationStep01Coefficient03 +
        row18_reducedY76_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep02Coefficient03 row18_reducedY76_combinationStep01Coefficient03 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep02Coefficient04 : ℂ :=
  (((22313 / 2370) : ℂ) - ((947 / 790) : ℂ) * ζ ^ 1 + ((27269 / 2370) : ℂ) * ζ ^ 2 + ((3889 / 790) : ℂ) * ζ ^ 5 + ((826 / 395) : ℂ) * ζ ^ 6 + ((826 / 395) : ℂ) * ζ ^ 8 + ((3889 / 790) : ℂ) * ζ ^ 9 + ((287 / 237) : ℂ) * ζ ^ 11 - ((6196 / 1185) : ℂ) * ζ ^ 12 + ((947 / 790) : ℂ) * ζ ^ 13 + ((5191 / 474) : ℂ) * ζ ^ 15 + ((947 / 790) : ℂ) * ζ ^ 17 - ((2209 / 790) : ℂ) * ζ ^ 18 - ((1471 / 790) : ℂ) * ζ ^ 21 - ((27269 / 2370) : ℂ) * ζ ^ 22 + ((557 / 790) : ℂ) * ζ ^ 24 - ((2418 / 395) : ℂ) * ζ ^ 25 - ((5191 / 474) : ℂ) * ζ ^ 27 - ((826 / 395) : ℂ) * ζ ^ 28 - ((947 / 790) : ℂ) * ζ ^ 29 + ((8674 / 1185) : ℂ) * ζ ^ 30 - ((287 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep02CoefficientIdentity04 :
    row18_reducedY76_combinationStep02Coefficient04 =
      row18_reducedY76_combinationStep01Coefficient04 +
        row18_reducedY76_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep02Coefficient04 row18_reducedY76_combinationStep01Coefficient04 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 (-((1827119 / 187230) : ℂ) - ((50387 / 187230) : ℂ) * ζ ^ 1 - ((393051 / 31205) : ℂ) * ζ ^ 2 - ((460915 / 37446) : ℂ) * ζ ^ 3 + ((1500431 / 187230) : ℂ) * ζ ^ 4 - ((94906 / 18723) : ℂ) * ζ ^ 5 + ((126295 / 18723) : ℂ) * ζ ^ 6 + ((713494 / 93615) : ℂ) * ζ ^ 7 - ((1766419 / 187230) : ℂ) * ζ ^ 8 + ((94063 / 18723) : ℂ) * ζ ^ 9 - ((677728 / 93615) : ℂ) * ζ ^ 10 - ((476441 / 62410) : ℂ) * ζ ^ 11 + ((292663 / 62410) : ℂ) * ζ ^ 12 + ((503383 / 93615) : ℂ) * ζ ^ 13 + ((374428 / 93615) : ℂ) * ζ ^ 14 - ((28546 / 6241) : ℂ) * ζ ^ 15 - ((299048 / 31205) : ℂ) * ζ ^ 16 - ((562001 / 62410) : ℂ) * ζ ^ 17 - ((610283 / 187230) : ℂ) * ζ ^ 18 + ((95732 / 18723) : ℂ) * ζ ^ 19 + ((48682 / 31205) : ℂ) * ζ ^ 20 + ((1159823 / 187230) : ℂ) * ζ ^ 21 + ((476221 / 62410) : ℂ) * ζ ^ 22 + ((757331 / 93615) : ℂ) * ζ ^ 23 + ((163972 / 31205) : ℂ) * ζ ^ 24 - ((318649 / 93615) : ℂ) * ζ ^ 25 - ((228499 / 62410) : ℂ) * ζ ^ 26 - ((118878 / 31205) : ℂ) * ζ ^ 27 + ((54541 / 62410) : ℂ) * ζ ^ 28 + ((48217 / 93615) : ℂ) * ζ ^ 29 + ((22225 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep02CoefficientIdentity05 :
    row18_reducedY76_combinationStep02Coefficient05 =
      row18_reducedY76_combinationStep01Coefficient05 +
        row18_reducedY76_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep02Coefficient05 row18_reducedY76_combinationStep01Coefficient05 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep02Coefficient06 : ℂ :=
  (((3105 / 79) : ℂ) + ((39689 / 1185) : ℂ) * ζ ^ 1 - ((9218 / 1185) : ℂ) * ζ ^ 2 - ((441 / 10) : ℂ) * ζ ^ 3 + ((418 / 15) : ℂ) * ζ ^ 5 + ((12386 / 395) : ℂ) * ζ ^ 6 - ((1808 / 79) : ℂ) * ζ ^ 8 - ((53131 / 2370) : ℂ) * ζ ^ 9 + ((25693 / 1185) : ℂ) * ζ ^ 11 - ((1808 / 79) : ℂ) * ζ ^ 12 - ((39689 / 1185) : ℂ) * ζ ^ 13 + ((91183 / 2370) : ℂ) * ζ ^ 15 - ((39689 / 1185) : ℂ) * ζ ^ 17 - ((46376 / 1185) : ℂ) * ζ ^ 18 + ((25139 / 2370) : ℂ) * ζ ^ 21 + ((9218 / 1185) : ℂ) * ζ ^ 22 + ((6667 / 1185) : ℂ) * ζ ^ 25 - ((25139 / 2370) : ℂ) * ζ ^ 27 + ((1808 / 79) : ℂ) * ζ ^ 28 + ((39689 / 1185) : ℂ) * ζ ^ 29 + ((6193 / 395) : ℂ) * ζ ^ 30 - ((25693 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep02CoefficientIdentity06 :
    row18_reducedY76_combinationStep02Coefficient06 =
      row18_reducedY76_combinationStep01Coefficient06 +
        row18_reducedY76_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep02Coefficient06 row18_reducedY76_combinationStep01Coefficient06 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 (-((3577471 / 93615) : ℂ) - ((2641711 / 93615) : ℂ) * ζ ^ 1 + ((1324721 / 187230) : ℂ) * ζ ^ 2 + ((1395936 / 31205) : ℂ) * ζ ^ 3 + ((3268358 / 93615) : ℂ) * ζ ^ 4 - ((45076 / 93615) : ℂ) * ζ ^ 5 - ((3514877 / 93615) : ℂ) * ζ ^ 6 - ((1486471 / 37446) : ℂ) * ζ ^ 7 - ((1213771 / 93615) : ℂ) * ζ ^ 8 + ((1089644 / 93615) : ℂ) * ζ ^ 9 + ((4434331 / 187230) : ℂ) * ζ ^ 10 + ((1218043 / 93615) : ℂ) * ζ ^ 11 - ((339299 / 93615) : ℂ) * ζ ^ 12 - ((123512 / 18723) : ℂ) * ζ ^ 13 - ((2058571 / 187230) : ℂ) * ζ ^ 14 - ((378149 / 93615) : ℂ) * ζ ^ 15 + ((13019 / 187230) : ℂ) * ζ ^ 16 + ((67009 / 18723) : ℂ) * ζ ^ 17 + ((945503 / 62410) : ℂ) * ζ ^ 18 + ((1213969 / 93615) : ℂ) * ζ ^ 19 + ((364729 / 187230) : ℂ) * ζ ^ 20 - ((1802707 / 187230) : ℂ) * ζ ^ 21 - ((532239 / 31205) : ℂ) * ζ ^ 22 - ((244831 / 31205) : ℂ) * ζ ^ 23 + ((173057 / 18723) : ℂ) * ζ ^ 24 + ((229123 / 12482) : ℂ) * ζ ^ 25 + ((820771 / 93615) : ℂ) * ζ ^ 26 - ((368603 / 93615) : ℂ) * ζ ^ 27 - ((912589 / 93615) : ℂ) * ζ ^ 28 - ((75831 / 12482) : ℂ) * ζ ^ 29 - ((15875 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep02CoefficientIdentity07 :
    row18_reducedY76_combinationStep02Coefficient07 =
      row18_reducedY76_combinationStep01Coefficient07 +
        row18_reducedY76_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep02Coefficient07 row18_reducedY76_combinationStep01Coefficient07 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep02CoefficientIdentity08 :
    row18_reducedY76_combinationStep02Coefficient08 =
      row18_reducedY76_combinationStep01Coefficient08 +
        row18_reducedY76_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep02Coefficient08 row18_reducedY76_combinationStep01Coefficient08 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep02CoefficientIdentity09 :
    row18_reducedY76_combinationStep02Coefficient09 =
      row18_reducedY76_combinationStep01Coefficient09 +
        row18_reducedY76_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep02Coefficient09 row18_reducedY76_combinationStep01Coefficient09 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep02CoefficientIdentity10 :
    row18_reducedY76_combinationStep02Coefficient10 =
      row18_reducedY76_combinationStep01Coefficient10 +
        row18_reducedY76_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep02Coefficient10 row18_reducedY76_combinationStep01Coefficient10 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep02CoefficientIdentity11 :
    row18_reducedY76_combinationStep02Coefficient11 =
      row18_reducedY76_combinationStep01Coefficient11 +
        row18_reducedY76_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep02Coefficient11 row18_reducedY76_combinationStep01Coefficient11 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep02CoefficientIdentity12 :
    row18_reducedY76_combinationStep02Coefficient12 =
      row18_reducedY76_combinationStep01Coefficient12 +
        row18_reducedY76_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep02Coefficient12 row18_reducedY76_combinationStep01Coefficient12 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep02CoefficientIdentity13 :
    row18_reducedY76_combinationStep02Coefficient13 =
      row18_reducedY76_combinationStep01Coefficient13 +
        row18_reducedY76_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep02Coefficient13 row18_reducedY76_combinationStep01Coefficient13 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep02CoefficientIdentity14 :
    row18_reducedY76_combinationStep02Coefficient14 =
      row18_reducedY76_combinationStep01Coefficient14 +
        row18_reducedY76_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep02Coefficient14 row18_reducedY76_combinationStep01Coefficient14 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep02CoefficientIdentity15 :
    row18_reducedY76_combinationStep02Coefficient15 =
      row18_reducedY76_combinationStep01Coefficient15 +
        row18_reducedY76_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep02Coefficient15 row18_reducedY76_combinationStep01Coefficient15 row18_reducedY76_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY76_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY76_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY76_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY76_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY76_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY76_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY76_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY76_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY76_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY76_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY76_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY76_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY76_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY76_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY76_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY76_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY76_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY76_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY76_combinationStep02CoefficientIdentity00,
      row18_reducedY76_combinationStep02CoefficientIdentity01,
      row18_reducedY76_combinationStep02CoefficientIdentity02,
      row18_reducedY76_combinationStep02CoefficientIdentity03,
      row18_reducedY76_combinationStep02CoefficientIdentity04,
      row18_reducedY76_combinationStep02CoefficientIdentity05,
      row18_reducedY76_combinationStep02CoefficientIdentity06,
      row18_reducedY76_combinationStep02CoefficientIdentity07,
      row18_reducedY76_combinationStep02CoefficientIdentity08,
      row18_reducedY76_combinationStep02CoefficientIdentity09,
      row18_reducedY76_combinationStep02CoefficientIdentity10,
      row18_reducedY76_combinationStep02CoefficientIdentity11,
      row18_reducedY76_combinationStep02CoefficientIdentity12,
      row18_reducedY76_combinationStep02CoefficientIdentity13,
      row18_reducedY76_combinationStep02CoefficientIdentity14,
      row18_reducedY76_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY76_combinationStep02Multiplier * equation

private def row18_reducedY76_combinationStep03Multiplier : ℂ :=
  (((640 / 79) : ℂ) + ((2056 / 237) : ℂ) * ζ ^ 1 + ((1816 / 237) : ℂ) * ζ ^ 2 - ((4204 / 237) : ℂ) * ζ ^ 3 + ((4618 / 237) : ℂ) * ζ ^ 5 + ((4000 / 237) : ℂ) * ζ ^ 6 + ((452 / 79) : ℂ) * ζ ^ 8 - ((304 / 79) : ℂ) * ζ ^ 9 + ((4618 / 237) : ℂ) * ζ ^ 11 + ((226 / 79) : ℂ) * ζ ^ 12 - ((2056 / 237) : ℂ) * ζ ^ 13 + ((1158 / 79) : ℂ) * ζ ^ 15 - ((2056 / 237) : ℂ) * ζ ^ 17 - ((4000 / 237) : ℂ) * ζ ^ 18 - ((138 / 79) : ℂ) * ζ ^ 21 - ((1816 / 237) : ℂ) * ζ ^ 22 - ((1092 / 79) : ℂ) * ζ ^ 24 - ((854 / 79) : ℂ) * ζ ^ 25 - ((854 / 79) : ℂ) * ζ ^ 27 - ((452 / 79) : ℂ) * ζ ^ 28 + ((2056 / 237) : ℂ) * ζ ^ 29 - ((4618 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY76_combinationStep03Coefficient00 : ℂ :=
  (-((5991 / 790) : ℂ) - ((959 / 395) : ℂ) * ζ ^ 1 - ((4979 / 395) : ℂ) * ζ ^ 2 - ((3042 / 395) : ℂ) * ζ ^ 5 - ((3967 / 790) : ℂ) * ζ ^ 6 - ((3967 / 790) : ℂ) * ζ ^ 8 - ((3042 / 395) : ℂ) * ζ ^ 9 - ((605 / 158) : ℂ) * ζ ^ 11 + ((4229 / 790) : ℂ) * ζ ^ 12 + ((959 / 395) : ℂ) * ζ ^ 13 - ((912 / 79) : ℂ) * ζ ^ 15 + ((959 / 395) : ℂ) * ζ ^ 17 + ((2797 / 395) : ℂ) * ζ ^ 18 + ((4001 / 790) : ℂ) * ζ ^ 21 + ((4979 / 395) : ℂ) * ζ ^ 22 - ((1627 / 790) : ℂ) * ζ ^ 24 + ((2083 / 395) : ℂ) * ζ ^ 25 + ((912 / 79) : ℂ) * ζ ^ 27 + ((3967 / 790) : ℂ) * ζ ^ 28 - ((959 / 395) : ℂ) * ζ ^ 29 - ((4098 / 395) : ℂ) * ζ ^ 30 + ((605 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep03CoefficientIdentity00 :
    row18_reducedY76_combinationStep03Coefficient00 =
      row18_reducedY76_combinationStep02Coefficient00 +
        row18_reducedY76_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep03Coefficient00 row18_reducedY76_combinationStep02Coefficient00 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 (((146773 / 18723) : ℂ) + ((147401 / 12482) : ℂ) * ζ ^ 1 + ((347621 / 37446) : ℂ) * ζ ^ 2 - ((51706 / 18723) : ℂ) * ζ ^ 3 - ((140452 / 18723) : ℂ) * ζ ^ 4 - ((39821 / 6241) : ℂ) * ζ ^ 5 - ((159695 / 37446) : ℂ) * ζ ^ 6 + ((45921 / 12482) : ℂ) * ζ ^ 7 + ((102113 / 12482) : ℂ) * ζ ^ 8 + ((37491 / 12482) : ℂ) * ζ ^ 9 + ((33157 / 37446) : ℂ) * ζ ^ 10 - ((65431 / 37446) : ℂ) * ζ ^ 11 - ((108776 / 18723) : ℂ) * ζ ^ 12 - ((95224 / 18723) : ℂ) * ζ ^ 13 - ((10045 / 37446) : ℂ) * ζ ^ 14 + ((66067 / 18723) : ℂ) * ζ ^ 15 + ((87460 / 18723) : ℂ) * ζ ^ 16 + ((40201 / 18723) : ℂ) * ζ ^ 17 - ((36172 / 18723) : ℂ) * ζ ^ 18 - ((89272 / 18723) : ℂ) * ζ ^ 19 - ((58348 / 18723) : ℂ) * ζ ^ 20 - ((7633 / 18723) : ℂ) * ζ ^ 21 + ((31191 / 12482) : ℂ) * ζ ^ 22 + ((50105 / 12482) : ℂ) * ζ ^ 23 + ((4451 / 6241) : ℂ) * ζ ^ 24 + ((10061 / 18723) : ℂ) * ζ ^ 25 - ((30875 / 37446) : ℂ) * ζ ^ 26 - ((175405 / 37446) : ℂ) * ζ ^ 27 + ((14597 / 37446) : ℂ) * ζ ^ 28 + ((18472 / 6241) : ℂ) * ζ ^ 29 + ((11545 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep03Coefficient01 : ℂ :=
  (((53 / 79) : ℂ) + ((43 / 79) : ℂ) * ζ ^ 1 + ((35 / 158) : ℂ) * ζ ^ 2 + ((14 / 79) : ℂ) * ζ ^ 3 + ((29 / 79) : ℂ) * ζ ^ 5 + ((29 / 79) : ℂ) * ζ ^ 6 + ((25 / 79) : ℂ) * ζ ^ 9 - ((29 / 79) : ℂ) * ζ ^ 11 - ((7 / 158) : ℂ) * ζ ^ 12 - ((43 / 79) : ℂ) * ζ ^ 13 + ((39 / 79) : ℂ) * ζ ^ 15 - ((43 / 79) : ℂ) * ζ ^ 17 - ((6 / 79) : ℂ) * ζ ^ 18 - ((15 / 79) : ℂ) * ζ ^ 21 - ((35 / 158) : ℂ) * ζ ^ 22 + ((53 / 79) : ℂ) * ζ ^ 24 + ((14 / 79) : ℂ) * ζ ^ 25 - ((14 / 79) : ℂ) * ζ ^ 27 + ((43 / 79) : ℂ) * ζ ^ 29 + ((35 / 79) : ℂ) * ζ ^ 30 + ((29 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep03CoefficientIdentity01 :
    row18_reducedY76_combinationStep03Coefficient01 =
      row18_reducedY76_combinationStep02Coefficient01 +
        row18_reducedY76_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep03Coefficient01 row18_reducedY76_combinationStep02Coefficient01 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 (-((56372 / 18723) : ℂ) - ((987653 / 37446) : ℂ) * ζ ^ 1 + ((11941 / 37446) : ℂ) * ζ ^ 2 + ((499903 / 37446) : ℂ) * ζ ^ 3 + ((24533 / 18723) : ℂ) * ζ ^ 4 + ((225370 / 18723) : ℂ) * ζ ^ 5 + ((380503 / 18723) : ℂ) * ζ ^ 6 + ((23561 / 18723) : ℂ) * ζ ^ 7 - ((124679 / 37446) : ℂ) * ζ ^ 8 - ((19618 / 18723) : ℂ) * ζ ^ 9 - ((181325 / 18723) : ℂ) * ζ ^ 10 + ((172689 / 12482) : ℂ) * ζ ^ 11 + ((292821 / 12482) : ℂ) * ζ ^ 12 + ((181228 / 18723) : ℂ) * ζ ^ 13 + ((157757 / 18723) : ℂ) * ζ ^ 14 - ((140263 / 37446) : ℂ) * ζ ^ 15 - ((75610 / 6241) : ℂ) * ζ ^ 16 + ((313601 / 37446) : ℂ) * ζ ^ 17 + ((291781 / 37446) : ℂ) * ζ ^ 18 + ((27248 / 18723) : ℂ) * ζ ^ 19 + ((83370 / 6241) : ℂ) * ζ ^ 20 + ((305107 / 37446) : ℂ) * ζ ^ 21 - ((363337 / 37446) : ℂ) * ζ ^ 22 - ((63442 / 18723) : ℂ) * ζ ^ 23 - ((725 / 474) : ℂ) * ζ ^ 24 - ((273 / 6241) : ℂ) * ζ ^ 25 + ((63419 / 6241) : ℂ) * ζ ^ 26 - ((3670 / 6241) : ℂ) * ζ ^ 27 - ((102829 / 37446) : ℂ) * ζ ^ 28 - ((9236 / 6241) : ℂ) * ζ ^ 29 - ((32326 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep03Coefficient02 : ℂ :=
  (-((490 / 237) : ℂ) + ((523 / 79) : ℂ) * ζ ^ 1 + ((4048 / 237) : ℂ) * ζ ^ 2 - ((767 / 158) : ℂ) * ζ ^ 3 + ((21 / 158) : ℂ) * ζ ^ 5 + ((1505 / 158) : ℂ) * ζ ^ 8 + ((1520 / 237) : ℂ) * ζ ^ 9 - ((739 / 474) : ℂ) * ζ ^ 11 - ((2555 / 474) : ℂ) * ζ ^ 12 - ((523 / 79) : ℂ) * ζ ^ 13 + ((896 / 79) : ℂ) * ζ ^ 15 - ((523 / 79) : ℂ) * ζ ^ 17 - ((4048 / 237) : ℂ) * ζ ^ 18 - ((1813 / 158) : ℂ) * ζ ^ 21 - ((4048 / 237) : ℂ) * ζ ^ 22 - ((980 / 237) : ℂ) * ζ ^ 24 + ((1025 / 158) : ℂ) * ζ ^ 25 - ((1813 / 158) : ℂ) * ζ ^ 27 - ((1505 / 158) : ℂ) * ζ ^ 28 + ((523 / 79) : ℂ) * ζ ^ 29 + ((2345 / 158) : ℂ) * ζ ^ 30 + ((739 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep03CoefficientIdentity02 :
    row18_reducedY76_combinationStep03Coefficient02 =
      row18_reducedY76_combinationStep02Coefficient02 +
        row18_reducedY76_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep03Coefficient02 row18_reducedY76_combinationStep02Coefficient02 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep03Coefficient03 : ℂ :=
  (-((687 / 79) : ℂ) - ((1771 / 237) : ℂ) * ζ ^ 1 - ((1739 / 237) : ℂ) * ζ ^ 2 - ((119 / 79) : ℂ) * ζ ^ 5 + ((322 / 237) : ℂ) * ζ ^ 6 + ((322 / 237) : ℂ) * ζ ^ 8 - ((119 / 79) : ℂ) * ζ ^ 9 + ((2947 / 474) : ℂ) * ζ ^ 11 + ((6025 / 474) : ℂ) * ζ ^ 12 + ((1771 / 237) : ℂ) * ζ ^ 13 - ((2180 / 237) : ℂ) * ζ ^ 15 + ((1771 / 237) : ℂ) * ζ ^ 17 + ((933 / 158) : ℂ) * ζ ^ 18 + ((1064 / 237) : ℂ) * ζ ^ 21 + ((1739 / 237) : ℂ) * ζ ^ 22 - ((3443 / 474) : ℂ) * ζ ^ 24 - ((1414 / 237) : ℂ) * ζ ^ 25 + ((2180 / 237) : ℂ) * ζ ^ 27 - ((322 / 237) : ℂ) * ζ ^ 28 - ((1771 / 237) : ℂ) * ζ ^ 29 - ((5381 / 474) : ℂ) * ζ ^ 30 - ((2947 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep03CoefficientIdentity03 :
    row18_reducedY76_combinationStep03Coefficient03 =
      row18_reducedY76_combinationStep02Coefficient03 +
        row18_reducedY76_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep03Coefficient03 row18_reducedY76_combinationStep02Coefficient03 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep03Coefficient04 : ℂ :=
  (((22313 / 2370) : ℂ) - ((947 / 790) : ℂ) * ζ ^ 1 + ((27269 / 2370) : ℂ) * ζ ^ 2 + ((3889 / 790) : ℂ) * ζ ^ 5 + ((826 / 395) : ℂ) * ζ ^ 6 + ((826 / 395) : ℂ) * ζ ^ 8 + ((3889 / 790) : ℂ) * ζ ^ 9 + ((287 / 237) : ℂ) * ζ ^ 11 - ((6196 / 1185) : ℂ) * ζ ^ 12 + ((947 / 790) : ℂ) * ζ ^ 13 + ((5191 / 474) : ℂ) * ζ ^ 15 + ((947 / 790) : ℂ) * ζ ^ 17 - ((2209 / 790) : ℂ) * ζ ^ 18 - ((1471 / 790) : ℂ) * ζ ^ 21 - ((27269 / 2370) : ℂ) * ζ ^ 22 + ((557 / 790) : ℂ) * ζ ^ 24 - ((2418 / 395) : ℂ) * ζ ^ 25 - ((5191 / 474) : ℂ) * ζ ^ 27 - ((826 / 395) : ℂ) * ζ ^ 28 - ((947 / 790) : ℂ) * ζ ^ 29 + ((8674 / 1185) : ℂ) * ζ ^ 30 - ((287 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep03CoefficientIdentity04 :
    row18_reducedY76_combinationStep03Coefficient04 =
      row18_reducedY76_combinationStep02Coefficient04 +
        row18_reducedY76_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep03Coefficient04 row18_reducedY76_combinationStep02Coefficient04 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep03Coefficient05 : ℂ :=
  (-((707 / 237) : ℂ) + ((1294 / 237) : ℂ) * ζ ^ 2 + ((217 / 237) : ℂ) * ζ ^ 3 + ((312 / 79) : ℂ) * ζ ^ 5 + ((343 / 158) : ℂ) * ζ ^ 6 + ((523 / 79) : ℂ) * ζ ^ 8 + ((1753 / 474) : ℂ) * ζ ^ 9 + ((312 / 79) : ℂ) * ζ ^ 11 + ((523 / 158) : ℂ) * ζ ^ 12 + ((119 / 474) : ℂ) * ζ ^ 15 - ((343 / 158) : ℂ) * ζ ^ 18 - ((1153 / 237) : ℂ) * ζ ^ 21 - ((1294 / 237) : ℂ) * ζ ^ 22 - ((862 / 237) : ℂ) * ζ ^ 24 - ((312 / 79) : ℂ) * ζ ^ 25 - ((312 / 79) : ℂ) * ζ ^ 27 - ((523 / 79) : ℂ) * ζ ^ 28 - ((312 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep03CoefficientIdentity05 :
    row18_reducedY76_combinationStep03Coefficient05 =
      row18_reducedY76_combinationStep02Coefficient05 +
        row18_reducedY76_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep03Coefficient05 row18_reducedY76_combinationStep02Coefficient05 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 (((61613 / 18723) : ℂ) + ((296 / 6241) : ℂ) * ζ ^ 1 - ((20544 / 6241) : ℂ) * ζ ^ 2 + ((7981 / 18723) : ℂ) * ζ ^ 3 - ((12490 / 18723) : ℂ) * ζ ^ 4 - ((47367 / 6241) : ℂ) * ζ ^ 5 + ((47515 / 18723) : ℂ) * ζ ^ 6 + ((208451 / 37446) : ℂ) * ζ ^ 7 - ((46943 / 18723) : ℂ) * ζ ^ 8 + ((37061 / 37446) : ℂ) * ζ ^ 9 - ((7957 / 37446) : ℂ) * ζ ^ 10 - ((158953 / 37446) : ℂ) * ζ ^ 11 + ((15385 / 6241) : ℂ) * ζ ^ 12 + ((32137 / 18723) : ℂ) * ζ ^ 13 - ((79481 / 18723) : ℂ) * ζ ^ 14 + ((110993 / 18723) : ℂ) * ζ ^ 15 + ((8521 / 6241) : ℂ) * ζ ^ 16 - ((40055 / 12482) : ℂ) * ζ ^ 17 + ((66010 / 18723) : ℂ) * ζ ^ 18 - ((13450 / 6241) : ℂ) * ζ ^ 19 - ((48544 / 18723) : ℂ) * ζ ^ 20 + ((23769 / 6241) : ℂ) * ζ ^ 21 - ((6591 / 12482) : ℂ) * ζ ^ 22 + ((10645 / 18723) : ℂ) * ζ ^ 23 + ((26597 / 18723) : ℂ) * ζ ^ 24 + ((9981 / 6241) : ℂ) * ζ ^ 25 - ((2177 / 12482) : ℂ) * ζ ^ 26 - ((54875 / 37446) : ℂ) * ζ ^ 27 + ((3669 / 12482) : ℂ) * ζ ^ 28 - ((18472 / 18723) : ℂ) * ζ ^ 29 + ((16163 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep03Coefficient06 : ℂ :=
  (((3105 / 79) : ℂ) + ((39689 / 1185) : ℂ) * ζ ^ 1 - ((9218 / 1185) : ℂ) * ζ ^ 2 - ((441 / 10) : ℂ) * ζ ^ 3 + ((418 / 15) : ℂ) * ζ ^ 5 + ((12386 / 395) : ℂ) * ζ ^ 6 - ((1808 / 79) : ℂ) * ζ ^ 8 - ((53131 / 2370) : ℂ) * ζ ^ 9 + ((25693 / 1185) : ℂ) * ζ ^ 11 - ((1808 / 79) : ℂ) * ζ ^ 12 - ((39689 / 1185) : ℂ) * ζ ^ 13 + ((91183 / 2370) : ℂ) * ζ ^ 15 - ((39689 / 1185) : ℂ) * ζ ^ 17 - ((46376 / 1185) : ℂ) * ζ ^ 18 + ((25139 / 2370) : ℂ) * ζ ^ 21 + ((9218 / 1185) : ℂ) * ζ ^ 22 + ((6667 / 1185) : ℂ) * ζ ^ 25 - ((25139 / 2370) : ℂ) * ζ ^ 27 + ((1808 / 79) : ℂ) * ζ ^ 28 + ((39689 / 1185) : ℂ) * ζ ^ 29 + ((6193 / 395) : ℂ) * ζ ^ 30 - ((25693 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep03CoefficientIdentity06 :
    row18_reducedY76_combinationStep03Coefficient06 =
      row18_reducedY76_combinationStep02Coefficient06 +
        row18_reducedY76_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep03Coefficient06 row18_reducedY76_combinationStep02Coefficient06 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep03Coefficient07 : ℂ :=
  (((1627 / 237) : ℂ) + ((5261 / 474) : ℂ) * ζ ^ 1 + ((1333 / 158) : ℂ) * ζ ^ 2 + ((677 / 158) : ℂ) * ζ ^ 5 + ((745 / 474) : ℂ) * ζ ^ 6 + ((745 / 474) : ℂ) * ζ ^ 8 + ((677 / 158) : ℂ) * ζ ^ 9 - ((853 / 237) : ℂ) * ζ ^ 11 - ((1014 / 79) : ℂ) * ζ ^ 12 - ((5261 / 474) : ℂ) * ζ ^ 13 + ((1547 / 158) : ℂ) * ζ ^ 15 - ((5261 / 474) : ℂ) * ζ ^ 17 - ((805 / 79) : ℂ) * ζ ^ 18 - ((1823 / 237) : ℂ) * ζ ^ 21 - ((1333 / 158) : ℂ) * ζ ^ 22 + ((4085 / 474) : ℂ) * ζ ^ 24 + ((1615 / 237) : ℂ) * ζ ^ 25 - ((1547 / 158) : ℂ) * ζ ^ 27 - ((745 / 474) : ℂ) * ζ ^ 28 + ((5261 / 474) : ℂ) * ζ ^ 29 + ((6829 / 474) : ℂ) * ζ ^ 30 + ((853 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep03CoefficientIdentity07 :
    row18_reducedY76_combinationStep03Coefficient07 =
      row18_reducedY76_combinationStep02Coefficient07 +
        row18_reducedY76_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep03Coefficient07 row18_reducedY76_combinationStep02Coefficient07 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 (-((146773 / 18723) : ℂ) - ((147401 / 12482) : ℂ) * ζ ^ 1 - ((347621 / 37446) : ℂ) * ζ ^ 2 + ((51706 / 18723) : ℂ) * ζ ^ 3 + ((140452 / 18723) : ℂ) * ζ ^ 4 + ((39821 / 6241) : ℂ) * ζ ^ 5 + ((159695 / 37446) : ℂ) * ζ ^ 6 - ((45921 / 12482) : ℂ) * ζ ^ 7 - ((102113 / 12482) : ℂ) * ζ ^ 8 - ((37491 / 12482) : ℂ) * ζ ^ 9 - ((33157 / 37446) : ℂ) * ζ ^ 10 + ((65431 / 37446) : ℂ) * ζ ^ 11 + ((108776 / 18723) : ℂ) * ζ ^ 12 + ((95224 / 18723) : ℂ) * ζ ^ 13 + ((10045 / 37446) : ℂ) * ζ ^ 14 - ((66067 / 18723) : ℂ) * ζ ^ 15 - ((87460 / 18723) : ℂ) * ζ ^ 16 - ((40201 / 18723) : ℂ) * ζ ^ 17 + ((36172 / 18723) : ℂ) * ζ ^ 18 + ((89272 / 18723) : ℂ) * ζ ^ 19 + ((58348 / 18723) : ℂ) * ζ ^ 20 + ((7633 / 18723) : ℂ) * ζ ^ 21 - ((31191 / 12482) : ℂ) * ζ ^ 22 - ((50105 / 12482) : ℂ) * ζ ^ 23 - ((4451 / 6241) : ℂ) * ζ ^ 24 - ((10061 / 18723) : ℂ) * ζ ^ 25 + ((30875 / 37446) : ℂ) * ζ ^ 26 + ((175405 / 37446) : ℂ) * ζ ^ 27 - ((14597 / 37446) : ℂ) * ζ ^ 28 - ((18472 / 6241) : ℂ) * ζ ^ 29 - ((11545 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep03CoefficientIdentity08 :
    row18_reducedY76_combinationStep03Coefficient08 =
      row18_reducedY76_combinationStep02Coefficient08 +
        row18_reducedY76_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep03Coefficient08 row18_reducedY76_combinationStep02Coefficient08 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep03CoefficientIdentity09 :
    row18_reducedY76_combinationStep03Coefficient09 =
      row18_reducedY76_combinationStep02Coefficient09 +
        row18_reducedY76_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep03Coefficient09 row18_reducedY76_combinationStep02Coefficient09 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep03CoefficientIdentity10 :
    row18_reducedY76_combinationStep03Coefficient10 =
      row18_reducedY76_combinationStep02Coefficient10 +
        row18_reducedY76_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep03Coefficient10 row18_reducedY76_combinationStep02Coefficient10 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep03CoefficientIdentity11 :
    row18_reducedY76_combinationStep03Coefficient11 =
      row18_reducedY76_combinationStep02Coefficient11 +
        row18_reducedY76_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep03Coefficient11 row18_reducedY76_combinationStep02Coefficient11 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep03CoefficientIdentity12 :
    row18_reducedY76_combinationStep03Coefficient12 =
      row18_reducedY76_combinationStep02Coefficient12 +
        row18_reducedY76_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep03Coefficient12 row18_reducedY76_combinationStep02Coefficient12 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep03CoefficientIdentity13 :
    row18_reducedY76_combinationStep03Coefficient13 =
      row18_reducedY76_combinationStep02Coefficient13 +
        row18_reducedY76_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep03Coefficient13 row18_reducedY76_combinationStep02Coefficient13 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep03CoefficientIdentity14 :
    row18_reducedY76_combinationStep03Coefficient14 =
      row18_reducedY76_combinationStep02Coefficient14 +
        row18_reducedY76_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep03Coefficient14 row18_reducedY76_combinationStep02Coefficient14 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep03CoefficientIdentity15 :
    row18_reducedY76_combinationStep03Coefficient15 =
      row18_reducedY76_combinationStep02Coefficient15 +
        row18_reducedY76_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep03Coefficient15 row18_reducedY76_combinationStep02Coefficient15 row18_reducedY76_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY76_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY76_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY76_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY76_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY76_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY76_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY76_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY76_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY76_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY76_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY76_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY76_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY76_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY76_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY76_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY76_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY76_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY76_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY76_combinationStep03CoefficientIdentity00,
      row18_reducedY76_combinationStep03CoefficientIdentity01,
      row18_reducedY76_combinationStep03CoefficientIdentity02,
      row18_reducedY76_combinationStep03CoefficientIdentity03,
      row18_reducedY76_combinationStep03CoefficientIdentity04,
      row18_reducedY76_combinationStep03CoefficientIdentity05,
      row18_reducedY76_combinationStep03CoefficientIdentity06,
      row18_reducedY76_combinationStep03CoefficientIdentity07,
      row18_reducedY76_combinationStep03CoefficientIdentity08,
      row18_reducedY76_combinationStep03CoefficientIdentity09,
      row18_reducedY76_combinationStep03CoefficientIdentity10,
      row18_reducedY76_combinationStep03CoefficientIdentity11,
      row18_reducedY76_combinationStep03CoefficientIdentity12,
      row18_reducedY76_combinationStep03CoefficientIdentity13,
      row18_reducedY76_combinationStep03CoefficientIdentity14,
      row18_reducedY76_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY76_combinationStep03Multiplier * equation

private def row18_reducedY76_combinationStep04Multiplier : ℂ :=
  (((14 / 79) : ℂ) + ((120 / 79) : ℂ) * ζ ^ 1 + ((218 / 79) : ℂ) * ζ ^ 2 - ((52 / 79) : ℂ) * ζ ^ 5 + ((204 / 79) : ℂ) * ζ ^ 6 + ((204 / 79) : ℂ) * ζ ^ 8 - ((52 / 79) : ℂ) * ζ ^ 9 - ((94 / 79) : ℂ) * ζ ^ 11 + ((2 / 79) : ℂ) * ζ ^ 12 - ((120 / 79) : ℂ) * ζ ^ 13 - ((40 / 79) : ℂ) * ζ ^ 15 - ((120 / 79) : ℂ) * ζ ^ 17 - ((148 / 79) : ℂ) * ζ ^ 18 - ((34 / 79) : ℂ) * ζ ^ 21 - ((218 / 79) : ℂ) * ζ ^ 22 - ((56 / 79) : ℂ) * ζ ^ 24 + ((172 / 79) : ℂ) * ζ ^ 25 + ((40 / 79) : ℂ) * ζ ^ 27 - ((204 / 79) : ℂ) * ζ ^ 28 + ((120 / 79) : ℂ) * ζ ^ 29 + ((202 / 79) : ℂ) * ζ ^ 30 + ((94 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY76_combinationStep04Coefficient00 : ℂ :=
  (-((5571 / 790) : ℂ) - ((914 / 395) : ℂ) * ζ ^ 1 - ((9953 / 790) : ℂ) * ζ ^ 2 - ((3022 / 395) : ℂ) * ζ ^ 5 - ((2191 / 395) : ℂ) * ζ ^ 6 - ((2191 / 395) : ℂ) * ζ ^ 8 - ((3022 / 395) : ℂ) * ζ ^ 9 - ((327 / 79) : ℂ) * ζ ^ 11 + ((3189 / 790) : ℂ) * ζ ^ 12 + ((914 / 395) : ℂ) * ζ ^ 13 - ((872 / 79) : ℂ) * ζ ^ 15 + ((914 / 395) : ℂ) * ζ ^ 17 + ((2702 / 395) : ℂ) * ζ ^ 18 + ((1968 / 395) : ℂ) * ζ ^ 21 + ((9953 / 790) : ℂ) * ζ ^ 22 - ((511 / 395) : ℂ) * ζ ^ 24 + ((2108 / 395) : ℂ) * ζ ^ 25 + ((872 / 79) : ℂ) * ζ ^ 27 + ((2191 / 395) : ℂ) * ζ ^ 28 - ((914 / 395) : ℂ) * ζ ^ 29 - ((7571 / 790) : ℂ) * ζ ^ 30 + ((327 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep04CoefficientIdentity00 :
    row18_reducedY76_combinationStep04Coefficient00 =
      row18_reducedY76_combinationStep03Coefficient00 +
        row18_reducedY76_combinationStep04Multiplier *
          (((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((73 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((105 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((73 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep04Coefficient00 row18_reducedY76_combinationStep03Coefficient00 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 (-((3276 / 6241) : ℂ) - ((625 / 12482) : ℂ) * ζ ^ 1 + ((689 / 6241) : ℂ) * ζ ^ 2 - ((3167 / 12482) : ℂ) * ζ ^ 3 - ((1285 / 12482) : ℂ) * ζ ^ 4 - ((117 / 6241) : ℂ) * ζ ^ 5 + ((5201 / 12482) : ℂ) * ζ ^ 6 + ((3018 / 6241) : ℂ) * ζ ^ 7 + ((4811 / 12482) : ℂ) * ζ ^ 8 - ((784 / 6241) : ℂ) * ζ ^ 9 - ((8487 / 6241) : ℂ) * ζ ^ 10 - ((4803 / 12482) : ℂ) * ζ ^ 11 + ((6691 / 12482) : ℂ) * ζ ^ 12 + ((178 / 6241) : ℂ) * ζ ^ 13 + ((6775 / 6241) : ℂ) * ζ ^ 14 - ((4021 / 12482) : ℂ) * ζ ^ 15 - ((19101 / 12482) : ℂ) * ζ ^ 16 - ((4973 / 12482) : ℂ) * ζ ^ 17 - ((4376 / 6241) : ℂ) * ζ ^ 18 + ((66 / 6241) : ℂ) * ζ ^ 19 + ((8447 / 12482) : ℂ) * ζ ^ 20 + ((551 / 6241) : ℂ) * ζ ^ 21 - ((119 / 6241) : ℂ) * ζ ^ 22 + ((550 / 6241) : ℂ) * ζ ^ 23 - ((2929 / 12482) : ℂ) * ζ ^ 24 + ((445 / 12482) : ℂ) * ζ ^ 25 + ((1398 / 6241) : ℂ) * ζ ^ 26 + ((1144 / 6241) : ℂ) * ζ ^ 27 + ((2973 / 12482) : ℂ) * ζ ^ 28 + ((1083 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep04Coefficient01 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep04CoefficientIdentity01 :
    row18_reducedY76_combinationStep04Coefficient01 =
      row18_reducedY76_combinationStep03Coefficient01 +
        row18_reducedY76_combinationStep04Multiplier *
          (-((5 / 316) : ℂ) + ((3 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((33 / 158) : ℂ) * ζ ^ 3 + ((3 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 + ((10 / 79) : ℂ) * ζ ^ 8 - ((3 / 316) : ℂ) * ζ ^ 9 - ((33 / 316) : ℂ) * ζ ^ 11 - ((3 / 79) : ℂ) * ζ ^ 12 - ((3 / 316) : ℂ) * ζ ^ 13 - ((35 / 158) : ℂ) * ζ ^ 15 - ((3 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 - ((45 / 158) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((59 / 316) : ℂ) * ζ ^ 24 - ((1 / 79) : ℂ) * ζ ^ 27 - ((10 / 79) : ℂ) * ζ ^ 28 + ((3 / 316) : ℂ) * ζ ^ 29 - ((13 / 79) : ℂ) * ζ ^ 30 + ((33 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep04Coefficient01 row18_reducedY76_combinationStep03Coefficient01 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 (((8339 / 12482) : ℂ) + ((6515 / 12482) : ℂ) * ζ ^ 1 + ((2155 / 12482) : ℂ) * ζ ^ 2 + ((901 / 12482) : ℂ) * ζ ^ 3 - ((4097 / 6241) : ℂ) * ζ ^ 4 + ((2706 / 6241) : ℂ) * ζ ^ 5 + ((1739 / 12482) : ℂ) * ζ ^ 6 - ((879 / 6241) : ℂ) * ζ ^ 7 - ((841 / 6241) : ℂ) * ζ ^ 8 + ((8085 / 12482) : ℂ) * ζ ^ 9 - ((1285 / 12482) : ℂ) * ζ ^ 10 + ((5841 / 12482) : ℂ) * ζ ^ 11 + ((731 / 6241) : ℂ) * ζ ^ 12 - ((5744 / 6241) : ℂ) * ζ ^ 13 - ((1365 / 12482) : ℂ) * ζ ^ 14 + ((3405 / 12482) : ℂ) * ζ ^ 15 - ((30 / 79) : ℂ) * ζ ^ 16 + ((7453 / 12482) : ℂ) * ζ ^ 17 + ((10 / 79) : ℂ) * ζ ^ 18 - ((7003 / 12482) : ℂ) * ζ ^ 19 + ((1337 / 12482) : ℂ) * ζ ^ 20 - ((3977 / 12482) : ℂ) * ζ ^ 21 - ((2345 / 6241) : ℂ) * ζ ^ 22 - ((249 / 6241) : ℂ) * ζ ^ 23 + ((9869 / 12482) : ℂ) * ζ ^ 24 - ((5039 / 12482) : ℂ) * ζ ^ 25 + ((365 / 12482) : ℂ) * ζ ^ 26 - ((8063 / 12482) : ℂ) * ζ ^ 27 - ((3131 / 12482) : ℂ) * ζ ^ 28 + ((889 / 12482) : ℂ) * ζ ^ 29 + ((1551 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep04Coefficient02 : ℂ :=
  (-((490 / 237) : ℂ) + ((523 / 79) : ℂ) * ζ ^ 1 + ((4048 / 237) : ℂ) * ζ ^ 2 - ((767 / 158) : ℂ) * ζ ^ 3 + ((21 / 158) : ℂ) * ζ ^ 5 + ((1505 / 158) : ℂ) * ζ ^ 8 + ((1520 / 237) : ℂ) * ζ ^ 9 - ((739 / 474) : ℂ) * ζ ^ 11 - ((2555 / 474) : ℂ) * ζ ^ 12 - ((523 / 79) : ℂ) * ζ ^ 13 + ((896 / 79) : ℂ) * ζ ^ 15 - ((523 / 79) : ℂ) * ζ ^ 17 - ((4048 / 237) : ℂ) * ζ ^ 18 - ((1813 / 158) : ℂ) * ζ ^ 21 - ((4048 / 237) : ℂ) * ζ ^ 22 - ((980 / 237) : ℂ) * ζ ^ 24 + ((1025 / 158) : ℂ) * ζ ^ 25 - ((1813 / 158) : ℂ) * ζ ^ 27 - ((1505 / 158) : ℂ) * ζ ^ 28 + ((523 / 79) : ℂ) * ζ ^ 29 + ((2345 / 158) : ℂ) * ζ ^ 30 + ((739 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep04CoefficientIdentity02 :
    row18_reducedY76_combinationStep04Coefficient02 =
      row18_reducedY76_combinationStep03Coefficient02 +
        row18_reducedY76_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep04Coefficient02 row18_reducedY76_combinationStep03Coefficient02 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep04Coefficient03 : ℂ :=
  (-((687 / 79) : ℂ) - ((1771 / 237) : ℂ) * ζ ^ 1 - ((1739 / 237) : ℂ) * ζ ^ 2 - ((119 / 79) : ℂ) * ζ ^ 5 + ((322 / 237) : ℂ) * ζ ^ 6 + ((322 / 237) : ℂ) * ζ ^ 8 - ((119 / 79) : ℂ) * ζ ^ 9 + ((2947 / 474) : ℂ) * ζ ^ 11 + ((6025 / 474) : ℂ) * ζ ^ 12 + ((1771 / 237) : ℂ) * ζ ^ 13 - ((2180 / 237) : ℂ) * ζ ^ 15 + ((1771 / 237) : ℂ) * ζ ^ 17 + ((933 / 158) : ℂ) * ζ ^ 18 + ((1064 / 237) : ℂ) * ζ ^ 21 + ((1739 / 237) : ℂ) * ζ ^ 22 - ((3443 / 474) : ℂ) * ζ ^ 24 - ((1414 / 237) : ℂ) * ζ ^ 25 + ((2180 / 237) : ℂ) * ζ ^ 27 - ((322 / 237) : ℂ) * ζ ^ 28 - ((1771 / 237) : ℂ) * ζ ^ 29 - ((5381 / 474) : ℂ) * ζ ^ 30 - ((2947 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep04CoefficientIdentity03 :
    row18_reducedY76_combinationStep04Coefficient03 =
      row18_reducedY76_combinationStep03Coefficient03 +
        row18_reducedY76_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep04Coefficient03 row18_reducedY76_combinationStep03Coefficient03 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep04Coefficient04 : ℂ :=
  (((22313 / 2370) : ℂ) - ((947 / 790) : ℂ) * ζ ^ 1 + ((27269 / 2370) : ℂ) * ζ ^ 2 + ((3889 / 790) : ℂ) * ζ ^ 5 + ((826 / 395) : ℂ) * ζ ^ 6 + ((826 / 395) : ℂ) * ζ ^ 8 + ((3889 / 790) : ℂ) * ζ ^ 9 + ((287 / 237) : ℂ) * ζ ^ 11 - ((6196 / 1185) : ℂ) * ζ ^ 12 + ((947 / 790) : ℂ) * ζ ^ 13 + ((5191 / 474) : ℂ) * ζ ^ 15 + ((947 / 790) : ℂ) * ζ ^ 17 - ((2209 / 790) : ℂ) * ζ ^ 18 - ((1471 / 790) : ℂ) * ζ ^ 21 - ((27269 / 2370) : ℂ) * ζ ^ 22 + ((557 / 790) : ℂ) * ζ ^ 24 - ((2418 / 395) : ℂ) * ζ ^ 25 - ((5191 / 474) : ℂ) * ζ ^ 27 - ((826 / 395) : ℂ) * ζ ^ 28 - ((947 / 790) : ℂ) * ζ ^ 29 + ((8674 / 1185) : ℂ) * ζ ^ 30 - ((287 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep04CoefficientIdentity04 :
    row18_reducedY76_combinationStep04Coefficient04 =
      row18_reducedY76_combinationStep03Coefficient04 +
        row18_reducedY76_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep04Coefficient04 row18_reducedY76_combinationStep03Coefficient04 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep04Coefficient05 : ℂ :=
  (-((707 / 237) : ℂ) + ((1294 / 237) : ℂ) * ζ ^ 2 + ((217 / 237) : ℂ) * ζ ^ 3 + ((312 / 79) : ℂ) * ζ ^ 5 + ((343 / 158) : ℂ) * ζ ^ 6 + ((523 / 79) : ℂ) * ζ ^ 8 + ((1753 / 474) : ℂ) * ζ ^ 9 + ((312 / 79) : ℂ) * ζ ^ 11 + ((523 / 158) : ℂ) * ζ ^ 12 + ((119 / 474) : ℂ) * ζ ^ 15 - ((343 / 158) : ℂ) * ζ ^ 18 - ((1153 / 237) : ℂ) * ζ ^ 21 - ((1294 / 237) : ℂ) * ζ ^ 22 - ((862 / 237) : ℂ) * ζ ^ 24 - ((312 / 79) : ℂ) * ζ ^ 25 - ((312 / 79) : ℂ) * ζ ^ 27 - ((523 / 79) : ℂ) * ζ ^ 28 - ((312 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep04CoefficientIdentity05 :
    row18_reducedY76_combinationStep04Coefficient05 =
      row18_reducedY76_combinationStep03Coefficient05 +
        row18_reducedY76_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep04Coefficient05 row18_reducedY76_combinationStep03Coefficient05 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep04Coefficient06 : ℂ :=
  (((3105 / 79) : ℂ) + ((39689 / 1185) : ℂ) * ζ ^ 1 - ((9218 / 1185) : ℂ) * ζ ^ 2 - ((441 / 10) : ℂ) * ζ ^ 3 + ((418 / 15) : ℂ) * ζ ^ 5 + ((12386 / 395) : ℂ) * ζ ^ 6 - ((1808 / 79) : ℂ) * ζ ^ 8 - ((53131 / 2370) : ℂ) * ζ ^ 9 + ((25693 / 1185) : ℂ) * ζ ^ 11 - ((1808 / 79) : ℂ) * ζ ^ 12 - ((39689 / 1185) : ℂ) * ζ ^ 13 + ((91183 / 2370) : ℂ) * ζ ^ 15 - ((39689 / 1185) : ℂ) * ζ ^ 17 - ((46376 / 1185) : ℂ) * ζ ^ 18 + ((25139 / 2370) : ℂ) * ζ ^ 21 + ((9218 / 1185) : ℂ) * ζ ^ 22 + ((6667 / 1185) : ℂ) * ζ ^ 25 - ((25139 / 2370) : ℂ) * ζ ^ 27 + ((1808 / 79) : ℂ) * ζ ^ 28 + ((39689 / 1185) : ℂ) * ζ ^ 29 + ((6193 / 395) : ℂ) * ζ ^ 30 - ((25693 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep04CoefficientIdentity06 :
    row18_reducedY76_combinationStep04Coefficient06 =
      row18_reducedY76_combinationStep03Coefficient06 +
        row18_reducedY76_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep04Coefficient06 row18_reducedY76_combinationStep03Coefficient06 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep04Coefficient07 : ℂ :=
  (((1627 / 237) : ℂ) + ((5261 / 474) : ℂ) * ζ ^ 1 + ((1333 / 158) : ℂ) * ζ ^ 2 + ((677 / 158) : ℂ) * ζ ^ 5 + ((745 / 474) : ℂ) * ζ ^ 6 + ((745 / 474) : ℂ) * ζ ^ 8 + ((677 / 158) : ℂ) * ζ ^ 9 - ((853 / 237) : ℂ) * ζ ^ 11 - ((1014 / 79) : ℂ) * ζ ^ 12 - ((5261 / 474) : ℂ) * ζ ^ 13 + ((1547 / 158) : ℂ) * ζ ^ 15 - ((5261 / 474) : ℂ) * ζ ^ 17 - ((805 / 79) : ℂ) * ζ ^ 18 - ((1823 / 237) : ℂ) * ζ ^ 21 - ((1333 / 158) : ℂ) * ζ ^ 22 + ((4085 / 474) : ℂ) * ζ ^ 24 + ((1615 / 237) : ℂ) * ζ ^ 25 - ((1547 / 158) : ℂ) * ζ ^ 27 - ((745 / 474) : ℂ) * ζ ^ 28 + ((5261 / 474) : ℂ) * ζ ^ 29 + ((6829 / 474) : ℂ) * ζ ^ 30 + ((853 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep04CoefficientIdentity07 :
    row18_reducedY76_combinationStep04Coefficient07 =
      row18_reducedY76_combinationStep03Coefficient07 +
        row18_reducedY76_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep04Coefficient07 row18_reducedY76_combinationStep03Coefficient07 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep04Coefficient08 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep04CoefficientIdentity08 :
    row18_reducedY76_combinationStep04Coefficient08 =
      row18_reducedY76_combinationStep03Coefficient08 +
        row18_reducedY76_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep04Coefficient08 row18_reducedY76_combinationStep03Coefficient08 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep04Coefficient09 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep04CoefficientIdentity09 :
    row18_reducedY76_combinationStep04Coefficient09 =
      row18_reducedY76_combinationStep03Coefficient09 +
        row18_reducedY76_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep04Coefficient09 row18_reducedY76_combinationStep03Coefficient09 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep04Coefficient10 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep04CoefficientIdentity10 :
    row18_reducedY76_combinationStep04Coefficient10 =
      row18_reducedY76_combinationStep03Coefficient10 +
        row18_reducedY76_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep04Coefficient10 row18_reducedY76_combinationStep03Coefficient10 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep04Coefficient11 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep04CoefficientIdentity11 :
    row18_reducedY76_combinationStep04Coefficient11 =
      row18_reducedY76_combinationStep03Coefficient11 +
        row18_reducedY76_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep04Coefficient11 row18_reducedY76_combinationStep03Coefficient11 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep04Coefficient12 : ℂ :=
  (-((42 / 79) : ℂ) - ((9 / 79) : ℂ) * ζ ^ 1 - ((1 / 158) : ℂ) * ζ ^ 2 - ((4 / 79) : ℂ) * ζ ^ 5 + ((83 / 158) : ℂ) * ζ ^ 6 + ((83 / 158) : ℂ) * ζ ^ 8 - ((4 / 79) : ℂ) * ζ ^ 9 + ((49 / 158) : ℂ) * ζ ^ 11 + ((104 / 79) : ℂ) * ζ ^ 12 + ((9 / 79) : ℂ) * ζ ^ 13 - ((40 / 79) : ℂ) * ζ ^ 15 + ((9 / 79) : ℂ) * ζ ^ 17 + ((19 / 79) : ℂ) * ζ ^ 18 + ((13 / 158) : ℂ) * ζ ^ 21 + ((1 / 158) : ℂ) * ζ ^ 22 - ((121 / 158) : ℂ) * ζ ^ 24 - ((5 / 79) : ℂ) * ζ ^ 25 + ((40 / 79) : ℂ) * ζ ^ 27 - ((83 / 158) : ℂ) * ζ ^ 28 - ((9 / 79) : ℂ) * ζ ^ 29 - ((125 / 158) : ℂ) * ζ ^ 30 - ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep04CoefficientIdentity12 :
    row18_reducedY76_combinationStep04Coefficient12 =
      row18_reducedY76_combinationStep03Coefficient12 +
        row18_reducedY76_combinationStep04Multiplier *
          (-((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((73 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((105 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((73 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep04Coefficient12 row18_reducedY76_combinationStep03Coefficient12 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 (((3276 / 6241) : ℂ) + ((625 / 12482) : ℂ) * ζ ^ 1 - ((689 / 6241) : ℂ) * ζ ^ 2 + ((3167 / 12482) : ℂ) * ζ ^ 3 + ((1285 / 12482) : ℂ) * ζ ^ 4 + ((117 / 6241) : ℂ) * ζ ^ 5 - ((5201 / 12482) : ℂ) * ζ ^ 6 - ((3018 / 6241) : ℂ) * ζ ^ 7 - ((4811 / 12482) : ℂ) * ζ ^ 8 + ((784 / 6241) : ℂ) * ζ ^ 9 + ((8487 / 6241) : ℂ) * ζ ^ 10 + ((4803 / 12482) : ℂ) * ζ ^ 11 - ((6691 / 12482) : ℂ) * ζ ^ 12 - ((178 / 6241) : ℂ) * ζ ^ 13 - ((6775 / 6241) : ℂ) * ζ ^ 14 + ((4021 / 12482) : ℂ) * ζ ^ 15 + ((19101 / 12482) : ℂ) * ζ ^ 16 + ((4973 / 12482) : ℂ) * ζ ^ 17 + ((4376 / 6241) : ℂ) * ζ ^ 18 - ((66 / 6241) : ℂ) * ζ ^ 19 - ((8447 / 12482) : ℂ) * ζ ^ 20 - ((551 / 6241) : ℂ) * ζ ^ 21 + ((119 / 6241) : ℂ) * ζ ^ 22 - ((550 / 6241) : ℂ) * ζ ^ 23 + ((2929 / 12482) : ℂ) * ζ ^ 24 - ((445 / 12482) : ℂ) * ζ ^ 25 - ((1398 / 6241) : ℂ) * ζ ^ 26 - ((1144 / 6241) : ℂ) * ζ ^ 27 - ((2973 / 12482) : ℂ) * ζ ^ 28 - ((1083 / 6241) : ℂ) * ζ ^ 29 - ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep04Coefficient13 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep04CoefficientIdentity13 :
    row18_reducedY76_combinationStep04Coefficient13 =
      row18_reducedY76_combinationStep03Coefficient13 +
        row18_reducedY76_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep04Coefficient13 row18_reducedY76_combinationStep03Coefficient13 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep04Coefficient14 : ℂ :=
  (((33 / 79) : ℂ) - ((24 / 79) : ℂ) * ζ ^ 1 - ((19 / 158) : ℂ) * ζ ^ 2 + ((77 / 158) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((2 / 79) : ℂ) * ζ ^ 6 + ((5 / 158) : ℂ) * ζ ^ 8 + ((95 / 158) : ℂ) * ζ ^ 9 + ((9 / 79) : ℂ) * ζ ^ 11 + ((5 / 158) : ℂ) * ζ ^ 12 + ((24 / 79) : ℂ) * ζ ^ 13 - ((5 / 79) : ℂ) * ζ ^ 15 + ((24 / 79) : ℂ) * ζ ^ 17 - ((23 / 158) : ℂ) * ζ ^ 18 - ((29 / 158) : ℂ) * ζ ^ 21 + ((19 / 158) : ℂ) * ζ ^ 22 - ((67 / 158) : ℂ) * ζ ^ 25 + ((29 / 158) : ℂ) * ζ ^ 27 - ((5 / 158) : ℂ) * ζ ^ 28 - ((24 / 79) : ℂ) * ζ ^ 29 + ((1 / 79) : ℂ) * ζ ^ 30 - ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep04CoefficientIdentity14 :
    row18_reducedY76_combinationStep04Coefficient14 =
      row18_reducedY76_combinationStep03Coefficient14 +
        row18_reducedY76_combinationStep04Multiplier *
          (((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep04Coefficient14 row18_reducedY76_combinationStep03Coefficient14 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 (-((2474 / 6241) : ℂ) + ((6163 / 12482) : ℂ) * ζ ^ 1 + ((3250 / 6241) : ℂ) * ζ ^ 2 - ((1919 / 6241) : ℂ) * ζ ^ 3 + ((7587 / 12482) : ℂ) * ζ ^ 4 - ((3018 / 6241) : ℂ) * ζ ^ 5 - ((1520 / 6241) : ℂ) * ζ ^ 6 + ((3459 / 6241) : ℂ) * ζ ^ 7 - ((315 / 12482) : ℂ) * ζ ^ 8 - ((1635 / 12482) : ℂ) * ζ ^ 9 + ((2433 / 12482) : ℂ) * ζ ^ 10 + ((203 / 12482) : ℂ) * ζ ^ 11 - ((1748 / 6241) : ℂ) * ζ ^ 12 + ((1205 / 6241) : ℂ) * ζ ^ 13 - ((837 / 12482) : ℂ) * ζ ^ 14 + ((894 / 6241) : ℂ) * ζ ^ 15 + ((247 / 12482) : ℂ) * ζ ^ 16 + ((163 / 6241) : ℂ) * ζ ^ 17 + ((1985 / 12482) : ℂ) * ζ ^ 18 - ((1125 / 6241) : ℂ) * ζ ^ 19 + ((871 / 12482) : ℂ) * ζ ^ 20 + ((706 / 6241) : ℂ) * ζ ^ 21 - ((3236 / 6241) : ℂ) * ζ ^ 22 + ((2 / 79) : ℂ) * ζ ^ 23 - ((710 / 6241) : ℂ) * ζ ^ 24 + ((240 / 6241) : ℂ) * ζ ^ 25 + ((10525 / 12482) : ℂ) * ζ ^ 26 - ((162 / 6241) : ℂ) * ζ ^ 27 - ((3337 / 12482) : ℂ) * ζ ^ 28 - ((741 / 12482) : ℂ) * ζ ^ 29 + ((705 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep04Coefficient15 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep04CoefficientIdentity15 :
    row18_reducedY76_combinationStep04Coefficient15 =
      row18_reducedY76_combinationStep03Coefficient15 +
        row18_reducedY76_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep04Coefficient15 row18_reducedY76_combinationStep03Coefficient15 row18_reducedY76_combinationStep04Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY76_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY76_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY76_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY76_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY76_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY76_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY76_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY76_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY76_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY76_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY76_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY76_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY76_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY76_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY76_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY76_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY76_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY76_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation06
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY76_combinationStep04CoefficientIdentity00,
      row18_reducedY76_combinationStep04CoefficientIdentity01,
      row18_reducedY76_combinationStep04CoefficientIdentity02,
      row18_reducedY76_combinationStep04CoefficientIdentity03,
      row18_reducedY76_combinationStep04CoefficientIdentity04,
      row18_reducedY76_combinationStep04CoefficientIdentity05,
      row18_reducedY76_combinationStep04CoefficientIdentity06,
      row18_reducedY76_combinationStep04CoefficientIdentity07,
      row18_reducedY76_combinationStep04CoefficientIdentity08,
      row18_reducedY76_combinationStep04CoefficientIdentity09,
      row18_reducedY76_combinationStep04CoefficientIdentity10,
      row18_reducedY76_combinationStep04CoefficientIdentity11,
      row18_reducedY76_combinationStep04CoefficientIdentity12,
      row18_reducedY76_combinationStep04CoefficientIdentity13,
      row18_reducedY76_combinationStep04CoefficientIdentity14,
      row18_reducedY76_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY76_combinationStep04Multiplier * equation

private def row18_reducedY76_combinationStep05Multiplier : ℂ :=
  (-((16088 / 1185) : ℂ) - ((35906 / 1185) : ℂ) * ζ ^ 1 - ((828 / 79) : ℂ) * ζ ^ 2 - ((14314 / 1185) : ℂ) * ζ ^ 3 - ((15508 / 1185) : ℂ) * ζ ^ 5 - ((6686 / 1185) : ℂ) * ζ ^ 8 - ((2498 / 1185) : ℂ) * ζ ^ 9 + ((5604 / 395) : ℂ) * ζ ^ 11 + ((12954 / 395) : ℂ) * ζ ^ 12 + ((35906 / 1185) : ℂ) * ζ ^ 13 - ((2028 / 395) : ℂ) * ζ ^ 15 + ((35906 / 1185) : ℂ) * ζ ^ 17 + ((828 / 79) : ℂ) * ζ ^ 18 + ((21592 / 1185) : ℂ) * ζ ^ 21 + ((828 / 79) : ℂ) * ζ ^ 22 - ((32176 / 1185) : ℂ) * ζ ^ 24 - ((20398 / 1185) : ℂ) * ζ ^ 25 + ((21592 / 1185) : ℂ) * ζ ^ 27 + ((6686 / 1185) : ℂ) * ζ ^ 28 - ((35906 / 1185) : ℂ) * ζ ^ 29 - ((1584 / 79) : ℂ) * ζ ^ 30 - ((5604 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY76_combinationStep05Coefficient00 : ℂ :=
  (-((5571 / 790) : ℂ) - ((914 / 395) : ℂ) * ζ ^ 1 - ((9953 / 790) : ℂ) * ζ ^ 2 - ((3022 / 395) : ℂ) * ζ ^ 5 - ((2191 / 395) : ℂ) * ζ ^ 6 - ((2191 / 395) : ℂ) * ζ ^ 8 - ((3022 / 395) : ℂ) * ζ ^ 9 - ((327 / 79) : ℂ) * ζ ^ 11 + ((3189 / 790) : ℂ) * ζ ^ 12 + ((914 / 395) : ℂ) * ζ ^ 13 - ((872 / 79) : ℂ) * ζ ^ 15 + ((914 / 395) : ℂ) * ζ ^ 17 + ((2702 / 395) : ℂ) * ζ ^ 18 + ((1968 / 395) : ℂ) * ζ ^ 21 + ((9953 / 790) : ℂ) * ζ ^ 22 - ((511 / 395) : ℂ) * ζ ^ 24 + ((2108 / 395) : ℂ) * ζ ^ 25 + ((872 / 79) : ℂ) * ζ ^ 27 + ((2191 / 395) : ℂ) * ζ ^ 28 - ((914 / 395) : ℂ) * ζ ^ 29 - ((7571 / 790) : ℂ) * ζ ^ 30 + ((327 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep05CoefficientIdentity00 :
    row18_reducedY76_combinationStep05Coefficient00 =
      row18_reducedY76_combinationStep04Coefficient00 +
        row18_reducedY76_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep05Coefficient00 row18_reducedY76_combinationStep04Coefficient00 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep05Coefficient01 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep05CoefficientIdentity01 :
    row18_reducedY76_combinationStep05Coefficient01 =
      row18_reducedY76_combinationStep04Coefficient01 +
        row18_reducedY76_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep05Coefficient01 row18_reducedY76_combinationStep04Coefficient01 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep05Coefficient02 : ℂ :=
  (-((729 / 395) : ℂ) + ((1868 / 237) : ℂ) * ζ ^ 1 + ((5353 / 474) : ℂ) * ζ ^ 2 - ((17 / 474) : ℂ) * ζ ^ 3 + ((887 / 237) : ℂ) * ζ ^ 5 + ((24017 / 2370) : ℂ) * ζ ^ 8 + ((907 / 474) : ℂ) * ζ ^ 9 - ((445 / 237) : ℂ) * ζ ^ 11 - ((15269 / 2370) : ℂ) * ζ ^ 12 - ((1868 / 237) : ℂ) * ζ ^ 13 + ((1979 / 474) : ℂ) * ζ ^ 15 - ((1868 / 237) : ℂ) * ζ ^ 17 - ((5353 / 474) : ℂ) * ζ ^ 18 - ((1251 / 158) : ℂ) * ζ ^ 21 - ((5353 / 474) : ℂ) * ζ ^ 22 - ((1458 / 395) : ℂ) * ζ ^ 24 + ((327 / 79) : ℂ) * ζ ^ 25 - ((1251 / 158) : ℂ) * ζ ^ 27 - ((24017 / 2370) : ℂ) * ζ ^ 28 + ((1868 / 237) : ℂ) * ζ ^ 29 + ((1184 / 237) : ℂ) * ζ ^ 30 + ((445 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep05CoefficientIdentity02 :
    row18_reducedY76_combinationStep05Coefficient02 =
      row18_reducedY76_combinationStep04Coefficient02 +
        row18_reducedY76_combinationStep05Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep05Coefficient02 row18_reducedY76_combinationStep04Coefficient02 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 (((27487 / 93615) : ℂ) - ((54629 / 93615) : ℂ) * ζ ^ 1 + ((822131 / 93615) : ℂ) * ζ ^ 2 + ((208437 / 62410) : ℂ) * ζ ^ 3 + ((358243 / 187230) : ℂ) * ζ ^ 4 + ((137611 / 93615) : ℂ) * ζ ^ 5 - ((76357 / 12482) : ℂ) * ζ ^ 6 + ((145253 / 37446) : ℂ) * ζ ^ 7 - ((39439 / 18723) : ℂ) * ζ ^ 8 + ((48545 / 37446) : ℂ) * ζ ^ 9 + ((1561183 / 187230) : ℂ) * ζ ^ 10 - ((241622 / 93615) : ℂ) * ζ ^ 11 + ((279436 / 93615) : ℂ) * ζ ^ 12 - ((248797 / 31205) : ℂ) * ζ ^ 13 - ((210035 / 37446) : ℂ) * ζ ^ 14 + ((557461 / 93615) : ℂ) * ζ ^ 15 + ((341849 / 187230) : ℂ) * ζ ^ 16 + ((656062 / 93615) : ℂ) * ζ ^ 17 + ((286349 / 93615) : ℂ) * ζ ^ 18 - ((72451 / 31205) : ℂ) * ζ ^ 19 + ((378511 / 187230) : ℂ) * ζ ^ 20 - ((717059 / 187230) : ℂ) * ζ ^ 21 - ((288701 / 93615) : ℂ) * ζ ^ 22 - ((1250429 / 187230) : ℂ) * ζ ^ 23 - ((236438 / 93615) : ℂ) * ζ ^ 24 + ((184888 / 93615) : ℂ) * ζ ^ 25 + ((324379 / 187230) : ℂ) * ζ ^ 26 + ((16586 / 6241) : ℂ) * ζ ^ 27 - ((76864 / 93615) : ℂ) * ζ ^ 28 - ((5304 / 31205) : ℂ) * ζ ^ 29 - ((19614 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep05Coefficient03 : ℂ :=
  (-((19 / 3) : ℂ) - ((5207 / 474) : ℂ) * ζ ^ 1 - ((666 / 79) : ℂ) * ζ ^ 2 - ((669 / 158) : ℂ) * ζ ^ 5 - ((497 / 237) : ℂ) * ζ ^ 6 - ((497 / 237) : ℂ) * ζ ^ 8 - ((669 / 158) : ℂ) * ζ ^ 9 + ((1559 / 474) : ℂ) * ζ ^ 11 + ((910 / 79) : ℂ) * ζ ^ 12 + ((5207 / 474) : ℂ) * ζ ^ 13 - ((1467 / 158) : ℂ) * ζ ^ 15 + ((5207 / 474) : ℂ) * ζ ^ 17 + ((786 / 79) : ℂ) * ζ ^ 18 + ((3607 / 474) : ℂ) * ζ ^ 21 + ((666 / 79) : ℂ) * ζ ^ 22 - ((1861 / 237) : ℂ) * ζ ^ 24 - ((1600 / 237) : ℂ) * ζ ^ 25 + ((1467 / 158) : ℂ) * ζ ^ 27 + ((497 / 237) : ℂ) * ζ ^ 28 - ((5207 / 474) : ℂ) * ζ ^ 29 - ((3227 / 237) : ℂ) * ζ ^ 30 - ((1559 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep05CoefficientIdentity03 :
    row18_reducedY76_combinationStep05Coefficient03 =
      row18_reducedY76_combinationStep04Coefficient03 +
        row18_reducedY76_combinationStep05Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep05Coefficient03 row18_reducedY76_combinationStep04Coefficient03 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 (-((498718 / 93615) : ℂ) + ((51329 / 93615) : ℂ) * ζ ^ 1 + ((1229729 / 187230) : ℂ) * ζ ^ 2 - ((168352 / 93615) : ℂ) * ζ ^ 3 + ((1083113 / 187230) : ℂ) * ζ ^ 4 + ((55153 / 31205) : ℂ) * ζ ^ 5 + ((131477 / 31205) : ℂ) * ζ ^ 6 - ((302783 / 93615) : ℂ) * ζ ^ 7 - ((116977 / 187230) : ℂ) * ζ ^ 8 + ((178713 / 62410) : ℂ) * ζ ^ 9 - ((1095319 / 187230) : ℂ) * ζ ^ 10 + ((1165837 / 187230) : ℂ) * ζ ^ 11 - ((245429 / 187230) : ℂ) * ζ ^ 12 - ((711551 / 187230) : ℂ) * ζ ^ 13 - ((181025 / 37446) : ℂ) * ζ ^ 14 - ((1338173 / 187230) : ℂ) * ζ ^ 15 + ((418309 / 187230) : ℂ) * ζ ^ 16 + ((130267 / 187230) : ℂ) * ζ ^ 17 - ((1512731 / 187230) : ℂ) * ζ ^ 18 - ((223084 / 93615) : ℂ) * ζ ^ 19 - ((1096393 / 187230) : ℂ) * ζ ^ 20 - ((409942 / 93615) : ℂ) * ζ ^ 21 - ((381909 / 31205) : ℂ) * ζ ^ 22 - ((319501 / 187230) : ℂ) * ζ ^ 23 - ((386359 / 93615) : ℂ) * ζ ^ 24 - ((588181 / 187230) : ℂ) * ζ ^ 25 + ((64151 / 12482) : ℂ) * ζ ^ 26 - ((571871 / 187230) : ℂ) * ζ ^ 27 - ((160399 / 187230) : ℂ) * ζ ^ 28 - ((101394 / 31205) : ℂ) * ζ ^ 29 - ((18213 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep05Coefficient04 : ℂ :=
  (((5571 / 790) : ℂ) + ((914 / 395) : ℂ) * ζ ^ 1 + ((9953 / 790) : ℂ) * ζ ^ 2 + ((3022 / 395) : ℂ) * ζ ^ 5 + ((2191 / 395) : ℂ) * ζ ^ 6 + ((2191 / 395) : ℂ) * ζ ^ 8 + ((3022 / 395) : ℂ) * ζ ^ 9 + ((327 / 79) : ℂ) * ζ ^ 11 - ((3189 / 790) : ℂ) * ζ ^ 12 - ((914 / 395) : ℂ) * ζ ^ 13 + ((872 / 79) : ℂ) * ζ ^ 15 - ((914 / 395) : ℂ) * ζ ^ 17 - ((2702 / 395) : ℂ) * ζ ^ 18 - ((1968 / 395) : ℂ) * ζ ^ 21 - ((9953 / 790) : ℂ) * ζ ^ 22 + ((511 / 395) : ℂ) * ζ ^ 24 - ((2108 / 395) : ℂ) * ζ ^ 25 - ((872 / 79) : ℂ) * ζ ^ 27 - ((2191 / 395) : ℂ) * ζ ^ 28 + ((914 / 395) : ℂ) * ζ ^ 29 + ((7571 / 790) : ℂ) * ζ ^ 30 - ((327 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep05CoefficientIdentity04 :
    row18_reducedY76_combinationStep05Coefficient04 =
      row18_reducedY76_combinationStep04Coefficient04 +
        row18_reducedY76_combinationStep05Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep05Coefficient04 row18_reducedY76_combinationStep04Coefficient04 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 (((498718 / 93615) : ℂ) - ((51329 / 93615) : ℂ) * ζ ^ 1 - ((1229729 / 187230) : ℂ) * ζ ^ 2 + ((168352 / 93615) : ℂ) * ζ ^ 3 - ((1083113 / 187230) : ℂ) * ζ ^ 4 - ((55153 / 31205) : ℂ) * ζ ^ 5 - ((131477 / 31205) : ℂ) * ζ ^ 6 + ((302783 / 93615) : ℂ) * ζ ^ 7 + ((116977 / 187230) : ℂ) * ζ ^ 8 - ((178713 / 62410) : ℂ) * ζ ^ 9 + ((1095319 / 187230) : ℂ) * ζ ^ 10 - ((1165837 / 187230) : ℂ) * ζ ^ 11 + ((245429 / 187230) : ℂ) * ζ ^ 12 + ((711551 / 187230) : ℂ) * ζ ^ 13 + ((181025 / 37446) : ℂ) * ζ ^ 14 + ((1338173 / 187230) : ℂ) * ζ ^ 15 - ((418309 / 187230) : ℂ) * ζ ^ 16 - ((130267 / 187230) : ℂ) * ζ ^ 17 + ((1512731 / 187230) : ℂ) * ζ ^ 18 + ((223084 / 93615) : ℂ) * ζ ^ 19 + ((1096393 / 187230) : ℂ) * ζ ^ 20 + ((409942 / 93615) : ℂ) * ζ ^ 21 + ((381909 / 31205) : ℂ) * ζ ^ 22 + ((319501 / 187230) : ℂ) * ζ ^ 23 + ((386359 / 93615) : ℂ) * ζ ^ 24 + ((588181 / 187230) : ℂ) * ζ ^ 25 - ((64151 / 12482) : ℂ) * ζ ^ 26 + ((571871 / 187230) : ℂ) * ζ ^ 27 + ((160399 / 187230) : ℂ) * ζ ^ 28 + ((101394 / 31205) : ℂ) * ζ ^ 29 + ((18213 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep05Coefficient05 : ℂ :=
  (-((707 / 237) : ℂ) + ((1294 / 237) : ℂ) * ζ ^ 2 + ((217 / 237) : ℂ) * ζ ^ 3 + ((312 / 79) : ℂ) * ζ ^ 5 + ((343 / 158) : ℂ) * ζ ^ 6 + ((523 / 79) : ℂ) * ζ ^ 8 + ((1753 / 474) : ℂ) * ζ ^ 9 + ((312 / 79) : ℂ) * ζ ^ 11 + ((523 / 158) : ℂ) * ζ ^ 12 + ((119 / 474) : ℂ) * ζ ^ 15 - ((343 / 158) : ℂ) * ζ ^ 18 - ((1153 / 237) : ℂ) * ζ ^ 21 - ((1294 / 237) : ℂ) * ζ ^ 22 - ((862 / 237) : ℂ) * ζ ^ 24 - ((312 / 79) : ℂ) * ζ ^ 25 - ((312 / 79) : ℂ) * ζ ^ 27 - ((523 / 79) : ℂ) * ζ ^ 28 - ((312 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep05CoefficientIdentity05 :
    row18_reducedY76_combinationStep05Coefficient05 =
      row18_reducedY76_combinationStep04Coefficient05 +
        row18_reducedY76_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep05Coefficient05 row18_reducedY76_combinationStep04Coefficient05 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep05Coefficient06 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep05CoefficientIdentity06 :
    row18_reducedY76_combinationStep05Coefficient06 =
      row18_reducedY76_combinationStep04Coefficient06 +
        row18_reducedY76_combinationStep05Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep05Coefficient06 row18_reducedY76_combinationStep04Coefficient06 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 (((3808129 / 93615) : ℂ) + ((15409 / 395) : ℂ) * ζ ^ 1 + ((964153 / 187230) : ℂ) * ζ ^ 2 - ((561824 / 18723) : ℂ) * ζ ^ 3 - ((766540 / 18723) : ℂ) * ζ ^ 4 - ((153909 / 62410) : ℂ) * ζ ^ 5 + ((1092849 / 31205) : ℂ) * ζ ^ 6 + ((1230361 / 31205) : ℂ) * ζ ^ 7 + ((582536 / 31205) : ℂ) * ζ ^ 8 - ((2875919 / 187230) : ℂ) * ζ ^ 9 - ((1139119 / 62410) : ℂ) * ζ ^ 10 - ((332204 / 18723) : ℂ) * ζ ^ 11 - ((765256 / 93615) : ℂ) * ζ ^ 12 - ((59502 / 31205) : ℂ) * ζ ^ 13 + ((500167 / 187230) : ℂ) * ζ ^ 14 + ((1129747 / 62410) : ℂ) * ζ ^ 15 + ((365748 / 31205) : ℂ) * ζ ^ 16 - ((699658 / 93615) : ℂ) * ζ ^ 17 - ((1159411 / 37446) : ℂ) * ζ ^ 18 - ((7675981 / 187230) : ℂ) * ζ ^ 19 + ((47216 / 93615) : ℂ) * ζ ^ 20 + ((543268 / 31205) : ℂ) * ζ ^ 21 + ((3016777 / 187230) : ℂ) * ζ ^ 22 - ((25373 / 93615) : ℂ) * ζ ^ 23 - ((438721 / 18723) : ℂ) * ζ ^ 24 - ((786841 / 62410) : ℂ) * ζ ^ 25 - ((578411 / 187230) : ℂ) * ζ ^ 26 + ((111530 / 18723) : ℂ) * ζ ^ 27 + ((633473 / 93615) : ℂ) * ζ ^ 28 + ((89064 / 31205) : ℂ) * ζ ^ 29 + ((39228 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep05Coefficient07 : ℂ :=
  (((1627 / 237) : ℂ) + ((5261 / 474) : ℂ) * ζ ^ 1 + ((1333 / 158) : ℂ) * ζ ^ 2 + ((677 / 158) : ℂ) * ζ ^ 5 + ((745 / 474) : ℂ) * ζ ^ 6 + ((745 / 474) : ℂ) * ζ ^ 8 + ((677 / 158) : ℂ) * ζ ^ 9 - ((853 / 237) : ℂ) * ζ ^ 11 - ((1014 / 79) : ℂ) * ζ ^ 12 - ((5261 / 474) : ℂ) * ζ ^ 13 + ((1547 / 158) : ℂ) * ζ ^ 15 - ((5261 / 474) : ℂ) * ζ ^ 17 - ((805 / 79) : ℂ) * ζ ^ 18 - ((1823 / 237) : ℂ) * ζ ^ 21 - ((1333 / 158) : ℂ) * ζ ^ 22 + ((4085 / 474) : ℂ) * ζ ^ 24 + ((1615 / 237) : ℂ) * ζ ^ 25 - ((1547 / 158) : ℂ) * ζ ^ 27 - ((745 / 474) : ℂ) * ζ ^ 28 + ((5261 / 474) : ℂ) * ζ ^ 29 + ((6829 / 474) : ℂ) * ζ ^ 30 + ((853 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep05CoefficientIdentity07 :
    row18_reducedY76_combinationStep05Coefficient07 =
      row18_reducedY76_combinationStep04Coefficient07 +
        row18_reducedY76_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep05Coefficient07 row18_reducedY76_combinationStep04Coefficient07 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep05Coefficient08 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep05CoefficientIdentity08 :
    row18_reducedY76_combinationStep05Coefficient08 =
      row18_reducedY76_combinationStep04Coefficient08 +
        row18_reducedY76_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep05Coefficient08 row18_reducedY76_combinationStep04Coefficient08 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep05Coefficient09 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep05CoefficientIdentity09 :
    row18_reducedY76_combinationStep05Coefficient09 =
      row18_reducedY76_combinationStep04Coefficient09 +
        row18_reducedY76_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep05Coefficient09 row18_reducedY76_combinationStep04Coefficient09 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep05Coefficient10 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep05CoefficientIdentity10 :
    row18_reducedY76_combinationStep05Coefficient10 =
      row18_reducedY76_combinationStep04Coefficient10 +
        row18_reducedY76_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep05Coefficient10 row18_reducedY76_combinationStep04Coefficient10 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep05Coefficient11 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep05CoefficientIdentity11 :
    row18_reducedY76_combinationStep05Coefficient11 =
      row18_reducedY76_combinationStep04Coefficient11 +
        row18_reducedY76_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep05Coefficient11 row18_reducedY76_combinationStep04Coefficient11 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep05Coefficient12 : ℂ :=
  (-((42 / 79) : ℂ) - ((9 / 79) : ℂ) * ζ ^ 1 - ((1 / 158) : ℂ) * ζ ^ 2 - ((4 / 79) : ℂ) * ζ ^ 5 + ((83 / 158) : ℂ) * ζ ^ 6 + ((83 / 158) : ℂ) * ζ ^ 8 - ((4 / 79) : ℂ) * ζ ^ 9 + ((49 / 158) : ℂ) * ζ ^ 11 + ((104 / 79) : ℂ) * ζ ^ 12 + ((9 / 79) : ℂ) * ζ ^ 13 - ((40 / 79) : ℂ) * ζ ^ 15 + ((9 / 79) : ℂ) * ζ ^ 17 + ((19 / 79) : ℂ) * ζ ^ 18 + ((13 / 158) : ℂ) * ζ ^ 21 + ((1 / 158) : ℂ) * ζ ^ 22 - ((121 / 158) : ℂ) * ζ ^ 24 - ((5 / 79) : ℂ) * ζ ^ 25 + ((40 / 79) : ℂ) * ζ ^ 27 - ((83 / 158) : ℂ) * ζ ^ 28 - ((9 / 79) : ℂ) * ζ ^ 29 - ((125 / 158) : ℂ) * ζ ^ 30 - ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep05CoefficientIdentity12 :
    row18_reducedY76_combinationStep05Coefficient12 =
      row18_reducedY76_combinationStep04Coefficient12 +
        row18_reducedY76_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep05Coefficient12 row18_reducedY76_combinationStep04Coefficient12 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep05Coefficient13 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep05CoefficientIdentity13 :
    row18_reducedY76_combinationStep05Coefficient13 =
      row18_reducedY76_combinationStep04Coefficient13 +
        row18_reducedY76_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep05Coefficient13 row18_reducedY76_combinationStep04Coefficient13 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep05Coefficient14 : ℂ :=
  (((33 / 79) : ℂ) - ((24 / 79) : ℂ) * ζ ^ 1 - ((19 / 158) : ℂ) * ζ ^ 2 + ((77 / 158) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((2 / 79) : ℂ) * ζ ^ 6 + ((5 / 158) : ℂ) * ζ ^ 8 + ((95 / 158) : ℂ) * ζ ^ 9 + ((9 / 79) : ℂ) * ζ ^ 11 + ((5 / 158) : ℂ) * ζ ^ 12 + ((24 / 79) : ℂ) * ζ ^ 13 - ((5 / 79) : ℂ) * ζ ^ 15 + ((24 / 79) : ℂ) * ζ ^ 17 - ((23 / 158) : ℂ) * ζ ^ 18 - ((29 / 158) : ℂ) * ζ ^ 21 + ((19 / 158) : ℂ) * ζ ^ 22 - ((67 / 158) : ℂ) * ζ ^ 25 + ((29 / 158) : ℂ) * ζ ^ 27 - ((5 / 158) : ℂ) * ζ ^ 28 - ((24 / 79) : ℂ) * ζ ^ 29 + ((1 / 79) : ℂ) * ζ ^ 30 - ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep05CoefficientIdentity14 :
    row18_reducedY76_combinationStep05Coefficient14 =
      row18_reducedY76_combinationStep04Coefficient14 +
        row18_reducedY76_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep05Coefficient14 row18_reducedY76_combinationStep04Coefficient14 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep05Coefficient15 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep05CoefficientIdentity15 :
    row18_reducedY76_combinationStep05Coefficient15 =
      row18_reducedY76_combinationStep04Coefficient15 +
        row18_reducedY76_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep05Coefficient15 row18_reducedY76_combinationStep04Coefficient15 row18_reducedY76_combinationStep05Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY76_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY76_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY76_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY76_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY76_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY76_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY76_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY76_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY76_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY76_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY76_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY76_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY76_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY76_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY76_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY76_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY76_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY76_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY76_combinationStep05CoefficientIdentity00,
      row18_reducedY76_combinationStep05CoefficientIdentity01,
      row18_reducedY76_combinationStep05CoefficientIdentity02,
      row18_reducedY76_combinationStep05CoefficientIdentity03,
      row18_reducedY76_combinationStep05CoefficientIdentity04,
      row18_reducedY76_combinationStep05CoefficientIdentity05,
      row18_reducedY76_combinationStep05CoefficientIdentity06,
      row18_reducedY76_combinationStep05CoefficientIdentity07,
      row18_reducedY76_combinationStep05CoefficientIdentity08,
      row18_reducedY76_combinationStep05CoefficientIdentity09,
      row18_reducedY76_combinationStep05CoefficientIdentity10,
      row18_reducedY76_combinationStep05CoefficientIdentity11,
      row18_reducedY76_combinationStep05CoefficientIdentity12,
      row18_reducedY76_combinationStep05CoefficientIdentity13,
      row18_reducedY76_combinationStep05CoefficientIdentity14,
      row18_reducedY76_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY76_combinationStep05Multiplier * equation

private def row18_reducedY76_combinationStep06Multiplier : ℂ :=
  (((1118 / 79) : ℂ) + ((2416 / 237) : ℂ) * ζ ^ 1 - ((340 / 79) : ℂ) * ζ ^ 2 - ((1020 / 79) : ℂ) * ζ ^ 3 + ((2416 / 237) : ℂ) * ζ ^ 5 + ((778 / 79) : ℂ) * ζ ^ 6 - ((778 / 79) : ℂ) * ζ ^ 8 - ((2416 / 237) : ℂ) * ζ ^ 9 + ((510 / 79) : ℂ) * ζ ^ 11 - ((1072 / 237) : ℂ) * ζ ^ 12 - ((2416 / 237) : ℂ) * ζ ^ 13 + ((1450 / 237) : ℂ) * ζ ^ 15 - ((2416 / 237) : ℂ) * ζ ^ 17 - ((656 / 237) : ℂ) * ζ ^ 18 - ((590 / 237) : ℂ) * ζ ^ 21 + ((340 / 79) : ℂ) * ζ ^ 22 + ((1678 / 237) : ℂ) * ζ ^ 24 - ((1610 / 237) : ℂ) * ζ ^ 27 + ((778 / 79) : ℂ) * ζ ^ 28 + ((2416 / 237) : ℂ) * ζ ^ 29 + ((1262 / 237) : ℂ) * ζ ^ 30 - ((510 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY76_combinationStep06Coefficient00 : ℂ :=
  (-((5571 / 790) : ℂ) - ((914 / 395) : ℂ) * ζ ^ 1 - ((9953 / 790) : ℂ) * ζ ^ 2 - ((3022 / 395) : ℂ) * ζ ^ 5 - ((2191 / 395) : ℂ) * ζ ^ 6 - ((2191 / 395) : ℂ) * ζ ^ 8 - ((3022 / 395) : ℂ) * ζ ^ 9 - ((327 / 79) : ℂ) * ζ ^ 11 + ((3189 / 790) : ℂ) * ζ ^ 12 + ((914 / 395) : ℂ) * ζ ^ 13 - ((872 / 79) : ℂ) * ζ ^ 15 + ((914 / 395) : ℂ) * ζ ^ 17 + ((2702 / 395) : ℂ) * ζ ^ 18 + ((1968 / 395) : ℂ) * ζ ^ 21 + ((9953 / 790) : ℂ) * ζ ^ 22 - ((511 / 395) : ℂ) * ζ ^ 24 + ((2108 / 395) : ℂ) * ζ ^ 25 + ((872 / 79) : ℂ) * ζ ^ 27 + ((2191 / 395) : ℂ) * ζ ^ 28 - ((914 / 395) : ℂ) * ζ ^ 29 - ((7571 / 790) : ℂ) * ζ ^ 30 + ((327 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep06CoefficientIdentity00 :
    row18_reducedY76_combinationStep06Coefficient00 =
      row18_reducedY76_combinationStep05Coefficient00 +
        row18_reducedY76_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep06Coefficient00 row18_reducedY76_combinationStep05Coefficient00 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep06Coefficient01 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep06CoefficientIdentity01 :
    row18_reducedY76_combinationStep06Coefficient01 =
      row18_reducedY76_combinationStep05Coefficient01 +
        row18_reducedY76_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep06Coefficient01 row18_reducedY76_combinationStep05Coefficient01 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep06Coefficient02 : ℂ :=
  (-((1099 / 395) : ℂ) + ((235 / 79) : ℂ) * ζ ^ 1 + ((229 / 79) : ℂ) * ζ ^ 2 - ((581 / 158) : ℂ) * ζ ^ 3 + ((1077 / 158) : ℂ) * ζ ^ 5 + ((2002 / 395) : ℂ) * ζ ^ 8 - ((247 / 158) : ℂ) * ζ ^ 9 + ((414 / 79) : ℂ) * ζ ^ 11 + ((196 / 395) : ℂ) * ζ ^ 12 - ((235 / 79) : ℂ) * ζ ^ 13 - ((13 / 79) : ℂ) * ζ ^ 15 - ((235 / 79) : ℂ) * ζ ^ 17 - ((229 / 79) : ℂ) * ζ ^ 18 - ((1051 / 158) : ℂ) * ζ ^ 21 - ((229 / 79) : ℂ) * ζ ^ 22 - ((2198 / 395) : ℂ) * ζ ^ 24 - ((607 / 158) : ℂ) * ζ ^ 25 - ((1051 / 158) : ℂ) * ζ ^ 27 - ((2002 / 395) : ℂ) * ζ ^ 28 + ((235 / 79) : ℂ) * ζ ^ 29 - ((242 / 79) : ℂ) * ζ ^ 30 - ((414 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep06CoefficientIdentity02 :
    row18_reducedY76_combinationStep06Coefficient02 =
      row18_reducedY76_combinationStep05Coefficient02 +
        row18_reducedY76_combinationStep06Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep06Coefficient02 row18_reducedY76_combinationStep05Coefficient02 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 (((16467 / 6241) : ℂ) + ((207857 / 37446) : ℂ) * ζ ^ 1 + ((148852 / 18723) : ℂ) * ζ ^ 2 + ((28942 / 18723) : ℂ) * ζ ^ 3 - ((18919 / 6241) : ℂ) * ζ ^ 4 - ((46941 / 6241) : ℂ) * ζ ^ 5 - ((87662 / 18723) : ℂ) * ζ ^ 6 - ((18695 / 37446) : ℂ) * ζ ^ 7 + ((126409 / 37446) : ℂ) * ζ ^ 8 + ((88937 / 37446) : ℂ) * ζ ^ 9 + ((35603 / 12482) : ℂ) * ζ ^ 10 - ((2362 / 18723) : ℂ) * ζ ^ 11 - ((10645 / 6241) : ℂ) * ζ ^ 12 - ((20782 / 6241) : ℂ) * ζ ^ 13 - ((23318 / 18723) : ℂ) * ζ ^ 14 + ((31069 / 37446) : ℂ) * ζ ^ 15 + ((53408 / 18723) : ℂ) * ζ ^ 16 + ((17310 / 6241) : ℂ) * ζ ^ 17 + ((21337 / 12482) : ℂ) * ζ ^ 18 - ((21153 / 12482) : ℂ) * ζ ^ 19 - ((54992 / 18723) : ℂ) * ζ ^ 20 - ((44488 / 18723) : ℂ) * ζ ^ 21 - ((2624 / 6241) : ℂ) * ζ ^ 22 + ((34817 / 18723) : ℂ) * ζ ^ 23 + ((72923 / 18723) : ℂ) * ζ ^ 24 + ((76951 / 37446) : ℂ) * ζ ^ 25 - ((7561 / 6241) : ℂ) * ζ ^ 26 - ((128827 / 37446) : ℂ) * ζ ^ 27 - ((12821 / 12482) : ℂ) * ζ ^ 28 + ((115 / 158) : ℂ) * ζ ^ 29 + ((3825 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep06Coefficient03 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep06CoefficientIdentity03 :
    row18_reducedY76_combinationStep06Coefficient03 =
      row18_reducedY76_combinationStep05Coefficient03 +
        row18_reducedY76_combinationStep06Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep06Coefficient03 row18_reducedY76_combinationStep05Coefficient03 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 (-((101701 / 18723) : ℂ) - ((140687 / 18723) : ℂ) * ζ ^ 1 - ((2252 / 6241) : ℂ) * ζ ^ 2 - ((27167 / 37446) : ℂ) * ζ ^ 3 - ((26407 / 18723) : ℂ) * ζ ^ 4 + ((135227 / 37446) : ℂ) * ζ ^ 5 + ((99017 / 12482) : ℂ) * ζ ^ 6 + ((37283 / 6241) : ℂ) * ζ ^ 7 - ((22097 / 6241) : ℂ) * ζ ^ 8 - ((109707 / 12482) : ℂ) * ζ ^ 9 - ((144223 / 18723) : ℂ) * ζ ^ 10 - ((122357 / 37446) : ℂ) * ζ ^ 11 + ((247607 / 37446) : ℂ) * ζ ^ 12 + ((117578 / 18723) : ℂ) * ζ ^ 13 + ((20755 / 12482) : ℂ) * ζ ^ 14 - ((604 / 237) : ℂ) * ζ ^ 15 - ((91817 / 18723) : ℂ) * ζ ^ 16 - ((266323 / 37446) : ℂ) * ζ ^ 17 - ((140453 / 18723) : ℂ) * ζ ^ 18 - ((50335 / 18723) : ℂ) * ζ ^ 19 + ((297983 / 37446) : ℂ) * ζ ^ 20 + ((113860 / 18723) : ℂ) * ζ ^ 21 - ((14494 / 6241) : ℂ) * ζ ^ 22 - ((50972 / 6241) : ℂ) * ζ ^ 23 - ((55917 / 12482) : ℂ) * ζ ^ 24 - ((7389 / 12482) : ℂ) * ζ ^ 25 + ((102913 / 18723) : ℂ) * ζ ^ 26 + ((29485 / 12482) : ℂ) * ζ ^ 27 + ((5363 / 37446) : ℂ) * ζ ^ 28 - ((346 / 18723) : ℂ) * ζ ^ 29 - ((3570 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep06Coefficient04 : ℂ :=
  (((5571 / 790) : ℂ) + ((914 / 395) : ℂ) * ζ ^ 1 + ((9953 / 790) : ℂ) * ζ ^ 2 + ((3022 / 395) : ℂ) * ζ ^ 5 + ((2191 / 395) : ℂ) * ζ ^ 6 + ((2191 / 395) : ℂ) * ζ ^ 8 + ((3022 / 395) : ℂ) * ζ ^ 9 + ((327 / 79) : ℂ) * ζ ^ 11 - ((3189 / 790) : ℂ) * ζ ^ 12 - ((914 / 395) : ℂ) * ζ ^ 13 + ((872 / 79) : ℂ) * ζ ^ 15 - ((914 / 395) : ℂ) * ζ ^ 17 - ((2702 / 395) : ℂ) * ζ ^ 18 - ((1968 / 395) : ℂ) * ζ ^ 21 - ((9953 / 790) : ℂ) * ζ ^ 22 + ((511 / 395) : ℂ) * ζ ^ 24 - ((2108 / 395) : ℂ) * ζ ^ 25 - ((872 / 79) : ℂ) * ζ ^ 27 - ((2191 / 395) : ℂ) * ζ ^ 28 + ((914 / 395) : ℂ) * ζ ^ 29 + ((7571 / 790) : ℂ) * ζ ^ 30 - ((327 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep06CoefficientIdentity04 :
    row18_reducedY76_combinationStep06Coefficient04 =
      row18_reducedY76_combinationStep05Coefficient04 +
        row18_reducedY76_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep06Coefficient04 row18_reducedY76_combinationStep05Coefficient04 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep06Coefficient05 : ℂ :=
  (-((569 / 158) : ℂ) - ((37 / 79) : ℂ) * ζ ^ 1 + ((631 / 79) : ℂ) * ζ ^ 2 + ((175 / 158) : ℂ) * ζ ^ 3 + ((655 / 158) : ℂ) * ζ ^ 5 + ((495 / 158) : ℂ) * ζ ^ 6 + ((733 / 79) : ℂ) * ζ ^ 8 + ((675 / 158) : ℂ) * ζ ^ 9 + ((655 / 158) : ℂ) * ζ ^ 11 + ((733 / 158) : ℂ) * ζ ^ 12 + ((37 / 79) : ℂ) * ζ ^ 13 + ((27 / 79) : ℂ) * ζ ^ 15 + ((37 / 79) : ℂ) * ζ ^ 17 - ((495 / 158) : ℂ) * ζ ^ 18 - ((415 / 79) : ℂ) * ζ ^ 21 - ((631 / 79) : ℂ) * ζ ^ 22 - ((897 / 158) : ℂ) * ζ ^ 24 - ((729 / 158) : ℂ) * ζ ^ 25 - ((729 / 158) : ℂ) * ζ ^ 27 - ((733 / 79) : ℂ) * ζ ^ 28 - ((37 / 79) : ℂ) * ζ ^ 29 - ((655 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep06CoefficientIdentity05 :
    row18_reducedY76_combinationStep06Coefficient05 =
      row18_reducedY76_combinationStep05Coefficient05 +
        row18_reducedY76_combinationStep06Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep06Coefficient05 row18_reducedY76_combinationStep05Coefficient05 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 (-((46283 / 18723) : ℂ) + ((25577 / 12482) : ℂ) * ζ ^ 1 + ((28135 / 37446) : ℂ) * ζ ^ 2 + ((557 / 37446) : ℂ) * ζ ^ 3 - ((10717 / 6241) : ℂ) * ζ ^ 4 + ((715 / 12482) : ℂ) * ζ ^ 5 - ((5058 / 6241) : ℂ) * ζ ^ 6 - ((24904 / 18723) : ℂ) * ζ ^ 7 + ((21955 / 18723) : ℂ) * ζ ^ 8 + ((1201 / 37446) : ℂ) * ζ ^ 9 - ((101609 / 37446) : ℂ) * ζ ^ 10 - ((116 / 237) : ℂ) * ζ ^ 11 + ((14049 / 12482) : ℂ) * ζ ^ 12 - ((12085 / 12482) : ℂ) * ζ ^ 13 - ((73060 / 18723) : ℂ) * ζ ^ 14 + ((3686 / 6241) : ℂ) * ζ ^ 15 + ((35515 / 37446) : ℂ) * ζ ^ 16 - ((33401 / 37446) : ℂ) * ζ ^ 17 - ((75404 / 18723) : ℂ) * ζ ^ 18 - ((55025 / 37446) : ℂ) * ζ ^ 19 - ((30329 / 37446) : ℂ) * ζ ^ 20 - ((48119 / 18723) : ℂ) * ζ ^ 21 - ((37013 / 12482) : ℂ) * ζ ^ 22 + ((16780 / 6241) : ℂ) * ζ ^ 23 - ((9052 / 6241) : ℂ) * ζ ^ 24 + ((5143 / 18723) : ℂ) * ζ ^ 25 - ((486 / 6241) : ℂ) * ζ ^ 26 + ((16451 / 18723) : ℂ) * ζ ^ 27 - ((114803 / 37446) : ℂ) * ζ ^ 28 + ((33107 / 37446) : ℂ) * ζ ^ 29 + ((3315 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep06Coefficient06 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep06CoefficientIdentity06 :
    row18_reducedY76_combinationStep06Coefficient06 =
      row18_reducedY76_combinationStep05Coefficient06 +
        row18_reducedY76_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep06Coefficient06 row18_reducedY76_combinationStep05Coefficient06 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep06Coefficient07 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep06CoefficientIdentity07 :
    row18_reducedY76_combinationStep06Coefficient07 =
      row18_reducedY76_combinationStep05Coefficient07 +
        row18_reducedY76_combinationStep06Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep06Coefficient07 row18_reducedY76_combinationStep05Coefficient07 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 (((101701 / 18723) : ℂ) + ((140687 / 18723) : ℂ) * ζ ^ 1 + ((2252 / 6241) : ℂ) * ζ ^ 2 + ((27167 / 37446) : ℂ) * ζ ^ 3 + ((26407 / 18723) : ℂ) * ζ ^ 4 - ((135227 / 37446) : ℂ) * ζ ^ 5 - ((99017 / 12482) : ℂ) * ζ ^ 6 - ((37283 / 6241) : ℂ) * ζ ^ 7 + ((22097 / 6241) : ℂ) * ζ ^ 8 + ((109707 / 12482) : ℂ) * ζ ^ 9 + ((144223 / 18723) : ℂ) * ζ ^ 10 + ((122357 / 37446) : ℂ) * ζ ^ 11 - ((247607 / 37446) : ℂ) * ζ ^ 12 - ((117578 / 18723) : ℂ) * ζ ^ 13 - ((20755 / 12482) : ℂ) * ζ ^ 14 + ((604 / 237) : ℂ) * ζ ^ 15 + ((91817 / 18723) : ℂ) * ζ ^ 16 + ((266323 / 37446) : ℂ) * ζ ^ 17 + ((140453 / 18723) : ℂ) * ζ ^ 18 + ((50335 / 18723) : ℂ) * ζ ^ 19 - ((297983 / 37446) : ℂ) * ζ ^ 20 - ((113860 / 18723) : ℂ) * ζ ^ 21 + ((14494 / 6241) : ℂ) * ζ ^ 22 + ((50972 / 6241) : ℂ) * ζ ^ 23 + ((55917 / 12482) : ℂ) * ζ ^ 24 + ((7389 / 12482) : ℂ) * ζ ^ 25 - ((102913 / 18723) : ℂ) * ζ ^ 26 - ((29485 / 12482) : ℂ) * ζ ^ 27 - ((5363 / 37446) : ℂ) * ζ ^ 28 + ((346 / 18723) : ℂ) * ζ ^ 29 + ((3570 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep06Coefficient08 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep06CoefficientIdentity08 :
    row18_reducedY76_combinationStep06Coefficient08 =
      row18_reducedY76_combinationStep05Coefficient08 +
        row18_reducedY76_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep06Coefficient08 row18_reducedY76_combinationStep05Coefficient08 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep06Coefficient09 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep06CoefficientIdentity09 :
    row18_reducedY76_combinationStep06Coefficient09 =
      row18_reducedY76_combinationStep05Coefficient09 +
        row18_reducedY76_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep06Coefficient09 row18_reducedY76_combinationStep05Coefficient09 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep06Coefficient10 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep06CoefficientIdentity10 :
    row18_reducedY76_combinationStep06Coefficient10 =
      row18_reducedY76_combinationStep05Coefficient10 +
        row18_reducedY76_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep06Coefficient10 row18_reducedY76_combinationStep05Coefficient10 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep06Coefficient11 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep06CoefficientIdentity11 :
    row18_reducedY76_combinationStep06Coefficient11 =
      row18_reducedY76_combinationStep05Coefficient11 +
        row18_reducedY76_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep06Coefficient11 row18_reducedY76_combinationStep05Coefficient11 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep06Coefficient12 : ℂ :=
  (-((42 / 79) : ℂ) - ((9 / 79) : ℂ) * ζ ^ 1 - ((1 / 158) : ℂ) * ζ ^ 2 - ((4 / 79) : ℂ) * ζ ^ 5 + ((83 / 158) : ℂ) * ζ ^ 6 + ((83 / 158) : ℂ) * ζ ^ 8 - ((4 / 79) : ℂ) * ζ ^ 9 + ((49 / 158) : ℂ) * ζ ^ 11 + ((104 / 79) : ℂ) * ζ ^ 12 + ((9 / 79) : ℂ) * ζ ^ 13 - ((40 / 79) : ℂ) * ζ ^ 15 + ((9 / 79) : ℂ) * ζ ^ 17 + ((19 / 79) : ℂ) * ζ ^ 18 + ((13 / 158) : ℂ) * ζ ^ 21 + ((1 / 158) : ℂ) * ζ ^ 22 - ((121 / 158) : ℂ) * ζ ^ 24 - ((5 / 79) : ℂ) * ζ ^ 25 + ((40 / 79) : ℂ) * ζ ^ 27 - ((83 / 158) : ℂ) * ζ ^ 28 - ((9 / 79) : ℂ) * ζ ^ 29 - ((125 / 158) : ℂ) * ζ ^ 30 - ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep06CoefficientIdentity12 :
    row18_reducedY76_combinationStep06Coefficient12 =
      row18_reducedY76_combinationStep05Coefficient12 +
        row18_reducedY76_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep06Coefficient12 row18_reducedY76_combinationStep05Coefficient12 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep06Coefficient13 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep06CoefficientIdentity13 :
    row18_reducedY76_combinationStep06Coefficient13 =
      row18_reducedY76_combinationStep05Coefficient13 +
        row18_reducedY76_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep06Coefficient13 row18_reducedY76_combinationStep05Coefficient13 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep06Coefficient14 : ℂ :=
  (((33 / 79) : ℂ) - ((24 / 79) : ℂ) * ζ ^ 1 - ((19 / 158) : ℂ) * ζ ^ 2 + ((77 / 158) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((2 / 79) : ℂ) * ζ ^ 6 + ((5 / 158) : ℂ) * ζ ^ 8 + ((95 / 158) : ℂ) * ζ ^ 9 + ((9 / 79) : ℂ) * ζ ^ 11 + ((5 / 158) : ℂ) * ζ ^ 12 + ((24 / 79) : ℂ) * ζ ^ 13 - ((5 / 79) : ℂ) * ζ ^ 15 + ((24 / 79) : ℂ) * ζ ^ 17 - ((23 / 158) : ℂ) * ζ ^ 18 - ((29 / 158) : ℂ) * ζ ^ 21 + ((19 / 158) : ℂ) * ζ ^ 22 - ((67 / 158) : ℂ) * ζ ^ 25 + ((29 / 158) : ℂ) * ζ ^ 27 - ((5 / 158) : ℂ) * ζ ^ 28 - ((24 / 79) : ℂ) * ζ ^ 29 + ((1 / 79) : ℂ) * ζ ^ 30 - ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep06CoefficientIdentity14 :
    row18_reducedY76_combinationStep06Coefficient14 =
      row18_reducedY76_combinationStep05Coefficient14 +
        row18_reducedY76_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep06Coefficient14 row18_reducedY76_combinationStep05Coefficient14 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep06Coefficient15 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep06CoefficientIdentity15 :
    row18_reducedY76_combinationStep06Coefficient15 =
      row18_reducedY76_combinationStep05Coefficient15 +
        row18_reducedY76_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep06Coefficient15 row18_reducedY76_combinationStep05Coefficient15 row18_reducedY76_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY76_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY76_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY76_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY76_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY76_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY76_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY76_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY76_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY76_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY76_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY76_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY76_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY76_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY76_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY76_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY76_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY76_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY76_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY76_combinationStep06CoefficientIdentity00,
      row18_reducedY76_combinationStep06CoefficientIdentity01,
      row18_reducedY76_combinationStep06CoefficientIdentity02,
      row18_reducedY76_combinationStep06CoefficientIdentity03,
      row18_reducedY76_combinationStep06CoefficientIdentity04,
      row18_reducedY76_combinationStep06CoefficientIdentity05,
      row18_reducedY76_combinationStep06CoefficientIdentity06,
      row18_reducedY76_combinationStep06CoefficientIdentity07,
      row18_reducedY76_combinationStep06CoefficientIdentity08,
      row18_reducedY76_combinationStep06CoefficientIdentity09,
      row18_reducedY76_combinationStep06CoefficientIdentity10,
      row18_reducedY76_combinationStep06CoefficientIdentity11,
      row18_reducedY76_combinationStep06CoefficientIdentity12,
      row18_reducedY76_combinationStep06CoefficientIdentity13,
      row18_reducedY76_combinationStep06CoefficientIdentity14,
      row18_reducedY76_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY76_combinationStep06Multiplier * equation

private def row18_reducedY76_combinationStep07Multiplier : ℂ :=
  (((208 / 79) : ℂ) + ((380 / 79) : ℂ) * ζ ^ 1 - ((60 / 79) : ℂ) * ζ ^ 2 + ((132 / 79) : ℂ) * ζ ^ 3 + ((306 / 79) : ℂ) * ζ ^ 5 - ((236 / 79) : ℂ) * ζ ^ 8 - ((156 / 79) : ℂ) * ζ ^ 9 + ((24 / 79) : ℂ) * ζ ^ 11 - ((180 / 79) : ℂ) * ζ ^ 12 - ((380 / 79) : ℂ) * ζ ^ 13 - ((58 / 79) : ℂ) * ζ ^ 15 - ((380 / 79) : ℂ) * ζ ^ 17 + ((60 / 79) : ℂ) * ζ ^ 18 - ((248 / 79) : ℂ) * ζ ^ 21 + ((60 / 79) : ℂ) * ζ ^ 22 + ((416 / 79) : ℂ) * ζ ^ 24 + ((74 / 79) : ℂ) * ζ ^ 25 - ((248 / 79) : ℂ) * ζ ^ 27 + ((236 / 79) : ℂ) * ζ ^ 28 + ((380 / 79) : ℂ) * ζ ^ 29 + ((160 / 79) : ℂ) * ζ ^ 30 - ((24 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY76_combinationStep07Coefficient00 : ℂ :=
  (-((5571 / 790) : ℂ) - ((914 / 395) : ℂ) * ζ ^ 1 - ((9953 / 790) : ℂ) * ζ ^ 2 - ((3022 / 395) : ℂ) * ζ ^ 5 - ((2191 / 395) : ℂ) * ζ ^ 6 - ((2191 / 395) : ℂ) * ζ ^ 8 - ((3022 / 395) : ℂ) * ζ ^ 9 - ((327 / 79) : ℂ) * ζ ^ 11 + ((3189 / 790) : ℂ) * ζ ^ 12 + ((914 / 395) : ℂ) * ζ ^ 13 - ((872 / 79) : ℂ) * ζ ^ 15 + ((914 / 395) : ℂ) * ζ ^ 17 + ((2702 / 395) : ℂ) * ζ ^ 18 + ((1968 / 395) : ℂ) * ζ ^ 21 + ((9953 / 790) : ℂ) * ζ ^ 22 - ((511 / 395) : ℂ) * ζ ^ 24 + ((2108 / 395) : ℂ) * ζ ^ 25 + ((872 / 79) : ℂ) * ζ ^ 27 + ((2191 / 395) : ℂ) * ζ ^ 28 - ((914 / 395) : ℂ) * ζ ^ 29 - ((7571 / 790) : ℂ) * ζ ^ 30 + ((327 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep07CoefficientIdentity00 :
    row18_reducedY76_combinationStep07Coefficient00 =
      row18_reducedY76_combinationStep06Coefficient00 +
        row18_reducedY76_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep07Coefficient00 row18_reducedY76_combinationStep06Coefficient00 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep07Coefficient01 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep07CoefficientIdentity01 :
    row18_reducedY76_combinationStep07Coefficient01 =
      row18_reducedY76_combinationStep06Coefficient01 +
        row18_reducedY76_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep07Coefficient01 row18_reducedY76_combinationStep06Coefficient01 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep07Coefficient02 : ℂ :=
  (-((1179 / 395) : ℂ) + ((224 / 79) : ℂ) * ζ ^ 1 + ((657 / 158) : ℂ) * ζ ^ 2 - ((723 / 158) : ℂ) * ζ ^ 3 + ((913 / 158) : ℂ) * ζ ^ 5 + ((4459 / 790) : ℂ) * ζ ^ 8 - ((77 / 158) : ℂ) * ζ ^ 9 + ((400 / 79) : ℂ) * ζ ^ 11 + ((257 / 790) : ℂ) * ζ ^ 12 - ((224 / 79) : ℂ) * ζ ^ 13 + ((129 / 79) : ℂ) * ζ ^ 15 - ((224 / 79) : ℂ) * ζ ^ 17 - ((657 / 158) : ℂ) * ζ ^ 18 - ((1171 / 158) : ℂ) * ζ ^ 21 - ((657 / 158) : ℂ) * ζ ^ 22 - ((2358 / 395) : ℂ) * ζ ^ 24 - ((465 / 158) : ℂ) * ζ ^ 25 - ((1171 / 158) : ℂ) * ζ ^ 27 - ((4459 / 790) : ℂ) * ζ ^ 28 + ((224 / 79) : ℂ) * ζ ^ 29 - ((165 / 79) : ℂ) * ζ ^ 30 - ((400 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep07CoefficientIdentity02 :
    row18_reducedY76_combinationStep07Coefficient02 =
      row18_reducedY76_combinationStep06Coefficient02 +
        row18_reducedY76_combinationStep07Multiplier *
          (((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((73 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((105 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((73 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep07Coefficient02 row18_reducedY76_combinationStep06Coefficient02 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 (((1888 / 6241) : ℂ) + ((2581 / 6241) : ℂ) * ζ ^ 1 - ((21583 / 12482) : ℂ) * ζ ^ 2 - ((991 / 6241) : ℂ) * ζ ^ 3 - ((240 / 6241) : ℂ) * ζ ^ 4 + ((1388 / 6241) : ℂ) * ζ ^ 5 + ((11558 / 6241) : ℂ) * ζ ^ 6 - ((2537 / 12482) : ℂ) * ζ ^ 7 - ((13673 / 12482) : ℂ) * ζ ^ 8 - ((12113 / 6241) : ℂ) * ζ ^ 9 - ((19497 / 12482) : ℂ) * ζ ^ 10 + ((11841 / 12482) : ℂ) * ζ ^ 11 + ((5693 / 6241) : ℂ) * ζ ^ 12 + ((13017 / 12482) : ℂ) * ζ ^ 13 - ((1838 / 6241) : ℂ) * ζ ^ 14 - ((30721 / 12482) : ℂ) * ζ ^ 15 - ((13835 / 12482) : ℂ) * ζ ^ 16 - ((6279 / 12482) : ℂ) * ζ ^ 17 + ((4003 / 12482) : ℂ) * ζ ^ 18 + ((7967 / 6241) : ℂ) * ζ ^ 19 + ((7195 / 12482) : ℂ) * ζ ^ 20 + ((591 / 12482) : ℂ) * ζ ^ 21 + ((2769 / 12482) : ℂ) * ζ ^ 22 - ((13 / 79) : ℂ) * ζ ^ 23 + ((793 / 6241) : ℂ) * ζ ^ 24 + ((3038 / 6241) : ℂ) * ζ ^ 25 + ((2527 / 6241) : ℂ) * ζ ^ 26 + ((2576 / 6241) : ℂ) * ζ ^ 27 + ((1904 / 6241) : ℂ) * ζ ^ 28 + ((464 / 6241) : ℂ) * ζ ^ 29 - ((84 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep07Coefficient03 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep07CoefficientIdentity03 :
    row18_reducedY76_combinationStep07Coefficient03 =
      row18_reducedY76_combinationStep06Coefficient03 +
        row18_reducedY76_combinationStep07Multiplier *
          (-((5 / 316) : ℂ) + ((3 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((33 / 158) : ℂ) * ζ ^ 3 + ((3 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 + ((10 / 79) : ℂ) * ζ ^ 8 - ((3 / 316) : ℂ) * ζ ^ 9 - ((33 / 316) : ℂ) * ζ ^ 11 - ((3 / 79) : ℂ) * ζ ^ 12 - ((3 / 316) : ℂ) * ζ ^ 13 - ((35 / 158) : ℂ) * ζ ^ 15 - ((3 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 - ((45 / 158) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((59 / 316) : ℂ) * ζ ^ 24 - ((1 / 79) : ℂ) * ζ ^ 27 - ((10 / 79) : ℂ) * ζ ^ 28 + ((3 / 316) : ℂ) * ζ ^ 29 - ((13 / 79) : ℂ) * ζ ^ 30 + ((33 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep07Coefficient03 row18_reducedY76_combinationStep06Coefficient03 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 (((3058 / 6241) : ℂ) + ((392 / 6241) : ℂ) * ζ ^ 1 - ((2841 / 12482) : ℂ) * ζ ^ 2 - ((103 / 6241) : ℂ) * ζ ^ 3 + ((3836 / 6241) : ℂ) * ζ ^ 4 - ((4895 / 12482) : ℂ) * ζ ^ 5 - ((2491 / 12482) : ℂ) * ζ ^ 6 - ((12839 / 12482) : ℂ) * ζ ^ 7 + ((2017 / 12482) : ℂ) * ζ ^ 8 + ((10211 / 12482) : ℂ) * ζ ^ 9 + ((2538 / 6241) : ℂ) * ζ ^ 10 - ((1486 / 6241) : ℂ) * ζ ^ 11 - ((24711 / 12482) : ℂ) * ζ ^ 12 - ((6425 / 12482) : ℂ) * ζ ^ 13 - ((1453 / 6241) : ℂ) * ζ ^ 14 + ((5079 / 12482) : ℂ) * ζ ^ 15 + ((2641 / 12482) : ℂ) * ζ ^ 16 - ((707 / 12482) : ℂ) * ζ ^ 17 - ((12423 / 12482) : ℂ) * ζ ^ 18 - ((1465 / 6241) : ℂ) * ζ ^ 19 - ((10497 / 12482) : ℂ) * ζ ^ 20 - ((3557 / 6241) : ℂ) * ζ ^ 21 - ((2515 / 12482) : ℂ) * ζ ^ 22 + ((7701 / 6241) : ℂ) * ζ ^ 23 - ((6705 / 12482) : ℂ) * ζ ^ 24 - ((2191 / 6241) : ℂ) * ζ ^ 25 - ((6207 / 6241) : ℂ) * ζ ^ 26 - ((2633 / 6241) : ℂ) * ζ ^ 27 + ((1037 / 6241) : ℂ) * ζ ^ 28 + ((1632 / 6241) : ℂ) * ζ ^ 29 - ((198 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep07Coefficient04 : ℂ :=
  (((5571 / 790) : ℂ) + ((914 / 395) : ℂ) * ζ ^ 1 + ((9953 / 790) : ℂ) * ζ ^ 2 + ((3022 / 395) : ℂ) * ζ ^ 5 + ((2191 / 395) : ℂ) * ζ ^ 6 + ((2191 / 395) : ℂ) * ζ ^ 8 + ((3022 / 395) : ℂ) * ζ ^ 9 + ((327 / 79) : ℂ) * ζ ^ 11 - ((3189 / 790) : ℂ) * ζ ^ 12 - ((914 / 395) : ℂ) * ζ ^ 13 + ((872 / 79) : ℂ) * ζ ^ 15 - ((914 / 395) : ℂ) * ζ ^ 17 - ((2702 / 395) : ℂ) * ζ ^ 18 - ((1968 / 395) : ℂ) * ζ ^ 21 - ((9953 / 790) : ℂ) * ζ ^ 22 + ((511 / 395) : ℂ) * ζ ^ 24 - ((2108 / 395) : ℂ) * ζ ^ 25 - ((872 / 79) : ℂ) * ζ ^ 27 - ((2191 / 395) : ℂ) * ζ ^ 28 + ((914 / 395) : ℂ) * ζ ^ 29 + ((7571 / 790) : ℂ) * ζ ^ 30 - ((327 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep07CoefficientIdentity04 :
    row18_reducedY76_combinationStep07Coefficient04 =
      row18_reducedY76_combinationStep06Coefficient04 +
        row18_reducedY76_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep07Coefficient04 row18_reducedY76_combinationStep06Coefficient04 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep07Coefficient05 : ℂ :=
  (-((569 / 158) : ℂ) - ((37 / 79) : ℂ) * ζ ^ 1 + ((631 / 79) : ℂ) * ζ ^ 2 + ((175 / 158) : ℂ) * ζ ^ 3 + ((655 / 158) : ℂ) * ζ ^ 5 + ((495 / 158) : ℂ) * ζ ^ 6 + ((733 / 79) : ℂ) * ζ ^ 8 + ((675 / 158) : ℂ) * ζ ^ 9 + ((655 / 158) : ℂ) * ζ ^ 11 + ((733 / 158) : ℂ) * ζ ^ 12 + ((37 / 79) : ℂ) * ζ ^ 13 + ((27 / 79) : ℂ) * ζ ^ 15 + ((37 / 79) : ℂ) * ζ ^ 17 - ((495 / 158) : ℂ) * ζ ^ 18 - ((415 / 79) : ℂ) * ζ ^ 21 - ((631 / 79) : ℂ) * ζ ^ 22 - ((897 / 158) : ℂ) * ζ ^ 24 - ((729 / 158) : ℂ) * ζ ^ 25 - ((729 / 158) : ℂ) * ζ ^ 27 - ((733 / 79) : ℂ) * ζ ^ 28 - ((37 / 79) : ℂ) * ζ ^ 29 - ((655 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY76_combinationStep07CoefficientIdentity05 :
    row18_reducedY76_combinationStep07Coefficient05 =
      row18_reducedY76_combinationStep06Coefficient05 +
        row18_reducedY76_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep07Coefficient05 row18_reducedY76_combinationStep06Coefficient05 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep07Coefficient06 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep07CoefficientIdentity06 :
    row18_reducedY76_combinationStep07Coefficient06 =
      row18_reducedY76_combinationStep06Coefficient06 +
        row18_reducedY76_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep07Coefficient06 row18_reducedY76_combinationStep06Coefficient06 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep07Coefficient07 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep07CoefficientIdentity07 :
    row18_reducedY76_combinationStep07Coefficient07 =
      row18_reducedY76_combinationStep06Coefficient07 +
        row18_reducedY76_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep07Coefficient07 row18_reducedY76_combinationStep06Coefficient07 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep07Coefficient08 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep07CoefficientIdentity08 :
    row18_reducedY76_combinationStep07Coefficient08 =
      row18_reducedY76_combinationStep06Coefficient08 +
        row18_reducedY76_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep07Coefficient08 row18_reducedY76_combinationStep06Coefficient08 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep07Coefficient09 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep07CoefficientIdentity09 :
    row18_reducedY76_combinationStep07Coefficient09 =
      row18_reducedY76_combinationStep06Coefficient09 +
        row18_reducedY76_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep07Coefficient09 row18_reducedY76_combinationStep06Coefficient09 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep07Coefficient10 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep07CoefficientIdentity10 :
    row18_reducedY76_combinationStep07Coefficient10 =
      row18_reducedY76_combinationStep06Coefficient10 +
        row18_reducedY76_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep07Coefficient10 row18_reducedY76_combinationStep06Coefficient10 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep07Coefficient11 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep07CoefficientIdentity11 :
    row18_reducedY76_combinationStep07Coefficient11 =
      row18_reducedY76_combinationStep06Coefficient11 +
        row18_reducedY76_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep07Coefficient11 row18_reducedY76_combinationStep06Coefficient11 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep07Coefficient12 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep07CoefficientIdentity12 :
    row18_reducedY76_combinationStep07Coefficient12 =
      row18_reducedY76_combinationStep06Coefficient12 +
        row18_reducedY76_combinationStep07Multiplier *
          (((5 / 316) : ℂ) - ((3 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((33 / 158) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 + ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 + ((3 / 316) : ℂ) * ζ ^ 9 + ((33 / 316) : ℂ) * ζ ^ 11 + ((3 / 79) : ℂ) * ζ ^ 12 + ((3 / 316) : ℂ) * ζ ^ 13 + ((35 / 158) : ℂ) * ζ ^ 15 + ((3 / 316) : ℂ) * ζ ^ 17 + ((19 / 316) : ℂ) * ζ ^ 18 + ((45 / 158) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((1 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 - ((3 / 316) : ℂ) * ζ ^ 29 + ((13 / 79) : ℂ) * ζ ^ 30 - ((33 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep07Coefficient12 row18_reducedY76_combinationStep06Coefficient12 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 (-((3058 / 6241) : ℂ) - ((392 / 6241) : ℂ) * ζ ^ 1 + ((2841 / 12482) : ℂ) * ζ ^ 2 + ((103 / 6241) : ℂ) * ζ ^ 3 - ((3836 / 6241) : ℂ) * ζ ^ 4 + ((4895 / 12482) : ℂ) * ζ ^ 5 + ((2491 / 12482) : ℂ) * ζ ^ 6 + ((12839 / 12482) : ℂ) * ζ ^ 7 - ((2017 / 12482) : ℂ) * ζ ^ 8 - ((10211 / 12482) : ℂ) * ζ ^ 9 - ((2538 / 6241) : ℂ) * ζ ^ 10 + ((1486 / 6241) : ℂ) * ζ ^ 11 + ((24711 / 12482) : ℂ) * ζ ^ 12 + ((6425 / 12482) : ℂ) * ζ ^ 13 + ((1453 / 6241) : ℂ) * ζ ^ 14 - ((5079 / 12482) : ℂ) * ζ ^ 15 - ((2641 / 12482) : ℂ) * ζ ^ 16 + ((707 / 12482) : ℂ) * ζ ^ 17 + ((12423 / 12482) : ℂ) * ζ ^ 18 + ((1465 / 6241) : ℂ) * ζ ^ 19 + ((10497 / 12482) : ℂ) * ζ ^ 20 + ((3557 / 6241) : ℂ) * ζ ^ 21 + ((2515 / 12482) : ℂ) * ζ ^ 22 - ((7701 / 6241) : ℂ) * ζ ^ 23 + ((6705 / 12482) : ℂ) * ζ ^ 24 + ((2191 / 6241) : ℂ) * ζ ^ 25 + ((6207 / 6241) : ℂ) * ζ ^ 26 + ((2633 / 6241) : ℂ) * ζ ^ 27 - ((1037 / 6241) : ℂ) * ζ ^ 28 - ((1632 / 6241) : ℂ) * ζ ^ 29 + ((198 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep07Coefficient13 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep07CoefficientIdentity13 :
    row18_reducedY76_combinationStep07Coefficient13 =
      row18_reducedY76_combinationStep06Coefficient13 +
        row18_reducedY76_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep07Coefficient13 row18_reducedY76_combinationStep06Coefficient13 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep07Coefficient14 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY76_combinationStep07CoefficientIdentity14 :
    row18_reducedY76_combinationStep07Coefficient14 =
      row18_reducedY76_combinationStep06Coefficient14 +
        row18_reducedY76_combinationStep07Multiplier *
          (-((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((35 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep07Coefficient14 row18_reducedY76_combinationStep06Coefficient14 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 (-((4466 / 6241) : ℂ) - ((3988 / 6241) : ℂ) * ζ ^ 1 - ((6751 / 12482) : ℂ) * ζ ^ 2 - ((1189 / 12482) : ℂ) * ζ ^ 3 + ((4723 / 6241) : ℂ) * ζ ^ 4 + ((1569 / 12482) : ℂ) * ζ ^ 5 - ((125 / 6241) : ℂ) * ζ ^ 6 - ((1633 / 6241) : ℂ) * ζ ^ 7 - ((4183 / 6241) : ℂ) * ζ ^ 8 + ((5487 / 6241) : ℂ) * ζ ^ 9 + ((1469 / 6241) : ℂ) * ζ ^ 10 + ((2829 / 6241) : ℂ) * ζ ^ 11 + ((1961 / 12482) : ℂ) * ζ ^ 12 - ((293 / 6241) : ℂ) * ζ ^ 13 + ((139 / 6241) : ℂ) * ζ ^ 14 + ((2645 / 12482) : ℂ) * ζ ^ 15 - ((191 / 6241) : ℂ) * ζ ^ 16 + ((3653 / 6241) : ℂ) * ζ ^ 17 + ((2886 / 6241) : ℂ) * ζ ^ 18 + ((3632 / 6241) : ℂ) * ζ ^ 19 - ((3885 / 6241) : ℂ) * ζ ^ 20 - ((2547 / 6241) : ℂ) * ζ ^ 21 + ((2357 / 12482) : ℂ) * ζ ^ 22 + ((3984 / 6241) : ℂ) * ζ ^ 23 + ((697 / 6241) : ℂ) * ζ ^ 24 - ((627 / 6241) : ℂ) * ζ ^ 25 - ((2849 / 6241) : ℂ) * ζ ^ 26 - ((718 / 6241) : ℂ) * ζ ^ 27 + ((916 / 6241) : ℂ) * ζ ^ 28 + ((8 / 79) : ℂ) * ζ ^ 29 - ((84 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep07Coefficient15 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep07CoefficientIdentity15 :
    row18_reducedY76_combinationStep07Coefficient15 =
      row18_reducedY76_combinationStep06Coefficient15 +
        row18_reducedY76_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep07Coefficient15 row18_reducedY76_combinationStep06Coefficient15 row18_reducedY76_combinationStep07Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY76_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY76_combinationStep07Coefficient00) * Y 0 0
      + (row18_reducedY76_combinationStep07Coefficient01) * Y 0 1
      + (row18_reducedY76_combinationStep07Coefficient02) * Y 1 0
      + (row18_reducedY76_combinationStep07Coefficient03) * Y 1 1
      + (row18_reducedY76_combinationStep07Coefficient04) * Y 2 2
      + (row18_reducedY76_combinationStep07Coefficient05) * Y 2 3
      + (row18_reducedY76_combinationStep07Coefficient06) * Y 3 2
      + (row18_reducedY76_combinationStep07Coefficient07) * Y 3 3
      + (row18_reducedY76_combinationStep07Coefficient08) * Y 4 4
      + (row18_reducedY76_combinationStep07Coefficient09) * Y 4 5
      + (row18_reducedY76_combinationStep07Coefficient10) * Y 5 4
      + (row18_reducedY76_combinationStep07Coefficient11) * Y 5 5
      + (row18_reducedY76_combinationStep07Coefficient12) * Y 6 6
      + (row18_reducedY76_combinationStep07Coefficient13) * Y 6 7
      + (row18_reducedY76_combinationStep07Coefficient14) * Y 7 6
      + (row18_reducedY76_combinationStep07Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY76_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation16
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY76_combinationStep07CoefficientIdentity00,
      row18_reducedY76_combinationStep07CoefficientIdentity01,
      row18_reducedY76_combinationStep07CoefficientIdentity02,
      row18_reducedY76_combinationStep07CoefficientIdentity03,
      row18_reducedY76_combinationStep07CoefficientIdentity04,
      row18_reducedY76_combinationStep07CoefficientIdentity05,
      row18_reducedY76_combinationStep07CoefficientIdentity06,
      row18_reducedY76_combinationStep07CoefficientIdentity07,
      row18_reducedY76_combinationStep07CoefficientIdentity08,
      row18_reducedY76_combinationStep07CoefficientIdentity09,
      row18_reducedY76_combinationStep07CoefficientIdentity10,
      row18_reducedY76_combinationStep07CoefficientIdentity11,
      row18_reducedY76_combinationStep07CoefficientIdentity12,
      row18_reducedY76_combinationStep07CoefficientIdentity13,
      row18_reducedY76_combinationStep07CoefficientIdentity14,
      row18_reducedY76_combinationStep07CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY76_combinationStep07Multiplier * equation

private def row18_reducedY76_combinationStep08Multiplier : ℂ :=
  (((116 / 79) : ℂ) + ((10942 / 395) : ℂ) * ζ ^ 1 - ((288 / 79) : ℂ) * ζ ^ 2 - ((2914 / 395) : ℂ) * ζ ^ 5 - ((404 / 79) : ℂ) * ζ ^ 6 - ((404 / 79) : ℂ) * ζ ^ 8 - ((2914 / 395) : ℂ) * ζ ^ 9 - ((1658 / 79) : ℂ) * ζ ^ 11 - ((2032 / 79) : ℂ) * ζ ^ 12 - ((10942 / 395) : ℂ) * ζ ^ 13 - ((50 / 79) : ℂ) * ζ ^ 15 - ((10942 / 395) : ℂ) * ζ ^ 17 - ((1316 / 79) : ℂ) * ζ ^ 18 - ((4014 / 395) : ℂ) * ζ ^ 21 + ((288 / 79) : ℂ) * ζ ^ 22 + ((1720 / 79) : ℂ) * ζ ^ 24 + ((13856 / 395) : ℂ) * ζ ^ 25 + ((50 / 79) : ℂ) * ζ ^ 27 + ((404 / 79) : ℂ) * ζ ^ 28 + ((10942 / 395) : ℂ) * ζ ^ 29 + ((1628 / 79) : ℂ) * ζ ^ 30 + ((1658 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY76_combinationStep08Coefficient00 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity00 :
    row18_reducedY76_combinationStep08Coefficient00 =
      row18_reducedY76_combinationStep07Coefficient00 +
        row18_reducedY76_combinationStep08Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep08Coefficient00 row18_reducedY76_combinationStep07Coefficient00 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 (-((436629 / 62410) : ℂ) - ((8195 / 6241) : ℂ) * ζ ^ 1 - ((439879 / 31205) : ℂ) * ζ ^ 2 - ((91481 / 12482) : ℂ) * ζ ^ 3 + ((246179 / 31205) : ℂ) * ζ ^ 4 - ((42099 / 6241) : ℂ) * ζ ^ 5 + ((364077 / 62410) : ℂ) * ζ ^ 6 + ((219444 / 31205) : ℂ) * ζ ^ 7 - ((750459 / 62410) : ℂ) * ζ ^ 8 - ((49913 / 12482) : ℂ) * ζ ^ 9 - ((122167 / 62410) : ℂ) * ζ ^ 10 - ((550479 / 62410) : ℂ) * ζ ^ 11 + ((650617 / 62410) : ℂ) * ζ ^ 12 + ((53750 / 6241) : ℂ) * ζ ^ 13 - ((16729 / 12482) : ℂ) * ζ ^ 14 - ((106837 / 62410) : ℂ) * ζ ^ 15 - ((273609 / 31205) : ℂ) * ζ ^ 16 - ((115029 / 12482) : ℂ) * ζ ^ 17 + ((387589 / 62410) : ℂ) * ζ ^ 18 + ((586559 / 62410) : ℂ) * ζ ^ 19 + ((172306 / 31205) : ℂ) * ζ ^ 20 + ((30378 / 6241) : ℂ) * ζ ^ 21 - ((57604 / 31205) : ℂ) * ζ ^ 22 - ((50046 / 31205) : ℂ) * ζ ^ 23 + ((27479 / 12482) : ℂ) * ζ ^ 24 + ((50567 / 12482) : ℂ) * ζ ^ 25 + ((72649 / 62410) : ℂ) * ζ ^ 26 - ((1371 / 62410) : ℂ) * ζ ^ 27 - ((2371 / 790) : ℂ) * ζ ^ 28 - ((12330 / 6241) : ℂ) * ζ ^ 29 - ((5803 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep08Coefficient01 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity01 :
    row18_reducedY76_combinationStep08Coefficient01 =
      row18_reducedY76_combinationStep07Coefficient01 +
        row18_reducedY76_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep08Coefficient01 row18_reducedY76_combinationStep07Coefficient01 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep08Coefficient02 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity02 :
    row18_reducedY76_combinationStep08Coefficient02 =
      row18_reducedY76_combinationStep07Coefficient02 +
        row18_reducedY76_combinationStep08Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep08Coefficient02 row18_reducedY76_combinationStep07Coefficient02 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 (-((98651 / 31205) : ℂ) - ((21124 / 31205) : ℂ) * ζ ^ 1 + ((38348 / 31205) : ℂ) * ζ ^ 2 - ((112727 / 31205) : ℂ) * ζ ^ 3 - ((68261 / 12482) : ℂ) * ζ ^ 4 + ((514169 / 62410) : ℂ) * ζ ^ 5 - ((234241 / 62410) : ℂ) * ζ ^ 6 + ((469391 / 62410) : ℂ) * ζ ^ 7 + ((170959 / 12482) : ℂ) * ζ ^ 8 - ((24719 / 62410) : ℂ) * ζ ^ 9 + ((77895 / 12482) : ℂ) * ζ ^ 10 + ((49282 / 31205) : ℂ) * ζ ^ 11 - ((58608 / 31205) : ℂ) * ζ ^ 12 - ((23276 / 31205) : ℂ) * ζ ^ 13 + ((86171 / 12482) : ℂ) * ζ ^ 14 + ((150583 / 62410) : ℂ) * ζ ^ 15 + ((66184 / 6241) : ℂ) * ζ ^ 16 + ((219987 / 31205) : ℂ) * ζ ^ 17 - ((120881 / 31205) : ℂ) * ζ ^ 18 - ((273679 / 62410) : ℂ) * ζ ^ 19 - ((466977 / 62410) : ℂ) * ζ ^ 20 - ((564399 / 62410) : ℂ) * ζ ^ 21 + ((14928 / 31205) : ℂ) * ζ ^ 22 - ((44191 / 62410) : ℂ) * ζ ^ 23 - ((252097 / 62410) : ℂ) * ζ ^ 24 - ((169219 / 62410) : ℂ) * ζ ^ 25 - ((512479 / 62410) : ℂ) * ζ ^ 26 - ((750733 / 62410) : ℂ) * ζ ^ 27 - ((816579 / 62410) : ℂ) * ζ ^ 28 - ((54084 / 6241) : ℂ) * ζ ^ 29 - ((34818 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep08Coefficient03 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity03 :
    row18_reducedY76_combinationStep08Coefficient03 =
      row18_reducedY76_combinationStep07Coefficient03 +
        row18_reducedY76_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep08Coefficient03 row18_reducedY76_combinationStep07Coefficient03 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep08Coefficient04 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity04 :
    row18_reducedY76_combinationStep08Coefficient04 =
      row18_reducedY76_combinationStep07Coefficient04 +
        row18_reducedY76_combinationStep08Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep08Coefficient04 row18_reducedY76_combinationStep07Coefficient04 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 (((436629 / 62410) : ℂ) + ((8195 / 6241) : ℂ) * ζ ^ 1 + ((439879 / 31205) : ℂ) * ζ ^ 2 + ((91481 / 12482) : ℂ) * ζ ^ 3 - ((246179 / 31205) : ℂ) * ζ ^ 4 + ((42099 / 6241) : ℂ) * ζ ^ 5 - ((364077 / 62410) : ℂ) * ζ ^ 6 - ((219444 / 31205) : ℂ) * ζ ^ 7 + ((750459 / 62410) : ℂ) * ζ ^ 8 + ((49913 / 12482) : ℂ) * ζ ^ 9 + ((122167 / 62410) : ℂ) * ζ ^ 10 + ((550479 / 62410) : ℂ) * ζ ^ 11 - ((650617 / 62410) : ℂ) * ζ ^ 12 - ((53750 / 6241) : ℂ) * ζ ^ 13 + ((16729 / 12482) : ℂ) * ζ ^ 14 + ((106837 / 62410) : ℂ) * ζ ^ 15 + ((273609 / 31205) : ℂ) * ζ ^ 16 + ((115029 / 12482) : ℂ) * ζ ^ 17 - ((387589 / 62410) : ℂ) * ζ ^ 18 - ((586559 / 62410) : ℂ) * ζ ^ 19 - ((172306 / 31205) : ℂ) * ζ ^ 20 - ((30378 / 6241) : ℂ) * ζ ^ 21 + ((57604 / 31205) : ℂ) * ζ ^ 22 + ((50046 / 31205) : ℂ) * ζ ^ 23 - ((27479 / 12482) : ℂ) * ζ ^ 24 - ((50567 / 12482) : ℂ) * ζ ^ 25 - ((72649 / 62410) : ℂ) * ζ ^ 26 + ((1371 / 62410) : ℂ) * ζ ^ 27 + ((2371 / 790) : ℂ) * ζ ^ 28 + ((12330 / 6241) : ℂ) * ζ ^ 29 + ((5803 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep08Coefficient05 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity05 :
    row18_reducedY76_combinationStep08Coefficient05 =
      row18_reducedY76_combinationStep07Coefficient05 +
        row18_reducedY76_combinationStep08Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY76_combinationStep08Coefficient05 row18_reducedY76_combinationStep07Coefficient05 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 (-((40949 / 12482) : ℂ) + ((343049 / 62410) : ℂ) * ζ ^ 1 + ((173861 / 31205) : ℂ) * ζ ^ 2 + ((16423 / 31205) : ℂ) * ζ ^ 3 + ((42245 / 12482) : ℂ) * ζ ^ 4 - ((187177 / 62410) : ℂ) * ζ ^ 5 - ((262049 / 62410) : ℂ) * ζ ^ 6 - ((422531 / 62410) : ℂ) * ζ ^ 7 + ((68157 / 12482) : ℂ) * ζ ^ 8 - ((57609 / 62410) : ℂ) * ζ ^ 9 + ((321413 / 62410) : ℂ) * ζ ^ 10 + ((58805 / 6241) : ℂ) * ζ ^ 11 + ((104939 / 12482) : ℂ) * ζ ^ 12 + ((23588 / 31205) : ℂ) * ζ ^ 13 + ((467137 / 62410) : ℂ) * ζ ^ 14 - ((179922 / 31205) : ℂ) * ζ ^ 15 - ((20125 / 6241) : ℂ) * ζ ^ 16 + ((22208 / 31205) : ℂ) * ζ ^ 17 - ((33851 / 12482) : ℂ) * ζ ^ 18 + ((78283 / 12482) : ℂ) * ζ ^ 19 + ((67618 / 6241) : ℂ) * ζ ^ 20 - ((65 / 6241) : ℂ) * ζ ^ 21 - ((236813 / 31205) : ℂ) * ζ ^ 22 - ((544473 / 62410) : ℂ) * ζ ^ 23 - ((79565 / 12482) : ℂ) * ζ ^ 24 + ((506144 / 31205) : ℂ) * ζ ^ 25 + ((535717 / 62410) : ℂ) * ζ ^ 26 - ((113592 / 31205) : ℂ) * ζ ^ 27 - ((127917 / 6241) : ℂ) * ζ ^ 28 - ((95643 / 6241) : ℂ) * ζ ^ 29 - ((74610 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY76_combinationStep08Coefficient06 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity06 :
    row18_reducedY76_combinationStep08Coefficient06 =
      row18_reducedY76_combinationStep07Coefficient06 +
        row18_reducedY76_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep08Coefficient06 row18_reducedY76_combinationStep07Coefficient06 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep08Coefficient07 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity07 :
    row18_reducedY76_combinationStep08Coefficient07 =
      row18_reducedY76_combinationStep07Coefficient07 +
        row18_reducedY76_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep08Coefficient07 row18_reducedY76_combinationStep07Coefficient07 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep08Coefficient08 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity08 :
    row18_reducedY76_combinationStep08Coefficient08 =
      row18_reducedY76_combinationStep07Coefficient08 +
        row18_reducedY76_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep08Coefficient08 row18_reducedY76_combinationStep07Coefficient08 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep08Coefficient09 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity09 :
    row18_reducedY76_combinationStep08Coefficient09 =
      row18_reducedY76_combinationStep07Coefficient09 +
        row18_reducedY76_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep08Coefficient09 row18_reducedY76_combinationStep07Coefficient09 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep08Coefficient10 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity10 :
    row18_reducedY76_combinationStep08Coefficient10 =
      row18_reducedY76_combinationStep07Coefficient10 +
        row18_reducedY76_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep08Coefficient10 row18_reducedY76_combinationStep07Coefficient10 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep08Coefficient11 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity11 :
    row18_reducedY76_combinationStep08Coefficient11 =
      row18_reducedY76_combinationStep07Coefficient11 +
        row18_reducedY76_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep08Coefficient11 row18_reducedY76_combinationStep07Coefficient11 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep08Coefficient12 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity12 :
    row18_reducedY76_combinationStep08Coefficient12 =
      row18_reducedY76_combinationStep07Coefficient12 +
        row18_reducedY76_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep08Coefficient12 row18_reducedY76_combinationStep07Coefficient12 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep08Coefficient13 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity13 :
    row18_reducedY76_combinationStep08Coefficient13 =
      row18_reducedY76_combinationStep07Coefficient13 +
        row18_reducedY76_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep08Coefficient13 row18_reducedY76_combinationStep07Coefficient13 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep08Coefficient14 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY76_combinationStep08CoefficientIdentity14 :
    row18_reducedY76_combinationStep08Coefficient14 =
      row18_reducedY76_combinationStep07Coefficient14 +
        row18_reducedY76_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep08Coefficient14 row18_reducedY76_combinationStep07Coefficient14 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY76_combinationStep08Coefficient15 : ℂ :=
  0

private theorem row18_reducedY76_combinationStep08CoefficientIdentity15 :
    row18_reducedY76_combinationStep08Coefficient15 =
      row18_reducedY76_combinationStep07Coefficient15 +
        row18_reducedY76_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY76_combinationStep08Coefficient15 row18_reducedY76_combinationStep07Coefficient15 row18_reducedY76_combinationStep08Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY76_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY76_combinationStep08Coefficient00) * Y 0 0
      + (row18_reducedY76_combinationStep08Coefficient01) * Y 0 1
      + (row18_reducedY76_combinationStep08Coefficient02) * Y 1 0
      + (row18_reducedY76_combinationStep08Coefficient03) * Y 1 1
      + (row18_reducedY76_combinationStep08Coefficient04) * Y 2 2
      + (row18_reducedY76_combinationStep08Coefficient05) * Y 2 3
      + (row18_reducedY76_combinationStep08Coefficient06) * Y 3 2
      + (row18_reducedY76_combinationStep08Coefficient07) * Y 3 3
      + (row18_reducedY76_combinationStep08Coefficient08) * Y 4 4
      + (row18_reducedY76_combinationStep08Coefficient09) * Y 4 5
      + (row18_reducedY76_combinationStep08Coefficient10) * Y 5 4
      + (row18_reducedY76_combinationStep08Coefficient11) * Y 5 5
      + (row18_reducedY76_combinationStep08Coefficient12) * Y 6 6
      + (row18_reducedY76_combinationStep08Coefficient13) * Y 6 7
      + (row18_reducedY76_combinationStep08Coefficient14) * Y 7 6
      + (row18_reducedY76_combinationStep08Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY76_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY76_combinationStep08CoefficientIdentity00,
      row18_reducedY76_combinationStep08CoefficientIdentity01,
      row18_reducedY76_combinationStep08CoefficientIdentity02,
      row18_reducedY76_combinationStep08CoefficientIdentity03,
      row18_reducedY76_combinationStep08CoefficientIdentity04,
      row18_reducedY76_combinationStep08CoefficientIdentity05,
      row18_reducedY76_combinationStep08CoefficientIdentity06,
      row18_reducedY76_combinationStep08CoefficientIdentity07,
      row18_reducedY76_combinationStep08CoefficientIdentity08,
      row18_reducedY76_combinationStep08CoefficientIdentity09,
      row18_reducedY76_combinationStep08CoefficientIdentity10,
      row18_reducedY76_combinationStep08CoefficientIdentity11,
      row18_reducedY76_combinationStep08CoefficientIdentity12,
      row18_reducedY76_combinationStep08CoefficientIdentity13,
      row18_reducedY76_combinationStep08CoefficientIdentity14,
      row18_reducedY76_combinationStep08CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY76_combinationStep08Multiplier * equation

theorem row18_reducedY76
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 7 6 = 0 := by
  have reduced :=
    row18_reducedY76_combinationStep08 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY76_combinationStep08Coefficient00,
      row18_reducedY76_combinationStep08Coefficient01,
      row18_reducedY76_combinationStep08Coefficient02,
      row18_reducedY76_combinationStep08Coefficient03,
      row18_reducedY76_combinationStep08Coefficient04,
      row18_reducedY76_combinationStep08Coefficient05,
      row18_reducedY76_combinationStep08Coefficient06,
      row18_reducedY76_combinationStep08Coefficient07,
      row18_reducedY76_combinationStep08Coefficient08,
      row18_reducedY76_combinationStep08Coefficient09,
      row18_reducedY76_combinationStep08Coefficient10,
      row18_reducedY76_combinationStep08Coefficient11,
      row18_reducedY76_combinationStep08Coefficient12,
      row18_reducedY76_combinationStep08Coefficient13,
      row18_reducedY76_combinationStep08Coefficient14,
      row18_reducedY76_combinationStep08Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
