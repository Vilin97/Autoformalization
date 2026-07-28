/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction09

/-!
# Ambient row 18 commutant reduction 10

This generated module checks the reduced relation `reducedY54` for
matrix coordinate (5, 4).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY54_combinationStep00Multiplier : ℂ :=
  (-((798 / 395) : ℂ) + ((2840 / 237) : ℂ) * ζ ^ 1 - ((17212 / 1185) : ℂ) * ζ ^ 2 + ((2456 / 237) : ℂ) * ζ ^ 5 - ((14818 / 1185) : ℂ) * ζ ^ 6 - ((14818 / 1185) : ℂ) * ζ ^ 8 + ((2456 / 237) : ℂ) * ζ ^ 9 - ((3436 / 237) : ℂ) * ζ ^ 11 - ((36524 / 1185) : ℂ) * ζ ^ 12 - ((2840 / 237) : ℂ) * ζ ^ 13 + ((1160 / 237) : ℂ) * ζ ^ 15 - ((2840 / 237) : ℂ) * ζ ^ 17 + ((4136 / 1185) : ℂ) * ζ ^ 18 - ((2648 / 237) : ℂ) * ζ ^ 21 + ((17212 / 1185) : ℂ) * ζ ^ 22 + ((10682 / 1185) : ℂ) * ζ ^ 24 + ((128 / 79) : ℂ) * ζ ^ 25 - ((1160 / 237) : ℂ) * ζ ^ 27 + ((14818 / 1185) : ℂ) * ζ ^ 28 + ((2840 / 237) : ℂ) * ζ ^ 29 + ((21706 / 1185) : ℂ) * ζ ^ 30 + ((3436 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY54_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep00CoefficientIdentity00 :
    row18_reducedY54_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep00Coefficient00 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep00Coefficient01 : ℂ :=
  (-((2386 / 237) : ℂ) - ((2851 / 237) : ℂ) * ζ ^ 1 - ((1262 / 237) : ℂ) * ζ ^ 2 + ((1387 / 474) : ℂ) * ζ ^ 3 - ((563 / 79) : ℂ) * ζ ^ 5 - ((1831 / 158) : ℂ) * ζ ^ 6 + ((3994 / 237) : ℂ) * ζ ^ 8 + ((8081 / 474) : ℂ) * ζ ^ 9 - ((563 / 79) : ℂ) * ζ ^ 11 + ((1997 / 237) : ℂ) * ζ ^ 12 + ((2851 / 237) : ℂ) * ζ ^ 13 - ((1919 / 158) : ℂ) * ζ ^ 15 + ((2851 / 237) : ℂ) * ζ ^ 17 + ((1831 / 158) : ℂ) * ζ ^ 18 + ((1991 / 474) : ℂ) * ζ ^ 21 + ((1262 / 237) : ℂ) * ζ ^ 22 - ((536 / 79) : ℂ) * ζ ^ 24 - ((1162 / 237) : ℂ) * ζ ^ 25 - ((1162 / 237) : ℂ) * ζ ^ 27 - ((3994 / 237) : ℂ) * ζ ^ 28 - ((2851 / 237) : ℂ) * ζ ^ 29 + ((563 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep00CoefficientIdentity01 :
    row18_reducedY54_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep00Coefficient01 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 (((892196 / 93615) : ℂ) + ((35923 / 2370) : ℂ) * ζ ^ 1 + ((142654 / 93615) : ℂ) * ζ ^ 2 - ((3961 / 2370) : ℂ) * ζ ^ 3 - ((1081528 / 93615) : ℂ) * ζ ^ 4 - ((5684 / 1185) : ℂ) * ζ ^ 5 + ((832711 / 187230) : ℂ) * ζ ^ 6 + ((1852 / 395) : ℂ) * ζ ^ 7 - ((774218 / 93615) : ℂ) * ζ ^ 8 - ((25811 / 2370) : ℂ) * ζ ^ 9 - ((584069 / 62410) : ℂ) * ζ ^ 10 + ((11129 / 2370) : ℂ) * ζ ^ 11 + ((334413 / 62410) : ℂ) * ζ ^ 12 + ((4721 / 1185) : ℂ) * ζ ^ 13 + ((451503 / 62410) : ℂ) * ζ ^ 14 + ((2763 / 395) : ℂ) * ζ ^ 15 + ((541927 / 187230) : ℂ) * ζ ^ 16 - ((13447 / 2370) : ℂ) * ζ ^ 17 - ((364649 / 62410) : ℂ) * ζ ^ 18 - ((5731 / 1185) : ℂ) * ζ ^ 19 + ((161636 / 93615) : ℂ) * ζ ^ 20 + ((89 / 79) : ℂ) * ζ ^ 21 + ((783431 / 187230) : ℂ) * ζ ^ 22 + ((691 / 474) : ℂ) * ζ ^ 23 + ((499399 / 187230) : ℂ) * ζ ^ 24 - ((587 / 2370) : ℂ) * ζ ^ 25 + ((826543 / 187230) : ℂ) * ζ ^ 26 + ((109 / 158) : ℂ) * ζ ^ 27 - ((112459 / 187230) : ℂ) * ζ ^ 28 - ((3203 / 1185) : ℂ) * ζ ^ 29 - ((58412 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep00Coefficient02 : ℂ :=
  (((637 / 79) : ℂ) + ((265 / 237) : ℂ) * ζ ^ 1 - ((2575 / 237) : ℂ) * ζ ^ 2 - ((1461 / 158) : ℂ) * ζ ^ 3 + ((1247 / 237) : ℂ) * ζ ^ 5 - ((461 / 79) : ℂ) * ζ ^ 6 - ((1043 / 158) : ℂ) * ζ ^ 8 + ((800 / 237) : ℂ) * ζ ^ 9 + ((5983 / 474) : ℂ) * ζ ^ 11 - ((1043 / 158) : ℂ) * ζ ^ 12 - ((265 / 237) : ℂ) * ζ ^ 13 + ((6347 / 474) : ℂ) * ζ ^ 15 - ((265 / 237) : ℂ) * ζ ^ 17 - ((1192 / 237) : ℂ) * ζ ^ 18 + ((3853 / 474) : ℂ) * ζ ^ 21 + ((2575 / 237) : ℂ) * ζ ^ 22 - ((982 / 237) : ℂ) * ζ ^ 25 - ((3853 / 474) : ℂ) * ζ ^ 27 + ((1043 / 158) : ℂ) * ζ ^ 28 + ((265 / 237) : ℂ) * ζ ^ 29 - ((461 / 158) : ℂ) * ζ ^ 30 - ((5983 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep00CoefficientIdentity02 :
    row18_reducedY54_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep00Coefficient02 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 (-((267974 / 31205) : ℂ) + ((357289 / 187230) : ℂ) * ζ ^ 1 + ((138016 / 18723) : ℂ) * ζ ^ 2 + ((125969 / 12482) : ℂ) * ζ ^ 3 + ((114484 / 18723) : ℂ) * ζ ^ 4 - ((1601 / 474) : ℂ) * ζ ^ 5 - ((165695 / 37446) : ℂ) * ζ ^ 6 - ((849496 / 93615) : ℂ) * ζ ^ 7 - ((156223 / 31205) : ℂ) * ζ ^ 8 + ((40142 / 31205) : ℂ) * ζ ^ 9 + ((131191 / 37446) : ℂ) * ζ ^ 10 - ((49278 / 31205) : ℂ) * ζ ^ 11 - ((379511 / 62410) : ℂ) * ζ ^ 12 - ((718624 / 93615) : ℂ) * ζ ^ 13 + ((47777 / 37446) : ℂ) * ζ ^ 14 + ((144873 / 31205) : ℂ) * ζ ^ 15 + ((628639 / 93615) : ℂ) * ζ ^ 16 + ((468439 / 93615) : ℂ) * ζ ^ 17 + ((109549 / 37446) : ℂ) * ζ ^ 18 - ((9461 / 187230) : ℂ) * ζ ^ 19 - ((965207 / 187230) : ℂ) * ζ ^ 20 - ((373559 / 62410) : ℂ) * ζ ^ 21 - ((37961 / 12482) : ℂ) * ζ ^ 22 - ((20179 / 37446) : ℂ) * ζ ^ 23 + ((30196 / 6241) : ℂ) * ζ ^ 24 + ((1165237 / 187230) : ℂ) * ζ ^ 25 + ((85549 / 18723) : ℂ) * ζ ^ 26 + ((60374 / 31205) : ℂ) * ζ ^ 27 - ((287861 / 187230) : ℂ) * ζ ^ 28 - ((26315 / 12482) : ℂ) * ζ ^ 29 - ((4295 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep00CoefficientIdentity03 :
    row18_reducedY54_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep00Coefficient03 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep00CoefficientIdentity04 :
    row18_reducedY54_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep00Coefficient04 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep00CoefficientIdentity05 :
    row18_reducedY54_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep00Coefficient05 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep00CoefficientIdentity06 :
    row18_reducedY54_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep00Coefficient06 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep00CoefficientIdentity07 :
    row18_reducedY54_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep00Coefficient07 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep00CoefficientIdentity08 :
    row18_reducedY54_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep00Coefficient08 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep00CoefficientIdentity09 :
    row18_reducedY54_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep00Coefficient09 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep00CoefficientIdentity10 :
    row18_reducedY54_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep00Coefficient10 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep00CoefficientIdentity11 :
    row18_reducedY54_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep00Coefficient11 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep00CoefficientIdentity12 :
    row18_reducedY54_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep00Coefficient12 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep00CoefficientIdentity13 :
    row18_reducedY54_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep00Coefficient13 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep00CoefficientIdentity14 :
    row18_reducedY54_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep00Coefficient14 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep00CoefficientIdentity15 :
    row18_reducedY54_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY54_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep00Coefficient15 row18_reducedY54_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY54_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY54_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY54_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY54_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY54_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY54_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY54_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY54_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY54_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY54_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY54_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY54_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY54_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY54_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY54_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY54_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY54_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY54_combinationStep00CoefficientIdentity00,
      row18_reducedY54_combinationStep00CoefficientIdentity01,
      row18_reducedY54_combinationStep00CoefficientIdentity02,
      row18_reducedY54_combinationStep00CoefficientIdentity03,
      row18_reducedY54_combinationStep00CoefficientIdentity04,
      row18_reducedY54_combinationStep00CoefficientIdentity05,
      row18_reducedY54_combinationStep00CoefficientIdentity06,
      row18_reducedY54_combinationStep00CoefficientIdentity07,
      row18_reducedY54_combinationStep00CoefficientIdentity08,
      row18_reducedY54_combinationStep00CoefficientIdentity09,
      row18_reducedY54_combinationStep00CoefficientIdentity10,
      row18_reducedY54_combinationStep00CoefficientIdentity11,
      row18_reducedY54_combinationStep00CoefficientIdentity12,
      row18_reducedY54_combinationStep00CoefficientIdentity13,
      row18_reducedY54_combinationStep00CoefficientIdentity14,
      row18_reducedY54_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY54_combinationStep00Multiplier * equation

private def row18_reducedY54_combinationStep01Multiplier : ℂ :=
  (-((3190 / 237) : ℂ) - ((14252 / 1185) : ℂ) * ζ ^ 1 - ((1436 / 237) : ℂ) * ζ ^ 2 + ((5228 / 1185) : ℂ) * ζ ^ 3 + ((7184 / 1185) : ℂ) * ζ ^ 5 + ((356 / 237) : ℂ) * ζ ^ 6 + ((2474 / 1185) : ℂ) * ζ ^ 9 - ((7184 / 1185) : ℂ) * ζ ^ 11 + ((974 / 79) : ℂ) * ζ ^ 12 + ((14252 / 1185) : ℂ) * ζ ^ 13 - ((18962 / 1185) : ℂ) * ζ ^ 15 + ((14252 / 1185) : ℂ) * ζ ^ 17 + ((1076 / 79) : ℂ) * ζ ^ 18 - ((652 / 395) : ℂ) * ζ ^ 21 + ((1436 / 237) : ℂ) * ζ ^ 22 - ((3190 / 237) : ℂ) * ζ ^ 24 - ((21436 / 1185) : ℂ) * ζ ^ 25 + ((21436 / 1185) : ℂ) * ζ ^ 27 - ((14252 / 1185) : ℂ) * ζ ^ 29 - ((2872 / 237) : ℂ) * ζ ^ 30 + ((7184 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY54_combinationStep01Coefficient00 : ℂ :=
  (((3253 / 474) : ℂ) + ((1636 / 237) : ℂ) * ζ ^ 1 + ((457 / 474) : ℂ) * ζ ^ 2 - ((1390 / 237) : ℂ) * ζ ^ 3 + ((1636 / 237) : ℂ) * ζ ^ 5 + ((1855 / 237) : ℂ) * ζ ^ 6 - ((1855 / 237) : ℂ) * ζ ^ 8 - ((1636 / 237) : ℂ) * ζ ^ 9 + ((695 / 237) : ℂ) * ζ ^ 11 - ((1373 / 237) : ℂ) * ζ ^ 12 - ((1636 / 237) : ℂ) * ζ ^ 13 + ((576 / 79) : ℂ) * ζ ^ 15 - ((1636 / 237) : ℂ) * ζ ^ 17 - ((3467 / 474) : ℂ) * ζ ^ 18 - ((121 / 474) : ℂ) * ζ ^ 21 - ((457 / 474) : ℂ) * ζ ^ 22 + ((81 / 158) : ℂ) * ζ ^ 24 + ((338 / 237) : ℂ) * ζ ^ 27 + ((1855 / 237) : ℂ) * ζ ^ 28 + ((1636 / 237) : ℂ) * ζ ^ 29 + ((482 / 237) : ℂ) * ζ ^ 30 - ((695 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep01CoefficientIdentity00 :
    row18_reducedY54_combinationStep01Coefficient00 =
      row18_reducedY54_combinationStep00Coefficient00 +
        row18_reducedY54_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep01Coefficient00 row18_reducedY54_combinationStep00Coefficient00 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 (-((126197 / 37446) : ℂ) - ((604433 / 187230) : ℂ) * ζ ^ 1 + ((477653 / 187230) : ℂ) * ζ ^ 2 + ((163551 / 31205) : ℂ) * ζ ^ 3 + ((548039 / 187230) : ℂ) * ζ ^ 4 - ((14653 / 2370) : ℂ) * ζ ^ 5 - ((956159 / 93615) : ℂ) * ζ ^ 6 - ((518309 / 93615) : ℂ) * ζ ^ 7 + ((87729 / 31205) : ℂ) * ζ ^ 8 + ((1316363 / 187230) : ℂ) * ζ ^ 9 + ((1149923 / 187230) : ℂ) * ζ ^ 10 + ((237987 / 62410) : ℂ) * ζ ^ 11 - ((244102 / 93615) : ℂ) * ζ ^ 12 - ((590068 / 93615) : ℂ) * ζ ^ 13 - ((496903 / 93615) : ℂ) * ζ ^ 14 - ((256496 / 93615) : ℂ) * ζ ^ 15 + ((508613 / 187230) : ℂ) * ζ ^ 16 + ((221489 / 93615) : ℂ) * ζ ^ 17 + ((125977 / 62410) : ℂ) * ζ ^ 18 + ((59968 / 93615) : ℂ) * ζ ^ 19 + ((285211 / 187230) : ℂ) * ζ ^ 20 + ((333247 / 187230) : ℂ) * ζ ^ 21 - ((483631 / 187230) : ℂ) * ζ ^ 22 - ((773423 / 187230) : ℂ) * ζ ^ 23 + ((53768 / 93615) : ℂ) * ζ ^ 24 + ((421244 / 93615) : ℂ) * ζ ^ 25 + ((291814 / 93615) : ℂ) * ζ ^ 26 - ((53029 / 31205) : ℂ) * ζ ^ 27 - ((173723 / 93615) : ℂ) * ζ ^ 28 - ((1786 / 31205) : ℂ) * ζ ^ 29 + ((1796 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep01Coefficient01 : ℂ :=
  (-((774 / 79) : ℂ) - ((950 / 237) : ℂ) * ζ ^ 1 + ((1969 / 237) : ℂ) * ζ ^ 2 + ((3155 / 237) : ℂ) * ζ ^ 3 - ((1250 / 237) : ℂ) * ζ ^ 5 - ((827 / 158) : ℂ) * ζ ^ 6 + ((1369 / 237) : ℂ) * ζ ^ 8 + ((2749 / 474) : ℂ) * ζ ^ 9 - ((1250 / 237) : ℂ) * ζ ^ 11 + ((1369 / 474) : ℂ) * ζ ^ 12 + ((950 / 237) : ℂ) * ζ ^ 13 - ((3349 / 474) : ℂ) * ζ ^ 15 + ((950 / 237) : ℂ) * ζ ^ 17 + ((827 / 158) : ℂ) * ζ ^ 18 - ((635 / 79) : ℂ) * ζ ^ 21 - ((1969 / 237) : ℂ) * ζ ^ 22 + ((953 / 237) : ℂ) * ζ ^ 24 + ((100 / 79) : ℂ) * ζ ^ 25 + ((100 / 79) : ℂ) * ζ ^ 27 - ((1369 / 237) : ℂ) * ζ ^ 28 - ((950 / 237) : ℂ) * ζ ^ 29 + ((1250 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep01CoefficientIdentity01 :
    row18_reducedY54_combinationStep01Coefficient01 =
      row18_reducedY54_combinationStep00Coefficient01 +
        row18_reducedY54_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep01Coefficient01 row18_reducedY54_combinationStep00Coefficient01 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 (((20464 / 18723) : ℂ) - ((549154 / 93615) : ℂ) * ζ ^ 1 - ((949013 / 187230) : ℂ) * ζ ^ 2 - ((80543 / 93615) : ℂ) * ζ ^ 3 + ((435916 / 93615) : ℂ) * ζ ^ 4 + ((1052 / 1185) : ℂ) * ζ ^ 5 - ((815069 / 187230) : ℂ) * ζ ^ 6 - ((297389 / 93615) : ℂ) * ζ ^ 7 + ((78752 / 18723) : ℂ) * ζ ^ 8 + ((926653 / 187230) : ℂ) * ζ ^ 9 + ((147293 / 187230) : ℂ) * ζ ^ 10 + ((25017 / 62410) : ℂ) * ζ ^ 11 + ((130277 / 93615) : ℂ) * ζ ^ 12 - ((714427 / 187230) : ℂ) * ζ ^ 13 - ((146173 / 12482) : ℂ) * ζ ^ 14 - ((2592829 / 187230) : ℂ) * ζ ^ 15 + ((101798 / 93615) : ℂ) * ζ ^ 16 + ((477403 / 31205) : ℂ) * ζ ^ 17 + ((494216 / 93615) : ℂ) * ζ ^ 18 - ((823163 / 187230) : ℂ) * ζ ^ 19 - ((231186 / 31205) : ℂ) * ζ ^ 20 + ((103733 / 31205) : ℂ) * ζ ^ 21 + ((55669 / 93615) : ℂ) * ζ ^ 22 - ((58678 / 31205) : ℂ) * ζ ^ 23 + ((2571 / 6241) : ℂ) * ζ ^ 24 + ((139686 / 31205) : ℂ) * ζ ^ 25 + ((42014 / 31205) : ℂ) * ζ ^ 26 - ((28084 / 93615) : ℂ) * ζ ^ 27 - ((225436 / 93615) : ℂ) * ζ ^ 28 - ((57416 / 93615) : ℂ) * ζ ^ 29 + ((50288 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep01Coefficient02 : ℂ :=
  (((637 / 79) : ℂ) + ((265 / 237) : ℂ) * ζ ^ 1 - ((2575 / 237) : ℂ) * ζ ^ 2 - ((1461 / 158) : ℂ) * ζ ^ 3 + ((1247 / 237) : ℂ) * ζ ^ 5 - ((461 / 79) : ℂ) * ζ ^ 6 - ((1043 / 158) : ℂ) * ζ ^ 8 + ((800 / 237) : ℂ) * ζ ^ 9 + ((5983 / 474) : ℂ) * ζ ^ 11 - ((1043 / 158) : ℂ) * ζ ^ 12 - ((265 / 237) : ℂ) * ζ ^ 13 + ((6347 / 474) : ℂ) * ζ ^ 15 - ((265 / 237) : ℂ) * ζ ^ 17 - ((1192 / 237) : ℂ) * ζ ^ 18 + ((3853 / 474) : ℂ) * ζ ^ 21 + ((2575 / 237) : ℂ) * ζ ^ 22 - ((982 / 237) : ℂ) * ζ ^ 25 - ((3853 / 474) : ℂ) * ζ ^ 27 + ((1043 / 158) : ℂ) * ζ ^ 28 + ((265 / 237) : ℂ) * ζ ^ 29 - ((461 / 158) : ℂ) * ζ ^ 30 - ((5983 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep01CoefficientIdentity02 :
    row18_reducedY54_combinationStep01Coefficient02 =
      row18_reducedY54_combinationStep00Coefficient02 +
        row18_reducedY54_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep01Coefficient02 row18_reducedY54_combinationStep00Coefficient02 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep01Coefficient03 : ℂ :=
  (-((3253 / 474) : ℂ) - ((1636 / 237) : ℂ) * ζ ^ 1 - ((457 / 474) : ℂ) * ζ ^ 2 + ((1390 / 237) : ℂ) * ζ ^ 3 - ((1636 / 237) : ℂ) * ζ ^ 5 - ((1855 / 237) : ℂ) * ζ ^ 6 + ((1855 / 237) : ℂ) * ζ ^ 8 + ((1636 / 237) : ℂ) * ζ ^ 9 - ((695 / 237) : ℂ) * ζ ^ 11 + ((1373 / 237) : ℂ) * ζ ^ 12 + ((1636 / 237) : ℂ) * ζ ^ 13 - ((576 / 79) : ℂ) * ζ ^ 15 + ((1636 / 237) : ℂ) * ζ ^ 17 + ((3467 / 474) : ℂ) * ζ ^ 18 + ((121 / 474) : ℂ) * ζ ^ 21 + ((457 / 474) : ℂ) * ζ ^ 22 - ((81 / 158) : ℂ) * ζ ^ 24 - ((338 / 237) : ℂ) * ζ ^ 27 - ((1855 / 237) : ℂ) * ζ ^ 28 - ((1636 / 237) : ℂ) * ζ ^ 29 - ((482 / 237) : ℂ) * ζ ^ 30 + ((695 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep01CoefficientIdentity03 :
    row18_reducedY54_combinationStep01Coefficient03 =
      row18_reducedY54_combinationStep00Coefficient03 +
        row18_reducedY54_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep01Coefficient03 row18_reducedY54_combinationStep00Coefficient03 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 (((126197 / 37446) : ℂ) + ((604433 / 187230) : ℂ) * ζ ^ 1 - ((477653 / 187230) : ℂ) * ζ ^ 2 - ((163551 / 31205) : ℂ) * ζ ^ 3 - ((548039 / 187230) : ℂ) * ζ ^ 4 + ((14653 / 2370) : ℂ) * ζ ^ 5 + ((956159 / 93615) : ℂ) * ζ ^ 6 + ((518309 / 93615) : ℂ) * ζ ^ 7 - ((87729 / 31205) : ℂ) * ζ ^ 8 - ((1316363 / 187230) : ℂ) * ζ ^ 9 - ((1149923 / 187230) : ℂ) * ζ ^ 10 - ((237987 / 62410) : ℂ) * ζ ^ 11 + ((244102 / 93615) : ℂ) * ζ ^ 12 + ((590068 / 93615) : ℂ) * ζ ^ 13 + ((496903 / 93615) : ℂ) * ζ ^ 14 + ((256496 / 93615) : ℂ) * ζ ^ 15 - ((508613 / 187230) : ℂ) * ζ ^ 16 - ((221489 / 93615) : ℂ) * ζ ^ 17 - ((125977 / 62410) : ℂ) * ζ ^ 18 - ((59968 / 93615) : ℂ) * ζ ^ 19 - ((285211 / 187230) : ℂ) * ζ ^ 20 - ((333247 / 187230) : ℂ) * ζ ^ 21 + ((483631 / 187230) : ℂ) * ζ ^ 22 + ((773423 / 187230) : ℂ) * ζ ^ 23 - ((53768 / 93615) : ℂ) * ζ ^ 24 - ((421244 / 93615) : ℂ) * ζ ^ 25 - ((291814 / 93615) : ℂ) * ζ ^ 26 + ((53029 / 31205) : ℂ) * ζ ^ 27 + ((173723 / 93615) : ℂ) * ζ ^ 28 + ((1786 / 31205) : ℂ) * ζ ^ 29 - ((1796 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep01CoefficientIdentity04 :
    row18_reducedY54_combinationStep01Coefficient04 =
      row18_reducedY54_combinationStep00Coefficient04 +
        row18_reducedY54_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep01Coefficient04 row18_reducedY54_combinationStep00Coefficient04 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep01CoefficientIdentity05 :
    row18_reducedY54_combinationStep01Coefficient05 =
      row18_reducedY54_combinationStep00Coefficient05 +
        row18_reducedY54_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep01Coefficient05 row18_reducedY54_combinationStep00Coefficient05 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep01CoefficientIdentity06 :
    row18_reducedY54_combinationStep01Coefficient06 =
      row18_reducedY54_combinationStep00Coefficient06 +
        row18_reducedY54_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep01Coefficient06 row18_reducedY54_combinationStep00Coefficient06 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep01CoefficientIdentity07 :
    row18_reducedY54_combinationStep01Coefficient07 =
      row18_reducedY54_combinationStep00Coefficient07 +
        row18_reducedY54_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep01Coefficient07 row18_reducedY54_combinationStep00Coefficient07 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep01CoefficientIdentity08 :
    row18_reducedY54_combinationStep01Coefficient08 =
      row18_reducedY54_combinationStep00Coefficient08 +
        row18_reducedY54_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep01Coefficient08 row18_reducedY54_combinationStep00Coefficient08 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep01CoefficientIdentity09 :
    row18_reducedY54_combinationStep01Coefficient09 =
      row18_reducedY54_combinationStep00Coefficient09 +
        row18_reducedY54_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep01Coefficient09 row18_reducedY54_combinationStep00Coefficient09 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep01CoefficientIdentity10 :
    row18_reducedY54_combinationStep01Coefficient10 =
      row18_reducedY54_combinationStep00Coefficient10 +
        row18_reducedY54_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep01Coefficient10 row18_reducedY54_combinationStep00Coefficient10 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep01CoefficientIdentity11 :
    row18_reducedY54_combinationStep01Coefficient11 =
      row18_reducedY54_combinationStep00Coefficient11 +
        row18_reducedY54_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep01Coefficient11 row18_reducedY54_combinationStep00Coefficient11 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep01CoefficientIdentity12 :
    row18_reducedY54_combinationStep01Coefficient12 =
      row18_reducedY54_combinationStep00Coefficient12 +
        row18_reducedY54_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep01Coefficient12 row18_reducedY54_combinationStep00Coefficient12 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep01CoefficientIdentity13 :
    row18_reducedY54_combinationStep01Coefficient13 =
      row18_reducedY54_combinationStep00Coefficient13 +
        row18_reducedY54_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep01Coefficient13 row18_reducedY54_combinationStep00Coefficient13 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep01CoefficientIdentity14 :
    row18_reducedY54_combinationStep01Coefficient14 =
      row18_reducedY54_combinationStep00Coefficient14 +
        row18_reducedY54_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep01Coefficient14 row18_reducedY54_combinationStep00Coefficient14 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep01CoefficientIdentity15 :
    row18_reducedY54_combinationStep01Coefficient15 =
      row18_reducedY54_combinationStep00Coefficient15 +
        row18_reducedY54_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep01Coefficient15 row18_reducedY54_combinationStep00Coefficient15 row18_reducedY54_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY54_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY54_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY54_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY54_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY54_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY54_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY54_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY54_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY54_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY54_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY54_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY54_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY54_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY54_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY54_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY54_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY54_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY54_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY54_combinationStep01CoefficientIdentity00,
      row18_reducedY54_combinationStep01CoefficientIdentity01,
      row18_reducedY54_combinationStep01CoefficientIdentity02,
      row18_reducedY54_combinationStep01CoefficientIdentity03,
      row18_reducedY54_combinationStep01CoefficientIdentity04,
      row18_reducedY54_combinationStep01CoefficientIdentity05,
      row18_reducedY54_combinationStep01CoefficientIdentity06,
      row18_reducedY54_combinationStep01CoefficientIdentity07,
      row18_reducedY54_combinationStep01CoefficientIdentity08,
      row18_reducedY54_combinationStep01CoefficientIdentity09,
      row18_reducedY54_combinationStep01CoefficientIdentity10,
      row18_reducedY54_combinationStep01CoefficientIdentity11,
      row18_reducedY54_combinationStep01CoefficientIdentity12,
      row18_reducedY54_combinationStep01CoefficientIdentity13,
      row18_reducedY54_combinationStep01CoefficientIdentity14,
      row18_reducedY54_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY54_combinationStep01Multiplier * equation

private def row18_reducedY54_combinationStep02Multiplier : ℂ :=
  (-((26512 / 1185) : ℂ) - ((3980 / 237) : ℂ) * ζ ^ 1 + ((7816 / 1185) : ℂ) * ζ ^ 2 + ((6664 / 237) : ℂ) * ζ ^ 3 - ((3980 / 237) : ℂ) * ζ ^ 5 - ((6232 / 395) : ℂ) * ζ ^ 6 + ((6232 / 395) : ℂ) * ζ ^ 8 + ((3980 / 237) : ℂ) * ζ ^ 9 - ((3332 / 237) : ℂ) * ζ ^ 11 + ((14918 / 1185) : ℂ) * ζ ^ 12 + ((3980 / 237) : ℂ) * ζ ^ 13 - ((5282 / 237) : ℂ) * ζ ^ 15 + ((3980 / 237) : ℂ) * ζ ^ 17 + ((24172 / 1185) : ℂ) * ζ ^ 18 - ((648 / 79) : ℂ) * ζ ^ 21 - ((7816 / 1185) : ℂ) * ζ ^ 22 + ((5476 / 1185) : ℂ) * ζ ^ 24 + ((1382 / 237) : ℂ) * ζ ^ 27 - ((6232 / 395) : ℂ) * ζ ^ 28 - ((3980 / 237) : ℂ) * ζ ^ 29 - ((3778 / 1185) : ℂ) * ζ ^ 30 + ((3332 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY54_combinationStep02Coefficient00 : ℂ :=
  (((6913 / 2370) : ℂ) + ((2221 / 474) : ℂ) * ζ ^ 1 + ((4721 / 2370) : ℂ) * ζ ^ 2 - ((3124 / 1185) : ℂ) * ζ ^ 3 + ((2221 / 474) : ℂ) * ζ ^ 5 + ((1939 / 395) : ℂ) * ζ ^ 6 - ((1939 / 395) : ℂ) * ζ ^ 8 - ((2221 / 474) : ℂ) * ζ ^ 9 + ((1562 / 1185) : ℂ) * ζ ^ 11 - ((3029 / 790) : ℂ) * ζ ^ 12 - ((2221 / 474) : ℂ) * ζ ^ 13 + ((9497 / 2370) : ℂ) * ζ ^ 15 - ((2221 / 474) : ℂ) * ζ ^ 17 - ((1923 / 395) : ℂ) * ζ ^ 18 - ((530 / 237) : ℂ) * ζ ^ 21 - ((4721 / 2370) : ℂ) * ζ ^ 22 + ((16 / 395) : ℂ) * ζ ^ 24 + ((1083 / 790) : ℂ) * ζ ^ 27 + ((1939 / 395) : ℂ) * ζ ^ 28 + ((2221 / 474) : ℂ) * ζ ^ 29 + ((849 / 790) : ℂ) * ζ ^ 30 - ((1562 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep02CoefficientIdentity00 :
    row18_reducedY54_combinationStep02Coefficient00 =
      row18_reducedY54_combinationStep01Coefficient00 +
        row18_reducedY54_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep02Coefficient00 row18_reducedY54_combinationStep01Coefficient00 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 (((89788 / 18723) : ℂ) + ((388729 / 187230) : ℂ) * ζ ^ 1 + ((77797 / 18723) : ℂ) * ζ ^ 2 + ((9633 / 31205) : ℂ) * ζ ^ 3 - ((106670 / 18723) : ℂ) * ζ ^ 4 - ((168434 / 31205) : ℂ) * ζ ^ 5 + ((208841 / 93615) : ℂ) * ζ ^ 6 + ((464636 / 93615) : ℂ) * ζ ^ 7 + ((46214 / 31205) : ℂ) * ζ ^ 8 - ((162107 / 187230) : ℂ) * ζ ^ 9 - ((109597 / 31205) : ℂ) * ζ ^ 10 - ((68156 / 93615) : ℂ) * ζ ^ 11 - ((132883 / 187230) : ℂ) * ζ ^ 12 + ((3897 / 31205) : ℂ) * ζ ^ 13 + ((211351 / 187230) : ℂ) * ζ ^ 14 + ((755 / 158) : ℂ) * ζ ^ 15 + ((299299 / 93615) : ℂ) * ζ ^ 16 + ((53459 / 93615) : ℂ) * ζ ^ 17 - ((3604 / 31205) : ℂ) * ζ ^ 18 - ((774041 / 187230) : ℂ) * ζ ^ 19 - ((128288 / 31205) : ℂ) * ζ ^ 20 + ((15541 / 37446) : ℂ) * ζ ^ 21 - ((221833 / 93615) : ℂ) * ζ ^ 22 + ((3869 / 31205) : ℂ) * ζ ^ 23 + ((167727 / 62410) : ℂ) * ζ ^ 24 + ((108437 / 62410) : ℂ) * ζ ^ 25 + ((146273 / 187230) : ℂ) * ζ ^ 26 - ((94667 / 62410) : ℂ) * ζ ^ 27 - ((8723 / 93615) : ℂ) * ζ ^ 28 - ((26621 / 31205) : ℂ) * ζ ^ 29 + ((11662 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep02Coefficient01 : ℂ :=
  (-((2456 / 237) : ℂ) - ((773 / 158) : ℂ) * ζ ^ 1 + ((1342 / 237) : ℂ) * ζ ^ 2 + ((3608 / 237) : ℂ) * ζ ^ 3 - ((2077 / 237) : ℂ) * ζ ^ 5 - ((1846 / 237) : ℂ) * ζ ^ 6 + ((908 / 237) : ℂ) * ζ ^ 8 + ((2587 / 474) : ℂ) * ζ ^ 9 - ((2077 / 237) : ℂ) * ζ ^ 11 + ((454 / 237) : ℂ) * ζ ^ 12 + ((773 / 158) : ℂ) * ζ ^ 13 - ((737 / 79) : ℂ) * ζ ^ 15 + ((773 / 158) : ℂ) * ζ ^ 17 + ((1846 / 237) : ℂ) * ζ ^ 18 - ((1531 / 237) : ℂ) * ζ ^ 21 - ((1342 / 237) : ℂ) * ζ ^ 22 + ((516 / 79) : ℂ) * ζ ^ 24 + ((1835 / 474) : ℂ) * ζ ^ 25 + ((1835 / 474) : ℂ) * ζ ^ 27 - ((908 / 237) : ℂ) * ζ ^ 28 - ((773 / 158) : ℂ) * ζ ^ 29 + ((2077 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep02CoefficientIdentity01 :
    row18_reducedY54_combinationStep02Coefficient01 =
      row18_reducedY54_combinationStep01Coefficient01 +
        row18_reducedY54_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep02Coefficient01 row18_reducedY54_combinationStep01Coefficient01 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 (-((404402 / 93615) : ℂ) + ((40381 / 12482) : ℂ) * ζ ^ 1 + ((745714 / 93615) : ℂ) * ζ ^ 2 + ((4214 / 31205) : ℂ) * ζ ^ 3 - ((415412 / 93615) : ℂ) * ζ ^ 4 + ((739373 / 187230) : ℂ) * ζ ^ 5 - ((567403 / 187230) : ℂ) * ζ ^ 6 - ((214267 / 93615) : ℂ) * ζ ^ 7 + ((709943 / 93615) : ℂ) * ζ ^ 8 - ((77641 / 187230) : ℂ) * ζ ^ 9 - ((499039 / 187230) : ℂ) * ζ ^ 10 + ((80 / 237) : ℂ) * ζ ^ 11 + ((284638 / 93615) : ℂ) * ζ ^ 12 - ((230914 / 93615) : ℂ) * ζ ^ 13 - ((197033 / 93615) : ℂ) * ζ ^ 14 - ((14879 / 31205) : ℂ) * ζ ^ 15 + ((875677 / 187230) : ℂ) * ζ ^ 16 + ((35687 / 62410) : ℂ) * ζ ^ 17 - ((622061 / 93615) : ℂ) * ζ ^ 18 - ((27259 / 6241) : ℂ) * ζ ^ 19 + ((253177 / 93615) : ℂ) * ζ ^ 20 - ((435743 / 62410) : ℂ) * ζ ^ 21 - ((8206 / 6241) : ℂ) * ζ ^ 22 + ((1070089 / 187230) : ℂ) * ζ ^ 23 - ((163013 / 187230) : ℂ) * ζ ^ 24 - ((47065 / 37446) : ℂ) * ζ ^ 25 + ((65627 / 62410) : ℂ) * ζ ^ 26 + ((151481 / 187230) : ℂ) * ζ ^ 27 - ((469703 / 93615) : ℂ) * ζ ^ 28 + ((425263 / 187230) : ℂ) * ζ ^ 29 + ((10829 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep02Coefficient02 : ℂ :=
  (((637 / 79) : ℂ) + ((265 / 237) : ℂ) * ζ ^ 1 - ((2575 / 237) : ℂ) * ζ ^ 2 - ((1461 / 158) : ℂ) * ζ ^ 3 + ((1247 / 237) : ℂ) * ζ ^ 5 - ((461 / 79) : ℂ) * ζ ^ 6 - ((1043 / 158) : ℂ) * ζ ^ 8 + ((800 / 237) : ℂ) * ζ ^ 9 + ((5983 / 474) : ℂ) * ζ ^ 11 - ((1043 / 158) : ℂ) * ζ ^ 12 - ((265 / 237) : ℂ) * ζ ^ 13 + ((6347 / 474) : ℂ) * ζ ^ 15 - ((265 / 237) : ℂ) * ζ ^ 17 - ((1192 / 237) : ℂ) * ζ ^ 18 + ((3853 / 474) : ℂ) * ζ ^ 21 + ((2575 / 237) : ℂ) * ζ ^ 22 - ((982 / 237) : ℂ) * ζ ^ 25 - ((3853 / 474) : ℂ) * ζ ^ 27 + ((1043 / 158) : ℂ) * ζ ^ 28 + ((265 / 237) : ℂ) * ζ ^ 29 - ((461 / 158) : ℂ) * ζ ^ 30 - ((5983 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep02CoefficientIdentity02 :
    row18_reducedY54_combinationStep02Coefficient02 =
      row18_reducedY54_combinationStep01Coefficient02 +
        row18_reducedY54_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep02Coefficient02 row18_reducedY54_combinationStep01Coefficient02 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep02Coefficient03 : ℂ :=
  (-((3253 / 474) : ℂ) - ((1636 / 237) : ℂ) * ζ ^ 1 - ((457 / 474) : ℂ) * ζ ^ 2 + ((1390 / 237) : ℂ) * ζ ^ 3 - ((1636 / 237) : ℂ) * ζ ^ 5 - ((1855 / 237) : ℂ) * ζ ^ 6 + ((1855 / 237) : ℂ) * ζ ^ 8 + ((1636 / 237) : ℂ) * ζ ^ 9 - ((695 / 237) : ℂ) * ζ ^ 11 + ((1373 / 237) : ℂ) * ζ ^ 12 + ((1636 / 237) : ℂ) * ζ ^ 13 - ((576 / 79) : ℂ) * ζ ^ 15 + ((1636 / 237) : ℂ) * ζ ^ 17 + ((3467 / 474) : ℂ) * ζ ^ 18 + ((121 / 474) : ℂ) * ζ ^ 21 + ((457 / 474) : ℂ) * ζ ^ 22 - ((81 / 158) : ℂ) * ζ ^ 24 - ((338 / 237) : ℂ) * ζ ^ 27 - ((1855 / 237) : ℂ) * ζ ^ 28 - ((1636 / 237) : ℂ) * ζ ^ 29 - ((482 / 237) : ℂ) * ζ ^ 30 + ((695 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep02CoefficientIdentity03 :
    row18_reducedY54_combinationStep02Coefficient03 =
      row18_reducedY54_combinationStep01Coefficient03 +
        row18_reducedY54_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep02Coefficient03 row18_reducedY54_combinationStep01Coefficient03 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep02Coefficient04 : ℂ :=
  (((4676 / 1185) : ℂ) + ((1051 / 474) : ℂ) * ζ ^ 1 - ((406 / 395) : ℂ) * ζ ^ 2 - ((3826 / 1185) : ℂ) * ζ ^ 3 + ((1051 / 474) : ℂ) * ζ ^ 5 + ((3458 / 1185) : ℂ) * ζ ^ 6 - ((3458 / 1185) : ℂ) * ζ ^ 8 - ((1051 / 474) : ℂ) * ζ ^ 9 + ((1913 / 1185) : ℂ) * ζ ^ 11 - ((4643 / 2370) : ℂ) * ζ ^ 12 - ((1051 / 474) : ℂ) * ζ ^ 13 + ((7783 / 2370) : ℂ) * ζ ^ 15 - ((1051 / 474) : ℂ) * ζ ^ 17 - ((5797 / 2370) : ℂ) * ζ ^ 18 + ((313 / 158) : ℂ) * ζ ^ 21 + ((406 / 395) : ℂ) * ζ ^ 22 + ((373 / 790) : ℂ) * ζ ^ 24 + ((131 / 2370) : ℂ) * ζ ^ 27 + ((3458 / 1185) : ℂ) * ζ ^ 28 + ((1051 / 474) : ℂ) * ζ ^ 29 + ((2273 / 2370) : ℂ) * ζ ^ 30 - ((1913 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep02CoefficientIdentity04 :
    row18_reducedY54_combinationStep02Coefficient04 =
      row18_reducedY54_combinationStep01Coefficient04 +
        row18_reducedY54_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep02Coefficient04 row18_reducedY54_combinationStep01Coefficient04 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 (-((89788 / 18723) : ℂ) - ((388729 / 187230) : ℂ) * ζ ^ 1 - ((77797 / 18723) : ℂ) * ζ ^ 2 - ((9633 / 31205) : ℂ) * ζ ^ 3 + ((106670 / 18723) : ℂ) * ζ ^ 4 + ((168434 / 31205) : ℂ) * ζ ^ 5 - ((208841 / 93615) : ℂ) * ζ ^ 6 - ((464636 / 93615) : ℂ) * ζ ^ 7 - ((46214 / 31205) : ℂ) * ζ ^ 8 + ((162107 / 187230) : ℂ) * ζ ^ 9 + ((109597 / 31205) : ℂ) * ζ ^ 10 + ((68156 / 93615) : ℂ) * ζ ^ 11 + ((132883 / 187230) : ℂ) * ζ ^ 12 - ((3897 / 31205) : ℂ) * ζ ^ 13 - ((211351 / 187230) : ℂ) * ζ ^ 14 - ((755 / 158) : ℂ) * ζ ^ 15 - ((299299 / 93615) : ℂ) * ζ ^ 16 - ((53459 / 93615) : ℂ) * ζ ^ 17 + ((3604 / 31205) : ℂ) * ζ ^ 18 + ((774041 / 187230) : ℂ) * ζ ^ 19 + ((128288 / 31205) : ℂ) * ζ ^ 20 - ((15541 / 37446) : ℂ) * ζ ^ 21 + ((221833 / 93615) : ℂ) * ζ ^ 22 - ((3869 / 31205) : ℂ) * ζ ^ 23 - ((167727 / 62410) : ℂ) * ζ ^ 24 - ((108437 / 62410) : ℂ) * ζ ^ 25 - ((146273 / 187230) : ℂ) * ζ ^ 26 + ((94667 / 62410) : ℂ) * ζ ^ 27 + ((8723 / 93615) : ℂ) * ζ ^ 28 + ((26621 / 31205) : ℂ) * ζ ^ 29 - ((11662 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep02CoefficientIdentity05 :
    row18_reducedY54_combinationStep02Coefficient05 =
      row18_reducedY54_combinationStep01Coefficient05 +
        row18_reducedY54_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep02Coefficient05 row18_reducedY54_combinationStep01Coefficient05 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep02Coefficient06 : ℂ :=
  (-((2038 / 237) : ℂ) - ((23141 / 1185) : ℂ) * ζ ^ 1 - ((2509 / 158) : ℂ) * ζ ^ 2 - ((1623 / 395) : ℂ) * ζ ^ 3 - ((2397 / 790) : ℂ) * ζ ^ 5 - ((2303 / 474) : ℂ) * ζ ^ 8 - ((2861 / 395) : ℂ) * ζ ^ 9 + ((4484 / 395) : ℂ) * ζ ^ 11 + ((3485 / 158) : ℂ) * ζ ^ 12 + ((23141 / 1185) : ℂ) * ζ ^ 13 - ((29353 / 2370) : ℂ) * ζ ^ 15 + ((23141 / 1185) : ℂ) * ζ ^ 17 + ((2509 / 158) : ℂ) * ζ ^ 18 + ((18272 / 1185) : ℂ) * ζ ^ 21 + ((2509 / 158) : ℂ) * ζ ^ 22 - ((4076 / 237) : ℂ) * ζ ^ 24 - ((39091 / 2370) : ℂ) * ζ ^ 25 + ((18272 / 1185) : ℂ) * ζ ^ 27 + ((2303 / 474) : ℂ) * ζ ^ 28 - ((23141 / 1185) : ℂ) * ζ ^ 29 - ((6080 / 237) : ℂ) * ζ ^ 30 - ((4484 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep02CoefficientIdentity06 :
    row18_reducedY54_combinationStep02Coefficient06 =
      row18_reducedY54_combinationStep01Coefficient06 +
        row18_reducedY54_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep02Coefficient06 row18_reducedY54_combinationStep01Coefficient06 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 (((1056874 / 93615) : ℂ) + ((128735 / 6241) : ℂ) * ζ ^ 1 + ((2841127 / 187230) : ℂ) * ζ ^ 2 - ((10834 / 93615) : ℂ) * ζ ^ 3 - ((1089478 / 93615) : ℂ) * ζ ^ 4 - ((3005329 / 187230) : ℂ) * ζ ^ 5 - ((1764709 / 187230) : ℂ) * ζ ^ 6 + ((173947 / 93615) : ℂ) * ζ ^ 7 + ((560823 / 62410) : ℂ) * ζ ^ 8 + ((1613521 / 187230) : ℂ) * ζ ^ 9 + ((1186003 / 187230) : ℂ) * ζ ^ 10 - ((96758 / 93615) : ℂ) * ζ ^ 11 - ((839984 / 93615) : ℂ) * ζ ^ 12 - ((920872 / 93615) : ℂ) * ζ ^ 13 - ((413093 / 187230) : ℂ) * ζ ^ 14 + ((395477 / 62410) : ℂ) * ζ ^ 15 + ((1927297 / 187230) : ℂ) * ζ ^ 16 + ((183339 / 31205) : ℂ) * ζ ^ 17 - ((52807 / 31205) : ℂ) * ζ ^ 18 - ((1443157 / 187230) : ℂ) * ζ ^ 19 - ((1388971 / 187230) : ℂ) * ζ ^ 20 - ((38611 / 31205) : ℂ) * ζ ^ 21 + ((105951 / 31205) : ℂ) * ζ ^ 22 + ((199021 / 37446) : ℂ) * ζ ^ 23 + ((985619 / 187230) : ℂ) * ζ ^ 24 + ((144098 / 93615) : ℂ) * ζ ^ 25 - ((332339 / 93615) : ℂ) * ζ ^ 26 - ((377949 / 62410) : ℂ) * ζ ^ 27 - ((65816 / 93615) : ℂ) * ζ ^ 28 + ((24767 / 12482) : ℂ) * ζ ^ 29 + ((4165 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep02CoefficientIdentity07 :
    row18_reducedY54_combinationStep02Coefficient07 =
      row18_reducedY54_combinationStep01Coefficient07 +
        row18_reducedY54_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep02Coefficient07 row18_reducedY54_combinationStep01Coefficient07 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep02CoefficientIdentity08 :
    row18_reducedY54_combinationStep02Coefficient08 =
      row18_reducedY54_combinationStep01Coefficient08 +
        row18_reducedY54_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep02Coefficient08 row18_reducedY54_combinationStep01Coefficient08 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep02CoefficientIdentity09 :
    row18_reducedY54_combinationStep02Coefficient09 =
      row18_reducedY54_combinationStep01Coefficient09 +
        row18_reducedY54_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep02Coefficient09 row18_reducedY54_combinationStep01Coefficient09 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep02CoefficientIdentity10 :
    row18_reducedY54_combinationStep02Coefficient10 =
      row18_reducedY54_combinationStep01Coefficient10 +
        row18_reducedY54_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep02Coefficient10 row18_reducedY54_combinationStep01Coefficient10 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep02CoefficientIdentity11 :
    row18_reducedY54_combinationStep02Coefficient11 =
      row18_reducedY54_combinationStep01Coefficient11 +
        row18_reducedY54_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep02Coefficient11 row18_reducedY54_combinationStep01Coefficient11 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep02CoefficientIdentity12 :
    row18_reducedY54_combinationStep02Coefficient12 =
      row18_reducedY54_combinationStep01Coefficient12 +
        row18_reducedY54_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep02Coefficient12 row18_reducedY54_combinationStep01Coefficient12 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep02CoefficientIdentity13 :
    row18_reducedY54_combinationStep02Coefficient13 =
      row18_reducedY54_combinationStep01Coefficient13 +
        row18_reducedY54_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep02Coefficient13 row18_reducedY54_combinationStep01Coefficient13 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep02CoefficientIdentity14 :
    row18_reducedY54_combinationStep02Coefficient14 =
      row18_reducedY54_combinationStep01Coefficient14 +
        row18_reducedY54_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep02Coefficient14 row18_reducedY54_combinationStep01Coefficient14 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep02CoefficientIdentity15 :
    row18_reducedY54_combinationStep02Coefficient15 =
      row18_reducedY54_combinationStep01Coefficient15 +
        row18_reducedY54_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep02Coefficient15 row18_reducedY54_combinationStep01Coefficient15 row18_reducedY54_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY54_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY54_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY54_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY54_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY54_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY54_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY54_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY54_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY54_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY54_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY54_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY54_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY54_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY54_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY54_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY54_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY54_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY54_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY54_combinationStep02CoefficientIdentity00,
      row18_reducedY54_combinationStep02CoefficientIdentity01,
      row18_reducedY54_combinationStep02CoefficientIdentity02,
      row18_reducedY54_combinationStep02CoefficientIdentity03,
      row18_reducedY54_combinationStep02CoefficientIdentity04,
      row18_reducedY54_combinationStep02CoefficientIdentity05,
      row18_reducedY54_combinationStep02CoefficientIdentity06,
      row18_reducedY54_combinationStep02CoefficientIdentity07,
      row18_reducedY54_combinationStep02CoefficientIdentity08,
      row18_reducedY54_combinationStep02CoefficientIdentity09,
      row18_reducedY54_combinationStep02CoefficientIdentity10,
      row18_reducedY54_combinationStep02CoefficientIdentity11,
      row18_reducedY54_combinationStep02CoefficientIdentity12,
      row18_reducedY54_combinationStep02CoefficientIdentity13,
      row18_reducedY54_combinationStep02CoefficientIdentity14,
      row18_reducedY54_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY54_combinationStep02Multiplier * equation

private def row18_reducedY54_combinationStep03Multiplier : ℂ :=
  (-((1504 / 237) : ℂ) - ((2204 / 237) : ℂ) * ζ ^ 1 - ((902 / 237) : ℂ) * ζ ^ 2 + ((826 / 237) : ℂ) * ζ ^ 3 - ((72 / 79) : ℂ) * ζ ^ 5 + ((4 / 237) : ℂ) * ζ ^ 6 + ((202 / 79) : ℂ) * ζ ^ 9 + ((72 / 79) : ℂ) * ζ ^ 11 + ((1888 / 237) : ℂ) * ζ ^ 12 + ((2204 / 237) : ℂ) * ζ ^ 13 - ((1382 / 237) : ℂ) * ζ ^ 15 + ((2204 / 237) : ℂ) * ζ ^ 17 + ((1808 / 237) : ℂ) * ζ ^ 18 + ((1042 / 237) : ℂ) * ζ ^ 21 + ((902 / 237) : ℂ) * ζ ^ 22 - ((1504 / 237) : ℂ) * ζ ^ 24 - ((1988 / 237) : ℂ) * ζ ^ 25 + ((1988 / 237) : ℂ) * ζ ^ 27 - ((2204 / 237) : ℂ) * ζ ^ 29 - ((1804 / 237) : ℂ) * ζ ^ 30 - ((72 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY54_combinationStep03Coefficient00 : ℂ :=
  (-((2142 / 395) : ℂ) - ((221 / 158) : ℂ) * ζ ^ 1 + ((8891 / 2370) : ℂ) * ζ ^ 2 + ((7156 / 1185) : ℂ) * ζ ^ 3 - ((221 / 158) : ℂ) * ζ ^ 5 - ((3961 / 2370) : ℂ) * ζ ^ 6 + ((3961 / 2370) : ℂ) * ζ ^ 8 + ((221 / 158) : ℂ) * ζ ^ 9 - ((3578 / 1185) : ℂ) * ζ ^ 11 + ((253 / 395) : ℂ) * ζ ^ 12 + ((221 / 158) : ℂ) * ζ ^ 13 - ((2531 / 790) : ℂ) * ζ ^ 15 + ((221 / 158) : ℂ) * ζ ^ 17 + ((1636 / 1185) : ℂ) * ζ ^ 18 - ((319 / 79) : ℂ) * ζ ^ 21 - ((8891 / 2370) : ℂ) * ζ ^ 22 - ((689 / 2370) : ℂ) * ζ ^ 24 + ((6719 / 2370) : ℂ) * ζ ^ 27 - ((3961 / 2370) : ℂ) * ζ ^ 28 - ((221 / 158) : ℂ) * ζ ^ 29 - ((2443 / 2370) : ℂ) * ζ ^ 30 + ((3578 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep03CoefficientIdentity00 :
    row18_reducedY54_combinationStep03Coefficient00 =
      row18_reducedY54_combinationStep02Coefficient00 +
        row18_reducedY54_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep03Coefficient00 row18_reducedY54_combinationStep02Coefficient00 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 (((283711 / 37446) : ℂ) + ((97868 / 18723) : ℂ) * ζ ^ 1 - ((38485 / 18723) : ℂ) * ζ ^ 2 - ((297365 / 37446) : ℂ) * ζ ^ 3 - ((267593 / 37446) : ℂ) * ζ ^ 4 + ((43363 / 37446) : ℂ) * ζ ^ 5 + ((96457 / 12482) : ℂ) * ζ ^ 6 + ((258683 / 37446) : ℂ) * ζ ^ 7 + ((26420 / 18723) : ℂ) * ζ ^ 8 - ((117505 / 37446) : ℂ) * ζ ^ 9 - ((174133 / 37446) : ℂ) * ζ ^ 10 - ((90257 / 37446) : ℂ) * ζ ^ 11 + ((11029 / 18723) : ℂ) * ζ ^ 12 + ((13447 / 6241) : ℂ) * ζ ^ 13 + ((81079 / 37446) : ℂ) * ζ ^ 14 + ((28970 / 18723) : ℂ) * ζ ^ 15 + ((1132 / 6241) : ℂ) * ζ ^ 16 - ((50755 / 37446) : ℂ) * ζ ^ 17 - ((52661 / 18723) : ℂ) * ζ ^ 18 - ((100747 / 37446) : ℂ) * ζ ^ 19 - ((6259 / 12482) : ℂ) * ζ ^ 20 + ((26135 / 12482) : ℂ) * ζ ^ 21 + ((62687 / 18723) : ℂ) * ζ ^ 22 + ((34963 / 18723) : ℂ) * ζ ^ 23 - ((37184 / 18723) : ℂ) * ζ ^ 24 - ((72487 / 18723) : ℂ) * ζ ^ 25 - ((9507 / 6241) : ℂ) * ζ ^ 26 + ((29125 / 18723) : ℂ) * ζ ^ 27 + ((10205 / 6241) : ℂ) * ζ ^ 28 + ((3119 / 6241) : ℂ) * ζ ^ 29 + ((270 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep03Coefficient01 : ℂ :=
  (-((59 / 237) : ℂ) + ((467 / 474) : ℂ) * ζ ^ 1 + ((590 / 237) : ℂ) * ζ ^ 2 + ((733 / 474) : ℂ) * ζ ^ 3 + ((49 / 474) : ℂ) * ζ ^ 5 + ((68 / 79) : ℂ) * ζ ^ 6 - ((150 / 79) : ℂ) * ζ ^ 8 - ((110 / 79) : ℂ) * ζ ^ 9 + ((49 / 474) : ℂ) * ζ ^ 11 - ((75 / 79) : ℂ) * ζ ^ 12 - ((467 / 474) : ℂ) * ζ ^ 13 + ((121 / 237) : ℂ) * ζ ^ 15 - ((467 / 474) : ℂ) * ζ ^ 17 - ((68 / 79) : ℂ) * ζ ^ 18 - ((391 / 237) : ℂ) * ζ ^ 21 - ((590 / 237) : ℂ) * ζ ^ 22 + ((509 / 237) : ℂ) * ζ ^ 24 + ((209 / 237) : ℂ) * ζ ^ 25 + ((209 / 237) : ℂ) * ζ ^ 27 + ((150 / 79) : ℂ) * ζ ^ 28 + ((467 / 474) : ℂ) * ζ ^ 29 - ((49 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep03CoefficientIdentity01 :
    row18_reducedY54_combinationStep03Coefficient01 =
      row18_reducedY54_combinationStep02Coefficient01 +
        row18_reducedY54_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep03Coefficient01 row18_reducedY54_combinationStep02Coefficient01 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 (-((201395 / 18723) : ℂ) - ((149111 / 18723) : ℂ) * ζ ^ 1 - ((35239 / 18723) : ℂ) * ζ ^ 2 + ((65562 / 6241) : ℂ) * ζ ^ 3 + ((221993 / 18723) : ℂ) * ζ ^ 4 - ((4901 / 12482) : ℂ) * ζ ^ 5 - ((399311 / 37446) : ℂ) * ζ ^ 6 - ((226774 / 18723) : ℂ) * ζ ^ 7 - ((85655 / 18723) : ℂ) * ζ ^ 8 + ((35837 / 6241) : ℂ) * ζ ^ 9 + ((147850 / 18723) : ℂ) * ζ ^ 10 + ((139055 / 37446) : ℂ) * ζ ^ 11 + ((360 / 6241) : ℂ) * ζ ^ 12 - ((36947 / 18723) : ℂ) * ζ ^ 13 - ((38996 / 18723) : ℂ) * ζ ^ 14 - ((33686 / 18723) : ℂ) * ζ ^ 15 - ((67405 / 18723) : ℂ) * ζ ^ 16 + ((17216 / 18723) : ℂ) * ζ ^ 17 + ((412645 / 37446) : ℂ) * ζ ^ 18 + ((137139 / 12482) : ℂ) * ζ ^ 19 + ((9059 / 18723) : ℂ) * ζ ^ 20 - ((42658 / 6241) : ℂ) * ζ ^ 21 - ((32023 / 6241) : ℂ) * ζ ^ 22 + ((38122 / 18723) : ℂ) * ζ ^ 23 + ((119791 / 18723) : ℂ) * ζ ^ 24 + ((26558 / 6241) : ℂ) * ζ ^ 25 - ((14155 / 18723) : ℂ) * ζ ^ 26 - ((167 / 79) : ℂ) * ζ ^ 27 - ((29330 / 18723) : ℂ) * ζ ^ 28 - ((13924 / 18723) : ℂ) * ζ ^ 29 - ((504 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep03Coefficient02 : ℂ :=
  (((637 / 79) : ℂ) + ((265 / 237) : ℂ) * ζ ^ 1 - ((2575 / 237) : ℂ) * ζ ^ 2 - ((1461 / 158) : ℂ) * ζ ^ 3 + ((1247 / 237) : ℂ) * ζ ^ 5 - ((461 / 79) : ℂ) * ζ ^ 6 - ((1043 / 158) : ℂ) * ζ ^ 8 + ((800 / 237) : ℂ) * ζ ^ 9 + ((5983 / 474) : ℂ) * ζ ^ 11 - ((1043 / 158) : ℂ) * ζ ^ 12 - ((265 / 237) : ℂ) * ζ ^ 13 + ((6347 / 474) : ℂ) * ζ ^ 15 - ((265 / 237) : ℂ) * ζ ^ 17 - ((1192 / 237) : ℂ) * ζ ^ 18 + ((3853 / 474) : ℂ) * ζ ^ 21 + ((2575 / 237) : ℂ) * ζ ^ 22 - ((982 / 237) : ℂ) * ζ ^ 25 - ((3853 / 474) : ℂ) * ζ ^ 27 + ((1043 / 158) : ℂ) * ζ ^ 28 + ((265 / 237) : ℂ) * ζ ^ 29 - ((461 / 158) : ℂ) * ζ ^ 30 - ((5983 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep03CoefficientIdentity02 :
    row18_reducedY54_combinationStep03Coefficient02 =
      row18_reducedY54_combinationStep02Coefficient02 +
        row18_reducedY54_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep03Coefficient02 row18_reducedY54_combinationStep02Coefficient02 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep03Coefficient03 : ℂ :=
  (-((3253 / 474) : ℂ) - ((1636 / 237) : ℂ) * ζ ^ 1 - ((457 / 474) : ℂ) * ζ ^ 2 + ((1390 / 237) : ℂ) * ζ ^ 3 - ((1636 / 237) : ℂ) * ζ ^ 5 - ((1855 / 237) : ℂ) * ζ ^ 6 + ((1855 / 237) : ℂ) * ζ ^ 8 + ((1636 / 237) : ℂ) * ζ ^ 9 - ((695 / 237) : ℂ) * ζ ^ 11 + ((1373 / 237) : ℂ) * ζ ^ 12 + ((1636 / 237) : ℂ) * ζ ^ 13 - ((576 / 79) : ℂ) * ζ ^ 15 + ((1636 / 237) : ℂ) * ζ ^ 17 + ((3467 / 474) : ℂ) * ζ ^ 18 + ((121 / 474) : ℂ) * ζ ^ 21 + ((457 / 474) : ℂ) * ζ ^ 22 - ((81 / 158) : ℂ) * ζ ^ 24 - ((338 / 237) : ℂ) * ζ ^ 27 - ((1855 / 237) : ℂ) * ζ ^ 28 - ((1636 / 237) : ℂ) * ζ ^ 29 - ((482 / 237) : ℂ) * ζ ^ 30 + ((695 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep03CoefficientIdentity03 :
    row18_reducedY54_combinationStep03Coefficient03 =
      row18_reducedY54_combinationStep02Coefficient03 +
        row18_reducedY54_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep03Coefficient03 row18_reducedY54_combinationStep02Coefficient03 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep03Coefficient04 : ℂ :=
  (((4676 / 1185) : ℂ) + ((1051 / 474) : ℂ) * ζ ^ 1 - ((406 / 395) : ℂ) * ζ ^ 2 - ((3826 / 1185) : ℂ) * ζ ^ 3 + ((1051 / 474) : ℂ) * ζ ^ 5 + ((3458 / 1185) : ℂ) * ζ ^ 6 - ((3458 / 1185) : ℂ) * ζ ^ 8 - ((1051 / 474) : ℂ) * ζ ^ 9 + ((1913 / 1185) : ℂ) * ζ ^ 11 - ((4643 / 2370) : ℂ) * ζ ^ 12 - ((1051 / 474) : ℂ) * ζ ^ 13 + ((7783 / 2370) : ℂ) * ζ ^ 15 - ((1051 / 474) : ℂ) * ζ ^ 17 - ((5797 / 2370) : ℂ) * ζ ^ 18 + ((313 / 158) : ℂ) * ζ ^ 21 + ((406 / 395) : ℂ) * ζ ^ 22 + ((373 / 790) : ℂ) * ζ ^ 24 + ((131 / 2370) : ℂ) * ζ ^ 27 + ((3458 / 1185) : ℂ) * ζ ^ 28 + ((1051 / 474) : ℂ) * ζ ^ 29 + ((2273 / 2370) : ℂ) * ζ ^ 30 - ((1913 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep03CoefficientIdentity04 :
    row18_reducedY54_combinationStep03Coefficient04 =
      row18_reducedY54_combinationStep02Coefficient04 +
        row18_reducedY54_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep03Coefficient04 row18_reducedY54_combinationStep02Coefficient04 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep03Coefficient05 : ℂ :=
  (((809 / 474) : ℂ) + ((149 / 237) : ℂ) * ζ ^ 1 + ((44 / 79) : ℂ) * ζ ^ 2 - ((65 / 474) : ℂ) * ζ ^ 3 - ((361 / 474) : ℂ) * ζ ^ 5 - ((16 / 237) : ℂ) * ζ ^ 6 + ((52 / 237) : ℂ) * ζ ^ 9 + ((361 / 474) : ℂ) * ζ ^ 11 - ((53 / 79) : ℂ) * ζ ^ 12 - ((149 / 237) : ℂ) * ζ ^ 13 + ((763 / 474) : ℂ) * ζ ^ 15 - ((149 / 237) : ℂ) * ζ ^ 17 - ((280 / 237) : ℂ) * ζ ^ 18 + ((148 / 237) : ℂ) * ζ ^ 21 - ((44 / 79) : ℂ) * ζ ^ 22 + ((809 / 474) : ℂ) * ζ ^ 24 + ((659 / 474) : ℂ) * ζ ^ 25 - ((659 / 474) : ℂ) * ζ ^ 27 + ((149 / 237) : ℂ) * ζ ^ 29 + ((88 / 79) : ℂ) * ζ ^ 30 - ((361 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep03CoefficientIdentity05 :
    row18_reducedY54_combinationStep03Coefficient05 =
      row18_reducedY54_combinationStep02Coefficient05 +
        row18_reducedY54_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep03Coefficient05 row18_reducedY54_combinationStep02Coefficient05 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 (-((72935 / 37446) : ℂ) - ((4749 / 6241) : ℂ) * ζ ^ 1 - ((13011 / 6241) : ℂ) * ζ ^ 2 - ((38557 / 18723) : ℂ) * ζ ^ 3 + ((32261 / 37446) : ℂ) * ζ ^ 4 + ((12906 / 6241) : ℂ) * ζ ^ 5 + ((17989 / 18723) : ℂ) * ζ ^ 6 + ((24079 / 37446) : ℂ) * ζ ^ 7 - ((6070 / 18723) : ℂ) * ζ ^ 8 - ((6543 / 6241) : ℂ) * ζ ^ 9 - ((6467 / 6241) : ℂ) * ζ ^ 10 - ((29680 / 18723) : ℂ) * ζ ^ 11 - ((3409 / 12482) : ℂ) * ζ ^ 12 + ((37045 / 18723) : ℂ) * ζ ^ 13 + ((7079 / 6241) : ℂ) * ζ ^ 14 - ((28301 / 37446) : ℂ) * ζ ^ 15 - ((55231 / 37446) : ℂ) * ζ ^ 16 - ((27613 / 18723) : ℂ) * ζ ^ 17 - ((4242 / 6241) : ℂ) * ζ ^ 18 + ((27131 / 37446) : ℂ) * ζ ^ 19 + ((6803 / 18723) : ℂ) * ζ ^ 20 - ((302 / 6241) : ℂ) * ζ ^ 21 + ((8752 / 6241) : ℂ) * ζ ^ 22 + ((33982 / 18723) : ℂ) * ζ ^ 23 + ((9182 / 18723) : ℂ) * ζ ^ 24 - ((3640 / 6241) : ℂ) * ζ ^ 25 - ((16736 / 18723) : ℂ) * ζ ^ 26 - ((1915 / 6241) : ℂ) * ζ ^ 27 + ((364 / 6241) : ℂ) * ζ ^ 28 + ((5450 / 18723) : ℂ) * ζ ^ 29 + ((252 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep03Coefficient06 : ℂ :=
  (-((2038 / 237) : ℂ) - ((23141 / 1185) : ℂ) * ζ ^ 1 - ((2509 / 158) : ℂ) * ζ ^ 2 - ((1623 / 395) : ℂ) * ζ ^ 3 - ((2397 / 790) : ℂ) * ζ ^ 5 - ((2303 / 474) : ℂ) * ζ ^ 8 - ((2861 / 395) : ℂ) * ζ ^ 9 + ((4484 / 395) : ℂ) * ζ ^ 11 + ((3485 / 158) : ℂ) * ζ ^ 12 + ((23141 / 1185) : ℂ) * ζ ^ 13 - ((29353 / 2370) : ℂ) * ζ ^ 15 + ((23141 / 1185) : ℂ) * ζ ^ 17 + ((2509 / 158) : ℂ) * ζ ^ 18 + ((18272 / 1185) : ℂ) * ζ ^ 21 + ((2509 / 158) : ℂ) * ζ ^ 22 - ((4076 / 237) : ℂ) * ζ ^ 24 - ((39091 / 2370) : ℂ) * ζ ^ 25 + ((18272 / 1185) : ℂ) * ζ ^ 27 + ((2303 / 474) : ℂ) * ζ ^ 28 - ((23141 / 1185) : ℂ) * ζ ^ 29 - ((6080 / 237) : ℂ) * ζ ^ 30 - ((4484 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep03CoefficientIdentity06 :
    row18_reducedY54_combinationStep03Coefficient06 =
      row18_reducedY54_combinationStep02Coefficient06 +
        row18_reducedY54_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep03Coefficient06 row18_reducedY54_combinationStep02Coefficient06 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep03Coefficient07 : ℂ :=
  (((3953 / 474) : ℂ) + ((1442 / 237) : ℂ) * ζ ^ 1 - ((139 / 79) : ℂ) * ζ ^ 2 - ((2056 / 237) : ℂ) * ζ ^ 3 + ((1442 / 237) : ℂ) * ζ ^ 5 + ((3119 / 474) : ℂ) * ζ ^ 6 - ((3119 / 474) : ℂ) * ζ ^ 8 - ((1442 / 237) : ℂ) * ζ ^ 9 + ((1028 / 237) : ℂ) * ζ ^ 11 - ((707 / 158) : ℂ) * ζ ^ 12 - ((1442 / 237) : ℂ) * ζ ^ 13 + ((1709 / 237) : ℂ) * ζ ^ 15 - ((1442 / 237) : ℂ) * ζ ^ 17 - ((1481 / 237) : ℂ) * ζ ^ 18 + ((427 / 237) : ℂ) * ζ ^ 21 + ((139 / 79) : ℂ) * ζ ^ 22 + ((157 / 474) : ℂ) * ζ ^ 24 - ((347 / 237) : ℂ) * ζ ^ 27 + ((3119 / 474) : ℂ) * ζ ^ 28 + ((1442 / 237) : ℂ) * ζ ^ 29 + ((499 / 237) : ℂ) * ζ ^ 30 - ((1028 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep03CoefficientIdentity07 :
    row18_reducedY54_combinationStep03Coefficient07 =
      row18_reducedY54_combinationStep02Coefficient07 +
        row18_reducedY54_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep03Coefficient07 row18_reducedY54_combinationStep02Coefficient07 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 (-((283711 / 37446) : ℂ) - ((97868 / 18723) : ℂ) * ζ ^ 1 + ((38485 / 18723) : ℂ) * ζ ^ 2 + ((297365 / 37446) : ℂ) * ζ ^ 3 + ((267593 / 37446) : ℂ) * ζ ^ 4 - ((43363 / 37446) : ℂ) * ζ ^ 5 - ((96457 / 12482) : ℂ) * ζ ^ 6 - ((258683 / 37446) : ℂ) * ζ ^ 7 - ((26420 / 18723) : ℂ) * ζ ^ 8 + ((117505 / 37446) : ℂ) * ζ ^ 9 + ((174133 / 37446) : ℂ) * ζ ^ 10 + ((90257 / 37446) : ℂ) * ζ ^ 11 - ((11029 / 18723) : ℂ) * ζ ^ 12 - ((13447 / 6241) : ℂ) * ζ ^ 13 - ((81079 / 37446) : ℂ) * ζ ^ 14 - ((28970 / 18723) : ℂ) * ζ ^ 15 - ((1132 / 6241) : ℂ) * ζ ^ 16 + ((50755 / 37446) : ℂ) * ζ ^ 17 + ((52661 / 18723) : ℂ) * ζ ^ 18 + ((100747 / 37446) : ℂ) * ζ ^ 19 + ((6259 / 12482) : ℂ) * ζ ^ 20 - ((26135 / 12482) : ℂ) * ζ ^ 21 - ((62687 / 18723) : ℂ) * ζ ^ 22 - ((34963 / 18723) : ℂ) * ζ ^ 23 + ((37184 / 18723) : ℂ) * ζ ^ 24 + ((72487 / 18723) : ℂ) * ζ ^ 25 + ((9507 / 6241) : ℂ) * ζ ^ 26 - ((29125 / 18723) : ℂ) * ζ ^ 27 - ((10205 / 6241) : ℂ) * ζ ^ 28 - ((3119 / 6241) : ℂ) * ζ ^ 29 - ((270 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep03CoefficientIdentity08 :
    row18_reducedY54_combinationStep03Coefficient08 =
      row18_reducedY54_combinationStep02Coefficient08 +
        row18_reducedY54_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep03Coefficient08 row18_reducedY54_combinationStep02Coefficient08 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep03CoefficientIdentity09 :
    row18_reducedY54_combinationStep03Coefficient09 =
      row18_reducedY54_combinationStep02Coefficient09 +
        row18_reducedY54_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep03Coefficient09 row18_reducedY54_combinationStep02Coefficient09 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep03CoefficientIdentity10 :
    row18_reducedY54_combinationStep03Coefficient10 =
      row18_reducedY54_combinationStep02Coefficient10 +
        row18_reducedY54_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep03Coefficient10 row18_reducedY54_combinationStep02Coefficient10 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep03CoefficientIdentity11 :
    row18_reducedY54_combinationStep03Coefficient11 =
      row18_reducedY54_combinationStep02Coefficient11 +
        row18_reducedY54_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep03Coefficient11 row18_reducedY54_combinationStep02Coefficient11 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep03CoefficientIdentity12 :
    row18_reducedY54_combinationStep03Coefficient12 =
      row18_reducedY54_combinationStep02Coefficient12 +
        row18_reducedY54_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep03Coefficient12 row18_reducedY54_combinationStep02Coefficient12 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep03CoefficientIdentity13 :
    row18_reducedY54_combinationStep03Coefficient13 =
      row18_reducedY54_combinationStep02Coefficient13 +
        row18_reducedY54_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep03Coefficient13 row18_reducedY54_combinationStep02Coefficient13 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep03CoefficientIdentity14 :
    row18_reducedY54_combinationStep03Coefficient14 =
      row18_reducedY54_combinationStep02Coefficient14 +
        row18_reducedY54_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep03Coefficient14 row18_reducedY54_combinationStep02Coefficient14 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep03CoefficientIdentity15 :
    row18_reducedY54_combinationStep03Coefficient15 =
      row18_reducedY54_combinationStep02Coefficient15 +
        row18_reducedY54_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep03Coefficient15 row18_reducedY54_combinationStep02Coefficient15 row18_reducedY54_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY54_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY54_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY54_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY54_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY54_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY54_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY54_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY54_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY54_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY54_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY54_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY54_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY54_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY54_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY54_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY54_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY54_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY54_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY54_combinationStep03CoefficientIdentity00,
      row18_reducedY54_combinationStep03CoefficientIdentity01,
      row18_reducedY54_combinationStep03CoefficientIdentity02,
      row18_reducedY54_combinationStep03CoefficientIdentity03,
      row18_reducedY54_combinationStep03CoefficientIdentity04,
      row18_reducedY54_combinationStep03CoefficientIdentity05,
      row18_reducedY54_combinationStep03CoefficientIdentity06,
      row18_reducedY54_combinationStep03CoefficientIdentity07,
      row18_reducedY54_combinationStep03CoefficientIdentity08,
      row18_reducedY54_combinationStep03CoefficientIdentity09,
      row18_reducedY54_combinationStep03CoefficientIdentity10,
      row18_reducedY54_combinationStep03CoefficientIdentity11,
      row18_reducedY54_combinationStep03CoefficientIdentity12,
      row18_reducedY54_combinationStep03CoefficientIdentity13,
      row18_reducedY54_combinationStep03CoefficientIdentity14,
      row18_reducedY54_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY54_combinationStep03Multiplier * equation

private def row18_reducedY54_combinationStep04Multiplier : ℂ :=
  (-((374 / 237) : ℂ) + ((22 / 237) : ℂ) * ζ ^ 1 - ((226 / 237) : ℂ) * ζ ^ 2 + ((290 / 79) : ℂ) * ζ ^ 5 + ((148 / 237) : ℂ) * ζ ^ 6 + ((148 / 237) : ℂ) * ζ ^ 8 + ((290 / 79) : ℂ) * ζ ^ 9 - ((694 / 237) : ℂ) * ζ ^ 11 - ((78 / 79) : ℂ) * ζ ^ 12 - ((22 / 237) : ℂ) * ζ ^ 13 - ((218 / 237) : ℂ) * ζ ^ 15 - ((22 / 237) : ℂ) * ζ ^ 17 + ((84 / 79) : ℂ) * ζ ^ 18 - ((446 / 237) : ℂ) * ζ ^ 21 + ((226 / 237) : ℂ) * ζ ^ 22 - ((400 / 237) : ℂ) * ζ ^ 24 - ((848 / 237) : ℂ) * ζ ^ 25 + ((218 / 237) : ℂ) * ζ ^ 27 - ((148 / 237) : ℂ) * ζ ^ 28 + ((22 / 237) : ℂ) * ζ ^ 29 + ((382 / 237) : ℂ) * ζ ^ 30 + ((694 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY54_combinationStep04Coefficient00 : ℂ :=
  (-((51 / 10) : ℂ) - ((5 / 2) : ℂ) * ζ ^ 1 + ((9 / 5) : ℂ) * ζ ^ 2 + ((23 / 5) : ℂ) * ζ ^ 3 - ((5 / 2) : ℂ) * ζ ^ 5 - ((33 / 10) : ℂ) * ζ ^ 6 + ((33 / 10) : ℂ) * ζ ^ 8 + ((5 / 2) : ℂ) * ζ ^ 9 - ((23 / 10) : ℂ) * ζ ^ 11 + ((19 / 10) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 13 - ((39 / 10) : ℂ) * ζ ^ 15 + ((5 / 2) : ℂ) * ζ ^ 17 + ((13 / 5) : ℂ) * ζ ^ 18 - ((5 / 2) : ℂ) * ζ ^ 21 - ((9 / 5) : ℂ) * ζ ^ 22 - ((7 / 10) : ℂ) * ζ ^ 24 + ((7 / 10) : ℂ) * ζ ^ 27 - ((33 / 10) : ℂ) * ζ ^ 28 - ((5 / 2) : ℂ) * ζ ^ 29 - ((7 / 5) : ℂ) * ζ ^ 30 + ((23 / 10) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep04CoefficientIdentity00 :
    row18_reducedY54_combinationStep04Coefficient00 =
      row18_reducedY54_combinationStep03Coefficient00 +
        row18_reducedY54_combinationStep04Multiplier *
          (-((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((57 / 158) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((57 / 158) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((57 / 158) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep04Coefficient00 row18_reducedY54_combinationStep03Coefficient00 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 (-((9095 / 37446) : ℂ) + ((39005 / 37446) : ℂ) * ζ ^ 1 + ((26843 / 18723) : ℂ) * ζ ^ 2 + ((54263 / 37446) : ℂ) * ζ ^ 3 - ((3809 / 37446) : ℂ) * ζ ^ 4 - ((2 / 79) : ℂ) * ζ ^ 5 + ((5347 / 18723) : ℂ) * ζ ^ 6 - ((856 / 18723) : ℂ) * ζ ^ 7 - ((51919 / 37446) : ℂ) * ζ ^ 8 - ((7379 / 6241) : ℂ) * ζ ^ 9 - ((3274 / 18723) : ℂ) * ζ ^ 10 + ((9033 / 12482) : ℂ) * ζ ^ 11 - ((1977 / 6241) : ℂ) * ζ ^ 12 + ((3337 / 37446) : ℂ) * ζ ^ 13 + ((31369 / 37446) : ℂ) * ζ ^ 14 + ((48329 / 37446) : ℂ) * ζ ^ 15 + ((5630 / 18723) : ℂ) * ζ ^ 16 - ((2018 / 18723) : ℂ) * ζ ^ 17 - ((415 / 12482) : ℂ) * ζ ^ 18 + ((2483 / 37446) : ℂ) * ζ ^ 19 - ((3558 / 6241) : ℂ) * ζ ^ 20 - ((39823 / 37446) : ℂ) * ζ ^ 21 - ((11171 / 37446) : ℂ) * ζ ^ 22 - ((2847 / 12482) : ℂ) * ζ ^ 23 + ((11891 / 37446) : ℂ) * ζ ^ 24 - ((3545 / 37446) : ℂ) * ζ ^ 25 - ((1546 / 18723) : ℂ) * ζ ^ 26 + ((1187 / 37446) : ℂ) * ζ ^ 27 + ((1985 / 12482) : ℂ) * ζ ^ 28 + ((745 / 18723) : ℂ) * ζ ^ 29 - ((2429 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep04Coefficient01 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep04CoefficientIdentity01 :
    row18_reducedY54_combinationStep04Coefficient01 =
      row18_reducedY54_combinationStep03Coefficient01 +
        row18_reducedY54_combinationStep04Multiplier *
          (-((5 / 79) : ℂ) - ((43 / 316) : ℂ) * ζ ^ 1 - ((9 / 158) : ℂ) * ζ ^ 2 - ((63 / 316) : ℂ) * ζ ^ 5 + ((1 / 158) : ℂ) * ζ ^ 6 + ((1 / 158) : ℂ) * ζ ^ 8 - ((63 / 316) : ℂ) * ζ ^ 9 + ((57 / 158) : ℂ) * ζ ^ 11 + ((31 / 316) : ℂ) * ζ ^ 12 + ((43 / 316) : ℂ) * ζ ^ 13 - ((3 / 79) : ℂ) * ζ ^ 15 + ((43 / 316) : ℂ) * ζ ^ 17 - ((3 / 316) : ℂ) * ζ ^ 18 + ((53 / 316) : ℂ) * ζ ^ 21 + ((9 / 158) : ℂ) * ζ ^ 22 + ((1 / 316) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((1 / 158) : ℂ) * ζ ^ 28 - ((43 / 316) : ℂ) * ζ ^ 29 - ((29 / 316) : ℂ) * ζ ^ 30 - ((57 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep04Coefficient01 row18_reducedY54_combinationStep03Coefficient01 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 (-((2791 / 18723) : ℂ) + ((283 / 237) : ℂ) * ζ ^ 1 + ((32791 / 12482) : ℂ) * ζ ^ 2 + ((132 / 79) : ℂ) * ζ ^ 3 + ((3808 / 18723) : ℂ) * ζ ^ 4 - ((239 / 237) : ℂ) * ζ ^ 5 - ((29131 / 12482) : ℂ) * ζ ^ 6 - ((841 / 474) : ℂ) * ζ ^ 7 - ((13688 / 6241) : ℂ) * ζ ^ 8 - ((61 / 158) : ℂ) * ζ ^ 9 + ((19516 / 18723) : ℂ) * ζ ^ 10 + ((217 / 158) : ℂ) * ζ ^ 11 + ((8977 / 6241) : ℂ) * ζ ^ 12 + ((119 / 474) : ℂ) * ζ ^ 13 + ((2188 / 18723) : ℂ) * ζ ^ 14 + ((166 / 237) : ℂ) * ζ ^ 15 + ((12163 / 18723) : ℂ) * ζ ^ 16 - ((241 / 474) : ℂ) * ζ ^ 17 - ((16294 / 18723) : ℂ) * ζ ^ 18 - ((371 / 474) : ℂ) * ζ ^ 19 - ((10397 / 12482) : ℂ) * ζ ^ 20 - ((415 / 474) : ℂ) * ζ ^ 21 - ((3418 / 18723) : ℂ) * ζ ^ 22 + ((493 / 474) : ℂ) * ζ ^ 23 + ((72583 / 37446) : ℂ) * ζ ^ 24 + ((72 / 79) : ℂ) * ζ ^ 25 + ((32587 / 37446) : ℂ) * ζ ^ 26 - ((5 / 237) : ℂ) * ζ ^ 27 - ((3619 / 6241) : ℂ) * ζ ^ 28 - ((403 / 474) : ℂ) * ζ ^ 29 - ((6593 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep04Coefficient02 : ℂ :=
  (((637 / 79) : ℂ) + ((265 / 237) : ℂ) * ζ ^ 1 - ((2575 / 237) : ℂ) * ζ ^ 2 - ((1461 / 158) : ℂ) * ζ ^ 3 + ((1247 / 237) : ℂ) * ζ ^ 5 - ((461 / 79) : ℂ) * ζ ^ 6 - ((1043 / 158) : ℂ) * ζ ^ 8 + ((800 / 237) : ℂ) * ζ ^ 9 + ((5983 / 474) : ℂ) * ζ ^ 11 - ((1043 / 158) : ℂ) * ζ ^ 12 - ((265 / 237) : ℂ) * ζ ^ 13 + ((6347 / 474) : ℂ) * ζ ^ 15 - ((265 / 237) : ℂ) * ζ ^ 17 - ((1192 / 237) : ℂ) * ζ ^ 18 + ((3853 / 474) : ℂ) * ζ ^ 21 + ((2575 / 237) : ℂ) * ζ ^ 22 - ((982 / 237) : ℂ) * ζ ^ 25 - ((3853 / 474) : ℂ) * ζ ^ 27 + ((1043 / 158) : ℂ) * ζ ^ 28 + ((265 / 237) : ℂ) * ζ ^ 29 - ((461 / 158) : ℂ) * ζ ^ 30 - ((5983 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep04CoefficientIdentity02 :
    row18_reducedY54_combinationStep04Coefficient02 =
      row18_reducedY54_combinationStep03Coefficient02 +
        row18_reducedY54_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep04Coefficient02 row18_reducedY54_combinationStep03Coefficient02 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep04Coefficient03 : ℂ :=
  (-((3253 / 474) : ℂ) - ((1636 / 237) : ℂ) * ζ ^ 1 - ((457 / 474) : ℂ) * ζ ^ 2 + ((1390 / 237) : ℂ) * ζ ^ 3 - ((1636 / 237) : ℂ) * ζ ^ 5 - ((1855 / 237) : ℂ) * ζ ^ 6 + ((1855 / 237) : ℂ) * ζ ^ 8 + ((1636 / 237) : ℂ) * ζ ^ 9 - ((695 / 237) : ℂ) * ζ ^ 11 + ((1373 / 237) : ℂ) * ζ ^ 12 + ((1636 / 237) : ℂ) * ζ ^ 13 - ((576 / 79) : ℂ) * ζ ^ 15 + ((1636 / 237) : ℂ) * ζ ^ 17 + ((3467 / 474) : ℂ) * ζ ^ 18 + ((121 / 474) : ℂ) * ζ ^ 21 + ((457 / 474) : ℂ) * ζ ^ 22 - ((81 / 158) : ℂ) * ζ ^ 24 - ((338 / 237) : ℂ) * ζ ^ 27 - ((1855 / 237) : ℂ) * ζ ^ 28 - ((1636 / 237) : ℂ) * ζ ^ 29 - ((482 / 237) : ℂ) * ζ ^ 30 + ((695 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep04CoefficientIdentity03 :
    row18_reducedY54_combinationStep04Coefficient03 =
      row18_reducedY54_combinationStep03Coefficient03 +
        row18_reducedY54_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep04Coefficient03 row18_reducedY54_combinationStep03Coefficient03 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep04Coefficient04 : ℂ :=
  (((4676 / 1185) : ℂ) + ((1051 / 474) : ℂ) * ζ ^ 1 - ((406 / 395) : ℂ) * ζ ^ 2 - ((3826 / 1185) : ℂ) * ζ ^ 3 + ((1051 / 474) : ℂ) * ζ ^ 5 + ((3458 / 1185) : ℂ) * ζ ^ 6 - ((3458 / 1185) : ℂ) * ζ ^ 8 - ((1051 / 474) : ℂ) * ζ ^ 9 + ((1913 / 1185) : ℂ) * ζ ^ 11 - ((4643 / 2370) : ℂ) * ζ ^ 12 - ((1051 / 474) : ℂ) * ζ ^ 13 + ((7783 / 2370) : ℂ) * ζ ^ 15 - ((1051 / 474) : ℂ) * ζ ^ 17 - ((5797 / 2370) : ℂ) * ζ ^ 18 + ((313 / 158) : ℂ) * ζ ^ 21 + ((406 / 395) : ℂ) * ζ ^ 22 + ((373 / 790) : ℂ) * ζ ^ 24 + ((131 / 2370) : ℂ) * ζ ^ 27 + ((3458 / 1185) : ℂ) * ζ ^ 28 + ((1051 / 474) : ℂ) * ζ ^ 29 + ((2273 / 2370) : ℂ) * ζ ^ 30 - ((1913 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep04CoefficientIdentity04 :
    row18_reducedY54_combinationStep04Coefficient04 =
      row18_reducedY54_combinationStep03Coefficient04 +
        row18_reducedY54_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep04Coefficient04 row18_reducedY54_combinationStep03Coefficient04 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep04Coefficient05 : ℂ :=
  (((809 / 474) : ℂ) + ((149 / 237) : ℂ) * ζ ^ 1 + ((44 / 79) : ℂ) * ζ ^ 2 - ((65 / 474) : ℂ) * ζ ^ 3 - ((361 / 474) : ℂ) * ζ ^ 5 - ((16 / 237) : ℂ) * ζ ^ 6 + ((52 / 237) : ℂ) * ζ ^ 9 + ((361 / 474) : ℂ) * ζ ^ 11 - ((53 / 79) : ℂ) * ζ ^ 12 - ((149 / 237) : ℂ) * ζ ^ 13 + ((763 / 474) : ℂ) * ζ ^ 15 - ((149 / 237) : ℂ) * ζ ^ 17 - ((280 / 237) : ℂ) * ζ ^ 18 + ((148 / 237) : ℂ) * ζ ^ 21 - ((44 / 79) : ℂ) * ζ ^ 22 + ((809 / 474) : ℂ) * ζ ^ 24 + ((659 / 474) : ℂ) * ζ ^ 25 - ((659 / 474) : ℂ) * ζ ^ 27 + ((149 / 237) : ℂ) * ζ ^ 29 + ((88 / 79) : ℂ) * ζ ^ 30 - ((361 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep04CoefficientIdentity05 :
    row18_reducedY54_combinationStep04Coefficient05 =
      row18_reducedY54_combinationStep03Coefficient05 +
        row18_reducedY54_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep04Coefficient05 row18_reducedY54_combinationStep03Coefficient05 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep04Coefficient06 : ℂ :=
  (-((2038 / 237) : ℂ) - ((23141 / 1185) : ℂ) * ζ ^ 1 - ((2509 / 158) : ℂ) * ζ ^ 2 - ((1623 / 395) : ℂ) * ζ ^ 3 - ((2397 / 790) : ℂ) * ζ ^ 5 - ((2303 / 474) : ℂ) * ζ ^ 8 - ((2861 / 395) : ℂ) * ζ ^ 9 + ((4484 / 395) : ℂ) * ζ ^ 11 + ((3485 / 158) : ℂ) * ζ ^ 12 + ((23141 / 1185) : ℂ) * ζ ^ 13 - ((29353 / 2370) : ℂ) * ζ ^ 15 + ((23141 / 1185) : ℂ) * ζ ^ 17 + ((2509 / 158) : ℂ) * ζ ^ 18 + ((18272 / 1185) : ℂ) * ζ ^ 21 + ((2509 / 158) : ℂ) * ζ ^ 22 - ((4076 / 237) : ℂ) * ζ ^ 24 - ((39091 / 2370) : ℂ) * ζ ^ 25 + ((18272 / 1185) : ℂ) * ζ ^ 27 + ((2303 / 474) : ℂ) * ζ ^ 28 - ((23141 / 1185) : ℂ) * ζ ^ 29 - ((6080 / 237) : ℂ) * ζ ^ 30 - ((4484 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep04CoefficientIdentity06 :
    row18_reducedY54_combinationStep04Coefficient06 =
      row18_reducedY54_combinationStep03Coefficient06 +
        row18_reducedY54_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep04Coefficient06 row18_reducedY54_combinationStep03Coefficient06 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep04Coefficient07 : ℂ :=
  (((3953 / 474) : ℂ) + ((1442 / 237) : ℂ) * ζ ^ 1 - ((139 / 79) : ℂ) * ζ ^ 2 - ((2056 / 237) : ℂ) * ζ ^ 3 + ((1442 / 237) : ℂ) * ζ ^ 5 + ((3119 / 474) : ℂ) * ζ ^ 6 - ((3119 / 474) : ℂ) * ζ ^ 8 - ((1442 / 237) : ℂ) * ζ ^ 9 + ((1028 / 237) : ℂ) * ζ ^ 11 - ((707 / 158) : ℂ) * ζ ^ 12 - ((1442 / 237) : ℂ) * ζ ^ 13 + ((1709 / 237) : ℂ) * ζ ^ 15 - ((1442 / 237) : ℂ) * ζ ^ 17 - ((1481 / 237) : ℂ) * ζ ^ 18 + ((427 / 237) : ℂ) * ζ ^ 21 + ((139 / 79) : ℂ) * ζ ^ 22 + ((157 / 474) : ℂ) * ζ ^ 24 - ((347 / 237) : ℂ) * ζ ^ 27 + ((3119 / 474) : ℂ) * ζ ^ 28 + ((1442 / 237) : ℂ) * ζ ^ 29 + ((499 / 237) : ℂ) * ζ ^ 30 - ((1028 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep04CoefficientIdentity07 :
    row18_reducedY54_combinationStep04Coefficient07 =
      row18_reducedY54_combinationStep03Coefficient07 +
        row18_reducedY54_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep04Coefficient07 row18_reducedY54_combinationStep03Coefficient07 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep04Coefficient08 : ℂ :=
  (-((51 / 158) : ℂ) + ((87 / 79) : ℂ) * ζ ^ 1 + ((925 / 474) : ℂ) * ζ ^ 2 + ((341 / 237) : ℂ) * ζ ^ 3 + ((87 / 79) : ℂ) * ζ ^ 5 + ((386 / 237) : ℂ) * ζ ^ 6 - ((386 / 237) : ℂ) * ζ ^ 8 - ((87 / 79) : ℂ) * ζ ^ 9 - ((341 / 474) : ℂ) * ζ ^ 11 - ((199 / 158) : ℂ) * ζ ^ 12 - ((87 / 79) : ℂ) * ζ ^ 13 + ((55 / 79) : ℂ) * ζ ^ 15 - ((87 / 79) : ℂ) * ζ ^ 17 - ((289 / 237) : ℂ) * ζ ^ 18 - ((243 / 158) : ℂ) * ζ ^ 21 - ((925 / 474) : ℂ) * ζ ^ 22 + ((97 / 237) : ℂ) * ζ ^ 24 + ((506 / 237) : ℂ) * ζ ^ 27 + ((386 / 237) : ℂ) * ζ ^ 28 + ((87 / 79) : ℂ) * ζ ^ 29 + ((175 / 474) : ℂ) * ζ ^ 30 + ((341 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep04CoefficientIdentity08 :
    row18_reducedY54_combinationStep04Coefficient08 =
      row18_reducedY54_combinationStep03Coefficient08 +
        row18_reducedY54_combinationStep04Multiplier *
          (((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((57 / 158) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((57 / 158) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((57 / 158) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep04Coefficient08 row18_reducedY54_combinationStep03Coefficient08 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 (((9095 / 37446) : ℂ) - ((39005 / 37446) : ℂ) * ζ ^ 1 - ((26843 / 18723) : ℂ) * ζ ^ 2 - ((54263 / 37446) : ℂ) * ζ ^ 3 + ((3809 / 37446) : ℂ) * ζ ^ 4 + ((2 / 79) : ℂ) * ζ ^ 5 - ((5347 / 18723) : ℂ) * ζ ^ 6 + ((856 / 18723) : ℂ) * ζ ^ 7 + ((51919 / 37446) : ℂ) * ζ ^ 8 + ((7379 / 6241) : ℂ) * ζ ^ 9 + ((3274 / 18723) : ℂ) * ζ ^ 10 - ((9033 / 12482) : ℂ) * ζ ^ 11 + ((1977 / 6241) : ℂ) * ζ ^ 12 - ((3337 / 37446) : ℂ) * ζ ^ 13 - ((31369 / 37446) : ℂ) * ζ ^ 14 - ((48329 / 37446) : ℂ) * ζ ^ 15 - ((5630 / 18723) : ℂ) * ζ ^ 16 + ((2018 / 18723) : ℂ) * ζ ^ 17 + ((415 / 12482) : ℂ) * ζ ^ 18 - ((2483 / 37446) : ℂ) * ζ ^ 19 + ((3558 / 6241) : ℂ) * ζ ^ 20 + ((39823 / 37446) : ℂ) * ζ ^ 21 + ((11171 / 37446) : ℂ) * ζ ^ 22 + ((2847 / 12482) : ℂ) * ζ ^ 23 - ((11891 / 37446) : ℂ) * ζ ^ 24 + ((3545 / 37446) : ℂ) * ζ ^ 25 + ((1546 / 18723) : ℂ) * ζ ^ 26 - ((1187 / 37446) : ℂ) * ζ ^ 27 - ((1985 / 12482) : ℂ) * ζ ^ 28 - ((745 / 18723) : ℂ) * ζ ^ 29 + ((2429 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep04Coefficient09 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep04CoefficientIdentity09 :
    row18_reducedY54_combinationStep04Coefficient09 =
      row18_reducedY54_combinationStep03Coefficient09 +
        row18_reducedY54_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep04Coefficient09 row18_reducedY54_combinationStep03Coefficient09 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep04Coefficient10 : ℂ :=
  (((53 / 158) : ℂ) + ((26 / 237) : ℂ) * ζ ^ 1 - ((20 / 237) : ℂ) * ζ ^ 2 + ((67 / 237) : ℂ) * ζ ^ 3 + ((149 / 474) : ℂ) * ζ ^ 5 + ((25 / 237) : ℂ) * ζ ^ 6 - ((64 / 237) : ℂ) * ζ ^ 8 - ((2 / 237) : ℂ) * ζ ^ 9 - ((23 / 79) : ℂ) * ζ ^ 11 - ((64 / 237) : ℂ) * ζ ^ 12 - ((26 / 237) : ℂ) * ζ ^ 13 - ((37 / 474) : ℂ) * ζ ^ 15 - ((26 / 237) : ℂ) * ζ ^ 17 - ((15 / 79) : ℂ) * ζ ^ 18 - ((31 / 79) : ℂ) * ζ ^ 21 + ((20 / 237) : ℂ) * ζ ^ 22 - ((97 / 474) : ℂ) * ζ ^ 25 + ((31 / 79) : ℂ) * ζ ^ 27 + ((64 / 237) : ℂ) * ζ ^ 28 + ((26 / 237) : ℂ) * ζ ^ 29 + ((25 / 474) : ℂ) * ζ ^ 30 + ((23 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep04CoefficientIdentity10 :
    row18_reducedY54_combinationStep04Coefficient10 =
      row18_reducedY54_combinationStep03Coefficient10 +
        row18_reducedY54_combinationStep04Multiplier *
          (-((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep04Coefficient10 row18_reducedY54_combinationStep03Coefficient10 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 (((2773 / 37446) : ℂ) - ((7441 / 37446) : ℂ) * ζ ^ 1 + ((6309 / 12482) : ℂ) * ζ ^ 2 - ((2647 / 12482) : ℂ) * ζ ^ 3 + ((805 / 37446) : ℂ) * ζ ^ 4 - ((236 / 237) : ℂ) * ζ ^ 5 - ((21233 / 37446) : ℂ) * ζ ^ 6 - ((3004 / 18723) : ℂ) * ζ ^ 7 - ((6627 / 12482) : ℂ) * ζ ^ 8 + ((15629 / 37446) : ℂ) * ζ ^ 9 + ((5555 / 12482) : ℂ) * ζ ^ 10 + ((14785 / 18723) : ℂ) * ζ ^ 11 + ((22459 / 37446) : ℂ) * ζ ^ 12 + ((19741 / 37446) : ℂ) * ζ ^ 13 - ((16807 / 37446) : ℂ) * ζ ^ 14 - ((4462 / 6241) : ℂ) * ζ ^ 15 - ((9259 / 37446) : ℂ) * ζ ^ 16 - ((7310 / 18723) : ℂ) * ζ ^ 17 - ((12271 / 37446) : ℂ) * ζ ^ 18 - ((2561 / 18723) : ℂ) * ζ ^ 19 + ((5344 / 18723) : ℂ) * ζ ^ 20 + ((17180 / 18723) : ℂ) * ζ ^ 21 - ((10897 / 37446) : ℂ) * ζ ^ 22 - ((8245 / 37446) : ℂ) * ζ ^ 23 + ((1244 / 6241) : ℂ) * ζ ^ 24 - ((2329 / 37446) : ℂ) * ζ ^ 25 - ((1577 / 12482) : ℂ) * ζ ^ 26 - ((5759 / 12482) : ℂ) * ζ ^ 27 + ((9503 / 37446) : ℂ) * ζ ^ 28 + ((1084 / 6241) : ℂ) * ζ ^ 29 - ((1735 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep04Coefficient11 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep04CoefficientIdentity11 :
    row18_reducedY54_combinationStep04Coefficient11 =
      row18_reducedY54_combinationStep03Coefficient11 +
        row18_reducedY54_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep04Coefficient11 row18_reducedY54_combinationStep03Coefficient11 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep04Coefficient12 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep04CoefficientIdentity12 :
    row18_reducedY54_combinationStep04Coefficient12 =
      row18_reducedY54_combinationStep03Coefficient12 +
        row18_reducedY54_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep04Coefficient12 row18_reducedY54_combinationStep03Coefficient12 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep04Coefficient13 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep04CoefficientIdentity13 :
    row18_reducedY54_combinationStep04Coefficient13 =
      row18_reducedY54_combinationStep03Coefficient13 +
        row18_reducedY54_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep04Coefficient13 row18_reducedY54_combinationStep03Coefficient13 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep04Coefficient14 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep04CoefficientIdentity14 :
    row18_reducedY54_combinationStep04Coefficient14 =
      row18_reducedY54_combinationStep03Coefficient14 +
        row18_reducedY54_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep04Coefficient14 row18_reducedY54_combinationStep03Coefficient14 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep04Coefficient15 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep04CoefficientIdentity15 :
    row18_reducedY54_combinationStep04Coefficient15 =
      row18_reducedY54_combinationStep03Coefficient15 +
        row18_reducedY54_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep04Coefficient15 row18_reducedY54_combinationStep03Coefficient15 row18_reducedY54_combinationStep04Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY54_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY54_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY54_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY54_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY54_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY54_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY54_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY54_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY54_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY54_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY54_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY54_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY54_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY54_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY54_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY54_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY54_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY54_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation04
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY54_combinationStep04CoefficientIdentity00,
      row18_reducedY54_combinationStep04CoefficientIdentity01,
      row18_reducedY54_combinationStep04CoefficientIdentity02,
      row18_reducedY54_combinationStep04CoefficientIdentity03,
      row18_reducedY54_combinationStep04CoefficientIdentity04,
      row18_reducedY54_combinationStep04CoefficientIdentity05,
      row18_reducedY54_combinationStep04CoefficientIdentity06,
      row18_reducedY54_combinationStep04CoefficientIdentity07,
      row18_reducedY54_combinationStep04CoefficientIdentity08,
      row18_reducedY54_combinationStep04CoefficientIdentity09,
      row18_reducedY54_combinationStep04CoefficientIdentity10,
      row18_reducedY54_combinationStep04CoefficientIdentity11,
      row18_reducedY54_combinationStep04CoefficientIdentity12,
      row18_reducedY54_combinationStep04CoefficientIdentity13,
      row18_reducedY54_combinationStep04CoefficientIdentity14,
      row18_reducedY54_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY54_combinationStep04Multiplier * equation

private def row18_reducedY54_combinationStep05Multiplier : ℂ :=
  (-((4462 / 237) : ℂ) - ((16666 / 1185) : ℂ) * ζ ^ 1 + ((1912 / 1185) : ℂ) * ζ ^ 2 + ((7778 / 395) : ℂ) * ζ ^ 3 - ((10348 / 1185) : ℂ) * ζ ^ 5 - ((5484 / 395) : ℂ) * ζ ^ 6 + ((1862 / 237) : ℂ) * ζ ^ 8 + ((15502 / 1185) : ℂ) * ζ ^ 9 - ((7832 / 1185) : ℂ) * ζ ^ 11 + ((1862 / 237) : ℂ) * ζ ^ 12 + ((16666 / 1185) : ℂ) * ζ ^ 13 - ((5672 / 395) : ℂ) * ζ ^ 15 + ((16666 / 1185) : ℂ) * ζ ^ 17 + ((18364 / 1185) : ℂ) * ζ ^ 18 - ((6668 / 1185) : ℂ) * ζ ^ 21 - ((1912 / 1185) : ℂ) * ζ ^ 22 - ((2106 / 395) : ℂ) * ζ ^ 25 + ((6668 / 1185) : ℂ) * ζ ^ 27 - ((1862 / 237) : ℂ) * ζ ^ 28 - ((16666 / 1185) : ℂ) * ζ ^ 29 - ((2742 / 395) : ℂ) * ζ ^ 30 + ((7832 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY54_combinationStep05Coefficient00 : ℂ :=
  (-((51 / 10) : ℂ) - ((5 / 2) : ℂ) * ζ ^ 1 + ((9 / 5) : ℂ) * ζ ^ 2 + ((23 / 5) : ℂ) * ζ ^ 3 - ((5 / 2) : ℂ) * ζ ^ 5 - ((33 / 10) : ℂ) * ζ ^ 6 + ((33 / 10) : ℂ) * ζ ^ 8 + ((5 / 2) : ℂ) * ζ ^ 9 - ((23 / 10) : ℂ) * ζ ^ 11 + ((19 / 10) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 13 - ((39 / 10) : ℂ) * ζ ^ 15 + ((5 / 2) : ℂ) * ζ ^ 17 + ((13 / 5) : ℂ) * ζ ^ 18 - ((5 / 2) : ℂ) * ζ ^ 21 - ((9 / 5) : ℂ) * ζ ^ 22 - ((7 / 10) : ℂ) * ζ ^ 24 + ((7 / 10) : ℂ) * ζ ^ 27 - ((33 / 10) : ℂ) * ζ ^ 28 - ((5 / 2) : ℂ) * ζ ^ 29 - ((7 / 5) : ℂ) * ζ ^ 30 + ((23 / 10) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep05CoefficientIdentity00 :
    row18_reducedY54_combinationStep05Coefficient00 =
      row18_reducedY54_combinationStep04Coefficient00 +
        row18_reducedY54_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep05Coefficient00 row18_reducedY54_combinationStep04Coefficient00 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep05Coefficient01 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep05CoefficientIdentity01 :
    row18_reducedY54_combinationStep05Coefficient01 =
      row18_reducedY54_combinationStep04Coefficient01 +
        row18_reducedY54_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep05Coefficient01 row18_reducedY54_combinationStep04Coefficient01 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep05Coefficient02 : ℂ :=
  (((1232 / 237) : ℂ) - ((169 / 395) : ℂ) * ζ ^ 1 - ((7767 / 790) : ℂ) * ζ ^ 2 - ((7462 / 1185) : ℂ) * ζ ^ 3 + ((4924 / 1185) : ℂ) * ζ ^ 5 - ((7942 / 1185) : ℂ) * ζ ^ 6 - ((2473 / 474) : ℂ) * ζ ^ 8 + ((1898 / 395) : ℂ) * ζ ^ 9 + ((13156 / 1185) : ℂ) * ζ ^ 11 - ((2473 / 474) : ℂ) * ζ ^ 12 + ((169 / 395) : ℂ) * ζ ^ 13 + ((12893 / 1185) : ℂ) * ζ ^ 15 + ((169 / 395) : ℂ) * ζ ^ 17 - ((7417 / 2370) : ℂ) * ζ ^ 18 + ((7969 / 1185) : ℂ) * ζ ^ 21 + ((7767 / 790) : ℂ) * ζ ^ 22 - ((5431 / 1185) : ℂ) * ζ ^ 25 - ((7969 / 1185) : ℂ) * ζ ^ 27 + ((2473 / 474) : ℂ) * ζ ^ 28 - ((169 / 395) : ℂ) * ζ ^ 29 - ((3971 / 1185) : ℂ) * ζ ^ 30 - ((13156 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep05CoefficientIdentity02 :
    row18_reducedY54_combinationStep05Coefficient02 =
      row18_reducedY54_combinationStep04Coefficient02 +
        row18_reducedY54_combinationStep05Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep05Coefficient02 row18_reducedY54_combinationStep04Coefficient02 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 (((67027 / 18723) : ℂ) + ((266747 / 187230) : ℂ) * ζ ^ 1 + ((651569 / 187230) : ℂ) * ζ ^ 2 + ((703 / 31205) : ℂ) * ζ ^ 3 - ((639859 / 187230) : ℂ) * ζ ^ 4 - ((258453 / 62410) : ℂ) * ζ ^ 5 + ((15186 / 31205) : ℂ) * ζ ^ 6 + ((296789 / 93615) : ℂ) * ζ ^ 7 + ((371051 / 187230) : ℂ) * ζ ^ 8 - ((81691 / 187230) : ℂ) * ζ ^ 9 - ((84884 / 93615) : ℂ) * ζ ^ 10 - ((36569 / 187230) : ℂ) * ζ ^ 11 - ((19387 / 18723) : ℂ) * ζ ^ 12 - ((54409 / 93615) : ℂ) * ζ ^ 13 - ((50773 / 187230) : ℂ) * ζ ^ 14 + ((259664 / 93615) : ℂ) * ζ ^ 15 + ((198481 / 62410) : ℂ) * ζ ^ 16 + ((212413 / 187230) : ℂ) * ζ ^ 17 + ((80423 / 187230) : ℂ) * ζ ^ 18 - ((238051 / 93615) : ℂ) * ζ ^ 19 - ((272621 / 93615) : ℂ) * ζ ^ 20 + ((6086 / 31205) : ℂ) * ζ ^ 21 - ((410929 / 187230) : ℂ) * ζ ^ 22 - ((22651 / 31205) : ℂ) * ζ ^ 23 + ((28717 / 31205) : ℂ) * ζ ^ 24 + ((16925 / 12482) : ℂ) * ζ ^ 25 + ((84766 / 93615) : ℂ) * ζ ^ 26 - ((22829 / 37446) : ℂ) * ζ ^ 27 - ((3889 / 93615) : ℂ) * ζ ^ 28 - ((761 / 1185) : ℂ) * ζ ^ 29 + ((27412 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep05Coefficient03 : ℂ :=
  (-((1900 / 237) : ℂ) - ((1703 / 237) : ℂ) * ζ ^ 1 - ((91 / 474) : ℂ) * ζ ^ 2 + ((1715 / 237) : ℂ) * ζ ^ 3 - ((1703 / 237) : ℂ) * ζ ^ 5 - ((1297 / 158) : ℂ) * ζ ^ 6 + ((1297 / 158) : ℂ) * ζ ^ 8 + ((1703 / 237) : ℂ) * ζ ^ 9 - ((1715 / 474) : ℂ) * ζ ^ 11 + ((453 / 79) : ℂ) * ζ ^ 12 + ((1703 / 237) : ℂ) * ζ ^ 13 - ((1874 / 237) : ℂ) * ζ ^ 15 + ((1703 / 237) : ℂ) * ζ ^ 17 + ((590 / 79) : ℂ) * ζ ^ 18 - ((125 / 474) : ℂ) * ζ ^ 21 + ((91 / 474) : ℂ) * ζ ^ 22 - ((117 / 158) : ℂ) * ζ ^ 24 - ((53 / 79) : ℂ) * ζ ^ 27 - ((1297 / 158) : ℂ) * ζ ^ 28 - ((1703 / 237) : ℂ) * ζ ^ 29 - ((391 / 158) : ℂ) * ζ ^ 30 + ((1715 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep05CoefficientIdentity03 :
    row18_reducedY54_combinationStep05Coefficient03 =
      row18_reducedY54_combinationStep04Coefficient03 +
        row18_reducedY54_combinationStep05Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep05Coefficient03 row18_reducedY54_combinationStep04Coefficient03 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 (-((55363 / 18723) : ℂ) + ((213064 / 93615) : ℂ) * ζ ^ 1 + ((264652 / 93615) : ℂ) * ζ ^ 2 + ((50993 / 93615) : ℂ) * ζ ^ 3 - ((215373 / 62410) : ℂ) * ζ ^ 4 + ((34783 / 18723) : ℂ) * ζ ^ 5 - ((222028 / 93615) : ℂ) * ζ ^ 6 - ((30096 / 31205) : ℂ) * ζ ^ 7 + ((106704 / 31205) : ℂ) * ζ ^ 8 + ((136333 / 187230) : ℂ) * ζ ^ 9 - ((171989 / 62410) : ℂ) * ζ ^ 10 - ((52859 / 62410) : ℂ) * ζ ^ 11 + ((398903 / 187230) : ℂ) * ζ ^ 12 - ((371791 / 187230) : ℂ) * ζ ^ 13 - ((4429 / 1185) : ℂ) * ζ ^ 14 - ((17952 / 31205) : ℂ) * ζ ^ 15 + ((519907 / 187230) : ℂ) * ζ ^ 16 - ((53071 / 187230) : ℂ) * ζ ^ 17 - ((422086 / 93615) : ℂ) * ζ ^ 18 - ((741047 / 187230) : ℂ) * ζ ^ 19 + ((26439 / 31205) : ℂ) * ζ ^ 20 - ((1020539 / 187230) : ℂ) * ζ ^ 21 - ((354143 / 187230) : ℂ) * ζ ^ 22 + ((62279 / 31205) : ℂ) * ζ ^ 23 - ((9092 / 18723) : ℂ) * ζ ^ 24 - ((132581 / 93615) : ℂ) * ζ ^ 25 + ((159883 / 187230) : ℂ) * ζ ^ 26 + ((72278 / 93615) : ℂ) * ζ ^ 27 - ((221097 / 62410) : ℂ) * ζ ^ 28 + ((10533 / 12482) : ℂ) * ζ ^ 29 + ((25454 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep05Coefficient04 : ℂ :=
  (((51 / 10) : ℂ) + ((5 / 2) : ℂ) * ζ ^ 1 - ((9 / 5) : ℂ) * ζ ^ 2 - ((23 / 5) : ℂ) * ζ ^ 3 + ((5 / 2) : ℂ) * ζ ^ 5 + ((33 / 10) : ℂ) * ζ ^ 6 - ((33 / 10) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 9 + ((23 / 10) : ℂ) * ζ ^ 11 - ((19 / 10) : ℂ) * ζ ^ 12 - ((5 / 2) : ℂ) * ζ ^ 13 + ((39 / 10) : ℂ) * ζ ^ 15 - ((5 / 2) : ℂ) * ζ ^ 17 - ((13 / 5) : ℂ) * ζ ^ 18 + ((5 / 2) : ℂ) * ζ ^ 21 + ((9 / 5) : ℂ) * ζ ^ 22 + ((7 / 10) : ℂ) * ζ ^ 24 - ((7 / 10) : ℂ) * ζ ^ 27 + ((33 / 10) : ℂ) * ζ ^ 28 + ((5 / 2) : ℂ) * ζ ^ 29 + ((7 / 5) : ℂ) * ζ ^ 30 - ((23 / 10) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep05CoefficientIdentity04 :
    row18_reducedY54_combinationStep05Coefficient04 =
      row18_reducedY54_combinationStep04Coefficient04 +
        row18_reducedY54_combinationStep05Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep05Coefficient04 row18_reducedY54_combinationStep04Coefficient04 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 (((55363 / 18723) : ℂ) - ((213064 / 93615) : ℂ) * ζ ^ 1 - ((264652 / 93615) : ℂ) * ζ ^ 2 - ((50993 / 93615) : ℂ) * ζ ^ 3 + ((215373 / 62410) : ℂ) * ζ ^ 4 - ((34783 / 18723) : ℂ) * ζ ^ 5 + ((222028 / 93615) : ℂ) * ζ ^ 6 + ((30096 / 31205) : ℂ) * ζ ^ 7 - ((106704 / 31205) : ℂ) * ζ ^ 8 - ((136333 / 187230) : ℂ) * ζ ^ 9 + ((171989 / 62410) : ℂ) * ζ ^ 10 + ((52859 / 62410) : ℂ) * ζ ^ 11 - ((398903 / 187230) : ℂ) * ζ ^ 12 + ((371791 / 187230) : ℂ) * ζ ^ 13 + ((4429 / 1185) : ℂ) * ζ ^ 14 + ((17952 / 31205) : ℂ) * ζ ^ 15 - ((519907 / 187230) : ℂ) * ζ ^ 16 + ((53071 / 187230) : ℂ) * ζ ^ 17 + ((422086 / 93615) : ℂ) * ζ ^ 18 + ((741047 / 187230) : ℂ) * ζ ^ 19 - ((26439 / 31205) : ℂ) * ζ ^ 20 + ((1020539 / 187230) : ℂ) * ζ ^ 21 + ((354143 / 187230) : ℂ) * ζ ^ 22 - ((62279 / 31205) : ℂ) * ζ ^ 23 + ((9092 / 18723) : ℂ) * ζ ^ 24 + ((132581 / 93615) : ℂ) * ζ ^ 25 - ((159883 / 187230) : ℂ) * ζ ^ 26 - ((72278 / 93615) : ℂ) * ζ ^ 27 + ((221097 / 62410) : ℂ) * ζ ^ 28 - ((10533 / 12482) : ℂ) * ζ ^ 29 - ((25454 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep05Coefficient05 : ℂ :=
  (((809 / 474) : ℂ) + ((149 / 237) : ℂ) * ζ ^ 1 + ((44 / 79) : ℂ) * ζ ^ 2 - ((65 / 474) : ℂ) * ζ ^ 3 - ((361 / 474) : ℂ) * ζ ^ 5 - ((16 / 237) : ℂ) * ζ ^ 6 + ((52 / 237) : ℂ) * ζ ^ 9 + ((361 / 474) : ℂ) * ζ ^ 11 - ((53 / 79) : ℂ) * ζ ^ 12 - ((149 / 237) : ℂ) * ζ ^ 13 + ((763 / 474) : ℂ) * ζ ^ 15 - ((149 / 237) : ℂ) * ζ ^ 17 - ((280 / 237) : ℂ) * ζ ^ 18 + ((148 / 237) : ℂ) * ζ ^ 21 - ((44 / 79) : ℂ) * ζ ^ 22 + ((809 / 474) : ℂ) * ζ ^ 24 + ((659 / 474) : ℂ) * ζ ^ 25 - ((659 / 474) : ℂ) * ζ ^ 27 + ((149 / 237) : ℂ) * ζ ^ 29 + ((88 / 79) : ℂ) * ζ ^ 30 - ((361 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep05CoefficientIdentity05 :
    row18_reducedY54_combinationStep05Coefficient05 =
      row18_reducedY54_combinationStep04Coefficient05 +
        row18_reducedY54_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep05Coefficient05 row18_reducedY54_combinationStep04Coefficient05 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep05Coefficient06 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep05CoefficientIdentity06 :
    row18_reducedY54_combinationStep05Coefficient06 =
      row18_reducedY54_combinationStep04Coefficient06 +
        row18_reducedY54_combinationStep05Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep05Coefficient06 row18_reducedY54_combinationStep04Coefficient06 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 (-((125306 / 18723) : ℂ) - ((917929 / 62410) : ℂ) * ζ ^ 1 - ((866681 / 187230) : ℂ) * ζ ^ 2 - ((407228 / 93615) : ℂ) * ζ ^ 3 - ((32674 / 31205) : ℂ) * ζ ^ 4 + ((355937 / 37446) : ℂ) * ζ ^ 5 + ((523304 / 31205) : ℂ) * ζ ^ 6 + ((980288 / 93615) : ℂ) * ζ ^ 7 - ((437517 / 62410) : ℂ) * ζ ^ 8 - ((3211289 / 187230) : ℂ) * ζ ^ 9 - ((960579 / 62410) : ℂ) * ζ ^ 10 + ((904 / 6241) : ℂ) * ζ ^ 11 + ((1410938 / 93615) : ℂ) * ζ ^ 12 + ((434102 / 31205) : ℂ) * ζ ^ 13 + ((26263 / 37446) : ℂ) * ζ ^ 14 - ((1844903 / 187230) : ℂ) * ζ ^ 15 - ((188462 / 18723) : ℂ) * ζ ^ 16 - ((94298 / 18723) : ℂ) * ζ ^ 17 - ((243835 / 37446) : ℂ) * ζ ^ 18 - ((346627 / 187230) : ℂ) * ζ ^ 19 + ((1150127 / 187230) : ℂ) * ζ ^ 20 + ((638812 / 93615) : ℂ) * ζ ^ 21 - ((628699 / 187230) : ℂ) * ζ ^ 22 - ((152500 / 18723) : ℂ) * ζ ^ 23 - ((555308 / 93615) : ℂ) * ζ ^ 24 - ((1211 / 790) : ℂ) * ζ ^ 25 + ((1177097 / 187230) : ℂ) * ζ ^ 26 + ((517781 / 187230) : ℂ) * ζ ^ 27 + ((54412 / 93615) : ℂ) * ζ ^ 28 + ((706 / 6241) : ℂ) * ζ ^ 29 - ((54824 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep05Coefficient07 : ℂ :=
  (((3953 / 474) : ℂ) + ((1442 / 237) : ℂ) * ζ ^ 1 - ((139 / 79) : ℂ) * ζ ^ 2 - ((2056 / 237) : ℂ) * ζ ^ 3 + ((1442 / 237) : ℂ) * ζ ^ 5 + ((3119 / 474) : ℂ) * ζ ^ 6 - ((3119 / 474) : ℂ) * ζ ^ 8 - ((1442 / 237) : ℂ) * ζ ^ 9 + ((1028 / 237) : ℂ) * ζ ^ 11 - ((707 / 158) : ℂ) * ζ ^ 12 - ((1442 / 237) : ℂ) * ζ ^ 13 + ((1709 / 237) : ℂ) * ζ ^ 15 - ((1442 / 237) : ℂ) * ζ ^ 17 - ((1481 / 237) : ℂ) * ζ ^ 18 + ((427 / 237) : ℂ) * ζ ^ 21 + ((139 / 79) : ℂ) * ζ ^ 22 + ((157 / 474) : ℂ) * ζ ^ 24 - ((347 / 237) : ℂ) * ζ ^ 27 + ((3119 / 474) : ℂ) * ζ ^ 28 + ((1442 / 237) : ℂ) * ζ ^ 29 + ((499 / 237) : ℂ) * ζ ^ 30 - ((1028 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep05CoefficientIdentity07 :
    row18_reducedY54_combinationStep05Coefficient07 =
      row18_reducedY54_combinationStep04Coefficient07 +
        row18_reducedY54_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep05Coefficient07 row18_reducedY54_combinationStep04Coefficient07 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep05Coefficient08 : ℂ :=
  (-((51 / 158) : ℂ) + ((87 / 79) : ℂ) * ζ ^ 1 + ((925 / 474) : ℂ) * ζ ^ 2 + ((341 / 237) : ℂ) * ζ ^ 3 + ((87 / 79) : ℂ) * ζ ^ 5 + ((386 / 237) : ℂ) * ζ ^ 6 - ((386 / 237) : ℂ) * ζ ^ 8 - ((87 / 79) : ℂ) * ζ ^ 9 - ((341 / 474) : ℂ) * ζ ^ 11 - ((199 / 158) : ℂ) * ζ ^ 12 - ((87 / 79) : ℂ) * ζ ^ 13 + ((55 / 79) : ℂ) * ζ ^ 15 - ((87 / 79) : ℂ) * ζ ^ 17 - ((289 / 237) : ℂ) * ζ ^ 18 - ((243 / 158) : ℂ) * ζ ^ 21 - ((925 / 474) : ℂ) * ζ ^ 22 + ((97 / 237) : ℂ) * ζ ^ 24 + ((506 / 237) : ℂ) * ζ ^ 27 + ((386 / 237) : ℂ) * ζ ^ 28 + ((87 / 79) : ℂ) * ζ ^ 29 + ((175 / 474) : ℂ) * ζ ^ 30 + ((341 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep05CoefficientIdentity08 :
    row18_reducedY54_combinationStep05Coefficient08 =
      row18_reducedY54_combinationStep04Coefficient08 +
        row18_reducedY54_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep05Coefficient08 row18_reducedY54_combinationStep04Coefficient08 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep05Coefficient09 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep05CoefficientIdentity09 :
    row18_reducedY54_combinationStep05Coefficient09 =
      row18_reducedY54_combinationStep04Coefficient09 +
        row18_reducedY54_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep05Coefficient09 row18_reducedY54_combinationStep04Coefficient09 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep05Coefficient10 : ℂ :=
  (((53 / 158) : ℂ) + ((26 / 237) : ℂ) * ζ ^ 1 - ((20 / 237) : ℂ) * ζ ^ 2 + ((67 / 237) : ℂ) * ζ ^ 3 + ((149 / 474) : ℂ) * ζ ^ 5 + ((25 / 237) : ℂ) * ζ ^ 6 - ((64 / 237) : ℂ) * ζ ^ 8 - ((2 / 237) : ℂ) * ζ ^ 9 - ((23 / 79) : ℂ) * ζ ^ 11 - ((64 / 237) : ℂ) * ζ ^ 12 - ((26 / 237) : ℂ) * ζ ^ 13 - ((37 / 474) : ℂ) * ζ ^ 15 - ((26 / 237) : ℂ) * ζ ^ 17 - ((15 / 79) : ℂ) * ζ ^ 18 - ((31 / 79) : ℂ) * ζ ^ 21 + ((20 / 237) : ℂ) * ζ ^ 22 - ((97 / 474) : ℂ) * ζ ^ 25 + ((31 / 79) : ℂ) * ζ ^ 27 + ((64 / 237) : ℂ) * ζ ^ 28 + ((26 / 237) : ℂ) * ζ ^ 29 + ((25 / 474) : ℂ) * ζ ^ 30 + ((23 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep05CoefficientIdentity10 :
    row18_reducedY54_combinationStep05Coefficient10 =
      row18_reducedY54_combinationStep04Coefficient10 +
        row18_reducedY54_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep05Coefficient10 row18_reducedY54_combinationStep04Coefficient10 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep05Coefficient11 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep05CoefficientIdentity11 :
    row18_reducedY54_combinationStep05Coefficient11 =
      row18_reducedY54_combinationStep04Coefficient11 +
        row18_reducedY54_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep05Coefficient11 row18_reducedY54_combinationStep04Coefficient11 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep05Coefficient12 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep05CoefficientIdentity12 :
    row18_reducedY54_combinationStep05Coefficient12 =
      row18_reducedY54_combinationStep04Coefficient12 +
        row18_reducedY54_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep05Coefficient12 row18_reducedY54_combinationStep04Coefficient12 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep05Coefficient13 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep05CoefficientIdentity13 :
    row18_reducedY54_combinationStep05Coefficient13 =
      row18_reducedY54_combinationStep04Coefficient13 +
        row18_reducedY54_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep05Coefficient13 row18_reducedY54_combinationStep04Coefficient13 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep05Coefficient14 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep05CoefficientIdentity14 :
    row18_reducedY54_combinationStep05Coefficient14 =
      row18_reducedY54_combinationStep04Coefficient14 +
        row18_reducedY54_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep05Coefficient14 row18_reducedY54_combinationStep04Coefficient14 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep05Coefficient15 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep05CoefficientIdentity15 :
    row18_reducedY54_combinationStep05Coefficient15 =
      row18_reducedY54_combinationStep04Coefficient15 +
        row18_reducedY54_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep05Coefficient15 row18_reducedY54_combinationStep04Coefficient15 row18_reducedY54_combinationStep05Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY54_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY54_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY54_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY54_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY54_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY54_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY54_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY54_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY54_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY54_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY54_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY54_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY54_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY54_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY54_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY54_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY54_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY54_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY54_combinationStep05CoefficientIdentity00,
      row18_reducedY54_combinationStep05CoefficientIdentity01,
      row18_reducedY54_combinationStep05CoefficientIdentity02,
      row18_reducedY54_combinationStep05CoefficientIdentity03,
      row18_reducedY54_combinationStep05CoefficientIdentity04,
      row18_reducedY54_combinationStep05CoefficientIdentity05,
      row18_reducedY54_combinationStep05CoefficientIdentity06,
      row18_reducedY54_combinationStep05CoefficientIdentity07,
      row18_reducedY54_combinationStep05CoefficientIdentity08,
      row18_reducedY54_combinationStep05CoefficientIdentity09,
      row18_reducedY54_combinationStep05CoefficientIdentity10,
      row18_reducedY54_combinationStep05CoefficientIdentity11,
      row18_reducedY54_combinationStep05CoefficientIdentity12,
      row18_reducedY54_combinationStep05CoefficientIdentity13,
      row18_reducedY54_combinationStep05CoefficientIdentity14,
      row18_reducedY54_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY54_combinationStep05Multiplier * equation

private def row18_reducedY54_combinationStep06Multiplier : ℂ :=
  (((56 / 79) : ℂ) - ((202 / 79) : ℂ) * ζ ^ 1 + ((1036 / 237) : ℂ) * ζ ^ 2 - ((2534 / 237) : ℂ) * ζ ^ 5 + ((868 / 237) : ℂ) * ζ ^ 6 + ((868 / 237) : ℂ) * ζ ^ 8 - ((2534 / 237) : ℂ) * ζ ^ 9 - ((34 / 79) : ℂ) * ζ ^ 11 + ((798 / 79) : ℂ) * ζ ^ 12 + ((202 / 79) : ℂ) * ζ ^ 13 - ((1220 / 237) : ℂ) * ζ ^ 15 + ((202 / 79) : ℂ) * ζ ^ 17 - ((196 / 237) : ℂ) * ζ ^ 18 + ((1570 / 237) : ℂ) * ζ ^ 21 - ((1036 / 237) : ℂ) * ζ ^ 22 - ((224 / 79) : ℂ) * ζ ^ 24 + ((1928 / 237) : ℂ) * ζ ^ 25 + ((1220 / 237) : ℂ) * ζ ^ 27 - ((868 / 237) : ℂ) * ζ ^ 28 - ((202 / 79) : ℂ) * ζ ^ 29 - ((1526 / 237) : ℂ) * ζ ^ 30 + ((34 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY54_combinationStep06Coefficient00 : ℂ :=
  (-((51 / 10) : ℂ) - ((5 / 2) : ℂ) * ζ ^ 1 + ((9 / 5) : ℂ) * ζ ^ 2 + ((23 / 5) : ℂ) * ζ ^ 3 - ((5 / 2) : ℂ) * ζ ^ 5 - ((33 / 10) : ℂ) * ζ ^ 6 + ((33 / 10) : ℂ) * ζ ^ 8 + ((5 / 2) : ℂ) * ζ ^ 9 - ((23 / 10) : ℂ) * ζ ^ 11 + ((19 / 10) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 13 - ((39 / 10) : ℂ) * ζ ^ 15 + ((5 / 2) : ℂ) * ζ ^ 17 + ((13 / 5) : ℂ) * ζ ^ 18 - ((5 / 2) : ℂ) * ζ ^ 21 - ((9 / 5) : ℂ) * ζ ^ 22 - ((7 / 10) : ℂ) * ζ ^ 24 + ((7 / 10) : ℂ) * ζ ^ 27 - ((33 / 10) : ℂ) * ζ ^ 28 - ((5 / 2) : ℂ) * ζ ^ 29 - ((7 / 5) : ℂ) * ζ ^ 30 + ((23 / 10) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep06CoefficientIdentity00 :
    row18_reducedY54_combinationStep06Coefficient00 =
      row18_reducedY54_combinationStep05Coefficient00 +
        row18_reducedY54_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep06Coefficient00 row18_reducedY54_combinationStep05Coefficient00 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep06Coefficient01 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep06CoefficientIdentity01 :
    row18_reducedY54_combinationStep06Coefficient01 =
      row18_reducedY54_combinationStep05Coefficient01 +
        row18_reducedY54_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep06Coefficient01 row18_reducedY54_combinationStep05Coefficient01 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep06Coefficient02 : ℂ :=
  (((58 / 237) : ℂ) - ((789 / 395) : ℂ) * ζ ^ 1 - ((2967 / 790) : ℂ) * ζ ^ 2 - ((323 / 790) : ℂ) * ζ ^ 3 + ((554 / 1185) : ℂ) * ζ ^ 5 - ((5092 / 1185) : ℂ) * ζ ^ 6 - ((233 / 474) : ℂ) * ζ ^ 8 + ((8963 / 2370) : ℂ) * ζ ^ 9 + ((4966 / 1185) : ℂ) * ζ ^ 11 - ((233 / 474) : ℂ) * ζ ^ 12 + ((789 / 395) : ℂ) * ζ ^ 13 + ((6811 / 2370) : ℂ) * ζ ^ 15 + ((789 / 395) : ℂ) * ζ ^ 17 + ((1283 / 2370) : ℂ) * ζ ^ 18 + ((1901 / 790) : ℂ) * ζ ^ 21 + ((2967 / 790) : ℂ) * ζ ^ 22 - ((2921 / 1185) : ℂ) * ζ ^ 25 - ((1901 / 790) : ℂ) * ζ ^ 27 + ((233 / 474) : ℂ) * ζ ^ 28 - ((789 / 395) : ℂ) * ζ ^ 29 - ((2546 / 1185) : ℂ) * ζ ^ 30 - ((4966 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep06CoefficientIdentity02 :
    row18_reducedY54_combinationStep06Coefficient02 =
      row18_reducedY54_combinationStep05Coefficient02 +
        row18_reducedY54_combinationStep06Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep06Coefficient02 row18_reducedY54_combinationStep05Coefficient02 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 (((94342 / 18723) : ℂ) + ((7695 / 6241) : ℂ) * ζ ^ 1 - ((202973 / 37446) : ℂ) * ζ ^ 2 - ((38762 / 6241) : ℂ) * ζ ^ 3 - ((87857 / 18723) : ℂ) * ζ ^ 4 + ((5224 / 6241) : ℂ) * ζ ^ 5 + ((74366 / 18723) : ℂ) * ζ ^ 6 + ((202691 / 37446) : ℂ) * ζ ^ 7 + ((10514 / 6241) : ℂ) * ζ ^ 8 - ((23206 / 18723) : ℂ) * ζ ^ 9 - ((44199 / 12482) : ℂ) * ζ ^ 10 - ((27754 / 18723) : ℂ) * ζ ^ 11 + ((18670 / 18723) : ℂ) * ζ ^ 12 + ((52922 / 18723) : ℂ) * ζ ^ 13 + ((14543 / 12482) : ℂ) * ζ ^ 14 - ((325 / 18723) : ℂ) * ζ ^ 15 - ((61051 / 37446) : ℂ) * ζ ^ 16 - ((13285 / 6241) : ℂ) * ζ ^ 17 - ((89387 / 37446) : ℂ) * ζ ^ 18 - ((304 / 18723) : ℂ) * ζ ^ 19 + ((97787 / 37446) : ℂ) * ζ ^ 20 + ((132719 / 37446) : ℂ) * ζ ^ 21 + ((18079 / 18723) : ℂ) * ζ ^ 22 - ((17627 / 18723) : ℂ) * ζ ^ 23 - ((46855 / 18723) : ℂ) * ζ ^ 24 - ((61957 / 37446) : ℂ) * ζ ^ 25 - ((13933 / 18723) : ℂ) * ζ ^ 26 + ((16991 / 18723) : ℂ) * ζ ^ 27 + ((6751 / 6241) : ℂ) * ζ ^ 28 + ((2999 / 12482) : ℂ) * ζ ^ 29 - ((255 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep06Coefficient03 : ℂ :=
  (((51 / 158) : ℂ) - ((87 / 79) : ℂ) * ζ ^ 1 - ((925 / 474) : ℂ) * ζ ^ 2 - ((341 / 237) : ℂ) * ζ ^ 3 - ((87 / 79) : ℂ) * ζ ^ 5 - ((386 / 237) : ℂ) * ζ ^ 6 + ((386 / 237) : ℂ) * ζ ^ 8 + ((87 / 79) : ℂ) * ζ ^ 9 + ((341 / 474) : ℂ) * ζ ^ 11 + ((199 / 158) : ℂ) * ζ ^ 12 + ((87 / 79) : ℂ) * ζ ^ 13 - ((55 / 79) : ℂ) * ζ ^ 15 + ((87 / 79) : ℂ) * ζ ^ 17 + ((289 / 237) : ℂ) * ζ ^ 18 + ((243 / 158) : ℂ) * ζ ^ 21 + ((925 / 474) : ℂ) * ζ ^ 22 - ((97 / 237) : ℂ) * ζ ^ 24 - ((506 / 237) : ℂ) * ζ ^ 27 - ((386 / 237) : ℂ) * ζ ^ 28 - ((87 / 79) : ℂ) * ζ ^ 29 - ((175 / 474) : ℂ) * ζ ^ 30 - ((341 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep06CoefficientIdentity03 :
    row18_reducedY54_combinationStep06Coefficient03 =
      row18_reducedY54_combinationStep05Coefficient03 +
        row18_reducedY54_combinationStep06Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep06Coefficient03 row18_reducedY54_combinationStep05Coefficient03 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 (-((309599 / 37446) : ℂ) - ((116372 / 18723) : ℂ) * ζ ^ 1 + ((77707 / 37446) : ℂ) * ζ ^ 2 + ((302759 / 37446) : ℂ) * ζ ^ 3 + ((68352 / 6241) : ℂ) * ζ ^ 4 - ((11215 / 6241) : ℂ) * ζ ^ 5 - ((412133 / 37446) : ℂ) * ζ ^ 6 - ((69340 / 6241) : ℂ) * ζ ^ 7 + ((1899 / 6241) : ℂ) * ζ ^ 8 + ((129179 / 18723) : ℂ) * ζ ^ 9 + ((242383 / 37446) : ℂ) * ζ ^ 10 + ((41451 / 12482) : ℂ) * ζ ^ 11 - ((2727 / 6241) : ℂ) * ζ ^ 12 - ((69370 / 18723) : ℂ) * ζ ^ 13 - ((237199 / 37446) : ℂ) * ζ ^ 14 - ((69545 / 18723) : ℂ) * ζ ^ 15 + ((36568 / 18723) : ℂ) * ζ ^ 16 + ((115510 / 18723) : ℂ) * ζ ^ 17 + ((49647 / 12482) : ℂ) * ζ ^ 18 + ((44713 / 37446) : ℂ) * ζ ^ 19 - ((62849 / 12482) : ℂ) * ζ ^ 20 - ((139933 / 37446) : ℂ) * ζ ^ 21 - ((21620 / 18723) : ℂ) * ζ ^ 22 + ((88027 / 18723) : ℂ) * ζ ^ 23 + ((59477 / 18723) : ℂ) * ζ ^ 24 + ((18108 / 6241) : ℂ) * ζ ^ 25 - ((28025 / 37446) : ℂ) * ζ ^ 26 - ((62303 / 37446) : ℂ) * ζ ^ 27 - ((7963 / 12482) : ℂ) * ζ ^ 28 - ((10070 / 18723) : ℂ) * ζ ^ 29 + ((238 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep06Coefficient04 : ℂ :=
  (((51 / 10) : ℂ) + ((5 / 2) : ℂ) * ζ ^ 1 - ((9 / 5) : ℂ) * ζ ^ 2 - ((23 / 5) : ℂ) * ζ ^ 3 + ((5 / 2) : ℂ) * ζ ^ 5 + ((33 / 10) : ℂ) * ζ ^ 6 - ((33 / 10) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 9 + ((23 / 10) : ℂ) * ζ ^ 11 - ((19 / 10) : ℂ) * ζ ^ 12 - ((5 / 2) : ℂ) * ζ ^ 13 + ((39 / 10) : ℂ) * ζ ^ 15 - ((5 / 2) : ℂ) * ζ ^ 17 - ((13 / 5) : ℂ) * ζ ^ 18 + ((5 / 2) : ℂ) * ζ ^ 21 + ((9 / 5) : ℂ) * ζ ^ 22 + ((7 / 10) : ℂ) * ζ ^ 24 - ((7 / 10) : ℂ) * ζ ^ 27 + ((33 / 10) : ℂ) * ζ ^ 28 + ((5 / 2) : ℂ) * ζ ^ 29 + ((7 / 5) : ℂ) * ζ ^ 30 - ((23 / 10) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep06CoefficientIdentity04 :
    row18_reducedY54_combinationStep06Coefficient04 =
      row18_reducedY54_combinationStep05Coefficient04 +
        row18_reducedY54_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep06Coefficient04 row18_reducedY54_combinationStep05Coefficient04 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep06Coefficient05 : ℂ :=
  (((22 / 79) : ℂ) + ((61 / 158) : ℂ) * ζ ^ 1 + ((84 / 79) : ℂ) * ζ ^ 2 + ((78 / 79) : ℂ) * ζ ^ 3 + ((85 / 79) : ℂ) * ζ ^ 5 + ((76 / 79) : ℂ) * ζ ^ 6 + ((335 / 158) : ℂ) * ζ ^ 9 - ((85 / 79) : ℂ) * ζ ^ 11 - ((152 / 79) : ℂ) * ζ ^ 12 - ((61 / 158) : ℂ) * ζ ^ 13 + ((113 / 79) : ℂ) * ζ ^ 15 - ((61 / 158) : ℂ) * ζ ^ 17 - ((92 / 79) : ℂ) * ζ ^ 18 - ((7 / 79) : ℂ) * ζ ^ 21 - ((84 / 79) : ℂ) * ζ ^ 22 + ((22 / 79) : ℂ) * ζ ^ 24 - ((109 / 158) : ℂ) * ζ ^ 25 + ((109 / 158) : ℂ) * ζ ^ 27 + ((61 / 158) : ℂ) * ζ ^ 29 + ((168 / 79) : ℂ) * ζ ^ 30 + ((85 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep06CoefficientIdentity05 :
    row18_reducedY54_combinationStep06Coefficient05 =
      row18_reducedY54_combinationStep05Coefficient05 +
        row18_reducedY54_combinationStep06Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep06Coefficient05 row18_reducedY54_combinationStep05Coefficient05 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 (((47687 / 37446) : ℂ) + ((18566 / 18723) : ℂ) * ζ ^ 1 - ((27071 / 12482) : ℂ) * ζ ^ 2 + ((411 / 6241) : ℂ) * ζ ^ 3 - ((44471 / 37446) : ℂ) * ζ ^ 4 - ((4141 / 6241) : ℂ) * ζ ^ 5 - ((42429 / 12482) : ℂ) * ζ ^ 6 + ((113491 / 37446) : ℂ) * ζ ^ 7 + ((9709 / 37446) : ℂ) * ζ ^ 8 + ((5987 / 6241) : ℂ) * ζ ^ 9 - ((12925 / 18723) : ℂ) * ζ ^ 10 + ((25867 / 18723) : ℂ) * ζ ^ 11 - ((1619 / 12482) : ℂ) * ζ ^ 12 + ((1904 / 18723) : ℂ) * ζ ^ 13 - ((434 / 18723) : ℂ) * ζ ^ 14 - ((7447 / 18723) : ℂ) * ζ ^ 15 - ((44063 / 37446) : ℂ) * ζ ^ 16 - ((68599 / 37446) : ℂ) * ζ ^ 17 + ((87 / 158) : ℂ) * ζ ^ 18 + ((29327 / 37446) : ℂ) * ζ ^ 19 + ((7624 / 6241) : ℂ) * ζ ^ 20 - ((4415 / 12482) : ℂ) * ζ ^ 21 + ((136481 / 37446) : ℂ) * ζ ^ 22 - ((8506 / 6241) : ℂ) * ζ ^ 23 + ((4353 / 6241) : ℂ) * ζ ^ 24 - ((47257 / 37446) : ℂ) * ζ ^ 25 + ((24760 / 18723) : ℂ) * ζ ^ 26 - ((46829 / 37446) : ℂ) * ζ ^ 27 + ((8246 / 6241) : ℂ) * ζ ^ 28 + ((7165 / 37446) : ℂ) * ζ ^ 29 - ((221 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep06Coefficient06 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep06CoefficientIdentity06 :
    row18_reducedY54_combinationStep06Coefficient06 =
      row18_reducedY54_combinationStep05Coefficient06 +
        row18_reducedY54_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep06Coefficient06 row18_reducedY54_combinationStep05Coefficient06 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep06Coefficient07 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep06CoefficientIdentity07 :
    row18_reducedY54_combinationStep06Coefficient07 =
      row18_reducedY54_combinationStep05Coefficient07 +
        row18_reducedY54_combinationStep06Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep06Coefficient07 row18_reducedY54_combinationStep05Coefficient07 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 (((309599 / 37446) : ℂ) + ((116372 / 18723) : ℂ) * ζ ^ 1 - ((77707 / 37446) : ℂ) * ζ ^ 2 - ((302759 / 37446) : ℂ) * ζ ^ 3 - ((68352 / 6241) : ℂ) * ζ ^ 4 + ((11215 / 6241) : ℂ) * ζ ^ 5 + ((412133 / 37446) : ℂ) * ζ ^ 6 + ((69340 / 6241) : ℂ) * ζ ^ 7 - ((1899 / 6241) : ℂ) * ζ ^ 8 - ((129179 / 18723) : ℂ) * ζ ^ 9 - ((242383 / 37446) : ℂ) * ζ ^ 10 - ((41451 / 12482) : ℂ) * ζ ^ 11 + ((2727 / 6241) : ℂ) * ζ ^ 12 + ((69370 / 18723) : ℂ) * ζ ^ 13 + ((237199 / 37446) : ℂ) * ζ ^ 14 + ((69545 / 18723) : ℂ) * ζ ^ 15 - ((36568 / 18723) : ℂ) * ζ ^ 16 - ((115510 / 18723) : ℂ) * ζ ^ 17 - ((49647 / 12482) : ℂ) * ζ ^ 18 - ((44713 / 37446) : ℂ) * ζ ^ 19 + ((62849 / 12482) : ℂ) * ζ ^ 20 + ((139933 / 37446) : ℂ) * ζ ^ 21 + ((21620 / 18723) : ℂ) * ζ ^ 22 - ((88027 / 18723) : ℂ) * ζ ^ 23 - ((59477 / 18723) : ℂ) * ζ ^ 24 - ((18108 / 6241) : ℂ) * ζ ^ 25 + ((28025 / 37446) : ℂ) * ζ ^ 26 + ((62303 / 37446) : ℂ) * ζ ^ 27 + ((7963 / 12482) : ℂ) * ζ ^ 28 + ((10070 / 18723) : ℂ) * ζ ^ 29 - ((238 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep06Coefficient08 : ℂ :=
  (-((51 / 158) : ℂ) + ((87 / 79) : ℂ) * ζ ^ 1 + ((925 / 474) : ℂ) * ζ ^ 2 + ((341 / 237) : ℂ) * ζ ^ 3 + ((87 / 79) : ℂ) * ζ ^ 5 + ((386 / 237) : ℂ) * ζ ^ 6 - ((386 / 237) : ℂ) * ζ ^ 8 - ((87 / 79) : ℂ) * ζ ^ 9 - ((341 / 474) : ℂ) * ζ ^ 11 - ((199 / 158) : ℂ) * ζ ^ 12 - ((87 / 79) : ℂ) * ζ ^ 13 + ((55 / 79) : ℂ) * ζ ^ 15 - ((87 / 79) : ℂ) * ζ ^ 17 - ((289 / 237) : ℂ) * ζ ^ 18 - ((243 / 158) : ℂ) * ζ ^ 21 - ((925 / 474) : ℂ) * ζ ^ 22 + ((97 / 237) : ℂ) * ζ ^ 24 + ((506 / 237) : ℂ) * ζ ^ 27 + ((386 / 237) : ℂ) * ζ ^ 28 + ((87 / 79) : ℂ) * ζ ^ 29 + ((175 / 474) : ℂ) * ζ ^ 30 + ((341 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep06CoefficientIdentity08 :
    row18_reducedY54_combinationStep06Coefficient08 =
      row18_reducedY54_combinationStep05Coefficient08 +
        row18_reducedY54_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep06Coefficient08 row18_reducedY54_combinationStep05Coefficient08 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep06Coefficient09 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep06CoefficientIdentity09 :
    row18_reducedY54_combinationStep06Coefficient09 =
      row18_reducedY54_combinationStep05Coefficient09 +
        row18_reducedY54_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep06Coefficient09 row18_reducedY54_combinationStep05Coefficient09 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep06Coefficient10 : ℂ :=
  (((53 / 158) : ℂ) + ((26 / 237) : ℂ) * ζ ^ 1 - ((20 / 237) : ℂ) * ζ ^ 2 + ((67 / 237) : ℂ) * ζ ^ 3 + ((149 / 474) : ℂ) * ζ ^ 5 + ((25 / 237) : ℂ) * ζ ^ 6 - ((64 / 237) : ℂ) * ζ ^ 8 - ((2 / 237) : ℂ) * ζ ^ 9 - ((23 / 79) : ℂ) * ζ ^ 11 - ((64 / 237) : ℂ) * ζ ^ 12 - ((26 / 237) : ℂ) * ζ ^ 13 - ((37 / 474) : ℂ) * ζ ^ 15 - ((26 / 237) : ℂ) * ζ ^ 17 - ((15 / 79) : ℂ) * ζ ^ 18 - ((31 / 79) : ℂ) * ζ ^ 21 + ((20 / 237) : ℂ) * ζ ^ 22 - ((97 / 474) : ℂ) * ζ ^ 25 + ((31 / 79) : ℂ) * ζ ^ 27 + ((64 / 237) : ℂ) * ζ ^ 28 + ((26 / 237) : ℂ) * ζ ^ 29 + ((25 / 474) : ℂ) * ζ ^ 30 + ((23 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep06CoefficientIdentity10 :
    row18_reducedY54_combinationStep06Coefficient10 =
      row18_reducedY54_combinationStep05Coefficient10 +
        row18_reducedY54_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep06Coefficient10 row18_reducedY54_combinationStep05Coefficient10 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep06Coefficient11 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep06CoefficientIdentity11 :
    row18_reducedY54_combinationStep06Coefficient11 =
      row18_reducedY54_combinationStep05Coefficient11 +
        row18_reducedY54_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep06Coefficient11 row18_reducedY54_combinationStep05Coefficient11 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep06Coefficient12 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep06CoefficientIdentity12 :
    row18_reducedY54_combinationStep06Coefficient12 =
      row18_reducedY54_combinationStep05Coefficient12 +
        row18_reducedY54_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep06Coefficient12 row18_reducedY54_combinationStep05Coefficient12 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep06Coefficient13 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep06CoefficientIdentity13 :
    row18_reducedY54_combinationStep06Coefficient13 =
      row18_reducedY54_combinationStep05Coefficient13 +
        row18_reducedY54_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep06Coefficient13 row18_reducedY54_combinationStep05Coefficient13 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep06Coefficient14 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep06CoefficientIdentity14 :
    row18_reducedY54_combinationStep06Coefficient14 =
      row18_reducedY54_combinationStep05Coefficient14 +
        row18_reducedY54_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep06Coefficient14 row18_reducedY54_combinationStep05Coefficient14 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep06Coefficient15 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep06CoefficientIdentity15 :
    row18_reducedY54_combinationStep06Coefficient15 =
      row18_reducedY54_combinationStep05Coefficient15 +
        row18_reducedY54_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep06Coefficient15 row18_reducedY54_combinationStep05Coefficient15 row18_reducedY54_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY54_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY54_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY54_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY54_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY54_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY54_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY54_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY54_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY54_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY54_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY54_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY54_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY54_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY54_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY54_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY54_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY54_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY54_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY54_combinationStep06CoefficientIdentity00,
      row18_reducedY54_combinationStep06CoefficientIdentity01,
      row18_reducedY54_combinationStep06CoefficientIdentity02,
      row18_reducedY54_combinationStep06CoefficientIdentity03,
      row18_reducedY54_combinationStep06CoefficientIdentity04,
      row18_reducedY54_combinationStep06CoefficientIdentity05,
      row18_reducedY54_combinationStep06CoefficientIdentity06,
      row18_reducedY54_combinationStep06CoefficientIdentity07,
      row18_reducedY54_combinationStep06CoefficientIdentity08,
      row18_reducedY54_combinationStep06CoefficientIdentity09,
      row18_reducedY54_combinationStep06CoefficientIdentity10,
      row18_reducedY54_combinationStep06CoefficientIdentity11,
      row18_reducedY54_combinationStep06CoefficientIdentity12,
      row18_reducedY54_combinationStep06CoefficientIdentity13,
      row18_reducedY54_combinationStep06CoefficientIdentity14,
      row18_reducedY54_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY54_combinationStep06Multiplier * equation

private def row18_reducedY54_combinationStep07Multiplier : ℂ :=
  (((1102 / 237) : ℂ) + ((728 / 237) : ℂ) * ζ ^ 1 - ((406 / 237) : ℂ) * ζ ^ 2 - ((592 / 237) : ℂ) * ζ ^ 3 + ((232 / 79) : ℂ) * ζ ^ 5 - ((1618 / 237) : ℂ) * ζ ^ 8 - ((236 / 79) : ℂ) * ζ ^ 9 + ((1300 / 237) : ℂ) * ζ ^ 11 - ((586 / 237) : ℂ) * ζ ^ 12 - ((728 / 237) : ℂ) * ζ ^ 13 + ((208 / 79) : ℂ) * ζ ^ 15 - ((728 / 237) : ℂ) * ζ ^ 17 + ((406 / 237) : ℂ) * ζ ^ 18 - ((440 / 79) : ℂ) * ζ ^ 21 + ((406 / 237) : ℂ) * ζ ^ 22 + ((2204 / 237) : ℂ) * ζ ^ 24 + ((32 / 237) : ℂ) * ζ ^ 25 - ((440 / 79) : ℂ) * ζ ^ 27 + ((1618 / 237) : ℂ) * ζ ^ 28 + ((728 / 237) : ℂ) * ζ ^ 29 + ((82 / 237) : ℂ) * ζ ^ 30 - ((1300 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY54_combinationStep07Coefficient00 : ℂ :=
  (-((51 / 10) : ℂ) - ((5 / 2) : ℂ) * ζ ^ 1 + ((9 / 5) : ℂ) * ζ ^ 2 + ((23 / 5) : ℂ) * ζ ^ 3 - ((5 / 2) : ℂ) * ζ ^ 5 - ((33 / 10) : ℂ) * ζ ^ 6 + ((33 / 10) : ℂ) * ζ ^ 8 + ((5 / 2) : ℂ) * ζ ^ 9 - ((23 / 10) : ℂ) * ζ ^ 11 + ((19 / 10) : ℂ) * ζ ^ 12 + ((5 / 2) : ℂ) * ζ ^ 13 - ((39 / 10) : ℂ) * ζ ^ 15 + ((5 / 2) : ℂ) * ζ ^ 17 + ((13 / 5) : ℂ) * ζ ^ 18 - ((5 / 2) : ℂ) * ζ ^ 21 - ((9 / 5) : ℂ) * ζ ^ 22 - ((7 / 10) : ℂ) * ζ ^ 24 + ((7 / 10) : ℂ) * ζ ^ 27 - ((33 / 10) : ℂ) * ζ ^ 28 - ((5 / 2) : ℂ) * ζ ^ 29 - ((7 / 5) : ℂ) * ζ ^ 30 + ((23 / 10) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep07CoefficientIdentity00 :
    row18_reducedY54_combinationStep07Coefficient00 =
      row18_reducedY54_combinationStep06Coefficient00 +
        row18_reducedY54_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep07Coefficient00 row18_reducedY54_combinationStep06Coefficient00 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep07Coefficient01 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep07CoefficientIdentity01 :
    row18_reducedY54_combinationStep07Coefficient01 =
      row18_reducedY54_combinationStep06Coefficient01 +
        row18_reducedY54_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep07Coefficient01 row18_reducedY54_combinationStep06Coefficient01 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep07Coefficient02 : ℂ :=
  (((73 / 79) : ℂ) + ((91 / 395) : ℂ) * ζ ^ 1 + ((583 / 790) : ℂ) * ζ ^ 2 - ((163 / 790) : ℂ) * ζ ^ 3 + ((561 / 790) : ℂ) * ζ ^ 5 + ((396 / 395) : ℂ) * ζ ^ 6 + ((35 / 158) : ℂ) * ζ ^ 8 + ((381 / 790) : ℂ) * ζ ^ 9 + ((272 / 395) : ℂ) * ζ ^ 11 + ((35 / 158) : ℂ) * ζ ^ 12 - ((91 / 395) : ℂ) * ζ ^ 13 + ((271 / 395) : ℂ) * ζ ^ 15 - ((91 / 395) : ℂ) * ζ ^ 17 - ((209 / 790) : ℂ) * ζ ^ 18 - ((19 / 790) : ℂ) * ζ ^ 21 - ((583 / 790) : ℂ) * ζ ^ 22 - ((379 / 790) : ℂ) * ζ ^ 25 + ((19 / 790) : ℂ) * ζ ^ 27 - ((35 / 158) : ℂ) * ζ ^ 28 + ((91 / 395) : ℂ) * ζ ^ 29 + ((198 / 395) : ℂ) * ζ ^ 30 - ((272 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep07CoefficientIdentity02 :
    row18_reducedY54_combinationStep07Coefficient02 =
      row18_reducedY54_combinationStep06Coefficient02 +
        row18_reducedY54_combinationStep07Multiplier *
          (-((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((57 / 158) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((57 / 158) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((57 / 158) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep07Coefficient02 row18_reducedY54_combinationStep06Coefficient02 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 (-((5709 / 6241) : ℂ) - ((351 / 158) : ℂ) * ζ ^ 1 - ((49102 / 18723) : ℂ) * ζ ^ 2 + ((149 / 158) : ℂ) * ζ ^ 3 + ((1188 / 6241) : ℂ) * ζ ^ 4 + ((313 / 474) : ℂ) * ζ ^ 5 - ((51370 / 18723) : ℂ) * ζ ^ 6 + ((52 / 237) : ℂ) * ζ ^ 7 - ((6326 / 18723) : ℂ) * ζ ^ 8 + ((577 / 237) : ℂ) * ζ ^ 9 - ((2789 / 18723) : ℂ) * ζ ^ 10 + ((520 / 237) : ℂ) * ζ ^ 11 - ((6392 / 18723) : ℂ) * ζ ^ 12 + ((8 / 79) : ℂ) * ζ ^ 13 - ((71104 / 18723) : ℂ) * ζ ^ 14 + ((17 / 474) : ℂ) * ζ ^ 15 - ((3805 / 18723) : ℂ) * ζ ^ 16 + ((457 / 237) : ℂ) * ζ ^ 17 - ((52694 / 18723) : ℂ) * ζ ^ 18 - ((277 / 237) : ℂ) * ζ ^ 19 - ((2040 / 6241) : ℂ) * ζ ^ 20 + ((565 / 237) : ℂ) * ζ ^ 21 + ((4766 / 18723) : ℂ) * ζ ^ 22 + ((6 / 79) : ℂ) * ζ ^ 23 - ((4136 / 6241) : ℂ) * ζ ^ 24 + ((14 / 79) : ℂ) * ζ ^ 25 + ((3676 / 6241) : ℂ) * ζ ^ 26 - ((11 / 158) : ℂ) * ζ ^ 27 - ((1959 / 6241) : ℂ) * ζ ^ 28 - ((53 / 237) : ℂ) * ζ ^ 29 + ((4550 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep07Coefficient03 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep07CoefficientIdentity03 :
    row18_reducedY54_combinationStep07Coefficient03 =
      row18_reducedY54_combinationStep06Coefficient03 +
        row18_reducedY54_combinationStep07Multiplier *
          (-((5 / 79) : ℂ) - ((43 / 316) : ℂ) * ζ ^ 1 - ((9 / 158) : ℂ) * ζ ^ 2 - ((63 / 316) : ℂ) * ζ ^ 5 + ((1 / 158) : ℂ) * ζ ^ 6 + ((1 / 158) : ℂ) * ζ ^ 8 - ((63 / 316) : ℂ) * ζ ^ 9 + ((57 / 158) : ℂ) * ζ ^ 11 + ((31 / 316) : ℂ) * ζ ^ 12 + ((43 / 316) : ℂ) * ζ ^ 13 - ((3 / 79) : ℂ) * ζ ^ 15 + ((43 / 316) : ℂ) * ζ ^ 17 - ((3 / 316) : ℂ) * ζ ^ 18 + ((53 / 316) : ℂ) * ζ ^ 21 + ((9 / 158) : ℂ) * ζ ^ 22 + ((1 / 316) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((1 / 158) : ℂ) * ζ ^ 28 - ((43 / 316) : ℂ) * ζ ^ 29 - ((29 / 316) : ℂ) * ζ ^ 30 - ((57 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep07Coefficient03 row18_reducedY54_combinationStep06Coefficient03 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 (((1067 / 37446) : ℂ) - ((72211 / 37446) : ℂ) * ζ ^ 1 - ((94585 / 37446) : ℂ) * ζ ^ 2 - ((45781 / 37446) : ℂ) * ζ ^ 3 + ((5105 / 12482) : ℂ) * ζ ^ 4 - ((34 / 237) : ℂ) * ζ ^ 5 - ((3197 / 37446) : ℂ) * ζ ^ 6 + ((8839 / 6241) : ℂ) * ζ ^ 7 + ((81197 / 37446) : ℂ) * ζ ^ 8 + ((26950 / 18723) : ℂ) * ζ ^ 9 - ((12281 / 37446) : ℂ) * ζ ^ 10 + ((7164 / 6241) : ℂ) * ζ ^ 11 + ((11084 / 18723) : ℂ) * ζ ^ 12 - ((6598 / 18723) : ℂ) * ζ ^ 13 - ((29001 / 12482) : ℂ) * ζ ^ 14 - ((69874 / 18723) : ℂ) * ζ ^ 15 - ((19597 / 18723) : ℂ) * ζ ^ 16 + ((42725 / 18723) : ℂ) * ζ ^ 17 + ((61819 / 18723) : ℂ) * ζ ^ 18 + ((43349 / 37446) : ℂ) * ζ ^ 19 - ((9803 / 37446) : ℂ) * ζ ^ 20 - ((35657 / 37446) : ℂ) * ζ ^ 21 + ((6305 / 18723) : ℂ) * ζ ^ 22 - ((3883 / 12482) : ℂ) * ζ ^ 23 + ((10347 / 12482) : ℂ) * ζ ^ 24 - ((30059 / 37446) : ℂ) * ζ ^ 25 - ((15285 / 12482) : ℂ) * ζ ^ 26 - ((34415 / 12482) : ℂ) * ζ ^ 27 - ((14735 / 37446) : ℂ) * ζ ^ 28 + ((7088 / 18723) : ℂ) * ζ ^ 29 + ((12350 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep07Coefficient04 : ℂ :=
  (((51 / 10) : ℂ) + ((5 / 2) : ℂ) * ζ ^ 1 - ((9 / 5) : ℂ) * ζ ^ 2 - ((23 / 5) : ℂ) * ζ ^ 3 + ((5 / 2) : ℂ) * ζ ^ 5 + ((33 / 10) : ℂ) * ζ ^ 6 - ((33 / 10) : ℂ) * ζ ^ 8 - ((5 / 2) : ℂ) * ζ ^ 9 + ((23 / 10) : ℂ) * ζ ^ 11 - ((19 / 10) : ℂ) * ζ ^ 12 - ((5 / 2) : ℂ) * ζ ^ 13 + ((39 / 10) : ℂ) * ζ ^ 15 - ((5 / 2) : ℂ) * ζ ^ 17 - ((13 / 5) : ℂ) * ζ ^ 18 + ((5 / 2) : ℂ) * ζ ^ 21 + ((9 / 5) : ℂ) * ζ ^ 22 + ((7 / 10) : ℂ) * ζ ^ 24 - ((7 / 10) : ℂ) * ζ ^ 27 + ((33 / 10) : ℂ) * ζ ^ 28 + ((5 / 2) : ℂ) * ζ ^ 29 + ((7 / 5) : ℂ) * ζ ^ 30 - ((23 / 10) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep07CoefficientIdentity04 :
    row18_reducedY54_combinationStep07Coefficient04 =
      row18_reducedY54_combinationStep06Coefficient04 +
        row18_reducedY54_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep07Coefficient04 row18_reducedY54_combinationStep06Coefficient04 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep07Coefficient05 : ℂ :=
  (((22 / 79) : ℂ) + ((61 / 158) : ℂ) * ζ ^ 1 + ((84 / 79) : ℂ) * ζ ^ 2 + ((78 / 79) : ℂ) * ζ ^ 3 + ((85 / 79) : ℂ) * ζ ^ 5 + ((76 / 79) : ℂ) * ζ ^ 6 + ((335 / 158) : ℂ) * ζ ^ 9 - ((85 / 79) : ℂ) * ζ ^ 11 - ((152 / 79) : ℂ) * ζ ^ 12 - ((61 / 158) : ℂ) * ζ ^ 13 + ((113 / 79) : ℂ) * ζ ^ 15 - ((61 / 158) : ℂ) * ζ ^ 17 - ((92 / 79) : ℂ) * ζ ^ 18 - ((7 / 79) : ℂ) * ζ ^ 21 - ((84 / 79) : ℂ) * ζ ^ 22 + ((22 / 79) : ℂ) * ζ ^ 24 - ((109 / 158) : ℂ) * ζ ^ 25 + ((109 / 158) : ℂ) * ζ ^ 27 + ((61 / 158) : ℂ) * ζ ^ 29 + ((168 / 79) : ℂ) * ζ ^ 30 + ((85 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY54_combinationStep07CoefficientIdentity05 :
    row18_reducedY54_combinationStep07Coefficient05 =
      row18_reducedY54_combinationStep06Coefficient05 +
        row18_reducedY54_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep07Coefficient05 row18_reducedY54_combinationStep06Coefficient05 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep07Coefficient06 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep07CoefficientIdentity06 :
    row18_reducedY54_combinationStep07Coefficient06 =
      row18_reducedY54_combinationStep06Coefficient06 +
        row18_reducedY54_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep07Coefficient06 row18_reducedY54_combinationStep06Coefficient06 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep07Coefficient07 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep07CoefficientIdentity07 :
    row18_reducedY54_combinationStep07Coefficient07 =
      row18_reducedY54_combinationStep06Coefficient07 +
        row18_reducedY54_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep07Coefficient07 row18_reducedY54_combinationStep06Coefficient07 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep07Coefficient08 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep07CoefficientIdentity08 :
    row18_reducedY54_combinationStep07Coefficient08 =
      row18_reducedY54_combinationStep06Coefficient08 +
        row18_reducedY54_combinationStep07Multiplier *
          (((5 / 79) : ℂ) + ((43 / 316) : ℂ) * ζ ^ 1 + ((9 / 158) : ℂ) * ζ ^ 2 + ((63 / 316) : ℂ) * ζ ^ 5 - ((1 / 158) : ℂ) * ζ ^ 6 - ((1 / 158) : ℂ) * ζ ^ 8 + ((63 / 316) : ℂ) * ζ ^ 9 - ((57 / 158) : ℂ) * ζ ^ 11 - ((31 / 316) : ℂ) * ζ ^ 12 - ((43 / 316) : ℂ) * ζ ^ 13 + ((3 / 79) : ℂ) * ζ ^ 15 - ((43 / 316) : ℂ) * ζ ^ 17 + ((3 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 - ((9 / 158) : ℂ) * ζ ^ 22 - ((1 / 316) : ℂ) * ζ ^ 24 - ((5 / 79) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((1 / 158) : ℂ) * ζ ^ 28 + ((43 / 316) : ℂ) * ζ ^ 29 + ((29 / 316) : ℂ) * ζ ^ 30 + ((57 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep07Coefficient08 row18_reducedY54_combinationStep06Coefficient08 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 (-((1067 / 37446) : ℂ) + ((72211 / 37446) : ℂ) * ζ ^ 1 + ((94585 / 37446) : ℂ) * ζ ^ 2 + ((45781 / 37446) : ℂ) * ζ ^ 3 - ((5105 / 12482) : ℂ) * ζ ^ 4 + ((34 / 237) : ℂ) * ζ ^ 5 + ((3197 / 37446) : ℂ) * ζ ^ 6 - ((8839 / 6241) : ℂ) * ζ ^ 7 - ((81197 / 37446) : ℂ) * ζ ^ 8 - ((26950 / 18723) : ℂ) * ζ ^ 9 + ((12281 / 37446) : ℂ) * ζ ^ 10 - ((7164 / 6241) : ℂ) * ζ ^ 11 - ((11084 / 18723) : ℂ) * ζ ^ 12 + ((6598 / 18723) : ℂ) * ζ ^ 13 + ((29001 / 12482) : ℂ) * ζ ^ 14 + ((69874 / 18723) : ℂ) * ζ ^ 15 + ((19597 / 18723) : ℂ) * ζ ^ 16 - ((42725 / 18723) : ℂ) * ζ ^ 17 - ((61819 / 18723) : ℂ) * ζ ^ 18 - ((43349 / 37446) : ℂ) * ζ ^ 19 + ((9803 / 37446) : ℂ) * ζ ^ 20 + ((35657 / 37446) : ℂ) * ζ ^ 21 - ((6305 / 18723) : ℂ) * ζ ^ 22 + ((3883 / 12482) : ℂ) * ζ ^ 23 - ((10347 / 12482) : ℂ) * ζ ^ 24 + ((30059 / 37446) : ℂ) * ζ ^ 25 + ((15285 / 12482) : ℂ) * ζ ^ 26 + ((34415 / 12482) : ℂ) * ζ ^ 27 + ((14735 / 37446) : ℂ) * ζ ^ 28 - ((7088 / 18723) : ℂ) * ζ ^ 29 - ((12350 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep07Coefficient09 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep07CoefficientIdentity09 :
    row18_reducedY54_combinationStep07Coefficient09 =
      row18_reducedY54_combinationStep06Coefficient09 +
        row18_reducedY54_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep07Coefficient09 row18_reducedY54_combinationStep06Coefficient09 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep07Coefficient10 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY54_combinationStep07CoefficientIdentity10 :
    row18_reducedY54_combinationStep07Coefficient10 =
      row18_reducedY54_combinationStep06Coefficient10 +
        row18_reducedY54_combinationStep07Multiplier *
          (-((16 / 79) : ℂ) - ((35 / 316) : ℂ) * ζ ^ 1 + ((61 / 316) : ℂ) * ζ ^ 2 - ((87 / 316) : ℂ) * ζ ^ 3 + ((3 / 316) : ℂ) * ζ ^ 5 + ((6 / 79) : ℂ) * ζ ^ 8 + ((31 / 316) : ℂ) * ζ ^ 9 + ((14 / 79) : ℂ) * ζ ^ 11 + ((26 / 79) : ℂ) * ζ ^ 12 + ((35 / 316) : ℂ) * ζ ^ 13 + ((49 / 316) : ℂ) * ζ ^ 15 + ((35 / 316) : ℂ) * ζ ^ 17 - ((61 / 316) : ℂ) * ζ ^ 18 - ((13 / 79) : ℂ) * ζ ^ 21 - ((61 / 316) : ℂ) * ζ ^ 22 - ((32 / 79) : ℂ) * ζ ^ 24 - ((19 / 158) : ℂ) * ζ ^ 25 - ((13 / 79) : ℂ) * ζ ^ 27 - ((6 / 79) : ℂ) * ζ ^ 28 - ((35 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((14 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep07Coefficient10 row18_reducedY54_combinationStep06Coefficient10 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 (-((60149 / 37446) : ℂ) - ((487 / 474) : ℂ) * ζ ^ 1 + ((30703 / 37446) : ℂ) * ζ ^ 2 + ((23 / 79) : ℂ) * ζ ^ 3 + ((13229 / 18723) : ℂ) * ζ ^ 4 + ((185 / 237) : ℂ) * ζ ^ 5 - ((12089 / 37446) : ℂ) * ζ ^ 6 + ((41 / 158) : ℂ) * ζ ^ 7 - ((1367 / 18723) : ℂ) * ζ ^ 8 + ((299 / 237) : ℂ) * ζ ^ 9 - ((8707 / 18723) : ℂ) * ζ ^ 10 + ((17 / 158) : ℂ) * ζ ^ 11 + ((27785 / 37446) : ℂ) * ζ ^ 12 + ((74 / 79) : ℂ) * ζ ^ 13 - ((4798 / 6241) : ℂ) * ζ ^ 14 - ((299 / 474) : ℂ) * ζ ^ 15 - ((5205 / 6241) : ℂ) * ζ ^ 16 + ((21 / 158) : ℂ) * ζ ^ 17 - ((7455 / 12482) : ℂ) * ζ ^ 18 - ((93 / 79) : ℂ) * ζ ^ 19 - ((31975 / 37446) : ℂ) * ζ ^ 20 - ((641 / 474) : ℂ) * ζ ^ 21 + ((4054 / 18723) : ℂ) * ζ ^ 22 + ((103 / 474) : ℂ) * ζ ^ 23 + ((2113 / 18723) : ℂ) * ζ ^ 24 - ((473 / 474) : ℂ) * ζ ^ 25 + ((29734 / 18723) : ℂ) * ζ ^ 26 - ((173 / 474) : ℂ) * ζ ^ 27 + ((2167 / 18723) : ℂ) * ζ ^ 28 - ((212 / 237) : ℂ) * ζ ^ 29 + ((18200 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep07Coefficient11 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep07CoefficientIdentity11 :
    row18_reducedY54_combinationStep07Coefficient11 =
      row18_reducedY54_combinationStep06Coefficient11 +
        row18_reducedY54_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep07Coefficient11 row18_reducedY54_combinationStep06Coefficient11 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep07Coefficient12 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep07CoefficientIdentity12 :
    row18_reducedY54_combinationStep07Coefficient12 =
      row18_reducedY54_combinationStep06Coefficient12 +
        row18_reducedY54_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep07Coefficient12 row18_reducedY54_combinationStep06Coefficient12 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep07Coefficient13 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep07CoefficientIdentity13 :
    row18_reducedY54_combinationStep07Coefficient13 =
      row18_reducedY54_combinationStep06Coefficient13 +
        row18_reducedY54_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep07Coefficient13 row18_reducedY54_combinationStep06Coefficient13 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep07Coefficient14 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep07CoefficientIdentity14 :
    row18_reducedY54_combinationStep07Coefficient14 =
      row18_reducedY54_combinationStep06Coefficient14 +
        row18_reducedY54_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep07Coefficient14 row18_reducedY54_combinationStep06Coefficient14 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep07Coefficient15 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep07CoefficientIdentity15 :
    row18_reducedY54_combinationStep07Coefficient15 =
      row18_reducedY54_combinationStep06Coefficient15 +
        row18_reducedY54_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep07Coefficient15 row18_reducedY54_combinationStep06Coefficient15 row18_reducedY54_combinationStep07Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY54_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY54_combinationStep07Coefficient00) * Y 0 0
      + (row18_reducedY54_combinationStep07Coefficient01) * Y 0 1
      + (row18_reducedY54_combinationStep07Coefficient02) * Y 1 0
      + (row18_reducedY54_combinationStep07Coefficient03) * Y 1 1
      + (row18_reducedY54_combinationStep07Coefficient04) * Y 2 2
      + (row18_reducedY54_combinationStep07Coefficient05) * Y 2 3
      + (row18_reducedY54_combinationStep07Coefficient06) * Y 3 2
      + (row18_reducedY54_combinationStep07Coefficient07) * Y 3 3
      + (row18_reducedY54_combinationStep07Coefficient08) * Y 4 4
      + (row18_reducedY54_combinationStep07Coefficient09) * Y 4 5
      + (row18_reducedY54_combinationStep07Coefficient10) * Y 5 4
      + (row18_reducedY54_combinationStep07Coefficient11) * Y 5 5
      + (row18_reducedY54_combinationStep07Coefficient12) * Y 6 6
      + (row18_reducedY54_combinationStep07Coefficient13) * Y 6 7
      + (row18_reducedY54_combinationStep07Coefficient14) * Y 7 6
      + (row18_reducedY54_combinationStep07Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY54_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation14
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY54_combinationStep07CoefficientIdentity00,
      row18_reducedY54_combinationStep07CoefficientIdentity01,
      row18_reducedY54_combinationStep07CoefficientIdentity02,
      row18_reducedY54_combinationStep07CoefficientIdentity03,
      row18_reducedY54_combinationStep07CoefficientIdentity04,
      row18_reducedY54_combinationStep07CoefficientIdentity05,
      row18_reducedY54_combinationStep07CoefficientIdentity06,
      row18_reducedY54_combinationStep07CoefficientIdentity07,
      row18_reducedY54_combinationStep07CoefficientIdentity08,
      row18_reducedY54_combinationStep07CoefficientIdentity09,
      row18_reducedY54_combinationStep07CoefficientIdentity10,
      row18_reducedY54_combinationStep07CoefficientIdentity11,
      row18_reducedY54_combinationStep07CoefficientIdentity12,
      row18_reducedY54_combinationStep07CoefficientIdentity13,
      row18_reducedY54_combinationStep07CoefficientIdentity14,
      row18_reducedY54_combinationStep07CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY54_combinationStep07Multiplier * equation

private def row18_reducedY54_combinationStep08Multiplier : ℂ :=
  (((4298 / 395) : ℂ) + ((662 / 79) : ℂ) * ζ ^ 1 - ((1664 / 395) : ℂ) * ζ ^ 2 - ((6144 / 395) : ℂ) * ζ ^ 3 + ((662 / 79) : ℂ) * ζ ^ 5 + ((2634 / 395) : ℂ) * ζ ^ 6 - ((2634 / 395) : ℂ) * ζ ^ 8 - ((662 / 79) : ℂ) * ζ ^ 9 + ((3072 / 395) : ℂ) * ζ ^ 11 - ((2462 / 395) : ℂ) * ζ ^ 12 - ((662 / 79) : ℂ) * ζ ^ 13 + ((4606 / 395) : ℂ) * ζ ^ 15 - ((662 / 79) : ℂ) * ζ ^ 17 - ((4268 / 395) : ℂ) * ζ ^ 18 + ((364 / 79) : ℂ) * ζ ^ 21 + ((1664 / 395) : ℂ) * ζ ^ 22 - ((1634 / 395) : ℂ) * ζ ^ 24 - ((1538 / 395) : ℂ) * ζ ^ 27 + ((2634 / 395) : ℂ) * ζ ^ 28 + ((662 / 79) : ℂ) * ζ ^ 29 + ((172 / 395) : ℂ) * ζ ^ 30 - ((3072 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY54_combinationStep08Coefficient00 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity00 :
    row18_reducedY54_combinationStep08Coefficient00 =
      row18_reducedY54_combinationStep07Coefficient00 +
        row18_reducedY54_combinationStep08Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep08Coefficient00 row18_reducedY54_combinationStep07Coefficient00 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 (-((292503 / 62410) : ℂ) - ((79902 / 31205) : ℂ) * ζ ^ 1 - ((49258 / 31205) : ℂ) * ζ ^ 2 + ((11655 / 6241) : ℂ) * ζ ^ 3 + ((39536 / 6241) : ℂ) * ζ ^ 4 + ((2799 / 790) : ℂ) * ζ ^ 5 - ((112592 / 31205) : ℂ) * ζ ^ 6 - ((149856 / 31205) : ℂ) * ζ ^ 7 - ((137621 / 31205) : ℂ) * ζ ^ 8 - ((347 / 6241) : ℂ) * ζ ^ 9 + ((356319 / 62410) : ℂ) * ζ ^ 10 + ((350913 / 62410) : ℂ) * ζ ^ 11 - ((6282 / 6241) : ℂ) * ζ ^ 12 - ((201537 / 62410) : ℂ) * ζ ^ 13 - ((26200 / 6241) : ℂ) * ζ ^ 14 - ((178453 / 62410) : ℂ) * ζ ^ 15 + ((50801 / 31205) : ℂ) * ζ ^ 16 + ((115487 / 31205) : ℂ) * ζ ^ 17 + ((90101 / 62410) : ℂ) * ζ ^ 18 + ((28911 / 31205) : ℂ) * ζ ^ 19 - ((9354 / 6241) : ℂ) * ζ ^ 20 - ((69768 / 31205) : ℂ) * ζ ^ 21 + ((521 / 395) : ℂ) * ζ ^ 22 + ((69977 / 62410) : ℂ) * ζ ^ 23 + ((1316 / 6241) : ℂ) * ζ ^ 24 + ((15669 / 31205) : ℂ) * ζ ^ 25 - ((28573 / 62410) : ℂ) * ζ ^ 26 - ((49812 / 31205) : ℂ) * ζ ^ 27 - ((765 / 6241) : ℂ) * ζ ^ 28 + ((11686 / 31205) : ℂ) * ζ ^ 29 + ((10752 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep08Coefficient01 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity01 :
    row18_reducedY54_combinationStep08Coefficient01 =
      row18_reducedY54_combinationStep07Coefficient01 +
        row18_reducedY54_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep08Coefficient01 row18_reducedY54_combinationStep07Coefficient01 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep08Coefficient02 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity02 :
    row18_reducedY54_combinationStep08Coefficient02 =
      row18_reducedY54_combinationStep07Coefficient02 +
        row18_reducedY54_combinationStep08Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep08Coefficient02 row18_reducedY54_combinationStep07Coefficient02 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 (-((11996 / 31205) : ℂ) - ((132323 / 62410) : ℂ) * ζ ^ 1 + ((36767 / 62410) : ℂ) * ζ ^ 2 - ((53941 / 62410) : ℂ) * ζ ^ 3 - ((25887 / 62410) : ℂ) * ζ ^ 4 + ((364 / 395) : ℂ) * ζ ^ 5 + ((20282 / 6241) : ℂ) * ζ ^ 6 + ((116989 / 62410) : ℂ) * ζ ^ 7 + ((189669 / 62410) : ℂ) * ζ ^ 8 - ((15477 / 62410) : ℂ) * ζ ^ 9 - ((51293 / 12482) : ℂ) * ζ ^ 10 - ((8599 / 12482) : ℂ) * ζ ^ 11 + ((17932 / 31205) : ℂ) * ζ ^ 12 + ((13329 / 6241) : ℂ) * ζ ^ 13 + ((158067 / 62410) : ℂ) * ζ ^ 14 + ((127853 / 31205) : ℂ) * ζ ^ 15 + ((13291 / 62410) : ℂ) * ζ ^ 16 - ((32337 / 31205) : ℂ) * ζ ^ 17 - ((70573 / 31205) : ℂ) * ζ ^ 18 - ((140311 / 62410) : ℂ) * ζ ^ 19 + ((12961 / 62410) : ℂ) * ζ ^ 20 + ((158343 / 62410) : ℂ) * ζ ^ 21 + ((18600 / 6241) : ℂ) * ζ ^ 22 + ((123839 / 62410) : ℂ) * ζ ^ 23 - ((58656 / 31205) : ℂ) * ζ ^ 24 - ((92912 / 31205) : ℂ) * ζ ^ 25 - ((68239 / 62410) : ℂ) * ζ ^ 26 - ((51399 / 31205) : ℂ) * ζ ^ 27 - ((41622 / 31205) : ℂ) * ζ ^ 28 + ((33252 / 31205) : ℂ) * ζ ^ 29 + ((64512 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep08Coefficient03 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity03 :
    row18_reducedY54_combinationStep08Coefficient03 =
      row18_reducedY54_combinationStep07Coefficient03 +
        row18_reducedY54_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep08Coefficient03 row18_reducedY54_combinationStep07Coefficient03 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep08Coefficient04 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity04 :
    row18_reducedY54_combinationStep08Coefficient04 =
      row18_reducedY54_combinationStep07Coefficient04 +
        row18_reducedY54_combinationStep08Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep08Coefficient04 row18_reducedY54_combinationStep07Coefficient04 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 (((292503 / 62410) : ℂ) + ((79902 / 31205) : ℂ) * ζ ^ 1 + ((49258 / 31205) : ℂ) * ζ ^ 2 - ((11655 / 6241) : ℂ) * ζ ^ 3 - ((39536 / 6241) : ℂ) * ζ ^ 4 - ((2799 / 790) : ℂ) * ζ ^ 5 + ((112592 / 31205) : ℂ) * ζ ^ 6 + ((149856 / 31205) : ℂ) * ζ ^ 7 + ((137621 / 31205) : ℂ) * ζ ^ 8 + ((347 / 6241) : ℂ) * ζ ^ 9 - ((356319 / 62410) : ℂ) * ζ ^ 10 - ((350913 / 62410) : ℂ) * ζ ^ 11 + ((6282 / 6241) : ℂ) * ζ ^ 12 + ((201537 / 62410) : ℂ) * ζ ^ 13 + ((26200 / 6241) : ℂ) * ζ ^ 14 + ((178453 / 62410) : ℂ) * ζ ^ 15 - ((50801 / 31205) : ℂ) * ζ ^ 16 - ((115487 / 31205) : ℂ) * ζ ^ 17 - ((90101 / 62410) : ℂ) * ζ ^ 18 - ((28911 / 31205) : ℂ) * ζ ^ 19 + ((9354 / 6241) : ℂ) * ζ ^ 20 + ((69768 / 31205) : ℂ) * ζ ^ 21 - ((521 / 395) : ℂ) * ζ ^ 22 - ((69977 / 62410) : ℂ) * ζ ^ 23 - ((1316 / 6241) : ℂ) * ζ ^ 24 - ((15669 / 31205) : ℂ) * ζ ^ 25 + ((28573 / 62410) : ℂ) * ζ ^ 26 + ((49812 / 31205) : ℂ) * ζ ^ 27 + ((765 / 6241) : ℂ) * ζ ^ 28 - ((11686 / 31205) : ℂ) * ζ ^ 29 - ((10752 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep08Coefficient05 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity05 :
    row18_reducedY54_combinationStep08Coefficient05 =
      row18_reducedY54_combinationStep07Coefficient05 +
        row18_reducedY54_combinationStep08Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY54_combinationStep08Coefficient05 row18_reducedY54_combinationStep07Coefficient05 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 (((165661 / 62410) : ℂ) + ((49804 / 31205) : ℂ) * ζ ^ 1 - ((40179 / 62410) : ℂ) * ζ ^ 2 - ((150267 / 62410) : ℂ) * ζ ^ 3 - ((102877 / 62410) : ℂ) * ζ ^ 4 + ((1167 / 790) : ℂ) * ζ ^ 5 - ((1956 / 6241) : ℂ) * ζ ^ 6 - ((5384 / 31205) : ℂ) * ζ ^ 7 - ((77999 / 62410) : ℂ) * ζ ^ 8 + ((42977 / 62410) : ℂ) * ζ ^ 9 + ((1261 / 790) : ℂ) * ζ ^ 10 + ((557963 / 62410) : ℂ) * ζ ^ 11 + ((179167 / 62410) : ℂ) * ζ ^ 12 - ((342677 / 62410) : ℂ) * ζ ^ 13 - ((602131 / 62410) : ℂ) * ζ ^ 14 - ((85187 / 62410) : ℂ) * ζ ^ 15 + ((31588 / 6241) : ℂ) * ζ ^ 16 + ((570429 / 62410) : ℂ) * ζ ^ 17 + ((1943 / 790) : ℂ) * ζ ^ 18 - ((154722 / 31205) : ℂ) * ζ ^ 19 - ((196692 / 31205) : ℂ) * ζ ^ 20 - ((37239 / 62410) : ℂ) * ζ ^ 21 + ((204867 / 62410) : ℂ) * ζ ^ 22 + ((47855 / 12482) : ℂ) * ζ ^ 23 + ((266149 / 62410) : ℂ) * ζ ^ 24 + ((36068 / 31205) : ℂ) * ζ ^ 25 - ((10170 / 6241) : ℂ) * ζ ^ 26 - ((223893 / 31205) : ℂ) * ζ ^ 27 - ((137448 / 31205) : ℂ) * ζ ^ 28 + ((33732 / 31205) : ℂ) * ζ ^ 29 + ((27648 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY54_combinationStep08Coefficient06 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity06 :
    row18_reducedY54_combinationStep08Coefficient06 =
      row18_reducedY54_combinationStep07Coefficient06 +
        row18_reducedY54_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep08Coefficient06 row18_reducedY54_combinationStep07Coefficient06 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep08Coefficient07 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity07 :
    row18_reducedY54_combinationStep08Coefficient07 =
      row18_reducedY54_combinationStep07Coefficient07 +
        row18_reducedY54_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep08Coefficient07 row18_reducedY54_combinationStep07Coefficient07 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep08Coefficient08 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity08 :
    row18_reducedY54_combinationStep08Coefficient08 =
      row18_reducedY54_combinationStep07Coefficient08 +
        row18_reducedY54_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep08Coefficient08 row18_reducedY54_combinationStep07Coefficient08 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep08Coefficient09 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity09 :
    row18_reducedY54_combinationStep08Coefficient09 =
      row18_reducedY54_combinationStep07Coefficient09 +
        row18_reducedY54_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep08Coefficient09 row18_reducedY54_combinationStep07Coefficient09 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep08Coefficient10 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY54_combinationStep08CoefficientIdentity10 :
    row18_reducedY54_combinationStep08Coefficient10 =
      row18_reducedY54_combinationStep07Coefficient10 +
        row18_reducedY54_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep08Coefficient10 row18_reducedY54_combinationStep07Coefficient10 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep08Coefficient11 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity11 :
    row18_reducedY54_combinationStep08Coefficient11 =
      row18_reducedY54_combinationStep07Coefficient11 +
        row18_reducedY54_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep08Coefficient11 row18_reducedY54_combinationStep07Coefficient11 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep08Coefficient12 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity12 :
    row18_reducedY54_combinationStep08Coefficient12 =
      row18_reducedY54_combinationStep07Coefficient12 +
        row18_reducedY54_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep08Coefficient12 row18_reducedY54_combinationStep07Coefficient12 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep08Coefficient13 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity13 :
    row18_reducedY54_combinationStep08Coefficient13 =
      row18_reducedY54_combinationStep07Coefficient13 +
        row18_reducedY54_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep08Coefficient13 row18_reducedY54_combinationStep07Coefficient13 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep08Coefficient14 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity14 :
    row18_reducedY54_combinationStep08Coefficient14 =
      row18_reducedY54_combinationStep07Coefficient14 +
        row18_reducedY54_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep08Coefficient14 row18_reducedY54_combinationStep07Coefficient14 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY54_combinationStep08Coefficient15 : ℂ :=
  0

private theorem row18_reducedY54_combinationStep08CoefficientIdentity15 :
    row18_reducedY54_combinationStep08Coefficient15 =
      row18_reducedY54_combinationStep07Coefficient15 +
        row18_reducedY54_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY54_combinationStep08Coefficient15 row18_reducedY54_combinationStep07Coefficient15 row18_reducedY54_combinationStep08Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY54_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY54_combinationStep08Coefficient00) * Y 0 0
      + (row18_reducedY54_combinationStep08Coefficient01) * Y 0 1
      + (row18_reducedY54_combinationStep08Coefficient02) * Y 1 0
      + (row18_reducedY54_combinationStep08Coefficient03) * Y 1 1
      + (row18_reducedY54_combinationStep08Coefficient04) * Y 2 2
      + (row18_reducedY54_combinationStep08Coefficient05) * Y 2 3
      + (row18_reducedY54_combinationStep08Coefficient06) * Y 3 2
      + (row18_reducedY54_combinationStep08Coefficient07) * Y 3 3
      + (row18_reducedY54_combinationStep08Coefficient08) * Y 4 4
      + (row18_reducedY54_combinationStep08Coefficient09) * Y 4 5
      + (row18_reducedY54_combinationStep08Coefficient10) * Y 5 4
      + (row18_reducedY54_combinationStep08Coefficient11) * Y 5 5
      + (row18_reducedY54_combinationStep08Coefficient12) * Y 6 6
      + (row18_reducedY54_combinationStep08Coefficient13) * Y 6 7
      + (row18_reducedY54_combinationStep08Coefficient14) * Y 7 6
      + (row18_reducedY54_combinationStep08Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY54_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY54_combinationStep08CoefficientIdentity00,
      row18_reducedY54_combinationStep08CoefficientIdentity01,
      row18_reducedY54_combinationStep08CoefficientIdentity02,
      row18_reducedY54_combinationStep08CoefficientIdentity03,
      row18_reducedY54_combinationStep08CoefficientIdentity04,
      row18_reducedY54_combinationStep08CoefficientIdentity05,
      row18_reducedY54_combinationStep08CoefficientIdentity06,
      row18_reducedY54_combinationStep08CoefficientIdentity07,
      row18_reducedY54_combinationStep08CoefficientIdentity08,
      row18_reducedY54_combinationStep08CoefficientIdentity09,
      row18_reducedY54_combinationStep08CoefficientIdentity10,
      row18_reducedY54_combinationStep08CoefficientIdentity11,
      row18_reducedY54_combinationStep08CoefficientIdentity12,
      row18_reducedY54_combinationStep08CoefficientIdentity13,
      row18_reducedY54_combinationStep08CoefficientIdentity14,
      row18_reducedY54_combinationStep08CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY54_combinationStep08Multiplier * equation

theorem row18_reducedY54
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 5 4 = 0 := by
  have reduced :=
    row18_reducedY54_combinationStep08 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY54_combinationStep08Coefficient00,
      row18_reducedY54_combinationStep08Coefficient01,
      row18_reducedY54_combinationStep08Coefficient02,
      row18_reducedY54_combinationStep08Coefficient03,
      row18_reducedY54_combinationStep08Coefficient04,
      row18_reducedY54_combinationStep08Coefficient05,
      row18_reducedY54_combinationStep08Coefficient06,
      row18_reducedY54_combinationStep08Coefficient07,
      row18_reducedY54_combinationStep08Coefficient08,
      row18_reducedY54_combinationStep08Coefficient09,
      row18_reducedY54_combinationStep08Coefficient10,
      row18_reducedY54_combinationStep08Coefficient11,
      row18_reducedY54_combinationStep08Coefficient12,
      row18_reducedY54_combinationStep08Coefficient13,
      row18_reducedY54_combinationStep08Coefficient14,
      row18_reducedY54_combinationStep08Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
