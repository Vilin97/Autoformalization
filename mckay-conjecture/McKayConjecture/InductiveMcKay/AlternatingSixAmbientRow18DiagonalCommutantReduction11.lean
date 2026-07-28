/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction10

/-!
# Ambient row 18 commutant reduction 11

This generated module checks the reduced relation `reducedY55` for
matrix coordinate (5, 5).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY55_combinationStep00Multiplier : ℂ :=
  (-((87034 / 1185) : ℂ) + ((22588 / 395) : ℂ) * ζ ^ 1 + ((18532 / 237) : ℂ) * ζ ^ 2 - ((87764 / 1185) : ℂ) * ζ ^ 3 + ((145052 / 1185) : ℂ) * ζ ^ 5 + ((45264 / 395) : ℂ) * ζ ^ 8 - ((27668 / 1185) : ℂ) * ζ ^ 9 + ((115432 / 1185) : ℂ) * ζ ^ 11 + ((38276 / 1185) : ℂ) * ζ ^ 12 - ((22588 / 395) : ℂ) * ζ ^ 13 + ((3492 / 395) : ℂ) * ζ ^ 15 - ((22588 / 395) : ℂ) * ζ ^ 17 - ((18532 / 237) : ℂ) * ζ ^ 18 - ((155528 / 1185) : ℂ) * ζ ^ 21 - ((18532 / 237) : ℂ) * ζ ^ 22 - ((174068 / 1185) : ℂ) * ζ ^ 24 - ((77288 / 1185) : ℂ) * ζ ^ 25 - ((155528 / 1185) : ℂ) * ζ ^ 27 - ((45264 / 395) : ℂ) * ζ ^ 28 + ((22588 / 395) : ℂ) * ζ ^ 29 - ((14290 / 237) : ℂ) * ζ ^ 30 - ((115432 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY55_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep00CoefficientIdentity00 :
    row18_reducedY55_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep00Coefficient00 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep00Coefficient01 : ℂ :=
  (((3539 / 474) : ℂ) - ((437 / 474) : ℂ) * ζ ^ 1 - ((716 / 237) : ℂ) * ζ ^ 2 + ((197 / 237) : ℂ) * ζ ^ 3 - ((437 / 474) : ℂ) * ζ ^ 5 + ((2107 / 474) : ℂ) * ζ ^ 6 - ((2107 / 474) : ℂ) * ζ ^ 8 + ((437 / 474) : ℂ) * ζ ^ 9 - ((197 / 474) : ℂ) * ζ ^ 11 - ((895 / 474) : ℂ) * ζ ^ 12 + ((437 / 474) : ℂ) * ζ ^ 13 + ((1289 / 474) : ℂ) * ζ ^ 15 + ((437 / 474) : ℂ) * ζ ^ 17 + ((34 / 79) : ℂ) * ζ ^ 18 + ((1131 / 158) : ℂ) * ζ ^ 21 + ((716 / 237) : ℂ) * ζ ^ 22 + ((2311 / 474) : ℂ) * ζ ^ 24 + ((561 / 158) : ℂ) * ζ ^ 27 + ((2107 / 474) : ℂ) * ζ ^ 28 - ((437 / 474) : ℂ) * ζ ^ 29 + ((202 / 79) : ℂ) * ζ ^ 30 + ((197 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep00CoefficientIdentity01 :
    row18_reducedY55_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep00Coefficient01 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 (-((5053333 / 187230) : ℂ) + ((262705 / 18723) : ℂ) * ζ ^ 1 + ((284755 / 18723) : ℂ) * ζ ^ 2 - ((193394 / 18723) : ℂ) * ζ ^ 3 + ((446461 / 12482) : ℂ) * ζ ^ 4 + ((2485358 / 93615) : ℂ) * ζ ^ 5 - ((3827551 / 187230) : ℂ) * ζ ^ 6 + ((147527 / 93615) : ℂ) * ζ ^ 7 + ((502874 / 31205) : ℂ) * ζ ^ 8 - ((1015274 / 93615) : ℂ) * ζ ^ 9 - ((13263 / 790) : ℂ) * ζ ^ 10 - ((1185819 / 62410) : ℂ) * ζ ^ 11 + ((973583 / 62410) : ℂ) * ζ ^ 12 - ((79020 / 6241) : ℂ) * ζ ^ 13 - ((2327583 / 62410) : ℂ) * ζ ^ 14 - ((27877 / 31205) : ℂ) * ζ ^ 15 - ((372827 / 187230) : ℂ) * ζ ^ 16 - ((341534 / 31205) : ℂ) * ζ ^ 17 + ((357603 / 62410) : ℂ) * ζ ^ 18 - ((129427 / 31205) : ℂ) * ζ ^ 19 - ((2955037 / 187230) : ℂ) * ζ ^ 20 - ((138678 / 31205) : ℂ) * ζ ^ 21 + ((386079 / 62410) : ℂ) * ζ ^ 22 - ((2383261 / 187230) : ℂ) * ζ ^ 23 - ((884621 / 37446) : ℂ) * ζ ^ 24 + ((48872 / 18723) : ℂ) * ζ ^ 25 + ((1396213 / 93615) : ℂ) * ζ ^ 26 + ((2901577 / 187230) : ℂ) * ζ ^ 27 - ((252533 / 12482) : ℂ) * ζ ^ 28 + ((435484 / 93615) : ℂ) * ζ ^ 29 + ((1962344 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep00Coefficient02 : ℂ :=
  (-((109 / 79) : ℂ) - ((312 / 79) : ℂ) * ζ ^ 1 - ((2353 / 474) : ℂ) * ζ ^ 2 + ((1203 / 158) : ℂ) * ζ ^ 3 - ((2653 / 237) : ℂ) * ζ ^ 5 - ((2105 / 474) : ℂ) * ζ ^ 6 - ((262 / 79) : ℂ) * ζ ^ 8 - ((781 / 474) : ℂ) * ζ ^ 9 - ((4913 / 474) : ℂ) * ζ ^ 11 - ((124 / 237) : ℂ) * ζ ^ 12 + ((312 / 79) : ℂ) * ζ ^ 13 - ((1203 / 158) : ℂ) * ζ ^ 15 + ((312 / 79) : ℂ) * ζ ^ 17 + ((3007 / 474) : ℂ) * ζ ^ 18 + ((1717 / 237) : ℂ) * ζ ^ 21 + ((2353 / 474) : ℂ) * ζ ^ 22 + ((2353 / 474) : ℂ) * ζ ^ 24 + ((1717 / 237) : ℂ) * ζ ^ 25 + ((4913 / 474) : ℂ) * ζ ^ 27 + ((262 / 79) : ℂ) * ζ ^ 28 - ((312 / 79) : ℂ) * ζ ^ 29 - ((781 / 474) : ℂ) * ζ ^ 30 + ((4913 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep00CoefficientIdentity02 :
    row18_reducedY55_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep00Coefficient02 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 (-((1655032 / 93615) : ℂ) + ((2952043 / 187230) : ℂ) * ζ ^ 1 + ((3689383 / 187230) : ℂ) * ζ ^ 2 - ((9389 / 790) : ℂ) * ζ ^ 3 + ((350165 / 18723) : ℂ) * ζ ^ 4 + ((829017 / 62410) : ℂ) * ζ ^ 5 - ((446863 / 62410) : ℂ) * ζ ^ 6 + ((5063779 / 187230) : ℂ) * ζ ^ 7 + ((822061 / 37446) : ℂ) * ζ ^ 8 - ((293257 / 31205) : ℂ) * ζ ^ 9 - ((1864187 / 187230) : ℂ) * ζ ^ 10 - ((1096879 / 187230) : ℂ) * ζ ^ 11 + ((2854 / 6241) : ℂ) * ζ ^ 12 - ((268871 / 93615) : ℂ) * ζ ^ 13 - ((400957 / 31205) : ℂ) * ζ ^ 14 + ((138229 / 62410) : ℂ) * ζ ^ 15 - ((230924 / 18723) : ℂ) * ζ ^ 16 - ((3122687 / 187230) : ℂ) * ζ ^ 17 - ((396637 / 37446) : ℂ) * ζ ^ 18 - ((393757 / 62410) : ℂ) * ζ ^ 19 - ((304759 / 187230) : ℂ) * ζ ^ 20 - ((202632 / 31205) : ℂ) * ζ ^ 21 + ((377489 / 187230) : ℂ) * ζ ^ 22 - ((195844 / 18723) : ℂ) * ζ ^ 23 - ((4521043 / 187230) : ℂ) * ζ ^ 24 + ((21790 / 6241) : ℂ) * ζ ^ 25 - ((470587 / 187230) : ℂ) * ζ ^ 26 - ((258765 / 12482) : ℂ) * ζ ^ 27 - ((293963 / 187230) : ℂ) * ζ ^ 28 + ((698069 / 62410) : ℂ) * ζ ^ 29 + ((28858 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep00CoefficientIdentity03 :
    row18_reducedY55_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep00Coefficient03 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep00CoefficientIdentity04 :
    row18_reducedY55_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep00Coefficient04 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep00CoefficientIdentity05 :
    row18_reducedY55_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep00Coefficient05 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep00CoefficientIdentity06 :
    row18_reducedY55_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep00Coefficient06 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep00CoefficientIdentity07 :
    row18_reducedY55_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep00Coefficient07 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep00CoefficientIdentity08 :
    row18_reducedY55_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep00Coefficient08 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep00CoefficientIdentity09 :
    row18_reducedY55_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep00Coefficient09 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep00CoefficientIdentity10 :
    row18_reducedY55_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep00Coefficient10 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep00CoefficientIdentity11 :
    row18_reducedY55_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep00Coefficient11 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep00CoefficientIdentity12 :
    row18_reducedY55_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep00Coefficient12 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep00CoefficientIdentity13 :
    row18_reducedY55_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep00Coefficient13 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep00CoefficientIdentity14 :
    row18_reducedY55_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep00Coefficient14 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep00CoefficientIdentity15 :
    row18_reducedY55_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY55_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep00Coefficient15 row18_reducedY55_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY55_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY55_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY55_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY55_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY55_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY55_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY55_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY55_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY55_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY55_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY55_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY55_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY55_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY55_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY55_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY55_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY55_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY55_combinationStep00CoefficientIdentity00,
      row18_reducedY55_combinationStep00CoefficientIdentity01,
      row18_reducedY55_combinationStep00CoefficientIdentity02,
      row18_reducedY55_combinationStep00CoefficientIdentity03,
      row18_reducedY55_combinationStep00CoefficientIdentity04,
      row18_reducedY55_combinationStep00CoefficientIdentity05,
      row18_reducedY55_combinationStep00CoefficientIdentity06,
      row18_reducedY55_combinationStep00CoefficientIdentity07,
      row18_reducedY55_combinationStep00CoefficientIdentity08,
      row18_reducedY55_combinationStep00CoefficientIdentity09,
      row18_reducedY55_combinationStep00CoefficientIdentity10,
      row18_reducedY55_combinationStep00CoefficientIdentity11,
      row18_reducedY55_combinationStep00CoefficientIdentity12,
      row18_reducedY55_combinationStep00CoefficientIdentity13,
      row18_reducedY55_combinationStep00CoefficientIdentity14,
      row18_reducedY55_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY55_combinationStep00Multiplier * equation

private def row18_reducedY55_combinationStep01Multiplier : ℂ :=
  (((1522 / 395) : ℂ) + ((882 / 395) : ℂ) * ζ ^ 1 + ((4856 / 395) : ℂ) * ζ ^ 2 + ((10498 / 1185) : ℂ) * ζ ^ 5 + ((3334 / 395) : ℂ) * ζ ^ 6 + ((3334 / 395) : ℂ) * ζ ^ 8 + ((10498 / 1185) : ℂ) * ζ ^ 9 + ((452 / 79) : ℂ) * ζ ^ 11 + ((362 / 395) : ℂ) * ζ ^ 12 - ((882 / 395) : ℂ) * ζ ^ 13 + ((2194 / 237) : ℂ) * ζ ^ 15 - ((882 / 395) : ℂ) * ζ ^ 17 - ((7804 / 1185) : ℂ) * ζ ^ 18 - ((6572 / 1185) : ℂ) * ζ ^ 21 - ((4856 / 395) : ℂ) * ζ ^ 22 - ((2198 / 1185) : ℂ) * ζ ^ 24 - ((7852 / 1185) : ℂ) * ζ ^ 25 - ((2194 / 237) : ℂ) * ζ ^ 27 - ((3334 / 395) : ℂ) * ζ ^ 28 + ((882 / 395) : ℂ) * ζ ^ 29 + ((2972 / 395) : ℂ) * ζ ^ 30 - ((452 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY55_combinationStep01Coefficient00 : ℂ :=
  (-((258 / 79) : ℂ) - ((142 / 79) : ℂ) * ζ ^ 1 + ((151 / 158) : ℂ) * ζ ^ 2 + ((465 / 158) : ℂ) * ζ ^ 3 - ((191 / 158) : ℂ) * ζ ^ 5 - ((214 / 237) : ℂ) * ζ ^ 6 + ((1039 / 474) : ℂ) * ζ ^ 8 + ((1043 / 474) : ℂ) * ζ ^ 9 - ((176 / 237) : ℂ) * ζ ^ 11 + ((1039 / 474) : ℂ) * ζ ^ 12 + ((142 / 79) : ℂ) * ζ ^ 13 - ((186 / 79) : ℂ) * ζ ^ 15 + ((142 / 79) : ℂ) * ζ ^ 17 + ((881 / 474) : ℂ) * ζ ^ 18 - ((181 / 158) : ℂ) * ζ ^ 21 - ((151 / 158) : ℂ) * ζ ^ 22 - ((93 / 158) : ℂ) * ζ ^ 25 + ((181 / 158) : ℂ) * ζ ^ 27 - ((1039 / 474) : ℂ) * ζ ^ 28 - ((142 / 79) : ℂ) * ζ ^ 29 - ((107 / 237) : ℂ) * ζ ^ 30 + ((176 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep01CoefficientIdentity00 :
    row18_reducedY55_combinationStep01Coefficient00 =
      row18_reducedY55_combinationStep00Coefficient00 +
        row18_reducedY55_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep01Coefficient00 row18_reducedY55_combinationStep00Coefficient00 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 (((70709 / 31205) : ℂ) + ((13225 / 12482) : ℂ) * ζ ^ 1 - ((145174 / 31205) : ℂ) * ζ ^ 2 - ((211969 / 62410) : ℂ) * ζ ^ 3 - ((106693 / 31205) : ℂ) * ζ ^ 4 - ((113821 / 93615) : ℂ) * ζ ^ 5 + ((268336 / 93615) : ℂ) * ζ ^ 6 + ((75575 / 37446) : ℂ) * ζ ^ 7 - ((82624 / 93615) : ℂ) * ζ ^ 8 - ((62021 / 37446) : ℂ) * ζ ^ 9 - ((232717 / 187230) : ℂ) * ζ ^ 10 - ((25645 / 37446) : ℂ) * ζ ^ 11 + ((6471 / 6241) : ℂ) * ζ ^ 12 + ((71524 / 31205) : ℂ) * ζ ^ 13 + ((264977 / 187230) : ℂ) * ζ ^ 14 + ((1067 / 62410) : ℂ) * ζ ^ 15 - ((255013 / 187230) : ℂ) * ζ ^ 16 + ((2015 / 12482) : ℂ) * ζ ^ 17 - ((5213 / 187230) : ℂ) * ζ ^ 18 + ((12834 / 31205) : ℂ) * ζ ^ 19 + ((35696 / 93615) : ℂ) * ζ ^ 20 + ((85093 / 62410) : ℂ) * ζ ^ 21 + ((169804 / 93615) : ℂ) * ζ ^ 22 + ((234877 / 187230) : ℂ) * ζ ^ 23 + ((15742 / 18723) : ℂ) * ζ ^ 24 - ((13733 / 12482) : ℂ) * ζ ^ 25 - ((134913 / 62410) : ℂ) * ζ ^ 26 + ((18257 / 31205) : ℂ) * ζ ^ 27 + ((61427 / 62410) : ℂ) * ζ ^ 28 - ((822 / 6241) : ℂ) * ζ ^ 29 - ((1695 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep01Coefficient01 : ℂ :=
  (((5143 / 474) : ℂ) - ((447 / 158) : ℂ) * ζ ^ 1 - ((1421 / 474) : ℂ) * ζ ^ 2 + ((634 / 237) : ℂ) * ζ ^ 3 - ((447 / 158) : ℂ) * ζ ^ 5 + ((1861 / 237) : ℂ) * ζ ^ 6 - ((1861 / 237) : ℂ) * ζ ^ 8 + ((447 / 158) : ℂ) * ζ ^ 9 - ((317 / 237) : ℂ) * ζ ^ 11 - ((273 / 158) : ℂ) * ζ ^ 12 + ((447 / 158) : ℂ) * ζ ^ 13 + ((2507 / 474) : ℂ) * ζ ^ 15 + ((447 / 158) : ℂ) * ζ ^ 17 + ((446 / 237) : ℂ) * ζ ^ 18 + ((2735 / 237) : ℂ) * ζ ^ 21 + ((1421 / 474) : ℂ) * ζ ^ 22 + ((769 / 79) : ℂ) * ζ ^ 24 + ((3775 / 474) : ℂ) * ζ ^ 27 + ((1861 / 237) : ℂ) * ζ ^ 28 - ((447 / 158) : ℂ) * ζ ^ 29 + ((2903 / 474) : ℂ) * ζ ^ 30 + ((317 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep01CoefficientIdentity01 :
    row18_reducedY55_combinationStep01Coefficient01 =
      row18_reducedY55_combinationStep00Coefficient01 +
        row18_reducedY55_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep01Coefficient01 row18_reducedY55_combinationStep00Coefficient01 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 (-((353318 / 93615) : ℂ) + ((132259 / 93615) : ℂ) * ζ ^ 1 - ((820 / 237) : ℂ) * ζ ^ 2 - ((448822 / 93615) : ℂ) * ζ ^ 3 - ((609017 / 187230) : ℂ) * ζ ^ 4 - ((267476 / 93615) : ℂ) * ζ ^ 5 - ((71787 / 62410) : ℂ) * ζ ^ 6 + ((187831 / 187230) : ℂ) * ζ ^ 7 - ((57268 / 93615) : ℂ) * ζ ^ 8 - ((112084 / 93615) : ℂ) * ζ ^ 9 - ((62429 / 37446) : ℂ) * ζ ^ 10 - ((249494 / 93615) : ℂ) * ζ ^ 11 - ((1026079 / 187230) : ℂ) * ζ ^ 12 - ((118019 / 93615) : ℂ) * ζ ^ 13 + ((37101 / 12482) : ℂ) * ζ ^ 14 - ((27579 / 31205) : ℂ) * ζ ^ 15 - ((124657 / 93615) : ℂ) * ζ ^ 16 - ((62334 / 31205) : ℂ) * ζ ^ 17 - ((672571 / 187230) : ℂ) * ζ ^ 18 + ((154309 / 187230) : ℂ) * ζ ^ 19 + ((1542343 / 187230) : ℂ) * ζ ^ 20 - ((83086 / 93615) : ℂ) * ζ ^ 21 + ((13525 / 37446) : ℂ) * ζ ^ 22 + ((321029 / 187230) : ℂ) * ζ ^ 23 - ((14581 / 187230) : ℂ) * ζ ^ 24 - ((52872 / 31205) : ℂ) * ζ ^ 25 - ((40808 / 93615) : ℂ) * ζ ^ 26 - ((27612 / 31205) : ℂ) * ζ ^ 27 + ((36436 / 31205) : ℂ) * ζ ^ 28 + ((7244 / 31205) : ℂ) * ζ ^ 29 - ((3164 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep01Coefficient02 : ℂ :=
  (-((109 / 79) : ℂ) - ((312 / 79) : ℂ) * ζ ^ 1 - ((2353 / 474) : ℂ) * ζ ^ 2 + ((1203 / 158) : ℂ) * ζ ^ 3 - ((2653 / 237) : ℂ) * ζ ^ 5 - ((2105 / 474) : ℂ) * ζ ^ 6 - ((262 / 79) : ℂ) * ζ ^ 8 - ((781 / 474) : ℂ) * ζ ^ 9 - ((4913 / 474) : ℂ) * ζ ^ 11 - ((124 / 237) : ℂ) * ζ ^ 12 + ((312 / 79) : ℂ) * ζ ^ 13 - ((1203 / 158) : ℂ) * ζ ^ 15 + ((312 / 79) : ℂ) * ζ ^ 17 + ((3007 / 474) : ℂ) * ζ ^ 18 + ((1717 / 237) : ℂ) * ζ ^ 21 + ((2353 / 474) : ℂ) * ζ ^ 22 + ((2353 / 474) : ℂ) * ζ ^ 24 + ((1717 / 237) : ℂ) * ζ ^ 25 + ((4913 / 474) : ℂ) * ζ ^ 27 + ((262 / 79) : ℂ) * ζ ^ 28 - ((312 / 79) : ℂ) * ζ ^ 29 - ((781 / 474) : ℂ) * ζ ^ 30 + ((4913 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep01CoefficientIdentity02 :
    row18_reducedY55_combinationStep01Coefficient02 =
      row18_reducedY55_combinationStep00Coefficient02 +
        row18_reducedY55_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep01Coefficient02 row18_reducedY55_combinationStep00Coefficient02 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep01Coefficient03 : ℂ :=
  (((258 / 79) : ℂ) + ((142 / 79) : ℂ) * ζ ^ 1 - ((151 / 158) : ℂ) * ζ ^ 2 - ((465 / 158) : ℂ) * ζ ^ 3 + ((191 / 158) : ℂ) * ζ ^ 5 + ((214 / 237) : ℂ) * ζ ^ 6 - ((1039 / 474) : ℂ) * ζ ^ 8 - ((1043 / 474) : ℂ) * ζ ^ 9 + ((176 / 237) : ℂ) * ζ ^ 11 - ((1039 / 474) : ℂ) * ζ ^ 12 - ((142 / 79) : ℂ) * ζ ^ 13 + ((186 / 79) : ℂ) * ζ ^ 15 - ((142 / 79) : ℂ) * ζ ^ 17 - ((881 / 474) : ℂ) * ζ ^ 18 + ((181 / 158) : ℂ) * ζ ^ 21 + ((151 / 158) : ℂ) * ζ ^ 22 + ((93 / 158) : ℂ) * ζ ^ 25 - ((181 / 158) : ℂ) * ζ ^ 27 + ((1039 / 474) : ℂ) * ζ ^ 28 + ((142 / 79) : ℂ) * ζ ^ 29 + ((107 / 237) : ℂ) * ζ ^ 30 - ((176 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep01CoefficientIdentity03 :
    row18_reducedY55_combinationStep01Coefficient03 =
      row18_reducedY55_combinationStep00Coefficient03 +
        row18_reducedY55_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep01Coefficient03 row18_reducedY55_combinationStep00Coefficient03 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 (-((70709 / 31205) : ℂ) - ((13225 / 12482) : ℂ) * ζ ^ 1 + ((145174 / 31205) : ℂ) * ζ ^ 2 + ((211969 / 62410) : ℂ) * ζ ^ 3 + ((106693 / 31205) : ℂ) * ζ ^ 4 + ((113821 / 93615) : ℂ) * ζ ^ 5 - ((268336 / 93615) : ℂ) * ζ ^ 6 - ((75575 / 37446) : ℂ) * ζ ^ 7 + ((82624 / 93615) : ℂ) * ζ ^ 8 + ((62021 / 37446) : ℂ) * ζ ^ 9 + ((232717 / 187230) : ℂ) * ζ ^ 10 + ((25645 / 37446) : ℂ) * ζ ^ 11 - ((6471 / 6241) : ℂ) * ζ ^ 12 - ((71524 / 31205) : ℂ) * ζ ^ 13 - ((264977 / 187230) : ℂ) * ζ ^ 14 - ((1067 / 62410) : ℂ) * ζ ^ 15 + ((255013 / 187230) : ℂ) * ζ ^ 16 - ((2015 / 12482) : ℂ) * ζ ^ 17 + ((5213 / 187230) : ℂ) * ζ ^ 18 - ((12834 / 31205) : ℂ) * ζ ^ 19 - ((35696 / 93615) : ℂ) * ζ ^ 20 - ((85093 / 62410) : ℂ) * ζ ^ 21 - ((169804 / 93615) : ℂ) * ζ ^ 22 - ((234877 / 187230) : ℂ) * ζ ^ 23 - ((15742 / 18723) : ℂ) * ζ ^ 24 + ((13733 / 12482) : ℂ) * ζ ^ 25 + ((134913 / 62410) : ℂ) * ζ ^ 26 - ((18257 / 31205) : ℂ) * ζ ^ 27 - ((61427 / 62410) : ℂ) * ζ ^ 28 + ((822 / 6241) : ℂ) * ζ ^ 29 + ((1695 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep01CoefficientIdentity04 :
    row18_reducedY55_combinationStep01Coefficient04 =
      row18_reducedY55_combinationStep00Coefficient04 +
        row18_reducedY55_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep01Coefficient04 row18_reducedY55_combinationStep00Coefficient04 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep01CoefficientIdentity05 :
    row18_reducedY55_combinationStep01Coefficient05 =
      row18_reducedY55_combinationStep00Coefficient05 +
        row18_reducedY55_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep01Coefficient05 row18_reducedY55_combinationStep00Coefficient05 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep01CoefficientIdentity06 :
    row18_reducedY55_combinationStep01Coefficient06 =
      row18_reducedY55_combinationStep00Coefficient06 +
        row18_reducedY55_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep01Coefficient06 row18_reducedY55_combinationStep00Coefficient06 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep01CoefficientIdentity07 :
    row18_reducedY55_combinationStep01Coefficient07 =
      row18_reducedY55_combinationStep00Coefficient07 +
        row18_reducedY55_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep01Coefficient07 row18_reducedY55_combinationStep00Coefficient07 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep01CoefficientIdentity08 :
    row18_reducedY55_combinationStep01Coefficient08 =
      row18_reducedY55_combinationStep00Coefficient08 +
        row18_reducedY55_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep01Coefficient08 row18_reducedY55_combinationStep00Coefficient08 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep01CoefficientIdentity09 :
    row18_reducedY55_combinationStep01Coefficient09 =
      row18_reducedY55_combinationStep00Coefficient09 +
        row18_reducedY55_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep01Coefficient09 row18_reducedY55_combinationStep00Coefficient09 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep01CoefficientIdentity10 :
    row18_reducedY55_combinationStep01Coefficient10 =
      row18_reducedY55_combinationStep00Coefficient10 +
        row18_reducedY55_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep01Coefficient10 row18_reducedY55_combinationStep00Coefficient10 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep01CoefficientIdentity11 :
    row18_reducedY55_combinationStep01Coefficient11 =
      row18_reducedY55_combinationStep00Coefficient11 +
        row18_reducedY55_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep01Coefficient11 row18_reducedY55_combinationStep00Coefficient11 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep01CoefficientIdentity12 :
    row18_reducedY55_combinationStep01Coefficient12 =
      row18_reducedY55_combinationStep00Coefficient12 +
        row18_reducedY55_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep01Coefficient12 row18_reducedY55_combinationStep00Coefficient12 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep01CoefficientIdentity13 :
    row18_reducedY55_combinationStep01Coefficient13 =
      row18_reducedY55_combinationStep00Coefficient13 +
        row18_reducedY55_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep01Coefficient13 row18_reducedY55_combinationStep00Coefficient13 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep01CoefficientIdentity14 :
    row18_reducedY55_combinationStep01Coefficient14 =
      row18_reducedY55_combinationStep00Coefficient14 +
        row18_reducedY55_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep01Coefficient14 row18_reducedY55_combinationStep00Coefficient14 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep01CoefficientIdentity15 :
    row18_reducedY55_combinationStep01Coefficient15 =
      row18_reducedY55_combinationStep00Coefficient15 +
        row18_reducedY55_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep01Coefficient15 row18_reducedY55_combinationStep00Coefficient15 row18_reducedY55_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY55_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY55_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY55_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY55_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY55_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY55_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY55_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY55_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY55_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY55_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY55_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY55_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY55_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY55_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY55_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY55_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY55_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY55_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY55_combinationStep01CoefficientIdentity00,
      row18_reducedY55_combinationStep01CoefficientIdentity01,
      row18_reducedY55_combinationStep01CoefficientIdentity02,
      row18_reducedY55_combinationStep01CoefficientIdentity03,
      row18_reducedY55_combinationStep01CoefficientIdentity04,
      row18_reducedY55_combinationStep01CoefficientIdentity05,
      row18_reducedY55_combinationStep01CoefficientIdentity06,
      row18_reducedY55_combinationStep01CoefficientIdentity07,
      row18_reducedY55_combinationStep01CoefficientIdentity08,
      row18_reducedY55_combinationStep01CoefficientIdentity09,
      row18_reducedY55_combinationStep01CoefficientIdentity10,
      row18_reducedY55_combinationStep01CoefficientIdentity11,
      row18_reducedY55_combinationStep01CoefficientIdentity12,
      row18_reducedY55_combinationStep01CoefficientIdentity13,
      row18_reducedY55_combinationStep01CoefficientIdentity14,
      row18_reducedY55_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY55_combinationStep01Multiplier * equation

private def row18_reducedY55_combinationStep02Multiplier : ℂ :=
  (((394 / 237) : ℂ) + ((18848 / 1185) : ℂ) * ζ ^ 1 - ((20558 / 1185) : ℂ) * ζ ^ 2 - ((5954 / 395) : ℂ) * ζ ^ 3 - ((712 / 395) : ℂ) * ζ ^ 5 - ((13052 / 1185) : ℂ) * ζ ^ 6 - ((1274 / 79) : ℂ) * ζ ^ 8 - ((8942 / 395) : ℂ) * ζ ^ 9 - ((2988 / 395) : ℂ) * ζ ^ 11 - ((1274 / 79) : ℂ) * ζ ^ 12 - ((18848 / 1185) : ℂ) * ζ ^ 13 - ((3122 / 1185) : ℂ) * ζ ^ 15 - ((18848 / 1185) : ℂ) * ζ ^ 17 - ((2502 / 395) : ℂ) * ζ ^ 18 - ((986 / 1185) : ℂ) * ζ ^ 21 + ((20558 / 1185) : ℂ) * ζ ^ 22 + ((20984 / 1185) : ℂ) * ζ ^ 25 + ((986 / 1185) : ℂ) * ζ ^ 27 + ((1274 / 79) : ℂ) * ζ ^ 28 + ((18848 / 1185) : ℂ) * ζ ^ 29 - ((6526 / 1185) : ℂ) * ζ ^ 30 + ((2988 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY55_combinationStep02Coefficient00 : ℂ :=
  (((883 / 474) : ℂ) - ((1109 / 237) : ℂ) * ζ ^ 1 + ((16241 / 2370) : ℂ) * ζ ^ 2 + ((1795 / 474) : ℂ) * ζ ^ 3 + ((697 / 237) : ℂ) * ζ ^ 5 + ((8207 / 1185) : ℂ) * ζ ^ 6 + ((2395 / 474) : ℂ) * ζ ^ 8 + ((17 / 2) : ℂ) * ζ ^ 9 + ((1117 / 237) : ℂ) * ζ ^ 11 + ((2395 / 474) : ℂ) * ζ ^ 12 + ((1109 / 237) : ℂ) * ζ ^ 13 + ((23 / 6) : ℂ) * ζ ^ 15 + ((1109 / 237) : ℂ) * ζ ^ 17 - ((173 / 2370) : ℂ) * ζ ^ 18 + ((141 / 158) : ℂ) * ζ ^ 21 - ((16241 / 2370) : ℂ) * ζ ^ 22 - ((602 / 79) : ℂ) * ζ ^ 25 - ((141 / 158) : ℂ) * ζ ^ 27 - ((2395 / 474) : ℂ) * ζ ^ 28 - ((1109 / 237) : ℂ) * ζ ^ 29 + ((8207 / 2370) : ℂ) * ζ ^ 30 - ((1117 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep02CoefficientIdentity00 :
    row18_reducedY55_combinationStep02Coefficient00 =
      row18_reducedY55_combinationStep01Coefficient00 +
        row18_reducedY55_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep02Coefficient00 row18_reducedY55_combinationStep01Coefficient00 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 (-((194413 / 37446) : ℂ) + ((437317 / 187230) : ℂ) * ζ ^ 1 - ((960817 / 187230) : ℂ) * ζ ^ 2 - ((320989 / 62410) : ℂ) * ζ ^ 3 + ((1766387 / 187230) : ℂ) * ζ ^ 4 - ((240802 / 93615) : ℂ) * ζ ^ 5 - ((666823 / 187230) : ℂ) * ζ ^ 6 + ((145949 / 31205) : ℂ) * ζ ^ 7 - ((367227 / 62410) : ℂ) * ζ ^ 8 - ((3417 / 12482) : ℂ) * ζ ^ 9 + ((439447 / 93615) : ℂ) * ζ ^ 10 - ((383621 / 93615) : ℂ) * ζ ^ 11 - ((49643 / 62410) : ℂ) * ζ ^ 12 + ((945031 / 187230) : ℂ) * ζ ^ 13 - ((566773 / 93615) : ℂ) * ζ ^ 14 - ((138553 / 93615) : ℂ) * ζ ^ 15 + ((15653 / 6241) : ℂ) * ζ ^ 16 - ((470432 / 93615) : ℂ) * ζ ^ 17 + ((121617 / 62410) : ℂ) * ζ ^ 18 + ((913441 / 187230) : ℂ) * ζ ^ 19 - ((197213 / 187230) : ℂ) * ζ ^ 20 + ((300977 / 93615) : ℂ) * ζ ^ 21 + ((168566 / 93615) : ℂ) * ζ ^ 22 + ((10195 / 37446) : ℂ) * ζ ^ 23 - ((79294 / 93615) : ℂ) * ζ ^ 24 - ((78824 / 93615) : ℂ) * ζ ^ 25 + ((67409 / 187230) : ℂ) * ζ ^ 26 - ((209777 / 187230) : ℂ) * ζ ^ 27 + ((116723 / 93615) : ℂ) * ζ ^ 28 - ((743 / 1185) : ℂ) * ζ ^ 29 + ((10458 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep02Coefficient01 : ℂ :=
  (-((1137 / 158) : ℂ) + ((3457 / 237) : ℂ) * ζ ^ 1 + ((440 / 237) : ℂ) * ζ ^ 2 - ((3967 / 237) : ℂ) * ζ ^ 3 + ((3457 / 237) : ℂ) * ζ ^ 5 - ((2531 / 474) : ℂ) * ζ ^ 6 + ((2531 / 474) : ℂ) * ζ ^ 8 - ((3457 / 237) : ℂ) * ζ ^ 9 + ((3967 / 474) : ℂ) * ζ ^ 11 - ((2057 / 474) : ℂ) * ζ ^ 12 - ((3457 / 237) : ℂ) * ζ ^ 13 + ((109 / 237) : ℂ) * ζ ^ 15 - ((3457 / 237) : ℂ) * ζ ^ 17 - ((938 / 79) : ℂ) * ζ ^ 18 - ((7945 / 474) : ℂ) * ζ ^ 21 - ((440 / 237) : ℂ) * ζ ^ 22 - ((8159 / 474) : ℂ) * ζ ^ 24 - ((1286 / 79) : ℂ) * ζ ^ 27 - ((2531 / 474) : ℂ) * ζ ^ 28 + ((3457 / 237) : ℂ) * ζ ^ 29 - ((2294 / 237) : ℂ) * ζ ^ 30 - ((3967 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep02CoefficientIdentity01 :
    row18_reducedY55_combinationStep02Coefficient01 =
      row18_reducedY55_combinationStep01Coefficient01 +
        row18_reducedY55_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep02Coefficient01 row18_reducedY55_combinationStep01Coefficient01 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 (((689359 / 37446) : ℂ) - ((1347097 / 93615) : ℂ) * ζ ^ 1 - ((2410321 / 187230) : ℂ) * ζ ^ 2 + ((2001346 / 93615) : ℂ) * ζ ^ 3 - ((845049 / 62410) : ℂ) * ζ ^ 4 - ((1071581 / 187230) : ℂ) * ζ ^ 5 + ((1782163 / 93615) : ℂ) * ζ ^ 6 - ((616269 / 62410) : ℂ) * ζ ^ 7 - ((400021 / 93615) : ℂ) * ζ ^ 8 + ((2701343 / 187230) : ℂ) * ζ ^ 9 - ((408317 / 93615) : ℂ) * ζ ^ 10 - ((365489 / 187230) : ℂ) * ζ ^ 11 + ((2694469 / 187230) : ℂ) * ζ ^ 12 - ((563288 / 93615) : ℂ) * ζ ^ 13 + ((490864 / 93615) : ℂ) * ζ ^ 14 + ((1276678 / 93615) : ℂ) * ζ ^ 15 - ((561261 / 62410) : ℂ) * ζ ^ 16 + ((172176 / 31205) : ℂ) * ζ ^ 17 + ((1616423 / 93615) : ℂ) * ζ ^ 18 - ((244764 / 31205) : ℂ) * ζ ^ 19 + ((209322 / 31205) : ℂ) * ζ ^ 20 + ((461863 / 37446) : ℂ) * ζ ^ 21 - ((120098 / 31205) : ℂ) * ζ ^ 22 - ((22621 / 93615) : ℂ) * ζ ^ 23 + ((1349833 / 187230) : ℂ) * ζ ^ 24 - ((138097 / 93615) : ℂ) * ζ ^ 25 - ((37039 / 12482) : ℂ) * ζ ^ 26 + ((630031 / 93615) : ℂ) * ζ ^ 27 - ((43466 / 18723) : ℂ) * ζ ^ 28 + ((199609 / 187230) : ℂ) * ζ ^ 29 + ((9711 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep02Coefficient02 : ℂ :=
  (-((109 / 79) : ℂ) - ((312 / 79) : ℂ) * ζ ^ 1 - ((2353 / 474) : ℂ) * ζ ^ 2 + ((1203 / 158) : ℂ) * ζ ^ 3 - ((2653 / 237) : ℂ) * ζ ^ 5 - ((2105 / 474) : ℂ) * ζ ^ 6 - ((262 / 79) : ℂ) * ζ ^ 8 - ((781 / 474) : ℂ) * ζ ^ 9 - ((4913 / 474) : ℂ) * ζ ^ 11 - ((124 / 237) : ℂ) * ζ ^ 12 + ((312 / 79) : ℂ) * ζ ^ 13 - ((1203 / 158) : ℂ) * ζ ^ 15 + ((312 / 79) : ℂ) * ζ ^ 17 + ((3007 / 474) : ℂ) * ζ ^ 18 + ((1717 / 237) : ℂ) * ζ ^ 21 + ((2353 / 474) : ℂ) * ζ ^ 22 + ((2353 / 474) : ℂ) * ζ ^ 24 + ((1717 / 237) : ℂ) * ζ ^ 25 + ((4913 / 474) : ℂ) * ζ ^ 27 + ((262 / 79) : ℂ) * ζ ^ 28 - ((312 / 79) : ℂ) * ζ ^ 29 - ((781 / 474) : ℂ) * ζ ^ 30 + ((4913 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep02CoefficientIdentity02 :
    row18_reducedY55_combinationStep02Coefficient02 =
      row18_reducedY55_combinationStep01Coefficient02 +
        row18_reducedY55_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep02Coefficient02 row18_reducedY55_combinationStep01Coefficient02 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep02Coefficient03 : ℂ :=
  (((258 / 79) : ℂ) + ((142 / 79) : ℂ) * ζ ^ 1 - ((151 / 158) : ℂ) * ζ ^ 2 - ((465 / 158) : ℂ) * ζ ^ 3 + ((191 / 158) : ℂ) * ζ ^ 5 + ((214 / 237) : ℂ) * ζ ^ 6 - ((1039 / 474) : ℂ) * ζ ^ 8 - ((1043 / 474) : ℂ) * ζ ^ 9 + ((176 / 237) : ℂ) * ζ ^ 11 - ((1039 / 474) : ℂ) * ζ ^ 12 - ((142 / 79) : ℂ) * ζ ^ 13 + ((186 / 79) : ℂ) * ζ ^ 15 - ((142 / 79) : ℂ) * ζ ^ 17 - ((881 / 474) : ℂ) * ζ ^ 18 + ((181 / 158) : ℂ) * ζ ^ 21 + ((151 / 158) : ℂ) * ζ ^ 22 + ((93 / 158) : ℂ) * ζ ^ 25 - ((181 / 158) : ℂ) * ζ ^ 27 + ((1039 / 474) : ℂ) * ζ ^ 28 + ((142 / 79) : ℂ) * ζ ^ 29 + ((107 / 237) : ℂ) * ζ ^ 30 - ((176 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep02CoefficientIdentity03 :
    row18_reducedY55_combinationStep02Coefficient03 =
      row18_reducedY55_combinationStep01Coefficient03 +
        row18_reducedY55_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep02Coefficient03 row18_reducedY55_combinationStep01Coefficient03 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep02Coefficient04 : ℂ :=
  (-((2431 / 474) : ℂ) + ((683 / 237) : ℂ) * ζ ^ 1 - ((6988 / 1185) : ℂ) * ζ ^ 2 - ((200 / 237) : ℂ) * ζ ^ 3 - ((1967 / 474) : ℂ) * ζ ^ 5 - ((9277 / 1185) : ℂ) * ζ ^ 6 - ((226 / 79) : ℂ) * ζ ^ 8 - ((1493 / 237) : ℂ) * ζ ^ 9 - ((431 / 79) : ℂ) * ζ ^ 11 - ((226 / 79) : ℂ) * ζ ^ 12 - ((683 / 237) : ℂ) * ζ ^ 13 - ((2933 / 474) : ℂ) * ζ ^ 15 - ((683 / 237) : ℂ) * ζ ^ 17 + ((763 / 395) : ℂ) * ζ ^ 18 - ((161 / 79) : ℂ) * ζ ^ 21 + ((6988 / 1185) : ℂ) * ζ ^ 22 + ((1111 / 158) : ℂ) * ζ ^ 25 + ((161 / 79) : ℂ) * ζ ^ 27 + ((226 / 79) : ℂ) * ζ ^ 28 + ((683 / 237) : ℂ) * ζ ^ 29 - ((9277 / 2370) : ℂ) * ζ ^ 30 + ((431 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep02CoefficientIdentity04 :
    row18_reducedY55_combinationStep02Coefficient04 =
      row18_reducedY55_combinationStep01Coefficient04 +
        row18_reducedY55_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep02Coefficient04 row18_reducedY55_combinationStep01Coefficient04 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 (((194413 / 37446) : ℂ) - ((437317 / 187230) : ℂ) * ζ ^ 1 + ((960817 / 187230) : ℂ) * ζ ^ 2 + ((320989 / 62410) : ℂ) * ζ ^ 3 - ((1766387 / 187230) : ℂ) * ζ ^ 4 + ((240802 / 93615) : ℂ) * ζ ^ 5 + ((666823 / 187230) : ℂ) * ζ ^ 6 - ((145949 / 31205) : ℂ) * ζ ^ 7 + ((367227 / 62410) : ℂ) * ζ ^ 8 + ((3417 / 12482) : ℂ) * ζ ^ 9 - ((439447 / 93615) : ℂ) * ζ ^ 10 + ((383621 / 93615) : ℂ) * ζ ^ 11 + ((49643 / 62410) : ℂ) * ζ ^ 12 - ((945031 / 187230) : ℂ) * ζ ^ 13 + ((566773 / 93615) : ℂ) * ζ ^ 14 + ((138553 / 93615) : ℂ) * ζ ^ 15 - ((15653 / 6241) : ℂ) * ζ ^ 16 + ((470432 / 93615) : ℂ) * ζ ^ 17 - ((121617 / 62410) : ℂ) * ζ ^ 18 - ((913441 / 187230) : ℂ) * ζ ^ 19 + ((197213 / 187230) : ℂ) * ζ ^ 20 - ((300977 / 93615) : ℂ) * ζ ^ 21 - ((168566 / 93615) : ℂ) * ζ ^ 22 - ((10195 / 37446) : ℂ) * ζ ^ 23 + ((79294 / 93615) : ℂ) * ζ ^ 24 + ((78824 / 93615) : ℂ) * ζ ^ 25 - ((67409 / 187230) : ℂ) * ζ ^ 26 + ((209777 / 187230) : ℂ) * ζ ^ 27 - ((116723 / 93615) : ℂ) * ζ ^ 28 + ((743 / 1185) : ℂ) * ζ ^ 29 - ((10458 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep02CoefficientIdentity05 :
    row18_reducedY55_combinationStep02Coefficient05 =
      row18_reducedY55_combinationStep01Coefficient05 +
        row18_reducedY55_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep02Coefficient05 row18_reducedY55_combinationStep01Coefficient05 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep02Coefficient06 : ℂ :=
  (((1591 / 1185) : ℂ) + ((1619 / 237) : ℂ) * ζ ^ 1 + ((6707 / 1185) : ℂ) * ζ ^ 2 + ((2837 / 1185) : ℂ) * ζ ^ 3 - ((3067 / 1185) : ℂ) * ζ ^ 6 + ((2782 / 1185) : ℂ) * ζ ^ 8 + ((410 / 237) : ℂ) * ζ ^ 9 - ((7076 / 1185) : ℂ) * ζ ^ 11 - ((3258 / 395) : ℂ) * ζ ^ 12 - ((1619 / 237) : ℂ) * ζ ^ 13 + ((2837 / 1185) : ℂ) * ζ ^ 15 - ((1619 / 237) : ℂ) * ζ ^ 17 - ((5116 / 1185) : ℂ) * ζ ^ 18 - ((1619 / 237) : ℂ) * ζ ^ 21 - ((6707 / 1185) : ℂ) * ζ ^ 22 + ((6707 / 1185) : ℂ) * ζ ^ 24 + ((1619 / 237) : ℂ) * ζ ^ 25 - ((7076 / 1185) : ℂ) * ζ ^ 27 - ((2782 / 1185) : ℂ) * ζ ^ 28 + ((1619 / 237) : ℂ) * ζ ^ 29 + ((3163 / 395) : ℂ) * ζ ^ 30 + ((7076 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep02CoefficientIdentity06 :
    row18_reducedY55_combinationStep02Coefficient06 =
      row18_reducedY55_combinationStep01Coefficient06 +
        row18_reducedY55_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep02Coefficient06 row18_reducedY55_combinationStep01Coefficient06 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 (-((144404 / 93615) : ℂ) - ((541439 / 62410) : ℂ) * ζ ^ 1 - ((185809 / 62410) : ℂ) * ζ ^ 2 - ((322519 / 187230) : ℂ) * ζ ^ 3 + ((17065 / 6241) : ℂ) * ζ ^ 4 + ((252741 / 31205) : ℂ) * ζ ^ 5 + ((342761 / 62410) : ℂ) * ζ ^ 6 - ((70987 / 187230) : ℂ) * ζ ^ 7 - ((44887 / 62410) : ℂ) * ζ ^ 8 - ((223027 / 62410) : ℂ) * ζ ^ 9 - ((456196 / 93615) : ℂ) * ζ ^ 10 - ((45647 / 93615) : ℂ) * ζ ^ 11 + ((340361 / 93615) : ℂ) * ζ ^ 12 + ((468589 / 187230) : ℂ) * ζ ^ 13 + ((54664 / 31205) : ℂ) * ζ ^ 14 - ((475271 / 187230) : ℂ) * ζ ^ 15 - ((60633 / 12482) : ℂ) * ζ ^ 16 - ((500813 / 187230) : ℂ) * ζ ^ 17 - ((67453 / 187230) : ℂ) * ζ ^ 18 + ((29996 / 18723) : ℂ) * ζ ^ 19 + ((330907 / 93615) : ℂ) * ζ ^ 20 + ((130393 / 187230) : ℂ) * ζ ^ 21 - ((179599 / 93615) : ℂ) * ζ ^ 22 - ((49337 / 187230) : ℂ) * ζ ^ 23 - ((263026 / 93615) : ℂ) * ζ ^ 24 - ((525383 / 187230) : ℂ) * ζ ^ 25 + ((323302 / 93615) : ℂ) * ζ ^ 26 + ((28882 / 18723) : ℂ) * ζ ^ 27 + ((7167 / 31205) : ℂ) * ζ ^ 28 + ((55397 / 62410) : ℂ) * ζ ^ 29 + ((2241 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep02CoefficientIdentity07 :
    row18_reducedY55_combinationStep02Coefficient07 =
      row18_reducedY55_combinationStep01Coefficient07 +
        row18_reducedY55_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep02Coefficient07 row18_reducedY55_combinationStep01Coefficient07 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep02CoefficientIdentity08 :
    row18_reducedY55_combinationStep02Coefficient08 =
      row18_reducedY55_combinationStep01Coefficient08 +
        row18_reducedY55_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep02Coefficient08 row18_reducedY55_combinationStep01Coefficient08 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep02CoefficientIdentity09 :
    row18_reducedY55_combinationStep02Coefficient09 =
      row18_reducedY55_combinationStep01Coefficient09 +
        row18_reducedY55_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep02Coefficient09 row18_reducedY55_combinationStep01Coefficient09 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep02CoefficientIdentity10 :
    row18_reducedY55_combinationStep02Coefficient10 =
      row18_reducedY55_combinationStep01Coefficient10 +
        row18_reducedY55_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep02Coefficient10 row18_reducedY55_combinationStep01Coefficient10 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep02CoefficientIdentity11 :
    row18_reducedY55_combinationStep02Coefficient11 =
      row18_reducedY55_combinationStep01Coefficient11 +
        row18_reducedY55_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep02Coefficient11 row18_reducedY55_combinationStep01Coefficient11 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep02CoefficientIdentity12 :
    row18_reducedY55_combinationStep02Coefficient12 =
      row18_reducedY55_combinationStep01Coefficient12 +
        row18_reducedY55_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep02Coefficient12 row18_reducedY55_combinationStep01Coefficient12 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep02CoefficientIdentity13 :
    row18_reducedY55_combinationStep02Coefficient13 =
      row18_reducedY55_combinationStep01Coefficient13 +
        row18_reducedY55_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep02Coefficient13 row18_reducedY55_combinationStep01Coefficient13 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep02CoefficientIdentity14 :
    row18_reducedY55_combinationStep02Coefficient14 =
      row18_reducedY55_combinationStep01Coefficient14 +
        row18_reducedY55_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep02Coefficient14 row18_reducedY55_combinationStep01Coefficient14 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep02CoefficientIdentity15 :
    row18_reducedY55_combinationStep02Coefficient15 =
      row18_reducedY55_combinationStep01Coefficient15 +
        row18_reducedY55_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep02Coefficient15 row18_reducedY55_combinationStep01Coefficient15 row18_reducedY55_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY55_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY55_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY55_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY55_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY55_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY55_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY55_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY55_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY55_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY55_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY55_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY55_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY55_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY55_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY55_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY55_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY55_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY55_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY55_combinationStep02CoefficientIdentity00,
      row18_reducedY55_combinationStep02CoefficientIdentity01,
      row18_reducedY55_combinationStep02CoefficientIdentity02,
      row18_reducedY55_combinationStep02CoefficientIdentity03,
      row18_reducedY55_combinationStep02CoefficientIdentity04,
      row18_reducedY55_combinationStep02CoefficientIdentity05,
      row18_reducedY55_combinationStep02CoefficientIdentity06,
      row18_reducedY55_combinationStep02CoefficientIdentity07,
      row18_reducedY55_combinationStep02CoefficientIdentity08,
      row18_reducedY55_combinationStep02CoefficientIdentity09,
      row18_reducedY55_combinationStep02CoefficientIdentity10,
      row18_reducedY55_combinationStep02CoefficientIdentity11,
      row18_reducedY55_combinationStep02CoefficientIdentity12,
      row18_reducedY55_combinationStep02CoefficientIdentity13,
      row18_reducedY55_combinationStep02CoefficientIdentity14,
      row18_reducedY55_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY55_combinationStep02Multiplier * equation

private def row18_reducedY55_combinationStep03Multiplier : ℂ :=
  (((38 / 237) : ℂ) + ((460 / 79) : ℂ) * ζ ^ 1 - ((2956 / 237) : ℂ) * ζ ^ 2 - ((2968 / 237) : ℂ) * ζ ^ 5 - ((998 / 79) : ℂ) * ζ ^ 6 - ((998 / 79) : ℂ) * ζ ^ 8 - ((2968 / 237) : ℂ) * ζ ^ 9 - ((3922 / 237) : ℂ) * ζ ^ 11 - ((2774 / 237) : ℂ) * ζ ^ 12 - ((460 / 79) : ℂ) * ζ ^ 13 - ((572 / 79) : ℂ) * ζ ^ 15 - ((460 / 79) : ℂ) * ζ ^ 17 + ((976 / 237) : ℂ) * ζ ^ 18 + ((794 / 237) : ℂ) * ζ ^ 21 + ((2956 / 237) : ℂ) * ζ ^ 22 + ((2018 / 237) : ℂ) * ζ ^ 24 + ((4348 / 237) : ℂ) * ζ ^ 25 + ((572 / 79) : ℂ) * ζ ^ 27 + ((998 / 79) : ℂ) * ζ ^ 28 + ((460 / 79) : ℂ) * ζ ^ 29 - ((220 / 237) : ℂ) * ζ ^ 30 + ((3922 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY55_combinationStep03Coefficient00 : ℂ :=
  (((911 / 158) : ℂ) - ((646 / 237) : ℂ) * ζ ^ 1 + ((18391 / 2370) : ℂ) * ζ ^ 2 + ((365 / 474) : ℂ) * ζ ^ 3 + ((1288 / 237) : ℂ) * ζ ^ 5 + ((12887 / 1185) : ℂ) * ζ ^ 6 + ((1963 / 474) : ℂ) * ζ ^ 8 + ((3575 / 474) : ℂ) * ζ ^ 9 + ((535 / 79) : ℂ) * ζ ^ 11 + ((1963 / 474) : ℂ) * ζ ^ 12 + ((646 / 237) : ℂ) * ζ ^ 13 + ((3503 / 474) : ℂ) * ζ ^ 15 + ((646 / 237) : ℂ) * ζ ^ 17 - ((2461 / 790) : ℂ) * ζ ^ 18 + ((309 / 158) : ℂ) * ζ ^ 21 - ((18391 / 2370) : ℂ) * ζ ^ 22 - ((1934 / 237) : ℂ) * ζ ^ 25 - ((309 / 158) : ℂ) * ζ ^ 27 - ((1963 / 474) : ℂ) * ζ ^ 28 - ((646 / 237) : ℂ) * ζ ^ 29 + ((12887 / 2370) : ℂ) * ζ ^ 30 - ((535 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep03CoefficientIdentity00 :
    row18_reducedY55_combinationStep03Coefficient00 =
      row18_reducedY55_combinationStep02Coefficient00 +
        row18_reducedY55_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep03Coefficient00 row18_reducedY55_combinationStep02Coefficient00 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 (-((24238 / 6241) : ℂ) - ((15727 / 12482) : ℂ) * ζ ^ 1 - ((32965 / 12482) : ℂ) * ζ ^ 2 + ((69659 / 18723) : ℂ) * ζ ^ 3 + ((56305 / 18723) : ℂ) * ζ ^ 4 - ((67117 / 37446) : ℂ) * ζ ^ 5 - ((28647 / 12482) : ℂ) * ζ ^ 6 - ((112721 / 37446) : ℂ) * ζ ^ 7 - ((27932 / 6241) : ℂ) * ζ ^ 8 + ((29837 / 18723) : ℂ) * ζ ^ 9 + ((19668 / 6241) : ℂ) * ζ ^ 10 + ((9114 / 6241) : ℂ) * ζ ^ 11 + ((12292 / 18723) : ℂ) * ζ ^ 12 + ((3007 / 6241) : ℂ) * ζ ^ 13 - ((13023 / 12482) : ℂ) * ζ ^ 14 + ((26 / 6241) : ℂ) * ζ ^ 15 + ((6605 / 12482) : ℂ) * ζ ^ 16 + ((5153 / 6241) : ℂ) * ζ ^ 17 + ((16505 / 12482) : ℂ) * ζ ^ 18 + ((31123 / 18723) : ℂ) * ζ ^ 19 - ((12721 / 37446) : ℂ) * ζ ^ 20 - ((5678 / 18723) : ℂ) * ζ ^ 21 - ((16324 / 18723) : ℂ) * ζ ^ 22 - ((28321 / 12482) : ℂ) * ζ ^ 23 + ((19993 / 12482) : ℂ) * ζ ^ 24 + ((23631 / 12482) : ℂ) * ζ ^ 25 - ((20678 / 18723) : ℂ) * ζ ^ 26 + ((10259 / 6241) : ℂ) * ζ ^ 27 - ((30563 / 37446) : ℂ) * ζ ^ 28 - ((15413 / 6241) : ℂ) * ζ ^ 29 - ((9805 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep03Coefficient01 : ℂ :=
  (-((5 / 158) : ℂ) + ((149 / 237) : ℂ) * ζ ^ 1 + ((19 / 79) : ℂ) * ζ ^ 2 - ((11 / 79) : ℂ) * ζ ^ 3 + ((149 / 237) : ℂ) * ζ ^ 5 + ((33 / 158) : ℂ) * ζ ^ 6 - ((33 / 158) : ℂ) * ζ ^ 8 - ((149 / 237) : ℂ) * ζ ^ 9 + ((11 / 158) : ℂ) * ζ ^ 11 - ((67 / 474) : ℂ) * ζ ^ 12 - ((149 / 237) : ℂ) * ζ ^ 13 + ((35 / 237) : ℂ) * ζ ^ 15 - ((149 / 237) : ℂ) * ζ ^ 17 - ((4 / 237) : ℂ) * ζ ^ 18 - ((329 / 474) : ℂ) * ζ ^ 21 - ((19 / 79) : ℂ) * ζ ^ 22 + ((91 / 474) : ℂ) * ζ ^ 24 + ((2 / 237) : ℂ) * ζ ^ 27 + ((33 / 158) : ℂ) * ζ ^ 28 + ((149 / 237) : ℂ) * ζ ^ 29 + ((16 / 237) : ℂ) * ζ ^ 30 - ((11 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep03CoefficientIdentity01 :
    row18_reducedY55_combinationStep03Coefficient01 =
      row18_reducedY55_combinationStep02Coefficient01 +
        row18_reducedY55_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep03Coefficient01 row18_reducedY55_combinationStep02Coefficient01 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 (-((133838 / 18723) : ℂ) + ((545827 / 37446) : ℂ) * ζ ^ 1 + ((701 / 474) : ℂ) * ζ ^ 2 - ((604471 / 37446) : ℂ) * ζ ^ 3 - ((946 / 6241) : ℂ) * ζ ^ 4 + ((45017 / 37446) : ℂ) * ζ ^ 5 - ((328021 / 37446) : ℂ) * ζ ^ 6 + ((76591 / 18723) : ℂ) * ζ ^ 7 + ((18843 / 12482) : ℂ) * ζ ^ 8 - ((295757 / 18723) : ℂ) * ζ ^ 9 - ((5811 / 6241) : ℂ) * ζ ^ 10 - ((313423 / 37446) : ℂ) * ζ ^ 11 - ((271808 / 18723) : ℂ) * ζ ^ 12 + ((48436 / 18723) : ℂ) * ζ ^ 13 - ((250513 / 37446) : ℂ) * ζ ^ 14 - ((62513 / 6241) : ℂ) * ζ ^ 15 + ((83333 / 18723) : ℂ) * ζ ^ 16 - ((64854 / 6241) : ℂ) * ζ ^ 17 - ((87821 / 6241) : ℂ) * ζ ^ 18 - ((9496 / 18723) : ℂ) * ζ ^ 19 - ((122399 / 18723) : ℂ) * ζ ^ 20 - ((134689 / 18723) : ℂ) * ζ ^ 21 + ((108776 / 18723) : ℂ) * ζ ^ 22 - ((27799 / 18723) : ℂ) * ζ ^ 23 - ((86788 / 18723) : ℂ) * ζ ^ 24 + ((28319 / 12482) : ℂ) * ζ ^ 25 - ((36620 / 6241) : ℂ) * ζ ^ 26 + ((12623 / 6241) : ℂ) * ζ ^ 27 + ((42819 / 12482) : ℂ) * ζ ^ 28 + ((21992 / 18723) : ℂ) * ζ ^ 29 + ((27454 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep03Coefficient02 : ℂ :=
  (-((109 / 79) : ℂ) - ((312 / 79) : ℂ) * ζ ^ 1 - ((2353 / 474) : ℂ) * ζ ^ 2 + ((1203 / 158) : ℂ) * ζ ^ 3 - ((2653 / 237) : ℂ) * ζ ^ 5 - ((2105 / 474) : ℂ) * ζ ^ 6 - ((262 / 79) : ℂ) * ζ ^ 8 - ((781 / 474) : ℂ) * ζ ^ 9 - ((4913 / 474) : ℂ) * ζ ^ 11 - ((124 / 237) : ℂ) * ζ ^ 12 + ((312 / 79) : ℂ) * ζ ^ 13 - ((1203 / 158) : ℂ) * ζ ^ 15 + ((312 / 79) : ℂ) * ζ ^ 17 + ((3007 / 474) : ℂ) * ζ ^ 18 + ((1717 / 237) : ℂ) * ζ ^ 21 + ((2353 / 474) : ℂ) * ζ ^ 22 + ((2353 / 474) : ℂ) * ζ ^ 24 + ((1717 / 237) : ℂ) * ζ ^ 25 + ((4913 / 474) : ℂ) * ζ ^ 27 + ((262 / 79) : ℂ) * ζ ^ 28 - ((312 / 79) : ℂ) * ζ ^ 29 - ((781 / 474) : ℂ) * ζ ^ 30 + ((4913 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep03CoefficientIdentity02 :
    row18_reducedY55_combinationStep03Coefficient02 =
      row18_reducedY55_combinationStep02Coefficient02 +
        row18_reducedY55_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep03Coefficient02 row18_reducedY55_combinationStep02Coefficient02 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep03Coefficient03 : ℂ :=
  (((258 / 79) : ℂ) + ((142 / 79) : ℂ) * ζ ^ 1 - ((151 / 158) : ℂ) * ζ ^ 2 - ((465 / 158) : ℂ) * ζ ^ 3 + ((191 / 158) : ℂ) * ζ ^ 5 + ((214 / 237) : ℂ) * ζ ^ 6 - ((1039 / 474) : ℂ) * ζ ^ 8 - ((1043 / 474) : ℂ) * ζ ^ 9 + ((176 / 237) : ℂ) * ζ ^ 11 - ((1039 / 474) : ℂ) * ζ ^ 12 - ((142 / 79) : ℂ) * ζ ^ 13 + ((186 / 79) : ℂ) * ζ ^ 15 - ((142 / 79) : ℂ) * ζ ^ 17 - ((881 / 474) : ℂ) * ζ ^ 18 + ((181 / 158) : ℂ) * ζ ^ 21 + ((151 / 158) : ℂ) * ζ ^ 22 + ((93 / 158) : ℂ) * ζ ^ 25 - ((181 / 158) : ℂ) * ζ ^ 27 + ((1039 / 474) : ℂ) * ζ ^ 28 + ((142 / 79) : ℂ) * ζ ^ 29 + ((107 / 237) : ℂ) * ζ ^ 30 - ((176 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep03CoefficientIdentity03 :
    row18_reducedY55_combinationStep03Coefficient03 =
      row18_reducedY55_combinationStep02Coefficient03 +
        row18_reducedY55_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep03Coefficient03 row18_reducedY55_combinationStep02Coefficient03 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep03Coefficient04 : ℂ :=
  (-((2431 / 474) : ℂ) + ((683 / 237) : ℂ) * ζ ^ 1 - ((6988 / 1185) : ℂ) * ζ ^ 2 - ((200 / 237) : ℂ) * ζ ^ 3 - ((1967 / 474) : ℂ) * ζ ^ 5 - ((9277 / 1185) : ℂ) * ζ ^ 6 - ((226 / 79) : ℂ) * ζ ^ 8 - ((1493 / 237) : ℂ) * ζ ^ 9 - ((431 / 79) : ℂ) * ζ ^ 11 - ((226 / 79) : ℂ) * ζ ^ 12 - ((683 / 237) : ℂ) * ζ ^ 13 - ((2933 / 474) : ℂ) * ζ ^ 15 - ((683 / 237) : ℂ) * ζ ^ 17 + ((763 / 395) : ℂ) * ζ ^ 18 - ((161 / 79) : ℂ) * ζ ^ 21 + ((6988 / 1185) : ℂ) * ζ ^ 22 + ((1111 / 158) : ℂ) * ζ ^ 25 + ((161 / 79) : ℂ) * ζ ^ 27 + ((226 / 79) : ℂ) * ζ ^ 28 + ((683 / 237) : ℂ) * ζ ^ 29 - ((9277 / 2370) : ℂ) * ζ ^ 30 + ((431 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep03CoefficientIdentity04 :
    row18_reducedY55_combinationStep03Coefficient04 =
      row18_reducedY55_combinationStep02Coefficient04 +
        row18_reducedY55_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep03Coefficient04 row18_reducedY55_combinationStep02Coefficient04 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep03Coefficient05 : ℂ :=
  (-((59 / 79) : ℂ) + ((317 / 474) : ℂ) * ζ ^ 1 - ((3023 / 474) : ℂ) * ζ ^ 2 - ((2431 / 474) : ℂ) * ζ ^ 5 - ((2669 / 474) : ℂ) * ζ ^ 6 - ((2669 / 474) : ℂ) * ζ ^ 8 - ((2431 / 474) : ℂ) * ζ ^ 9 - ((2773 / 474) : ℂ) * ζ ^ 11 - ((818 / 237) : ℂ) * ζ ^ 12 - ((317 / 474) : ℂ) * ζ ^ 13 - ((1891 / 474) : ℂ) * ζ ^ 15 - ((317 / 474) : ℂ) * ζ ^ 17 + ((731 / 237) : ℂ) * ζ ^ 18 + ((1057 / 474) : ℂ) * ζ ^ 21 + ((3023 / 474) : ℂ) * ζ ^ 22 + ((1207 / 474) : ℂ) * ζ ^ 24 + ((458 / 79) : ℂ) * ζ ^ 25 + ((1891 / 474) : ℂ) * ζ ^ 27 + ((2669 / 474) : ℂ) * ζ ^ 28 + ((317 / 474) : ℂ) * ζ ^ 29 - ((1033 / 474) : ℂ) * ζ ^ 30 + ((2773 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep03CoefficientIdentity05 :
    row18_reducedY55_combinationStep03Coefficient05 =
      row18_reducedY55_combinationStep02Coefficient05 +
        row18_reducedY55_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep03Coefficient05 row18_reducedY55_combinationStep02Coefficient05 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 (((4699 / 6241) : ℂ) - ((8486 / 18723) : ℂ) * ζ ^ 1 + ((35851 / 6241) : ℂ) * ζ ^ 2 + ((37435 / 18723) : ℂ) * ζ ^ 3 - ((77602 / 18723) : ℂ) * ζ ^ 4 + ((97265 / 18723) : ℂ) * ζ ^ 5 + ((7823 / 37446) : ℂ) * ζ ^ 6 - ((63515 / 12482) : ℂ) * ζ ^ 7 + ((175853 / 37446) : ℂ) * ζ ^ 8 - ((4125 / 6241) : ℂ) * ζ ^ 9 - ((43465 / 18723) : ℂ) * ζ ^ 10 + ((56511 / 12482) : ℂ) * ζ ^ 11 - ((49429 / 37446) : ℂ) * ζ ^ 12 - ((49341 / 12482) : ℂ) * ζ ^ 13 + ((106730 / 18723) : ℂ) * ζ ^ 14 - ((46274 / 18723) : ℂ) * ζ ^ 15 - ((637 / 474) : ℂ) * ζ ^ 16 + ((33030 / 6241) : ℂ) * ζ ^ 17 - ((121501 / 37446) : ℂ) * ζ ^ 18 - ((57703 / 37446) : ℂ) * ζ ^ 19 + ((28267 / 18723) : ℂ) * ζ ^ 20 - ((52407 / 12482) : ℂ) * ζ ^ 21 - ((42085 / 37446) : ℂ) * ζ ^ 22 - ((12700 / 18723) : ℂ) * ζ ^ 23 - ((11144 / 18723) : ℂ) * ζ ^ 24 - ((10075 / 37446) : ℂ) * ζ ^ 25 + ((2461 / 37446) : ℂ) * ζ ^ 26 + ((59927 / 37446) : ℂ) * ζ ^ 27 - ((10997 / 12482) : ℂ) * ζ ^ 28 + ((5486 / 6241) : ℂ) * ζ ^ 29 - ((13727 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep03Coefficient06 : ℂ :=
  (((1591 / 1185) : ℂ) + ((1619 / 237) : ℂ) * ζ ^ 1 + ((6707 / 1185) : ℂ) * ζ ^ 2 + ((2837 / 1185) : ℂ) * ζ ^ 3 - ((3067 / 1185) : ℂ) * ζ ^ 6 + ((2782 / 1185) : ℂ) * ζ ^ 8 + ((410 / 237) : ℂ) * ζ ^ 9 - ((7076 / 1185) : ℂ) * ζ ^ 11 - ((3258 / 395) : ℂ) * ζ ^ 12 - ((1619 / 237) : ℂ) * ζ ^ 13 + ((2837 / 1185) : ℂ) * ζ ^ 15 - ((1619 / 237) : ℂ) * ζ ^ 17 - ((5116 / 1185) : ℂ) * ζ ^ 18 - ((1619 / 237) : ℂ) * ζ ^ 21 - ((6707 / 1185) : ℂ) * ζ ^ 22 + ((6707 / 1185) : ℂ) * ζ ^ 24 + ((1619 / 237) : ℂ) * ζ ^ 25 - ((7076 / 1185) : ℂ) * ζ ^ 27 - ((2782 / 1185) : ℂ) * ζ ^ 28 + ((1619 / 237) : ℂ) * ζ ^ 29 + ((3163 / 395) : ℂ) * ζ ^ 30 + ((7076 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep03CoefficientIdentity06 :
    row18_reducedY55_combinationStep03Coefficient06 =
      row18_reducedY55_combinationStep02Coefficient06 +
        row18_reducedY55_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep03Coefficient06 row18_reducedY55_combinationStep02Coefficient06 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep03Coefficient07 : ℂ :=
  (-((925 / 237) : ℂ) - ((463 / 237) : ℂ) * ζ ^ 1 - ((215 / 237) : ℂ) * ζ ^ 2 + ((715 / 237) : ℂ) * ζ ^ 3 - ((197 / 79) : ℂ) * ζ ^ 5 - ((312 / 79) : ℂ) * ζ ^ 6 + ((72 / 79) : ℂ) * ζ ^ 8 + ((227 / 237) : ℂ) * ζ ^ 9 - ((488 / 237) : ℂ) * ζ ^ 11 + ((72 / 79) : ℂ) * ζ ^ 12 + ((463 / 237) : ℂ) * ζ ^ 13 - ((281 / 79) : ℂ) * ζ ^ 15 + ((463 / 237) : ℂ) * ζ ^ 17 + ((721 / 237) : ℂ) * ζ ^ 18 - ((84 / 79) : ℂ) * ζ ^ 21 + ((215 / 237) : ℂ) * ζ ^ 22 + ((128 / 237) : ℂ) * ζ ^ 25 + ((84 / 79) : ℂ) * ζ ^ 27 - ((72 / 79) : ℂ) * ζ ^ 28 - ((463 / 237) : ℂ) * ζ ^ 29 - ((156 / 79) : ℂ) * ζ ^ 30 + ((488 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep03CoefficientIdentity07 :
    row18_reducedY55_combinationStep03Coefficient07 =
      row18_reducedY55_combinationStep02Coefficient07 +
        row18_reducedY55_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep03Coefficient07 row18_reducedY55_combinationStep02Coefficient07 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 (((24238 / 6241) : ℂ) + ((15727 / 12482) : ℂ) * ζ ^ 1 + ((32965 / 12482) : ℂ) * ζ ^ 2 - ((69659 / 18723) : ℂ) * ζ ^ 3 - ((56305 / 18723) : ℂ) * ζ ^ 4 + ((67117 / 37446) : ℂ) * ζ ^ 5 + ((28647 / 12482) : ℂ) * ζ ^ 6 + ((112721 / 37446) : ℂ) * ζ ^ 7 + ((27932 / 6241) : ℂ) * ζ ^ 8 - ((29837 / 18723) : ℂ) * ζ ^ 9 - ((19668 / 6241) : ℂ) * ζ ^ 10 - ((9114 / 6241) : ℂ) * ζ ^ 11 - ((12292 / 18723) : ℂ) * ζ ^ 12 - ((3007 / 6241) : ℂ) * ζ ^ 13 + ((13023 / 12482) : ℂ) * ζ ^ 14 - ((26 / 6241) : ℂ) * ζ ^ 15 - ((6605 / 12482) : ℂ) * ζ ^ 16 - ((5153 / 6241) : ℂ) * ζ ^ 17 - ((16505 / 12482) : ℂ) * ζ ^ 18 - ((31123 / 18723) : ℂ) * ζ ^ 19 + ((12721 / 37446) : ℂ) * ζ ^ 20 + ((5678 / 18723) : ℂ) * ζ ^ 21 + ((16324 / 18723) : ℂ) * ζ ^ 22 + ((28321 / 12482) : ℂ) * ζ ^ 23 - ((19993 / 12482) : ℂ) * ζ ^ 24 - ((23631 / 12482) : ℂ) * ζ ^ 25 + ((20678 / 18723) : ℂ) * ζ ^ 26 - ((10259 / 6241) : ℂ) * ζ ^ 27 + ((30563 / 37446) : ℂ) * ζ ^ 28 + ((15413 / 6241) : ℂ) * ζ ^ 29 + ((9805 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep03CoefficientIdentity08 :
    row18_reducedY55_combinationStep03Coefficient08 =
      row18_reducedY55_combinationStep02Coefficient08 +
        row18_reducedY55_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep03Coefficient08 row18_reducedY55_combinationStep02Coefficient08 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep03CoefficientIdentity09 :
    row18_reducedY55_combinationStep03Coefficient09 =
      row18_reducedY55_combinationStep02Coefficient09 +
        row18_reducedY55_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep03Coefficient09 row18_reducedY55_combinationStep02Coefficient09 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep03CoefficientIdentity10 :
    row18_reducedY55_combinationStep03Coefficient10 =
      row18_reducedY55_combinationStep02Coefficient10 +
        row18_reducedY55_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep03Coefficient10 row18_reducedY55_combinationStep02Coefficient10 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep03CoefficientIdentity11 :
    row18_reducedY55_combinationStep03Coefficient11 =
      row18_reducedY55_combinationStep02Coefficient11 +
        row18_reducedY55_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep03Coefficient11 row18_reducedY55_combinationStep02Coefficient11 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep03CoefficientIdentity12 :
    row18_reducedY55_combinationStep03Coefficient12 =
      row18_reducedY55_combinationStep02Coefficient12 +
        row18_reducedY55_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep03Coefficient12 row18_reducedY55_combinationStep02Coefficient12 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep03CoefficientIdentity13 :
    row18_reducedY55_combinationStep03Coefficient13 =
      row18_reducedY55_combinationStep02Coefficient13 +
        row18_reducedY55_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep03Coefficient13 row18_reducedY55_combinationStep02Coefficient13 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep03CoefficientIdentity14 :
    row18_reducedY55_combinationStep03Coefficient14 =
      row18_reducedY55_combinationStep02Coefficient14 +
        row18_reducedY55_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep03Coefficient14 row18_reducedY55_combinationStep02Coefficient14 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep03CoefficientIdentity15 :
    row18_reducedY55_combinationStep03Coefficient15 =
      row18_reducedY55_combinationStep02Coefficient15 +
        row18_reducedY55_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep03Coefficient15 row18_reducedY55_combinationStep02Coefficient15 row18_reducedY55_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY55_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY55_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY55_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY55_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY55_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY55_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY55_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY55_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY55_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY55_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY55_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY55_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY55_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY55_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY55_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY55_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY55_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY55_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY55_combinationStep03CoefficientIdentity00,
      row18_reducedY55_combinationStep03CoefficientIdentity01,
      row18_reducedY55_combinationStep03CoefficientIdentity02,
      row18_reducedY55_combinationStep03CoefficientIdentity03,
      row18_reducedY55_combinationStep03CoefficientIdentity04,
      row18_reducedY55_combinationStep03CoefficientIdentity05,
      row18_reducedY55_combinationStep03CoefficientIdentity06,
      row18_reducedY55_combinationStep03CoefficientIdentity07,
      row18_reducedY55_combinationStep03CoefficientIdentity08,
      row18_reducedY55_combinationStep03CoefficientIdentity09,
      row18_reducedY55_combinationStep03CoefficientIdentity10,
      row18_reducedY55_combinationStep03CoefficientIdentity11,
      row18_reducedY55_combinationStep03CoefficientIdentity12,
      row18_reducedY55_combinationStep03CoefficientIdentity13,
      row18_reducedY55_combinationStep03CoefficientIdentity14,
      row18_reducedY55_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY55_combinationStep03Multiplier * equation

private def row18_reducedY55_combinationStep04Multiplier : ℂ :=
  (-((374 / 237) : ℂ) + ((22 / 237) : ℂ) * ζ ^ 1 - ((226 / 237) : ℂ) * ζ ^ 2 + ((290 / 79) : ℂ) * ζ ^ 5 + ((148 / 237) : ℂ) * ζ ^ 6 + ((148 / 237) : ℂ) * ζ ^ 8 + ((290 / 79) : ℂ) * ζ ^ 9 - ((694 / 237) : ℂ) * ζ ^ 11 - ((78 / 79) : ℂ) * ζ ^ 12 - ((22 / 237) : ℂ) * ζ ^ 13 - ((218 / 237) : ℂ) * ζ ^ 15 - ((22 / 237) : ℂ) * ζ ^ 17 + ((84 / 79) : ℂ) * ζ ^ 18 - ((446 / 237) : ℂ) * ζ ^ 21 + ((226 / 237) : ℂ) * ζ ^ 22 - ((400 / 237) : ℂ) * ζ ^ 24 - ((848 / 237) : ℂ) * ζ ^ 25 + ((218 / 237) : ℂ) * ζ ^ 27 - ((148 / 237) : ℂ) * ζ ^ 28 + ((22 / 237) : ℂ) * ζ ^ 29 + ((382 / 237) : ℂ) * ζ ^ 30 + ((694 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY55_combinationStep04Coefficient00 : ℂ :=
  (((429 / 79) : ℂ) - ((224 / 79) : ℂ) * ζ ^ 1 + ((6197 / 790) : ℂ) * ζ ^ 2 + ((77 / 158) : ℂ) * ζ ^ 3 + ((809 / 158) : ℂ) * ζ ^ 5 + ((4254 / 395) : ℂ) * ζ ^ 6 + ((697 / 158) : ℂ) * ζ ^ 8 + ((1193 / 158) : ℂ) * ζ ^ 9 + ((558 / 79) : ℂ) * ζ ^ 11 + ((697 / 158) : ℂ) * ζ ^ 12 + ((224 / 79) : ℂ) * ζ ^ 13 + ((590 / 79) : ℂ) * ζ ^ 15 + ((224 / 79) : ℂ) * ζ ^ 17 - ((2311 / 790) : ℂ) * ζ ^ 18 + ((371 / 158) : ℂ) * ζ ^ 21 - ((6197 / 790) : ℂ) * ζ ^ 22 - ((1257 / 158) : ℂ) * ζ ^ 25 - ((371 / 158) : ℂ) * ζ ^ 27 - ((697 / 158) : ℂ) * ζ ^ 28 - ((224 / 79) : ℂ) * ζ ^ 29 + ((2127 / 395) : ℂ) * ζ ^ 30 - ((558 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep04CoefficientIdentity00 :
    row18_reducedY55_combinationStep04Coefficient00 =
      row18_reducedY55_combinationStep03Coefficient00 +
        row18_reducedY55_combinationStep04Multiplier *
          (((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep04Coefficient00 row18_reducedY55_combinationStep03Coefficient00 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 (-((2773 / 37446) : ℂ) + ((7441 / 37446) : ℂ) * ζ ^ 1 - ((6309 / 12482) : ℂ) * ζ ^ 2 + ((2647 / 12482) : ℂ) * ζ ^ 3 - ((805 / 37446) : ℂ) * ζ ^ 4 + ((236 / 237) : ℂ) * ζ ^ 5 + ((21233 / 37446) : ℂ) * ζ ^ 6 + ((3004 / 18723) : ℂ) * ζ ^ 7 + ((6627 / 12482) : ℂ) * ζ ^ 8 - ((15629 / 37446) : ℂ) * ζ ^ 9 - ((5555 / 12482) : ℂ) * ζ ^ 10 - ((14785 / 18723) : ℂ) * ζ ^ 11 - ((22459 / 37446) : ℂ) * ζ ^ 12 - ((19741 / 37446) : ℂ) * ζ ^ 13 + ((16807 / 37446) : ℂ) * ζ ^ 14 + ((4462 / 6241) : ℂ) * ζ ^ 15 + ((9259 / 37446) : ℂ) * ζ ^ 16 + ((7310 / 18723) : ℂ) * ζ ^ 17 + ((12271 / 37446) : ℂ) * ζ ^ 18 + ((2561 / 18723) : ℂ) * ζ ^ 19 - ((5344 / 18723) : ℂ) * ζ ^ 20 - ((17180 / 18723) : ℂ) * ζ ^ 21 + ((10897 / 37446) : ℂ) * ζ ^ 22 + ((8245 / 37446) : ℂ) * ζ ^ 23 - ((1244 / 6241) : ℂ) * ζ ^ 24 + ((2329 / 37446) : ℂ) * ζ ^ 25 + ((1577 / 12482) : ℂ) * ζ ^ 26 + ((5759 / 12482) : ℂ) * ζ ^ 27 - ((9503 / 37446) : ℂ) * ζ ^ 28 - ((1084 / 6241) : ℂ) * ζ ^ 29 + ((1735 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep04Coefficient01 : ℂ :=
  (-((33 / 158) : ℂ) + ((23 / 158) : ℂ) * ζ ^ 1 - ((7 / 158) : ℂ) * ζ ^ 2 - ((14 / 79) : ℂ) * ζ ^ 3 + ((23 / 158) : ℂ) * ζ ^ 5 - ((20 / 79) : ℂ) * ζ ^ 6 + ((20 / 79) : ℂ) * ζ ^ 8 - ((23 / 158) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((45 / 158) : ℂ) * ζ ^ 12 - ((23 / 158) : ℂ) * ζ ^ 13 - ((11 / 158) : ℂ) * ζ ^ 15 - ((23 / 158) : ℂ) * ζ ^ 17 + ((16 / 79) : ℂ) * ζ ^ 18 - ((29 / 79) : ℂ) * ζ ^ 21 + ((7 / 158) : ℂ) * ζ ^ 22 - ((4 / 79) : ℂ) * ζ ^ 24 - ((39 / 158) : ℂ) * ζ ^ 27 - ((20 / 79) : ℂ) * ζ ^ 28 + ((23 / 158) : ℂ) * ζ ^ 29 + ((5 / 158) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep04CoefficientIdentity01 :
    row18_reducedY55_combinationStep04Coefficient01 =
      row18_reducedY55_combinationStep03Coefficient01 +
        row18_reducedY55_combinationStep04Multiplier *
          (((16 / 79) : ℂ) + ((35 / 316) : ℂ) * ζ ^ 1 - ((61 / 316) : ℂ) * ζ ^ 2 + ((87 / 316) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 - ((6 / 79) : ℂ) * ζ ^ 8 - ((31 / 316) : ℂ) * ζ ^ 9 - ((14 / 79) : ℂ) * ζ ^ 11 - ((26 / 79) : ℂ) * ζ ^ 12 - ((35 / 316) : ℂ) * ζ ^ 13 - ((49 / 316) : ℂ) * ζ ^ 15 - ((35 / 316) : ℂ) * ζ ^ 17 + ((61 / 316) : ℂ) * ζ ^ 18 + ((13 / 79) : ℂ) * ζ ^ 21 + ((61 / 316) : ℂ) * ζ ^ 22 + ((32 / 79) : ℂ) * ζ ^ 24 + ((19 / 158) : ℂ) * ζ ^ 25 + ((13 / 79) : ℂ) * ζ ^ 27 + ((6 / 79) : ℂ) * ζ ^ 28 + ((35 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((14 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep04Coefficient01 row18_reducedY55_combinationStep03Coefficient01 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 (-((2666 / 18723) : ℂ) + ((6125 / 18723) : ℂ) * ζ ^ 1 + ((5075 / 12482) : ℂ) * ζ ^ 2 - ((6491 / 12482) : ℂ) * ζ ^ 3 + ((2197 / 6241) : ℂ) * ζ ^ 4 + ((103 / 158) : ℂ) * ζ ^ 5 + ((11002 / 18723) : ℂ) * ζ ^ 6 - ((4133 / 37446) : ℂ) * ζ ^ 7 + ((2012 / 6241) : ℂ) * ζ ^ 8 - ((101 / 37446) : ℂ) * ζ ^ 9 - ((3409 / 12482) : ℂ) * ζ ^ 10 - ((12565 / 18723) : ℂ) * ζ ^ 11 + ((1841 / 18723) : ℂ) * ζ ^ 12 + ((11695 / 37446) : ℂ) * ζ ^ 13 - ((1592 / 18723) : ℂ) * ζ ^ 14 + ((4067 / 18723) : ℂ) * ζ ^ 15 - ((4373 / 6241) : ℂ) * ζ ^ 16 - ((36865 / 37446) : ℂ) * ζ ^ 17 - ((2962 / 6241) : ℂ) * ζ ^ 18 - ((6813 / 12482) : ℂ) * ζ ^ 19 - ((8855 / 37446) : ℂ) * ζ ^ 20 + ((581 / 37446) : ℂ) * ζ ^ 21 + ((4019 / 12482) : ℂ) * ζ ^ 22 + ((49253 / 37446) : ℂ) * ζ ^ 23 - ((5770 / 18723) : ℂ) * ζ ^ 24 + ((1389 / 6241) : ℂ) * ζ ^ 25 + ((13237 / 37446) : ℂ) * ζ ^ 26 + ((3447 / 12482) : ℂ) * ζ ^ 27 + ((3593 / 37446) : ℂ) * ζ ^ 28 - ((2980 / 18723) : ℂ) * ζ ^ 29 + ((9716 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep04Coefficient02 : ℂ :=
  (-((109 / 79) : ℂ) - ((312 / 79) : ℂ) * ζ ^ 1 - ((2353 / 474) : ℂ) * ζ ^ 2 + ((1203 / 158) : ℂ) * ζ ^ 3 - ((2653 / 237) : ℂ) * ζ ^ 5 - ((2105 / 474) : ℂ) * ζ ^ 6 - ((262 / 79) : ℂ) * ζ ^ 8 - ((781 / 474) : ℂ) * ζ ^ 9 - ((4913 / 474) : ℂ) * ζ ^ 11 - ((124 / 237) : ℂ) * ζ ^ 12 + ((312 / 79) : ℂ) * ζ ^ 13 - ((1203 / 158) : ℂ) * ζ ^ 15 + ((312 / 79) : ℂ) * ζ ^ 17 + ((3007 / 474) : ℂ) * ζ ^ 18 + ((1717 / 237) : ℂ) * ζ ^ 21 + ((2353 / 474) : ℂ) * ζ ^ 22 + ((2353 / 474) : ℂ) * ζ ^ 24 + ((1717 / 237) : ℂ) * ζ ^ 25 + ((4913 / 474) : ℂ) * ζ ^ 27 + ((262 / 79) : ℂ) * ζ ^ 28 - ((312 / 79) : ℂ) * ζ ^ 29 - ((781 / 474) : ℂ) * ζ ^ 30 + ((4913 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep04CoefficientIdentity02 :
    row18_reducedY55_combinationStep04Coefficient02 =
      row18_reducedY55_combinationStep03Coefficient02 +
        row18_reducedY55_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep04Coefficient02 row18_reducedY55_combinationStep03Coefficient02 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep04Coefficient03 : ℂ :=
  (((258 / 79) : ℂ) + ((142 / 79) : ℂ) * ζ ^ 1 - ((151 / 158) : ℂ) * ζ ^ 2 - ((465 / 158) : ℂ) * ζ ^ 3 + ((191 / 158) : ℂ) * ζ ^ 5 + ((214 / 237) : ℂ) * ζ ^ 6 - ((1039 / 474) : ℂ) * ζ ^ 8 - ((1043 / 474) : ℂ) * ζ ^ 9 + ((176 / 237) : ℂ) * ζ ^ 11 - ((1039 / 474) : ℂ) * ζ ^ 12 - ((142 / 79) : ℂ) * ζ ^ 13 + ((186 / 79) : ℂ) * ζ ^ 15 - ((142 / 79) : ℂ) * ζ ^ 17 - ((881 / 474) : ℂ) * ζ ^ 18 + ((181 / 158) : ℂ) * ζ ^ 21 + ((151 / 158) : ℂ) * ζ ^ 22 + ((93 / 158) : ℂ) * ζ ^ 25 - ((181 / 158) : ℂ) * ζ ^ 27 + ((1039 / 474) : ℂ) * ζ ^ 28 + ((142 / 79) : ℂ) * ζ ^ 29 + ((107 / 237) : ℂ) * ζ ^ 30 - ((176 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep04CoefficientIdentity03 :
    row18_reducedY55_combinationStep04Coefficient03 =
      row18_reducedY55_combinationStep03Coefficient03 +
        row18_reducedY55_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep04Coefficient03 row18_reducedY55_combinationStep03Coefficient03 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep04Coefficient04 : ℂ :=
  (-((2431 / 474) : ℂ) + ((683 / 237) : ℂ) * ζ ^ 1 - ((6988 / 1185) : ℂ) * ζ ^ 2 - ((200 / 237) : ℂ) * ζ ^ 3 - ((1967 / 474) : ℂ) * ζ ^ 5 - ((9277 / 1185) : ℂ) * ζ ^ 6 - ((226 / 79) : ℂ) * ζ ^ 8 - ((1493 / 237) : ℂ) * ζ ^ 9 - ((431 / 79) : ℂ) * ζ ^ 11 - ((226 / 79) : ℂ) * ζ ^ 12 - ((683 / 237) : ℂ) * ζ ^ 13 - ((2933 / 474) : ℂ) * ζ ^ 15 - ((683 / 237) : ℂ) * ζ ^ 17 + ((763 / 395) : ℂ) * ζ ^ 18 - ((161 / 79) : ℂ) * ζ ^ 21 + ((6988 / 1185) : ℂ) * ζ ^ 22 + ((1111 / 158) : ℂ) * ζ ^ 25 + ((161 / 79) : ℂ) * ζ ^ 27 + ((226 / 79) : ℂ) * ζ ^ 28 + ((683 / 237) : ℂ) * ζ ^ 29 - ((9277 / 2370) : ℂ) * ζ ^ 30 + ((431 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep04CoefficientIdentity04 :
    row18_reducedY55_combinationStep04Coefficient04 =
      row18_reducedY55_combinationStep03Coefficient04 +
        row18_reducedY55_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep04Coefficient04 row18_reducedY55_combinationStep03Coefficient04 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep04Coefficient05 : ℂ :=
  (-((59 / 79) : ℂ) + ((317 / 474) : ℂ) * ζ ^ 1 - ((3023 / 474) : ℂ) * ζ ^ 2 - ((2431 / 474) : ℂ) * ζ ^ 5 - ((2669 / 474) : ℂ) * ζ ^ 6 - ((2669 / 474) : ℂ) * ζ ^ 8 - ((2431 / 474) : ℂ) * ζ ^ 9 - ((2773 / 474) : ℂ) * ζ ^ 11 - ((818 / 237) : ℂ) * ζ ^ 12 - ((317 / 474) : ℂ) * ζ ^ 13 - ((1891 / 474) : ℂ) * ζ ^ 15 - ((317 / 474) : ℂ) * ζ ^ 17 + ((731 / 237) : ℂ) * ζ ^ 18 + ((1057 / 474) : ℂ) * ζ ^ 21 + ((3023 / 474) : ℂ) * ζ ^ 22 + ((1207 / 474) : ℂ) * ζ ^ 24 + ((458 / 79) : ℂ) * ζ ^ 25 + ((1891 / 474) : ℂ) * ζ ^ 27 + ((2669 / 474) : ℂ) * ζ ^ 28 + ((317 / 474) : ℂ) * ζ ^ 29 - ((1033 / 474) : ℂ) * ζ ^ 30 + ((2773 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep04CoefficientIdentity05 :
    row18_reducedY55_combinationStep04Coefficient05 =
      row18_reducedY55_combinationStep03Coefficient05 +
        row18_reducedY55_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep04Coefficient05 row18_reducedY55_combinationStep03Coefficient05 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep04Coefficient06 : ℂ :=
  (((1591 / 1185) : ℂ) + ((1619 / 237) : ℂ) * ζ ^ 1 + ((6707 / 1185) : ℂ) * ζ ^ 2 + ((2837 / 1185) : ℂ) * ζ ^ 3 - ((3067 / 1185) : ℂ) * ζ ^ 6 + ((2782 / 1185) : ℂ) * ζ ^ 8 + ((410 / 237) : ℂ) * ζ ^ 9 - ((7076 / 1185) : ℂ) * ζ ^ 11 - ((3258 / 395) : ℂ) * ζ ^ 12 - ((1619 / 237) : ℂ) * ζ ^ 13 + ((2837 / 1185) : ℂ) * ζ ^ 15 - ((1619 / 237) : ℂ) * ζ ^ 17 - ((5116 / 1185) : ℂ) * ζ ^ 18 - ((1619 / 237) : ℂ) * ζ ^ 21 - ((6707 / 1185) : ℂ) * ζ ^ 22 + ((6707 / 1185) : ℂ) * ζ ^ 24 + ((1619 / 237) : ℂ) * ζ ^ 25 - ((7076 / 1185) : ℂ) * ζ ^ 27 - ((2782 / 1185) : ℂ) * ζ ^ 28 + ((1619 / 237) : ℂ) * ζ ^ 29 + ((3163 / 395) : ℂ) * ζ ^ 30 + ((7076 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep04CoefficientIdentity06 :
    row18_reducedY55_combinationStep04Coefficient06 =
      row18_reducedY55_combinationStep03Coefficient06 +
        row18_reducedY55_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep04Coefficient06 row18_reducedY55_combinationStep03Coefficient06 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep04Coefficient07 : ℂ :=
  (-((925 / 237) : ℂ) - ((463 / 237) : ℂ) * ζ ^ 1 - ((215 / 237) : ℂ) * ζ ^ 2 + ((715 / 237) : ℂ) * ζ ^ 3 - ((197 / 79) : ℂ) * ζ ^ 5 - ((312 / 79) : ℂ) * ζ ^ 6 + ((72 / 79) : ℂ) * ζ ^ 8 + ((227 / 237) : ℂ) * ζ ^ 9 - ((488 / 237) : ℂ) * ζ ^ 11 + ((72 / 79) : ℂ) * ζ ^ 12 + ((463 / 237) : ℂ) * ζ ^ 13 - ((281 / 79) : ℂ) * ζ ^ 15 + ((463 / 237) : ℂ) * ζ ^ 17 + ((721 / 237) : ℂ) * ζ ^ 18 - ((84 / 79) : ℂ) * ζ ^ 21 + ((215 / 237) : ℂ) * ζ ^ 22 + ((128 / 237) : ℂ) * ζ ^ 25 + ((84 / 79) : ℂ) * ζ ^ 27 - ((72 / 79) : ℂ) * ζ ^ 28 - ((463 / 237) : ℂ) * ζ ^ 29 - ((156 / 79) : ℂ) * ζ ^ 30 + ((488 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep04CoefficientIdentity07 :
    row18_reducedY55_combinationStep04Coefficient07 =
      row18_reducedY55_combinationStep03Coefficient07 +
        row18_reducedY55_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep04Coefficient07 row18_reducedY55_combinationStep03Coefficient07 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep04Coefficient08 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep04CoefficientIdentity08 :
    row18_reducedY55_combinationStep04Coefficient08 =
      row18_reducedY55_combinationStep03Coefficient08 +
        row18_reducedY55_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep04Coefficient08 row18_reducedY55_combinationStep03Coefficient08 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep04Coefficient09 : ℂ :=
  (-((51 / 158) : ℂ) + ((87 / 79) : ℂ) * ζ ^ 1 + ((925 / 474) : ℂ) * ζ ^ 2 + ((341 / 237) : ℂ) * ζ ^ 3 + ((87 / 79) : ℂ) * ζ ^ 5 + ((386 / 237) : ℂ) * ζ ^ 6 - ((386 / 237) : ℂ) * ζ ^ 8 - ((87 / 79) : ℂ) * ζ ^ 9 - ((341 / 474) : ℂ) * ζ ^ 11 - ((199 / 158) : ℂ) * ζ ^ 12 - ((87 / 79) : ℂ) * ζ ^ 13 + ((55 / 79) : ℂ) * ζ ^ 15 - ((87 / 79) : ℂ) * ζ ^ 17 - ((289 / 237) : ℂ) * ζ ^ 18 - ((243 / 158) : ℂ) * ζ ^ 21 - ((925 / 474) : ℂ) * ζ ^ 22 + ((97 / 237) : ℂ) * ζ ^ 24 + ((506 / 237) : ℂ) * ζ ^ 27 + ((386 / 237) : ℂ) * ζ ^ 28 + ((87 / 79) : ℂ) * ζ ^ 29 + ((175 / 474) : ℂ) * ζ ^ 30 + ((341 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep04CoefficientIdentity09 :
    row18_reducedY55_combinationStep04Coefficient09 =
      row18_reducedY55_combinationStep03Coefficient09 +
        row18_reducedY55_combinationStep04Multiplier *
          (((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((57 / 158) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((57 / 158) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((57 / 158) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep04Coefficient09 row18_reducedY55_combinationStep03Coefficient09 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 (((9095 / 37446) : ℂ) - ((39005 / 37446) : ℂ) * ζ ^ 1 - ((26843 / 18723) : ℂ) * ζ ^ 2 - ((54263 / 37446) : ℂ) * ζ ^ 3 + ((3809 / 37446) : ℂ) * ζ ^ 4 + ((2 / 79) : ℂ) * ζ ^ 5 - ((5347 / 18723) : ℂ) * ζ ^ 6 + ((856 / 18723) : ℂ) * ζ ^ 7 + ((51919 / 37446) : ℂ) * ζ ^ 8 + ((7379 / 6241) : ℂ) * ζ ^ 9 + ((3274 / 18723) : ℂ) * ζ ^ 10 - ((9033 / 12482) : ℂ) * ζ ^ 11 + ((1977 / 6241) : ℂ) * ζ ^ 12 - ((3337 / 37446) : ℂ) * ζ ^ 13 - ((31369 / 37446) : ℂ) * ζ ^ 14 - ((48329 / 37446) : ℂ) * ζ ^ 15 - ((5630 / 18723) : ℂ) * ζ ^ 16 + ((2018 / 18723) : ℂ) * ζ ^ 17 + ((415 / 12482) : ℂ) * ζ ^ 18 - ((2483 / 37446) : ℂ) * ζ ^ 19 + ((3558 / 6241) : ℂ) * ζ ^ 20 + ((39823 / 37446) : ℂ) * ζ ^ 21 + ((11171 / 37446) : ℂ) * ζ ^ 22 + ((2847 / 12482) : ℂ) * ζ ^ 23 - ((11891 / 37446) : ℂ) * ζ ^ 24 + ((3545 / 37446) : ℂ) * ζ ^ 25 + ((1546 / 18723) : ℂ) * ζ ^ 26 - ((1187 / 37446) : ℂ) * ζ ^ 27 - ((1985 / 12482) : ℂ) * ζ ^ 28 - ((745 / 18723) : ℂ) * ζ ^ 29 + ((2429 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep04Coefficient10 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep04CoefficientIdentity10 :
    row18_reducedY55_combinationStep04Coefficient10 =
      row18_reducedY55_combinationStep03Coefficient10 +
        row18_reducedY55_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep04Coefficient10 row18_reducedY55_combinationStep03Coefficient10 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep04Coefficient11 : ℂ :=
  (((53 / 158) : ℂ) + ((26 / 237) : ℂ) * ζ ^ 1 - ((20 / 237) : ℂ) * ζ ^ 2 + ((67 / 237) : ℂ) * ζ ^ 3 + ((149 / 474) : ℂ) * ζ ^ 5 + ((25 / 237) : ℂ) * ζ ^ 6 - ((64 / 237) : ℂ) * ζ ^ 8 - ((2 / 237) : ℂ) * ζ ^ 9 - ((23 / 79) : ℂ) * ζ ^ 11 - ((64 / 237) : ℂ) * ζ ^ 12 - ((26 / 237) : ℂ) * ζ ^ 13 - ((37 / 474) : ℂ) * ζ ^ 15 - ((26 / 237) : ℂ) * ζ ^ 17 - ((15 / 79) : ℂ) * ζ ^ 18 - ((31 / 79) : ℂ) * ζ ^ 21 + ((20 / 237) : ℂ) * ζ ^ 22 - ((97 / 474) : ℂ) * ζ ^ 25 + ((31 / 79) : ℂ) * ζ ^ 27 + ((64 / 237) : ℂ) * ζ ^ 28 + ((26 / 237) : ℂ) * ζ ^ 29 + ((25 / 474) : ℂ) * ζ ^ 30 + ((23 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep04CoefficientIdentity11 :
    row18_reducedY55_combinationStep04Coefficient11 =
      row18_reducedY55_combinationStep03Coefficient11 +
        row18_reducedY55_combinationStep04Multiplier *
          (-((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep04Coefficient11 row18_reducedY55_combinationStep03Coefficient11 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 (((2773 / 37446) : ℂ) - ((7441 / 37446) : ℂ) * ζ ^ 1 + ((6309 / 12482) : ℂ) * ζ ^ 2 - ((2647 / 12482) : ℂ) * ζ ^ 3 + ((805 / 37446) : ℂ) * ζ ^ 4 - ((236 / 237) : ℂ) * ζ ^ 5 - ((21233 / 37446) : ℂ) * ζ ^ 6 - ((3004 / 18723) : ℂ) * ζ ^ 7 - ((6627 / 12482) : ℂ) * ζ ^ 8 + ((15629 / 37446) : ℂ) * ζ ^ 9 + ((5555 / 12482) : ℂ) * ζ ^ 10 + ((14785 / 18723) : ℂ) * ζ ^ 11 + ((22459 / 37446) : ℂ) * ζ ^ 12 + ((19741 / 37446) : ℂ) * ζ ^ 13 - ((16807 / 37446) : ℂ) * ζ ^ 14 - ((4462 / 6241) : ℂ) * ζ ^ 15 - ((9259 / 37446) : ℂ) * ζ ^ 16 - ((7310 / 18723) : ℂ) * ζ ^ 17 - ((12271 / 37446) : ℂ) * ζ ^ 18 - ((2561 / 18723) : ℂ) * ζ ^ 19 + ((5344 / 18723) : ℂ) * ζ ^ 20 + ((17180 / 18723) : ℂ) * ζ ^ 21 - ((10897 / 37446) : ℂ) * ζ ^ 22 - ((8245 / 37446) : ℂ) * ζ ^ 23 + ((1244 / 6241) : ℂ) * ζ ^ 24 - ((2329 / 37446) : ℂ) * ζ ^ 25 - ((1577 / 12482) : ℂ) * ζ ^ 26 - ((5759 / 12482) : ℂ) * ζ ^ 27 + ((9503 / 37446) : ℂ) * ζ ^ 28 + ((1084 / 6241) : ℂ) * ζ ^ 29 - ((1735 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep04Coefficient12 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep04CoefficientIdentity12 :
    row18_reducedY55_combinationStep04Coefficient12 =
      row18_reducedY55_combinationStep03Coefficient12 +
        row18_reducedY55_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep04Coefficient12 row18_reducedY55_combinationStep03Coefficient12 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep04Coefficient13 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep04CoefficientIdentity13 :
    row18_reducedY55_combinationStep04Coefficient13 =
      row18_reducedY55_combinationStep03Coefficient13 +
        row18_reducedY55_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep04Coefficient13 row18_reducedY55_combinationStep03Coefficient13 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep04Coefficient14 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep04CoefficientIdentity14 :
    row18_reducedY55_combinationStep04Coefficient14 =
      row18_reducedY55_combinationStep03Coefficient14 +
        row18_reducedY55_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep04Coefficient14 row18_reducedY55_combinationStep03Coefficient14 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep04Coefficient15 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep04CoefficientIdentity15 :
    row18_reducedY55_combinationStep04Coefficient15 =
      row18_reducedY55_combinationStep03Coefficient15 +
        row18_reducedY55_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep04Coefficient15 row18_reducedY55_combinationStep03Coefficient15 row18_reducedY55_combinationStep04Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY55_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY55_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY55_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY55_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY55_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY55_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY55_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY55_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY55_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY55_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY55_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY55_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY55_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY55_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY55_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY55_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY55_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY55_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation05
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY55_combinationStep04CoefficientIdentity00,
      row18_reducedY55_combinationStep04CoefficientIdentity01,
      row18_reducedY55_combinationStep04CoefficientIdentity02,
      row18_reducedY55_combinationStep04CoefficientIdentity03,
      row18_reducedY55_combinationStep04CoefficientIdentity04,
      row18_reducedY55_combinationStep04CoefficientIdentity05,
      row18_reducedY55_combinationStep04CoefficientIdentity06,
      row18_reducedY55_combinationStep04CoefficientIdentity07,
      row18_reducedY55_combinationStep04CoefficientIdentity08,
      row18_reducedY55_combinationStep04CoefficientIdentity09,
      row18_reducedY55_combinationStep04CoefficientIdentity10,
      row18_reducedY55_combinationStep04CoefficientIdentity11,
      row18_reducedY55_combinationStep04CoefficientIdentity12,
      row18_reducedY55_combinationStep04CoefficientIdentity13,
      row18_reducedY55_combinationStep04CoefficientIdentity14,
      row18_reducedY55_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY55_combinationStep04Multiplier * equation

private def row18_reducedY55_combinationStep05Multiplier : ℂ :=
  (-((14 / 79) : ℂ) - ((120 / 79) : ℂ) * ζ ^ 1 - ((218 / 79) : ℂ) * ζ ^ 2 + ((52 / 79) : ℂ) * ζ ^ 5 - ((204 / 79) : ℂ) * ζ ^ 6 - ((204 / 79) : ℂ) * ζ ^ 8 + ((52 / 79) : ℂ) * ζ ^ 9 + ((94 / 79) : ℂ) * ζ ^ 11 - ((2 / 79) : ℂ) * ζ ^ 12 + ((120 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 + ((120 / 79) : ℂ) * ζ ^ 17 + ((148 / 79) : ℂ) * ζ ^ 18 + ((34 / 79) : ℂ) * ζ ^ 21 + ((218 / 79) : ℂ) * ζ ^ 22 + ((56 / 79) : ℂ) * ζ ^ 24 - ((172 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((204 / 79) : ℂ) * ζ ^ 28 - ((120 / 79) : ℂ) * ζ ^ 29 - ((202 / 79) : ℂ) * ζ ^ 30 - ((94 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY55_combinationStep05Coefficient00 : ℂ :=
  (((462 / 79) : ℂ) - ((248 / 79) : ℂ) * ζ ^ 1 + ((3051 / 395) : ℂ) * ζ ^ 2 + ((77 / 79) : ℂ) * ζ ^ 3 + ((414 / 79) : ℂ) * ζ ^ 5 + ((4264 / 395) : ℂ) * ζ ^ 6 + ((351 / 79) : ℂ) * ζ ^ 8 + ((644 / 79) : ℂ) * ζ ^ 9 + ((567 / 79) : ℂ) * ζ ^ 11 + ((351 / 79) : ℂ) * ζ ^ 12 + ((248 / 79) : ℂ) * ζ ^ 13 + ((585 / 79) : ℂ) * ζ ^ 15 + ((248 / 79) : ℂ) * ζ ^ 17 - ((1213 / 395) : ℂ) * ζ ^ 18 + ((171 / 79) : ℂ) * ζ ^ 21 - ((3051 / 395) : ℂ) * ζ ^ 22 - ((662 / 79) : ℂ) * ζ ^ 25 - ((171 / 79) : ℂ) * ζ ^ 27 - ((351 / 79) : ℂ) * ζ ^ 28 - ((248 / 79) : ℂ) * ζ ^ 29 + ((2132 / 395) : ℂ) * ζ ^ 30 - ((567 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep05CoefficientIdentity00 :
    row18_reducedY55_combinationStep05Coefficient00 =
      row18_reducedY55_combinationStep04Coefficient00 +
        row18_reducedY55_combinationStep05Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep05Coefficient00 row18_reducedY55_combinationStep04Coefficient00 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 (-((2474 / 6241) : ℂ) + ((6163 / 12482) : ℂ) * ζ ^ 1 + ((3250 / 6241) : ℂ) * ζ ^ 2 - ((1919 / 6241) : ℂ) * ζ ^ 3 + ((7587 / 12482) : ℂ) * ζ ^ 4 - ((3018 / 6241) : ℂ) * ζ ^ 5 - ((1520 / 6241) : ℂ) * ζ ^ 6 + ((3459 / 6241) : ℂ) * ζ ^ 7 - ((315 / 12482) : ℂ) * ζ ^ 8 - ((1635 / 12482) : ℂ) * ζ ^ 9 + ((2433 / 12482) : ℂ) * ζ ^ 10 + ((203 / 12482) : ℂ) * ζ ^ 11 - ((1748 / 6241) : ℂ) * ζ ^ 12 + ((1205 / 6241) : ℂ) * ζ ^ 13 - ((837 / 12482) : ℂ) * ζ ^ 14 + ((894 / 6241) : ℂ) * ζ ^ 15 + ((247 / 12482) : ℂ) * ζ ^ 16 + ((163 / 6241) : ℂ) * ζ ^ 17 + ((1985 / 12482) : ℂ) * ζ ^ 18 - ((1125 / 6241) : ℂ) * ζ ^ 19 + ((871 / 12482) : ℂ) * ζ ^ 20 + ((706 / 6241) : ℂ) * ζ ^ 21 - ((3236 / 6241) : ℂ) * ζ ^ 22 + ((2 / 79) : ℂ) * ζ ^ 23 - ((710 / 6241) : ℂ) * ζ ^ 24 + ((240 / 6241) : ℂ) * ζ ^ 25 + ((10525 / 12482) : ℂ) * ζ ^ 26 - ((162 / 6241) : ℂ) * ζ ^ 27 - ((3337 / 12482) : ℂ) * ζ ^ 28 - ((741 / 12482) : ℂ) * ζ ^ 29 + ((705 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep05Coefficient01 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep05CoefficientIdentity01 :
    row18_reducedY55_combinationStep05Coefficient01 =
      row18_reducedY55_combinationStep04Coefficient01 +
        row18_reducedY55_combinationStep05Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep05Coefficient01 row18_reducedY55_combinationStep04Coefficient01 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 (-((2719 / 12482) : ℂ) + ((390 / 6241) : ℂ) * ζ ^ 1 - ((1601 / 6241) : ℂ) * ζ ^ 2 - ((2752 / 6241) : ℂ) * ζ ^ 3 - ((518 / 6241) : ℂ) * ζ ^ 4 + ((676 / 6241) : ℂ) * ζ ^ 5 - ((1552 / 6241) : ℂ) * ζ ^ 6 + ((1011 / 6241) : ℂ) * ζ ^ 7 - ((495 / 6241) : ℂ) * ζ ^ 8 - ((1661 / 6241) : ℂ) * ζ ^ 9 + ((1017 / 6241) : ℂ) * ζ ^ 10 - ((893 / 12482) : ℂ) * ζ ^ 11 + ((1643 / 12482) : ℂ) * ζ ^ 12 + ((887 / 6241) : ℂ) * ζ ^ 13 - ((55 / 6241) : ℂ) * ζ ^ 14 - ((204 / 6241) : ℂ) * ζ ^ 15 - ((886 / 6241) : ℂ) * ζ ^ 16 + ((638 / 6241) : ℂ) * ζ ^ 17 + ((2889 / 12482) : ℂ) * ζ ^ 18 + ((2551 / 12482) : ℂ) * ζ ^ 19 + ((5915 / 12482) : ℂ) * ζ ^ 20 - ((4831 / 12482) : ℂ) * ζ ^ 21 - ((1303 / 6241) : ℂ) * ζ ^ 22 + ((594 / 6241) : ℂ) * ζ ^ 23 + ((2049 / 6241) : ℂ) * ζ ^ 24 + ((442 / 6241) : ℂ) * ζ ^ 25 + ((72 / 6241) : ℂ) * ζ ^ 26 - ((3541 / 12482) : ℂ) * ζ ^ 27 - ((889 / 12482) : ℂ) * ζ ^ 28 + ((425 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep05Coefficient02 : ℂ :=
  (-((109 / 79) : ℂ) - ((312 / 79) : ℂ) * ζ ^ 1 - ((2353 / 474) : ℂ) * ζ ^ 2 + ((1203 / 158) : ℂ) * ζ ^ 3 - ((2653 / 237) : ℂ) * ζ ^ 5 - ((2105 / 474) : ℂ) * ζ ^ 6 - ((262 / 79) : ℂ) * ζ ^ 8 - ((781 / 474) : ℂ) * ζ ^ 9 - ((4913 / 474) : ℂ) * ζ ^ 11 - ((124 / 237) : ℂ) * ζ ^ 12 + ((312 / 79) : ℂ) * ζ ^ 13 - ((1203 / 158) : ℂ) * ζ ^ 15 + ((312 / 79) : ℂ) * ζ ^ 17 + ((3007 / 474) : ℂ) * ζ ^ 18 + ((1717 / 237) : ℂ) * ζ ^ 21 + ((2353 / 474) : ℂ) * ζ ^ 22 + ((2353 / 474) : ℂ) * ζ ^ 24 + ((1717 / 237) : ℂ) * ζ ^ 25 + ((4913 / 474) : ℂ) * ζ ^ 27 + ((262 / 79) : ℂ) * ζ ^ 28 - ((312 / 79) : ℂ) * ζ ^ 29 - ((781 / 474) : ℂ) * ζ ^ 30 + ((4913 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep05CoefficientIdentity02 :
    row18_reducedY55_combinationStep05Coefficient02 =
      row18_reducedY55_combinationStep04Coefficient02 +
        row18_reducedY55_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep05Coefficient02 row18_reducedY55_combinationStep04Coefficient02 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep05Coefficient03 : ℂ :=
  (((258 / 79) : ℂ) + ((142 / 79) : ℂ) * ζ ^ 1 - ((151 / 158) : ℂ) * ζ ^ 2 - ((465 / 158) : ℂ) * ζ ^ 3 + ((191 / 158) : ℂ) * ζ ^ 5 + ((214 / 237) : ℂ) * ζ ^ 6 - ((1039 / 474) : ℂ) * ζ ^ 8 - ((1043 / 474) : ℂ) * ζ ^ 9 + ((176 / 237) : ℂ) * ζ ^ 11 - ((1039 / 474) : ℂ) * ζ ^ 12 - ((142 / 79) : ℂ) * ζ ^ 13 + ((186 / 79) : ℂ) * ζ ^ 15 - ((142 / 79) : ℂ) * ζ ^ 17 - ((881 / 474) : ℂ) * ζ ^ 18 + ((181 / 158) : ℂ) * ζ ^ 21 + ((151 / 158) : ℂ) * ζ ^ 22 + ((93 / 158) : ℂ) * ζ ^ 25 - ((181 / 158) : ℂ) * ζ ^ 27 + ((1039 / 474) : ℂ) * ζ ^ 28 + ((142 / 79) : ℂ) * ζ ^ 29 + ((107 / 237) : ℂ) * ζ ^ 30 - ((176 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep05CoefficientIdentity03 :
    row18_reducedY55_combinationStep05Coefficient03 =
      row18_reducedY55_combinationStep04Coefficient03 +
        row18_reducedY55_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep05Coefficient03 row18_reducedY55_combinationStep04Coefficient03 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep05Coefficient04 : ℂ :=
  (-((2431 / 474) : ℂ) + ((683 / 237) : ℂ) * ζ ^ 1 - ((6988 / 1185) : ℂ) * ζ ^ 2 - ((200 / 237) : ℂ) * ζ ^ 3 - ((1967 / 474) : ℂ) * ζ ^ 5 - ((9277 / 1185) : ℂ) * ζ ^ 6 - ((226 / 79) : ℂ) * ζ ^ 8 - ((1493 / 237) : ℂ) * ζ ^ 9 - ((431 / 79) : ℂ) * ζ ^ 11 - ((226 / 79) : ℂ) * ζ ^ 12 - ((683 / 237) : ℂ) * ζ ^ 13 - ((2933 / 474) : ℂ) * ζ ^ 15 - ((683 / 237) : ℂ) * ζ ^ 17 + ((763 / 395) : ℂ) * ζ ^ 18 - ((161 / 79) : ℂ) * ζ ^ 21 + ((6988 / 1185) : ℂ) * ζ ^ 22 + ((1111 / 158) : ℂ) * ζ ^ 25 + ((161 / 79) : ℂ) * ζ ^ 27 + ((226 / 79) : ℂ) * ζ ^ 28 + ((683 / 237) : ℂ) * ζ ^ 29 - ((9277 / 2370) : ℂ) * ζ ^ 30 + ((431 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep05CoefficientIdentity04 :
    row18_reducedY55_combinationStep05Coefficient04 =
      row18_reducedY55_combinationStep04Coefficient04 +
        row18_reducedY55_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep05Coefficient04 row18_reducedY55_combinationStep04Coefficient04 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep05Coefficient05 : ℂ :=
  (-((59 / 79) : ℂ) + ((317 / 474) : ℂ) * ζ ^ 1 - ((3023 / 474) : ℂ) * ζ ^ 2 - ((2431 / 474) : ℂ) * ζ ^ 5 - ((2669 / 474) : ℂ) * ζ ^ 6 - ((2669 / 474) : ℂ) * ζ ^ 8 - ((2431 / 474) : ℂ) * ζ ^ 9 - ((2773 / 474) : ℂ) * ζ ^ 11 - ((818 / 237) : ℂ) * ζ ^ 12 - ((317 / 474) : ℂ) * ζ ^ 13 - ((1891 / 474) : ℂ) * ζ ^ 15 - ((317 / 474) : ℂ) * ζ ^ 17 + ((731 / 237) : ℂ) * ζ ^ 18 + ((1057 / 474) : ℂ) * ζ ^ 21 + ((3023 / 474) : ℂ) * ζ ^ 22 + ((1207 / 474) : ℂ) * ζ ^ 24 + ((458 / 79) : ℂ) * ζ ^ 25 + ((1891 / 474) : ℂ) * ζ ^ 27 + ((2669 / 474) : ℂ) * ζ ^ 28 + ((317 / 474) : ℂ) * ζ ^ 29 - ((1033 / 474) : ℂ) * ζ ^ 30 + ((2773 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep05CoefficientIdentity05 :
    row18_reducedY55_combinationStep05Coefficient05 =
      row18_reducedY55_combinationStep04Coefficient05 +
        row18_reducedY55_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep05Coefficient05 row18_reducedY55_combinationStep04Coefficient05 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep05Coefficient06 : ℂ :=
  (((1591 / 1185) : ℂ) + ((1619 / 237) : ℂ) * ζ ^ 1 + ((6707 / 1185) : ℂ) * ζ ^ 2 + ((2837 / 1185) : ℂ) * ζ ^ 3 - ((3067 / 1185) : ℂ) * ζ ^ 6 + ((2782 / 1185) : ℂ) * ζ ^ 8 + ((410 / 237) : ℂ) * ζ ^ 9 - ((7076 / 1185) : ℂ) * ζ ^ 11 - ((3258 / 395) : ℂ) * ζ ^ 12 - ((1619 / 237) : ℂ) * ζ ^ 13 + ((2837 / 1185) : ℂ) * ζ ^ 15 - ((1619 / 237) : ℂ) * ζ ^ 17 - ((5116 / 1185) : ℂ) * ζ ^ 18 - ((1619 / 237) : ℂ) * ζ ^ 21 - ((6707 / 1185) : ℂ) * ζ ^ 22 + ((6707 / 1185) : ℂ) * ζ ^ 24 + ((1619 / 237) : ℂ) * ζ ^ 25 - ((7076 / 1185) : ℂ) * ζ ^ 27 - ((2782 / 1185) : ℂ) * ζ ^ 28 + ((1619 / 237) : ℂ) * ζ ^ 29 + ((3163 / 395) : ℂ) * ζ ^ 30 + ((7076 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep05CoefficientIdentity06 :
    row18_reducedY55_combinationStep05Coefficient06 =
      row18_reducedY55_combinationStep04Coefficient06 +
        row18_reducedY55_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep05Coefficient06 row18_reducedY55_combinationStep04Coefficient06 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep05Coefficient07 : ℂ :=
  (-((925 / 237) : ℂ) - ((463 / 237) : ℂ) * ζ ^ 1 - ((215 / 237) : ℂ) * ζ ^ 2 + ((715 / 237) : ℂ) * ζ ^ 3 - ((197 / 79) : ℂ) * ζ ^ 5 - ((312 / 79) : ℂ) * ζ ^ 6 + ((72 / 79) : ℂ) * ζ ^ 8 + ((227 / 237) : ℂ) * ζ ^ 9 - ((488 / 237) : ℂ) * ζ ^ 11 + ((72 / 79) : ℂ) * ζ ^ 12 + ((463 / 237) : ℂ) * ζ ^ 13 - ((281 / 79) : ℂ) * ζ ^ 15 + ((463 / 237) : ℂ) * ζ ^ 17 + ((721 / 237) : ℂ) * ζ ^ 18 - ((84 / 79) : ℂ) * ζ ^ 21 + ((215 / 237) : ℂ) * ζ ^ 22 + ((128 / 237) : ℂ) * ζ ^ 25 + ((84 / 79) : ℂ) * ζ ^ 27 - ((72 / 79) : ℂ) * ζ ^ 28 - ((463 / 237) : ℂ) * ζ ^ 29 - ((156 / 79) : ℂ) * ζ ^ 30 + ((488 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep05CoefficientIdentity07 :
    row18_reducedY55_combinationStep05Coefficient07 =
      row18_reducedY55_combinationStep04Coefficient07 +
        row18_reducedY55_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep05Coefficient07 row18_reducedY55_combinationStep04Coefficient07 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep05Coefficient08 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep05CoefficientIdentity08 :
    row18_reducedY55_combinationStep05Coefficient08 =
      row18_reducedY55_combinationStep04Coefficient08 +
        row18_reducedY55_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep05Coefficient08 row18_reducedY55_combinationStep04Coefficient08 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep05Coefficient09 : ℂ :=
  (-((51 / 158) : ℂ) + ((87 / 79) : ℂ) * ζ ^ 1 + ((925 / 474) : ℂ) * ζ ^ 2 + ((341 / 237) : ℂ) * ζ ^ 3 + ((87 / 79) : ℂ) * ζ ^ 5 + ((386 / 237) : ℂ) * ζ ^ 6 - ((386 / 237) : ℂ) * ζ ^ 8 - ((87 / 79) : ℂ) * ζ ^ 9 - ((341 / 474) : ℂ) * ζ ^ 11 - ((199 / 158) : ℂ) * ζ ^ 12 - ((87 / 79) : ℂ) * ζ ^ 13 + ((55 / 79) : ℂ) * ζ ^ 15 - ((87 / 79) : ℂ) * ζ ^ 17 - ((289 / 237) : ℂ) * ζ ^ 18 - ((243 / 158) : ℂ) * ζ ^ 21 - ((925 / 474) : ℂ) * ζ ^ 22 + ((97 / 237) : ℂ) * ζ ^ 24 + ((506 / 237) : ℂ) * ζ ^ 27 + ((386 / 237) : ℂ) * ζ ^ 28 + ((87 / 79) : ℂ) * ζ ^ 29 + ((175 / 474) : ℂ) * ζ ^ 30 + ((341 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep05CoefficientIdentity09 :
    row18_reducedY55_combinationStep05Coefficient09 =
      row18_reducedY55_combinationStep04Coefficient09 +
        row18_reducedY55_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep05Coefficient09 row18_reducedY55_combinationStep04Coefficient09 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep05Coefficient10 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep05CoefficientIdentity10 :
    row18_reducedY55_combinationStep05Coefficient10 =
      row18_reducedY55_combinationStep04Coefficient10 +
        row18_reducedY55_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep05Coefficient10 row18_reducedY55_combinationStep04Coefficient10 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep05Coefficient11 : ℂ :=
  (((53 / 158) : ℂ) + ((26 / 237) : ℂ) * ζ ^ 1 - ((20 / 237) : ℂ) * ζ ^ 2 + ((67 / 237) : ℂ) * ζ ^ 3 + ((149 / 474) : ℂ) * ζ ^ 5 + ((25 / 237) : ℂ) * ζ ^ 6 - ((64 / 237) : ℂ) * ζ ^ 8 - ((2 / 237) : ℂ) * ζ ^ 9 - ((23 / 79) : ℂ) * ζ ^ 11 - ((64 / 237) : ℂ) * ζ ^ 12 - ((26 / 237) : ℂ) * ζ ^ 13 - ((37 / 474) : ℂ) * ζ ^ 15 - ((26 / 237) : ℂ) * ζ ^ 17 - ((15 / 79) : ℂ) * ζ ^ 18 - ((31 / 79) : ℂ) * ζ ^ 21 + ((20 / 237) : ℂ) * ζ ^ 22 - ((97 / 474) : ℂ) * ζ ^ 25 + ((31 / 79) : ℂ) * ζ ^ 27 + ((64 / 237) : ℂ) * ζ ^ 28 + ((26 / 237) : ℂ) * ζ ^ 29 + ((25 / 474) : ℂ) * ζ ^ 30 + ((23 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep05CoefficientIdentity11 :
    row18_reducedY55_combinationStep05Coefficient11 =
      row18_reducedY55_combinationStep04Coefficient11 +
        row18_reducedY55_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep05Coefficient11 row18_reducedY55_combinationStep04Coefficient11 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep05Coefficient12 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep05CoefficientIdentity12 :
    row18_reducedY55_combinationStep05Coefficient12 =
      row18_reducedY55_combinationStep04Coefficient12 +
        row18_reducedY55_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep05Coefficient12 row18_reducedY55_combinationStep04Coefficient12 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep05Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep05CoefficientIdentity13 :
    row18_reducedY55_combinationStep05Coefficient13 =
      row18_reducedY55_combinationStep04Coefficient13 +
        row18_reducedY55_combinationStep05Multiplier *
          (-((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((73 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((105 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((73 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep05Coefficient13 row18_reducedY55_combinationStep04Coefficient13 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 (-((3276 / 6241) : ℂ) - ((625 / 12482) : ℂ) * ζ ^ 1 + ((689 / 6241) : ℂ) * ζ ^ 2 - ((3167 / 12482) : ℂ) * ζ ^ 3 - ((1285 / 12482) : ℂ) * ζ ^ 4 - ((117 / 6241) : ℂ) * ζ ^ 5 + ((5201 / 12482) : ℂ) * ζ ^ 6 + ((3018 / 6241) : ℂ) * ζ ^ 7 + ((4811 / 12482) : ℂ) * ζ ^ 8 - ((784 / 6241) : ℂ) * ζ ^ 9 - ((8487 / 6241) : ℂ) * ζ ^ 10 - ((4803 / 12482) : ℂ) * ζ ^ 11 + ((6691 / 12482) : ℂ) * ζ ^ 12 + ((178 / 6241) : ℂ) * ζ ^ 13 + ((6775 / 6241) : ℂ) * ζ ^ 14 - ((4021 / 12482) : ℂ) * ζ ^ 15 - ((19101 / 12482) : ℂ) * ζ ^ 16 - ((4973 / 12482) : ℂ) * ζ ^ 17 - ((4376 / 6241) : ℂ) * ζ ^ 18 + ((66 / 6241) : ℂ) * ζ ^ 19 + ((8447 / 12482) : ℂ) * ζ ^ 20 + ((551 / 6241) : ℂ) * ζ ^ 21 - ((119 / 6241) : ℂ) * ζ ^ 22 + ((550 / 6241) : ℂ) * ζ ^ 23 - ((2929 / 12482) : ℂ) * ζ ^ 24 + ((445 / 12482) : ℂ) * ζ ^ 25 + ((1398 / 6241) : ℂ) * ζ ^ 26 + ((1144 / 6241) : ℂ) * ζ ^ 27 + ((2973 / 12482) : ℂ) * ζ ^ 28 + ((1083 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep05Coefficient14 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep05CoefficientIdentity14 :
    row18_reducedY55_combinationStep05Coefficient14 =
      row18_reducedY55_combinationStep04Coefficient14 +
        row18_reducedY55_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep05Coefficient14 row18_reducedY55_combinationStep04Coefficient14 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep05Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep05CoefficientIdentity15 :
    row18_reducedY55_combinationStep05Coefficient15 =
      row18_reducedY55_combinationStep04Coefficient15 +
        row18_reducedY55_combinationStep05Multiplier *
          (((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep05Coefficient15 row18_reducedY55_combinationStep04Coefficient15 row18_reducedY55_combinationStep05Multiplier
  close_cyclotomic_row18 (((2474 / 6241) : ℂ) - ((6163 / 12482) : ℂ) * ζ ^ 1 - ((3250 / 6241) : ℂ) * ζ ^ 2 + ((1919 / 6241) : ℂ) * ζ ^ 3 - ((7587 / 12482) : ℂ) * ζ ^ 4 + ((3018 / 6241) : ℂ) * ζ ^ 5 + ((1520 / 6241) : ℂ) * ζ ^ 6 - ((3459 / 6241) : ℂ) * ζ ^ 7 + ((315 / 12482) : ℂ) * ζ ^ 8 + ((1635 / 12482) : ℂ) * ζ ^ 9 - ((2433 / 12482) : ℂ) * ζ ^ 10 - ((203 / 12482) : ℂ) * ζ ^ 11 + ((1748 / 6241) : ℂ) * ζ ^ 12 - ((1205 / 6241) : ℂ) * ζ ^ 13 + ((837 / 12482) : ℂ) * ζ ^ 14 - ((894 / 6241) : ℂ) * ζ ^ 15 - ((247 / 12482) : ℂ) * ζ ^ 16 - ((163 / 6241) : ℂ) * ζ ^ 17 - ((1985 / 12482) : ℂ) * ζ ^ 18 + ((1125 / 6241) : ℂ) * ζ ^ 19 - ((871 / 12482) : ℂ) * ζ ^ 20 - ((706 / 6241) : ℂ) * ζ ^ 21 + ((3236 / 6241) : ℂ) * ζ ^ 22 - ((2 / 79) : ℂ) * ζ ^ 23 + ((710 / 6241) : ℂ) * ζ ^ 24 - ((240 / 6241) : ℂ) * ζ ^ 25 - ((10525 / 12482) : ℂ) * ζ ^ 26 + ((162 / 6241) : ℂ) * ζ ^ 27 + ((3337 / 12482) : ℂ) * ζ ^ 28 + ((741 / 12482) : ℂ) * ζ ^ 29 - ((705 / 12482) : ℂ) * ζ ^ 30)

private theorem row18_reducedY55_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY55_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY55_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY55_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY55_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY55_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY55_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY55_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY55_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY55_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY55_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY55_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY55_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY55_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY55_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY55_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY55_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY55_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation07
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY55_combinationStep05CoefficientIdentity00,
      row18_reducedY55_combinationStep05CoefficientIdentity01,
      row18_reducedY55_combinationStep05CoefficientIdentity02,
      row18_reducedY55_combinationStep05CoefficientIdentity03,
      row18_reducedY55_combinationStep05CoefficientIdentity04,
      row18_reducedY55_combinationStep05CoefficientIdentity05,
      row18_reducedY55_combinationStep05CoefficientIdentity06,
      row18_reducedY55_combinationStep05CoefficientIdentity07,
      row18_reducedY55_combinationStep05CoefficientIdentity08,
      row18_reducedY55_combinationStep05CoefficientIdentity09,
      row18_reducedY55_combinationStep05CoefficientIdentity10,
      row18_reducedY55_combinationStep05CoefficientIdentity11,
      row18_reducedY55_combinationStep05CoefficientIdentity12,
      row18_reducedY55_combinationStep05CoefficientIdentity13,
      row18_reducedY55_combinationStep05CoefficientIdentity14,
      row18_reducedY55_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY55_combinationStep05Multiplier * equation

private def row18_reducedY55_combinationStep06Multiplier : ℂ :=
  (((1454 / 237) : ℂ) + ((7834 / 1185) : ℂ) * ζ ^ 1 + ((374 / 237) : ℂ) * ζ ^ 2 - ((1156 / 237) : ℂ) * ζ ^ 3 + ((5072 / 1185) : ℂ) * ζ ^ 5 + ((470 / 79) : ℂ) * ζ ^ 6 + ((14 / 237) : ℂ) * ζ ^ 8 - ((1766 / 395) : ℂ) * ζ ^ 9 + ((286 / 237) : ℂ) * ζ ^ 11 - ((1036 / 237) : ℂ) * ζ ^ 12 - ((7834 / 1185) : ℂ) * ζ ^ 13 + ((1156 / 237) : ℂ) * ζ ^ 15 - ((7834 / 1185) : ℂ) * ζ ^ 17 - ((1828 / 237) : ℂ) * ζ ^ 18 + ((2762 / 1185) : ℂ) * ζ ^ 21 - ((374 / 237) : ℂ) * ζ ^ 22 - ((374 / 237) : ℂ) * ζ ^ 24 + ((2762 / 1185) : ℂ) * ζ ^ 25 - ((286 / 237) : ℂ) * ζ ^ 27 - ((14 / 237) : ℂ) * ζ ^ 28 + ((7834 / 1185) : ℂ) * ζ ^ 29 + ((120 / 79) : ℂ) * ζ ^ 30 - ((286 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY55_combinationStep06Coefficient00 : ℂ :=
  (((462 / 79) : ℂ) - ((248 / 79) : ℂ) * ζ ^ 1 + ((3051 / 395) : ℂ) * ζ ^ 2 + ((77 / 79) : ℂ) * ζ ^ 3 + ((414 / 79) : ℂ) * ζ ^ 5 + ((4264 / 395) : ℂ) * ζ ^ 6 + ((351 / 79) : ℂ) * ζ ^ 8 + ((644 / 79) : ℂ) * ζ ^ 9 + ((567 / 79) : ℂ) * ζ ^ 11 + ((351 / 79) : ℂ) * ζ ^ 12 + ((248 / 79) : ℂ) * ζ ^ 13 + ((585 / 79) : ℂ) * ζ ^ 15 + ((248 / 79) : ℂ) * ζ ^ 17 - ((1213 / 395) : ℂ) * ζ ^ 18 + ((171 / 79) : ℂ) * ζ ^ 21 - ((3051 / 395) : ℂ) * ζ ^ 22 - ((662 / 79) : ℂ) * ζ ^ 25 - ((171 / 79) : ℂ) * ζ ^ 27 - ((351 / 79) : ℂ) * ζ ^ 28 - ((248 / 79) : ℂ) * ζ ^ 29 + ((2132 / 395) : ℂ) * ζ ^ 30 - ((567 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep06CoefficientIdentity00 :
    row18_reducedY55_combinationStep06Coefficient00 =
      row18_reducedY55_combinationStep05Coefficient00 +
        row18_reducedY55_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep06Coefficient00 row18_reducedY55_combinationStep05Coefficient00 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep06Coefficient01 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep06CoefficientIdentity01 :
    row18_reducedY55_combinationStep06Coefficient01 =
      row18_reducedY55_combinationStep05Coefficient01 +
        row18_reducedY55_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep06Coefficient01 row18_reducedY55_combinationStep05Coefficient01 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep06Coefficient02 : ℂ :=
  (-((773 / 2370) : ℂ) - ((3107 / 790) : ℂ) * ζ ^ 1 - ((12029 / 2370) : ℂ) * ζ ^ 2 + ((1427 / 237) : ℂ) * ζ ^ 3 - ((4598 / 395) : ℂ) * ζ ^ 5 - ((9911 / 2370) : ℂ) * ζ ^ 6 - ((11101 / 2370) : ℂ) * ζ ^ 8 - ((1491 / 790) : ℂ) * ζ ^ 9 - ((4813 / 474) : ℂ) * ζ ^ 11 - ((353 / 395) : ℂ) * ζ ^ 12 + ((3107 / 790) : ℂ) * ζ ^ 13 - ((1427 / 237) : ℂ) * ζ ^ 15 + ((3107 / 790) : ℂ) * ζ ^ 17 + ((6401 / 1185) : ℂ) * ζ ^ 18 + ((6089 / 790) : ℂ) * ζ ^ 21 + ((12029 / 2370) : ℂ) * ζ ^ 22 + ((12029 / 2370) : ℂ) * ζ ^ 24 + ((6089 / 790) : ℂ) * ζ ^ 25 + ((4813 / 474) : ℂ) * ζ ^ 27 + ((11101 / 2370) : ℂ) * ζ ^ 28 - ((3107 / 790) : ℂ) * ζ ^ 29 - ((464 / 1185) : ℂ) * ζ ^ 30 + ((4813 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep06CoefficientIdentity02 :
    row18_reducedY55_combinationStep06Coefficient02 =
      row18_reducedY55_combinationStep05Coefficient02 +
        row18_reducedY55_combinationStep06Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep06Coefficient02 row18_reducedY55_combinationStep05Coefficient02 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 (-((240883 / 187230) : ℂ) - ((1010 / 18723) : ℂ) * ζ ^ 1 - ((128126 / 93615) : ℂ) * ζ ^ 2 + ((3503 / 37446) : ℂ) * ζ ^ 3 + ((68726 / 93615) : ℂ) * ζ ^ 4 + ((48341 / 37446) : ℂ) * ζ ^ 5 - ((3181 / 187230) : ℂ) * ζ ^ 6 - ((4271 / 2370) : ℂ) * ζ ^ 7 - ((8057 / 62410) : ℂ) * ζ ^ 8 + ((5669 / 37446) : ℂ) * ζ ^ 9 - ((45698 / 93615) : ℂ) * ζ ^ 10 + ((203177 / 187230) : ℂ) * ζ ^ 11 - ((19906 / 31205) : ℂ) * ζ ^ 12 + ((9449 / 18723) : ℂ) * ζ ^ 13 + ((61963 / 62410) : ℂ) * ζ ^ 14 - ((125363 / 62410) : ℂ) * ζ ^ 15 - ((33819 / 62410) : ℂ) * ζ ^ 16 - ((15575 / 18723) : ℂ) * ζ ^ 17 - ((55037 / 93615) : ℂ) * ζ ^ 18 + ((116044 / 93615) : ℂ) * ζ ^ 19 + ((9315 / 12482) : ℂ) * ζ ^ 20 + ((323 / 12482) : ℂ) * ζ ^ 21 + ((67757 / 93615) : ℂ) * ζ ^ 22 + ((44621 / 187230) : ℂ) * ζ ^ 23 + ((4796 / 93615) : ℂ) * ζ ^ 24 - ((13838 / 18723) : ℂ) * ζ ^ 25 + ((1426 / 93615) : ℂ) * ζ ^ 26 - ((28237 / 187230) : ℂ) * ζ ^ 27 + ((32573 / 187230) : ℂ) * ζ ^ 28 + ((2404 / 18723) : ℂ) * ζ ^ 29 - ((1001 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep06Coefficient03 : ℂ :=
  (((1889 / 474) : ℂ) + ((365 / 237) : ℂ) * ζ ^ 1 + ((413 / 474) : ℂ) * ζ ^ 2 - ((1333 / 474) : ℂ) * ζ ^ 3 + ((545 / 237) : ℂ) * ζ ^ 5 + ((917 / 237) : ℂ) * ζ ^ 6 - ((289 / 474) : ℂ) * ζ ^ 8 - ((55 / 158) : ℂ) * ζ ^ 9 + ((584 / 237) : ℂ) * ζ ^ 11 - ((289 / 474) : ℂ) * ζ ^ 12 - ((365 / 237) : ℂ) * ζ ^ 13 + ((1693 / 474) : ℂ) * ζ ^ 15 - ((365 / 237) : ℂ) * ζ ^ 17 - ((1421 / 474) : ℂ) * ζ ^ 18 + ((201 / 158) : ℂ) * ζ ^ 21 - ((413 / 474) : ℂ) * ζ ^ 22 - ((60 / 79) : ℂ) * ζ ^ 25 - ((201 / 158) : ℂ) * ζ ^ 27 + ((289 / 474) : ℂ) * ζ ^ 28 + ((365 / 237) : ℂ) * ζ ^ 29 + ((917 / 474) : ℂ) * ζ ^ 30 - ((584 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep06CoefficientIdentity03 :
    row18_reducedY55_combinationStep06Coefficient03 =
      row18_reducedY55_combinationStep05Coefficient03 +
        row18_reducedY55_combinationStep06Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep06Coefficient03 row18_reducedY55_combinationStep05Coefficient03 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 (((11612 / 18723) : ℂ) + ((4744 / 93615) : ℂ) * ζ ^ 1 - ((38519 / 12482) : ℂ) * ζ ^ 2 - ((86806 / 93615) : ℂ) * ζ ^ 3 + ((79929 / 62410) : ℂ) * ζ ^ 4 - ((174697 / 93615) : ℂ) * ζ ^ 5 - ((4965 / 12482) : ℂ) * ζ ^ 6 + ((20477 / 31205) : ℂ) * ζ ^ 7 - ((133637 / 62410) : ℂ) * ζ ^ 8 - ((313493 / 187230) : ℂ) * ζ ^ 9 + ((34441 / 18723) : ℂ) * ζ ^ 10 - ((52591 / 37446) : ℂ) * ζ ^ 11 - ((196439 / 187230) : ℂ) * ζ ^ 12 + ((116566 / 93615) : ℂ) * ζ ^ 13 - ((7739 / 18723) : ℂ) * ζ ^ 14 + ((134653 / 187230) : ℂ) * ζ ^ 15 - ((41555 / 37446) : ℂ) * ζ ^ 16 - ((97259 / 93615) : ℂ) * ζ ^ 17 + ((20127 / 12482) : ℂ) * ζ ^ 18 + ((34574 / 18723) : ℂ) * ζ ^ 19 - ((91211 / 93615) : ℂ) * ζ ^ 20 + ((68719 / 37446) : ℂ) * ζ ^ 21 + ((20386 / 18723) : ℂ) * ζ ^ 22 - ((52503 / 62410) : ℂ) * ζ ^ 23 - ((8827 / 31205) : ℂ) * ζ ^ 24 + ((304001 / 187230) : ℂ) * ζ ^ 25 - ((54071 / 37446) : ℂ) * ζ ^ 26 + ((78793 / 187230) : ℂ) * ζ ^ 27 + ((26716 / 31205) : ℂ) * ζ ^ 28 - ((897 / 6241) : ℂ) * ζ ^ 29 - ((1859 / 37446) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep06Coefficient04 : ℂ :=
  (-((462 / 79) : ℂ) + ((248 / 79) : ℂ) * ζ ^ 1 - ((3051 / 395) : ℂ) * ζ ^ 2 - ((77 / 79) : ℂ) * ζ ^ 3 - ((414 / 79) : ℂ) * ζ ^ 5 - ((4264 / 395) : ℂ) * ζ ^ 6 - ((351 / 79) : ℂ) * ζ ^ 8 - ((644 / 79) : ℂ) * ζ ^ 9 - ((567 / 79) : ℂ) * ζ ^ 11 - ((351 / 79) : ℂ) * ζ ^ 12 - ((248 / 79) : ℂ) * ζ ^ 13 - ((585 / 79) : ℂ) * ζ ^ 15 - ((248 / 79) : ℂ) * ζ ^ 17 + ((1213 / 395) : ℂ) * ζ ^ 18 - ((171 / 79) : ℂ) * ζ ^ 21 + ((3051 / 395) : ℂ) * ζ ^ 22 + ((662 / 79) : ℂ) * ζ ^ 25 + ((171 / 79) : ℂ) * ζ ^ 27 + ((351 / 79) : ℂ) * ζ ^ 28 + ((248 / 79) : ℂ) * ζ ^ 29 - ((2132 / 395) : ℂ) * ζ ^ 30 + ((567 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep06CoefficientIdentity04 :
    row18_reducedY55_combinationStep06Coefficient04 =
      row18_reducedY55_combinationStep05Coefficient04 +
        row18_reducedY55_combinationStep06Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep06Coefficient04 row18_reducedY55_combinationStep05Coefficient04 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 (-((11612 / 18723) : ℂ) - ((4744 / 93615) : ℂ) * ζ ^ 1 + ((38519 / 12482) : ℂ) * ζ ^ 2 + ((86806 / 93615) : ℂ) * ζ ^ 3 - ((79929 / 62410) : ℂ) * ζ ^ 4 + ((174697 / 93615) : ℂ) * ζ ^ 5 + ((4965 / 12482) : ℂ) * ζ ^ 6 - ((20477 / 31205) : ℂ) * ζ ^ 7 + ((133637 / 62410) : ℂ) * ζ ^ 8 + ((313493 / 187230) : ℂ) * ζ ^ 9 - ((34441 / 18723) : ℂ) * ζ ^ 10 + ((52591 / 37446) : ℂ) * ζ ^ 11 + ((196439 / 187230) : ℂ) * ζ ^ 12 - ((116566 / 93615) : ℂ) * ζ ^ 13 + ((7739 / 18723) : ℂ) * ζ ^ 14 - ((134653 / 187230) : ℂ) * ζ ^ 15 + ((41555 / 37446) : ℂ) * ζ ^ 16 + ((97259 / 93615) : ℂ) * ζ ^ 17 - ((20127 / 12482) : ℂ) * ζ ^ 18 - ((34574 / 18723) : ℂ) * ζ ^ 19 + ((91211 / 93615) : ℂ) * ζ ^ 20 - ((68719 / 37446) : ℂ) * ζ ^ 21 - ((20386 / 18723) : ℂ) * ζ ^ 22 + ((52503 / 62410) : ℂ) * ζ ^ 23 + ((8827 / 31205) : ℂ) * ζ ^ 24 - ((304001 / 187230) : ℂ) * ζ ^ 25 + ((54071 / 37446) : ℂ) * ζ ^ 26 - ((78793 / 187230) : ℂ) * ζ ^ 27 - ((26716 / 31205) : ℂ) * ζ ^ 28 + ((897 / 6241) : ℂ) * ζ ^ 29 + ((1859 / 37446) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep06Coefficient05 : ℂ :=
  (-((59 / 79) : ℂ) + ((317 / 474) : ℂ) * ζ ^ 1 - ((3023 / 474) : ℂ) * ζ ^ 2 - ((2431 / 474) : ℂ) * ζ ^ 5 - ((2669 / 474) : ℂ) * ζ ^ 6 - ((2669 / 474) : ℂ) * ζ ^ 8 - ((2431 / 474) : ℂ) * ζ ^ 9 - ((2773 / 474) : ℂ) * ζ ^ 11 - ((818 / 237) : ℂ) * ζ ^ 12 - ((317 / 474) : ℂ) * ζ ^ 13 - ((1891 / 474) : ℂ) * ζ ^ 15 - ((317 / 474) : ℂ) * ζ ^ 17 + ((731 / 237) : ℂ) * ζ ^ 18 + ((1057 / 474) : ℂ) * ζ ^ 21 + ((3023 / 474) : ℂ) * ζ ^ 22 + ((1207 / 474) : ℂ) * ζ ^ 24 + ((458 / 79) : ℂ) * ζ ^ 25 + ((1891 / 474) : ℂ) * ζ ^ 27 + ((2669 / 474) : ℂ) * ζ ^ 28 + ((317 / 474) : ℂ) * ζ ^ 29 - ((1033 / 474) : ℂ) * ζ ^ 30 + ((2773 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep06CoefficientIdentity05 :
    row18_reducedY55_combinationStep06Coefficient05 =
      row18_reducedY55_combinationStep05Coefficient05 +
        row18_reducedY55_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep06Coefficient05 row18_reducedY55_combinationStep05Coefficient05 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep06Coefficient06 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep06CoefficientIdentity06 :
    row18_reducedY55_combinationStep06Coefficient06 =
      row18_reducedY55_combinationStep05Coefficient06 +
        row18_reducedY55_combinationStep06Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep06Coefficient06 row18_reducedY55_combinationStep05Coefficient06 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 (((67529 / 93615) : ℂ) + ((946471 / 187230) : ℂ) * ζ ^ 1 + ((132451 / 93615) : ℂ) * ζ ^ 2 + ((61231 / 62410) : ℂ) * ζ ^ 3 + ((95983 / 93615) : ℂ) * ζ ^ 4 - ((440624 / 93615) : ℂ) * ζ ^ 5 - ((806618 / 93615) : ℂ) * ζ ^ 6 - ((142352 / 31205) : ℂ) * ζ ^ 7 + ((81119 / 62410) : ℂ) * ζ ^ 8 + ((81645 / 12482) : ℂ) * ζ ^ 9 + ((1110421 / 187230) : ℂ) * ζ ^ 10 - ((17727 / 12482) : ℂ) * ζ ^ 11 - ((1212293 / 187230) : ℂ) * ζ ^ 12 - ((463357 / 93615) : ℂ) * ζ ^ 13 + ((7551 / 31205) : ℂ) * ζ ^ 14 + ((197199 / 62410) : ℂ) * ζ ^ 15 + ((128099 / 31205) : ℂ) * ζ ^ 16 + ((6025 / 37446) : ℂ) * ζ ^ 17 + ((124429 / 93615) : ℂ) * ζ ^ 18 + ((42952 / 18723) : ℂ) * ζ ^ 19 - ((39733 / 18723) : ℂ) * ζ ^ 20 - ((66091 / 31205) : ℂ) * ζ ^ 21 + ((279949 / 187230) : ℂ) * ζ ^ 22 + ((35889 / 31205) : ℂ) * ζ ^ 23 + ((196197 / 62410) : ℂ) * ζ ^ 24 + ((33597 / 62410) : ℂ) * ζ ^ 25 - ((329039 / 187230) : ℂ) * ζ ^ 26 - ((67874 / 93615) : ℂ) * ζ ^ 27 - ((90521 / 187230) : ℂ) * ζ ^ 28 - ((268 / 6241) : ℂ) * ζ ^ 29 + ((2002 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep06Coefficient07 : ℂ :=
  (-((925 / 237) : ℂ) - ((463 / 237) : ℂ) * ζ ^ 1 - ((215 / 237) : ℂ) * ζ ^ 2 + ((715 / 237) : ℂ) * ζ ^ 3 - ((197 / 79) : ℂ) * ζ ^ 5 - ((312 / 79) : ℂ) * ζ ^ 6 + ((72 / 79) : ℂ) * ζ ^ 8 + ((227 / 237) : ℂ) * ζ ^ 9 - ((488 / 237) : ℂ) * ζ ^ 11 + ((72 / 79) : ℂ) * ζ ^ 12 + ((463 / 237) : ℂ) * ζ ^ 13 - ((281 / 79) : ℂ) * ζ ^ 15 + ((463 / 237) : ℂ) * ζ ^ 17 + ((721 / 237) : ℂ) * ζ ^ 18 - ((84 / 79) : ℂ) * ζ ^ 21 + ((215 / 237) : ℂ) * ζ ^ 22 + ((128 / 237) : ℂ) * ζ ^ 25 + ((84 / 79) : ℂ) * ζ ^ 27 - ((72 / 79) : ℂ) * ζ ^ 28 - ((463 / 237) : ℂ) * ζ ^ 29 - ((156 / 79) : ℂ) * ζ ^ 30 + ((488 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep06CoefficientIdentity07 :
    row18_reducedY55_combinationStep06Coefficient07 =
      row18_reducedY55_combinationStep05Coefficient07 +
        row18_reducedY55_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep06Coefficient07 row18_reducedY55_combinationStep05Coefficient07 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep06Coefficient08 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep06CoefficientIdentity08 :
    row18_reducedY55_combinationStep06Coefficient08 =
      row18_reducedY55_combinationStep05Coefficient08 +
        row18_reducedY55_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep06Coefficient08 row18_reducedY55_combinationStep05Coefficient08 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep06Coefficient09 : ℂ :=
  (-((51 / 158) : ℂ) + ((87 / 79) : ℂ) * ζ ^ 1 + ((925 / 474) : ℂ) * ζ ^ 2 + ((341 / 237) : ℂ) * ζ ^ 3 + ((87 / 79) : ℂ) * ζ ^ 5 + ((386 / 237) : ℂ) * ζ ^ 6 - ((386 / 237) : ℂ) * ζ ^ 8 - ((87 / 79) : ℂ) * ζ ^ 9 - ((341 / 474) : ℂ) * ζ ^ 11 - ((199 / 158) : ℂ) * ζ ^ 12 - ((87 / 79) : ℂ) * ζ ^ 13 + ((55 / 79) : ℂ) * ζ ^ 15 - ((87 / 79) : ℂ) * ζ ^ 17 - ((289 / 237) : ℂ) * ζ ^ 18 - ((243 / 158) : ℂ) * ζ ^ 21 - ((925 / 474) : ℂ) * ζ ^ 22 + ((97 / 237) : ℂ) * ζ ^ 24 + ((506 / 237) : ℂ) * ζ ^ 27 + ((386 / 237) : ℂ) * ζ ^ 28 + ((87 / 79) : ℂ) * ζ ^ 29 + ((175 / 474) : ℂ) * ζ ^ 30 + ((341 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep06CoefficientIdentity09 :
    row18_reducedY55_combinationStep06Coefficient09 =
      row18_reducedY55_combinationStep05Coefficient09 +
        row18_reducedY55_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep06Coefficient09 row18_reducedY55_combinationStep05Coefficient09 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep06Coefficient10 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep06CoefficientIdentity10 :
    row18_reducedY55_combinationStep06Coefficient10 =
      row18_reducedY55_combinationStep05Coefficient10 +
        row18_reducedY55_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep06Coefficient10 row18_reducedY55_combinationStep05Coefficient10 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep06Coefficient11 : ℂ :=
  (((53 / 158) : ℂ) + ((26 / 237) : ℂ) * ζ ^ 1 - ((20 / 237) : ℂ) * ζ ^ 2 + ((67 / 237) : ℂ) * ζ ^ 3 + ((149 / 474) : ℂ) * ζ ^ 5 + ((25 / 237) : ℂ) * ζ ^ 6 - ((64 / 237) : ℂ) * ζ ^ 8 - ((2 / 237) : ℂ) * ζ ^ 9 - ((23 / 79) : ℂ) * ζ ^ 11 - ((64 / 237) : ℂ) * ζ ^ 12 - ((26 / 237) : ℂ) * ζ ^ 13 - ((37 / 474) : ℂ) * ζ ^ 15 - ((26 / 237) : ℂ) * ζ ^ 17 - ((15 / 79) : ℂ) * ζ ^ 18 - ((31 / 79) : ℂ) * ζ ^ 21 + ((20 / 237) : ℂ) * ζ ^ 22 - ((97 / 474) : ℂ) * ζ ^ 25 + ((31 / 79) : ℂ) * ζ ^ 27 + ((64 / 237) : ℂ) * ζ ^ 28 + ((26 / 237) : ℂ) * ζ ^ 29 + ((25 / 474) : ℂ) * ζ ^ 30 + ((23 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep06CoefficientIdentity11 :
    row18_reducedY55_combinationStep06Coefficient11 =
      row18_reducedY55_combinationStep05Coefficient11 +
        row18_reducedY55_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep06Coefficient11 row18_reducedY55_combinationStep05Coefficient11 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep06Coefficient12 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep06CoefficientIdentity12 :
    row18_reducedY55_combinationStep06Coefficient12 =
      row18_reducedY55_combinationStep05Coefficient12 +
        row18_reducedY55_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep06Coefficient12 row18_reducedY55_combinationStep05Coefficient12 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep06Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep06CoefficientIdentity13 :
    row18_reducedY55_combinationStep06Coefficient13 =
      row18_reducedY55_combinationStep05Coefficient13 +
        row18_reducedY55_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep06Coefficient13 row18_reducedY55_combinationStep05Coefficient13 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep06Coefficient14 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep06CoefficientIdentity14 :
    row18_reducedY55_combinationStep06Coefficient14 =
      row18_reducedY55_combinationStep05Coefficient14 +
        row18_reducedY55_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep06Coefficient14 row18_reducedY55_combinationStep05Coefficient14 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep06Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep06CoefficientIdentity15 :
    row18_reducedY55_combinationStep06Coefficient15 =
      row18_reducedY55_combinationStep05Coefficient15 +
        row18_reducedY55_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep06Coefficient15 row18_reducedY55_combinationStep05Coefficient15 row18_reducedY55_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY55_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY55_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY55_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY55_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY55_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY55_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY55_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY55_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY55_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY55_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY55_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY55_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY55_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY55_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY55_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY55_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY55_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY55_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY55_combinationStep06CoefficientIdentity00,
      row18_reducedY55_combinationStep06CoefficientIdentity01,
      row18_reducedY55_combinationStep06CoefficientIdentity02,
      row18_reducedY55_combinationStep06CoefficientIdentity03,
      row18_reducedY55_combinationStep06CoefficientIdentity04,
      row18_reducedY55_combinationStep06CoefficientIdentity05,
      row18_reducedY55_combinationStep06CoefficientIdentity06,
      row18_reducedY55_combinationStep06CoefficientIdentity07,
      row18_reducedY55_combinationStep06CoefficientIdentity08,
      row18_reducedY55_combinationStep06CoefficientIdentity09,
      row18_reducedY55_combinationStep06CoefficientIdentity10,
      row18_reducedY55_combinationStep06CoefficientIdentity11,
      row18_reducedY55_combinationStep06CoefficientIdentity12,
      row18_reducedY55_combinationStep06CoefficientIdentity13,
      row18_reducedY55_combinationStep06CoefficientIdentity14,
      row18_reducedY55_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY55_combinationStep06Multiplier * equation

private def row18_reducedY55_combinationStep07Multiplier : ℂ :=
  (((550 / 237) : ℂ) + ((940 / 237) : ℂ) * ζ ^ 1 - ((182 / 237) : ℂ) * ζ ^ 2 - ((706 / 237) : ℂ) * ζ ^ 3 + ((424 / 79) : ℂ) * ζ ^ 5 - ((542 / 237) : ℂ) * ζ ^ 8 - ((2 / 237) : ℂ) * ζ ^ 9 + ((236 / 79) : ℂ) * ζ ^ 11 - ((186 / 79) : ℂ) * ζ ^ 12 - ((940 / 237) : ℂ) * ζ ^ 13 + ((374 / 237) : ℂ) * ζ ^ 15 - ((940 / 237) : ℂ) * ζ ^ 17 + ((182 / 237) : ℂ) * ζ ^ 18 - ((1646 / 237) : ℂ) * ζ ^ 21 + ((182 / 237) : ℂ) * ζ ^ 22 + ((1100 / 237) : ℂ) * ζ ^ 24 - ((332 / 237) : ℂ) * ζ ^ 25 - ((1646 / 237) : ℂ) * ζ ^ 27 + ((542 / 237) : ℂ) * ζ ^ 28 + ((940 / 237) : ℂ) * ζ ^ 29 + ((854 / 237) : ℂ) * ζ ^ 30 - ((236 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY55_combinationStep07Coefficient00 : ℂ :=
  (((462 / 79) : ℂ) - ((248 / 79) : ℂ) * ζ ^ 1 + ((3051 / 395) : ℂ) * ζ ^ 2 + ((77 / 79) : ℂ) * ζ ^ 3 + ((414 / 79) : ℂ) * ζ ^ 5 + ((4264 / 395) : ℂ) * ζ ^ 6 + ((351 / 79) : ℂ) * ζ ^ 8 + ((644 / 79) : ℂ) * ζ ^ 9 + ((567 / 79) : ℂ) * ζ ^ 11 + ((351 / 79) : ℂ) * ζ ^ 12 + ((248 / 79) : ℂ) * ζ ^ 13 + ((585 / 79) : ℂ) * ζ ^ 15 + ((248 / 79) : ℂ) * ζ ^ 17 - ((1213 / 395) : ℂ) * ζ ^ 18 + ((171 / 79) : ℂ) * ζ ^ 21 - ((3051 / 395) : ℂ) * ζ ^ 22 - ((662 / 79) : ℂ) * ζ ^ 25 - ((171 / 79) : ℂ) * ζ ^ 27 - ((351 / 79) : ℂ) * ζ ^ 28 - ((248 / 79) : ℂ) * ζ ^ 29 + ((2132 / 395) : ℂ) * ζ ^ 30 - ((567 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep07CoefficientIdentity00 :
    row18_reducedY55_combinationStep07Coefficient00 =
      row18_reducedY55_combinationStep06Coefficient00 +
        row18_reducedY55_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep07Coefficient00 row18_reducedY55_combinationStep06Coefficient00 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep07Coefficient01 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep07CoefficientIdentity01 :
    row18_reducedY55_combinationStep07Coefficient01 =
      row18_reducedY55_combinationStep06Coefficient01 +
        row18_reducedY55_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep07Coefficient01 row18_reducedY55_combinationStep06Coefficient01 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep07Coefficient02 : ℂ :=
  (((6437 / 2370) : ℂ) - ((1317 / 790) : ℂ) * ζ ^ 1 - ((6113 / 790) : ℂ) * ζ ^ 2 + ((683 / 237) : ℂ) * ζ ^ 3 - ((9274 / 1185) : ℂ) * ζ ^ 5 - ((9751 / 2370) : ℂ) * ζ ^ 6 - ((20441 / 2370) : ℂ) * ζ ^ 8 - ((5323 / 2370) : ℂ) * ζ ^ 9 - ((3241 / 474) : ℂ) * ζ ^ 11 - ((4294 / 1185) : ℂ) * ζ ^ 12 + ((1317 / 790) : ℂ) * ζ ^ 13 - ((683 / 237) : ℂ) * ζ ^ 15 + ((1317 / 790) : ℂ) * ζ ^ 17 + ((5951 / 1185) : ℂ) * ζ ^ 18 + ((14597 / 2370) : ℂ) * ζ ^ 21 + ((6113 / 790) : ℂ) * ζ ^ 22 + ((6113 / 790) : ℂ) * ζ ^ 24 + ((14597 / 2370) : ℂ) * ζ ^ 25 + ((3241 / 474) : ℂ) * ζ ^ 27 + ((20441 / 2370) : ℂ) * ζ ^ 28 - ((1317 / 790) : ℂ) * ζ ^ 29 + ((1051 / 1185) : ℂ) * ζ ^ 30 + ((3241 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep07CoefficientIdentity02 :
    row18_reducedY55_combinationStep07Coefficient02 =
      row18_reducedY55_combinationStep06Coefficient02 +
        row18_reducedY55_combinationStep07Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep07Coefficient02 row18_reducedY55_combinationStep06Coefficient02 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 (-((51734 / 18723) : ℂ) - ((70561 / 37446) : ℂ) * ζ ^ 1 + ((93155 / 37446) : ℂ) * ζ ^ 2 + ((103891 / 37446) : ℂ) * ζ ^ 3 + ((47888 / 18723) : ℂ) * ζ ^ 4 - ((24901 / 18723) : ℂ) * ζ ^ 5 - ((86129 / 37446) : ℂ) * ζ ^ 6 - ((80915 / 37446) : ℂ) * ζ ^ 7 + ((2305 / 12482) : ℂ) * ζ ^ 8 + ((1295 / 12482) : ℂ) * ζ ^ 9 + ((8175 / 6241) : ℂ) * ζ ^ 10 + ((15446 / 18723) : ℂ) * ζ ^ 11 + ((9845 / 18723) : ℂ) * ζ ^ 12 - ((24443 / 37446) : ℂ) * ζ ^ 13 - ((4211 / 6241) : ℂ) * ζ ^ 14 - ((51857 / 37446) : ℂ) * ζ ^ 15 - ((8873 / 37446) : ℂ) * ζ ^ 16 + ((28369 / 37446) : ℂ) * ζ ^ 17 + ((24155 / 12482) : ℂ) * ζ ^ 18 + ((19528 / 18723) : ℂ) * ζ ^ 19 - ((3576 / 6241) : ℂ) * ζ ^ 20 - ((24099 / 12482) : ℂ) * ζ ^ 21 - ((22900 / 18723) : ℂ) * ζ ^ 22 - ((1157 / 37446) : ℂ) * ζ ^ 23 + ((10629 / 6241) : ℂ) * ζ ^ 24 + ((19843 / 12482) : ℂ) * ζ ^ 25 + ((1300 / 6241) : ℂ) * ζ ^ 26 - ((26531 / 18723) : ℂ) * ζ ^ 27 - ((3824 / 6241) : ℂ) * ζ ^ 28 + ((3529 / 12482) : ℂ) * ζ ^ 29 + ((885 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep07Coefficient03 : ℂ :=
  (((13 / 158) : ℂ) - ((98 / 237) : ℂ) * ζ ^ 1 - ((17 / 474) : ℂ) * ζ ^ 2 + ((97 / 474) : ℂ) * ζ ^ 3 - ((46 / 237) : ℂ) * ζ ^ 5 - ((19 / 237) : ℂ) * ζ ^ 6 + ((143 / 474) : ℂ) * ζ ^ 8 + ((289 / 474) : ℂ) * ζ ^ 9 + ((32 / 79) : ℂ) * ζ ^ 11 + ((143 / 474) : ℂ) * ζ ^ 12 + ((98 / 237) : ℂ) * ζ ^ 13 + ((7 / 474) : ℂ) * ζ ^ 15 + ((98 / 237) : ℂ) * ζ ^ 17 + ((7 / 158) : ℂ) * ζ ^ 18 + ((33 / 158) : ℂ) * ζ ^ 21 + ((17 / 474) : ℂ) * ζ ^ 22 - ((52 / 237) : ℂ) * ζ ^ 25 - ((33 / 158) : ℂ) * ζ ^ 27 - ((143 / 474) : ℂ) * ζ ^ 28 - ((98 / 237) : ℂ) * ζ ^ 29 - ((19 / 474) : ℂ) * ζ ^ 30 - ((32 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep07CoefficientIdentity03 :
    row18_reducedY55_combinationStep07Coefficient03 =
      row18_reducedY55_combinationStep06Coefficient03 +
        row18_reducedY55_combinationStep07Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep07Coefficient03 row18_reducedY55_combinationStep06Coefficient03 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 (((25825 / 6241) : ℂ) + ((34623 / 12482) : ℂ) * ζ ^ 1 + ((32941 / 12482) : ℂ) * ζ ^ 2 - ((13433 / 6241) : ℂ) * ζ ^ 3 - ((37470 / 6241) : ℂ) * ζ ^ 4 - ((8779 / 37446) : ℂ) * ζ ^ 5 + ((79279 / 18723) : ℂ) * ζ ^ 6 + ((83222 / 18723) : ℂ) * ζ ^ 7 + ((15859 / 6241) : ℂ) * ζ ^ 8 - ((19331 / 37446) : ℂ) * ζ ^ 9 - ((43112 / 18723) : ℂ) * ζ ^ 10 - ((70313 / 37446) : ℂ) * ζ ^ 11 - ((13765 / 18723) : ℂ) * ζ ^ 12 + ((46 / 18723) : ℂ) * ζ ^ 13 + ((71968 / 18723) : ℂ) * ζ ^ 14 + ((113789 / 37446) : ℂ) * ζ ^ 15 + ((10281 / 6241) : ℂ) * ζ ^ 16 - ((73141 / 37446) : ℂ) * ζ ^ 17 - ((100820 / 18723) : ℂ) * ζ ^ 18 - ((154289 / 37446) : ℂ) * ζ ^ 19 + ((47629 / 12482) : ℂ) * ζ ^ 20 + ((81482 / 18723) : ℂ) * ζ ^ 21 + ((8226 / 6241) : ℂ) * ζ ^ 22 - ((56948 / 18723) : ℂ) * ζ ^ 23 - ((100003 / 37446) : ℂ) * ζ ^ 24 - ((19781 / 12482) : ℂ) * ζ ^ 25 + ((36361 / 18723) : ℂ) * ζ ^ 26 + ((38959 / 37446) : ℂ) * ζ ^ 27 + ((1615 / 18723) : ℂ) * ζ ^ 28 + ((1730 / 18723) : ℂ) * ζ ^ 29 - ((1652 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep07Coefficient04 : ℂ :=
  (-((462 / 79) : ℂ) + ((248 / 79) : ℂ) * ζ ^ 1 - ((3051 / 395) : ℂ) * ζ ^ 2 - ((77 / 79) : ℂ) * ζ ^ 3 - ((414 / 79) : ℂ) * ζ ^ 5 - ((4264 / 395) : ℂ) * ζ ^ 6 - ((351 / 79) : ℂ) * ζ ^ 8 - ((644 / 79) : ℂ) * ζ ^ 9 - ((567 / 79) : ℂ) * ζ ^ 11 - ((351 / 79) : ℂ) * ζ ^ 12 - ((248 / 79) : ℂ) * ζ ^ 13 - ((585 / 79) : ℂ) * ζ ^ 15 - ((248 / 79) : ℂ) * ζ ^ 17 + ((1213 / 395) : ℂ) * ζ ^ 18 - ((171 / 79) : ℂ) * ζ ^ 21 + ((3051 / 395) : ℂ) * ζ ^ 22 + ((662 / 79) : ℂ) * ζ ^ 25 + ((171 / 79) : ℂ) * ζ ^ 27 + ((351 / 79) : ℂ) * ζ ^ 28 + ((248 / 79) : ℂ) * ζ ^ 29 - ((2132 / 395) : ℂ) * ζ ^ 30 + ((567 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep07CoefficientIdentity04 :
    row18_reducedY55_combinationStep07Coefficient04 =
      row18_reducedY55_combinationStep06Coefficient04 +
        row18_reducedY55_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep07Coefficient04 row18_reducedY55_combinationStep06Coefficient04 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep07Coefficient05 : ℂ :=
  (-((71 / 79) : ℂ) + ((87 / 79) : ℂ) * ζ ^ 1 - ((605 / 79) : ℂ) * ζ ^ 2 - ((567 / 79) : ℂ) * ζ ^ 5 - ((534 / 79) : ℂ) * ζ ^ 6 - ((534 / 79) : ℂ) * ζ ^ 8 - ((567 / 79) : ℂ) * ζ ^ 9 - ((636 / 79) : ℂ) * ζ ^ 11 - ((323 / 79) : ℂ) * ζ ^ 12 - ((87 / 79) : ℂ) * ζ ^ 13 - ((432 / 79) : ℂ) * ζ ^ 15 - ((87 / 79) : ℂ) * ζ ^ 17 + ((287 / 79) : ℂ) * ζ ^ 18 + ((240 / 79) : ℂ) * ζ ^ 21 + ((605 / 79) : ℂ) * ζ ^ 22 + ((247 / 79) : ℂ) * ζ ^ 24 + ((654 / 79) : ℂ) * ζ ^ 25 + ((432 / 79) : ℂ) * ζ ^ 27 + ((534 / 79) : ℂ) * ζ ^ 28 + ((87 / 79) : ℂ) * ζ ^ 29 - ((211 / 79) : ℂ) * ζ ^ 30 + ((636 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep07CoefficientIdentity05 :
    row18_reducedY55_combinationStep07Coefficient05 =
      row18_reducedY55_combinationStep06Coefficient05 +
        row18_reducedY55_combinationStep07Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep07Coefficient05 row18_reducedY55_combinationStep06Coefficient05 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 (-((4429 / 12482) : ℂ) - ((12625 / 18723) : ℂ) * ζ ^ 1 + ((30569 / 12482) : ℂ) * ζ ^ 2 + ((2621 / 18723) : ℂ) * ζ ^ 3 - ((9373 / 12482) : ℂ) * ζ ^ 4 + ((86993 / 37446) : ℂ) * ζ ^ 5 + ((16148 / 18723) : ℂ) * ζ ^ 6 - ((55361 / 37446) : ℂ) * ζ ^ 7 + ((35545 / 18723) : ℂ) * ζ ^ 8 + ((2523 / 12482) : ℂ) * ζ ^ 9 - ((11465 / 18723) : ℂ) * ζ ^ 10 + ((18185 / 12482) : ℂ) * ζ ^ 11 + ((10521 / 12482) : ℂ) * ζ ^ 12 + ((1100 / 18723) : ℂ) * ζ ^ 13 - ((1956 / 6241) : ℂ) * ζ ^ 14 + ((4469 / 18723) : ℂ) * ζ ^ 15 + ((10831 / 37446) : ℂ) * ζ ^ 16 + ((34183 / 18723) : ℂ) * ζ ^ 17 - ((10939 / 6241) : ℂ) * ζ ^ 18 + ((1061 / 18723) : ℂ) * ζ ^ 19 + ((5494 / 6241) : ℂ) * ζ ^ 20 - ((14437 / 37446) : ℂ) * ζ ^ 21 - ((44489 / 18723) : ℂ) * ζ ^ 22 + ((11827 / 6241) : ℂ) * ζ ^ 23 - ((33437 / 37446) : ℂ) * ζ ^ 24 + ((2306 / 6241) : ℂ) * ζ ^ 25 + ((313 / 12482) : ℂ) * ζ ^ 26 + ((5834 / 6241) : ℂ) * ζ ^ 27 - ((29629 / 18723) : ℂ) * ζ ^ 28 + ((13565 / 37446) : ℂ) * ζ ^ 29 + ((767 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep07Coefficient06 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep07CoefficientIdentity06 :
    row18_reducedY55_combinationStep07Coefficient06 =
      row18_reducedY55_combinationStep06Coefficient06 +
        row18_reducedY55_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep07Coefficient06 row18_reducedY55_combinationStep06Coefficient06 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep07Coefficient07 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep07CoefficientIdentity07 :
    row18_reducedY55_combinationStep07Coefficient07 =
      row18_reducedY55_combinationStep06Coefficient07 +
        row18_reducedY55_combinationStep07Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep07Coefficient07 row18_reducedY55_combinationStep06Coefficient07 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 (-((25825 / 6241) : ℂ) - ((34623 / 12482) : ℂ) * ζ ^ 1 - ((32941 / 12482) : ℂ) * ζ ^ 2 + ((13433 / 6241) : ℂ) * ζ ^ 3 + ((37470 / 6241) : ℂ) * ζ ^ 4 + ((8779 / 37446) : ℂ) * ζ ^ 5 - ((79279 / 18723) : ℂ) * ζ ^ 6 - ((83222 / 18723) : ℂ) * ζ ^ 7 - ((15859 / 6241) : ℂ) * ζ ^ 8 + ((19331 / 37446) : ℂ) * ζ ^ 9 + ((43112 / 18723) : ℂ) * ζ ^ 10 + ((70313 / 37446) : ℂ) * ζ ^ 11 + ((13765 / 18723) : ℂ) * ζ ^ 12 - ((46 / 18723) : ℂ) * ζ ^ 13 - ((71968 / 18723) : ℂ) * ζ ^ 14 - ((113789 / 37446) : ℂ) * ζ ^ 15 - ((10281 / 6241) : ℂ) * ζ ^ 16 + ((73141 / 37446) : ℂ) * ζ ^ 17 + ((100820 / 18723) : ℂ) * ζ ^ 18 + ((154289 / 37446) : ℂ) * ζ ^ 19 - ((47629 / 12482) : ℂ) * ζ ^ 20 - ((81482 / 18723) : ℂ) * ζ ^ 21 - ((8226 / 6241) : ℂ) * ζ ^ 22 + ((56948 / 18723) : ℂ) * ζ ^ 23 + ((100003 / 37446) : ℂ) * ζ ^ 24 + ((19781 / 12482) : ℂ) * ζ ^ 25 - ((36361 / 18723) : ℂ) * ζ ^ 26 - ((38959 / 37446) : ℂ) * ζ ^ 27 - ((1615 / 18723) : ℂ) * ζ ^ 28 - ((1730 / 18723) : ℂ) * ζ ^ 29 + ((1652 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep07Coefficient08 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep07CoefficientIdentity08 :
    row18_reducedY55_combinationStep07Coefficient08 =
      row18_reducedY55_combinationStep06Coefficient08 +
        row18_reducedY55_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep07Coefficient08 row18_reducedY55_combinationStep06Coefficient08 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep07Coefficient09 : ℂ :=
  (-((51 / 158) : ℂ) + ((87 / 79) : ℂ) * ζ ^ 1 + ((925 / 474) : ℂ) * ζ ^ 2 + ((341 / 237) : ℂ) * ζ ^ 3 + ((87 / 79) : ℂ) * ζ ^ 5 + ((386 / 237) : ℂ) * ζ ^ 6 - ((386 / 237) : ℂ) * ζ ^ 8 - ((87 / 79) : ℂ) * ζ ^ 9 - ((341 / 474) : ℂ) * ζ ^ 11 - ((199 / 158) : ℂ) * ζ ^ 12 - ((87 / 79) : ℂ) * ζ ^ 13 + ((55 / 79) : ℂ) * ζ ^ 15 - ((87 / 79) : ℂ) * ζ ^ 17 - ((289 / 237) : ℂ) * ζ ^ 18 - ((243 / 158) : ℂ) * ζ ^ 21 - ((925 / 474) : ℂ) * ζ ^ 22 + ((97 / 237) : ℂ) * ζ ^ 24 + ((506 / 237) : ℂ) * ζ ^ 27 + ((386 / 237) : ℂ) * ζ ^ 28 + ((87 / 79) : ℂ) * ζ ^ 29 + ((175 / 474) : ℂ) * ζ ^ 30 + ((341 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep07CoefficientIdentity09 :
    row18_reducedY55_combinationStep07Coefficient09 =
      row18_reducedY55_combinationStep06Coefficient09 +
        row18_reducedY55_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep07Coefficient09 row18_reducedY55_combinationStep06Coefficient09 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep07Coefficient10 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep07CoefficientIdentity10 :
    row18_reducedY55_combinationStep07Coefficient10 =
      row18_reducedY55_combinationStep06Coefficient10 +
        row18_reducedY55_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep07Coefficient10 row18_reducedY55_combinationStep06Coefficient10 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep07Coefficient11 : ℂ :=
  (((53 / 158) : ℂ) + ((26 / 237) : ℂ) * ζ ^ 1 - ((20 / 237) : ℂ) * ζ ^ 2 + ((67 / 237) : ℂ) * ζ ^ 3 + ((149 / 474) : ℂ) * ζ ^ 5 + ((25 / 237) : ℂ) * ζ ^ 6 - ((64 / 237) : ℂ) * ζ ^ 8 - ((2 / 237) : ℂ) * ζ ^ 9 - ((23 / 79) : ℂ) * ζ ^ 11 - ((64 / 237) : ℂ) * ζ ^ 12 - ((26 / 237) : ℂ) * ζ ^ 13 - ((37 / 474) : ℂ) * ζ ^ 15 - ((26 / 237) : ℂ) * ζ ^ 17 - ((15 / 79) : ℂ) * ζ ^ 18 - ((31 / 79) : ℂ) * ζ ^ 21 + ((20 / 237) : ℂ) * ζ ^ 22 - ((97 / 474) : ℂ) * ζ ^ 25 + ((31 / 79) : ℂ) * ζ ^ 27 + ((64 / 237) : ℂ) * ζ ^ 28 + ((26 / 237) : ℂ) * ζ ^ 29 + ((25 / 474) : ℂ) * ζ ^ 30 + ((23 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep07CoefficientIdentity11 :
    row18_reducedY55_combinationStep07Coefficient11 =
      row18_reducedY55_combinationStep06Coefficient11 +
        row18_reducedY55_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep07Coefficient11 row18_reducedY55_combinationStep06Coefficient11 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep07Coefficient12 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep07CoefficientIdentity12 :
    row18_reducedY55_combinationStep07Coefficient12 =
      row18_reducedY55_combinationStep06Coefficient12 +
        row18_reducedY55_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep07Coefficient12 row18_reducedY55_combinationStep06Coefficient12 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep07Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep07CoefficientIdentity13 :
    row18_reducedY55_combinationStep07Coefficient13 =
      row18_reducedY55_combinationStep06Coefficient13 +
        row18_reducedY55_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep07Coefficient13 row18_reducedY55_combinationStep06Coefficient13 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep07Coefficient14 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep07CoefficientIdentity14 :
    row18_reducedY55_combinationStep07Coefficient14 =
      row18_reducedY55_combinationStep06Coefficient14 +
        row18_reducedY55_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep07Coefficient14 row18_reducedY55_combinationStep06Coefficient14 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep07Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep07CoefficientIdentity15 :
    row18_reducedY55_combinationStep07Coefficient15 =
      row18_reducedY55_combinationStep06Coefficient15 +
        row18_reducedY55_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep07Coefficient15 row18_reducedY55_combinationStep06Coefficient15 row18_reducedY55_combinationStep07Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY55_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY55_combinationStep07Coefficient00) * Y 0 0
      + (row18_reducedY55_combinationStep07Coefficient01) * Y 0 1
      + (row18_reducedY55_combinationStep07Coefficient02) * Y 1 0
      + (row18_reducedY55_combinationStep07Coefficient03) * Y 1 1
      + (row18_reducedY55_combinationStep07Coefficient04) * Y 2 2
      + (row18_reducedY55_combinationStep07Coefficient05) * Y 2 3
      + (row18_reducedY55_combinationStep07Coefficient06) * Y 3 2
      + (row18_reducedY55_combinationStep07Coefficient07) * Y 3 3
      + (row18_reducedY55_combinationStep07Coefficient08) * Y 4 4
      + (row18_reducedY55_combinationStep07Coefficient09) * Y 4 5
      + (row18_reducedY55_combinationStep07Coefficient10) * Y 5 4
      + (row18_reducedY55_combinationStep07Coefficient11) * Y 5 5
      + (row18_reducedY55_combinationStep07Coefficient12) * Y 6 6
      + (row18_reducedY55_combinationStep07Coefficient13) * Y 6 7
      + (row18_reducedY55_combinationStep07Coefficient14) * Y 7 6
      + (row18_reducedY55_combinationStep07Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY55_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY55_combinationStep07CoefficientIdentity00,
      row18_reducedY55_combinationStep07CoefficientIdentity01,
      row18_reducedY55_combinationStep07CoefficientIdentity02,
      row18_reducedY55_combinationStep07CoefficientIdentity03,
      row18_reducedY55_combinationStep07CoefficientIdentity04,
      row18_reducedY55_combinationStep07CoefficientIdentity05,
      row18_reducedY55_combinationStep07CoefficientIdentity06,
      row18_reducedY55_combinationStep07CoefficientIdentity07,
      row18_reducedY55_combinationStep07CoefficientIdentity08,
      row18_reducedY55_combinationStep07CoefficientIdentity09,
      row18_reducedY55_combinationStep07CoefficientIdentity10,
      row18_reducedY55_combinationStep07CoefficientIdentity11,
      row18_reducedY55_combinationStep07CoefficientIdentity12,
      row18_reducedY55_combinationStep07CoefficientIdentity13,
      row18_reducedY55_combinationStep07CoefficientIdentity14,
      row18_reducedY55_combinationStep07CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY55_combinationStep07Multiplier * equation

private def row18_reducedY55_combinationStep08Multiplier : ℂ :=
  (((1102 / 237) : ℂ) + ((728 / 237) : ℂ) * ζ ^ 1 - ((406 / 237) : ℂ) * ζ ^ 2 - ((592 / 237) : ℂ) * ζ ^ 3 + ((232 / 79) : ℂ) * ζ ^ 5 - ((1618 / 237) : ℂ) * ζ ^ 8 - ((236 / 79) : ℂ) * ζ ^ 9 + ((1300 / 237) : ℂ) * ζ ^ 11 - ((586 / 237) : ℂ) * ζ ^ 12 - ((728 / 237) : ℂ) * ζ ^ 13 + ((208 / 79) : ℂ) * ζ ^ 15 - ((728 / 237) : ℂ) * ζ ^ 17 + ((406 / 237) : ℂ) * ζ ^ 18 - ((440 / 79) : ℂ) * ζ ^ 21 + ((406 / 237) : ℂ) * ζ ^ 22 + ((2204 / 237) : ℂ) * ζ ^ 24 + ((32 / 237) : ℂ) * ζ ^ 25 - ((440 / 79) : ℂ) * ζ ^ 27 + ((1618 / 237) : ℂ) * ζ ^ 28 + ((728 / 237) : ℂ) * ζ ^ 29 + ((82 / 237) : ℂ) * ζ ^ 30 - ((1300 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY55_combinationStep08Coefficient00 : ℂ :=
  (((462 / 79) : ℂ) - ((248 / 79) : ℂ) * ζ ^ 1 + ((3051 / 395) : ℂ) * ζ ^ 2 + ((77 / 79) : ℂ) * ζ ^ 3 + ((414 / 79) : ℂ) * ζ ^ 5 + ((4264 / 395) : ℂ) * ζ ^ 6 + ((351 / 79) : ℂ) * ζ ^ 8 + ((644 / 79) : ℂ) * ζ ^ 9 + ((567 / 79) : ℂ) * ζ ^ 11 + ((351 / 79) : ℂ) * ζ ^ 12 + ((248 / 79) : ℂ) * ζ ^ 13 + ((585 / 79) : ℂ) * ζ ^ 15 + ((248 / 79) : ℂ) * ζ ^ 17 - ((1213 / 395) : ℂ) * ζ ^ 18 + ((171 / 79) : ℂ) * ζ ^ 21 - ((3051 / 395) : ℂ) * ζ ^ 22 - ((662 / 79) : ℂ) * ζ ^ 25 - ((171 / 79) : ℂ) * ζ ^ 27 - ((351 / 79) : ℂ) * ζ ^ 28 - ((248 / 79) : ℂ) * ζ ^ 29 + ((2132 / 395) : ℂ) * ζ ^ 30 - ((567 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep08CoefficientIdentity00 :
    row18_reducedY55_combinationStep08Coefficient00 =
      row18_reducedY55_combinationStep07Coefficient00 +
        row18_reducedY55_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep08Coefficient00 row18_reducedY55_combinationStep07Coefficient00 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep08Coefficient01 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep08CoefficientIdentity01 :
    row18_reducedY55_combinationStep08Coefficient01 =
      row18_reducedY55_combinationStep07Coefficient01 +
        row18_reducedY55_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep08Coefficient01 row18_reducedY55_combinationStep07Coefficient01 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep08Coefficient02 : ℂ :=
  (((1007 / 395) : ℂ) - ((781 / 395) : ℂ) * ζ ^ 1 - ((6113 / 790) : ℂ) * ζ ^ 2 + ((455 / 158) : ℂ) * ζ ^ 3 - ((3313 / 395) : ℂ) * ζ ^ 5 - ((2987 / 790) : ℂ) * ζ ^ 6 - ((3341 / 395) : ℂ) * ζ ^ 8 - ((1751 / 790) : ℂ) * ζ ^ 9 - ((1149 / 158) : ℂ) * ζ ^ 11 - ((1563 / 395) : ℂ) * ζ ^ 12 + ((781 / 395) : ℂ) * ζ ^ 13 - ((455 / 158) : ℂ) * ζ ^ 15 + ((781 / 395) : ℂ) * ζ ^ 17 + ((4099 / 790) : ℂ) * ζ ^ 18 + ((2532 / 395) : ℂ) * ζ ^ 21 + ((6113 / 790) : ℂ) * ζ ^ 22 + ((6113 / 790) : ℂ) * ζ ^ 24 + ((2532 / 395) : ℂ) * ζ ^ 25 + ((1149 / 158) : ℂ) * ζ ^ 27 + ((3341 / 395) : ℂ) * ζ ^ 28 - ((781 / 395) : ℂ) * ζ ^ 29 + ((569 / 790) : ℂ) * ζ ^ 30 + ((1149 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep08CoefficientIdentity02 :
    row18_reducedY55_combinationStep08Coefficient02 =
      row18_reducedY55_combinationStep07Coefficient02 +
        row18_reducedY55_combinationStep08Multiplier *
          (((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep08Coefficient02 row18_reducedY55_combinationStep07Coefficient02 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 (((17141 / 12482) : ℂ) + ((17149 / 18723) : ℂ) * ζ ^ 1 - ((1322 / 18723) : ℂ) * ζ ^ 2 + ((2023 / 18723) : ℂ) * ζ ^ 3 - ((193 / 158) : ℂ) * ζ ^ 4 + ((2 / 237) : ℂ) * ζ ^ 5 - ((65 / 158) : ℂ) * ζ ^ 6 + ((1965 / 6241) : ℂ) * ζ ^ 7 - ((9055 / 6241) : ℂ) * ζ ^ 8 - ((4619 / 37446) : ℂ) * ζ ^ 9 + ((15910 / 18723) : ℂ) * ζ ^ 10 + ((24929 / 37446) : ℂ) * ζ ^ 11 + ((18613 / 18723) : ℂ) * ζ ^ 12 + ((3973 / 37446) : ℂ) * ζ ^ 13 + ((1100 / 6241) : ℂ) * ζ ^ 14 - ((429 / 12482) : ℂ) * ζ ^ 15 + ((4681 / 37446) : ℂ) * ζ ^ 16 - ((12349 / 12482) : ℂ) * ζ ^ 17 - ((2843 / 37446) : ℂ) * ζ ^ 18 - ((7289 / 18723) : ℂ) * ζ ^ 19 + ((9829 / 12482) : ℂ) * ζ ^ 20 + ((2927 / 37446) : ℂ) * ζ ^ 21 - ((4463 / 18723) : ℂ) * ζ ^ 22 - ((3509 / 6241) : ℂ) * ζ ^ 23 + ((24178 / 18723) : ℂ) * ζ ^ 24 + ((10727 / 37446) : ℂ) * ζ ^ 25 - ((7237 / 18723) : ℂ) * ζ ^ 26 - ((18938 / 18723) : ℂ) * ζ ^ 27 + ((12803 / 37446) : ℂ) * ζ ^ 28 + ((6055 / 12482) : ℂ) * ζ ^ 29 - ((1625 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep08Coefficient03 : ℂ :=
  (-((46 / 79) : ℂ) - ((24 / 79) : ℂ) * ζ ^ 1 - ((19 / 158) : ℂ) * ζ ^ 2 + ((77 / 158) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((2 / 79) : ℂ) * ζ ^ 6 + ((5 / 158) : ℂ) * ζ ^ 8 + ((95 / 158) : ℂ) * ζ ^ 9 + ((9 / 79) : ℂ) * ζ ^ 11 + ((5 / 158) : ℂ) * ζ ^ 12 + ((24 / 79) : ℂ) * ζ ^ 13 - ((5 / 79) : ℂ) * ζ ^ 15 + ((24 / 79) : ℂ) * ζ ^ 17 - ((23 / 158) : ℂ) * ζ ^ 18 - ((29 / 158) : ℂ) * ζ ^ 21 + ((19 / 158) : ℂ) * ζ ^ 22 - ((67 / 158) : ℂ) * ζ ^ 25 + ((29 / 158) : ℂ) * ζ ^ 27 - ((5 / 158) : ℂ) * ζ ^ 28 - ((24 / 79) : ℂ) * ζ ^ 29 + ((1 / 79) : ℂ) * ζ ^ 30 - ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep08CoefficientIdentity03 :
    row18_reducedY55_combinationStep08Coefficient03 =
      row18_reducedY55_combinationStep07Coefficient03 +
        row18_reducedY55_combinationStep08Multiplier *
          (((16 / 79) : ℂ) + ((35 / 316) : ℂ) * ζ ^ 1 - ((61 / 316) : ℂ) * ζ ^ 2 + ((87 / 316) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 - ((6 / 79) : ℂ) * ζ ^ 8 - ((31 / 316) : ℂ) * ζ ^ 9 - ((14 / 79) : ℂ) * ζ ^ 11 - ((26 / 79) : ℂ) * ζ ^ 12 - ((35 / 316) : ℂ) * ζ ^ 13 - ((49 / 316) : ℂ) * ζ ^ 15 - ((35 / 316) : ℂ) * ζ ^ 17 + ((61 / 316) : ℂ) * ζ ^ 18 + ((13 / 79) : ℂ) * ζ ^ 21 + ((61 / 316) : ℂ) * ζ ^ 22 + ((32 / 79) : ℂ) * ζ ^ 24 + ((19 / 158) : ℂ) * ζ ^ 25 + ((13 / 79) : ℂ) * ζ ^ 27 + ((6 / 79) : ℂ) * ζ ^ 28 + ((35 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((14 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep08Coefficient03 row18_reducedY55_combinationStep07Coefficient03 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 (((60149 / 37446) : ℂ) + ((487 / 474) : ℂ) * ζ ^ 1 - ((30703 / 37446) : ℂ) * ζ ^ 2 - ((23 / 79) : ℂ) * ζ ^ 3 - ((13229 / 18723) : ℂ) * ζ ^ 4 - ((185 / 237) : ℂ) * ζ ^ 5 + ((12089 / 37446) : ℂ) * ζ ^ 6 - ((41 / 158) : ℂ) * ζ ^ 7 + ((1367 / 18723) : ℂ) * ζ ^ 8 - ((299 / 237) : ℂ) * ζ ^ 9 + ((8707 / 18723) : ℂ) * ζ ^ 10 - ((17 / 158) : ℂ) * ζ ^ 11 - ((27785 / 37446) : ℂ) * ζ ^ 12 - ((74 / 79) : ℂ) * ζ ^ 13 + ((4798 / 6241) : ℂ) * ζ ^ 14 + ((299 / 474) : ℂ) * ζ ^ 15 + ((5205 / 6241) : ℂ) * ζ ^ 16 - ((21 / 158) : ℂ) * ζ ^ 17 + ((7455 / 12482) : ℂ) * ζ ^ 18 + ((93 / 79) : ℂ) * ζ ^ 19 + ((31975 / 37446) : ℂ) * ζ ^ 20 + ((641 / 474) : ℂ) * ζ ^ 21 - ((4054 / 18723) : ℂ) * ζ ^ 22 - ((103 / 474) : ℂ) * ζ ^ 23 - ((2113 / 18723) : ℂ) * ζ ^ 24 + ((473 / 474) : ℂ) * ζ ^ 25 - ((29734 / 18723) : ℂ) * ζ ^ 26 + ((173 / 474) : ℂ) * ζ ^ 27 - ((2167 / 18723) : ℂ) * ζ ^ 28 + ((212 / 237) : ℂ) * ζ ^ 29 - ((18200 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep08Coefficient04 : ℂ :=
  (-((462 / 79) : ℂ) + ((248 / 79) : ℂ) * ζ ^ 1 - ((3051 / 395) : ℂ) * ζ ^ 2 - ((77 / 79) : ℂ) * ζ ^ 3 - ((414 / 79) : ℂ) * ζ ^ 5 - ((4264 / 395) : ℂ) * ζ ^ 6 - ((351 / 79) : ℂ) * ζ ^ 8 - ((644 / 79) : ℂ) * ζ ^ 9 - ((567 / 79) : ℂ) * ζ ^ 11 - ((351 / 79) : ℂ) * ζ ^ 12 - ((248 / 79) : ℂ) * ζ ^ 13 - ((585 / 79) : ℂ) * ζ ^ 15 - ((248 / 79) : ℂ) * ζ ^ 17 + ((1213 / 395) : ℂ) * ζ ^ 18 - ((171 / 79) : ℂ) * ζ ^ 21 + ((3051 / 395) : ℂ) * ζ ^ 22 + ((662 / 79) : ℂ) * ζ ^ 25 + ((171 / 79) : ℂ) * ζ ^ 27 + ((351 / 79) : ℂ) * ζ ^ 28 + ((248 / 79) : ℂ) * ζ ^ 29 - ((2132 / 395) : ℂ) * ζ ^ 30 + ((567 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep08CoefficientIdentity04 :
    row18_reducedY55_combinationStep08Coefficient04 =
      row18_reducedY55_combinationStep07Coefficient04 +
        row18_reducedY55_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep08Coefficient04 row18_reducedY55_combinationStep07Coefficient04 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep08Coefficient05 : ℂ :=
  (-((71 / 79) : ℂ) + ((87 / 79) : ℂ) * ζ ^ 1 - ((605 / 79) : ℂ) * ζ ^ 2 - ((567 / 79) : ℂ) * ζ ^ 5 - ((534 / 79) : ℂ) * ζ ^ 6 - ((534 / 79) : ℂ) * ζ ^ 8 - ((567 / 79) : ℂ) * ζ ^ 9 - ((636 / 79) : ℂ) * ζ ^ 11 - ((323 / 79) : ℂ) * ζ ^ 12 - ((87 / 79) : ℂ) * ζ ^ 13 - ((432 / 79) : ℂ) * ζ ^ 15 - ((87 / 79) : ℂ) * ζ ^ 17 + ((287 / 79) : ℂ) * ζ ^ 18 + ((240 / 79) : ℂ) * ζ ^ 21 + ((605 / 79) : ℂ) * ζ ^ 22 + ((247 / 79) : ℂ) * ζ ^ 24 + ((654 / 79) : ℂ) * ζ ^ 25 + ((432 / 79) : ℂ) * ζ ^ 27 + ((534 / 79) : ℂ) * ζ ^ 28 + ((87 / 79) : ℂ) * ζ ^ 29 - ((211 / 79) : ℂ) * ζ ^ 30 + ((636 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep08CoefficientIdentity05 :
    row18_reducedY55_combinationStep08Coefficient05 =
      row18_reducedY55_combinationStep07Coefficient05 +
        row18_reducedY55_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep08Coefficient05 row18_reducedY55_combinationStep07Coefficient05 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep08Coefficient06 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep08CoefficientIdentity06 :
    row18_reducedY55_combinationStep08Coefficient06 =
      row18_reducedY55_combinationStep07Coefficient06 +
        row18_reducedY55_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep08Coefficient06 row18_reducedY55_combinationStep07Coefficient06 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep08Coefficient07 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep08CoefficientIdentity07 :
    row18_reducedY55_combinationStep08Coefficient07 =
      row18_reducedY55_combinationStep07Coefficient07 +
        row18_reducedY55_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep08Coefficient07 row18_reducedY55_combinationStep07Coefficient07 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep08Coefficient08 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep08CoefficientIdentity08 :
    row18_reducedY55_combinationStep08Coefficient08 =
      row18_reducedY55_combinationStep07Coefficient08 +
        row18_reducedY55_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep08Coefficient08 row18_reducedY55_combinationStep07Coefficient08 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep08Coefficient09 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep08CoefficientIdentity09 :
    row18_reducedY55_combinationStep08Coefficient09 =
      row18_reducedY55_combinationStep07Coefficient09 +
        row18_reducedY55_combinationStep08Multiplier *
          (((5 / 79) : ℂ) + ((43 / 316) : ℂ) * ζ ^ 1 + ((9 / 158) : ℂ) * ζ ^ 2 + ((63 / 316) : ℂ) * ζ ^ 5 - ((1 / 158) : ℂ) * ζ ^ 6 - ((1 / 158) : ℂ) * ζ ^ 8 + ((63 / 316) : ℂ) * ζ ^ 9 - ((57 / 158) : ℂ) * ζ ^ 11 - ((31 / 316) : ℂ) * ζ ^ 12 - ((43 / 316) : ℂ) * ζ ^ 13 + ((3 / 79) : ℂ) * ζ ^ 15 - ((43 / 316) : ℂ) * ζ ^ 17 + ((3 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 - ((9 / 158) : ℂ) * ζ ^ 22 - ((1 / 316) : ℂ) * ζ ^ 24 - ((5 / 79) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((1 / 158) : ℂ) * ζ ^ 28 + ((43 / 316) : ℂ) * ζ ^ 29 + ((29 / 316) : ℂ) * ζ ^ 30 + ((57 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep08Coefficient09 row18_reducedY55_combinationStep07Coefficient09 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 (-((1067 / 37446) : ℂ) + ((72211 / 37446) : ℂ) * ζ ^ 1 + ((94585 / 37446) : ℂ) * ζ ^ 2 + ((45781 / 37446) : ℂ) * ζ ^ 3 - ((5105 / 12482) : ℂ) * ζ ^ 4 + ((34 / 237) : ℂ) * ζ ^ 5 + ((3197 / 37446) : ℂ) * ζ ^ 6 - ((8839 / 6241) : ℂ) * ζ ^ 7 - ((81197 / 37446) : ℂ) * ζ ^ 8 - ((26950 / 18723) : ℂ) * ζ ^ 9 + ((12281 / 37446) : ℂ) * ζ ^ 10 - ((7164 / 6241) : ℂ) * ζ ^ 11 - ((11084 / 18723) : ℂ) * ζ ^ 12 + ((6598 / 18723) : ℂ) * ζ ^ 13 + ((29001 / 12482) : ℂ) * ζ ^ 14 + ((69874 / 18723) : ℂ) * ζ ^ 15 + ((19597 / 18723) : ℂ) * ζ ^ 16 - ((42725 / 18723) : ℂ) * ζ ^ 17 - ((61819 / 18723) : ℂ) * ζ ^ 18 - ((43349 / 37446) : ℂ) * ζ ^ 19 + ((9803 / 37446) : ℂ) * ζ ^ 20 + ((35657 / 37446) : ℂ) * ζ ^ 21 - ((6305 / 18723) : ℂ) * ζ ^ 22 + ((3883 / 12482) : ℂ) * ζ ^ 23 - ((10347 / 12482) : ℂ) * ζ ^ 24 + ((30059 / 37446) : ℂ) * ζ ^ 25 + ((15285 / 12482) : ℂ) * ζ ^ 26 + ((34415 / 12482) : ℂ) * ζ ^ 27 + ((14735 / 37446) : ℂ) * ζ ^ 28 - ((7088 / 18723) : ℂ) * ζ ^ 29 - ((12350 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep08Coefficient10 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep08CoefficientIdentity10 :
    row18_reducedY55_combinationStep08Coefficient10 =
      row18_reducedY55_combinationStep07Coefficient10 +
        row18_reducedY55_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep08Coefficient10 row18_reducedY55_combinationStep07Coefficient10 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep08Coefficient11 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY55_combinationStep08CoefficientIdentity11 :
    row18_reducedY55_combinationStep08Coefficient11 =
      row18_reducedY55_combinationStep07Coefficient11 +
        row18_reducedY55_combinationStep08Multiplier *
          (-((16 / 79) : ℂ) - ((35 / 316) : ℂ) * ζ ^ 1 + ((61 / 316) : ℂ) * ζ ^ 2 - ((87 / 316) : ℂ) * ζ ^ 3 + ((3 / 316) : ℂ) * ζ ^ 5 + ((6 / 79) : ℂ) * ζ ^ 8 + ((31 / 316) : ℂ) * ζ ^ 9 + ((14 / 79) : ℂ) * ζ ^ 11 + ((26 / 79) : ℂ) * ζ ^ 12 + ((35 / 316) : ℂ) * ζ ^ 13 + ((49 / 316) : ℂ) * ζ ^ 15 + ((35 / 316) : ℂ) * ζ ^ 17 - ((61 / 316) : ℂ) * ζ ^ 18 - ((13 / 79) : ℂ) * ζ ^ 21 - ((61 / 316) : ℂ) * ζ ^ 22 - ((32 / 79) : ℂ) * ζ ^ 24 - ((19 / 158) : ℂ) * ζ ^ 25 - ((13 / 79) : ℂ) * ζ ^ 27 - ((6 / 79) : ℂ) * ζ ^ 28 - ((35 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((14 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep08Coefficient11 row18_reducedY55_combinationStep07Coefficient11 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 (-((60149 / 37446) : ℂ) - ((487 / 474) : ℂ) * ζ ^ 1 + ((30703 / 37446) : ℂ) * ζ ^ 2 + ((23 / 79) : ℂ) * ζ ^ 3 + ((13229 / 18723) : ℂ) * ζ ^ 4 + ((185 / 237) : ℂ) * ζ ^ 5 - ((12089 / 37446) : ℂ) * ζ ^ 6 + ((41 / 158) : ℂ) * ζ ^ 7 - ((1367 / 18723) : ℂ) * ζ ^ 8 + ((299 / 237) : ℂ) * ζ ^ 9 - ((8707 / 18723) : ℂ) * ζ ^ 10 + ((17 / 158) : ℂ) * ζ ^ 11 + ((27785 / 37446) : ℂ) * ζ ^ 12 + ((74 / 79) : ℂ) * ζ ^ 13 - ((4798 / 6241) : ℂ) * ζ ^ 14 - ((299 / 474) : ℂ) * ζ ^ 15 - ((5205 / 6241) : ℂ) * ζ ^ 16 + ((21 / 158) : ℂ) * ζ ^ 17 - ((7455 / 12482) : ℂ) * ζ ^ 18 - ((93 / 79) : ℂ) * ζ ^ 19 - ((31975 / 37446) : ℂ) * ζ ^ 20 - ((641 / 474) : ℂ) * ζ ^ 21 + ((4054 / 18723) : ℂ) * ζ ^ 22 + ((103 / 474) : ℂ) * ζ ^ 23 + ((2113 / 18723) : ℂ) * ζ ^ 24 - ((473 / 474) : ℂ) * ζ ^ 25 + ((29734 / 18723) : ℂ) * ζ ^ 26 - ((173 / 474) : ℂ) * ζ ^ 27 + ((2167 / 18723) : ℂ) * ζ ^ 28 - ((212 / 237) : ℂ) * ζ ^ 29 + ((18200 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep08Coefficient12 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep08CoefficientIdentity12 :
    row18_reducedY55_combinationStep08Coefficient12 =
      row18_reducedY55_combinationStep07Coefficient12 +
        row18_reducedY55_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep08Coefficient12 row18_reducedY55_combinationStep07Coefficient12 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep08Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep08CoefficientIdentity13 :
    row18_reducedY55_combinationStep08Coefficient13 =
      row18_reducedY55_combinationStep07Coefficient13 +
        row18_reducedY55_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep08Coefficient13 row18_reducedY55_combinationStep07Coefficient13 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep08Coefficient14 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep08CoefficientIdentity14 :
    row18_reducedY55_combinationStep08Coefficient14 =
      row18_reducedY55_combinationStep07Coefficient14 +
        row18_reducedY55_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep08Coefficient14 row18_reducedY55_combinationStep07Coefficient14 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep08Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep08CoefficientIdentity15 :
    row18_reducedY55_combinationStep08Coefficient15 =
      row18_reducedY55_combinationStep07Coefficient15 +
        row18_reducedY55_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep08Coefficient15 row18_reducedY55_combinationStep07Coefficient15 row18_reducedY55_combinationStep08Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY55_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY55_combinationStep08Coefficient00) * Y 0 0
      + (row18_reducedY55_combinationStep08Coefficient01) * Y 0 1
      + (row18_reducedY55_combinationStep08Coefficient02) * Y 1 0
      + (row18_reducedY55_combinationStep08Coefficient03) * Y 1 1
      + (row18_reducedY55_combinationStep08Coefficient04) * Y 2 2
      + (row18_reducedY55_combinationStep08Coefficient05) * Y 2 3
      + (row18_reducedY55_combinationStep08Coefficient06) * Y 3 2
      + (row18_reducedY55_combinationStep08Coefficient07) * Y 3 3
      + (row18_reducedY55_combinationStep08Coefficient08) * Y 4 4
      + (row18_reducedY55_combinationStep08Coefficient09) * Y 4 5
      + (row18_reducedY55_combinationStep08Coefficient10) * Y 5 4
      + (row18_reducedY55_combinationStep08Coefficient11) * Y 5 5
      + (row18_reducedY55_combinationStep08Coefficient12) * Y 6 6
      + (row18_reducedY55_combinationStep08Coefficient13) * Y 6 7
      + (row18_reducedY55_combinationStep08Coefficient14) * Y 7 6
      + (row18_reducedY55_combinationStep08Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY55_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation15
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY55_combinationStep08CoefficientIdentity00,
      row18_reducedY55_combinationStep08CoefficientIdentity01,
      row18_reducedY55_combinationStep08CoefficientIdentity02,
      row18_reducedY55_combinationStep08CoefficientIdentity03,
      row18_reducedY55_combinationStep08CoefficientIdentity04,
      row18_reducedY55_combinationStep08CoefficientIdentity05,
      row18_reducedY55_combinationStep08CoefficientIdentity06,
      row18_reducedY55_combinationStep08CoefficientIdentity07,
      row18_reducedY55_combinationStep08CoefficientIdentity08,
      row18_reducedY55_combinationStep08CoefficientIdentity09,
      row18_reducedY55_combinationStep08CoefficientIdentity10,
      row18_reducedY55_combinationStep08CoefficientIdentity11,
      row18_reducedY55_combinationStep08CoefficientIdentity12,
      row18_reducedY55_combinationStep08CoefficientIdentity13,
      row18_reducedY55_combinationStep08CoefficientIdentity14,
      row18_reducedY55_combinationStep08CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY55_combinationStep08Multiplier * equation

private def row18_reducedY55_combinationStep09Multiplier : ℂ :=
  (-((208 / 79) : ℂ) - ((380 / 79) : ℂ) * ζ ^ 1 + ((60 / 79) : ℂ) * ζ ^ 2 - ((132 / 79) : ℂ) * ζ ^ 3 - ((306 / 79) : ℂ) * ζ ^ 5 + ((236 / 79) : ℂ) * ζ ^ 8 + ((156 / 79) : ℂ) * ζ ^ 9 - ((24 / 79) : ℂ) * ζ ^ 11 + ((180 / 79) : ℂ) * ζ ^ 12 + ((380 / 79) : ℂ) * ζ ^ 13 + ((58 / 79) : ℂ) * ζ ^ 15 + ((380 / 79) : ℂ) * ζ ^ 17 - ((60 / 79) : ℂ) * ζ ^ 18 + ((248 / 79) : ℂ) * ζ ^ 21 - ((60 / 79) : ℂ) * ζ ^ 22 - ((416 / 79) : ℂ) * ζ ^ 24 - ((74 / 79) : ℂ) * ζ ^ 25 + ((248 / 79) : ℂ) * ζ ^ 27 - ((236 / 79) : ℂ) * ζ ^ 28 - ((380 / 79) : ℂ) * ζ ^ 29 - ((160 / 79) : ℂ) * ζ ^ 30 + ((24 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY55_combinationStep09Coefficient00 : ℂ :=
  (((462 / 79) : ℂ) - ((248 / 79) : ℂ) * ζ ^ 1 + ((3051 / 395) : ℂ) * ζ ^ 2 + ((77 / 79) : ℂ) * ζ ^ 3 + ((414 / 79) : ℂ) * ζ ^ 5 + ((4264 / 395) : ℂ) * ζ ^ 6 + ((351 / 79) : ℂ) * ζ ^ 8 + ((644 / 79) : ℂ) * ζ ^ 9 + ((567 / 79) : ℂ) * ζ ^ 11 + ((351 / 79) : ℂ) * ζ ^ 12 + ((248 / 79) : ℂ) * ζ ^ 13 + ((585 / 79) : ℂ) * ζ ^ 15 + ((248 / 79) : ℂ) * ζ ^ 17 - ((1213 / 395) : ℂ) * ζ ^ 18 + ((171 / 79) : ℂ) * ζ ^ 21 - ((3051 / 395) : ℂ) * ζ ^ 22 - ((662 / 79) : ℂ) * ζ ^ 25 - ((171 / 79) : ℂ) * ζ ^ 27 - ((351 / 79) : ℂ) * ζ ^ 28 - ((248 / 79) : ℂ) * ζ ^ 29 + ((2132 / 395) : ℂ) * ζ ^ 30 - ((567 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep09CoefficientIdentity00 :
    row18_reducedY55_combinationStep09Coefficient00 =
      row18_reducedY55_combinationStep08Coefficient00 +
        row18_reducedY55_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep09Coefficient00 row18_reducedY55_combinationStep08Coefficient00 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep09Coefficient01 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep09CoefficientIdentity01 :
    row18_reducedY55_combinationStep09Coefficient01 =
      row18_reducedY55_combinationStep08Coefficient01 +
        row18_reducedY55_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep09Coefficient01 row18_reducedY55_combinationStep08Coefficient01 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep09Coefficient02 : ℂ :=
  (((817 / 395) : ℂ) - ((596 / 395) : ℂ) * ζ ^ 1 - ((2904 / 395) : ℂ) * ζ ^ 2 + ((257 / 79) : ℂ) * ζ ^ 3 - ((3298 / 395) : ℂ) * ζ ^ 5 - ((1521 / 395) : ℂ) * ζ ^ 6 - ((3281 / 395) : ℂ) * ζ ^ 8 - ((1053 / 395) : ℂ) * ζ ^ 9 - ((620 / 79) : ℂ) * ζ ^ 11 - ((1383 / 395) : ℂ) * ζ ^ 12 + ((596 / 395) : ℂ) * ζ ^ 13 - ((257 / 79) : ℂ) * ζ ^ 15 + ((596 / 395) : ℂ) * ζ ^ 17 + ((2087 / 395) : ℂ) * ζ ^ 18 + ((2702 / 395) : ℂ) * ζ ^ 21 + ((2904 / 395) : ℂ) * ζ ^ 22 + ((2904 / 395) : ℂ) * ζ ^ 24 + ((2702 / 395) : ℂ) * ζ ^ 25 + ((620 / 79) : ℂ) * ζ ^ 27 + ((3281 / 395) : ℂ) * ζ ^ 28 - ((596 / 395) : ℂ) * ζ ^ 29 + ((377 / 395) : ℂ) * ζ ^ 30 + ((620 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep09CoefficientIdentity02 :
    row18_reducedY55_combinationStep09Coefficient02 =
      row18_reducedY55_combinationStep08Coefficient02 +
        row18_reducedY55_combinationStep09Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep09Coefficient02 row18_reducedY55_combinationStep08Coefficient02 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 (((4978 / 6241) : ℂ) + ((1363 / 6241) : ℂ) * ζ ^ 1 - ((2345 / 12482) : ℂ) * ζ ^ 2 + ((2043 / 12482) : ℂ) * ζ ^ 3 - ((2434 / 6241) : ℂ) * ζ ^ 4 + ((1310 / 6241) : ℂ) * ζ ^ 5 + ((10323 / 12482) : ℂ) * ζ ^ 6 + ((3050 / 6241) : ℂ) * ζ ^ 7 - ((2498 / 6241) : ℂ) * ζ ^ 8 - ((1739 / 12482) : ℂ) * ζ ^ 9 + ((5095 / 12482) : ℂ) * ζ ^ 10 - ((4917 / 12482) : ℂ) * ζ ^ 11 + ((4607 / 6241) : ℂ) * ζ ^ 12 - ((1753 / 6241) : ℂ) * ζ ^ 13 - ((2961 / 6241) : ℂ) * ζ ^ 14 + ((8021 / 12482) : ℂ) * ζ ^ 15 - ((347 / 6241) : ℂ) * ζ ^ 16 + ((1852 / 6241) : ℂ) * ζ ^ 17 + ((505 / 6241) : ℂ) * ζ ^ 18 - ((728 / 6241) : ℂ) * ζ ^ 19 + ((1667 / 6241) : ℂ) * ζ ^ 20 - ((6627 / 12482) : ℂ) * ζ ^ 21 - ((4319 / 12482) : ℂ) * ζ ^ 22 + ((92 / 6241) : ℂ) * ζ ^ 23 + ((4045 / 12482) : ℂ) * ζ ^ 24 + ((7860 / 6241) : ℂ) * ζ ^ 25 + ((13 / 6241) : ℂ) * ζ ^ 26 - ((3509 / 6241) : ℂ) * ζ ^ 27 - ((573 / 6241) : ℂ) * ζ ^ 28 + ((888 / 6241) : ℂ) * ζ ^ 29 - ((90 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep09Coefficient03 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep09CoefficientIdentity03 :
    row18_reducedY55_combinationStep09Coefficient03 =
      row18_reducedY55_combinationStep08Coefficient03 +
        row18_reducedY55_combinationStep09Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep09Coefficient03 row18_reducedY55_combinationStep08Coefficient03 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 (-((4466 / 6241) : ℂ) - ((3988 / 6241) : ℂ) * ζ ^ 1 - ((6751 / 12482) : ℂ) * ζ ^ 2 - ((1189 / 12482) : ℂ) * ζ ^ 3 + ((4723 / 6241) : ℂ) * ζ ^ 4 + ((1569 / 12482) : ℂ) * ζ ^ 5 - ((125 / 6241) : ℂ) * ζ ^ 6 - ((1633 / 6241) : ℂ) * ζ ^ 7 - ((4183 / 6241) : ℂ) * ζ ^ 8 + ((5487 / 6241) : ℂ) * ζ ^ 9 + ((1469 / 6241) : ℂ) * ζ ^ 10 + ((2829 / 6241) : ℂ) * ζ ^ 11 + ((1961 / 12482) : ℂ) * ζ ^ 12 - ((293 / 6241) : ℂ) * ζ ^ 13 + ((139 / 6241) : ℂ) * ζ ^ 14 + ((2645 / 12482) : ℂ) * ζ ^ 15 - ((191 / 6241) : ℂ) * ζ ^ 16 + ((3653 / 6241) : ℂ) * ζ ^ 17 + ((2886 / 6241) : ℂ) * ζ ^ 18 + ((3632 / 6241) : ℂ) * ζ ^ 19 - ((3885 / 6241) : ℂ) * ζ ^ 20 - ((2547 / 6241) : ℂ) * ζ ^ 21 + ((2357 / 12482) : ℂ) * ζ ^ 22 + ((3984 / 6241) : ℂ) * ζ ^ 23 + ((697 / 6241) : ℂ) * ζ ^ 24 - ((627 / 6241) : ℂ) * ζ ^ 25 - ((2849 / 6241) : ℂ) * ζ ^ 26 - ((718 / 6241) : ℂ) * ζ ^ 27 + ((916 / 6241) : ℂ) * ζ ^ 28 + ((8 / 79) : ℂ) * ζ ^ 29 - ((84 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep09Coefficient04 : ℂ :=
  (-((462 / 79) : ℂ) + ((248 / 79) : ℂ) * ζ ^ 1 - ((3051 / 395) : ℂ) * ζ ^ 2 - ((77 / 79) : ℂ) * ζ ^ 3 - ((414 / 79) : ℂ) * ζ ^ 5 - ((4264 / 395) : ℂ) * ζ ^ 6 - ((351 / 79) : ℂ) * ζ ^ 8 - ((644 / 79) : ℂ) * ζ ^ 9 - ((567 / 79) : ℂ) * ζ ^ 11 - ((351 / 79) : ℂ) * ζ ^ 12 - ((248 / 79) : ℂ) * ζ ^ 13 - ((585 / 79) : ℂ) * ζ ^ 15 - ((248 / 79) : ℂ) * ζ ^ 17 + ((1213 / 395) : ℂ) * ζ ^ 18 - ((171 / 79) : ℂ) * ζ ^ 21 + ((3051 / 395) : ℂ) * ζ ^ 22 + ((662 / 79) : ℂ) * ζ ^ 25 + ((171 / 79) : ℂ) * ζ ^ 27 + ((351 / 79) : ℂ) * ζ ^ 28 + ((248 / 79) : ℂ) * ζ ^ 29 - ((2132 / 395) : ℂ) * ζ ^ 30 + ((567 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep09CoefficientIdentity04 :
    row18_reducedY55_combinationStep09Coefficient04 =
      row18_reducedY55_combinationStep08Coefficient04 +
        row18_reducedY55_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep09Coefficient04 row18_reducedY55_combinationStep08Coefficient04 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep09Coefficient05 : ℂ :=
  (-((71 / 79) : ℂ) + ((87 / 79) : ℂ) * ζ ^ 1 - ((605 / 79) : ℂ) * ζ ^ 2 - ((567 / 79) : ℂ) * ζ ^ 5 - ((534 / 79) : ℂ) * ζ ^ 6 - ((534 / 79) : ℂ) * ζ ^ 8 - ((567 / 79) : ℂ) * ζ ^ 9 - ((636 / 79) : ℂ) * ζ ^ 11 - ((323 / 79) : ℂ) * ζ ^ 12 - ((87 / 79) : ℂ) * ζ ^ 13 - ((432 / 79) : ℂ) * ζ ^ 15 - ((87 / 79) : ℂ) * ζ ^ 17 + ((287 / 79) : ℂ) * ζ ^ 18 + ((240 / 79) : ℂ) * ζ ^ 21 + ((605 / 79) : ℂ) * ζ ^ 22 + ((247 / 79) : ℂ) * ζ ^ 24 + ((654 / 79) : ℂ) * ζ ^ 25 + ((432 / 79) : ℂ) * ζ ^ 27 + ((534 / 79) : ℂ) * ζ ^ 28 + ((87 / 79) : ℂ) * ζ ^ 29 - ((211 / 79) : ℂ) * ζ ^ 30 + ((636 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY55_combinationStep09CoefficientIdentity05 :
    row18_reducedY55_combinationStep09Coefficient05 =
      row18_reducedY55_combinationStep08Coefficient05 +
        row18_reducedY55_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep09Coefficient05 row18_reducedY55_combinationStep08Coefficient05 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep09Coefficient06 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep09CoefficientIdentity06 :
    row18_reducedY55_combinationStep09Coefficient06 =
      row18_reducedY55_combinationStep08Coefficient06 +
        row18_reducedY55_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep09Coefficient06 row18_reducedY55_combinationStep08Coefficient06 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep09Coefficient07 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep09CoefficientIdentity07 :
    row18_reducedY55_combinationStep09Coefficient07 =
      row18_reducedY55_combinationStep08Coefficient07 +
        row18_reducedY55_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep09Coefficient07 row18_reducedY55_combinationStep08Coefficient07 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep09Coefficient08 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep09CoefficientIdentity08 :
    row18_reducedY55_combinationStep09Coefficient08 =
      row18_reducedY55_combinationStep08Coefficient08 +
        row18_reducedY55_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep09Coefficient08 row18_reducedY55_combinationStep08Coefficient08 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep09Coefficient09 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep09CoefficientIdentity09 :
    row18_reducedY55_combinationStep09Coefficient09 =
      row18_reducedY55_combinationStep08Coefficient09 +
        row18_reducedY55_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep09Coefficient09 row18_reducedY55_combinationStep08Coefficient09 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep09Coefficient10 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep09CoefficientIdentity10 :
    row18_reducedY55_combinationStep09Coefficient10 =
      row18_reducedY55_combinationStep08Coefficient10 +
        row18_reducedY55_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep09Coefficient10 row18_reducedY55_combinationStep08Coefficient10 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep09Coefficient11 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY55_combinationStep09CoefficientIdentity11 :
    row18_reducedY55_combinationStep09Coefficient11 =
      row18_reducedY55_combinationStep08Coefficient11 +
        row18_reducedY55_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep09Coefficient11 row18_reducedY55_combinationStep08Coefficient11 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep09Coefficient12 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep09CoefficientIdentity12 :
    row18_reducedY55_combinationStep09Coefficient12 =
      row18_reducedY55_combinationStep08Coefficient12 +
        row18_reducedY55_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep09Coefficient12 row18_reducedY55_combinationStep08Coefficient12 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep09Coefficient13 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep09CoefficientIdentity13 :
    row18_reducedY55_combinationStep09Coefficient13 =
      row18_reducedY55_combinationStep08Coefficient13 +
        row18_reducedY55_combinationStep09Multiplier *
          (((5 / 316) : ℂ) - ((3 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((33 / 158) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 + ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 + ((3 / 316) : ℂ) * ζ ^ 9 + ((33 / 316) : ℂ) * ζ ^ 11 + ((3 / 79) : ℂ) * ζ ^ 12 + ((3 / 316) : ℂ) * ζ ^ 13 + ((35 / 158) : ℂ) * ζ ^ 15 + ((3 / 316) : ℂ) * ζ ^ 17 + ((19 / 316) : ℂ) * ζ ^ 18 + ((45 / 158) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((1 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 - ((3 / 316) : ℂ) * ζ ^ 29 + ((13 / 79) : ℂ) * ζ ^ 30 - ((33 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep09Coefficient13 row18_reducedY55_combinationStep08Coefficient13 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 (((3058 / 6241) : ℂ) + ((392 / 6241) : ℂ) * ζ ^ 1 - ((2841 / 12482) : ℂ) * ζ ^ 2 - ((103 / 6241) : ℂ) * ζ ^ 3 + ((3836 / 6241) : ℂ) * ζ ^ 4 - ((4895 / 12482) : ℂ) * ζ ^ 5 - ((2491 / 12482) : ℂ) * ζ ^ 6 - ((12839 / 12482) : ℂ) * ζ ^ 7 + ((2017 / 12482) : ℂ) * ζ ^ 8 + ((10211 / 12482) : ℂ) * ζ ^ 9 + ((2538 / 6241) : ℂ) * ζ ^ 10 - ((1486 / 6241) : ℂ) * ζ ^ 11 - ((24711 / 12482) : ℂ) * ζ ^ 12 - ((6425 / 12482) : ℂ) * ζ ^ 13 - ((1453 / 6241) : ℂ) * ζ ^ 14 + ((5079 / 12482) : ℂ) * ζ ^ 15 + ((2641 / 12482) : ℂ) * ζ ^ 16 - ((707 / 12482) : ℂ) * ζ ^ 17 - ((12423 / 12482) : ℂ) * ζ ^ 18 - ((1465 / 6241) : ℂ) * ζ ^ 19 - ((10497 / 12482) : ℂ) * ζ ^ 20 - ((3557 / 6241) : ℂ) * ζ ^ 21 - ((2515 / 12482) : ℂ) * ζ ^ 22 + ((7701 / 6241) : ℂ) * ζ ^ 23 - ((6705 / 12482) : ℂ) * ζ ^ 24 - ((2191 / 6241) : ℂ) * ζ ^ 25 - ((6207 / 6241) : ℂ) * ζ ^ 26 - ((2633 / 6241) : ℂ) * ζ ^ 27 + ((1037 / 6241) : ℂ) * ζ ^ 28 + ((1632 / 6241) : ℂ) * ζ ^ 29 - ((198 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep09Coefficient14 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep09CoefficientIdentity14 :
    row18_reducedY55_combinationStep09Coefficient14 =
      row18_reducedY55_combinationStep08Coefficient14 +
        row18_reducedY55_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep09Coefficient14 row18_reducedY55_combinationStep08Coefficient14 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep09Coefficient15 : ℂ :=
  (-(1 : ℂ))

private theorem row18_reducedY55_combinationStep09CoefficientIdentity15 :
    row18_reducedY55_combinationStep09Coefficient15 =
      row18_reducedY55_combinationStep08Coefficient15 +
        row18_reducedY55_combinationStep09Multiplier *
          (-((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((35 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep09Coefficient15 row18_reducedY55_combinationStep08Coefficient15 row18_reducedY55_combinationStep09Multiplier
  close_cyclotomic_row18 (((4466 / 6241) : ℂ) + ((3988 / 6241) : ℂ) * ζ ^ 1 + ((6751 / 12482) : ℂ) * ζ ^ 2 + ((1189 / 12482) : ℂ) * ζ ^ 3 - ((4723 / 6241) : ℂ) * ζ ^ 4 - ((1569 / 12482) : ℂ) * ζ ^ 5 + ((125 / 6241) : ℂ) * ζ ^ 6 + ((1633 / 6241) : ℂ) * ζ ^ 7 + ((4183 / 6241) : ℂ) * ζ ^ 8 - ((5487 / 6241) : ℂ) * ζ ^ 9 - ((1469 / 6241) : ℂ) * ζ ^ 10 - ((2829 / 6241) : ℂ) * ζ ^ 11 - ((1961 / 12482) : ℂ) * ζ ^ 12 + ((293 / 6241) : ℂ) * ζ ^ 13 - ((139 / 6241) : ℂ) * ζ ^ 14 - ((2645 / 12482) : ℂ) * ζ ^ 15 + ((191 / 6241) : ℂ) * ζ ^ 16 - ((3653 / 6241) : ℂ) * ζ ^ 17 - ((2886 / 6241) : ℂ) * ζ ^ 18 - ((3632 / 6241) : ℂ) * ζ ^ 19 + ((3885 / 6241) : ℂ) * ζ ^ 20 + ((2547 / 6241) : ℂ) * ζ ^ 21 - ((2357 / 12482) : ℂ) * ζ ^ 22 - ((3984 / 6241) : ℂ) * ζ ^ 23 - ((697 / 6241) : ℂ) * ζ ^ 24 + ((627 / 6241) : ℂ) * ζ ^ 25 + ((2849 / 6241) : ℂ) * ζ ^ 26 + ((718 / 6241) : ℂ) * ζ ^ 27 - ((916 / 6241) : ℂ) * ζ ^ 28 - ((8 / 79) : ℂ) * ζ ^ 29 + ((84 / 6241) : ℂ) * ζ ^ 30)

private theorem row18_reducedY55_combinationStep09
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY55_combinationStep09Coefficient00) * Y 0 0
      + (row18_reducedY55_combinationStep09Coefficient01) * Y 0 1
      + (row18_reducedY55_combinationStep09Coefficient02) * Y 1 0
      + (row18_reducedY55_combinationStep09Coefficient03) * Y 1 1
      + (row18_reducedY55_combinationStep09Coefficient04) * Y 2 2
      + (row18_reducedY55_combinationStep09Coefficient05) * Y 2 3
      + (row18_reducedY55_combinationStep09Coefficient06) * Y 3 2
      + (row18_reducedY55_combinationStep09Coefficient07) * Y 3 3
      + (row18_reducedY55_combinationStep09Coefficient08) * Y 4 4
      + (row18_reducedY55_combinationStep09Coefficient09) * Y 4 5
      + (row18_reducedY55_combinationStep09Coefficient10) * Y 5 4
      + (row18_reducedY55_combinationStep09Coefficient11) * Y 5 5
      + (row18_reducedY55_combinationStep09Coefficient12) * Y 6 6
      + (row18_reducedY55_combinationStep09Coefficient13) * Y 6 7
      + (row18_reducedY55_combinationStep09Coefficient14) * Y 7 6
      + (row18_reducedY55_combinationStep09Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY55_combinationStep08 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation17
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY55_combinationStep09CoefficientIdentity00,
      row18_reducedY55_combinationStep09CoefficientIdentity01,
      row18_reducedY55_combinationStep09CoefficientIdentity02,
      row18_reducedY55_combinationStep09CoefficientIdentity03,
      row18_reducedY55_combinationStep09CoefficientIdentity04,
      row18_reducedY55_combinationStep09CoefficientIdentity05,
      row18_reducedY55_combinationStep09CoefficientIdentity06,
      row18_reducedY55_combinationStep09CoefficientIdentity07,
      row18_reducedY55_combinationStep09CoefficientIdentity08,
      row18_reducedY55_combinationStep09CoefficientIdentity09,
      row18_reducedY55_combinationStep09CoefficientIdentity10,
      row18_reducedY55_combinationStep09CoefficientIdentity11,
      row18_reducedY55_combinationStep09CoefficientIdentity12,
      row18_reducedY55_combinationStep09CoefficientIdentity13,
      row18_reducedY55_combinationStep09CoefficientIdentity14,
      row18_reducedY55_combinationStep09CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY55_combinationStep09Multiplier * equation

private def row18_reducedY55_combinationStep10Multiplier : ℂ :=
  (((236 / 79) : ℂ) - ((4896 / 395) : ℂ) * ζ ^ 1 + ((6784 / 395) : ℂ) * ζ ^ 2 + ((4044 / 395) : ℂ) * ζ ^ 3 + ((1872 / 395) : ℂ) * ζ ^ 5 + ((6056 / 395) : ℂ) * ζ ^ 6 + ((1076 / 79) : ℂ) * ζ ^ 8 + ((8092 / 395) : ℂ) * ζ ^ 9 + ((4048 / 395) : ℂ) * ζ ^ 11 + ((1076 / 79) : ℂ) * ζ ^ 12 + ((4896 / 395) : ℂ) * ζ ^ 13 + ((2724 / 395) : ℂ) * ζ ^ 15 + ((4896 / 395) : ℂ) * ζ ^ 17 + ((728 / 395) : ℂ) * ζ ^ 18 + ((852 / 395) : ℂ) * ζ ^ 21 - ((6784 / 395) : ℂ) * ζ ^ 22 - ((6768 / 395) : ℂ) * ζ ^ 25 - ((852 / 395) : ℂ) * ζ ^ 27 - ((1076 / 79) : ℂ) * ζ ^ 28 - ((4896 / 395) : ℂ) * ζ ^ 29 + ((3028 / 395) : ℂ) * ζ ^ 30 - ((4048 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY55_combinationStep10Coefficient00 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep10CoefficientIdentity00 :
    row18_reducedY55_combinationStep10Coefficient00 =
      row18_reducedY55_combinationStep09Coefficient00 +
        row18_reducedY55_combinationStep10Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep10Coefficient00 row18_reducedY55_combinationStep09Coefficient00 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 (((37206 / 6241) : ℂ) - ((1467 / 395) : ℂ) * ζ ^ 1 + ((49954 / 6241) : ℂ) * ζ ^ 2 + ((127636 / 31205) : ℂ) * ζ ^ 3 - ((340087 / 31205) : ℂ) * ζ ^ 4 + ((188558 / 31205) : ℂ) * ζ ^ 5 + ((25275 / 6241) : ℂ) * ζ ^ 6 - ((195782 / 31205) : ℂ) * ζ ^ 7 + ((270787 / 31205) : ℂ) * ζ ^ 8 + ((88112 / 31205) : ℂ) * ζ ^ 9 - ((70453 / 6241) : ℂ) * ζ ^ 10 + ((188988 / 31205) : ℂ) * ζ ^ 11 - ((5893 / 31205) : ℂ) * ζ ^ 12 - ((179073 / 31205) : ℂ) * ζ ^ 13 + ((263928 / 31205) : ℂ) * ζ ^ 14 + ((5417 / 31205) : ℂ) * ζ ^ 15 - ((194609 / 31205) : ℂ) * ζ ^ 16 + ((31596 / 6241) : ℂ) * ζ ^ 17 - ((144171 / 31205) : ℂ) * ζ ^ 18 - ((135181 / 31205) : ℂ) * ζ ^ 19 + ((134352 / 31205) : ℂ) * ζ ^ 20 - ((107736 / 31205) : ℂ) * ζ ^ 21 - ((12905 / 6241) : ℂ) * ζ ^ 22 + ((55473 / 31205) : ℂ) * ζ ^ 23 - ((8348 / 6241) : ℂ) * ζ ^ 24 - ((7863 / 6241) : ℂ) * ζ ^ 25 + ((62437 / 31205) : ℂ) * ζ ^ 26 - ((5333 / 31205) : ℂ) * ζ ^ 27 + ((16156 / 31205) : ℂ) * ζ ^ 28 + ((5594 / 31205) : ℂ) * ζ ^ 29 + ((14168 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep10Coefficient01 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep10CoefficientIdentity01 :
    row18_reducedY55_combinationStep10Coefficient01 =
      row18_reducedY55_combinationStep09Coefficient01 +
        row18_reducedY55_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep10Coefficient01 row18_reducedY55_combinationStep09Coefficient01 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep10Coefficient02 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep10CoefficientIdentity02 :
    row18_reducedY55_combinationStep10Coefficient02 =
      row18_reducedY55_combinationStep09Coefficient02 +
        row18_reducedY55_combinationStep10Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep10Coefficient02 row18_reducedY55_combinationStep09Coefficient02 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 (((53333 / 31205) : ℂ) - ((12077 / 31205) : ℂ) * ζ ^ 1 - ((242883 / 31205) : ℂ) * ζ ^ 2 - ((45126 / 31205) : ℂ) * ζ ^ 3 + ((44622 / 31205) : ℂ) * ζ ^ 4 - ((86760 / 6241) : ℂ) * ζ ^ 5 + ((3531 / 6241) : ℂ) * ζ ^ 6 - ((131796 / 31205) : ℂ) * ζ ^ 7 - ((357132 / 31205) : ℂ) * ζ ^ 8 + ((41009 / 31205) : ℂ) * ζ ^ 9 - ((22517 / 31205) : ℂ) * ζ ^ 10 - ((206663 / 31205) : ℂ) * ζ ^ 11 - ((28561 / 31205) : ℂ) * ζ ^ 12 + ((51336 / 31205) : ℂ) * ζ ^ 13 - ((308319 / 31205) : ℂ) * ζ ^ 14 + ((80141 / 31205) : ℂ) * ζ ^ 15 - ((27979 / 31205) : ℂ) * ζ ^ 16 - ((87341 / 31205) : ℂ) * ζ ^ 17 + ((186304 / 31205) : ℂ) * ζ ^ 18 + ((55749 / 31205) : ℂ) * ζ ^ 19 - ((16463 / 31205) : ℂ) * ζ ^ 20 + ((168464 / 31205) : ℂ) * ζ ^ 21 - ((20988 / 31205) : ℂ) * ζ ^ 22 + ((22791 / 31205) : ℂ) * ζ ^ 23 + ((43510 / 6241) : ℂ) * ζ ^ 24 + ((86319 / 31205) : ℂ) * ζ ^ 25 + ((17105 / 6241) : ℂ) * ζ ^ 26 + ((201917 / 31205) : ℂ) * ζ ^ 27 + ((105948 / 31205) : ℂ) * ζ ^ 28 - ((15012 / 31205) : ℂ) * ζ ^ 29 + ((85008 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep10Coefficient03 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep10CoefficientIdentity03 :
    row18_reducedY55_combinationStep10Coefficient03 =
      row18_reducedY55_combinationStep09Coefficient03 +
        row18_reducedY55_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep10Coefficient03 row18_reducedY55_combinationStep09Coefficient03 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep10Coefficient04 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep10CoefficientIdentity04 :
    row18_reducedY55_combinationStep10Coefficient04 =
      row18_reducedY55_combinationStep09Coefficient04 +
        row18_reducedY55_combinationStep10Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep10Coefficient04 row18_reducedY55_combinationStep09Coefficient04 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 (-((37206 / 6241) : ℂ) + ((1467 / 395) : ℂ) * ζ ^ 1 - ((49954 / 6241) : ℂ) * ζ ^ 2 - ((127636 / 31205) : ℂ) * ζ ^ 3 + ((340087 / 31205) : ℂ) * ζ ^ 4 - ((188558 / 31205) : ℂ) * ζ ^ 5 - ((25275 / 6241) : ℂ) * ζ ^ 6 + ((195782 / 31205) : ℂ) * ζ ^ 7 - ((270787 / 31205) : ℂ) * ζ ^ 8 - ((88112 / 31205) : ℂ) * ζ ^ 9 + ((70453 / 6241) : ℂ) * ζ ^ 10 - ((188988 / 31205) : ℂ) * ζ ^ 11 + ((5893 / 31205) : ℂ) * ζ ^ 12 + ((179073 / 31205) : ℂ) * ζ ^ 13 - ((263928 / 31205) : ℂ) * ζ ^ 14 - ((5417 / 31205) : ℂ) * ζ ^ 15 + ((194609 / 31205) : ℂ) * ζ ^ 16 - ((31596 / 6241) : ℂ) * ζ ^ 17 + ((144171 / 31205) : ℂ) * ζ ^ 18 + ((135181 / 31205) : ℂ) * ζ ^ 19 - ((134352 / 31205) : ℂ) * ζ ^ 20 + ((107736 / 31205) : ℂ) * ζ ^ 21 + ((12905 / 6241) : ℂ) * ζ ^ 22 - ((55473 / 31205) : ℂ) * ζ ^ 23 + ((8348 / 6241) : ℂ) * ζ ^ 24 + ((7863 / 6241) : ℂ) * ζ ^ 25 - ((62437 / 31205) : ℂ) * ζ ^ 26 + ((5333 / 31205) : ℂ) * ζ ^ 27 - ((16156 / 31205) : ℂ) * ζ ^ 28 - ((5594 / 31205) : ℂ) * ζ ^ 29 - ((14168 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep10Coefficient05 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep10CoefficientIdentity05 :
    row18_reducedY55_combinationStep10Coefficient05 =
      row18_reducedY55_combinationStep09Coefficient05 +
        row18_reducedY55_combinationStep10Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY55_combinationStep10Coefficient05 row18_reducedY55_combinationStep09Coefficient05 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 (-((1538 / 6241) : ℂ) - ((55401 / 31205) : ℂ) * ζ ^ 1 - ((102574 / 31205) : ℂ) * ζ ^ 2 + ((50247 / 31205) : ℂ) * ζ ^ 3 - ((25772 / 31205) : ℂ) * ζ ^ 4 - ((147731 / 31205) : ℂ) * ζ ^ 5 - ((25532 / 31205) : ℂ) * ζ ^ 6 + ((193 / 31205) : ℂ) * ζ ^ 7 - ((53873 / 6241) : ℂ) * ζ ^ 8 + ((53397 / 31205) : ℂ) * ζ ^ 9 - ((149227 / 31205) : ℂ) * ζ ^ 10 - ((287734 / 31205) : ℂ) * ζ ^ 11 - ((144901 / 31205) : ℂ) * ζ ^ 12 + ((200677 / 31205) : ℂ) * ζ ^ 13 - ((22234 / 6241) : ℂ) * ζ ^ 14 + ((64747 / 31205) : ℂ) * ζ ^ 15 - ((15427 / 31205) : ℂ) * ζ ^ 16 - ((207339 / 31205) : ℂ) * ζ ^ 17 - ((4007 / 6241) : ℂ) * ζ ^ 18 + ((147057 / 31205) : ℂ) * ζ ^ 19 - ((17438 / 6241) : ℂ) * ζ ^ 20 + ((74483 / 31205) : ℂ) * ζ ^ 21 + ((54976 / 31205) : ℂ) * ζ ^ 22 - ((154553 / 31205) : ℂ) * ζ ^ 23 + ((119986 / 31205) : ℂ) * ζ ^ 24 - ((42493 / 31205) : ℂ) * ζ ^ 25 + ((95908 / 31205) : ℂ) * ζ ^ 26 + ((215634 / 31205) : ℂ) * ζ ^ 27 + ((2502 / 395) : ℂ) * ζ ^ 28 - ((81612 / 31205) : ℂ) * ζ ^ 29 + ((36432 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY55_combinationStep10Coefficient06 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep10CoefficientIdentity06 :
    row18_reducedY55_combinationStep10Coefficient06 =
      row18_reducedY55_combinationStep09Coefficient06 +
        row18_reducedY55_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep10Coefficient06 row18_reducedY55_combinationStep09Coefficient06 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep10Coefficient07 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep10CoefficientIdentity07 :
    row18_reducedY55_combinationStep10Coefficient07 =
      row18_reducedY55_combinationStep09Coefficient07 +
        row18_reducedY55_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep10Coefficient07 row18_reducedY55_combinationStep09Coefficient07 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep10Coefficient08 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep10CoefficientIdentity08 :
    row18_reducedY55_combinationStep10Coefficient08 =
      row18_reducedY55_combinationStep09Coefficient08 +
        row18_reducedY55_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep10Coefficient08 row18_reducedY55_combinationStep09Coefficient08 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep10Coefficient09 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep10CoefficientIdentity09 :
    row18_reducedY55_combinationStep10Coefficient09 =
      row18_reducedY55_combinationStep09Coefficient09 +
        row18_reducedY55_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep10Coefficient09 row18_reducedY55_combinationStep09Coefficient09 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep10Coefficient10 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep10CoefficientIdentity10 :
    row18_reducedY55_combinationStep10Coefficient10 =
      row18_reducedY55_combinationStep09Coefficient10 +
        row18_reducedY55_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep10Coefficient10 row18_reducedY55_combinationStep09Coefficient10 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep10Coefficient11 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY55_combinationStep10CoefficientIdentity11 :
    row18_reducedY55_combinationStep10Coefficient11 =
      row18_reducedY55_combinationStep09Coefficient11 +
        row18_reducedY55_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep10Coefficient11 row18_reducedY55_combinationStep09Coefficient11 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep10Coefficient12 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep10CoefficientIdentity12 :
    row18_reducedY55_combinationStep10Coefficient12 =
      row18_reducedY55_combinationStep09Coefficient12 +
        row18_reducedY55_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep10Coefficient12 row18_reducedY55_combinationStep09Coefficient12 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep10Coefficient13 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep10CoefficientIdentity13 :
    row18_reducedY55_combinationStep10Coefficient13 =
      row18_reducedY55_combinationStep09Coefficient13 +
        row18_reducedY55_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep10Coefficient13 row18_reducedY55_combinationStep09Coefficient13 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep10Coefficient14 : ℂ :=
  0

private theorem row18_reducedY55_combinationStep10CoefficientIdentity14 :
    row18_reducedY55_combinationStep10Coefficient14 =
      row18_reducedY55_combinationStep09Coefficient14 +
        row18_reducedY55_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep10Coefficient14 row18_reducedY55_combinationStep09Coefficient14 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY55_combinationStep10Coefficient15 : ℂ :=
  (-(1 : ℂ))

private theorem row18_reducedY55_combinationStep10CoefficientIdentity15 :
    row18_reducedY55_combinationStep10Coefficient15 =
      row18_reducedY55_combinationStep09Coefficient15 +
        row18_reducedY55_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY55_combinationStep10Coefficient15 row18_reducedY55_combinationStep09Coefficient15 row18_reducedY55_combinationStep10Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY55_combinationStep10
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY55_combinationStep10Coefficient00) * Y 0 0
      + (row18_reducedY55_combinationStep10Coefficient01) * Y 0 1
      + (row18_reducedY55_combinationStep10Coefficient02) * Y 1 0
      + (row18_reducedY55_combinationStep10Coefficient03) * Y 1 1
      + (row18_reducedY55_combinationStep10Coefficient04) * Y 2 2
      + (row18_reducedY55_combinationStep10Coefficient05) * Y 2 3
      + (row18_reducedY55_combinationStep10Coefficient06) * Y 3 2
      + (row18_reducedY55_combinationStep10Coefficient07) * Y 3 3
      + (row18_reducedY55_combinationStep10Coefficient08) * Y 4 4
      + (row18_reducedY55_combinationStep10Coefficient09) * Y 4 5
      + (row18_reducedY55_combinationStep10Coefficient10) * Y 5 4
      + (row18_reducedY55_combinationStep10Coefficient11) * Y 5 5
      + (row18_reducedY55_combinationStep10Coefficient12) * Y 6 6
      + (row18_reducedY55_combinationStep10Coefficient13) * Y 6 7
      + (row18_reducedY55_combinationStep10Coefficient14) * Y 7 6
      + (row18_reducedY55_combinationStep10Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY55_combinationStep09 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY55_combinationStep10CoefficientIdentity00,
      row18_reducedY55_combinationStep10CoefficientIdentity01,
      row18_reducedY55_combinationStep10CoefficientIdentity02,
      row18_reducedY55_combinationStep10CoefficientIdentity03,
      row18_reducedY55_combinationStep10CoefficientIdentity04,
      row18_reducedY55_combinationStep10CoefficientIdentity05,
      row18_reducedY55_combinationStep10CoefficientIdentity06,
      row18_reducedY55_combinationStep10CoefficientIdentity07,
      row18_reducedY55_combinationStep10CoefficientIdentity08,
      row18_reducedY55_combinationStep10CoefficientIdentity09,
      row18_reducedY55_combinationStep10CoefficientIdentity10,
      row18_reducedY55_combinationStep10CoefficientIdentity11,
      row18_reducedY55_combinationStep10CoefficientIdentity12,
      row18_reducedY55_combinationStep10CoefficientIdentity13,
      row18_reducedY55_combinationStep10CoefficientIdentity14,
      row18_reducedY55_combinationStep10CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY55_combinationStep10Multiplier * equation

theorem row18_reducedY55
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 5 5 = Y 7 7 := by
  have reduced :=
    row18_reducedY55_combinationStep10 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY55_combinationStep10Coefficient00,
      row18_reducedY55_combinationStep10Coefficient01,
      row18_reducedY55_combinationStep10Coefficient02,
      row18_reducedY55_combinationStep10Coefficient03,
      row18_reducedY55_combinationStep10Coefficient04,
      row18_reducedY55_combinationStep10Coefficient05,
      row18_reducedY55_combinationStep10Coefficient06,
      row18_reducedY55_combinationStep10Coefficient07,
      row18_reducedY55_combinationStep10Coefficient08,
      row18_reducedY55_combinationStep10Coefficient09,
      row18_reducedY55_combinationStep10Coefficient10,
      row18_reducedY55_combinationStep10Coefficient11,
      row18_reducedY55_combinationStep10Coefficient12,
      row18_reducedY55_combinationStep10Coefficient13,
      row18_reducedY55_combinationStep10Coefficient14,
      row18_reducedY55_combinationStep10Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
