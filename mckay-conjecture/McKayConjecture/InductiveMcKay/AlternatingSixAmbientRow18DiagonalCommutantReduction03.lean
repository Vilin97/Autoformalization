/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction02

/-!
# Ambient row 18 commutant reduction 03

This generated module checks the reduced relation `reducedY11` for
matrix coordinate (1, 1).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY11_combinationStep00Multiplier : ℂ :=
  (-((77336 / 1185) : ℂ) + ((22712 / 395) : ℂ) * ζ ^ 1 + ((238 / 3) : ℂ) * ζ ^ 2 - ((26912 / 395) : ℂ) * ζ ^ 3 + ((44536 / 395) : ℂ) * ζ ^ 5 + ((41346 / 395) : ℂ) * ζ ^ 8 - ((17732 / 1185) : ℂ) * ζ ^ 9 + ((98468 / 1185) : ℂ) * ζ ^ 11 + ((30634 / 1185) : ℂ) * ζ ^ 12 - ((22712 / 395) : ℂ) * ζ ^ 13 + ((5088 / 395) : ℂ) * ζ ^ 15 - ((22712 / 395) : ℂ) * ζ ^ 17 - ((238 / 3) : ℂ) * ζ ^ 18 - ((49624 / 395) : ℂ) * ζ ^ 21 - ((238 / 3) : ℂ) * ζ ^ 22 - ((154672 / 1185) : ℂ) * ζ ^ 24 - ((21824 / 395) : ℂ) * ζ ^ 25 - ((49624 / 395) : ℂ) * ζ ^ 27 - ((41346 / 395) : ℂ) * ζ ^ 28 + ((22712 / 395) : ℂ) * ζ ^ 29 - (48 : ℂ) * ζ ^ 30 - ((98468 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY11_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep00CoefficientIdentity00 :
    row18_reducedY11_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep00Coefficient00 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep00Coefficient01 : ℂ :=
  (((46150 / 18723) : ℂ) - ((50821 / 12482) : ℂ) * ζ ^ 1 - ((23843 / 12482) : ℂ) * ζ ^ 2 + ((38184 / 6241) : ℂ) * ζ ^ 3 - ((50821 / 12482) : ℂ) * ζ ^ 5 + ((20771 / 37446) : ℂ) * ζ ^ 6 - ((20771 / 37446) : ℂ) * ζ ^ 8 + ((50821 / 12482) : ℂ) * ζ ^ 9 - ((19092 / 6241) : ℂ) * ζ ^ 11 + ((38413 / 18723) : ℂ) * ζ ^ 12 + ((50821 / 12482) : ℂ) * ζ ^ 13 - ((34939 / 37446) : ℂ) * ζ ^ 15 + ((50821 / 12482) : ℂ) * ζ ^ 17 + ((58153 / 18723) : ℂ) * ζ ^ 18 + ((17661 / 6241) : ℂ) * ζ ^ 21 + ((23843 / 12482) : ℂ) * ζ ^ 22 + ((137077 / 37446) : ℂ) * ζ ^ 24 + ((194165 / 37446) : ℂ) * ζ ^ 27 + ((20771 / 37446) : ℂ) * ζ ^ 28 - ((50821 / 12482) : ℂ) * ζ ^ 29 + ((97597 / 37446) : ℂ) * ζ ^ 30 + ((19092 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep00CoefficientIdentity01 :
    row18_reducedY11_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep00Coefficient01 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 (-((1854806 / 93615) : ℂ) + ((218401 / 12482) : ℂ) * ζ ^ 1 + ((582257 / 37446) : ℂ) * ζ ^ 2 - ((174293 / 12482) : ℂ) * ζ ^ 3 + ((180484 / 6241) : ℂ) * ζ ^ 4 + ((703624 / 31205) : ℂ) * ζ ^ 5 - ((1711142 / 93615) : ℂ) * ζ ^ 6 + ((110946 / 31205) : ℂ) * ζ ^ 7 + ((2593051 / 187230) : ℂ) * ζ ^ 8 - ((336422 / 31205) : ℂ) * ζ ^ 9 - ((562379 / 31205) : ℂ) * ζ ^ 10 - ((3559603 / 187230) : ℂ) * ζ ^ 11 + ((2977921 / 187230) : ℂ) * ζ ^ 12 - ((208712 / 18723) : ℂ) * ζ ^ 13 - ((3187093 / 93615) : ℂ) * ζ ^ 14 - ((6753 / 31205) : ℂ) * ζ ^ 15 + ((117517 / 187230) : ℂ) * ζ ^ 16 - ((278956 / 31205) : ℂ) * ζ ^ 17 + ((130957 / 62410) : ℂ) * ζ ^ 18 - ((1289923 / 187230) : ℂ) * ζ ^ 19 - ((1488124 / 93615) : ℂ) * ζ ^ 20 - ((194027 / 187230) : ℂ) * ζ ^ 21 + ((1508173 / 187230) : ℂ) * ζ ^ 22 - ((349099 / 31205) : ℂ) * ζ ^ 23 - ((137395 / 6241) : ℂ) * ζ ^ 24 + ((23441 / 12482) : ℂ) * ζ ^ 25 + ((2950019 / 187230) : ℂ) * ζ ^ 26 + ((1455904 / 93615) : ℂ) * ζ ^ 27 - ((117587 / 6241) : ℂ) * ζ ^ 28 + ((100767 / 31205) : ℂ) * ζ ^ 29 + ((1673956 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep00Coefficient02 : ℂ :=
  (((117983 / 37446) : ℂ) - ((34669 / 37446) : ℂ) * ζ ^ 1 - ((138223 / 37446) : ℂ) * ζ ^ 2 + ((14780 / 6241) : ℂ) * ζ ^ 3 - ((55176 / 6241) : ℂ) * ζ ^ 5 - ((26123 / 37446) : ℂ) * ζ ^ 6 - ((207223 / 37446) : ℂ) * ζ ^ 8 - ((130859 / 37446) : ℂ) * ζ ^ 9 - ((305057 / 37446) : ℂ) * ζ ^ 11 - ((56050 / 18723) : ℂ) * ζ ^ 12 + ((34669 / 37446) : ℂ) * ζ ^ 13 - ((14780 / 6241) : ℂ) * ζ ^ 15 + ((34669 / 37446) : ℂ) * ζ ^ 17 + ((10120 / 18723) : ℂ) * ζ ^ 18 + ((296387 / 37446) : ℂ) * ζ ^ 21 + ((138223 / 37446) : ℂ) * ζ ^ 22 + ((138223 / 37446) : ℂ) * ζ ^ 24 + ((296387 / 37446) : ℂ) * ζ ^ 25 + ((305057 / 37446) : ℂ) * ζ ^ 27 + ((207223 / 37446) : ℂ) * ζ ^ 28 - ((34669 / 37446) : ℂ) * ζ ^ 29 + ((11500 / 6241) : ℂ) * ζ ^ 30 + ((305057 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep00CoefficientIdentity02 :
    row18_reducedY11_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep00Coefficient02 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 (-((3760691 / 187230) : ℂ) + ((2464237 / 187230) : ℂ) * ζ ^ 1 + ((3673697 / 187230) : ℂ) * ζ ^ 2 - ((1056167 / 187230) : ℂ) * ζ ^ 3 + ((267763 / 12482) : ℂ) * ζ ^ 4 + ((2168339 / 187230) : ℂ) * ζ ^ 5 - ((355191 / 31205) : ℂ) * ζ ^ 6 + ((3702251 / 187230) : ℂ) * ζ ^ 7 + ((675547 / 37446) : ℂ) * ζ ^ 8 - ((365191 / 62410) : ℂ) * ζ ^ 9 - ((1263803 / 187230) : ℂ) * ζ ^ 10 - ((131796 / 31205) : ℂ) * ζ ^ 11 - ((8149 / 18723) : ℂ) * ζ ^ 12 - ((394961 / 62410) : ℂ) * ζ ^ 13 - ((1278514 / 93615) : ℂ) * ζ ^ 14 + ((212909 / 93615) : ℂ) * ζ ^ 15 - ((363971 / 37446) : ℂ) * ζ ^ 16 - ((1279454 / 93615) : ℂ) * ζ ^ 17 - ((185608 / 18723) : ℂ) * ζ ^ 18 - ((972649 / 187230) : ℂ) * ζ ^ 19 - ((143273 / 93615) : ℂ) * ζ ^ 20 - ((1370323 / 187230) : ℂ) * ζ ^ 21 - ((63 / 62410) : ℂ) * ζ ^ 22 - ((70270 / 6241) : ℂ) * ζ ^ 23 - ((1335209 / 62410) : ℂ) * ζ ^ 24 + ((73277 / 12482) : ℂ) * ζ ^ 25 + ((7359 / 62410) : ℂ) * ζ ^ 26 - ((672509 / 37446) : ℂ) * ζ ^ 27 - ((191591 / 93615) : ℂ) * ζ ^ 28 + ((292653 / 31205) : ℂ) * ζ ^ 29 + ((24617 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep00CoefficientIdentity03 :
    row18_reducedY11_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep00Coefficient03 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep00CoefficientIdentity04 :
    row18_reducedY11_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep00Coefficient04 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep00CoefficientIdentity05 :
    row18_reducedY11_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep00Coefficient05 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep00CoefficientIdentity06 :
    row18_reducedY11_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep00Coefficient06 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep00CoefficientIdentity07 :
    row18_reducedY11_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep00Coefficient07 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep00CoefficientIdentity08 :
    row18_reducedY11_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep00Coefficient08 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep00CoefficientIdentity09 :
    row18_reducedY11_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep00Coefficient09 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep00CoefficientIdentity10 :
    row18_reducedY11_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep00Coefficient10 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep00CoefficientIdentity11 :
    row18_reducedY11_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep00Coefficient11 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep00CoefficientIdentity12 :
    row18_reducedY11_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep00Coefficient12 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep00CoefficientIdentity13 :
    row18_reducedY11_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep00Coefficient13 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep00CoefficientIdentity14 :
    row18_reducedY11_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep00Coefficient14 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep00CoefficientIdentity15 :
    row18_reducedY11_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY11_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep00Coefficient15 row18_reducedY11_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY11_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY11_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY11_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY11_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY11_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY11_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY11_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY11_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY11_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY11_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY11_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY11_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY11_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY11_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY11_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY11_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY11_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY11_combinationStep00CoefficientIdentity00,
      row18_reducedY11_combinationStep00CoefficientIdentity01,
      row18_reducedY11_combinationStep00CoefficientIdentity02,
      row18_reducedY11_combinationStep00CoefficientIdentity03,
      row18_reducedY11_combinationStep00CoefficientIdentity04,
      row18_reducedY11_combinationStep00CoefficientIdentity05,
      row18_reducedY11_combinationStep00CoefficientIdentity06,
      row18_reducedY11_combinationStep00CoefficientIdentity07,
      row18_reducedY11_combinationStep00CoefficientIdentity08,
      row18_reducedY11_combinationStep00CoefficientIdentity09,
      row18_reducedY11_combinationStep00CoefficientIdentity10,
      row18_reducedY11_combinationStep00CoefficientIdentity11,
      row18_reducedY11_combinationStep00CoefficientIdentity12,
      row18_reducedY11_combinationStep00CoefficientIdentity13,
      row18_reducedY11_combinationStep00CoefficientIdentity14,
      row18_reducedY11_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY11_combinationStep00Multiplier * equation

private def row18_reducedY11_combinationStep01Multiplier : ℂ :=
  (-((1176 / 395) : ℂ) - ((364 / 237) : ℂ) * ζ ^ 1 + ((6446 / 1185) : ℂ) * ζ ^ 2 + ((344 / 79) : ℂ) * ζ ^ 5 + ((9974 / 1185) : ℂ) * ζ ^ 6 + ((9974 / 1185) : ℂ) * ζ ^ 8 + ((344 / 79) : ℂ) * ζ ^ 9 + ((2546 / 237) : ℂ) * ζ ^ 11 + ((10132 / 1185) : ℂ) * ζ ^ 12 + ((364 / 237) : ℂ) * ζ ^ 13 + ((1312 / 237) : ℂ) * ζ ^ 15 + ((364 / 237) : ℂ) * ζ ^ 17 + ((204 / 395) : ℂ) * ζ ^ 18 - ((334 / 237) : ℂ) * ζ ^ 21 - ((6446 / 1185) : ℂ) * ζ ^ 22 - ((134 / 15) : ℂ) * ζ ^ 24 - ((1396 / 237) : ℂ) * ζ ^ 25 - ((1312 / 237) : ℂ) * ζ ^ 27 - ((9974 / 1185) : ℂ) * ζ ^ 28 - ((364 / 237) : ℂ) * ζ ^ 29 - ((2 / 15) : ℂ) * ζ ^ 30 - ((2546 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY11_combinationStep01Coefficient00 : ℂ :=
  (((14079 / 12482) : ℂ) + ((14009 / 18723) : ℂ) * ζ ^ 1 + ((11627 / 37446) : ℂ) * ζ ^ 2 - ((18731 / 12482) : ℂ) * ζ ^ 3 + ((20338 / 18723) : ℂ) * ζ ^ 5 + ((23869 / 18723) : ℂ) * ζ ^ 6 - ((22249 / 37446) : ℂ) * ζ ^ 8 - ((5505 / 12482) : ℂ) * ζ ^ 9 + ((6613 / 6241) : ℂ) * ζ ^ 11 - ((22249 / 37446) : ℂ) * ζ ^ 12 - ((14009 / 18723) : ℂ) * ζ ^ 13 + ((68851 / 37446) : ℂ) * ζ ^ 15 - ((14009 / 18723) : ℂ) * ζ ^ 17 - ((12037 / 12482) : ℂ) * ζ ^ 18 + ((28175 / 37446) : ℂ) * ζ ^ 21 - ((11627 / 37446) : ℂ) * ζ ^ 22 - ((6329 / 18723) : ℂ) * ζ ^ 25 - ((28175 / 37446) : ℂ) * ζ ^ 27 + ((22249 / 37446) : ℂ) * ζ ^ 28 + ((14009 / 18723) : ℂ) * ζ ^ 29 + ((23869 / 37446) : ℂ) * ζ ^ 30 - ((6613 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep01CoefficientIdentity00 :
    row18_reducedY11_combinationStep01Coefficient00 =
      row18_reducedY11_combinationStep00Coefficient00 +
        row18_reducedY11_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep01Coefficient00 row18_reducedY11_combinationStep00Coefficient00 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 (-((22179 / 62410) : ℂ) - ((21269 / 93615) : ℂ) * ζ ^ 1 - ((50123 / 37446) : ℂ) * ζ ^ 2 + ((7589 / 6241) : ℂ) * ζ ^ 3 - ((12977 / 37446) : ℂ) * ζ ^ 4 - ((9835 / 6241) : ℂ) * ζ ^ 5 - ((82229 / 37446) : ℂ) * ζ ^ 6 - ((370211 / 187230) : ℂ) * ζ ^ 7 - ((483499 / 187230) : ℂ) * ζ ^ 8 + ((17438 / 93615) : ℂ) * ζ ^ 9 + ((33731 / 18723) : ℂ) * ζ ^ 10 - ((81559 / 187230) : ℂ) * ζ ^ 11 + ((43 / 790) : ℂ) * ζ ^ 12 - ((229039 / 187230) : ℂ) * ζ ^ 13 - ((3889 / 6241) : ℂ) * ζ ^ 14 + ((42293 / 62410) : ℂ) * ζ ^ 15 + ((40627 / 93615) : ℂ) * ζ ^ 16 + ((340759 / 187230) : ℂ) * ζ ^ 17 + ((1118 / 6241) : ℂ) * ζ ^ 18 + ((74761 / 93615) : ℂ) * ζ ^ 19 + ((39257 / 93615) : ℂ) * ζ ^ 20 - ((31097 / 62410) : ℂ) * ζ ^ 21 - ((11515 / 37446) : ℂ) * ζ ^ 22 + ((2878 / 18723) : ℂ) * ζ ^ 23 + ((32393 / 18723) : ℂ) * ζ ^ 24 + ((103003 / 93615) : ℂ) * ζ ^ 25 + ((2375 / 18723) : ℂ) * ζ ^ 26 + ((96639 / 62410) : ℂ) * ζ ^ 27 + ((33481 / 93615) : ℂ) * ζ ^ 28 - ((5768 / 6241) : ℂ) * ζ ^ 29 - ((6365 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep01Coefficient01 : ℂ :=
  (((46153 / 12482) : ℂ) - ((125969 / 18723) : ℂ) * ζ ^ 1 - ((4787 / 6241) : ℂ) * ζ ^ 2 + ((139591 / 18723) : ℂ) * ζ ^ 3 - ((125969 / 18723) : ℂ) * ζ ^ 5 + ((36579 / 12482) : ℂ) * ζ ^ 6 - ((36579 / 12482) : ℂ) * ζ ^ 8 + ((125969 / 18723) : ℂ) * ζ ^ 9 - ((139591 / 37446) : ℂ) * ζ ^ 11 + ((84413 / 37446) : ℂ) * ζ ^ 12 + ((125969 / 18723) : ℂ) * ζ ^ 13 + ((7871 / 18723) : ℂ) * ζ ^ 15 + ((125969 / 18723) : ℂ) * ζ ^ 17 + ((36258 / 6241) : ℂ) * ζ ^ 18 + ((311707 / 37446) : ℂ) * ζ ^ 21 + ((4787 / 6241) : ℂ) * ζ ^ 22 + ((109095 / 12482) : ℂ) * ζ ^ 24 + ((49154 / 6241) : ℂ) * ζ ^ 27 + ((36579 / 12482) : ℂ) * ζ ^ 28 - ((125969 / 18723) : ℂ) * ζ ^ 29 + ((97075 / 18723) : ℂ) * ζ ^ 30 + ((139591 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep01CoefficientIdentity01 :
    row18_reducedY11_combinationStep01Coefficient01 =
      row18_reducedY11_combinationStep00Coefficient01 +
        row18_reducedY11_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep01Coefficient01 row18_reducedY11_combinationStep00Coefficient01 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 (-((174347 / 187230) : ℂ) + ((565303 / 187230) : ℂ) * ζ ^ 1 - ((2563 / 187230) : ℂ) * ζ ^ 2 - ((6171 / 31205) : ℂ) * ζ ^ 3 - ((49274 / 31205) : ℂ) * ζ ^ 4 - ((91849 / 37446) : ℂ) * ζ ^ 5 - ((693191 / 187230) : ℂ) * ζ ^ 6 - ((190537 / 93615) : ℂ) * ζ ^ 7 - ((466607 / 187230) : ℂ) * ζ ^ 8 - ((797041 / 187230) : ℂ) * ζ ^ 9 - ((76706 / 93615) : ℂ) * ζ ^ 10 + ((22857 / 62410) : ℂ) * ζ ^ 11 - ((61513 / 37446) : ℂ) * ζ ^ 12 - ((147232 / 93615) : ℂ) * ζ ^ 13 - ((310684 / 93615) : ℂ) * ζ ^ 14 - ((29185 / 12482) : ℂ) * ζ ^ 15 - ((14502 / 31205) : ℂ) * ζ ^ 16 + ((67457 / 187230) : ℂ) * ζ ^ 17 - ((277306 / 93615) : ℂ) * ζ ^ 18 - ((173633 / 187230) : ℂ) * ζ ^ 19 + ((106019 / 31205) : ℂ) * ζ ^ 20 - ((419243 / 93615) : ℂ) * ζ ^ 21 - ((141761 / 187230) : ℂ) * ζ ^ 22 + ((37811 / 12482) : ℂ) * ζ ^ 23 + ((35176 / 18723) : ℂ) * ζ ^ 24 + ((201073 / 187230) : ℂ) * ζ ^ 25 + ((21667 / 12482) : ℂ) * ζ ^ 26 - ((13893 / 31205) : ℂ) * ζ ^ 27 + ((713 / 1185) : ℂ) * ζ ^ 28 - ((77486 / 93615) : ℂ) * ζ ^ 29 - ((17822 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep01Coefficient02 : ℂ :=
  (((117983 / 37446) : ℂ) - ((34669 / 37446) : ℂ) * ζ ^ 1 - ((138223 / 37446) : ℂ) * ζ ^ 2 + ((14780 / 6241) : ℂ) * ζ ^ 3 - ((55176 / 6241) : ℂ) * ζ ^ 5 - ((26123 / 37446) : ℂ) * ζ ^ 6 - ((207223 / 37446) : ℂ) * ζ ^ 8 - ((130859 / 37446) : ℂ) * ζ ^ 9 - ((305057 / 37446) : ℂ) * ζ ^ 11 - ((56050 / 18723) : ℂ) * ζ ^ 12 + ((34669 / 37446) : ℂ) * ζ ^ 13 - ((14780 / 6241) : ℂ) * ζ ^ 15 + ((34669 / 37446) : ℂ) * ζ ^ 17 + ((10120 / 18723) : ℂ) * ζ ^ 18 + ((296387 / 37446) : ℂ) * ζ ^ 21 + ((138223 / 37446) : ℂ) * ζ ^ 22 + ((138223 / 37446) : ℂ) * ζ ^ 24 + ((296387 / 37446) : ℂ) * ζ ^ 25 + ((305057 / 37446) : ℂ) * ζ ^ 27 + ((207223 / 37446) : ℂ) * ζ ^ 28 - ((34669 / 37446) : ℂ) * ζ ^ 29 + ((11500 / 6241) : ℂ) * ζ ^ 30 + ((305057 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep01CoefficientIdentity02 :
    row18_reducedY11_combinationStep01Coefficient02 =
      row18_reducedY11_combinationStep00Coefficient02 +
        row18_reducedY11_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep01Coefficient02 row18_reducedY11_combinationStep00Coefficient02 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep01Coefficient03 : ℂ :=
  (-((14079 / 12482) : ℂ) - ((14009 / 18723) : ℂ) * ζ ^ 1 - ((11627 / 37446) : ℂ) * ζ ^ 2 + ((18731 / 12482) : ℂ) * ζ ^ 3 - ((20338 / 18723) : ℂ) * ζ ^ 5 - ((23869 / 18723) : ℂ) * ζ ^ 6 + ((22249 / 37446) : ℂ) * ζ ^ 8 + ((5505 / 12482) : ℂ) * ζ ^ 9 - ((6613 / 6241) : ℂ) * ζ ^ 11 + ((22249 / 37446) : ℂ) * ζ ^ 12 + ((14009 / 18723) : ℂ) * ζ ^ 13 - ((68851 / 37446) : ℂ) * ζ ^ 15 + ((14009 / 18723) : ℂ) * ζ ^ 17 + ((12037 / 12482) : ℂ) * ζ ^ 18 - ((28175 / 37446) : ℂ) * ζ ^ 21 + ((11627 / 37446) : ℂ) * ζ ^ 22 + ((6329 / 18723) : ℂ) * ζ ^ 25 + ((28175 / 37446) : ℂ) * ζ ^ 27 - ((22249 / 37446) : ℂ) * ζ ^ 28 - ((14009 / 18723) : ℂ) * ζ ^ 29 - ((23869 / 37446) : ℂ) * ζ ^ 30 + ((6613 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep01CoefficientIdentity03 :
    row18_reducedY11_combinationStep01Coefficient03 =
      row18_reducedY11_combinationStep00Coefficient03 +
        row18_reducedY11_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep01Coefficient03 row18_reducedY11_combinationStep00Coefficient03 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 (((22179 / 62410) : ℂ) + ((21269 / 93615) : ℂ) * ζ ^ 1 + ((50123 / 37446) : ℂ) * ζ ^ 2 - ((7589 / 6241) : ℂ) * ζ ^ 3 + ((12977 / 37446) : ℂ) * ζ ^ 4 + ((9835 / 6241) : ℂ) * ζ ^ 5 + ((82229 / 37446) : ℂ) * ζ ^ 6 + ((370211 / 187230) : ℂ) * ζ ^ 7 + ((483499 / 187230) : ℂ) * ζ ^ 8 - ((17438 / 93615) : ℂ) * ζ ^ 9 - ((33731 / 18723) : ℂ) * ζ ^ 10 + ((81559 / 187230) : ℂ) * ζ ^ 11 - ((43 / 790) : ℂ) * ζ ^ 12 + ((229039 / 187230) : ℂ) * ζ ^ 13 + ((3889 / 6241) : ℂ) * ζ ^ 14 - ((42293 / 62410) : ℂ) * ζ ^ 15 - ((40627 / 93615) : ℂ) * ζ ^ 16 - ((340759 / 187230) : ℂ) * ζ ^ 17 - ((1118 / 6241) : ℂ) * ζ ^ 18 - ((74761 / 93615) : ℂ) * ζ ^ 19 - ((39257 / 93615) : ℂ) * ζ ^ 20 + ((31097 / 62410) : ℂ) * ζ ^ 21 + ((11515 / 37446) : ℂ) * ζ ^ 22 - ((2878 / 18723) : ℂ) * ζ ^ 23 - ((32393 / 18723) : ℂ) * ζ ^ 24 - ((103003 / 93615) : ℂ) * ζ ^ 25 - ((2375 / 18723) : ℂ) * ζ ^ 26 - ((96639 / 62410) : ℂ) * ζ ^ 27 - ((33481 / 93615) : ℂ) * ζ ^ 28 + ((5768 / 6241) : ℂ) * ζ ^ 29 + ((6365 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep01CoefficientIdentity04 :
    row18_reducedY11_combinationStep01Coefficient04 =
      row18_reducedY11_combinationStep00Coefficient04 +
        row18_reducedY11_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep01Coefficient04 row18_reducedY11_combinationStep00Coefficient04 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep01CoefficientIdentity05 :
    row18_reducedY11_combinationStep01Coefficient05 =
      row18_reducedY11_combinationStep00Coefficient05 +
        row18_reducedY11_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep01Coefficient05 row18_reducedY11_combinationStep00Coefficient05 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep01CoefficientIdentity06 :
    row18_reducedY11_combinationStep01Coefficient06 =
      row18_reducedY11_combinationStep00Coefficient06 +
        row18_reducedY11_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep01Coefficient06 row18_reducedY11_combinationStep00Coefficient06 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep01CoefficientIdentity07 :
    row18_reducedY11_combinationStep01Coefficient07 =
      row18_reducedY11_combinationStep00Coefficient07 +
        row18_reducedY11_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep01Coefficient07 row18_reducedY11_combinationStep00Coefficient07 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep01CoefficientIdentity08 :
    row18_reducedY11_combinationStep01Coefficient08 =
      row18_reducedY11_combinationStep00Coefficient08 +
        row18_reducedY11_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep01Coefficient08 row18_reducedY11_combinationStep00Coefficient08 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep01CoefficientIdentity09 :
    row18_reducedY11_combinationStep01Coefficient09 =
      row18_reducedY11_combinationStep00Coefficient09 +
        row18_reducedY11_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep01Coefficient09 row18_reducedY11_combinationStep00Coefficient09 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep01CoefficientIdentity10 :
    row18_reducedY11_combinationStep01Coefficient10 =
      row18_reducedY11_combinationStep00Coefficient10 +
        row18_reducedY11_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep01Coefficient10 row18_reducedY11_combinationStep00Coefficient10 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep01CoefficientIdentity11 :
    row18_reducedY11_combinationStep01Coefficient11 =
      row18_reducedY11_combinationStep00Coefficient11 +
        row18_reducedY11_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep01Coefficient11 row18_reducedY11_combinationStep00Coefficient11 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep01CoefficientIdentity12 :
    row18_reducedY11_combinationStep01Coefficient12 =
      row18_reducedY11_combinationStep00Coefficient12 +
        row18_reducedY11_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep01Coefficient12 row18_reducedY11_combinationStep00Coefficient12 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep01CoefficientIdentity13 :
    row18_reducedY11_combinationStep01Coefficient13 =
      row18_reducedY11_combinationStep00Coefficient13 +
        row18_reducedY11_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep01Coefficient13 row18_reducedY11_combinationStep00Coefficient13 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep01CoefficientIdentity14 :
    row18_reducedY11_combinationStep01Coefficient14 =
      row18_reducedY11_combinationStep00Coefficient14 +
        row18_reducedY11_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep01Coefficient14 row18_reducedY11_combinationStep00Coefficient14 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep01CoefficientIdentity15 :
    row18_reducedY11_combinationStep01Coefficient15 =
      row18_reducedY11_combinationStep00Coefficient15 +
        row18_reducedY11_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep01Coefficient15 row18_reducedY11_combinationStep00Coefficient15 row18_reducedY11_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY11_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY11_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY11_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY11_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY11_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY11_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY11_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY11_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY11_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY11_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY11_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY11_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY11_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY11_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY11_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY11_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY11_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY11_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY11_combinationStep01CoefficientIdentity00,
      row18_reducedY11_combinationStep01CoefficientIdentity01,
      row18_reducedY11_combinationStep01CoefficientIdentity02,
      row18_reducedY11_combinationStep01CoefficientIdentity03,
      row18_reducedY11_combinationStep01CoefficientIdentity04,
      row18_reducedY11_combinationStep01CoefficientIdentity05,
      row18_reducedY11_combinationStep01CoefficientIdentity06,
      row18_reducedY11_combinationStep01CoefficientIdentity07,
      row18_reducedY11_combinationStep01CoefficientIdentity08,
      row18_reducedY11_combinationStep01CoefficientIdentity09,
      row18_reducedY11_combinationStep01CoefficientIdentity10,
      row18_reducedY11_combinationStep01CoefficientIdentity11,
      row18_reducedY11_combinationStep01CoefficientIdentity12,
      row18_reducedY11_combinationStep01CoefficientIdentity13,
      row18_reducedY11_combinationStep01CoefficientIdentity14,
      row18_reducedY11_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY11_combinationStep01Multiplier * equation

private def row18_reducedY11_combinationStep02Multiplier : ℂ :=
  (-((212902 / 18723) : ℂ) + ((25628 / 6241) : ℂ) * ζ ^ 1 - ((390618 / 31205) : ℂ) * ζ ^ 2 - ((18506 / 18723) : ℂ) * ζ ^ 3 - ((175348 / 18723) : ℂ) * ζ ^ 5 - ((630012 / 31205) : ℂ) * ζ ^ 6 - ((41050 / 6241) : ℂ) * ζ ^ 8 - ((262178 / 18723) : ℂ) * ζ ^ 9 - ((81224 / 6241) : ℂ) * ζ ^ 11 - ((41050 / 6241) : ℂ) * ζ ^ 12 - ((25628 / 6241) : ℂ) * ζ ^ 13 - ((233726 / 18723) : ℂ) * ζ ^ 15 - ((25628 / 6241) : ℂ) * ζ ^ 17 + ((239394 / 31205) : ℂ) * ζ ^ 18 - ((58378 / 18723) : ℂ) * ζ ^ 21 + ((390618 / 31205) : ℂ) * ζ ^ 22 + ((252232 / 18723) : ℂ) * ζ ^ 25 + ((58378 / 18723) : ℂ) * ζ ^ 27 + ((41050 / 6241) : ℂ) * ζ ^ 28 + ((25628 / 6241) : ℂ) * ζ ^ 29 - ((315006 / 31205) : ℂ) * ζ ^ 30 + ((81224 / 6241) : ℂ) * ζ ^ 31)

private def row18_reducedY11_combinationStep02Coefficient00 : ℂ :=
  (((47102 / 18723) : ℂ) - ((202757 / 93615) : ℂ) * ζ ^ 1 + ((1103461 / 187230) : ℂ) * ζ ^ 2 + ((37757 / 62410) : ℂ) * ζ ^ 3 + ((247831 / 62410) : ℂ) * ζ ^ 5 + ((229494 / 31205) : ℂ) * ζ ^ 6 + ((149047 / 37446) : ℂ) * ζ ^ 8 + ((1194043 / 187230) : ℂ) * ζ ^ 9 + ((540386 / 93615) : ℂ) * ζ ^ 11 + ((149047 / 37446) : ℂ) * ζ ^ 12 + ((202757 / 93615) : ℂ) * ζ ^ 13 + ((517868 / 93615) : ℂ) * ζ ^ 15 + ((202757 / 93615) : ℂ) * ζ ^ 17 - ((273503 / 187230) : ℂ) * ζ ^ 18 + ((292243 / 187230) : ℂ) * ζ ^ 21 - ((1103461 / 187230) : ℂ) * ζ ^ 22 - ((1149007 / 187230) : ℂ) * ζ ^ 25 - ((292243 / 187230) : ℂ) * ζ ^ 27 - ((149047 / 37446) : ℂ) * ζ ^ 28 - ((202757 / 93615) : ℂ) * ζ ^ 29 + ((114747 / 31205) : ℂ) * ζ ^ 30 - ((540386 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep02CoefficientIdentity00 :
    row18_reducedY11_combinationStep02Coefficient00 =
      row18_reducedY11_combinationStep01Coefficient00 +
        row18_reducedY11_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep02Coefficient00 row18_reducedY11_combinationStep01Coefficient00 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 (-((2827981 / 2958234) : ℂ) + ((34941391 / 14791170) : ℂ) * ζ ^ 1 - ((5638729 / 2958234) : ℂ) * ζ ^ 2 - ((54437021 / 14791170) : ℂ) * ζ ^ 3 + ((12763841 / 2958234) : ℂ) * ζ ^ 4 - ((9912727 / 2465195) : ℂ) * ζ ^ 5 - ((8384843 / 2958234) : ℂ) * ζ ^ 6 + ((14380861 / 2465195) : ℂ) * ζ ^ 7 - ((47337061 / 14791170) : ℂ) * ζ ^ 8 - ((8064297 / 4930390) : ℂ) * ζ ^ 9 + ((4639876 / 1479117) : ℂ) * ζ ^ 10 - ((24369754 / 7395585) : ℂ) * ζ ^ 11 - ((29306243 / 14791170) : ℂ) * ζ ^ 12 + ((78023569 / 14791170) : ℂ) * ζ ^ 13 - ((2641316 / 493039) : ℂ) * ζ ^ 14 + ((2763651 / 2465195) : ℂ) * ζ ^ 15 + ((12244638 / 2465195) : ℂ) * ζ ^ 16 - ((6509888 / 1479117) : ℂ) * ζ ^ 17 + ((1970929 / 986078) : ℂ) * ζ ^ 18 + ((6269405 / 2958234) : ℂ) * ζ ^ 19 - ((50404733 / 14791170) : ℂ) * ζ ^ 20 + ((21302842 / 7395585) : ℂ) * ζ ^ 21 - ((56021 / 1479117) : ℂ) * ζ ^ 22 - ((28747 / 4930390) : ℂ) * ζ ^ 23 + ((1739978 / 7395585) : ℂ) * ζ ^ 24 + ((2271772 / 7395585) : ℂ) * ζ ^ 25 + ((3032035 / 2958234) : ℂ) * ζ ^ 26 - ((8428003 / 4930390) : ℂ) * ζ ^ 27 + ((2825344 / 2465195) : ℂ) * ζ ^ 28 - ((34519 / 31205) : ℂ) * ζ ^ 29 + ((284284 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep02Coefficient01 : ℂ :=
  (-((159331 / 12482) : ℂ) + ((331967 / 37446) : ℂ) * ζ ^ 1 + ((127609 / 37446) : ℂ) * ζ ^ 2 - ((54622 / 6241) : ℂ) * ζ ^ 3 + ((331967 / 37446) : ℂ) * ζ ^ 5 - ((175192 / 18723) : ℂ) * ζ ^ 6 + ((175192 / 18723) : ℂ) * ζ ^ 8 - ((331967 / 37446) : ℂ) * ζ ^ 9 + ((27311 / 6241) : ℂ) * ζ ^ 11 - ((14521 / 37446) : ℂ) * ζ ^ 12 - ((331967 / 37446) : ℂ) * ζ ^ 13 - ((184571 / 37446) : ℂ) * ζ ^ 15 - ((331967 / 37446) : ℂ) * ζ ^ 17 - ((106582 / 18723) : ℂ) * ζ ^ 18 - ((320638 / 18723) : ℂ) * ζ ^ 21 - ((127609 / 37446) : ℂ) * ζ ^ 22 - ((281774 / 18723) : ℂ) * ζ ^ 24 - ((512303 / 37446) : ℂ) * ζ ^ 27 - ((175192 / 18723) : ℂ) * ζ ^ 28 + ((331967 / 37446) : ℂ) * ζ ^ 29 - ((121635 / 12482) : ℂ) * ζ ^ 30 - ((27311 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep02CoefficientIdentity01 :
    row18_reducedY11_combinationStep02Coefficient01 =
      row18_reducedY11_combinationStep01Coefficient01 +
        row18_reducedY11_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep02Coefficient01 row18_reducedY11_combinationStep01Coefficient01 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 (((13784863 / 986078) : ℂ) - ((17213831 / 1479117) : ℂ) * ζ ^ 1 - ((123307853 / 14791170) : ℂ) * ζ ^ 2 + ((27423380 / 1479117) : ℂ) * ζ ^ 3 - ((203116303 / 14791170) : ℂ) * ζ ^ 4 - ((19720169 / 4930390) : ℂ) * ζ ^ 5 + ((36342371 / 2465195) : ℂ) * ζ ^ 6 - ((26611285 / 2958234) : ℂ) * ζ ^ 7 - ((667718 / 493039) : ℂ) * ζ ^ 8 + ((182333459 / 14791170) : ℂ) * ζ ^ 9 - ((2193689 / 493039) : ℂ) * ζ ^ 10 - ((7177681 / 2958234) : ℂ) * ζ ^ 11 + ((70670077 / 4930390) : ℂ) * ζ ^ 12 - ((49140229 / 7395585) : ℂ) * ζ ^ 13 + ((249248 / 93615) : ℂ) * ζ ^ 14 + ((16862938 / 1479117) : ℂ) * ζ ^ 15 - ((29861073 / 4930390) : ℂ) * ζ ^ 16 + ((35411293 / 7395585) : ℂ) * ζ ^ 17 + ((16879729 / 1479117) : ℂ) * ζ ^ 18 - ((14542831 / 1479117) : ℂ) * ζ ^ 19 + ((44594159 / 7395585) : ℂ) * ζ ^ 20 + ((36007267 / 4930390) : ℂ) * ζ ^ 21 - ((11823899 / 2465195) : ℂ) * ζ ^ 22 + ((610981 / 493039) : ℂ) * ζ ^ 23 + ((32047067 / 4930390) : ℂ) * ζ ^ 24 - ((1127638 / 493039) : ℂ) * ζ ^ 25 - ((37716917 / 14791170) : ℂ) * ζ ^ 26 + ((3402034 / 493039) : ℂ) * ζ ^ 27 - ((12466176 / 2465195) : ℂ) * ζ ^ 28 + ((8917701 / 4930390) : ℂ) * ζ ^ 29 + ((263978 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep02Coefficient02 : ℂ :=
  (((117983 / 37446) : ℂ) - ((34669 / 37446) : ℂ) * ζ ^ 1 - ((138223 / 37446) : ℂ) * ζ ^ 2 + ((14780 / 6241) : ℂ) * ζ ^ 3 - ((55176 / 6241) : ℂ) * ζ ^ 5 - ((26123 / 37446) : ℂ) * ζ ^ 6 - ((207223 / 37446) : ℂ) * ζ ^ 8 - ((130859 / 37446) : ℂ) * ζ ^ 9 - ((305057 / 37446) : ℂ) * ζ ^ 11 - ((56050 / 18723) : ℂ) * ζ ^ 12 + ((34669 / 37446) : ℂ) * ζ ^ 13 - ((14780 / 6241) : ℂ) * ζ ^ 15 + ((34669 / 37446) : ℂ) * ζ ^ 17 + ((10120 / 18723) : ℂ) * ζ ^ 18 + ((296387 / 37446) : ℂ) * ζ ^ 21 + ((138223 / 37446) : ℂ) * ζ ^ 22 + ((138223 / 37446) : ℂ) * ζ ^ 24 + ((296387 / 37446) : ℂ) * ζ ^ 25 + ((305057 / 37446) : ℂ) * ζ ^ 27 + ((207223 / 37446) : ℂ) * ζ ^ 28 - ((34669 / 37446) : ℂ) * ζ ^ 29 + ((11500 / 6241) : ℂ) * ζ ^ 30 + ((305057 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep02CoefficientIdentity02 :
    row18_reducedY11_combinationStep02Coefficient02 =
      row18_reducedY11_combinationStep01Coefficient02 +
        row18_reducedY11_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep02Coefficient02 row18_reducedY11_combinationStep01Coefficient02 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep02Coefficient03 : ℂ :=
  (-((14079 / 12482) : ℂ) - ((14009 / 18723) : ℂ) * ζ ^ 1 - ((11627 / 37446) : ℂ) * ζ ^ 2 + ((18731 / 12482) : ℂ) * ζ ^ 3 - ((20338 / 18723) : ℂ) * ζ ^ 5 - ((23869 / 18723) : ℂ) * ζ ^ 6 + ((22249 / 37446) : ℂ) * ζ ^ 8 + ((5505 / 12482) : ℂ) * ζ ^ 9 - ((6613 / 6241) : ℂ) * ζ ^ 11 + ((22249 / 37446) : ℂ) * ζ ^ 12 + ((14009 / 18723) : ℂ) * ζ ^ 13 - ((68851 / 37446) : ℂ) * ζ ^ 15 + ((14009 / 18723) : ℂ) * ζ ^ 17 + ((12037 / 12482) : ℂ) * ζ ^ 18 - ((28175 / 37446) : ℂ) * ζ ^ 21 + ((11627 / 37446) : ℂ) * ζ ^ 22 + ((6329 / 18723) : ℂ) * ζ ^ 25 + ((28175 / 37446) : ℂ) * ζ ^ 27 - ((22249 / 37446) : ℂ) * ζ ^ 28 - ((14009 / 18723) : ℂ) * ζ ^ 29 - ((23869 / 37446) : ℂ) * ζ ^ 30 + ((6613 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep02CoefficientIdentity03 :
    row18_reducedY11_combinationStep02Coefficient03 =
      row18_reducedY11_combinationStep01Coefficient03 +
        row18_reducedY11_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep02Coefficient03 row18_reducedY11_combinationStep01Coefficient03 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep02Coefficient04 : ℂ :=
  (-((51967 / 37446) : ℂ) + ((90934 / 31205) : ℂ) * ζ ^ 1 - ((174221 / 31205) : ℂ) * ζ ^ 2 - ((65706 / 31205) : ℂ) * ζ ^ 3 - ((540113 / 187230) : ℂ) * ζ ^ 5 - ((569137 / 93615) : ℂ) * ζ ^ 6 - ((85648 / 18723) : ℂ) * ζ ^ 8 - ((638309 / 93615) : ℂ) * ζ ^ 9 - ((441191 / 93615) : ℂ) * ζ ^ 11 - ((85648 / 18723) : ℂ) * ζ ^ 12 - ((90934 / 31205) : ℂ) * ζ ^ 13 - ((691481 / 187230) : ℂ) * ζ ^ 15 - ((90934 / 31205) : ℂ) * ζ ^ 17 + ((46474 / 93615) : ℂ) * ζ ^ 18 - ((25228 / 31205) : ℂ) * ζ ^ 21 + ((174221 / 31205) : ℂ) * ζ ^ 22 + ((1085717 / 187230) : ℂ) * ζ ^ 25 + ((25228 / 31205) : ℂ) * ζ ^ 27 + ((85648 / 18723) : ℂ) * ζ ^ 28 + ((90934 / 31205) : ℂ) * ζ ^ 29 - ((569137 / 187230) : ℂ) * ζ ^ 30 + ((441191 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep02CoefficientIdentity04 :
    row18_reducedY11_combinationStep02Coefficient04 =
      row18_reducedY11_combinationStep01Coefficient04 +
        row18_reducedY11_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep02Coefficient04 row18_reducedY11_combinationStep01Coefficient04 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 (((2827981 / 2958234) : ℂ) - ((34941391 / 14791170) : ℂ) * ζ ^ 1 + ((5638729 / 2958234) : ℂ) * ζ ^ 2 + ((54437021 / 14791170) : ℂ) * ζ ^ 3 - ((12763841 / 2958234) : ℂ) * ζ ^ 4 + ((9912727 / 2465195) : ℂ) * ζ ^ 5 + ((8384843 / 2958234) : ℂ) * ζ ^ 6 - ((14380861 / 2465195) : ℂ) * ζ ^ 7 + ((47337061 / 14791170) : ℂ) * ζ ^ 8 + ((8064297 / 4930390) : ℂ) * ζ ^ 9 - ((4639876 / 1479117) : ℂ) * ζ ^ 10 + ((24369754 / 7395585) : ℂ) * ζ ^ 11 + ((29306243 / 14791170) : ℂ) * ζ ^ 12 - ((78023569 / 14791170) : ℂ) * ζ ^ 13 + ((2641316 / 493039) : ℂ) * ζ ^ 14 - ((2763651 / 2465195) : ℂ) * ζ ^ 15 - ((12244638 / 2465195) : ℂ) * ζ ^ 16 + ((6509888 / 1479117) : ℂ) * ζ ^ 17 - ((1970929 / 986078) : ℂ) * ζ ^ 18 - ((6269405 / 2958234) : ℂ) * ζ ^ 19 + ((50404733 / 14791170) : ℂ) * ζ ^ 20 - ((21302842 / 7395585) : ℂ) * ζ ^ 21 + ((56021 / 1479117) : ℂ) * ζ ^ 22 + ((28747 / 4930390) : ℂ) * ζ ^ 23 - ((1739978 / 7395585) : ℂ) * ζ ^ 24 - ((2271772 / 7395585) : ℂ) * ζ ^ 25 - ((3032035 / 2958234) : ℂ) * ζ ^ 26 + ((8428003 / 4930390) : ℂ) * ζ ^ 27 - ((2825344 / 2465195) : ℂ) * ζ ^ 28 + ((34519 / 31205) : ℂ) * ζ ^ 29 - ((284284 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep02CoefficientIdentity05 :
    row18_reducedY11_combinationStep02Coefficient05 =
      row18_reducedY11_combinationStep01Coefficient05 +
        row18_reducedY11_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep02Coefficient05 row18_reducedY11_combinationStep01Coefficient05 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep02Coefficient06 : ℂ :=
  (-((27593 / 18723) : ℂ) - ((29299 / 18723) : ℂ) * ζ ^ 1 - ((61685 / 18723) : ℂ) * ζ ^ 2 - ((214474 / 93615) : ℂ) * ζ ^ 3 - ((3933 / 6241) : ℂ) * ζ ^ 6 - ((26044 / 18723) : ℂ) * ζ ^ 8 - ((20245 / 6241) : ℂ) * ζ ^ 9 + ((165587 / 93615) : ℂ) * ζ ^ 11 + ((49886 / 18723) : ℂ) * ζ ^ 12 + ((29299 / 18723) : ℂ) * ζ ^ 13 - ((214474 / 93615) : ℂ) * ζ ^ 15 + ((29299 / 18723) : ℂ) * ζ ^ 17 + ((11364 / 6241) : ℂ) * ζ ^ 18 + ((29299 / 18723) : ℂ) * ζ ^ 21 + ((61685 / 18723) : ℂ) * ζ ^ 22 - ((61685 / 18723) : ℂ) * ζ ^ 24 - ((29299 / 18723) : ℂ) * ζ ^ 25 + ((165587 / 93615) : ℂ) * ζ ^ 27 + ((26044 / 18723) : ℂ) * ζ ^ 28 - ((29299 / 18723) : ℂ) * ζ ^ 29 - ((29243 / 6241) : ℂ) * ζ ^ 30 - ((165587 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep02CoefficientIdentity06 :
    row18_reducedY11_combinationStep02Coefficient06 =
      row18_reducedY11_combinationStep01Coefficient06 +
        row18_reducedY11_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep02Coefficient06 row18_reducedY11_combinationStep01Coefficient06 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 (((4202416 / 1479117) : ℂ) + ((594861 / 986078) : ℂ) * ζ ^ 1 + ((79349911 / 14791170) : ℂ) * ζ ^ 2 + ((4379827 / 4930390) : ℂ) * ζ ^ 3 - ((5261228 / 2465195) : ℂ) * ζ ^ 4 - ((969698 / 2465195) : ℂ) * ζ ^ 5 - ((22830517 / 14791170) : ℂ) * ζ ^ 6 - ((5427557 / 2958234) : ℂ) * ζ ^ 7 + ((52234169 / 14791170) : ℂ) * ζ ^ 8 + ((6742307 / 4930390) : ℂ) * ζ ^ 9 - ((363848 / 7395585) : ℂ) * ζ ^ 10 - ((2557162 / 7395585) : ℂ) * ζ ^ 11 - ((151694 / 93615) : ℂ) * ζ ^ 12 - ((39024071 / 14791170) : ℂ) * ζ ^ 13 - ((2047322 / 7395585) : ℂ) * ζ ^ 14 + ((7880621 / 14791170) : ℂ) * ζ ^ 15 + ((15840719 / 14791170) : ℂ) * ζ ^ 16 + ((1201649 / 2958234) : ℂ) * ζ ^ 17 - ((2880001 / 14791170) : ℂ) * ζ ^ 18 - ((4195362 / 2465195) : ℂ) * ζ ^ 19 - ((274505 / 493039) : ℂ) * ζ ^ 20 - ((885649 / 2958234) : ℂ) * ζ ^ 21 - ((7681921 / 7395585) : ℂ) * ζ ^ 22 + ((6487079 / 2958234) : ℂ) * ζ ^ 23 + ((5052746 / 7395585) : ℂ) * ζ ^ 24 - ((1026535 / 986078) : ℂ) * ζ ^ 25 + ((4844756 / 2465195) : ℂ) * ζ ^ 26 - ((4706672 / 2465195) : ℂ) * ζ ^ 27 - ((1979657 / 2465195) : ℂ) * ζ ^ 28 + ((1476867 / 986078) : ℂ) * ζ ^ 29 + ((304590 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep02CoefficientIdentity07 :
    row18_reducedY11_combinationStep02Coefficient07 =
      row18_reducedY11_combinationStep01Coefficient07 +
        row18_reducedY11_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep02Coefficient07 row18_reducedY11_combinationStep01Coefficient07 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep02CoefficientIdentity08 :
    row18_reducedY11_combinationStep02Coefficient08 =
      row18_reducedY11_combinationStep01Coefficient08 +
        row18_reducedY11_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep02Coefficient08 row18_reducedY11_combinationStep01Coefficient08 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep02CoefficientIdentity09 :
    row18_reducedY11_combinationStep02Coefficient09 =
      row18_reducedY11_combinationStep01Coefficient09 +
        row18_reducedY11_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep02Coefficient09 row18_reducedY11_combinationStep01Coefficient09 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep02CoefficientIdentity10 :
    row18_reducedY11_combinationStep02Coefficient10 =
      row18_reducedY11_combinationStep01Coefficient10 +
        row18_reducedY11_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep02Coefficient10 row18_reducedY11_combinationStep01Coefficient10 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep02CoefficientIdentity11 :
    row18_reducedY11_combinationStep02Coefficient11 =
      row18_reducedY11_combinationStep01Coefficient11 +
        row18_reducedY11_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep02Coefficient11 row18_reducedY11_combinationStep01Coefficient11 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep02CoefficientIdentity12 :
    row18_reducedY11_combinationStep02Coefficient12 =
      row18_reducedY11_combinationStep01Coefficient12 +
        row18_reducedY11_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep02Coefficient12 row18_reducedY11_combinationStep01Coefficient12 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep02CoefficientIdentity13 :
    row18_reducedY11_combinationStep02Coefficient13 =
      row18_reducedY11_combinationStep01Coefficient13 +
        row18_reducedY11_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep02Coefficient13 row18_reducedY11_combinationStep01Coefficient13 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep02CoefficientIdentity14 :
    row18_reducedY11_combinationStep02Coefficient14 =
      row18_reducedY11_combinationStep01Coefficient14 +
        row18_reducedY11_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep02Coefficient14 row18_reducedY11_combinationStep01Coefficient14 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep02CoefficientIdentity15 :
    row18_reducedY11_combinationStep02Coefficient15 =
      row18_reducedY11_combinationStep01Coefficient15 +
        row18_reducedY11_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep02Coefficient15 row18_reducedY11_combinationStep01Coefficient15 row18_reducedY11_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY11_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY11_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY11_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY11_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY11_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY11_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY11_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY11_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY11_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY11_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY11_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY11_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY11_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY11_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY11_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY11_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY11_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY11_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY11_combinationStep02CoefficientIdentity00,
      row18_reducedY11_combinationStep02CoefficientIdentity01,
      row18_reducedY11_combinationStep02CoefficientIdentity02,
      row18_reducedY11_combinationStep02CoefficientIdentity03,
      row18_reducedY11_combinationStep02CoefficientIdentity04,
      row18_reducedY11_combinationStep02CoefficientIdentity05,
      row18_reducedY11_combinationStep02CoefficientIdentity06,
      row18_reducedY11_combinationStep02CoefficientIdentity07,
      row18_reducedY11_combinationStep02CoefficientIdentity08,
      row18_reducedY11_combinationStep02CoefficientIdentity09,
      row18_reducedY11_combinationStep02CoefficientIdentity10,
      row18_reducedY11_combinationStep02CoefficientIdentity11,
      row18_reducedY11_combinationStep02CoefficientIdentity12,
      row18_reducedY11_combinationStep02CoefficientIdentity13,
      row18_reducedY11_combinationStep02CoefficientIdentity14,
      row18_reducedY11_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY11_combinationStep02Multiplier * equation

private def row18_reducedY11_combinationStep03Multiplier : ℂ :=
  (-((33454 / 18723) : ℂ) + ((19636 / 18723) : ℂ) * ζ ^ 1 - ((246932 / 18723) : ℂ) * ζ ^ 2 - ((76840 / 6241) : ℂ) * ζ ^ 5 - ((213478 / 18723) : ℂ) * ζ ^ 6 - ((213478 / 18723) : ℂ) * ζ ^ 8 - ((76840 / 6241) : ℂ) * ζ ^ 9 - ((81938 / 6241) : ℂ) * ζ ^ 11 - ((132082 / 18723) : ℂ) * ζ ^ 12 - ((19636 / 18723) : ℂ) * ζ ^ 13 - ((182768 / 18723) : ℂ) * ζ ^ 15 - ((19636 / 18723) : ℂ) * ζ ^ 17 + ((38404 / 6241) : ℂ) * ζ ^ 18 + ((105442 / 18723) : ℂ) * ζ ^ 21 + ((246932 / 18723) : ℂ) * ζ ^ 22 + ((98266 / 18723) : ℂ) * ζ ^ 24 + ((250156 / 18723) : ℂ) * ζ ^ 25 + ((182768 / 18723) : ℂ) * ζ ^ 27 + ((213478 / 18723) : ℂ) * ζ ^ 28 + ((19636 / 18723) : ℂ) * ζ ^ 29 - ((27132 / 6241) : ℂ) * ζ ^ 30 + ((81938 / 6241) : ℂ) * ζ ^ 31)

private def row18_reducedY11_combinationStep03Coefficient00 : ℂ :=
  (((138 / 79) : ℂ) - ((1386 / 395) : ℂ) * ζ ^ 1 + ((5993 / 790) : ℂ) * ζ ^ 2 + ((1773 / 790) : ℂ) * ζ ^ 3 + ((2709 / 790) : ℂ) * ζ ^ 5 + ((3236 / 395) : ℂ) * ζ ^ 6 + ((933 / 158) : ℂ) * ζ ^ 8 + ((6249 / 790) : ℂ) * ζ ^ 9 + ((2238 / 395) : ℂ) * ζ ^ 11 + ((933 / 158) : ℂ) * ζ ^ 12 + ((1386 / 395) : ℂ) * ζ ^ 13 + ((1854 / 395) : ℂ) * ζ ^ 15 + ((1386 / 395) : ℂ) * ζ ^ 17 - ((479 / 790) : ℂ) * ζ ^ 18 + ((999 / 790) : ℂ) * ζ ^ 21 - ((5993 / 790) : ℂ) * ζ ^ 22 - ((5481 / 790) : ℂ) * ζ ^ 25 - ((999 / 790) : ℂ) * ζ ^ 27 - ((933 / 158) : ℂ) * ζ ^ 28 - ((1386 / 395) : ℂ) * ζ ^ 29 + ((1618 / 395) : ℂ) * ζ ^ 30 - ((2238 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep03CoefficientIdentity00 :
    row18_reducedY11_combinationStep03Coefficient00 =
      row18_reducedY11_combinationStep02Coefficient00 +
        row18_reducedY11_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep03Coefficient00 row18_reducedY11_combinationStep02Coefficient00 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 (((273157 / 493039) : ℂ) + ((4563445 / 2958234) : ℂ) * ζ ^ 1 - ((3336681 / 986078) : ℂ) * ζ ^ 2 - ((1367495 / 1479117) : ℂ) * ζ ^ 3 - ((1616350 / 1479117) : ℂ) * ζ ^ 4 - ((4377073 / 2958234) : ℂ) * ζ ^ 5 + ((1468201 / 986078) : ℂ) * ζ ^ 6 + ((3188549 / 2958234) : ℂ) * ζ ^ 7 - ((4068034 / 1479117) : ℂ) * ζ ^ 8 + ((119108 / 1479117) : ℂ) * ζ ^ 9 + ((1189715 / 1479117) : ℂ) * ζ ^ 10 - ((8062 / 493039) : ℂ) * ζ ^ 11 + ((1034530 / 1479117) : ℂ) * ζ ^ 12 + ((2221252 / 1479117) : ℂ) * ζ ^ 13 - ((400291 / 2958234) : ℂ) * ζ ^ 14 + ((273509 / 493039) : ℂ) * ζ ^ 15 + ((2093875 / 2958234) : ℂ) * ζ ^ 16 + ((236948 / 1479117) : ℂ) * ζ ^ 17 - ((63881 / 2958234) : ℂ) * ζ ^ 18 + ((272333 / 1479117) : ℂ) * ζ ^ 19 - ((1485035 / 2958234) : ℂ) * ζ ^ 20 + ((1386739 / 1479117) : ℂ) * ζ ^ 21 + ((1073444 / 1479117) : ℂ) * ζ ^ 22 - ((3575185 / 2958234) : ℂ) * ζ ^ 23 + ((524825 / 986078) : ℂ) * ζ ^ 24 - ((516181 / 2958234) : ℂ) * ζ ^ 25 - ((2667919 / 1479117) : ℂ) * ζ ^ 26 + ((951373 / 493039) : ℂ) * ζ ^ 27 + ((69481 / 986078) : ℂ) * ζ ^ 28 - ((881511 / 493039) : ℂ) * ζ ^ 29 - ((614535 / 986078) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep03Coefficient01 : ℂ :=
  (-((33 / 158) : ℂ) + ((23 / 158) : ℂ) * ζ ^ 1 - ((7 / 158) : ℂ) * ζ ^ 2 - ((14 / 79) : ℂ) * ζ ^ 3 + ((23 / 158) : ℂ) * ζ ^ 5 - ((20 / 79) : ℂ) * ζ ^ 6 + ((20 / 79) : ℂ) * ζ ^ 8 - ((23 / 158) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((45 / 158) : ℂ) * ζ ^ 12 - ((23 / 158) : ℂ) * ζ ^ 13 - ((11 / 158) : ℂ) * ζ ^ 15 - ((23 / 158) : ℂ) * ζ ^ 17 + ((16 / 79) : ℂ) * ζ ^ 18 - ((29 / 79) : ℂ) * ζ ^ 21 + ((7 / 158) : ℂ) * ζ ^ 22 - ((4 / 79) : ℂ) * ζ ^ 24 - ((39 / 158) : ℂ) * ζ ^ 27 - ((20 / 79) : ℂ) * ζ ^ 28 + ((23 / 158) : ℂ) * ζ ^ 29 + ((5 / 158) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep03CoefficientIdentity01 :
    row18_reducedY11_combinationStep03Coefficient01 =
      row18_reducedY11_combinationStep02Coefficient01 +
        row18_reducedY11_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep03Coefficient01 row18_reducedY11_combinationStep02Coefficient01 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 (-((18839426 / 1479117) : ℂ) + ((8385167 / 986078) : ℂ) * ζ ^ 1 + ((4328563 / 2958234) : ℂ) * ζ ^ 2 - ((29653285 / 2958234) : ℂ) * ζ ^ 3 + ((9263216 / 1479117) : ℂ) * ζ ^ 4 + ((1606193 / 986078) : ℂ) * ζ ^ 5 - ((13427761 / 986078) : ℂ) * ζ ^ 6 - ((2852123 / 1479117) : ℂ) * ζ ^ 7 - ((1839031 / 2958234) : ℂ) * ζ ^ 8 - ((17020517 / 1479117) : ℂ) * ζ ^ 9 + ((4513177 / 1479117) : ℂ) * ζ ^ 10 - ((5818773 / 986078) : ℂ) * ζ ^ 11 - ((18739303 / 1479117) : ℂ) * ζ ^ 12 + ((2916382 / 1479117) : ℂ) * ζ ^ 13 - ((21889993 / 2958234) : ℂ) * ζ ^ 14 - ((15323170 / 1479117) : ℂ) * ζ ^ 15 + ((1114999 / 493039) : ℂ) * ζ ^ 16 - ((4398243 / 493039) : ℂ) * ζ ^ 17 - ((11097502 / 1479117) : ℂ) * ζ ^ 18 + ((2205308 / 493039) : ℂ) * ζ ^ 19 - ((8192879 / 1479117) : ℂ) * ζ ^ 20 - ((13170494 / 1479117) : ℂ) * ζ ^ 21 + ((3887584 / 1479117) : ℂ) * ζ ^ 22 - ((836789 / 1479117) : ℂ) * ζ ^ 23 - ((1333355 / 1479117) : ℂ) * ζ ^ 24 + ((4012821 / 986078) : ℂ) * ζ ^ 25 - ((7359598 / 1479117) : ℂ) * ζ ^ 26 + ((1189711 / 1479117) : ℂ) * ζ ^ 27 + ((6303851 / 2958234) : ℂ) * ζ ^ 28 + ((301704 / 493039) : ℂ) * ζ ^ 29 + ((573566 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep03Coefficient02 : ℂ :=
  (((117983 / 37446) : ℂ) - ((34669 / 37446) : ℂ) * ζ ^ 1 - ((138223 / 37446) : ℂ) * ζ ^ 2 + ((14780 / 6241) : ℂ) * ζ ^ 3 - ((55176 / 6241) : ℂ) * ζ ^ 5 - ((26123 / 37446) : ℂ) * ζ ^ 6 - ((207223 / 37446) : ℂ) * ζ ^ 8 - ((130859 / 37446) : ℂ) * ζ ^ 9 - ((305057 / 37446) : ℂ) * ζ ^ 11 - ((56050 / 18723) : ℂ) * ζ ^ 12 + ((34669 / 37446) : ℂ) * ζ ^ 13 - ((14780 / 6241) : ℂ) * ζ ^ 15 + ((34669 / 37446) : ℂ) * ζ ^ 17 + ((10120 / 18723) : ℂ) * ζ ^ 18 + ((296387 / 37446) : ℂ) * ζ ^ 21 + ((138223 / 37446) : ℂ) * ζ ^ 22 + ((138223 / 37446) : ℂ) * ζ ^ 24 + ((296387 / 37446) : ℂ) * ζ ^ 25 + ((305057 / 37446) : ℂ) * ζ ^ 27 + ((207223 / 37446) : ℂ) * ζ ^ 28 - ((34669 / 37446) : ℂ) * ζ ^ 29 + ((11500 / 6241) : ℂ) * ζ ^ 30 + ((305057 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep03CoefficientIdentity02 :
    row18_reducedY11_combinationStep03Coefficient02 =
      row18_reducedY11_combinationStep02Coefficient02 +
        row18_reducedY11_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep03Coefficient02 row18_reducedY11_combinationStep02Coefficient02 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep03Coefficient03 : ℂ :=
  (-((14079 / 12482) : ℂ) - ((14009 / 18723) : ℂ) * ζ ^ 1 - ((11627 / 37446) : ℂ) * ζ ^ 2 + ((18731 / 12482) : ℂ) * ζ ^ 3 - ((20338 / 18723) : ℂ) * ζ ^ 5 - ((23869 / 18723) : ℂ) * ζ ^ 6 + ((22249 / 37446) : ℂ) * ζ ^ 8 + ((5505 / 12482) : ℂ) * ζ ^ 9 - ((6613 / 6241) : ℂ) * ζ ^ 11 + ((22249 / 37446) : ℂ) * ζ ^ 12 + ((14009 / 18723) : ℂ) * ζ ^ 13 - ((68851 / 37446) : ℂ) * ζ ^ 15 + ((14009 / 18723) : ℂ) * ζ ^ 17 + ((12037 / 12482) : ℂ) * ζ ^ 18 - ((28175 / 37446) : ℂ) * ζ ^ 21 + ((11627 / 37446) : ℂ) * ζ ^ 22 + ((6329 / 18723) : ℂ) * ζ ^ 25 + ((28175 / 37446) : ℂ) * ζ ^ 27 - ((22249 / 37446) : ℂ) * ζ ^ 28 - ((14009 / 18723) : ℂ) * ζ ^ 29 - ((23869 / 37446) : ℂ) * ζ ^ 30 + ((6613 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep03CoefficientIdentity03 :
    row18_reducedY11_combinationStep03Coefficient03 =
      row18_reducedY11_combinationStep02Coefficient03 +
        row18_reducedY11_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep03Coefficient03 row18_reducedY11_combinationStep02Coefficient03 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep03Coefficient04 : ℂ :=
  (-((51967 / 37446) : ℂ) + ((90934 / 31205) : ℂ) * ζ ^ 1 - ((174221 / 31205) : ℂ) * ζ ^ 2 - ((65706 / 31205) : ℂ) * ζ ^ 3 - ((540113 / 187230) : ℂ) * ζ ^ 5 - ((569137 / 93615) : ℂ) * ζ ^ 6 - ((85648 / 18723) : ℂ) * ζ ^ 8 - ((638309 / 93615) : ℂ) * ζ ^ 9 - ((441191 / 93615) : ℂ) * ζ ^ 11 - ((85648 / 18723) : ℂ) * ζ ^ 12 - ((90934 / 31205) : ℂ) * ζ ^ 13 - ((691481 / 187230) : ℂ) * ζ ^ 15 - ((90934 / 31205) : ℂ) * ζ ^ 17 + ((46474 / 93615) : ℂ) * ζ ^ 18 - ((25228 / 31205) : ℂ) * ζ ^ 21 + ((174221 / 31205) : ℂ) * ζ ^ 22 + ((1085717 / 187230) : ℂ) * ζ ^ 25 + ((25228 / 31205) : ℂ) * ζ ^ 27 + ((85648 / 18723) : ℂ) * ζ ^ 28 + ((90934 / 31205) : ℂ) * ζ ^ 29 - ((569137 / 187230) : ℂ) * ζ ^ 30 + ((441191 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep03CoefficientIdentity04 :
    row18_reducedY11_combinationStep03Coefficient04 =
      row18_reducedY11_combinationStep02Coefficient04 +
        row18_reducedY11_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep03Coefficient04 row18_reducedY11_combinationStep02Coefficient04 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep03Coefficient05 : ℂ :=
  (-((10481 / 18723) : ℂ) + ((17585 / 12482) : ℂ) * ζ ^ 1 - ((207581 / 37446) : ℂ) * ζ ^ 2 - ((166601 / 37446) : ℂ) * ζ ^ 5 - ((186619 / 37446) : ℂ) * ζ ^ 6 - ((186619 / 37446) : ℂ) * ζ ^ 8 - ((166601 / 37446) : ℂ) * ζ ^ 9 - ((207679 / 37446) : ℂ) * ζ ^ 11 - ((63343 / 18723) : ℂ) * ζ ^ 12 - ((17585 / 12482) : ℂ) * ζ ^ 13 - ((114439 / 37446) : ℂ) * ζ ^ 15 - ((17585 / 12482) : ℂ) * ζ ^ 17 + ((44947 / 18723) : ℂ) * ζ ^ 18 + ((56923 / 37446) : ℂ) * ζ ^ 21 + ((207581 / 37446) : ℂ) * ζ ^ 22 + ((96725 / 37446) : ℂ) * ζ ^ 24 + ((109678 / 18723) : ℂ) * ζ ^ 25 + ((114439 / 37446) : ℂ) * ζ ^ 27 + ((186619 / 37446) : ℂ) * ζ ^ 28 + ((17585 / 12482) : ℂ) * ζ ^ 29 - ((59933 / 37446) : ℂ) * ζ ^ 30 + ((207679 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep03CoefficientIdentity05 :
    row18_reducedY11_combinationStep03Coefficient05 =
      row18_reducedY11_combinationStep02Coefficient05 +
        row18_reducedY11_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep03Coefficient05 row18_reducedY11_combinationStep02Coefficient05 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 (((727637 / 1479117) : ℂ) - ((1932916 / 1479117) : ℂ) * ζ ^ 1 + ((6693757 / 1479117) : ℂ) * ζ ^ 2 + ((1113055 / 1479117) : ℂ) * ζ ^ 3 - ((1994920 / 493039) : ℂ) * ζ ^ 4 + ((7786655 / 1479117) : ℂ) * ζ ^ 5 + ((331219 / 986078) : ℂ) * ζ ^ 6 - ((12880759 / 2958234) : ℂ) * ζ ^ 7 + ((13223791 / 2958234) : ℂ) * ζ ^ 8 - ((1475849 / 1479117) : ℂ) * ζ ^ 9 - ((1091571 / 493039) : ℂ) * ζ ^ 10 + ((3598921 / 986078) : ℂ) * ζ ^ 11 - ((1221023 / 986078) : ℂ) * ζ ^ 12 - ((2278347 / 986078) : ℂ) * ζ ^ 13 + ((7926866 / 1479117) : ℂ) * ζ ^ 14 - ((4095803 / 1479117) : ℂ) * ζ ^ 15 - ((1908383 / 986078) : ℂ) * ζ ^ 16 + ((5397491 / 1479117) : ℂ) * ζ ^ 17 - ((3195217 / 986078) : ℂ) * ζ ^ 18 - ((3449917 / 2958234) : ℂ) * ζ ^ 19 + ((2170651 / 1479117) : ℂ) * ζ ^ 20 - ((3388319 / 986078) : ℂ) * ζ ^ 21 - ((1091189 / 2958234) : ℂ) * ζ ^ 22 + ((155499 / 493039) : ℂ) * ζ ^ 23 - ((115783 / 493039) : ℂ) * ζ ^ 24 - ((1375565 / 2958234) : ℂ) * ζ ^ 25 - ((981073 / 2958234) : ℂ) * ζ ^ 26 + ((3412165 / 2958234) : ℂ) * ζ ^ 27 - ((2140597 / 2958234) : ℂ) * ζ ^ 28 + ((422714 / 493039) : ℂ) * ζ ^ 29 - ((286783 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep03Coefficient06 : ℂ :=
  (-((27593 / 18723) : ℂ) - ((29299 / 18723) : ℂ) * ζ ^ 1 - ((61685 / 18723) : ℂ) * ζ ^ 2 - ((214474 / 93615) : ℂ) * ζ ^ 3 - ((3933 / 6241) : ℂ) * ζ ^ 6 - ((26044 / 18723) : ℂ) * ζ ^ 8 - ((20245 / 6241) : ℂ) * ζ ^ 9 + ((165587 / 93615) : ℂ) * ζ ^ 11 + ((49886 / 18723) : ℂ) * ζ ^ 12 + ((29299 / 18723) : ℂ) * ζ ^ 13 - ((214474 / 93615) : ℂ) * ζ ^ 15 + ((29299 / 18723) : ℂ) * ζ ^ 17 + ((11364 / 6241) : ℂ) * ζ ^ 18 + ((29299 / 18723) : ℂ) * ζ ^ 21 + ((61685 / 18723) : ℂ) * ζ ^ 22 - ((61685 / 18723) : ℂ) * ζ ^ 24 - ((29299 / 18723) : ℂ) * ζ ^ 25 + ((165587 / 93615) : ℂ) * ζ ^ 27 + ((26044 / 18723) : ℂ) * ζ ^ 28 - ((29299 / 18723) : ℂ) * ζ ^ 29 - ((29243 / 6241) : ℂ) * ζ ^ 30 - ((165587 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep03CoefficientIdentity06 :
    row18_reducedY11_combinationStep03Coefficient06 =
      row18_reducedY11_combinationStep02Coefficient06 +
        row18_reducedY11_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep03Coefficient06 row18_reducedY11_combinationStep02Coefficient06 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep03Coefficient07 : ℂ :=
  (((14396 / 18723) : ℂ) + ((25145 / 18723) : ℂ) * ζ ^ 1 - ((31688 / 18723) : ℂ) * ζ ^ 2 - ((10231 / 6241) : ℂ) * ζ ^ 3 + ((3382 / 6241) : ℂ) * ζ ^ 5 - ((5230 / 6241) : ℂ) * ζ ^ 6 - ((36037 / 18723) : ℂ) * ζ ^ 8 - ((28697 / 18723) : ℂ) * ζ ^ 9 + ((1996 / 18723) : ℂ) * ζ ^ 11 - ((36037 / 18723) : ℂ) * ζ ^ 12 - ((25145 / 18723) : ℂ) * ζ ^ 13 + ((15694 / 18723) : ℂ) * ζ ^ 15 - ((25145 / 18723) : ℂ) * ζ ^ 17 - ((15998 / 18723) : ℂ) * ζ ^ 18 + ((5548 / 18723) : ℂ) * ζ ^ 21 + ((31688 / 18723) : ℂ) * ζ ^ 22 + ((14999 / 18723) : ℂ) * ζ ^ 25 - ((5548 / 18723) : ℂ) * ζ ^ 27 + ((36037 / 18723) : ℂ) * ζ ^ 28 + ((25145 / 18723) : ℂ) * ζ ^ 29 - ((2615 / 6241) : ℂ) * ζ ^ 30 - ((1996 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep03CoefficientIdentity07 :
    row18_reducedY11_combinationStep03Coefficient07 =
      row18_reducedY11_combinationStep02Coefficient07 +
        row18_reducedY11_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep03Coefficient07 row18_reducedY11_combinationStep02Coefficient07 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 (-((273157 / 493039) : ℂ) - ((4563445 / 2958234) : ℂ) * ζ ^ 1 + ((3336681 / 986078) : ℂ) * ζ ^ 2 + ((1367495 / 1479117) : ℂ) * ζ ^ 3 + ((1616350 / 1479117) : ℂ) * ζ ^ 4 + ((4377073 / 2958234) : ℂ) * ζ ^ 5 - ((1468201 / 986078) : ℂ) * ζ ^ 6 - ((3188549 / 2958234) : ℂ) * ζ ^ 7 + ((4068034 / 1479117) : ℂ) * ζ ^ 8 - ((119108 / 1479117) : ℂ) * ζ ^ 9 - ((1189715 / 1479117) : ℂ) * ζ ^ 10 + ((8062 / 493039) : ℂ) * ζ ^ 11 - ((1034530 / 1479117) : ℂ) * ζ ^ 12 - ((2221252 / 1479117) : ℂ) * ζ ^ 13 + ((400291 / 2958234) : ℂ) * ζ ^ 14 - ((273509 / 493039) : ℂ) * ζ ^ 15 - ((2093875 / 2958234) : ℂ) * ζ ^ 16 - ((236948 / 1479117) : ℂ) * ζ ^ 17 + ((63881 / 2958234) : ℂ) * ζ ^ 18 - ((272333 / 1479117) : ℂ) * ζ ^ 19 + ((1485035 / 2958234) : ℂ) * ζ ^ 20 - ((1386739 / 1479117) : ℂ) * ζ ^ 21 - ((1073444 / 1479117) : ℂ) * ζ ^ 22 + ((3575185 / 2958234) : ℂ) * ζ ^ 23 - ((524825 / 986078) : ℂ) * ζ ^ 24 + ((516181 / 2958234) : ℂ) * ζ ^ 25 + ((2667919 / 1479117) : ℂ) * ζ ^ 26 - ((951373 / 493039) : ℂ) * ζ ^ 27 - ((69481 / 986078) : ℂ) * ζ ^ 28 + ((881511 / 493039) : ℂ) * ζ ^ 29 + ((614535 / 986078) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep03CoefficientIdentity08 :
    row18_reducedY11_combinationStep03Coefficient08 =
      row18_reducedY11_combinationStep02Coefficient08 +
        row18_reducedY11_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep03Coefficient08 row18_reducedY11_combinationStep02Coefficient08 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep03CoefficientIdentity09 :
    row18_reducedY11_combinationStep03Coefficient09 =
      row18_reducedY11_combinationStep02Coefficient09 +
        row18_reducedY11_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep03Coefficient09 row18_reducedY11_combinationStep02Coefficient09 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep03CoefficientIdentity10 :
    row18_reducedY11_combinationStep03Coefficient10 =
      row18_reducedY11_combinationStep02Coefficient10 +
        row18_reducedY11_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep03Coefficient10 row18_reducedY11_combinationStep02Coefficient10 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep03CoefficientIdentity11 :
    row18_reducedY11_combinationStep03Coefficient11 =
      row18_reducedY11_combinationStep02Coefficient11 +
        row18_reducedY11_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep03Coefficient11 row18_reducedY11_combinationStep02Coefficient11 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep03CoefficientIdentity12 :
    row18_reducedY11_combinationStep03Coefficient12 =
      row18_reducedY11_combinationStep02Coefficient12 +
        row18_reducedY11_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep03Coefficient12 row18_reducedY11_combinationStep02Coefficient12 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep03CoefficientIdentity13 :
    row18_reducedY11_combinationStep03Coefficient13 =
      row18_reducedY11_combinationStep02Coefficient13 +
        row18_reducedY11_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep03Coefficient13 row18_reducedY11_combinationStep02Coefficient13 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep03CoefficientIdentity14 :
    row18_reducedY11_combinationStep03Coefficient14 =
      row18_reducedY11_combinationStep02Coefficient14 +
        row18_reducedY11_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep03Coefficient14 row18_reducedY11_combinationStep02Coefficient14 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep03CoefficientIdentity15 :
    row18_reducedY11_combinationStep03Coefficient15 =
      row18_reducedY11_combinationStep02Coefficient15 +
        row18_reducedY11_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep03Coefficient15 row18_reducedY11_combinationStep02Coefficient15 row18_reducedY11_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY11_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY11_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY11_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY11_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY11_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY11_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY11_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY11_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY11_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY11_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY11_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY11_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY11_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY11_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY11_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY11_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY11_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY11_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY11_combinationStep03CoefficientIdentity00,
      row18_reducedY11_combinationStep03CoefficientIdentity01,
      row18_reducedY11_combinationStep03CoefficientIdentity02,
      row18_reducedY11_combinationStep03CoefficientIdentity03,
      row18_reducedY11_combinationStep03CoefficientIdentity04,
      row18_reducedY11_combinationStep03CoefficientIdentity05,
      row18_reducedY11_combinationStep03CoefficientIdentity06,
      row18_reducedY11_combinationStep03CoefficientIdentity07,
      row18_reducedY11_combinationStep03CoefficientIdentity08,
      row18_reducedY11_combinationStep03CoefficientIdentity09,
      row18_reducedY11_combinationStep03CoefficientIdentity10,
      row18_reducedY11_combinationStep03CoefficientIdentity11,
      row18_reducedY11_combinationStep03CoefficientIdentity12,
      row18_reducedY11_combinationStep03CoefficientIdentity13,
      row18_reducedY11_combinationStep03CoefficientIdentity14,
      row18_reducedY11_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY11_combinationStep03Multiplier * equation

private def row18_reducedY11_combinationStep04Multiplier : ℂ :=
  (-((14 / 79) : ℂ) - ((120 / 79) : ℂ) * ζ ^ 1 - ((218 / 79) : ℂ) * ζ ^ 2 + ((52 / 79) : ℂ) * ζ ^ 5 - ((204 / 79) : ℂ) * ζ ^ 6 - ((204 / 79) : ℂ) * ζ ^ 8 + ((52 / 79) : ℂ) * ζ ^ 9 + ((94 / 79) : ℂ) * ζ ^ 11 - ((2 / 79) : ℂ) * ζ ^ 12 + ((120 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 + ((120 / 79) : ℂ) * ζ ^ 17 + ((148 / 79) : ℂ) * ζ ^ 18 + ((34 / 79) : ℂ) * ζ ^ 21 + ((218 / 79) : ℂ) * ζ ^ 22 + ((56 / 79) : ℂ) * ζ ^ 24 - ((172 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((204 / 79) : ℂ) * ζ ^ 28 - ((120 / 79) : ℂ) * ζ ^ 29 - ((202 / 79) : ℂ) * ζ ^ 30 - ((94 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY11_combinationStep04Coefficient00 : ℂ :=
  (((171 / 79) : ℂ) - ((1506 / 395) : ℂ) * ζ ^ 1 + ((2949 / 395) : ℂ) * ζ ^ 2 + ((1079 / 395) : ℂ) * ζ ^ 3 + ((1402 / 395) : ℂ) * ζ ^ 5 + ((3246 / 395) : ℂ) * ζ ^ 6 + ((469 / 79) : ℂ) * ζ ^ 8 + ((3362 / 395) : ℂ) * ζ ^ 9 + ((2283 / 395) : ℂ) * ζ ^ 11 + ((469 / 79) : ℂ) * ζ ^ 12 + ((1506 / 395) : ℂ) * ζ ^ 13 + ((1829 / 395) : ℂ) * ζ ^ 15 + ((1506 / 395) : ℂ) * ζ ^ 17 - ((297 / 395) : ℂ) * ζ ^ 18 + ((427 / 395) : ℂ) * ζ ^ 21 - ((2949 / 395) : ℂ) * ζ ^ 22 - ((2908 / 395) : ℂ) * ζ ^ 25 - ((427 / 395) : ℂ) * ζ ^ 27 - ((469 / 79) : ℂ) * ζ ^ 28 - ((1506 / 395) : ℂ) * ζ ^ 29 + ((1623 / 395) : ℂ) * ζ ^ 30 - ((2283 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep04CoefficientIdentity00 :
    row18_reducedY11_combinationStep04Coefficient00 =
      row18_reducedY11_combinationStep03Coefficient00 +
        row18_reducedY11_combinationStep04Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep04Coefficient00 row18_reducedY11_combinationStep03Coefficient00 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 (-((2474 / 6241) : ℂ) + ((6163 / 12482) : ℂ) * ζ ^ 1 + ((3250 / 6241) : ℂ) * ζ ^ 2 - ((1919 / 6241) : ℂ) * ζ ^ 3 + ((7587 / 12482) : ℂ) * ζ ^ 4 - ((3018 / 6241) : ℂ) * ζ ^ 5 - ((1520 / 6241) : ℂ) * ζ ^ 6 + ((3459 / 6241) : ℂ) * ζ ^ 7 - ((315 / 12482) : ℂ) * ζ ^ 8 - ((1635 / 12482) : ℂ) * ζ ^ 9 + ((2433 / 12482) : ℂ) * ζ ^ 10 + ((203 / 12482) : ℂ) * ζ ^ 11 - ((1748 / 6241) : ℂ) * ζ ^ 12 + ((1205 / 6241) : ℂ) * ζ ^ 13 - ((837 / 12482) : ℂ) * ζ ^ 14 + ((894 / 6241) : ℂ) * ζ ^ 15 + ((247 / 12482) : ℂ) * ζ ^ 16 + ((163 / 6241) : ℂ) * ζ ^ 17 + ((1985 / 12482) : ℂ) * ζ ^ 18 - ((1125 / 6241) : ℂ) * ζ ^ 19 + ((871 / 12482) : ℂ) * ζ ^ 20 + ((706 / 6241) : ℂ) * ζ ^ 21 - ((3236 / 6241) : ℂ) * ζ ^ 22 + ((2 / 79) : ℂ) * ζ ^ 23 - ((710 / 6241) : ℂ) * ζ ^ 24 + ((240 / 6241) : ℂ) * ζ ^ 25 + ((10525 / 12482) : ℂ) * ζ ^ 26 - ((162 / 6241) : ℂ) * ζ ^ 27 - ((3337 / 12482) : ℂ) * ζ ^ 28 - ((741 / 12482) : ℂ) * ζ ^ 29 + ((705 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep04Coefficient01 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep04CoefficientIdentity01 :
    row18_reducedY11_combinationStep04Coefficient01 =
      row18_reducedY11_combinationStep03Coefficient01 +
        row18_reducedY11_combinationStep04Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep04Coefficient01 row18_reducedY11_combinationStep03Coefficient01 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 (-((2719 / 12482) : ℂ) + ((390 / 6241) : ℂ) * ζ ^ 1 - ((1601 / 6241) : ℂ) * ζ ^ 2 - ((2752 / 6241) : ℂ) * ζ ^ 3 - ((518 / 6241) : ℂ) * ζ ^ 4 + ((676 / 6241) : ℂ) * ζ ^ 5 - ((1552 / 6241) : ℂ) * ζ ^ 6 + ((1011 / 6241) : ℂ) * ζ ^ 7 - ((495 / 6241) : ℂ) * ζ ^ 8 - ((1661 / 6241) : ℂ) * ζ ^ 9 + ((1017 / 6241) : ℂ) * ζ ^ 10 - ((893 / 12482) : ℂ) * ζ ^ 11 + ((1643 / 12482) : ℂ) * ζ ^ 12 + ((887 / 6241) : ℂ) * ζ ^ 13 - ((55 / 6241) : ℂ) * ζ ^ 14 - ((204 / 6241) : ℂ) * ζ ^ 15 - ((886 / 6241) : ℂ) * ζ ^ 16 + ((638 / 6241) : ℂ) * ζ ^ 17 + ((2889 / 12482) : ℂ) * ζ ^ 18 + ((2551 / 12482) : ℂ) * ζ ^ 19 + ((5915 / 12482) : ℂ) * ζ ^ 20 - ((4831 / 12482) : ℂ) * ζ ^ 21 - ((1303 / 6241) : ℂ) * ζ ^ 22 + ((594 / 6241) : ℂ) * ζ ^ 23 + ((2049 / 6241) : ℂ) * ζ ^ 24 + ((442 / 6241) : ℂ) * ζ ^ 25 + ((72 / 6241) : ℂ) * ζ ^ 26 - ((3541 / 12482) : ℂ) * ζ ^ 27 - ((889 / 12482) : ℂ) * ζ ^ 28 + ((425 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep04Coefficient02 : ℂ :=
  (((117983 / 37446) : ℂ) - ((34669 / 37446) : ℂ) * ζ ^ 1 - ((138223 / 37446) : ℂ) * ζ ^ 2 + ((14780 / 6241) : ℂ) * ζ ^ 3 - ((55176 / 6241) : ℂ) * ζ ^ 5 - ((26123 / 37446) : ℂ) * ζ ^ 6 - ((207223 / 37446) : ℂ) * ζ ^ 8 - ((130859 / 37446) : ℂ) * ζ ^ 9 - ((305057 / 37446) : ℂ) * ζ ^ 11 - ((56050 / 18723) : ℂ) * ζ ^ 12 + ((34669 / 37446) : ℂ) * ζ ^ 13 - ((14780 / 6241) : ℂ) * ζ ^ 15 + ((34669 / 37446) : ℂ) * ζ ^ 17 + ((10120 / 18723) : ℂ) * ζ ^ 18 + ((296387 / 37446) : ℂ) * ζ ^ 21 + ((138223 / 37446) : ℂ) * ζ ^ 22 + ((138223 / 37446) : ℂ) * ζ ^ 24 + ((296387 / 37446) : ℂ) * ζ ^ 25 + ((305057 / 37446) : ℂ) * ζ ^ 27 + ((207223 / 37446) : ℂ) * ζ ^ 28 - ((34669 / 37446) : ℂ) * ζ ^ 29 + ((11500 / 6241) : ℂ) * ζ ^ 30 + ((305057 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep04CoefficientIdentity02 :
    row18_reducedY11_combinationStep04Coefficient02 =
      row18_reducedY11_combinationStep03Coefficient02 +
        row18_reducedY11_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep04Coefficient02 row18_reducedY11_combinationStep03Coefficient02 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep04Coefficient03 : ℂ :=
  (-((14079 / 12482) : ℂ) - ((14009 / 18723) : ℂ) * ζ ^ 1 - ((11627 / 37446) : ℂ) * ζ ^ 2 + ((18731 / 12482) : ℂ) * ζ ^ 3 - ((20338 / 18723) : ℂ) * ζ ^ 5 - ((23869 / 18723) : ℂ) * ζ ^ 6 + ((22249 / 37446) : ℂ) * ζ ^ 8 + ((5505 / 12482) : ℂ) * ζ ^ 9 - ((6613 / 6241) : ℂ) * ζ ^ 11 + ((22249 / 37446) : ℂ) * ζ ^ 12 + ((14009 / 18723) : ℂ) * ζ ^ 13 - ((68851 / 37446) : ℂ) * ζ ^ 15 + ((14009 / 18723) : ℂ) * ζ ^ 17 + ((12037 / 12482) : ℂ) * ζ ^ 18 - ((28175 / 37446) : ℂ) * ζ ^ 21 + ((11627 / 37446) : ℂ) * ζ ^ 22 + ((6329 / 18723) : ℂ) * ζ ^ 25 + ((28175 / 37446) : ℂ) * ζ ^ 27 - ((22249 / 37446) : ℂ) * ζ ^ 28 - ((14009 / 18723) : ℂ) * ζ ^ 29 - ((23869 / 37446) : ℂ) * ζ ^ 30 + ((6613 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep04CoefficientIdentity03 :
    row18_reducedY11_combinationStep04Coefficient03 =
      row18_reducedY11_combinationStep03Coefficient03 +
        row18_reducedY11_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep04Coefficient03 row18_reducedY11_combinationStep03Coefficient03 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep04Coefficient04 : ℂ :=
  (-((51967 / 37446) : ℂ) + ((90934 / 31205) : ℂ) * ζ ^ 1 - ((174221 / 31205) : ℂ) * ζ ^ 2 - ((65706 / 31205) : ℂ) * ζ ^ 3 - ((540113 / 187230) : ℂ) * ζ ^ 5 - ((569137 / 93615) : ℂ) * ζ ^ 6 - ((85648 / 18723) : ℂ) * ζ ^ 8 - ((638309 / 93615) : ℂ) * ζ ^ 9 - ((441191 / 93615) : ℂ) * ζ ^ 11 - ((85648 / 18723) : ℂ) * ζ ^ 12 - ((90934 / 31205) : ℂ) * ζ ^ 13 - ((691481 / 187230) : ℂ) * ζ ^ 15 - ((90934 / 31205) : ℂ) * ζ ^ 17 + ((46474 / 93615) : ℂ) * ζ ^ 18 - ((25228 / 31205) : ℂ) * ζ ^ 21 + ((174221 / 31205) : ℂ) * ζ ^ 22 + ((1085717 / 187230) : ℂ) * ζ ^ 25 + ((25228 / 31205) : ℂ) * ζ ^ 27 + ((85648 / 18723) : ℂ) * ζ ^ 28 + ((90934 / 31205) : ℂ) * ζ ^ 29 - ((569137 / 187230) : ℂ) * ζ ^ 30 + ((441191 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep04CoefficientIdentity04 :
    row18_reducedY11_combinationStep04Coefficient04 =
      row18_reducedY11_combinationStep03Coefficient04 +
        row18_reducedY11_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep04Coefficient04 row18_reducedY11_combinationStep03Coefficient04 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep04Coefficient05 : ℂ :=
  (-((10481 / 18723) : ℂ) + ((17585 / 12482) : ℂ) * ζ ^ 1 - ((207581 / 37446) : ℂ) * ζ ^ 2 - ((166601 / 37446) : ℂ) * ζ ^ 5 - ((186619 / 37446) : ℂ) * ζ ^ 6 - ((186619 / 37446) : ℂ) * ζ ^ 8 - ((166601 / 37446) : ℂ) * ζ ^ 9 - ((207679 / 37446) : ℂ) * ζ ^ 11 - ((63343 / 18723) : ℂ) * ζ ^ 12 - ((17585 / 12482) : ℂ) * ζ ^ 13 - ((114439 / 37446) : ℂ) * ζ ^ 15 - ((17585 / 12482) : ℂ) * ζ ^ 17 + ((44947 / 18723) : ℂ) * ζ ^ 18 + ((56923 / 37446) : ℂ) * ζ ^ 21 + ((207581 / 37446) : ℂ) * ζ ^ 22 + ((96725 / 37446) : ℂ) * ζ ^ 24 + ((109678 / 18723) : ℂ) * ζ ^ 25 + ((114439 / 37446) : ℂ) * ζ ^ 27 + ((186619 / 37446) : ℂ) * ζ ^ 28 + ((17585 / 12482) : ℂ) * ζ ^ 29 - ((59933 / 37446) : ℂ) * ζ ^ 30 + ((207679 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep04CoefficientIdentity05 :
    row18_reducedY11_combinationStep04Coefficient05 =
      row18_reducedY11_combinationStep03Coefficient05 +
        row18_reducedY11_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep04Coefficient05 row18_reducedY11_combinationStep03Coefficient05 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep04Coefficient06 : ℂ :=
  (-((27593 / 18723) : ℂ) - ((29299 / 18723) : ℂ) * ζ ^ 1 - ((61685 / 18723) : ℂ) * ζ ^ 2 - ((214474 / 93615) : ℂ) * ζ ^ 3 - ((3933 / 6241) : ℂ) * ζ ^ 6 - ((26044 / 18723) : ℂ) * ζ ^ 8 - ((20245 / 6241) : ℂ) * ζ ^ 9 + ((165587 / 93615) : ℂ) * ζ ^ 11 + ((49886 / 18723) : ℂ) * ζ ^ 12 + ((29299 / 18723) : ℂ) * ζ ^ 13 - ((214474 / 93615) : ℂ) * ζ ^ 15 + ((29299 / 18723) : ℂ) * ζ ^ 17 + ((11364 / 6241) : ℂ) * ζ ^ 18 + ((29299 / 18723) : ℂ) * ζ ^ 21 + ((61685 / 18723) : ℂ) * ζ ^ 22 - ((61685 / 18723) : ℂ) * ζ ^ 24 - ((29299 / 18723) : ℂ) * ζ ^ 25 + ((165587 / 93615) : ℂ) * ζ ^ 27 + ((26044 / 18723) : ℂ) * ζ ^ 28 - ((29299 / 18723) : ℂ) * ζ ^ 29 - ((29243 / 6241) : ℂ) * ζ ^ 30 - ((165587 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep04CoefficientIdentity06 :
    row18_reducedY11_combinationStep04Coefficient06 =
      row18_reducedY11_combinationStep03Coefficient06 +
        row18_reducedY11_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep04Coefficient06 row18_reducedY11_combinationStep03Coefficient06 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep04Coefficient07 : ℂ :=
  (((14396 / 18723) : ℂ) + ((25145 / 18723) : ℂ) * ζ ^ 1 - ((31688 / 18723) : ℂ) * ζ ^ 2 - ((10231 / 6241) : ℂ) * ζ ^ 3 + ((3382 / 6241) : ℂ) * ζ ^ 5 - ((5230 / 6241) : ℂ) * ζ ^ 6 - ((36037 / 18723) : ℂ) * ζ ^ 8 - ((28697 / 18723) : ℂ) * ζ ^ 9 + ((1996 / 18723) : ℂ) * ζ ^ 11 - ((36037 / 18723) : ℂ) * ζ ^ 12 - ((25145 / 18723) : ℂ) * ζ ^ 13 + ((15694 / 18723) : ℂ) * ζ ^ 15 - ((25145 / 18723) : ℂ) * ζ ^ 17 - ((15998 / 18723) : ℂ) * ζ ^ 18 + ((5548 / 18723) : ℂ) * ζ ^ 21 + ((31688 / 18723) : ℂ) * ζ ^ 22 + ((14999 / 18723) : ℂ) * ζ ^ 25 - ((5548 / 18723) : ℂ) * ζ ^ 27 + ((36037 / 18723) : ℂ) * ζ ^ 28 + ((25145 / 18723) : ℂ) * ζ ^ 29 - ((2615 / 6241) : ℂ) * ζ ^ 30 - ((1996 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep04CoefficientIdentity07 :
    row18_reducedY11_combinationStep04Coefficient07 =
      row18_reducedY11_combinationStep03Coefficient07 +
        row18_reducedY11_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep04Coefficient07 row18_reducedY11_combinationStep03Coefficient07 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep04Coefficient08 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep04CoefficientIdentity08 :
    row18_reducedY11_combinationStep04Coefficient08 =
      row18_reducedY11_combinationStep03Coefficient08 +
        row18_reducedY11_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep04Coefficient08 row18_reducedY11_combinationStep03Coefficient08 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep04Coefficient09 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep04CoefficientIdentity09 :
    row18_reducedY11_combinationStep04Coefficient09 =
      row18_reducedY11_combinationStep03Coefficient09 +
        row18_reducedY11_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep04Coefficient09 row18_reducedY11_combinationStep03Coefficient09 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep04Coefficient10 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep04CoefficientIdentity10 :
    row18_reducedY11_combinationStep04Coefficient10 =
      row18_reducedY11_combinationStep03Coefficient10 +
        row18_reducedY11_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep04Coefficient10 row18_reducedY11_combinationStep03Coefficient10 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep04Coefficient11 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep04CoefficientIdentity11 :
    row18_reducedY11_combinationStep04Coefficient11 =
      row18_reducedY11_combinationStep03Coefficient11 +
        row18_reducedY11_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep04Coefficient11 row18_reducedY11_combinationStep03Coefficient11 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep04Coefficient12 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep04CoefficientIdentity12 :
    row18_reducedY11_combinationStep04Coefficient12 =
      row18_reducedY11_combinationStep03Coefficient12 +
        row18_reducedY11_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep04Coefficient12 row18_reducedY11_combinationStep03Coefficient12 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep04Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep04CoefficientIdentity13 :
    row18_reducedY11_combinationStep04Coefficient13 =
      row18_reducedY11_combinationStep03Coefficient13 +
        row18_reducedY11_combinationStep04Multiplier *
          (-((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((73 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((105 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((73 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep04Coefficient13 row18_reducedY11_combinationStep03Coefficient13 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 (-((3276 / 6241) : ℂ) - ((625 / 12482) : ℂ) * ζ ^ 1 + ((689 / 6241) : ℂ) * ζ ^ 2 - ((3167 / 12482) : ℂ) * ζ ^ 3 - ((1285 / 12482) : ℂ) * ζ ^ 4 - ((117 / 6241) : ℂ) * ζ ^ 5 + ((5201 / 12482) : ℂ) * ζ ^ 6 + ((3018 / 6241) : ℂ) * ζ ^ 7 + ((4811 / 12482) : ℂ) * ζ ^ 8 - ((784 / 6241) : ℂ) * ζ ^ 9 - ((8487 / 6241) : ℂ) * ζ ^ 10 - ((4803 / 12482) : ℂ) * ζ ^ 11 + ((6691 / 12482) : ℂ) * ζ ^ 12 + ((178 / 6241) : ℂ) * ζ ^ 13 + ((6775 / 6241) : ℂ) * ζ ^ 14 - ((4021 / 12482) : ℂ) * ζ ^ 15 - ((19101 / 12482) : ℂ) * ζ ^ 16 - ((4973 / 12482) : ℂ) * ζ ^ 17 - ((4376 / 6241) : ℂ) * ζ ^ 18 + ((66 / 6241) : ℂ) * ζ ^ 19 + ((8447 / 12482) : ℂ) * ζ ^ 20 + ((551 / 6241) : ℂ) * ζ ^ 21 - ((119 / 6241) : ℂ) * ζ ^ 22 + ((550 / 6241) : ℂ) * ζ ^ 23 - ((2929 / 12482) : ℂ) * ζ ^ 24 + ((445 / 12482) : ℂ) * ζ ^ 25 + ((1398 / 6241) : ℂ) * ζ ^ 26 + ((1144 / 6241) : ℂ) * ζ ^ 27 + ((2973 / 12482) : ℂ) * ζ ^ 28 + ((1083 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep04Coefficient14 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep04CoefficientIdentity14 :
    row18_reducedY11_combinationStep04Coefficient14 =
      row18_reducedY11_combinationStep03Coefficient14 +
        row18_reducedY11_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep04Coefficient14 row18_reducedY11_combinationStep03Coefficient14 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep04Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep04CoefficientIdentity15 :
    row18_reducedY11_combinationStep04Coefficient15 =
      row18_reducedY11_combinationStep03Coefficient15 +
        row18_reducedY11_combinationStep04Multiplier *
          (((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep04Coefficient15 row18_reducedY11_combinationStep03Coefficient15 row18_reducedY11_combinationStep04Multiplier
  close_cyclotomic_row18 (((2474 / 6241) : ℂ) - ((6163 / 12482) : ℂ) * ζ ^ 1 - ((3250 / 6241) : ℂ) * ζ ^ 2 + ((1919 / 6241) : ℂ) * ζ ^ 3 - ((7587 / 12482) : ℂ) * ζ ^ 4 + ((3018 / 6241) : ℂ) * ζ ^ 5 + ((1520 / 6241) : ℂ) * ζ ^ 6 - ((3459 / 6241) : ℂ) * ζ ^ 7 + ((315 / 12482) : ℂ) * ζ ^ 8 + ((1635 / 12482) : ℂ) * ζ ^ 9 - ((2433 / 12482) : ℂ) * ζ ^ 10 - ((203 / 12482) : ℂ) * ζ ^ 11 + ((1748 / 6241) : ℂ) * ζ ^ 12 - ((1205 / 6241) : ℂ) * ζ ^ 13 + ((837 / 12482) : ℂ) * ζ ^ 14 - ((894 / 6241) : ℂ) * ζ ^ 15 - ((247 / 12482) : ℂ) * ζ ^ 16 - ((163 / 6241) : ℂ) * ζ ^ 17 - ((1985 / 12482) : ℂ) * ζ ^ 18 + ((1125 / 6241) : ℂ) * ζ ^ 19 - ((871 / 12482) : ℂ) * ζ ^ 20 - ((706 / 6241) : ℂ) * ζ ^ 21 + ((3236 / 6241) : ℂ) * ζ ^ 22 - ((2 / 79) : ℂ) * ζ ^ 23 + ((710 / 6241) : ℂ) * ζ ^ 24 - ((240 / 6241) : ℂ) * ζ ^ 25 - ((10525 / 12482) : ℂ) * ζ ^ 26 + ((162 / 6241) : ℂ) * ζ ^ 27 + ((3337 / 12482) : ℂ) * ζ ^ 28 + ((741 / 12482) : ℂ) * ζ ^ 29 - ((705 / 12482) : ℂ) * ζ ^ 30)

private theorem row18_reducedY11_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY11_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY11_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY11_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY11_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY11_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY11_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY11_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY11_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY11_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY11_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY11_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY11_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY11_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY11_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY11_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY11_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY11_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation07
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY11_combinationStep04CoefficientIdentity00,
      row18_reducedY11_combinationStep04CoefficientIdentity01,
      row18_reducedY11_combinationStep04CoefficientIdentity02,
      row18_reducedY11_combinationStep04CoefficientIdentity03,
      row18_reducedY11_combinationStep04CoefficientIdentity04,
      row18_reducedY11_combinationStep04CoefficientIdentity05,
      row18_reducedY11_combinationStep04CoefficientIdentity06,
      row18_reducedY11_combinationStep04CoefficientIdentity07,
      row18_reducedY11_combinationStep04CoefficientIdentity08,
      row18_reducedY11_combinationStep04CoefficientIdentity09,
      row18_reducedY11_combinationStep04CoefficientIdentity10,
      row18_reducedY11_combinationStep04CoefficientIdentity11,
      row18_reducedY11_combinationStep04CoefficientIdentity12,
      row18_reducedY11_combinationStep04CoefficientIdentity13,
      row18_reducedY11_combinationStep04CoefficientIdentity14,
      row18_reducedY11_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY11_combinationStep04Multiplier * equation

private def row18_reducedY11_combinationStep05Multiplier : ℂ :=
  (-((387898 / 93615) : ℂ) - ((256226 / 93615) : ℂ) * ζ ^ 1 + ((343486 / 93615) : ℂ) * ζ ^ 2 + ((18840 / 6241) : ℂ) * ζ ^ 3 - ((95136 / 31205) : ℂ) * ζ ^ 5 - ((30886 / 93615) : ℂ) * ζ ^ 6 + ((159598 / 31205) : ℂ) * ζ ^ 8 + ((113522 / 93615) : ℂ) * ζ ^ 9 - ((38926 / 18723) : ℂ) * ζ ^ 11 + ((374372 / 93615) : ℂ) * ζ ^ 12 + ((256226 / 93615) : ℂ) * ζ ^ 13 - ((18840 / 6241) : ℂ) * ζ ^ 15 + ((256226 / 93615) : ℂ) * ζ ^ 17 + ((14804 / 31205) : ℂ) * ζ ^ 18 + ((29182 / 93615) : ℂ) * ζ ^ 21 - ((343486 / 93615) : ℂ) * ζ ^ 22 - ((343486 / 93615) : ℂ) * ζ ^ 24 + ((29182 / 93615) : ℂ) * ζ ^ 25 + ((38926 / 18723) : ℂ) * ζ ^ 27 - ((159598 / 31205) : ℂ) * ζ ^ 28 - ((256226 / 93615) : ℂ) * ζ ^ 29 - ((135308 / 93615) : ℂ) * ζ ^ 30 + ((38926 / 18723) : ℂ) * ζ ^ 31)

private def row18_reducedY11_combinationStep05Coefficient00 : ℂ :=
  (((171 / 79) : ℂ) - ((1506 / 395) : ℂ) * ζ ^ 1 + ((2949 / 395) : ℂ) * ζ ^ 2 + ((1079 / 395) : ℂ) * ζ ^ 3 + ((1402 / 395) : ℂ) * ζ ^ 5 + ((3246 / 395) : ℂ) * ζ ^ 6 + ((469 / 79) : ℂ) * ζ ^ 8 + ((3362 / 395) : ℂ) * ζ ^ 9 + ((2283 / 395) : ℂ) * ζ ^ 11 + ((469 / 79) : ℂ) * ζ ^ 12 + ((1506 / 395) : ℂ) * ζ ^ 13 + ((1829 / 395) : ℂ) * ζ ^ 15 + ((1506 / 395) : ℂ) * ζ ^ 17 - ((297 / 395) : ℂ) * ζ ^ 18 + ((427 / 395) : ℂ) * ζ ^ 21 - ((2949 / 395) : ℂ) * ζ ^ 22 - ((2908 / 395) : ℂ) * ζ ^ 25 - ((427 / 395) : ℂ) * ζ ^ 27 - ((469 / 79) : ℂ) * ζ ^ 28 - ((1506 / 395) : ℂ) * ζ ^ 29 + ((1623 / 395) : ℂ) * ζ ^ 30 - ((2283 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep05CoefficientIdentity00 :
    row18_reducedY11_combinationStep05Coefficient00 =
      row18_reducedY11_combinationStep04Coefficient00 +
        row18_reducedY11_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep05Coefficient00 row18_reducedY11_combinationStep04Coefficient00 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep05Coefficient01 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep05CoefficientIdentity01 :
    row18_reducedY11_combinationStep05Coefficient01 =
      row18_reducedY11_combinationStep04Coefficient01 +
        row18_reducedY11_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep05Coefficient01 row18_reducedY11_combinationStep04Coefficient01 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep05Coefficient02 : ℂ :=
  (((266972 / 93615) : ℂ) - ((115672 / 93615) : ℂ) * ζ ^ 1 - ((790783 / 187230) : ℂ) * ζ ^ 2 + ((114101 / 37446) : ℂ) * ζ ^ 3 - ((885871 / 93615) : ℂ) * ζ ^ 5 - ((225667 / 187230) : ℂ) * ζ ^ 6 - ((537271 / 93615) : ℂ) * ζ ^ 8 - ((654527 / 187230) : ℂ) * ζ ^ 9 - ((328783 / 37446) : ℂ) * ζ ^ 11 - ((94186 / 31205) : ℂ) * ζ ^ 12 + ((115672 / 93615) : ℂ) * ζ ^ 13 - ((114101 / 37446) : ℂ) * ζ ^ 15 + ((115672 / 93615) : ℂ) * ζ ^ 17 + ((85613 / 62410) : ℂ) * ζ ^ 18 + ((256733 / 31205) : ℂ) * ζ ^ 21 + ((790783 / 187230) : ℂ) * ζ ^ 22 + ((790783 / 187230) : ℂ) * ζ ^ 24 + ((256733 / 31205) : ℂ) * ζ ^ 25 + ((328783 / 37446) : ℂ) * ζ ^ 27 + ((537271 / 93615) : ℂ) * ζ ^ 28 - ((115672 / 93615) : ℂ) * ζ ^ 29 + ((283759 / 187230) : ℂ) * ζ ^ 30 + ((328783 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep05CoefficientIdentity02 :
    row18_reducedY11_combinationStep05Coefficient02 =
      row18_reducedY11_combinationStep04Coefficient02 +
        row18_reducedY11_combinationStep05Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep05Coefficient02 row18_reducedY11_combinationStep04Coefficient02 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 (((2249699 / 4930390) : ℂ) + ((1992919 / 7395585) : ℂ) * ζ ^ 1 + ((10444639 / 7395585) : ℂ) * ζ ^ 2 + ((43599 / 986078) : ℂ) * ζ ^ 3 - ((10024589 / 7395585) : ℂ) * ζ ^ 4 - ((70325 / 986078) : ℂ) * ζ ^ 5 - ((1947161 / 4930390) : ℂ) * ζ ^ 6 + ((12142481 / 14791170) : ℂ) * ζ ^ 7 + ((6270703 / 14791170) : ℂ) * ζ ^ 8 - ((736723 / 2958234) : ℂ) * ζ ^ 9 - ((603859 / 2465195) : ℂ) * ζ ^ 10 + ((4510993 / 14791170) : ℂ) * ζ ^ 11 - ((18051 / 31205) : ℂ) * ζ ^ 12 - ((1208552 / 7395585) : ℂ) * ζ ^ 13 + ((7691063 / 14791170) : ℂ) * ζ ^ 14 + ((4996313 / 14791170) : ℂ) * ζ ^ 15 + ((8729071 / 14791170) : ℂ) * ζ ^ 16 + ((884966 / 7395585) : ℂ) * ζ ^ 17 - ((498763 / 1479117) : ℂ) * ζ ^ 18 - ((1438616 / 2465195) : ℂ) * ζ ^ 19 - ((1830551 / 4930390) : ℂ) * ζ ^ 20 - ((5632637 / 14791170) : ℂ) * ζ ^ 21 - ((190800 / 493039) : ℂ) * ζ ^ 22 - ((1146739 / 2958234) : ℂ) * ζ ^ 23 + ((5274134 / 7395585) : ℂ) * ζ ^ 24 + ((319707 / 2465195) : ℂ) * ζ ^ 25 + ((3027047 / 7395585) : ℂ) * ζ ^ 26 - ((1817323 / 4930390) : ℂ) * ζ ^ 27 + ((359347 / 14791170) : ℂ) * ζ ^ 28 - ((417366 / 2465195) : ℂ) * ζ ^ 29 + ((136241 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep05Coefficient03 : ℂ :=
  (-((6575 / 18723) : ℂ) - ((30833 / 18723) : ℂ) * ζ ^ 1 + ((58873 / 37446) : ℂ) * ζ ^ 2 + ((26545 / 12482) : ℂ) * ζ ^ 3 - ((5263 / 12482) : ℂ) * ζ ^ 5 + ((5388 / 6241) : ℂ) * ζ ^ 6 + ((73259 / 37446) : ℂ) * ζ ^ 8 + ((79909 / 37446) : ℂ) * ζ ^ 9 + ((137 / 18723) : ℂ) * ζ ^ 11 + ((73259 / 37446) : ℂ) * ζ ^ 12 + ((30833 / 18723) : ℂ) * ζ ^ 13 - ((16879 / 18723) : ℂ) * ζ ^ 15 + ((30833 / 18723) : ℂ) * ζ ^ 17 + ((26545 / 37446) : ℂ) * ζ ^ 18 - ((17969 / 37446) : ℂ) * ζ ^ 21 - ((58873 / 37446) : ℂ) * ζ ^ 22 - ((45877 / 37446) : ℂ) * ζ ^ 25 + ((17969 / 37446) : ℂ) * ζ ^ 27 - ((73259 / 37446) : ℂ) * ζ ^ 28 - ((30833 / 18723) : ℂ) * ζ ^ 29 + ((2694 / 6241) : ℂ) * ζ ^ 30 - ((137 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep05CoefficientIdentity03 :
    row18_reducedY11_combinationStep05Coefficient03 =
      row18_reducedY11_combinationStep04Coefficient03 +
        row18_reducedY11_combinationStep05Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep05Coefficient03 row18_reducedY11_combinationStep04Coefficient03 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 (-((12435923 / 7395585) : ℂ) + ((10468414 / 7395585) : ℂ) * ζ ^ 1 - ((6853169 / 14791170) : ℂ) * ζ ^ 2 - ((3383956 / 2465195) : ℂ) * ζ ^ 3 + ((2215219 / 2958234) : ℂ) * ζ ^ 4 - ((3065181 / 2465195) : ℂ) * ζ ^ 5 - ((2854649 / 2958234) : ℂ) * ζ ^ 6 - ((709819 / 2465195) : ℂ) * ζ ^ 7 - ((2042467 / 14791170) : ℂ) * ζ ^ 8 - ((18954749 / 14791170) : ℂ) * ζ ^ 9 - ((276293 / 7395585) : ℂ) * ζ ^ 10 - ((3044371 / 2958234) : ℂ) * ζ ^ 11 - ((3188743 / 14791170) : ℂ) * ζ ^ 12 - ((3103838 / 7395585) : ℂ) * ζ ^ 13 - ((5326841 / 2465195) : ℂ) * ζ ^ 14 - ((1620241 / 4930390) : ℂ) * ζ ^ 15 + ((2100985 / 2958234) : ℂ) * ζ ^ 16 - ((10250411 / 7395585) : ℂ) * ζ ^ 17 - ((23026523 / 14791170) : ℂ) * ζ ^ 18 + ((206767 / 1479117) : ℂ) * ζ ^ 19 - ((1853692 / 1479117) : ℂ) * ζ ^ 20 - ((13311889 / 14791170) : ℂ) * ζ ^ 21 - ((5625169 / 7395585) : ℂ) * ζ ^ 22 + ((12500237 / 14791170) : ℂ) * ζ ^ 23 - ((7094701 / 7395585) : ℂ) * ζ ^ 24 + ((10694201 / 14791170) : ℂ) * ζ ^ 25 - ((435755 / 986078) : ℂ) * ζ ^ 26 + ((3310897 / 14791170) : ℂ) * ζ ^ 27 - ((1359056 / 1479117) : ℂ) * ζ ^ 28 + ((2187754 / 7395585) : ℂ) * ζ ^ 29 + ((253019 / 2958234) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep05Coefficient04 : ℂ :=
  (-((171 / 79) : ℂ) + ((1506 / 395) : ℂ) * ζ ^ 1 - ((2949 / 395) : ℂ) * ζ ^ 2 - ((1079 / 395) : ℂ) * ζ ^ 3 - ((1402 / 395) : ℂ) * ζ ^ 5 - ((3246 / 395) : ℂ) * ζ ^ 6 - ((469 / 79) : ℂ) * ζ ^ 8 - ((3362 / 395) : ℂ) * ζ ^ 9 - ((2283 / 395) : ℂ) * ζ ^ 11 - ((469 / 79) : ℂ) * ζ ^ 12 - ((1506 / 395) : ℂ) * ζ ^ 13 - ((1829 / 395) : ℂ) * ζ ^ 15 - ((1506 / 395) : ℂ) * ζ ^ 17 + ((297 / 395) : ℂ) * ζ ^ 18 - ((427 / 395) : ℂ) * ζ ^ 21 + ((2949 / 395) : ℂ) * ζ ^ 22 + ((2908 / 395) : ℂ) * ζ ^ 25 + ((427 / 395) : ℂ) * ζ ^ 27 + ((469 / 79) : ℂ) * ζ ^ 28 + ((1506 / 395) : ℂ) * ζ ^ 29 - ((1623 / 395) : ℂ) * ζ ^ 30 + ((2283 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep05CoefficientIdentity04 :
    row18_reducedY11_combinationStep05Coefficient04 =
      row18_reducedY11_combinationStep04Coefficient04 +
        row18_reducedY11_combinationStep05Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep05Coefficient04 row18_reducedY11_combinationStep04Coefficient04 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 (((12435923 / 7395585) : ℂ) - ((10468414 / 7395585) : ℂ) * ζ ^ 1 + ((6853169 / 14791170) : ℂ) * ζ ^ 2 + ((3383956 / 2465195) : ℂ) * ζ ^ 3 - ((2215219 / 2958234) : ℂ) * ζ ^ 4 + ((3065181 / 2465195) : ℂ) * ζ ^ 5 + ((2854649 / 2958234) : ℂ) * ζ ^ 6 + ((709819 / 2465195) : ℂ) * ζ ^ 7 + ((2042467 / 14791170) : ℂ) * ζ ^ 8 + ((18954749 / 14791170) : ℂ) * ζ ^ 9 + ((276293 / 7395585) : ℂ) * ζ ^ 10 + ((3044371 / 2958234) : ℂ) * ζ ^ 11 + ((3188743 / 14791170) : ℂ) * ζ ^ 12 + ((3103838 / 7395585) : ℂ) * ζ ^ 13 + ((5326841 / 2465195) : ℂ) * ζ ^ 14 + ((1620241 / 4930390) : ℂ) * ζ ^ 15 - ((2100985 / 2958234) : ℂ) * ζ ^ 16 + ((10250411 / 7395585) : ℂ) * ζ ^ 17 + ((23026523 / 14791170) : ℂ) * ζ ^ 18 - ((206767 / 1479117) : ℂ) * ζ ^ 19 + ((1853692 / 1479117) : ℂ) * ζ ^ 20 + ((13311889 / 14791170) : ℂ) * ζ ^ 21 + ((5625169 / 7395585) : ℂ) * ζ ^ 22 - ((12500237 / 14791170) : ℂ) * ζ ^ 23 + ((7094701 / 7395585) : ℂ) * ζ ^ 24 - ((10694201 / 14791170) : ℂ) * ζ ^ 25 + ((435755 / 986078) : ℂ) * ζ ^ 26 - ((3310897 / 14791170) : ℂ) * ζ ^ 27 + ((1359056 / 1479117) : ℂ) * ζ ^ 28 - ((2187754 / 7395585) : ℂ) * ζ ^ 29 - ((253019 / 2958234) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep05Coefficient05 : ℂ :=
  (-((10481 / 18723) : ℂ) + ((17585 / 12482) : ℂ) * ζ ^ 1 - ((207581 / 37446) : ℂ) * ζ ^ 2 - ((166601 / 37446) : ℂ) * ζ ^ 5 - ((186619 / 37446) : ℂ) * ζ ^ 6 - ((186619 / 37446) : ℂ) * ζ ^ 8 - ((166601 / 37446) : ℂ) * ζ ^ 9 - ((207679 / 37446) : ℂ) * ζ ^ 11 - ((63343 / 18723) : ℂ) * ζ ^ 12 - ((17585 / 12482) : ℂ) * ζ ^ 13 - ((114439 / 37446) : ℂ) * ζ ^ 15 - ((17585 / 12482) : ℂ) * ζ ^ 17 + ((44947 / 18723) : ℂ) * ζ ^ 18 + ((56923 / 37446) : ℂ) * ζ ^ 21 + ((207581 / 37446) : ℂ) * ζ ^ 22 + ((96725 / 37446) : ℂ) * ζ ^ 24 + ((109678 / 18723) : ℂ) * ζ ^ 25 + ((114439 / 37446) : ℂ) * ζ ^ 27 + ((186619 / 37446) : ℂ) * ζ ^ 28 + ((17585 / 12482) : ℂ) * ζ ^ 29 - ((59933 / 37446) : ℂ) * ζ ^ 30 + ((207679 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep05CoefficientIdentity05 :
    row18_reducedY11_combinationStep05Coefficient05 =
      row18_reducedY11_combinationStep04Coefficient05 +
        row18_reducedY11_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep05Coefficient05 row18_reducedY11_combinationStep04Coefficient05 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep05Coefficient06 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep05CoefficientIdentity06 :
    row18_reducedY11_combinationStep05Coefficient06 =
      row18_reducedY11_combinationStep04Coefficient06 +
        row18_reducedY11_combinationStep05Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep05Coefficient06 row18_reducedY11_combinationStep04Coefficient06 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 (-((7796051 / 7395585) : ℂ) - ((7991501 / 14791170) : ℂ) * ζ ^ 1 - ((9013042 / 7395585) : ℂ) * ζ ^ 2 - ((44043079 / 14791170) : ℂ) * ζ ^ 3 - ((13958203 / 7395585) : ℂ) * ζ ^ 4 + ((11867771 / 7395585) : ℂ) * ζ ^ 5 + ((20384176 / 7395585) : ℂ) * ζ ^ 6 + ((8225902 / 2465195) : ℂ) * ζ ^ 7 - ((25181047 / 14791170) : ℂ) * ζ ^ 8 - ((13907999 / 2958234) : ℂ) * ζ ^ 9 - ((50176109 / 14791170) : ℂ) * ζ ^ 10 - ((10118993 / 4930390) : ℂ) * ζ ^ 11 + ((24417473 / 14791170) : ℂ) * ζ ^ 12 + ((23171951 / 7395585) : ℂ) * ζ ^ 13 + ((2142118 / 7395585) : ℂ) * ζ ^ 14 - ((7328759 / 4930390) : ℂ) * ζ ^ 15 - ((2892709 / 1479117) : ℂ) * ζ ^ 16 - ((58390201 / 14791170) : ℂ) * ζ ^ 17 - ((21121103 / 7395585) : ℂ) * ζ ^ 18 + ((229963 / 1479117) : ℂ) * ζ ^ 19 + ((22962176 / 7395585) : ℂ) * ζ ^ 20 + ((11541958 / 7395585) : ℂ) * ζ ^ 21 - ((11492449 / 14791170) : ℂ) * ζ ^ 22 - ((25128329 / 7395585) : ℂ) * ζ ^ 23 - ((5307957 / 4930390) : ℂ) * ζ ^ 24 + ((1407679 / 4930390) : ℂ) * ζ ^ 25 + ((26900027 / 14791170) : ℂ) * ζ ^ 26 + ((2077721 / 2465195) : ℂ) * ζ ^ 27 - ((67219 / 2958234) : ℂ) * ζ ^ 28 - ((220624 / 7395585) : ℂ) * ζ ^ 29 - ((272482 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep05Coefficient07 : ℂ :=
  (((14396 / 18723) : ℂ) + ((25145 / 18723) : ℂ) * ζ ^ 1 - ((31688 / 18723) : ℂ) * ζ ^ 2 - ((10231 / 6241) : ℂ) * ζ ^ 3 + ((3382 / 6241) : ℂ) * ζ ^ 5 - ((5230 / 6241) : ℂ) * ζ ^ 6 - ((36037 / 18723) : ℂ) * ζ ^ 8 - ((28697 / 18723) : ℂ) * ζ ^ 9 + ((1996 / 18723) : ℂ) * ζ ^ 11 - ((36037 / 18723) : ℂ) * ζ ^ 12 - ((25145 / 18723) : ℂ) * ζ ^ 13 + ((15694 / 18723) : ℂ) * ζ ^ 15 - ((25145 / 18723) : ℂ) * ζ ^ 17 - ((15998 / 18723) : ℂ) * ζ ^ 18 + ((5548 / 18723) : ℂ) * ζ ^ 21 + ((31688 / 18723) : ℂ) * ζ ^ 22 + ((14999 / 18723) : ℂ) * ζ ^ 25 - ((5548 / 18723) : ℂ) * ζ ^ 27 + ((36037 / 18723) : ℂ) * ζ ^ 28 + ((25145 / 18723) : ℂ) * ζ ^ 29 - ((2615 / 6241) : ℂ) * ζ ^ 30 - ((1996 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep05CoefficientIdentity07 :
    row18_reducedY11_combinationStep05Coefficient07 =
      row18_reducedY11_combinationStep04Coefficient07 +
        row18_reducedY11_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep05Coefficient07 row18_reducedY11_combinationStep04Coefficient07 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep05Coefficient08 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep05CoefficientIdentity08 :
    row18_reducedY11_combinationStep05Coefficient08 =
      row18_reducedY11_combinationStep04Coefficient08 +
        row18_reducedY11_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep05Coefficient08 row18_reducedY11_combinationStep04Coefficient08 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep05Coefficient09 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep05CoefficientIdentity09 :
    row18_reducedY11_combinationStep05Coefficient09 =
      row18_reducedY11_combinationStep04Coefficient09 +
        row18_reducedY11_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep05Coefficient09 row18_reducedY11_combinationStep04Coefficient09 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep05Coefficient10 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep05CoefficientIdentity10 :
    row18_reducedY11_combinationStep05Coefficient10 =
      row18_reducedY11_combinationStep04Coefficient10 +
        row18_reducedY11_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep05Coefficient10 row18_reducedY11_combinationStep04Coefficient10 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep05Coefficient11 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep05CoefficientIdentity11 :
    row18_reducedY11_combinationStep05Coefficient11 =
      row18_reducedY11_combinationStep04Coefficient11 +
        row18_reducedY11_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep05Coefficient11 row18_reducedY11_combinationStep04Coefficient11 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep05Coefficient12 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep05CoefficientIdentity12 :
    row18_reducedY11_combinationStep05Coefficient12 =
      row18_reducedY11_combinationStep04Coefficient12 +
        row18_reducedY11_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep05Coefficient12 row18_reducedY11_combinationStep04Coefficient12 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep05Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep05CoefficientIdentity13 :
    row18_reducedY11_combinationStep05Coefficient13 =
      row18_reducedY11_combinationStep04Coefficient13 +
        row18_reducedY11_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep05Coefficient13 row18_reducedY11_combinationStep04Coefficient13 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep05Coefficient14 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep05CoefficientIdentity14 :
    row18_reducedY11_combinationStep05Coefficient14 =
      row18_reducedY11_combinationStep04Coefficient14 +
        row18_reducedY11_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep05Coefficient14 row18_reducedY11_combinationStep04Coefficient14 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep05Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep05CoefficientIdentity15 :
    row18_reducedY11_combinationStep05Coefficient15 =
      row18_reducedY11_combinationStep04Coefficient15 +
        row18_reducedY11_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep05Coefficient15 row18_reducedY11_combinationStep04Coefficient15 row18_reducedY11_combinationStep05Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY11_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY11_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY11_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY11_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY11_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY11_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY11_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY11_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY11_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY11_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY11_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY11_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY11_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY11_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY11_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY11_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY11_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY11_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY11_combinationStep05CoefficientIdentity00,
      row18_reducedY11_combinationStep05CoefficientIdentity01,
      row18_reducedY11_combinationStep05CoefficientIdentity02,
      row18_reducedY11_combinationStep05CoefficientIdentity03,
      row18_reducedY11_combinationStep05CoefficientIdentity04,
      row18_reducedY11_combinationStep05CoefficientIdentity05,
      row18_reducedY11_combinationStep05CoefficientIdentity06,
      row18_reducedY11_combinationStep05CoefficientIdentity07,
      row18_reducedY11_combinationStep05CoefficientIdentity08,
      row18_reducedY11_combinationStep05CoefficientIdentity09,
      row18_reducedY11_combinationStep05CoefficientIdentity10,
      row18_reducedY11_combinationStep05CoefficientIdentity11,
      row18_reducedY11_combinationStep05CoefficientIdentity12,
      row18_reducedY11_combinationStep05CoefficientIdentity13,
      row18_reducedY11_combinationStep05CoefficientIdentity14,
      row18_reducedY11_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY11_combinationStep05Multiplier * equation

private def row18_reducedY11_combinationStep06Multiplier : ℂ :=
  (((31750 / 18723) : ℂ) + ((35584 / 18723) : ℂ) * ζ ^ 1 - ((17598 / 6241) : ℂ) * ζ ^ 2 - ((63278 / 18723) : ℂ) * ζ ^ 3 + ((97456 / 18723) : ℂ) * ζ ^ 5 - ((63434 / 18723) : ℂ) * ζ ^ 8 - ((24010 / 18723) : ℂ) * ζ ^ 9 + ((29096 / 6241) : ℂ) * ζ ^ 11 - ((22 / 6241) : ℂ) * ζ ^ 12 - ((35584 / 18723) : ℂ) * ζ ^ 13 + ((1406 / 18723) : ℂ) * ζ ^ 15 - ((35584 / 18723) : ℂ) * ζ ^ 17 + ((17598 / 6241) : ℂ) * ζ ^ 18 - ((32954 / 6241) : ℂ) * ζ ^ 21 + ((17598 / 6241) : ℂ) * ζ ^ 22 + ((63500 / 18723) : ℂ) * ζ ^ 24 - ((20624 / 6241) : ℂ) * ζ ^ 25 - ((32954 / 6241) : ℂ) * ζ ^ 27 + ((63434 / 18723) : ℂ) * ζ ^ 28 + ((35584 / 18723) : ℂ) * ζ ^ 29 + ((9802 / 18723) : ℂ) * ζ ^ 30 - ((29096 / 6241) : ℂ) * ζ ^ 31)

private def row18_reducedY11_combinationStep06Coefficient00 : ℂ :=
  (((171 / 79) : ℂ) - ((1506 / 395) : ℂ) * ζ ^ 1 + ((2949 / 395) : ℂ) * ζ ^ 2 + ((1079 / 395) : ℂ) * ζ ^ 3 + ((1402 / 395) : ℂ) * ζ ^ 5 + ((3246 / 395) : ℂ) * ζ ^ 6 + ((469 / 79) : ℂ) * ζ ^ 8 + ((3362 / 395) : ℂ) * ζ ^ 9 + ((2283 / 395) : ℂ) * ζ ^ 11 + ((469 / 79) : ℂ) * ζ ^ 12 + ((1506 / 395) : ℂ) * ζ ^ 13 + ((1829 / 395) : ℂ) * ζ ^ 15 + ((1506 / 395) : ℂ) * ζ ^ 17 - ((297 / 395) : ℂ) * ζ ^ 18 + ((427 / 395) : ℂ) * ζ ^ 21 - ((2949 / 395) : ℂ) * ζ ^ 22 - ((2908 / 395) : ℂ) * ζ ^ 25 - ((427 / 395) : ℂ) * ζ ^ 27 - ((469 / 79) : ℂ) * ζ ^ 28 - ((1506 / 395) : ℂ) * ζ ^ 29 + ((1623 / 395) : ℂ) * ζ ^ 30 - ((2283 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep06CoefficientIdentity00 :
    row18_reducedY11_combinationStep06Coefficient00 =
      row18_reducedY11_combinationStep05Coefficient00 +
        row18_reducedY11_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep06Coefficient00 row18_reducedY11_combinationStep05Coefficient00 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep06Coefficient01 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep06CoefficientIdentity01 :
    row18_reducedY11_combinationStep06Coefficient01 =
      row18_reducedY11_combinationStep05Coefficient01 +
        row18_reducedY11_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep06Coefficient01 row18_reducedY11_combinationStep05Coefficient01 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep06Coefficient02 : ℂ :=
  (((1056 / 395) : ℂ) - ((596 / 395) : ℂ) * ζ ^ 1 - ((5289 / 790) : ℂ) * ζ ^ 2 + ((477 / 158) : ℂ) * ζ ^ 3 - ((2903 / 395) : ℂ) * ζ ^ 5 - ((2451 / 790) : ℂ) * ζ ^ 6 - ((3178 / 395) : ℂ) * ζ ^ 8 - ((1711 / 790) : ℂ) * ζ ^ 9 - ((1041 / 158) : ℂ) * ζ ^ 11 - ((1419 / 395) : ℂ) * ζ ^ 12 + ((596 / 395) : ℂ) * ζ ^ 13 - ((477 / 158) : ℂ) * ζ ^ 15 + ((596 / 395) : ℂ) * ζ ^ 17 + ((3177 / 790) : ℂ) * ζ ^ 18 + ((2307 / 395) : ℂ) * ζ ^ 21 + ((5289 / 790) : ℂ) * ζ ^ 22 + ((5289 / 790) : ℂ) * ζ ^ 24 + ((2307 / 395) : ℂ) * ζ ^ 25 + ((1041 / 158) : ℂ) * ζ ^ 27 + ((3178 / 395) : ℂ) * ζ ^ 28 - ((596 / 395) : ℂ) * ζ ^ 29 + ((1067 / 790) : ℂ) * ζ ^ 30 + ((1041 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep06CoefficientIdentity02 :
    row18_reducedY11_combinationStep06Coefficient02 =
      row18_reducedY11_combinationStep05Coefficient02 +
        row18_reducedY11_combinationStep06Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep06Coefficient02 row18_reducedY11_combinationStep05Coefficient02 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 (((188495 / 493039) : ℂ) + ((1278049 / 2958234) : ℂ) * ζ ^ 1 + ((2083687 / 986078) : ℂ) * ζ ^ 2 - ((961301 / 2958234) : ℂ) * ζ ^ 3 - ((718519 / 1479117) : ℂ) * ζ ^ 4 - ((898877 / 493039) : ℂ) * ζ ^ 5 + ((27037 / 2958234) : ℂ) * ζ ^ 6 + ((2102237 / 2958234) : ℂ) * ζ ^ 7 + ((4051111 / 2958234) : ℂ) * ζ ^ 8 - ((681359 / 986078) : ℂ) * ζ ^ 9 - ((78482 / 1479117) : ℂ) * ζ ^ 10 - ((53150 / 493039) : ℂ) * ζ ^ 11 + ((297896 / 493039) : ℂ) * ζ ^ 12 - ((112367 / 986078) : ℂ) * ζ ^ 13 - ((215224 / 1479117) : ℂ) * ζ ^ 14 - ((2753743 / 2958234) : ℂ) * ζ ^ 15 + ((88333 / 2958234) : ℂ) * ζ ^ 16 + ((1562263 / 2958234) : ℂ) * ζ ^ 17 + ((1049179 / 986078) : ℂ) * ζ ^ 18 - ((81325 / 1479117) : ℂ) * ζ ^ 19 - ((1246564 / 1479117) : ℂ) * ζ ^ 20 - ((3432667 / 2958234) : ℂ) * ζ ^ 21 - ((1379 / 493039) : ℂ) * ζ ^ 22 + ((664229 / 986078) : ℂ) * ζ ^ 23 + ((1873477 / 1479117) : ℂ) * ζ ^ 24 + ((354071 / 986078) : ℂ) * ζ ^ 25 - ((1016204 / 1479117) : ℂ) * ζ ^ 26 - ((1984240 / 1479117) : ℂ) * ζ ^ 27 + ((10874 / 493039) : ℂ) * ζ ^ 28 + ((673799 / 986078) : ℂ) * ζ ^ 29 + ((109110 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep06Coefficient03 : ℂ :=
  (((33 / 79) : ℂ) - ((24 / 79) : ℂ) * ζ ^ 1 - ((19 / 158) : ℂ) * ζ ^ 2 + ((77 / 158) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((2 / 79) : ℂ) * ζ ^ 6 + ((5 / 158) : ℂ) * ζ ^ 8 + ((95 / 158) : ℂ) * ζ ^ 9 + ((9 / 79) : ℂ) * ζ ^ 11 + ((5 / 158) : ℂ) * ζ ^ 12 + ((24 / 79) : ℂ) * ζ ^ 13 - ((5 / 79) : ℂ) * ζ ^ 15 + ((24 / 79) : ℂ) * ζ ^ 17 - ((23 / 158) : ℂ) * ζ ^ 18 - ((29 / 158) : ℂ) * ζ ^ 21 + ((19 / 158) : ℂ) * ζ ^ 22 - ((67 / 158) : ℂ) * ζ ^ 25 + ((29 / 158) : ℂ) * ζ ^ 27 - ((5 / 158) : ℂ) * ζ ^ 28 - ((24 / 79) : ℂ) * ζ ^ 29 + ((1 / 79) : ℂ) * ζ ^ 30 - ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep06CoefficientIdentity03 :
    row18_reducedY11_combinationStep06Coefficient03 =
      row18_reducedY11_combinationStep05Coefficient03 +
        row18_reducedY11_combinationStep06Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep06Coefficient03 row18_reducedY11_combinationStep05Coefficient03 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 (-((294428 / 493039) : ℂ) - ((10543 / 12482) : ℂ) * ζ ^ 1 + ((7541519 / 2958234) : ℂ) * ζ ^ 2 + ((1880525 / 1479117) : ℂ) * ζ ^ 3 - ((2669996 / 1479117) : ℂ) * ζ ^ 4 + ((443009 / 986078) : ℂ) * ζ ^ 5 + ((947408 / 1479117) : ℂ) * ζ ^ 6 + ((152086 / 493039) : ℂ) * ζ ^ 7 + ((1487858 / 1479117) : ℂ) * ζ ^ 8 + ((822147 / 986078) : ℂ) * ζ ^ 9 - ((172333 / 1479117) : ℂ) * ζ ^ 10 - ((671443 / 986078) : ℂ) * ζ ^ 11 - ((141586 / 1479117) : ℂ) * ζ ^ 12 + ((77782 / 1479117) : ℂ) * ζ ^ 13 + ((4345439 / 1479117) : ℂ) * ζ ^ 14 + ((4391113 / 2958234) : ℂ) * ζ ^ 15 + ((53989 / 493039) : ℂ) * ζ ^ 16 - ((5395397 / 2958234) : ℂ) * ζ ^ 17 - ((3625295 / 1479117) : ℂ) * ζ ^ 18 - ((1645957 / 2958234) : ℂ) * ζ ^ 19 + ((4992159 / 986078) : ℂ) * ζ ^ 20 + ((1238393 / 493039) : ℂ) * ζ ^ 21 - ((1156915 / 1479117) : ℂ) * ζ ^ 22 - ((1460264 / 493039) : ℂ) * ζ ^ 23 - ((675329 / 986078) : ℂ) * ζ ^ 24 + ((362841 / 986078) : ℂ) * ζ ^ 25 + ((1253404 / 493039) : ℂ) * ζ ^ 26 + ((1070713 / 2958234) : ℂ) * ζ ^ 27 - ((935954 / 1479117) : ℂ) * ζ ^ 28 - ((455114 / 1479117) : ℂ) * ζ ^ 29 - ((203672 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep06Coefficient04 : ℂ :=
  (-((171 / 79) : ℂ) + ((1506 / 395) : ℂ) * ζ ^ 1 - ((2949 / 395) : ℂ) * ζ ^ 2 - ((1079 / 395) : ℂ) * ζ ^ 3 - ((1402 / 395) : ℂ) * ζ ^ 5 - ((3246 / 395) : ℂ) * ζ ^ 6 - ((469 / 79) : ℂ) * ζ ^ 8 - ((3362 / 395) : ℂ) * ζ ^ 9 - ((2283 / 395) : ℂ) * ζ ^ 11 - ((469 / 79) : ℂ) * ζ ^ 12 - ((1506 / 395) : ℂ) * ζ ^ 13 - ((1829 / 395) : ℂ) * ζ ^ 15 - ((1506 / 395) : ℂ) * ζ ^ 17 + ((297 / 395) : ℂ) * ζ ^ 18 - ((427 / 395) : ℂ) * ζ ^ 21 + ((2949 / 395) : ℂ) * ζ ^ 22 + ((2908 / 395) : ℂ) * ζ ^ 25 + ((427 / 395) : ℂ) * ζ ^ 27 + ((469 / 79) : ℂ) * ζ ^ 28 + ((1506 / 395) : ℂ) * ζ ^ 29 - ((1623 / 395) : ℂ) * ζ ^ 30 + ((2283 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep06CoefficientIdentity04 :
    row18_reducedY11_combinationStep06Coefficient04 =
      row18_reducedY11_combinationStep05Coefficient04 +
        row18_reducedY11_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep06Coefficient04 row18_reducedY11_combinationStep05Coefficient04 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep06Coefficient05 : ℂ :=
  (-((50 / 79) : ℂ) + ((148 / 79) : ℂ) * ζ ^ 1 - ((515 / 79) : ℂ) * ζ ^ 2 - ((496 / 79) : ℂ) * ζ ^ 5 - ((465 / 79) : ℂ) * ζ ^ 6 - ((465 / 79) : ℂ) * ζ ^ 8 - ((496 / 79) : ℂ) * ζ ^ 9 - ((614 / 79) : ℂ) * ζ ^ 11 - ((320 / 79) : ℂ) * ζ ^ 12 - ((148 / 79) : ℂ) * ζ ^ 13 - ((347 / 79) : ℂ) * ζ ^ 15 - ((148 / 79) : ℂ) * ζ ^ 17 + ((223 / 79) : ℂ) * ζ ^ 18 + ((174 / 79) : ℂ) * ζ ^ 21 + ((515 / 79) : ℂ) * ζ ^ 22 + ((242 / 79) : ℂ) * ζ ^ 24 + ((644 / 79) : ℂ) * ζ ^ 25 + ((347 / 79) : ℂ) * ζ ^ 27 + ((465 / 79) : ℂ) * ζ ^ 28 + ((148 / 79) : ℂ) * ζ ^ 29 - ((145 / 79) : ℂ) * ζ ^ 30 + ((614 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep06CoefficientIdentity05 :
    row18_reducedY11_combinationStep06Coefficient05 =
      row18_reducedY11_combinationStep05Coefficient05 +
        row18_reducedY11_combinationStep06Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep06Coefficient05 row18_reducedY11_combinationStep05Coefficient05 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 (-((879073 / 2958234) : ℂ) - ((626318 / 1479117) : ℂ) * ζ ^ 1 + ((2025543 / 986078) : ℂ) * ζ ^ 2 - ((316766 / 1479117) : ℂ) * ζ ^ 3 - ((2035261 / 2958234) : ℂ) * ζ ^ 4 + ((5622589 / 2958234) : ℂ) * ζ ^ 5 + ((915712 / 1479117) : ℂ) * ζ ^ 6 - ((3436541 / 2958234) : ℂ) * ζ ^ 7 + ((3117098 / 1479117) : ℂ) * ζ ^ 8 + ((142597 / 986078) : ℂ) * ζ ^ 9 - ((997901 / 1479117) : ℂ) * ζ ^ 10 + ((4124489 / 2958234) : ℂ) * ζ ^ 11 + ((729005 / 986078) : ℂ) * ζ ^ 12 + ((182647 / 1479117) : ℂ) * ζ ^ 13 + ((90065 / 1479117) : ℂ) * ζ ^ 14 + ((1007044 / 1479117) : ℂ) * ζ ^ 15 + ((99949 / 986078) : ℂ) * ζ ^ 16 + ((716302 / 493039) : ℂ) * ζ ^ 17 - ((706133 / 493039) : ℂ) * ζ ^ 18 + ((1106836 / 1479117) : ℂ) * ζ ^ 19 + ((553983 / 493039) : ℂ) * ζ ^ 20 + ((613381 / 2958234) : ℂ) * ζ ^ 21 - ((728923 / 493039) : ℂ) * ζ ^ 22 + ((3802792 / 1479117) : ℂ) * ζ ^ 23 - ((2210039 / 2958234) : ℂ) * ζ ^ 24 + ((822586 / 1479117) : ℂ) * ζ ^ 25 - ((158293 / 2958234) : ℂ) * ζ ^ 26 + ((1223864 / 1479117) : ℂ) * ζ ^ 27 - ((2102845 / 1479117) : ℂ) * ζ ^ 28 + ((2293063 / 2958234) : ℂ) * ζ ^ 29 + ((94562 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep06Coefficient06 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep06CoefficientIdentity06 :
    row18_reducedY11_combinationStep06Coefficient06 =
      row18_reducedY11_combinationStep05Coefficient06 +
        row18_reducedY11_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep06Coefficient06 row18_reducedY11_combinationStep05Coefficient06 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep06Coefficient07 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep06CoefficientIdentity07 :
    row18_reducedY11_combinationStep06Coefficient07 =
      row18_reducedY11_combinationStep05Coefficient07 +
        row18_reducedY11_combinationStep06Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep06Coefficient07 row18_reducedY11_combinationStep05Coefficient07 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 (((294428 / 493039) : ℂ) + ((10543 / 12482) : ℂ) * ζ ^ 1 - ((7541519 / 2958234) : ℂ) * ζ ^ 2 - ((1880525 / 1479117) : ℂ) * ζ ^ 3 + ((2669996 / 1479117) : ℂ) * ζ ^ 4 - ((443009 / 986078) : ℂ) * ζ ^ 5 - ((947408 / 1479117) : ℂ) * ζ ^ 6 - ((152086 / 493039) : ℂ) * ζ ^ 7 - ((1487858 / 1479117) : ℂ) * ζ ^ 8 - ((822147 / 986078) : ℂ) * ζ ^ 9 + ((172333 / 1479117) : ℂ) * ζ ^ 10 + ((671443 / 986078) : ℂ) * ζ ^ 11 + ((141586 / 1479117) : ℂ) * ζ ^ 12 - ((77782 / 1479117) : ℂ) * ζ ^ 13 - ((4345439 / 1479117) : ℂ) * ζ ^ 14 - ((4391113 / 2958234) : ℂ) * ζ ^ 15 - ((53989 / 493039) : ℂ) * ζ ^ 16 + ((5395397 / 2958234) : ℂ) * ζ ^ 17 + ((3625295 / 1479117) : ℂ) * ζ ^ 18 + ((1645957 / 2958234) : ℂ) * ζ ^ 19 - ((4992159 / 986078) : ℂ) * ζ ^ 20 - ((1238393 / 493039) : ℂ) * ζ ^ 21 + ((1156915 / 1479117) : ℂ) * ζ ^ 22 + ((1460264 / 493039) : ℂ) * ζ ^ 23 + ((675329 / 986078) : ℂ) * ζ ^ 24 - ((362841 / 986078) : ℂ) * ζ ^ 25 - ((1253404 / 493039) : ℂ) * ζ ^ 26 - ((1070713 / 2958234) : ℂ) * ζ ^ 27 + ((935954 / 1479117) : ℂ) * ζ ^ 28 + ((455114 / 1479117) : ℂ) * ζ ^ 29 + ((203672 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep06Coefficient08 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep06CoefficientIdentity08 :
    row18_reducedY11_combinationStep06Coefficient08 =
      row18_reducedY11_combinationStep05Coefficient08 +
        row18_reducedY11_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep06Coefficient08 row18_reducedY11_combinationStep05Coefficient08 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep06Coefficient09 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep06CoefficientIdentity09 :
    row18_reducedY11_combinationStep06Coefficient09 =
      row18_reducedY11_combinationStep05Coefficient09 +
        row18_reducedY11_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep06Coefficient09 row18_reducedY11_combinationStep05Coefficient09 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep06Coefficient10 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep06CoefficientIdentity10 :
    row18_reducedY11_combinationStep06Coefficient10 =
      row18_reducedY11_combinationStep05Coefficient10 +
        row18_reducedY11_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep06Coefficient10 row18_reducedY11_combinationStep05Coefficient10 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep06Coefficient11 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep06CoefficientIdentity11 :
    row18_reducedY11_combinationStep06Coefficient11 =
      row18_reducedY11_combinationStep05Coefficient11 +
        row18_reducedY11_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep06Coefficient11 row18_reducedY11_combinationStep05Coefficient11 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep06Coefficient12 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep06CoefficientIdentity12 :
    row18_reducedY11_combinationStep06Coefficient12 =
      row18_reducedY11_combinationStep05Coefficient12 +
        row18_reducedY11_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep06Coefficient12 row18_reducedY11_combinationStep05Coefficient12 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep06Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep06CoefficientIdentity13 :
    row18_reducedY11_combinationStep06Coefficient13 =
      row18_reducedY11_combinationStep05Coefficient13 +
        row18_reducedY11_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep06Coefficient13 row18_reducedY11_combinationStep05Coefficient13 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep06Coefficient14 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep06CoefficientIdentity14 :
    row18_reducedY11_combinationStep06Coefficient14 =
      row18_reducedY11_combinationStep05Coefficient14 +
        row18_reducedY11_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep06Coefficient14 row18_reducedY11_combinationStep05Coefficient14 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep06Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep06CoefficientIdentity15 :
    row18_reducedY11_combinationStep06Coefficient15 =
      row18_reducedY11_combinationStep05Coefficient15 +
        row18_reducedY11_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep06Coefficient15 row18_reducedY11_combinationStep05Coefficient15 row18_reducedY11_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY11_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY11_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY11_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY11_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY11_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY11_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY11_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY11_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY11_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY11_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY11_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY11_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY11_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY11_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY11_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY11_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY11_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY11_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY11_combinationStep06CoefficientIdentity00,
      row18_reducedY11_combinationStep06CoefficientIdentity01,
      row18_reducedY11_combinationStep06CoefficientIdentity02,
      row18_reducedY11_combinationStep06CoefficientIdentity03,
      row18_reducedY11_combinationStep06CoefficientIdentity04,
      row18_reducedY11_combinationStep06CoefficientIdentity05,
      row18_reducedY11_combinationStep06CoefficientIdentity06,
      row18_reducedY11_combinationStep06CoefficientIdentity07,
      row18_reducedY11_combinationStep06CoefficientIdentity08,
      row18_reducedY11_combinationStep06CoefficientIdentity09,
      row18_reducedY11_combinationStep06CoefficientIdentity10,
      row18_reducedY11_combinationStep06CoefficientIdentity11,
      row18_reducedY11_combinationStep06CoefficientIdentity12,
      row18_reducedY11_combinationStep06CoefficientIdentity13,
      row18_reducedY11_combinationStep06CoefficientIdentity14,
      row18_reducedY11_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY11_combinationStep06Multiplier * equation

private def row18_reducedY11_combinationStep07Multiplier : ℂ :=
  (-((208 / 79) : ℂ) - ((380 / 79) : ℂ) * ζ ^ 1 + ((60 / 79) : ℂ) * ζ ^ 2 - ((132 / 79) : ℂ) * ζ ^ 3 - ((306 / 79) : ℂ) * ζ ^ 5 + ((236 / 79) : ℂ) * ζ ^ 8 + ((156 / 79) : ℂ) * ζ ^ 9 - ((24 / 79) : ℂ) * ζ ^ 11 + ((180 / 79) : ℂ) * ζ ^ 12 + ((380 / 79) : ℂ) * ζ ^ 13 + ((58 / 79) : ℂ) * ζ ^ 15 + ((380 / 79) : ℂ) * ζ ^ 17 - ((60 / 79) : ℂ) * ζ ^ 18 + ((248 / 79) : ℂ) * ζ ^ 21 - ((60 / 79) : ℂ) * ζ ^ 22 - ((416 / 79) : ℂ) * ζ ^ 24 - ((74 / 79) : ℂ) * ζ ^ 25 + ((248 / 79) : ℂ) * ζ ^ 27 - ((236 / 79) : ℂ) * ζ ^ 28 - ((380 / 79) : ℂ) * ζ ^ 29 - ((160 / 79) : ℂ) * ζ ^ 30 + ((24 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY11_combinationStep07Coefficient00 : ℂ :=
  (((171 / 79) : ℂ) - ((1506 / 395) : ℂ) * ζ ^ 1 + ((2949 / 395) : ℂ) * ζ ^ 2 + ((1079 / 395) : ℂ) * ζ ^ 3 + ((1402 / 395) : ℂ) * ζ ^ 5 + ((3246 / 395) : ℂ) * ζ ^ 6 + ((469 / 79) : ℂ) * ζ ^ 8 + ((3362 / 395) : ℂ) * ζ ^ 9 + ((2283 / 395) : ℂ) * ζ ^ 11 + ((469 / 79) : ℂ) * ζ ^ 12 + ((1506 / 395) : ℂ) * ζ ^ 13 + ((1829 / 395) : ℂ) * ζ ^ 15 + ((1506 / 395) : ℂ) * ζ ^ 17 - ((297 / 395) : ℂ) * ζ ^ 18 + ((427 / 395) : ℂ) * ζ ^ 21 - ((2949 / 395) : ℂ) * ζ ^ 22 - ((2908 / 395) : ℂ) * ζ ^ 25 - ((427 / 395) : ℂ) * ζ ^ 27 - ((469 / 79) : ℂ) * ζ ^ 28 - ((1506 / 395) : ℂ) * ζ ^ 29 + ((1623 / 395) : ℂ) * ζ ^ 30 - ((2283 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep07CoefficientIdentity00 :
    row18_reducedY11_combinationStep07Coefficient00 =
      row18_reducedY11_combinationStep06Coefficient00 +
        row18_reducedY11_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep07Coefficient00 row18_reducedY11_combinationStep06Coefficient00 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep07Coefficient01 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep07CoefficientIdentity01 :
    row18_reducedY11_combinationStep07Coefficient01 =
      row18_reducedY11_combinationStep06Coefficient01 +
        row18_reducedY11_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep07Coefficient01 row18_reducedY11_combinationStep06Coefficient01 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep07Coefficient02 : ℂ :=
  (((866 / 395) : ℂ) - ((411 / 395) : ℂ) * ζ ^ 1 - ((2492 / 395) : ℂ) * ζ ^ 2 + ((268 / 79) : ℂ) * ζ ^ 3 - ((2888 / 395) : ℂ) * ζ ^ 5 - ((1253 / 395) : ℂ) * ζ ^ 6 - ((3118 / 395) : ℂ) * ζ ^ 8 - ((1033 / 395) : ℂ) * ζ ^ 9 - ((566 / 79) : ℂ) * ζ ^ 11 - ((1239 / 395) : ℂ) * ζ ^ 12 + ((411 / 395) : ℂ) * ζ ^ 13 - ((268 / 79) : ℂ) * ζ ^ 15 + ((411 / 395) : ℂ) * ζ ^ 17 + ((1626 / 395) : ℂ) * ζ ^ 18 + ((2477 / 395) : ℂ) * ζ ^ 21 + ((2492 / 395) : ℂ) * ζ ^ 22 + ((2492 / 395) : ℂ) * ζ ^ 24 + ((2477 / 395) : ℂ) * ζ ^ 25 + ((566 / 79) : ℂ) * ζ ^ 27 + ((3118 / 395) : ℂ) * ζ ^ 28 - ((411 / 395) : ℂ) * ζ ^ 29 + ((626 / 395) : ℂ) * ζ ^ 30 + ((566 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep07CoefficientIdentity02 :
    row18_reducedY11_combinationStep07Coefficient02 =
      row18_reducedY11_combinationStep06Coefficient02 +
        row18_reducedY11_combinationStep07Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep07Coefficient02 row18_reducedY11_combinationStep06Coefficient02 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 (((4978 / 6241) : ℂ) + ((1363 / 6241) : ℂ) * ζ ^ 1 - ((2345 / 12482) : ℂ) * ζ ^ 2 + ((2043 / 12482) : ℂ) * ζ ^ 3 - ((2434 / 6241) : ℂ) * ζ ^ 4 + ((1310 / 6241) : ℂ) * ζ ^ 5 + ((10323 / 12482) : ℂ) * ζ ^ 6 + ((3050 / 6241) : ℂ) * ζ ^ 7 - ((2498 / 6241) : ℂ) * ζ ^ 8 - ((1739 / 12482) : ℂ) * ζ ^ 9 + ((5095 / 12482) : ℂ) * ζ ^ 10 - ((4917 / 12482) : ℂ) * ζ ^ 11 + ((4607 / 6241) : ℂ) * ζ ^ 12 - ((1753 / 6241) : ℂ) * ζ ^ 13 - ((2961 / 6241) : ℂ) * ζ ^ 14 + ((8021 / 12482) : ℂ) * ζ ^ 15 - ((347 / 6241) : ℂ) * ζ ^ 16 + ((1852 / 6241) : ℂ) * ζ ^ 17 + ((505 / 6241) : ℂ) * ζ ^ 18 - ((728 / 6241) : ℂ) * ζ ^ 19 + ((1667 / 6241) : ℂ) * ζ ^ 20 - ((6627 / 12482) : ℂ) * ζ ^ 21 - ((4319 / 12482) : ℂ) * ζ ^ 22 + ((92 / 6241) : ℂ) * ζ ^ 23 + ((4045 / 12482) : ℂ) * ζ ^ 24 + ((7860 / 6241) : ℂ) * ζ ^ 25 + ((13 / 6241) : ℂ) * ζ ^ 26 - ((3509 / 6241) : ℂ) * ζ ^ 27 - ((573 / 6241) : ℂ) * ζ ^ 28 + ((888 / 6241) : ℂ) * ζ ^ 29 - ((90 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep07Coefficient03 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY11_combinationStep07CoefficientIdentity03 :
    row18_reducedY11_combinationStep07Coefficient03 =
      row18_reducedY11_combinationStep06Coefficient03 +
        row18_reducedY11_combinationStep07Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep07Coefficient03 row18_reducedY11_combinationStep06Coefficient03 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 (-((4466 / 6241) : ℂ) - ((3988 / 6241) : ℂ) * ζ ^ 1 - ((6751 / 12482) : ℂ) * ζ ^ 2 - ((1189 / 12482) : ℂ) * ζ ^ 3 + ((4723 / 6241) : ℂ) * ζ ^ 4 + ((1569 / 12482) : ℂ) * ζ ^ 5 - ((125 / 6241) : ℂ) * ζ ^ 6 - ((1633 / 6241) : ℂ) * ζ ^ 7 - ((4183 / 6241) : ℂ) * ζ ^ 8 + ((5487 / 6241) : ℂ) * ζ ^ 9 + ((1469 / 6241) : ℂ) * ζ ^ 10 + ((2829 / 6241) : ℂ) * ζ ^ 11 + ((1961 / 12482) : ℂ) * ζ ^ 12 - ((293 / 6241) : ℂ) * ζ ^ 13 + ((139 / 6241) : ℂ) * ζ ^ 14 + ((2645 / 12482) : ℂ) * ζ ^ 15 - ((191 / 6241) : ℂ) * ζ ^ 16 + ((3653 / 6241) : ℂ) * ζ ^ 17 + ((2886 / 6241) : ℂ) * ζ ^ 18 + ((3632 / 6241) : ℂ) * ζ ^ 19 - ((3885 / 6241) : ℂ) * ζ ^ 20 - ((2547 / 6241) : ℂ) * ζ ^ 21 + ((2357 / 12482) : ℂ) * ζ ^ 22 + ((3984 / 6241) : ℂ) * ζ ^ 23 + ((697 / 6241) : ℂ) * ζ ^ 24 - ((627 / 6241) : ℂ) * ζ ^ 25 - ((2849 / 6241) : ℂ) * ζ ^ 26 - ((718 / 6241) : ℂ) * ζ ^ 27 + ((916 / 6241) : ℂ) * ζ ^ 28 + ((8 / 79) : ℂ) * ζ ^ 29 - ((84 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep07Coefficient04 : ℂ :=
  (-((171 / 79) : ℂ) + ((1506 / 395) : ℂ) * ζ ^ 1 - ((2949 / 395) : ℂ) * ζ ^ 2 - ((1079 / 395) : ℂ) * ζ ^ 3 - ((1402 / 395) : ℂ) * ζ ^ 5 - ((3246 / 395) : ℂ) * ζ ^ 6 - ((469 / 79) : ℂ) * ζ ^ 8 - ((3362 / 395) : ℂ) * ζ ^ 9 - ((2283 / 395) : ℂ) * ζ ^ 11 - ((469 / 79) : ℂ) * ζ ^ 12 - ((1506 / 395) : ℂ) * ζ ^ 13 - ((1829 / 395) : ℂ) * ζ ^ 15 - ((1506 / 395) : ℂ) * ζ ^ 17 + ((297 / 395) : ℂ) * ζ ^ 18 - ((427 / 395) : ℂ) * ζ ^ 21 + ((2949 / 395) : ℂ) * ζ ^ 22 + ((2908 / 395) : ℂ) * ζ ^ 25 + ((427 / 395) : ℂ) * ζ ^ 27 + ((469 / 79) : ℂ) * ζ ^ 28 + ((1506 / 395) : ℂ) * ζ ^ 29 - ((1623 / 395) : ℂ) * ζ ^ 30 + ((2283 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep07CoefficientIdentity04 :
    row18_reducedY11_combinationStep07Coefficient04 =
      row18_reducedY11_combinationStep06Coefficient04 +
        row18_reducedY11_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep07Coefficient04 row18_reducedY11_combinationStep06Coefficient04 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep07Coefficient05 : ℂ :=
  (-((50 / 79) : ℂ) + ((148 / 79) : ℂ) * ζ ^ 1 - ((515 / 79) : ℂ) * ζ ^ 2 - ((496 / 79) : ℂ) * ζ ^ 5 - ((465 / 79) : ℂ) * ζ ^ 6 - ((465 / 79) : ℂ) * ζ ^ 8 - ((496 / 79) : ℂ) * ζ ^ 9 - ((614 / 79) : ℂ) * ζ ^ 11 - ((320 / 79) : ℂ) * ζ ^ 12 - ((148 / 79) : ℂ) * ζ ^ 13 - ((347 / 79) : ℂ) * ζ ^ 15 - ((148 / 79) : ℂ) * ζ ^ 17 + ((223 / 79) : ℂ) * ζ ^ 18 + ((174 / 79) : ℂ) * ζ ^ 21 + ((515 / 79) : ℂ) * ζ ^ 22 + ((242 / 79) : ℂ) * ζ ^ 24 + ((644 / 79) : ℂ) * ζ ^ 25 + ((347 / 79) : ℂ) * ζ ^ 27 + ((465 / 79) : ℂ) * ζ ^ 28 + ((148 / 79) : ℂ) * ζ ^ 29 - ((145 / 79) : ℂ) * ζ ^ 30 + ((614 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY11_combinationStep07CoefficientIdentity05 :
    row18_reducedY11_combinationStep07Coefficient05 =
      row18_reducedY11_combinationStep06Coefficient05 +
        row18_reducedY11_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep07Coefficient05 row18_reducedY11_combinationStep06Coefficient05 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep07Coefficient06 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep07CoefficientIdentity06 :
    row18_reducedY11_combinationStep07Coefficient06 =
      row18_reducedY11_combinationStep06Coefficient06 +
        row18_reducedY11_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep07Coefficient06 row18_reducedY11_combinationStep06Coefficient06 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep07Coefficient07 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep07CoefficientIdentity07 :
    row18_reducedY11_combinationStep07Coefficient07 =
      row18_reducedY11_combinationStep06Coefficient07 +
        row18_reducedY11_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep07Coefficient07 row18_reducedY11_combinationStep06Coefficient07 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep07Coefficient08 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep07CoefficientIdentity08 :
    row18_reducedY11_combinationStep07Coefficient08 =
      row18_reducedY11_combinationStep06Coefficient08 +
        row18_reducedY11_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep07Coefficient08 row18_reducedY11_combinationStep06Coefficient08 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep07Coefficient09 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep07CoefficientIdentity09 :
    row18_reducedY11_combinationStep07Coefficient09 =
      row18_reducedY11_combinationStep06Coefficient09 +
        row18_reducedY11_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep07Coefficient09 row18_reducedY11_combinationStep06Coefficient09 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep07Coefficient10 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep07CoefficientIdentity10 :
    row18_reducedY11_combinationStep07Coefficient10 =
      row18_reducedY11_combinationStep06Coefficient10 +
        row18_reducedY11_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep07Coefficient10 row18_reducedY11_combinationStep06Coefficient10 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep07Coefficient11 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep07CoefficientIdentity11 :
    row18_reducedY11_combinationStep07Coefficient11 =
      row18_reducedY11_combinationStep06Coefficient11 +
        row18_reducedY11_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep07Coefficient11 row18_reducedY11_combinationStep06Coefficient11 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep07Coefficient12 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep07CoefficientIdentity12 :
    row18_reducedY11_combinationStep07Coefficient12 =
      row18_reducedY11_combinationStep06Coefficient12 +
        row18_reducedY11_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep07Coefficient12 row18_reducedY11_combinationStep06Coefficient12 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep07Coefficient13 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep07CoefficientIdentity13 :
    row18_reducedY11_combinationStep07Coefficient13 =
      row18_reducedY11_combinationStep06Coefficient13 +
        row18_reducedY11_combinationStep07Multiplier *
          (((5 / 316) : ℂ) - ((3 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((33 / 158) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 + ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 + ((3 / 316) : ℂ) * ζ ^ 9 + ((33 / 316) : ℂ) * ζ ^ 11 + ((3 / 79) : ℂ) * ζ ^ 12 + ((3 / 316) : ℂ) * ζ ^ 13 + ((35 / 158) : ℂ) * ζ ^ 15 + ((3 / 316) : ℂ) * ζ ^ 17 + ((19 / 316) : ℂ) * ζ ^ 18 + ((45 / 158) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((1 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 - ((3 / 316) : ℂ) * ζ ^ 29 + ((13 / 79) : ℂ) * ζ ^ 30 - ((33 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep07Coefficient13 row18_reducedY11_combinationStep06Coefficient13 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 (((3058 / 6241) : ℂ) + ((392 / 6241) : ℂ) * ζ ^ 1 - ((2841 / 12482) : ℂ) * ζ ^ 2 - ((103 / 6241) : ℂ) * ζ ^ 3 + ((3836 / 6241) : ℂ) * ζ ^ 4 - ((4895 / 12482) : ℂ) * ζ ^ 5 - ((2491 / 12482) : ℂ) * ζ ^ 6 - ((12839 / 12482) : ℂ) * ζ ^ 7 + ((2017 / 12482) : ℂ) * ζ ^ 8 + ((10211 / 12482) : ℂ) * ζ ^ 9 + ((2538 / 6241) : ℂ) * ζ ^ 10 - ((1486 / 6241) : ℂ) * ζ ^ 11 - ((24711 / 12482) : ℂ) * ζ ^ 12 - ((6425 / 12482) : ℂ) * ζ ^ 13 - ((1453 / 6241) : ℂ) * ζ ^ 14 + ((5079 / 12482) : ℂ) * ζ ^ 15 + ((2641 / 12482) : ℂ) * ζ ^ 16 - ((707 / 12482) : ℂ) * ζ ^ 17 - ((12423 / 12482) : ℂ) * ζ ^ 18 - ((1465 / 6241) : ℂ) * ζ ^ 19 - ((10497 / 12482) : ℂ) * ζ ^ 20 - ((3557 / 6241) : ℂ) * ζ ^ 21 - ((2515 / 12482) : ℂ) * ζ ^ 22 + ((7701 / 6241) : ℂ) * ζ ^ 23 - ((6705 / 12482) : ℂ) * ζ ^ 24 - ((2191 / 6241) : ℂ) * ζ ^ 25 - ((6207 / 6241) : ℂ) * ζ ^ 26 - ((2633 / 6241) : ℂ) * ζ ^ 27 + ((1037 / 6241) : ℂ) * ζ ^ 28 + ((1632 / 6241) : ℂ) * ζ ^ 29 - ((198 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep07Coefficient14 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep07CoefficientIdentity14 :
    row18_reducedY11_combinationStep07Coefficient14 =
      row18_reducedY11_combinationStep06Coefficient14 +
        row18_reducedY11_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep07Coefficient14 row18_reducedY11_combinationStep06Coefficient14 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep07Coefficient15 : ℂ :=
  (-(1 : ℂ))

private theorem row18_reducedY11_combinationStep07CoefficientIdentity15 :
    row18_reducedY11_combinationStep07Coefficient15 =
      row18_reducedY11_combinationStep06Coefficient15 +
        row18_reducedY11_combinationStep07Multiplier *
          (-((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((35 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep07Coefficient15 row18_reducedY11_combinationStep06Coefficient15 row18_reducedY11_combinationStep07Multiplier
  close_cyclotomic_row18 (((4466 / 6241) : ℂ) + ((3988 / 6241) : ℂ) * ζ ^ 1 + ((6751 / 12482) : ℂ) * ζ ^ 2 + ((1189 / 12482) : ℂ) * ζ ^ 3 - ((4723 / 6241) : ℂ) * ζ ^ 4 - ((1569 / 12482) : ℂ) * ζ ^ 5 + ((125 / 6241) : ℂ) * ζ ^ 6 + ((1633 / 6241) : ℂ) * ζ ^ 7 + ((4183 / 6241) : ℂ) * ζ ^ 8 - ((5487 / 6241) : ℂ) * ζ ^ 9 - ((1469 / 6241) : ℂ) * ζ ^ 10 - ((2829 / 6241) : ℂ) * ζ ^ 11 - ((1961 / 12482) : ℂ) * ζ ^ 12 + ((293 / 6241) : ℂ) * ζ ^ 13 - ((139 / 6241) : ℂ) * ζ ^ 14 - ((2645 / 12482) : ℂ) * ζ ^ 15 + ((191 / 6241) : ℂ) * ζ ^ 16 - ((3653 / 6241) : ℂ) * ζ ^ 17 - ((2886 / 6241) : ℂ) * ζ ^ 18 - ((3632 / 6241) : ℂ) * ζ ^ 19 + ((3885 / 6241) : ℂ) * ζ ^ 20 + ((2547 / 6241) : ℂ) * ζ ^ 21 - ((2357 / 12482) : ℂ) * ζ ^ 22 - ((3984 / 6241) : ℂ) * ζ ^ 23 - ((697 / 6241) : ℂ) * ζ ^ 24 + ((627 / 6241) : ℂ) * ζ ^ 25 + ((2849 / 6241) : ℂ) * ζ ^ 26 + ((718 / 6241) : ℂ) * ζ ^ 27 - ((916 / 6241) : ℂ) * ζ ^ 28 - ((8 / 79) : ℂ) * ζ ^ 29 + ((84 / 6241) : ℂ) * ζ ^ 30)

private theorem row18_reducedY11_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY11_combinationStep07Coefficient00) * Y 0 0
      + (row18_reducedY11_combinationStep07Coefficient01) * Y 0 1
      + (row18_reducedY11_combinationStep07Coefficient02) * Y 1 0
      + (row18_reducedY11_combinationStep07Coefficient03) * Y 1 1
      + (row18_reducedY11_combinationStep07Coefficient04) * Y 2 2
      + (row18_reducedY11_combinationStep07Coefficient05) * Y 2 3
      + (row18_reducedY11_combinationStep07Coefficient06) * Y 3 2
      + (row18_reducedY11_combinationStep07Coefficient07) * Y 3 3
      + (row18_reducedY11_combinationStep07Coefficient08) * Y 4 4
      + (row18_reducedY11_combinationStep07Coefficient09) * Y 4 5
      + (row18_reducedY11_combinationStep07Coefficient10) * Y 5 4
      + (row18_reducedY11_combinationStep07Coefficient11) * Y 5 5
      + (row18_reducedY11_combinationStep07Coefficient12) * Y 6 6
      + (row18_reducedY11_combinationStep07Coefficient13) * Y 6 7
      + (row18_reducedY11_combinationStep07Coefficient14) * Y 7 6
      + (row18_reducedY11_combinationStep07Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY11_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation17
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY11_combinationStep07CoefficientIdentity00,
      row18_reducedY11_combinationStep07CoefficientIdentity01,
      row18_reducedY11_combinationStep07CoefficientIdentity02,
      row18_reducedY11_combinationStep07CoefficientIdentity03,
      row18_reducedY11_combinationStep07CoefficientIdentity04,
      row18_reducedY11_combinationStep07CoefficientIdentity05,
      row18_reducedY11_combinationStep07CoefficientIdentity06,
      row18_reducedY11_combinationStep07CoefficientIdentity07,
      row18_reducedY11_combinationStep07CoefficientIdentity08,
      row18_reducedY11_combinationStep07CoefficientIdentity09,
      row18_reducedY11_combinationStep07CoefficientIdentity10,
      row18_reducedY11_combinationStep07CoefficientIdentity11,
      row18_reducedY11_combinationStep07CoefficientIdentity12,
      row18_reducedY11_combinationStep07CoefficientIdentity13,
      row18_reducedY11_combinationStep07CoefficientIdentity14,
      row18_reducedY11_combinationStep07CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY11_combinationStep07Multiplier * equation

private def row18_reducedY11_combinationStep08Multiplier : ℂ :=
  (((748 / 79) : ℂ) - ((2128 / 395) : ℂ) * ζ ^ 1 + ((5504 / 395) : ℂ) * ζ ^ 2 + ((992 / 395) : ℂ) * ζ ^ 3 + ((3216 / 395) : ℂ) * ζ ^ 5 + ((7656 / 395) : ℂ) * ζ ^ 6 + ((636 / 79) : ℂ) * ζ ^ 8 + ((6056 / 395) : ℂ) * ζ ^ 9 + ((5064 / 395) : ℂ) * ζ ^ 11 + ((636 / 79) : ℂ) * ζ ^ 12 + ((2128 / 395) : ℂ) * ζ ^ 13 + ((4352 / 395) : ℂ) * ζ ^ 15 + ((2128 / 395) : ℂ) * ζ ^ 17 - ((2152 / 395) : ℂ) * ζ ^ 18 + ((1136 / 395) : ℂ) * ζ ^ 21 - ((5504 / 395) : ℂ) * ζ ^ 22 - ((5344 / 395) : ℂ) * ζ ^ 25 - ((1136 / 395) : ℂ) * ζ ^ 27 - ((636 / 79) : ℂ) * ζ ^ 28 - ((2128 / 395) : ℂ) * ζ ^ 29 + ((3828 / 395) : ℂ) * ζ ^ 30 - ((5064 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY11_combinationStep08Coefficient00 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep08CoefficientIdentity00 :
    row18_reducedY11_combinationStep08Coefficient00 =
      row18_reducedY11_combinationStep07Coefficient00 +
        row18_reducedY11_combinationStep08Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep08Coefficient00 row18_reducedY11_combinationStep07Coefficient00 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 (((15753 / 6241) : ℂ) - ((1717 / 395) : ℂ) * ζ ^ 1 + ((35172 / 6241) : ℂ) * ζ ^ 2 + ((117366 / 31205) : ℂ) * ζ ^ 3 - ((197921 / 31205) : ℂ) * ζ ^ 4 + ((205543 / 31205) : ℂ) * ζ ^ 5 + ((16098 / 6241) : ℂ) * ζ ^ 6 - ((231016 / 31205) : ℂ) * ζ ^ 7 + ((29005 / 6241) : ℂ) * ζ ^ 8 + ((90403 / 31205) : ℂ) * ζ ^ 9 - ((48783 / 6241) : ℂ) * ζ ^ 10 + ((47246 / 6241) : ℂ) * ζ ^ 11 + ((14898 / 31205) : ℂ) * ζ ^ 12 - ((220864 / 31205) : ℂ) * ζ ^ 13 + ((167144 / 31205) : ℂ) * ζ ^ 14 - ((41272 / 31205) : ℂ) * ζ ^ 15 - ((188799 / 31205) : ℂ) * ζ ^ 16 + ((200798 / 31205) : ℂ) * ζ ^ 17 - ((87388 / 31205) : ℂ) * ζ ^ 18 - ((97498 / 31205) : ℂ) * ζ ^ 19 + ((124558 / 31205) : ℂ) * ζ ^ 20 - ((126538 / 31205) : ℂ) * ζ ^ 21 - ((9103 / 6241) : ℂ) * ζ ^ 22 + ((74354 / 31205) : ℂ) * ζ ^ 23 - ((29729 / 31205) : ℂ) * ζ ^ 24 - ((23673 / 31205) : ℂ) * ζ ^ 25 + ((53511 / 31205) : ℂ) * ζ ^ 26 - ((7039 / 6241) : ℂ) * ζ ^ 27 + ((6062 / 31205) : ℂ) * ζ ^ 28 + ((6858 / 31205) : ℂ) * ζ ^ 29 + ((17724 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep08Coefficient01 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep08CoefficientIdentity01 :
    row18_reducedY11_combinationStep08Coefficient01 =
      row18_reducedY11_combinationStep07Coefficient01 +
        row18_reducedY11_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep08Coefficient01 row18_reducedY11_combinationStep07Coefficient01 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep08Coefficient02 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep08CoefficientIdentity02 :
    row18_reducedY11_combinationStep08Coefficient02 =
      row18_reducedY11_combinationStep07Coefficient02 +
        row18_reducedY11_combinationStep08Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep08Coefficient02 row18_reducedY11_combinationStep07Coefficient02 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 (((32884 / 31205) : ℂ) - ((48718 / 31205) : ℂ) * ζ ^ 1 - ((218123 / 31205) : ℂ) * ζ ^ 2 - ((10755 / 6241) : ℂ) * ζ ^ 3 + ((24184 / 31205) : ℂ) * ζ ^ 4 - ((77122 / 6241) : ℂ) * ζ ^ 5 + ((48318 / 31205) : ℂ) * ζ ^ 6 - ((96163 / 31205) : ℂ) * ζ ^ 7 - ((53521 / 6241) : ℂ) * ζ ^ 8 + ((20877 / 31205) : ℂ) * ζ ^ 9 - ((64007 / 31205) : ℂ) * ζ ^ 10 - ((37340 / 6241) : ℂ) * ζ ^ 11 - ((21231 / 31205) : ℂ) * ζ ^ 12 + ((19828 / 6241) : ℂ) * ζ ^ 13 - ((241141 / 31205) : ℂ) * ζ ^ 14 + ((133299 / 31205) : ℂ) * ζ ^ 15 - ((3996 / 31205) : ℂ) * ζ ^ 16 - ((90891 / 31205) : ℂ) * ζ ^ 17 + ((134041 / 31205) : ℂ) * ζ ^ 18 + ((3421 / 6241) : ℂ) * ζ ^ 19 - ((16689 / 31205) : ℂ) * ζ ^ 20 + ((191774 / 31205) : ℂ) * ζ ^ 21 + ((34344 / 31205) : ℂ) * ζ ^ 22 + ((40516 / 31205) : ℂ) * ζ ^ 23 + ((155373 / 31205) : ℂ) * ζ ^ 24 + ((15257 / 31205) : ℂ) * ζ ^ 25 + ((26301 / 31205) : ℂ) * ζ ^ 26 + ((129687 / 31205) : ℂ) * ζ ^ 27 + ((48126 / 31205) : ℂ) * ζ ^ 28 - ((3924 / 6241) : ℂ) * ζ ^ 29 + ((106344 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep08Coefficient03 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY11_combinationStep08CoefficientIdentity03 :
    row18_reducedY11_combinationStep08Coefficient03 =
      row18_reducedY11_combinationStep07Coefficient03 +
        row18_reducedY11_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep08Coefficient03 row18_reducedY11_combinationStep07Coefficient03 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep08Coefficient04 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep08CoefficientIdentity04 :
    row18_reducedY11_combinationStep08Coefficient04 =
      row18_reducedY11_combinationStep07Coefficient04 +
        row18_reducedY11_combinationStep08Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep08Coefficient04 row18_reducedY11_combinationStep07Coefficient04 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 (-((15753 / 6241) : ℂ) + ((1717 / 395) : ℂ) * ζ ^ 1 - ((35172 / 6241) : ℂ) * ζ ^ 2 - ((117366 / 31205) : ℂ) * ζ ^ 3 + ((197921 / 31205) : ℂ) * ζ ^ 4 - ((205543 / 31205) : ℂ) * ζ ^ 5 - ((16098 / 6241) : ℂ) * ζ ^ 6 + ((231016 / 31205) : ℂ) * ζ ^ 7 - ((29005 / 6241) : ℂ) * ζ ^ 8 - ((90403 / 31205) : ℂ) * ζ ^ 9 + ((48783 / 6241) : ℂ) * ζ ^ 10 - ((47246 / 6241) : ℂ) * ζ ^ 11 - ((14898 / 31205) : ℂ) * ζ ^ 12 + ((220864 / 31205) : ℂ) * ζ ^ 13 - ((167144 / 31205) : ℂ) * ζ ^ 14 + ((41272 / 31205) : ℂ) * ζ ^ 15 + ((188799 / 31205) : ℂ) * ζ ^ 16 - ((200798 / 31205) : ℂ) * ζ ^ 17 + ((87388 / 31205) : ℂ) * ζ ^ 18 + ((97498 / 31205) : ℂ) * ζ ^ 19 - ((124558 / 31205) : ℂ) * ζ ^ 20 + ((126538 / 31205) : ℂ) * ζ ^ 21 + ((9103 / 6241) : ℂ) * ζ ^ 22 - ((74354 / 31205) : ℂ) * ζ ^ 23 + ((29729 / 31205) : ℂ) * ζ ^ 24 + ((23673 / 31205) : ℂ) * ζ ^ 25 - ((53511 / 31205) : ℂ) * ζ ^ 26 + ((7039 / 6241) : ℂ) * ζ ^ 27 - ((6062 / 31205) : ℂ) * ζ ^ 28 - ((6858 / 31205) : ℂ) * ζ ^ 29 - ((17724 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep08Coefficient05 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep08CoefficientIdentity05 :
    row18_reducedY11_combinationStep08Coefficient05 =
      row18_reducedY11_combinationStep07Coefficient05 +
        row18_reducedY11_combinationStep08Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY11_combinationStep08Coefficient05 row18_reducedY11_combinationStep07Coefficient05 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 (((8953 / 6241) : ℂ) + ((4922 / 31205) : ℂ) * ζ ^ 1 - ((21464 / 6241) : ℂ) * ζ ^ 2 - ((2868 / 31205) : ℂ) * ζ ^ 3 - ((61613 / 31205) : ℂ) * ζ ^ 4 - ((155078 / 31205) : ℂ) * ζ ^ 5 - ((5487 / 6241) : ℂ) * ζ ^ 6 - ((8332 / 31205) : ℂ) * ζ ^ 7 - ((53335 / 6241) : ℂ) * ζ ^ 8 + ((63986 / 31205) : ℂ) * ζ ^ 9 - ((116476 / 31205) : ℂ) * ζ ^ 10 - ((100546 / 31205) : ℂ) * ζ ^ 11 - ((52369 / 31205) : ℂ) * ζ ^ 12 + ((101686 / 31205) : ℂ) * ζ ^ 13 - ((235381 / 31205) : ℂ) * ζ ^ 14 - ((4216 / 31205) : ℂ) * ζ ^ 15 + ((47763 / 31205) : ℂ) * ζ ^ 16 - ((53932 / 31205) : ℂ) * ζ ^ 17 + ((1068 / 6241) : ℂ) * ζ ^ 18 + ((16360 / 6241) : ℂ) * ζ ^ 19 - ((137458 / 31205) : ℂ) * ζ ^ 20 + ((66019 / 31205) : ℂ) * ζ ^ 21 + ((109389 / 31205) : ℂ) * ζ ^ 22 - ((98511 / 31205) : ℂ) * ζ ^ 23 + ((174592 / 31205) : ℂ) * ζ ^ 24 + ((10701 / 31205) : ℂ) * ζ ^ 25 + ((58002 / 31205) : ℂ) * ζ ^ 26 + ((55854 / 31205) : ℂ) * ζ ^ 27 + ((13374 / 6241) : ℂ) * ζ ^ 28 - ((103896 / 31205) : ℂ) * ζ ^ 29 + ((45576 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY11_combinationStep08Coefficient06 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep08CoefficientIdentity06 :
    row18_reducedY11_combinationStep08Coefficient06 =
      row18_reducedY11_combinationStep07Coefficient06 +
        row18_reducedY11_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep08Coefficient06 row18_reducedY11_combinationStep07Coefficient06 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep08Coefficient07 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep08CoefficientIdentity07 :
    row18_reducedY11_combinationStep08Coefficient07 =
      row18_reducedY11_combinationStep07Coefficient07 +
        row18_reducedY11_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep08Coefficient07 row18_reducedY11_combinationStep07Coefficient07 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep08Coefficient08 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep08CoefficientIdentity08 :
    row18_reducedY11_combinationStep08Coefficient08 =
      row18_reducedY11_combinationStep07Coefficient08 +
        row18_reducedY11_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep08Coefficient08 row18_reducedY11_combinationStep07Coefficient08 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep08Coefficient09 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep08CoefficientIdentity09 :
    row18_reducedY11_combinationStep08Coefficient09 =
      row18_reducedY11_combinationStep07Coefficient09 +
        row18_reducedY11_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep08Coefficient09 row18_reducedY11_combinationStep07Coefficient09 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep08Coefficient10 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep08CoefficientIdentity10 :
    row18_reducedY11_combinationStep08Coefficient10 =
      row18_reducedY11_combinationStep07Coefficient10 +
        row18_reducedY11_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep08Coefficient10 row18_reducedY11_combinationStep07Coefficient10 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep08Coefficient11 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep08CoefficientIdentity11 :
    row18_reducedY11_combinationStep08Coefficient11 =
      row18_reducedY11_combinationStep07Coefficient11 +
        row18_reducedY11_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep08Coefficient11 row18_reducedY11_combinationStep07Coefficient11 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep08Coefficient12 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep08CoefficientIdentity12 :
    row18_reducedY11_combinationStep08Coefficient12 =
      row18_reducedY11_combinationStep07Coefficient12 +
        row18_reducedY11_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep08Coefficient12 row18_reducedY11_combinationStep07Coefficient12 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep08Coefficient13 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep08CoefficientIdentity13 :
    row18_reducedY11_combinationStep08Coefficient13 =
      row18_reducedY11_combinationStep07Coefficient13 +
        row18_reducedY11_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep08Coefficient13 row18_reducedY11_combinationStep07Coefficient13 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep08Coefficient14 : ℂ :=
  0

private theorem row18_reducedY11_combinationStep08CoefficientIdentity14 :
    row18_reducedY11_combinationStep08Coefficient14 =
      row18_reducedY11_combinationStep07Coefficient14 +
        row18_reducedY11_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep08Coefficient14 row18_reducedY11_combinationStep07Coefficient14 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY11_combinationStep08Coefficient15 : ℂ :=
  (-(1 : ℂ))

private theorem row18_reducedY11_combinationStep08CoefficientIdentity15 :
    row18_reducedY11_combinationStep08Coefficient15 =
      row18_reducedY11_combinationStep07Coefficient15 +
        row18_reducedY11_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY11_combinationStep08Coefficient15 row18_reducedY11_combinationStep07Coefficient15 row18_reducedY11_combinationStep08Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY11_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY11_combinationStep08Coefficient00) * Y 0 0
      + (row18_reducedY11_combinationStep08Coefficient01) * Y 0 1
      + (row18_reducedY11_combinationStep08Coefficient02) * Y 1 0
      + (row18_reducedY11_combinationStep08Coefficient03) * Y 1 1
      + (row18_reducedY11_combinationStep08Coefficient04) * Y 2 2
      + (row18_reducedY11_combinationStep08Coefficient05) * Y 2 3
      + (row18_reducedY11_combinationStep08Coefficient06) * Y 3 2
      + (row18_reducedY11_combinationStep08Coefficient07) * Y 3 3
      + (row18_reducedY11_combinationStep08Coefficient08) * Y 4 4
      + (row18_reducedY11_combinationStep08Coefficient09) * Y 4 5
      + (row18_reducedY11_combinationStep08Coefficient10) * Y 5 4
      + (row18_reducedY11_combinationStep08Coefficient11) * Y 5 5
      + (row18_reducedY11_combinationStep08Coefficient12) * Y 6 6
      + (row18_reducedY11_combinationStep08Coefficient13) * Y 6 7
      + (row18_reducedY11_combinationStep08Coefficient14) * Y 7 6
      + (row18_reducedY11_combinationStep08Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY11_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY11_combinationStep08CoefficientIdentity00,
      row18_reducedY11_combinationStep08CoefficientIdentity01,
      row18_reducedY11_combinationStep08CoefficientIdentity02,
      row18_reducedY11_combinationStep08CoefficientIdentity03,
      row18_reducedY11_combinationStep08CoefficientIdentity04,
      row18_reducedY11_combinationStep08CoefficientIdentity05,
      row18_reducedY11_combinationStep08CoefficientIdentity06,
      row18_reducedY11_combinationStep08CoefficientIdentity07,
      row18_reducedY11_combinationStep08CoefficientIdentity08,
      row18_reducedY11_combinationStep08CoefficientIdentity09,
      row18_reducedY11_combinationStep08CoefficientIdentity10,
      row18_reducedY11_combinationStep08CoefficientIdentity11,
      row18_reducedY11_combinationStep08CoefficientIdentity12,
      row18_reducedY11_combinationStep08CoefficientIdentity13,
      row18_reducedY11_combinationStep08CoefficientIdentity14,
      row18_reducedY11_combinationStep08CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY11_combinationStep08Multiplier * equation

theorem row18_reducedY11
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 1 1 = Y 7 7 := by
  have reduced :=
    row18_reducedY11_combinationStep08 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY11_combinationStep08Coefficient00,
      row18_reducedY11_combinationStep08Coefficient01,
      row18_reducedY11_combinationStep08Coefficient02,
      row18_reducedY11_combinationStep08Coefficient03,
      row18_reducedY11_combinationStep08Coefficient04,
      row18_reducedY11_combinationStep08Coefficient05,
      row18_reducedY11_combinationStep08Coefficient06,
      row18_reducedY11_combinationStep08Coefficient07,
      row18_reducedY11_combinationStep08Coefficient08,
      row18_reducedY11_combinationStep08Coefficient09,
      row18_reducedY11_combinationStep08Coefficient10,
      row18_reducedY11_combinationStep08Coefficient11,
      row18_reducedY11_combinationStep08Coefficient12,
      row18_reducedY11_combinationStep08Coefficient13,
      row18_reducedY11_combinationStep08Coefficient14,
      row18_reducedY11_combinationStep08Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
