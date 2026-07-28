/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction04

/-!
# Ambient row 18 commutant reduction 05

This generated module checks the reduced relation `reducedY23` for
matrix coordinate (2, 3).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY23_combinationStep00Multiplier : ℂ :=
  (((16604 / 1185) : ℂ) + ((6802 / 395) : ℂ) * ζ ^ 1 + ((52 / 1185) : ℂ) * ζ ^ 2 - ((1080 / 79) : ℂ) * ζ ^ 3 + ((22028 / 1185) : ℂ) * ζ ^ 5 + ((13958 / 1185) : ℂ) * ζ ^ 6 - ((5762 / 1185) : ℂ) * ζ ^ 8 - ((9392 / 1185) : ℂ) * ζ ^ 9 + ((774 / 79) : ℂ) * ζ ^ 11 - ((13906 / 1185) : ℂ) * ζ ^ 12 - ((6802 / 395) : ℂ) * ζ ^ 13 + ((1080 / 79) : ℂ) * ζ ^ 15 - ((6802 / 395) : ℂ) * ζ ^ 17 - ((5552 / 395) : ℂ) * ζ ^ 18 - ((1622 / 1185) : ℂ) * ζ ^ 21 - ((52 / 1185) : ℂ) * ζ ^ 22 - ((52 / 1185) : ℂ) * ζ ^ 24 - ((1622 / 1185) : ℂ) * ζ ^ 25 - ((774 / 79) : ℂ) * ζ ^ 27 + ((5762 / 1185) : ℂ) * ζ ^ 28 + ((6802 / 395) : ℂ) * ζ ^ 29 + ((1938 / 395) : ℂ) * ζ ^ 30 - ((774 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY23_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep00CoefficientIdentity00 :
    row18_reducedY23_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep00Coefficient00 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep00Coefficient01 : ℂ :=
  (((1469 / 474) : ℂ) + ((1753 / 237) : ℂ) * ζ ^ 1 + ((593 / 158) : ℂ) * ζ ^ 2 + ((1541 / 474) : ℂ) * ζ ^ 3 + ((1091 / 474) : ℂ) * ζ ^ 5 + ((559 / 237) : ℂ) * ζ ^ 8 + ((557 / 237) : ℂ) * ζ ^ 9 - ((885 / 158) : ℂ) * ζ ^ 11 - ((676 / 79) : ℂ) * ζ ^ 12 - ((1753 / 237) : ℂ) * ζ ^ 13 + ((437 / 237) : ℂ) * ζ ^ 15 - ((1753 / 237) : ℂ) * ζ ^ 17 - ((593 / 158) : ℂ) * ζ ^ 18 - ((655 / 158) : ℂ) * ζ ^ 21 - ((593 / 158) : ℂ) * ζ ^ 22 + ((1469 / 237) : ℂ) * ζ ^ 24 + ((805 / 158) : ℂ) * ζ ^ 25 - ((655 / 158) : ℂ) * ζ ^ 27 - ((559 / 237) : ℂ) * ζ ^ 28 + ((1753 / 237) : ℂ) * ζ ^ 29 + ((1657 / 237) : ℂ) * ζ ^ 30 + ((885 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep00CoefficientIdentity01 :
    row18_reducedY23_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep00Coefficient01 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 (((117113 / 187230) : ℂ) - ((45310 / 18723) : ℂ) * ζ ^ 1 - ((121703 / 93615) : ℂ) * ζ ^ 2 - ((839929 / 187230) : ℂ) * ζ ^ 3 - ((188869 / 187230) : ℂ) * ζ ^ 4 - ((10573 / 62410) : ℂ) * ζ ^ 5 - ((56179 / 62410) : ℂ) * ζ ^ 6 + ((162881 / 31205) : ℂ) * ζ ^ 7 + ((86711 / 187230) : ℂ) * ζ ^ 8 - ((767737 / 93615) : ℂ) * ζ ^ 9 - ((796403 / 93615) : ℂ) * ζ ^ 10 + ((137518 / 93615) : ℂ) * ζ ^ 11 + ((313325 / 37446) : ℂ) * ζ ^ 12 + ((821999 / 187230) : ℂ) * ζ ^ 13 - ((55083 / 31205) : ℂ) * ζ ^ 14 - ((65149 / 31205) : ℂ) * ζ ^ 15 - ((48056 / 31205) : ℂ) * ζ ^ 16 - ((32759 / 93615) : ℂ) * ζ ^ 17 - ((103229 / 93615) : ℂ) * ζ ^ 18 - ((90841 / 62410) : ℂ) * ζ ^ 19 - ((14909 / 62410) : ℂ) * ζ ^ 20 + ((109617 / 31205) : ℂ) * ζ ^ 21 + ((24489 / 6241) : ℂ) * ζ ^ 22 - ((221564 / 93615) : ℂ) * ζ ^ 23 - ((31823 / 12482) : ℂ) * ζ ^ 24 + ((136931 / 62410) : ℂ) * ζ ^ 25 + ((121179 / 31205) : ℂ) * ζ ^ 26 - ((63232 / 93615) : ℂ) * ζ ^ 27 - ((22252 / 6241) : ℂ) * ζ ^ 28 - ((118137 / 62410) : ℂ) * ζ ^ 29 + ((13158 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep00Coefficient02 : ℂ :=
  (-((551 / 237) : ℂ) * ζ ^ 1 - ((585 / 79) : ℂ) * ζ ^ 2 - ((551 / 237) : ℂ) * ζ ^ 3 + ((577 / 237) : ℂ) * ζ ^ 5 + ((140 / 237) : ℂ) * ζ ^ 6 - ((1627 / 474) : ℂ) * ζ ^ 8 - ((865 / 237) : ℂ) * ζ ^ 9 + ((376 / 79) : ℂ) * ζ ^ 11 + ((859 / 237) : ℂ) * ζ ^ 12 + ((551 / 237) : ℂ) * ζ ^ 13 - ((647 / 237) : ℂ) * ζ ^ 15 + ((551 / 237) : ℂ) * ζ ^ 17 + ((585 / 158) : ℂ) * ζ ^ 18 + ((1198 / 237) : ℂ) * ζ ^ 21 + ((585 / 79) : ℂ) * ζ ^ 22 - ((859 / 237) : ℂ) * ζ ^ 24 - ((376 / 79) : ℂ) * ζ ^ 25 + ((865 / 237) : ℂ) * ζ ^ 27 + ((1627 / 474) : ℂ) * ζ ^ 28 - ((551 / 237) : ℂ) * ζ ^ 29 - ((1895 / 237) : ℂ) * ζ ^ 30 - ((376 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep00CoefficientIdentity02 :
    row18_reducedY23_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep00Coefficient02 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 (((340382 / 93615) : ℂ) + ((229977 / 31205) : ℂ) * ζ ^ 1 + ((601163 / 62410) : ℂ) * ζ ^ 2 - ((40459 / 93615) : ℂ) * ζ ^ 3 - ((515026 / 93615) : ℂ) * ζ ^ 4 - ((201428 / 31205) : ℂ) * ζ ^ 5 - ((912907 / 187230) : ℂ) * ζ ^ 6 + ((329177 / 93615) : ℂ) * ζ ^ 7 + ((903289 / 187230) : ℂ) * ζ ^ 8 - ((3989 / 31205) : ℂ) * ζ ^ 9 - ((901 / 62410) : ℂ) * ζ ^ 10 - ((213062 / 93615) : ℂ) * ζ ^ 11 - ((107474 / 31205) : ℂ) * ζ ^ 12 - ((129203 / 31205) : ℂ) * ζ ^ 13 - ((114676 / 93615) : ℂ) * ζ ^ 14 + ((379559 / 93615) : ℂ) * ζ ^ 15 + ((282369 / 62410) : ℂ) * ζ ^ 16 + ((128147 / 93615) : ℂ) * ζ ^ 17 - ((155647 / 187230) : ℂ) * ζ ^ 18 - ((373861 / 93615) : ℂ) * ζ ^ 19 - ((249394 / 93615) : ℂ) * ζ ^ 20 - ((7158 / 6241) : ℂ) * ζ ^ 21 - ((10543 / 187230) : ℂ) * ζ ^ 22 + ((31138 / 31205) : ℂ) * ζ ^ 23 + ((49702 / 18723) : ℂ) * ζ ^ 24 + ((373523 / 93615) : ℂ) * ζ ^ 25 + ((24184 / 31205) : ℂ) * ζ ^ 26 - ((21167 / 6241) : ℂ) * ζ ^ 27 - ((102333 / 62410) : ℂ) * ζ ^ 28 + ((3771 / 6241) : ℂ) * ζ ^ 29 + ((5805 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep00CoefficientIdentity03 :
    row18_reducedY23_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep00Coefficient03 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep00CoefficientIdentity04 :
    row18_reducedY23_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep00Coefficient04 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep00CoefficientIdentity05 :
    row18_reducedY23_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep00Coefficient05 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep00CoefficientIdentity06 :
    row18_reducedY23_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep00Coefficient06 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep00CoefficientIdentity07 :
    row18_reducedY23_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep00Coefficient07 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep00CoefficientIdentity08 :
    row18_reducedY23_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep00Coefficient08 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep00CoefficientIdentity09 :
    row18_reducedY23_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep00Coefficient09 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep00CoefficientIdentity10 :
    row18_reducedY23_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep00Coefficient10 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep00CoefficientIdentity11 :
    row18_reducedY23_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep00Coefficient11 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep00CoefficientIdentity12 :
    row18_reducedY23_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep00Coefficient12 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep00CoefficientIdentity13 :
    row18_reducedY23_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep00Coefficient13 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep00CoefficientIdentity14 :
    row18_reducedY23_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep00Coefficient14 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep00CoefficientIdentity15 :
    row18_reducedY23_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY23_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep00Coefficient15 row18_reducedY23_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY23_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY23_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY23_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY23_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY23_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY23_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY23_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY23_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY23_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY23_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY23_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY23_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY23_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY23_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY23_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY23_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY23_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY23_combinationStep00CoefficientIdentity00,
      row18_reducedY23_combinationStep00CoefficientIdentity01,
      row18_reducedY23_combinationStep00CoefficientIdentity02,
      row18_reducedY23_combinationStep00CoefficientIdentity03,
      row18_reducedY23_combinationStep00CoefficientIdentity04,
      row18_reducedY23_combinationStep00CoefficientIdentity05,
      row18_reducedY23_combinationStep00CoefficientIdentity06,
      row18_reducedY23_combinationStep00CoefficientIdentity07,
      row18_reducedY23_combinationStep00CoefficientIdentity08,
      row18_reducedY23_combinationStep00CoefficientIdentity09,
      row18_reducedY23_combinationStep00CoefficientIdentity10,
      row18_reducedY23_combinationStep00CoefficientIdentity11,
      row18_reducedY23_combinationStep00CoefficientIdentity12,
      row18_reducedY23_combinationStep00CoefficientIdentity13,
      row18_reducedY23_combinationStep00CoefficientIdentity14,
      row18_reducedY23_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY23_combinationStep00Multiplier * equation

private def row18_reducedY23_combinationStep01Multiplier : ℂ :=
  (-((2818 / 237) : ℂ) - ((14642 / 1185) : ℂ) * ζ ^ 1 + ((1198 / 237) : ℂ) * ζ ^ 2 + ((17648 / 1185) : ℂ) * ζ ^ 3 - ((3482 / 395) : ℂ) * ζ ^ 5 - ((644 / 79) : ℂ) * ζ ^ 6 + ((576 / 79) : ℂ) * ζ ^ 8 + ((10084 / 1185) : ℂ) * ζ ^ 9 - ((7564 / 1185) : ℂ) * ζ ^ 11 + ((576 / 79) : ℂ) * ζ ^ 12 + ((14642 / 1185) : ℂ) * ζ ^ 13 - ((4484 / 395) : ℂ) * ζ ^ 15 + ((14642 / 1185) : ℂ) * ζ ^ 17 + ((3130 / 237) : ℂ) * ζ ^ 18 - ((1002 / 395) : ℂ) * ζ ^ 21 - ((1198 / 237) : ℂ) * ζ ^ 22 - ((4196 / 1185) : ℂ) * ζ ^ 25 + ((1002 / 395) : ℂ) * ζ ^ 27 - ((576 / 79) : ℂ) * ζ ^ 28 - ((14642 / 1185) : ℂ) * ζ ^ 29 - ((322 / 79) : ℂ) * ζ ^ 30 + ((7564 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY23_combinationStep01Coefficient00 : ℂ :=
  (-((508 / 237) : ℂ) - ((617 / 158) : ℂ) * ζ ^ 1 - ((2167 / 474) : ℂ) * ζ ^ 2 - ((409 / 158) : ℂ) * ζ ^ 3 + ((725 / 474) : ℂ) * ζ ^ 6 - ((431 / 237) : ℂ) * ζ ^ 8 - ((596 / 237) : ℂ) * ζ ^ 9 + ((350 / 79) : ℂ) * ζ ^ 11 + ((482 / 79) : ℂ) * ζ ^ 12 + ((617 / 158) : ℂ) * ζ ^ 13 - ((409 / 158) : ℂ) * ζ ^ 15 + ((617 / 158) : ℂ) * ζ ^ 17 + ((1151 / 474) : ℂ) * ζ ^ 18 + ((617 / 158) : ℂ) * ζ ^ 21 + ((2167 / 474) : ℂ) * ζ ^ 22 - ((2167 / 474) : ℂ) * ζ ^ 24 - ((617 / 158) : ℂ) * ζ ^ 25 + ((350 / 79) : ℂ) * ζ ^ 27 + ((431 / 237) : ℂ) * ζ ^ 28 - ((617 / 158) : ℂ) * ζ ^ 29 - ((3029 / 474) : ℂ) * ζ ^ 30 - ((350 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep01CoefficientIdentity00 :
    row18_reducedY23_combinationStep01Coefficient00 =
      row18_reducedY23_combinationStep00Coefficient00 +
        row18_reducedY23_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep01Coefficient00 row18_reducedY23_combinationStep00Coefficient00 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 (((97901 / 18723) : ℂ) + ((711526 / 93615) : ℂ) * ζ ^ 1 + ((157513 / 31205) : ℂ) * ζ ^ 2 - ((99002 / 93615) : ℂ) * ζ ^ 3 - ((685628 / 93615) : ℂ) * ζ ^ 4 - ((203817 / 31205) : ℂ) * ζ ^ 5 - ((478223 / 187230) : ℂ) * ζ ^ 6 + ((172969 / 62410) : ℂ) * ζ ^ 7 + ((155614 / 31205) : ℂ) * ζ ^ 8 + ((43243 / 187230) : ℂ) * ζ ^ 9 - ((46631 / 93615) : ℂ) * ζ ^ 10 - ((61003 / 62410) : ℂ) * ζ ^ 11 - ((313597 / 93615) : ℂ) * ζ ^ 12 - ((251363 / 93615) : ℂ) * ζ ^ 13 - ((181781 / 187230) : ℂ) * ζ ^ 14 + ((178631 / 62410) : ℂ) * ζ ^ 15 + ((778963 / 187230) : ℂ) * ζ ^ 16 + ((201553 / 187230) : ℂ) * ζ ^ 17 - ((17149 / 31205) : ℂ) * ζ ^ 18 - ((204703 / 62410) : ℂ) * ζ ^ 19 - ((474889 / 187230) : ℂ) * ζ ^ 20 + ((1019 / 62410) : ℂ) * ζ ^ 21 + ((147079 / 187230) : ℂ) * ζ ^ 22 + ((46842 / 31205) : ℂ) * ζ ^ 23 + ((82891 / 31205) : ℂ) * ζ ^ 24 + ((3251 / 1185) : ℂ) * ζ ^ 25 + ((34933 / 187230) : ℂ) * ζ ^ 26 - ((230887 / 93615) : ℂ) * ζ ^ 27 - ((112093 / 93615) : ℂ) * ζ ^ 28 + ((21963 / 62410) : ℂ) * ζ ^ 29 + ((1891 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep01Coefficient01 : ℂ :=
  (((2123 / 474) : ℂ) + ((2009 / 237) : ℂ) * ζ ^ 1 + ((1400 / 237) : ℂ) * ζ ^ 2 + ((1567 / 474) : ℂ) * ζ ^ 3 + ((209 / 158) : ℂ) * ζ ^ 5 + ((308 / 237) : ℂ) * ζ ^ 8 + ((483 / 158) : ℂ) * ζ ^ 9 - ((1508 / 237) : ℂ) * ζ ^ 11 - ((2431 / 237) : ℂ) * ζ ^ 12 - ((2009 / 237) : ℂ) * ζ ^ 13 + ((304 / 79) : ℂ) * ζ ^ 15 - ((2009 / 237) : ℂ) * ζ ^ 17 - ((1400 / 237) : ℂ) * ζ ^ 18 - ((817 / 158) : ℂ) * ζ ^ 21 - ((1400 / 237) : ℂ) * ζ ^ 22 + ((2123 / 237) : ℂ) * ζ ^ 24 + ((3391 / 474) : ℂ) * ζ ^ 25 - ((817 / 158) : ℂ) * ζ ^ 27 - ((308 / 237) : ℂ) * ζ ^ 28 + ((2009 / 237) : ℂ) * ζ ^ 29 + ((4673 / 474) : ℂ) * ζ ^ 30 + ((1508 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep01CoefficientIdentity01 :
    row18_reducedY23_combinationStep01Coefficient01 =
      row18_reducedY23_combinationStep00Coefficient01 +
        row18_reducedY23_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep01Coefficient01 row18_reducedY23_combinationStep00Coefficient01 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 (-((3289 / 18723) : ℂ) + ((93511 / 93615) : ℂ) * ζ ^ 1 + ((419221 / 93615) : ℂ) * ζ ^ 2 + ((8813 / 1185) : ℂ) * ζ ^ 3 - ((56164 / 93615) : ℂ) * ζ ^ 4 - ((1802549 / 187230) : ℂ) * ζ ^ 5 - ((754487 / 93615) : ℂ) * ζ ^ 6 - ((300143 / 187230) : ℂ) * ζ ^ 7 + ((108099 / 12482) : ℂ) * ζ ^ 8 + ((962603 / 187230) : ℂ) * ζ ^ 9 - ((239987 / 187230) : ℂ) * ζ ^ 10 - ((58053 / 62410) : ℂ) * ζ ^ 11 - ((340557 / 62410) : ℂ) * ζ ^ 12 - ((263039 / 62410) : ℂ) * ζ ^ 13 - ((5905 / 6241) : ℂ) * ζ ^ 14 - ((72813 / 62410) : ℂ) * ζ ^ 15 + ((204677 / 62410) : ℂ) * ζ ^ 16 + ((688003 / 187230) : ℂ) * ζ ^ 17 - ((385429 / 93615) : ℂ) * ζ ^ 18 - ((756664 / 93615) : ℂ) * ζ ^ 19 - ((147916 / 31205) : ℂ) * ζ ^ 20 + ((976843 / 187230) : ℂ) * ζ ^ 21 + ((246071 / 62410) : ℂ) * ζ ^ 22 + ((176171 / 93615) : ℂ) * ζ ^ 23 + ((93455 / 37446) : ℂ) * ζ ^ 24 + ((107937 / 62410) : ℂ) * ζ ^ 25 - ((88948 / 93615) : ℂ) * ζ ^ 26 - ((48153 / 31205) : ℂ) * ζ ^ 27 - ((57692 / 31205) : ℂ) * ζ ^ 28 + ((3858 / 31205) : ℂ) * ζ ^ 29 + ((52948 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep01Coefficient02 : ℂ :=
  (-((551 / 237) : ℂ) * ζ ^ 1 - ((585 / 79) : ℂ) * ζ ^ 2 - ((551 / 237) : ℂ) * ζ ^ 3 + ((577 / 237) : ℂ) * ζ ^ 5 + ((140 / 237) : ℂ) * ζ ^ 6 - ((1627 / 474) : ℂ) * ζ ^ 8 - ((865 / 237) : ℂ) * ζ ^ 9 + ((376 / 79) : ℂ) * ζ ^ 11 + ((859 / 237) : ℂ) * ζ ^ 12 + ((551 / 237) : ℂ) * ζ ^ 13 - ((647 / 237) : ℂ) * ζ ^ 15 + ((551 / 237) : ℂ) * ζ ^ 17 + ((585 / 158) : ℂ) * ζ ^ 18 + ((1198 / 237) : ℂ) * ζ ^ 21 + ((585 / 79) : ℂ) * ζ ^ 22 - ((859 / 237) : ℂ) * ζ ^ 24 - ((376 / 79) : ℂ) * ζ ^ 25 + ((865 / 237) : ℂ) * ζ ^ 27 + ((1627 / 474) : ℂ) * ζ ^ 28 - ((551 / 237) : ℂ) * ζ ^ 29 - ((1895 / 237) : ℂ) * ζ ^ 30 - ((376 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep01CoefficientIdentity02 :
    row18_reducedY23_combinationStep01Coefficient02 =
      row18_reducedY23_combinationStep00Coefficient02 +
        row18_reducedY23_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep01Coefficient02 row18_reducedY23_combinationStep00Coefficient02 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep01Coefficient03 : ℂ :=
  (((508 / 237) : ℂ) + ((617 / 158) : ℂ) * ζ ^ 1 + ((2167 / 474) : ℂ) * ζ ^ 2 + ((409 / 158) : ℂ) * ζ ^ 3 - ((725 / 474) : ℂ) * ζ ^ 6 + ((431 / 237) : ℂ) * ζ ^ 8 + ((596 / 237) : ℂ) * ζ ^ 9 - ((350 / 79) : ℂ) * ζ ^ 11 - ((482 / 79) : ℂ) * ζ ^ 12 - ((617 / 158) : ℂ) * ζ ^ 13 + ((409 / 158) : ℂ) * ζ ^ 15 - ((617 / 158) : ℂ) * ζ ^ 17 - ((1151 / 474) : ℂ) * ζ ^ 18 - ((617 / 158) : ℂ) * ζ ^ 21 - ((2167 / 474) : ℂ) * ζ ^ 22 + ((2167 / 474) : ℂ) * ζ ^ 24 + ((617 / 158) : ℂ) * ζ ^ 25 - ((350 / 79) : ℂ) * ζ ^ 27 - ((431 / 237) : ℂ) * ζ ^ 28 + ((617 / 158) : ℂ) * ζ ^ 29 + ((3029 / 474) : ℂ) * ζ ^ 30 + ((350 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep01CoefficientIdentity03 :
    row18_reducedY23_combinationStep01Coefficient03 =
      row18_reducedY23_combinationStep00Coefficient03 +
        row18_reducedY23_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep01Coefficient03 row18_reducedY23_combinationStep00Coefficient03 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 (-((97901 / 18723) : ℂ) - ((711526 / 93615) : ℂ) * ζ ^ 1 - ((157513 / 31205) : ℂ) * ζ ^ 2 + ((99002 / 93615) : ℂ) * ζ ^ 3 + ((685628 / 93615) : ℂ) * ζ ^ 4 + ((203817 / 31205) : ℂ) * ζ ^ 5 + ((478223 / 187230) : ℂ) * ζ ^ 6 - ((172969 / 62410) : ℂ) * ζ ^ 7 - ((155614 / 31205) : ℂ) * ζ ^ 8 - ((43243 / 187230) : ℂ) * ζ ^ 9 + ((46631 / 93615) : ℂ) * ζ ^ 10 + ((61003 / 62410) : ℂ) * ζ ^ 11 + ((313597 / 93615) : ℂ) * ζ ^ 12 + ((251363 / 93615) : ℂ) * ζ ^ 13 + ((181781 / 187230) : ℂ) * ζ ^ 14 - ((178631 / 62410) : ℂ) * ζ ^ 15 - ((778963 / 187230) : ℂ) * ζ ^ 16 - ((201553 / 187230) : ℂ) * ζ ^ 17 + ((17149 / 31205) : ℂ) * ζ ^ 18 + ((204703 / 62410) : ℂ) * ζ ^ 19 + ((474889 / 187230) : ℂ) * ζ ^ 20 - ((1019 / 62410) : ℂ) * ζ ^ 21 - ((147079 / 187230) : ℂ) * ζ ^ 22 - ((46842 / 31205) : ℂ) * ζ ^ 23 - ((82891 / 31205) : ℂ) * ζ ^ 24 - ((3251 / 1185) : ℂ) * ζ ^ 25 - ((34933 / 187230) : ℂ) * ζ ^ 26 + ((230887 / 93615) : ℂ) * ζ ^ 27 + ((112093 / 93615) : ℂ) * ζ ^ 28 - ((21963 / 62410) : ℂ) * ζ ^ 29 - ((1891 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep01CoefficientIdentity04 :
    row18_reducedY23_combinationStep01Coefficient04 =
      row18_reducedY23_combinationStep00Coefficient04 +
        row18_reducedY23_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep01Coefficient04 row18_reducedY23_combinationStep00Coefficient04 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep01CoefficientIdentity05 :
    row18_reducedY23_combinationStep01Coefficient05 =
      row18_reducedY23_combinationStep00Coefficient05 +
        row18_reducedY23_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep01Coefficient05 row18_reducedY23_combinationStep00Coefficient05 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep01CoefficientIdentity06 :
    row18_reducedY23_combinationStep01Coefficient06 =
      row18_reducedY23_combinationStep00Coefficient06 +
        row18_reducedY23_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep01Coefficient06 row18_reducedY23_combinationStep00Coefficient06 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep01CoefficientIdentity07 :
    row18_reducedY23_combinationStep01Coefficient07 =
      row18_reducedY23_combinationStep00Coefficient07 +
        row18_reducedY23_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep01Coefficient07 row18_reducedY23_combinationStep00Coefficient07 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep01CoefficientIdentity08 :
    row18_reducedY23_combinationStep01Coefficient08 =
      row18_reducedY23_combinationStep00Coefficient08 +
        row18_reducedY23_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep01Coefficient08 row18_reducedY23_combinationStep00Coefficient08 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep01CoefficientIdentity09 :
    row18_reducedY23_combinationStep01Coefficient09 =
      row18_reducedY23_combinationStep00Coefficient09 +
        row18_reducedY23_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep01Coefficient09 row18_reducedY23_combinationStep00Coefficient09 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep01CoefficientIdentity10 :
    row18_reducedY23_combinationStep01Coefficient10 =
      row18_reducedY23_combinationStep00Coefficient10 +
        row18_reducedY23_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep01Coefficient10 row18_reducedY23_combinationStep00Coefficient10 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep01CoefficientIdentity11 :
    row18_reducedY23_combinationStep01Coefficient11 =
      row18_reducedY23_combinationStep00Coefficient11 +
        row18_reducedY23_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep01Coefficient11 row18_reducedY23_combinationStep00Coefficient11 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep01CoefficientIdentity12 :
    row18_reducedY23_combinationStep01Coefficient12 =
      row18_reducedY23_combinationStep00Coefficient12 +
        row18_reducedY23_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep01Coefficient12 row18_reducedY23_combinationStep00Coefficient12 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep01CoefficientIdentity13 :
    row18_reducedY23_combinationStep01Coefficient13 =
      row18_reducedY23_combinationStep00Coefficient13 +
        row18_reducedY23_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep01Coefficient13 row18_reducedY23_combinationStep00Coefficient13 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep01CoefficientIdentity14 :
    row18_reducedY23_combinationStep01Coefficient14 =
      row18_reducedY23_combinationStep00Coefficient14 +
        row18_reducedY23_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep01Coefficient14 row18_reducedY23_combinationStep00Coefficient14 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep01CoefficientIdentity15 :
    row18_reducedY23_combinationStep01Coefficient15 =
      row18_reducedY23_combinationStep00Coefficient15 +
        row18_reducedY23_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep01Coefficient15 row18_reducedY23_combinationStep00Coefficient15 row18_reducedY23_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY23_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY23_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY23_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY23_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY23_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY23_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY23_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY23_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY23_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY23_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY23_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY23_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY23_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY23_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY23_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY23_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY23_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY23_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY23_combinationStep01CoefficientIdentity00,
      row18_reducedY23_combinationStep01CoefficientIdentity01,
      row18_reducedY23_combinationStep01CoefficientIdentity02,
      row18_reducedY23_combinationStep01CoefficientIdentity03,
      row18_reducedY23_combinationStep01CoefficientIdentity04,
      row18_reducedY23_combinationStep01CoefficientIdentity05,
      row18_reducedY23_combinationStep01CoefficientIdentity06,
      row18_reducedY23_combinationStep01CoefficientIdentity07,
      row18_reducedY23_combinationStep01CoefficientIdentity08,
      row18_reducedY23_combinationStep01CoefficientIdentity09,
      row18_reducedY23_combinationStep01CoefficientIdentity10,
      row18_reducedY23_combinationStep01CoefficientIdentity11,
      row18_reducedY23_combinationStep01CoefficientIdentity12,
      row18_reducedY23_combinationStep01CoefficientIdentity13,
      row18_reducedY23_combinationStep01CoefficientIdentity14,
      row18_reducedY23_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY23_combinationStep01Multiplier * equation

private def row18_reducedY23_combinationStep02Multiplier : ℂ :=
  (((404 / 395) : ℂ) + ((1160 / 79) : ℂ) * ζ ^ 1 + ((15904 / 1185) : ℂ) * ζ ^ 2 + ((1354 / 237) : ℂ) * ζ ^ 3 - ((1244 / 1185) : ℂ) * ζ ^ 6 + ((9224 / 1185) : ℂ) * ζ ^ 8 + ((1934 / 237) : ℂ) * ζ ^ 9 - ((2446 / 237) : ℂ) * ζ ^ 11 - ((5716 / 395) : ℂ) * ζ ^ 12 - ((1160 / 79) : ℂ) * ζ ^ 13 + ((1354 / 237) : ℂ) * ζ ^ 15 - ((1160 / 79) : ℂ) * ζ ^ 17 - ((14692 / 1185) : ℂ) * ζ ^ 18 - ((1160 / 79) : ℂ) * ζ ^ 21 - ((15904 / 1185) : ℂ) * ζ ^ 22 + ((15904 / 1185) : ℂ) * ζ ^ 24 + ((1160 / 79) : ℂ) * ζ ^ 25 - ((2446 / 237) : ℂ) * ζ ^ 27 - ((9224 / 1185) : ℂ) * ζ ^ 28 + ((1160 / 79) : ℂ) * ζ ^ 29 + ((8376 / 395) : ℂ) * ζ ^ 30 + ((2446 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY23_combinationStep02Coefficient00 : ℂ :=
  (-((31187 / 187230) : ℂ) - ((110869 / 37446) : ℂ) * ζ ^ 1 - ((218422 / 93615) : ℂ) * ζ ^ 2 - ((212143 / 187230) : ℂ) * ζ ^ 3 + ((16759 / 31205) : ℂ) * ζ ^ 6 - ((94643 / 62410) : ℂ) * ζ ^ 8 - ((28829 / 18723) : ℂ) * ζ ^ 9 + ((70359 / 31205) : ℂ) * ζ ^ 11 + ((268699 / 93615) : ℂ) * ζ ^ 12 + ((110869 / 37446) : ℂ) * ζ ^ 13 - ((212143 / 187230) : ℂ) * ζ ^ 15 + ((110869 / 37446) : ℂ) * ζ ^ 17 + ((135219 / 62410) : ℂ) * ζ ^ 18 + ((110869 / 37446) : ℂ) * ζ ^ 21 + ((218422 / 93615) : ℂ) * ζ ^ 22 - ((218422 / 93615) : ℂ) * ζ ^ 24 - ((110869 / 37446) : ℂ) * ζ ^ 25 + ((70359 / 31205) : ℂ) * ζ ^ 27 + ((94643 / 62410) : ℂ) * ζ ^ 28 - ((110869 / 37446) : ℂ) * ζ ^ 29 - ((720773 / 187230) : ℂ) * ζ ^ 30 - ((70359 / 31205) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep02CoefficientIdentity00 :
    row18_reducedY23_combinationStep02Coefficient00 =
      row18_reducedY23_combinationStep01Coefficient00 +
        row18_reducedY23_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep02Coefficient00 row18_reducedY23_combinationStep01Coefficient00 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 (-((75481 / 37446) : ℂ) - ((137267 / 93615) : ℂ) * ζ ^ 1 - ((31357 / 12482) : ℂ) * ζ ^ 2 - ((6101 / 1185) : ℂ) * ζ ^ 3 - ((24388 / 18723) : ℂ) * ζ ^ 4 - ((8801 / 187230) : ℂ) * ζ ^ 5 + ((80953 / 31205) : ℂ) * ζ ^ 6 + ((87938 / 31205) : ℂ) * ζ ^ 7 - ((56362 / 93615) : ℂ) * ζ ^ 8 + ((2209 / 62410) : ℂ) * ζ ^ 9 - ((650633 / 187230) : ℂ) * ζ ^ 10 - ((70378 / 31205) : ℂ) * ζ ^ 11 + ((132124 / 93615) : ℂ) * ζ ^ 12 + ((262189 / 93615) : ℂ) * ζ ^ 13 + ((675149 / 187230) : ℂ) * ζ ^ 14 - ((17875 / 12482) : ℂ) * ζ ^ 15 - ((451864 / 93615) : ℂ) * ζ ^ 16 - ((594193 / 187230) : ℂ) * ζ ^ 17 - ((81306 / 31205) : ℂ) * ζ ^ 18 - ((25717 / 93615) : ℂ) * ζ ^ 19 + ((120743 / 187230) : ℂ) * ζ ^ 20 + ((45035 / 37446) : ℂ) * ζ ^ 21 + ((255973 / 93615) : ℂ) * ζ ^ 22 + ((130451 / 31205) : ℂ) * ζ ^ 23 + ((262232 / 93615) : ℂ) * ζ ^ 24 - ((28686 / 31205) : ℂ) * ζ ^ 25 - ((361973 / 187230) : ℂ) * ζ ^ 26 - ((279589 / 187230) : ℂ) * ζ ^ 27 - ((11959 / 187230) : ℂ) * ζ ^ 28 + ((39028 / 93615) : ℂ) * ζ ^ 29 + ((8561 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep02Coefficient01 : ℂ :=
  (((153199 / 37446) : ℂ) + ((56320 / 6241) : ℂ) * ζ ^ 1 + ((278465 / 37446) : ℂ) * ζ ^ 2 + ((80117 / 37446) : ℂ) * ζ ^ 3 + ((33568 / 18723) : ℂ) * ζ ^ 5 + ((26127 / 12482) : ℂ) * ζ ^ 8 + ((138551 / 37446) : ℂ) * ζ ^ 9 - ((109334 / 18723) : ℂ) * ζ ^ 11 - ((384779 / 37446) : ℂ) * ζ ^ 12 - ((56320 / 6241) : ℂ) * ζ ^ 13 + ((190667 / 37446) : ℂ) * ζ ^ 15 - ((56320 / 6241) : ℂ) * ζ ^ 17 - ((278465 / 37446) : ℂ) * ζ ^ 18 - ((257803 / 37446) : ℂ) * ζ ^ 21 - ((278465 / 37446) : ℂ) * ζ ^ 22 + ((153199 / 18723) : ℂ) * ζ ^ 24 + ((135392 / 18723) : ℂ) * ζ ^ 25 - ((257803 / 37446) : ℂ) * ζ ^ 27 - ((26127 / 12482) : ℂ) * ζ ^ 28 + ((56320 / 6241) : ℂ) * ζ ^ 29 + ((422071 / 37446) : ℂ) * ζ ^ 30 + ((109334 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep02CoefficientIdentity01 :
    row18_reducedY23_combinationStep02Coefficient01 =
      row18_reducedY23_combinationStep01Coefficient01 +
        row18_reducedY23_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep02Coefficient01 row18_reducedY23_combinationStep01Coefficient01 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 (((57202 / 93615) : ℂ) + ((44630 / 18723) : ℂ) * ζ ^ 1 - ((471683 / 187230) : ℂ) * ζ ^ 2 - ((129919 / 187230) : ℂ) * ζ ^ 3 - ((34787 / 62410) : ℂ) * ζ ^ 4 - ((174304 / 93615) : ℂ) * ζ ^ 5 - ((175457 / 187230) : ℂ) * ζ ^ 6 + ((61823 / 62410) : ℂ) * ζ ^ 7 + ((553669 / 187230) : ℂ) * ζ ^ 8 - ((2651 / 2370) : ℂ) * ζ ^ 9 - ((12461 / 31205) : ℂ) * ζ ^ 10 - ((17015 / 37446) : ℂ) * ζ ^ 11 - ((135208 / 93615) : ℂ) * ζ ^ 12 + ((89494 / 93615) : ℂ) * ζ ^ 13 + ((608351 / 187230) : ℂ) * ζ ^ 14 + ((93779 / 31205) : ℂ) * ζ ^ 15 + ((28849 / 93615) : ℂ) * ζ ^ 16 - ((365471 / 187230) : ℂ) * ζ ^ 17 + ((183839 / 62410) : ℂ) * ζ ^ 18 + ((75715 / 18723) : ℂ) * ζ ^ 19 + ((257593 / 93615) : ℂ) * ζ ^ 20 + ((532189 / 187230) : ℂ) * ζ ^ 21 + ((125473 / 18723) : ℂ) * ζ ^ 22 + ((322707 / 62410) : ℂ) * ζ ^ 23 + ((35479 / 93615) : ℂ) * ζ ^ 24 + ((34738 / 18723) : ℂ) * ζ ^ 25 - ((19771 / 31205) : ℂ) * ζ ^ 26 - ((90563 / 93615) : ℂ) * ζ ^ 27 + ((271781 / 187230) : ℂ) * ζ ^ 28 + ((82257 / 31205) : ℂ) * ζ ^ 29 + ((15899 / 37446) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep02Coefficient02 : ℂ :=
  (-((551 / 237) : ℂ) * ζ ^ 1 - ((585 / 79) : ℂ) * ζ ^ 2 - ((551 / 237) : ℂ) * ζ ^ 3 + ((577 / 237) : ℂ) * ζ ^ 5 + ((140 / 237) : ℂ) * ζ ^ 6 - ((1627 / 474) : ℂ) * ζ ^ 8 - ((865 / 237) : ℂ) * ζ ^ 9 + ((376 / 79) : ℂ) * ζ ^ 11 + ((859 / 237) : ℂ) * ζ ^ 12 + ((551 / 237) : ℂ) * ζ ^ 13 - ((647 / 237) : ℂ) * ζ ^ 15 + ((551 / 237) : ℂ) * ζ ^ 17 + ((585 / 158) : ℂ) * ζ ^ 18 + ((1198 / 237) : ℂ) * ζ ^ 21 + ((585 / 79) : ℂ) * ζ ^ 22 - ((859 / 237) : ℂ) * ζ ^ 24 - ((376 / 79) : ℂ) * ζ ^ 25 + ((865 / 237) : ℂ) * ζ ^ 27 + ((1627 / 474) : ℂ) * ζ ^ 28 - ((551 / 237) : ℂ) * ζ ^ 29 - ((1895 / 237) : ℂ) * ζ ^ 30 - ((376 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep02CoefficientIdentity02 :
    row18_reducedY23_combinationStep02Coefficient02 =
      row18_reducedY23_combinationStep01Coefficient02 +
        row18_reducedY23_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep02Coefficient02 row18_reducedY23_combinationStep01Coefficient02 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep02Coefficient03 : ℂ :=
  (((508 / 237) : ℂ) + ((617 / 158) : ℂ) * ζ ^ 1 + ((2167 / 474) : ℂ) * ζ ^ 2 + ((409 / 158) : ℂ) * ζ ^ 3 - ((725 / 474) : ℂ) * ζ ^ 6 + ((431 / 237) : ℂ) * ζ ^ 8 + ((596 / 237) : ℂ) * ζ ^ 9 - ((350 / 79) : ℂ) * ζ ^ 11 - ((482 / 79) : ℂ) * ζ ^ 12 - ((617 / 158) : ℂ) * ζ ^ 13 + ((409 / 158) : ℂ) * ζ ^ 15 - ((617 / 158) : ℂ) * ζ ^ 17 - ((1151 / 474) : ℂ) * ζ ^ 18 - ((617 / 158) : ℂ) * ζ ^ 21 - ((2167 / 474) : ℂ) * ζ ^ 22 + ((2167 / 474) : ℂ) * ζ ^ 24 + ((617 / 158) : ℂ) * ζ ^ 25 - ((350 / 79) : ℂ) * ζ ^ 27 - ((431 / 237) : ℂ) * ζ ^ 28 + ((617 / 158) : ℂ) * ζ ^ 29 + ((3029 / 474) : ℂ) * ζ ^ 30 + ((350 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep02CoefficientIdentity03 :
    row18_reducedY23_combinationStep02Coefficient03 =
      row18_reducedY23_combinationStep01Coefficient03 +
        row18_reducedY23_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep02Coefficient03 row18_reducedY23_combinationStep01Coefficient03 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep02Coefficient04 : ℂ :=
  (-((370133 / 187230) : ℂ) - ((17680 / 18723) : ℂ) * ζ ^ 1 - ((139707 / 62410) : ℂ) * ζ ^ 2 - ((136261 / 93615) : ℂ) * ζ ^ 3 + ((185821 / 187230) : ℂ) * ζ ^ 6 - ((56561 / 187230) : ℂ) * ζ ^ 8 - ((6085 / 6241) : ℂ) * ζ ^ 9 + ((67891 / 31205) : ℂ) * ζ ^ 11 + ((302471 / 93615) : ℂ) * ζ ^ 12 + ((17680 / 18723) : ℂ) * ζ ^ 13 - ((136261 / 93615) : ℂ) * ζ ^ 15 + ((17680 / 18723) : ℂ) * ζ ^ 17 + ((24494 / 93615) : ℂ) * ζ ^ 18 + ((17680 / 18723) : ℂ) * ζ ^ 21 + ((139707 / 62410) : ℂ) * ζ ^ 22 - ((139707 / 62410) : ℂ) * ζ ^ 24 - ((17680 / 18723) : ℂ) * ζ ^ 25 + ((67891 / 31205) : ℂ) * ζ ^ 27 + ((56561 / 187230) : ℂ) * ζ ^ 28 - ((17680 / 18723) : ℂ) * ζ ^ 29 - ((237841 / 93615) : ℂ) * ζ ^ 30 - ((67891 / 31205) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep02CoefficientIdentity04 :
    row18_reducedY23_combinationStep02Coefficient04 =
      row18_reducedY23_combinationStep01Coefficient04 +
        row18_reducedY23_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep02Coefficient04 row18_reducedY23_combinationStep01Coefficient04 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 (((75481 / 37446) : ℂ) + ((137267 / 93615) : ℂ) * ζ ^ 1 + ((31357 / 12482) : ℂ) * ζ ^ 2 + ((6101 / 1185) : ℂ) * ζ ^ 3 + ((24388 / 18723) : ℂ) * ζ ^ 4 + ((8801 / 187230) : ℂ) * ζ ^ 5 - ((80953 / 31205) : ℂ) * ζ ^ 6 - ((87938 / 31205) : ℂ) * ζ ^ 7 + ((56362 / 93615) : ℂ) * ζ ^ 8 - ((2209 / 62410) : ℂ) * ζ ^ 9 + ((650633 / 187230) : ℂ) * ζ ^ 10 + ((70378 / 31205) : ℂ) * ζ ^ 11 - ((132124 / 93615) : ℂ) * ζ ^ 12 - ((262189 / 93615) : ℂ) * ζ ^ 13 - ((675149 / 187230) : ℂ) * ζ ^ 14 + ((17875 / 12482) : ℂ) * ζ ^ 15 + ((451864 / 93615) : ℂ) * ζ ^ 16 + ((594193 / 187230) : ℂ) * ζ ^ 17 + ((81306 / 31205) : ℂ) * ζ ^ 18 + ((25717 / 93615) : ℂ) * ζ ^ 19 - ((120743 / 187230) : ℂ) * ζ ^ 20 - ((45035 / 37446) : ℂ) * ζ ^ 21 - ((255973 / 93615) : ℂ) * ζ ^ 22 - ((130451 / 31205) : ℂ) * ζ ^ 23 - ((262232 / 93615) : ℂ) * ζ ^ 24 + ((28686 / 31205) : ℂ) * ζ ^ 25 + ((361973 / 187230) : ℂ) * ζ ^ 26 + ((279589 / 187230) : ℂ) * ζ ^ 27 + ((11959 / 187230) : ℂ) * ζ ^ 28 - ((39028 / 93615) : ℂ) * ζ ^ 29 - ((8561 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep02CoefficientIdentity05 :
    row18_reducedY23_combinationStep02Coefficient05 =
      row18_reducedY23_combinationStep01Coefficient05 +
        row18_reducedY23_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep02Coefficient05 row18_reducedY23_combinationStep01Coefficient05 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep02Coefficient06 : ℂ :=
  (-((408929 / 18723) : ℂ) - ((3821077 / 187230) : ℂ) * ζ ^ 1 + ((3821077 / 187230) : ℂ) * ζ ^ 3 - ((2550871 / 187230) : ℂ) * ζ ^ 5 - ((256774 / 18723) : ℂ) * ζ ^ 6 + ((408929 / 37446) : ℂ) * ζ ^ 8 + ((299584 / 31205) : ℂ) * ζ ^ 9 - ((211701 / 31205) : ℂ) * ζ ^ 11 + ((109123 / 6241) : ℂ) * ζ ^ 12 + ((3821077 / 187230) : ℂ) * ζ ^ 13 - ((2064559 / 93615) : ℂ) * ζ ^ 15 + ((3821077 / 187230) : ℂ) * ζ ^ 17 + ((274535 / 12482) : ℂ) * ζ ^ 18 - ((308041 / 187230) : ℂ) * ζ ^ 21 - ((81560 / 18723) : ℂ) * ζ ^ 24 - ((211701 / 31205) : ℂ) * ζ ^ 25 + ((299584 / 31205) : ℂ) * ζ ^ 27 - ((408929 / 37446) : ℂ) * ζ ^ 28 - ((3821077 / 187230) : ℂ) * ζ ^ 29 - ((256774 / 18723) : ℂ) * ζ ^ 30 + ((211701 / 31205) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep02CoefficientIdentity06 :
    row18_reducedY23_combinationStep02Coefficient06 =
      row18_reducedY23_combinationStep01Coefficient06 +
        row18_reducedY23_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep02Coefficient06 row18_reducedY23_combinationStep01Coefficient06 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 (((2033131 / 93615) : ℂ) + ((699671 / 37446) : ℂ) * ζ ^ 1 - ((97871 / 93615) : ℂ) * ζ ^ 2 - ((3927487 / 187230) : ℂ) * ζ ^ 3 - ((3900929 / 187230) : ℂ) * ζ ^ 4 - ((10049 / 2370) : ℂ) * ζ ^ 5 + ((1423877 / 93615) : ℂ) * ζ ^ 6 + ((1207867 / 62410) : ℂ) * ζ ^ 7 + ((726628 / 93615) : ℂ) * ζ ^ 8 - ((693221 / 187230) : ℂ) * ζ ^ 9 - ((545221 / 62410) : ℂ) * ζ ^ 10 - ((401643 / 62410) : ℂ) * ζ ^ 11 - ((45759 / 62410) : ℂ) * ζ ^ 12 + ((164822 / 93615) : ℂ) * ζ ^ 13 + ((367049 / 93615) : ℂ) * ζ ^ 14 + ((784529 / 187230) : ℂ) * ζ ^ 15 + ((287359 / 93615) : ℂ) * ζ ^ 16 - ((26663 / 62410) : ℂ) * ζ ^ 17 - ((1289083 / 187230) : ℂ) * ζ ^ 18 - ((776284 / 93615) : ℂ) * ζ ^ 19 - ((540959 / 187230) : ℂ) * ζ ^ 20 + ((919621 / 187230) : ℂ) * ζ ^ 21 + ((281024 / 31205) : ℂ) * ζ ^ 22 + ((182389 / 37446) : ℂ) * ζ ^ 23 - ((540959 / 187230) : ℂ) * ζ ^ 24 - ((768608 / 93615) : ℂ) * ζ ^ 25 - ((374909 / 62410) : ℂ) * ζ ^ 26 + ((150967 / 187230) : ℂ) * ζ ^ 27 + ((813067 / 187230) : ℂ) * ζ ^ 28 + ((16066 / 6241) : ℂ) * ζ ^ 29 + ((6115 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep02CoefficientIdentity07 :
    row18_reducedY23_combinationStep02Coefficient07 =
      row18_reducedY23_combinationStep01Coefficient07 +
        row18_reducedY23_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep02Coefficient07 row18_reducedY23_combinationStep01Coefficient07 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep02CoefficientIdentity08 :
    row18_reducedY23_combinationStep02Coefficient08 =
      row18_reducedY23_combinationStep01Coefficient08 +
        row18_reducedY23_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep02Coefficient08 row18_reducedY23_combinationStep01Coefficient08 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep02CoefficientIdentity09 :
    row18_reducedY23_combinationStep02Coefficient09 =
      row18_reducedY23_combinationStep01Coefficient09 +
        row18_reducedY23_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep02Coefficient09 row18_reducedY23_combinationStep01Coefficient09 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep02CoefficientIdentity10 :
    row18_reducedY23_combinationStep02Coefficient10 =
      row18_reducedY23_combinationStep01Coefficient10 +
        row18_reducedY23_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep02Coefficient10 row18_reducedY23_combinationStep01Coefficient10 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep02CoefficientIdentity11 :
    row18_reducedY23_combinationStep02Coefficient11 =
      row18_reducedY23_combinationStep01Coefficient11 +
        row18_reducedY23_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep02Coefficient11 row18_reducedY23_combinationStep01Coefficient11 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep02CoefficientIdentity12 :
    row18_reducedY23_combinationStep02Coefficient12 =
      row18_reducedY23_combinationStep01Coefficient12 +
        row18_reducedY23_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep02Coefficient12 row18_reducedY23_combinationStep01Coefficient12 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep02CoefficientIdentity13 :
    row18_reducedY23_combinationStep02Coefficient13 =
      row18_reducedY23_combinationStep01Coefficient13 +
        row18_reducedY23_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep02Coefficient13 row18_reducedY23_combinationStep01Coefficient13 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep02CoefficientIdentity14 :
    row18_reducedY23_combinationStep02Coefficient14 =
      row18_reducedY23_combinationStep01Coefficient14 +
        row18_reducedY23_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep02Coefficient14 row18_reducedY23_combinationStep01Coefficient14 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep02CoefficientIdentity15 :
    row18_reducedY23_combinationStep02Coefficient15 =
      row18_reducedY23_combinationStep01Coefficient15 +
        row18_reducedY23_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep02Coefficient15 row18_reducedY23_combinationStep01Coefficient15 row18_reducedY23_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY23_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY23_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY23_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY23_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY23_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY23_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY23_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY23_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY23_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY23_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY23_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY23_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY23_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY23_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY23_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY23_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY23_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY23_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY23_combinationStep02CoefficientIdentity00,
      row18_reducedY23_combinationStep02CoefficientIdentity01,
      row18_reducedY23_combinationStep02CoefficientIdentity02,
      row18_reducedY23_combinationStep02CoefficientIdentity03,
      row18_reducedY23_combinationStep02CoefficientIdentity04,
      row18_reducedY23_combinationStep02CoefficientIdentity05,
      row18_reducedY23_combinationStep02CoefficientIdentity06,
      row18_reducedY23_combinationStep02CoefficientIdentity07,
      row18_reducedY23_combinationStep02CoefficientIdentity08,
      row18_reducedY23_combinationStep02CoefficientIdentity09,
      row18_reducedY23_combinationStep02CoefficientIdentity10,
      row18_reducedY23_combinationStep02CoefficientIdentity11,
      row18_reducedY23_combinationStep02CoefficientIdentity12,
      row18_reducedY23_combinationStep02CoefficientIdentity13,
      row18_reducedY23_combinationStep02CoefficientIdentity14,
      row18_reducedY23_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY23_combinationStep02Multiplier * equation

private def row18_reducedY23_combinationStep03Multiplier : ℂ :=
  (-((1724 / 237) : ℂ) - ((1448 / 237) : ℂ) * ζ ^ 1 + ((470 / 237) : ℂ) * ζ ^ 2 + ((1888 / 237) : ℂ) * ζ ^ 3 - ((396 / 79) : ℂ) * ζ ^ 5 - ((1496 / 237) : ℂ) * ζ ^ 6 + ((298 / 79) : ℂ) * ζ ^ 8 + ((1088 / 237) : ℂ) * ζ ^ 9 - ((800 / 237) : ℂ) * ζ ^ 11 + ((298 / 79) : ℂ) * ζ ^ 12 + ((1448 / 237) : ℂ) * ζ ^ 13 - ((1628 / 237) : ℂ) * ζ ^ 15 + ((1448 / 237) : ℂ) * ζ ^ 17 + ((1966 / 237) : ℂ) * ζ ^ 18 - ((440 / 237) : ℂ) * ζ ^ 21 - ((470 / 237) : ℂ) * ζ ^ 22 - ((260 / 237) : ℂ) * ζ ^ 25 + ((440 / 237) : ℂ) * ζ ^ 27 - ((298 / 79) : ℂ) * ζ ^ 28 - ((1448 / 237) : ℂ) * ζ ^ 29 - ((748 / 237) : ℂ) * ζ ^ 30 + ((800 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY23_combinationStep03Coefficient00 : ℂ :=
  (((527 / 395) : ℂ) + ((134 / 79) : ℂ) * ζ ^ 1 + ((2093 / 790) : ℂ) * ζ ^ 2 + ((1301 / 790) : ℂ) * ζ ^ 3 - ((533 / 790) : ℂ) * ζ ^ 6 + ((294 / 395) : ℂ) * ζ ^ 8 + ((255 / 158) : ℂ) * ζ ^ 9 - ((1613 / 790) : ℂ) * ζ ^ 11 - ((1313 / 395) : ℂ) * ζ ^ 12 - ((134 / 79) : ℂ) * ζ ^ 13 + ((1301 / 790) : ℂ) * ζ ^ 15 - ((134 / 79) : ℂ) * ζ ^ 17 - ((1039 / 790) : ℂ) * ζ ^ 18 - ((134 / 79) : ℂ) * ζ ^ 21 - ((2093 / 790) : ℂ) * ζ ^ 22 + ((2093 / 790) : ℂ) * ζ ^ 24 + ((134 / 79) : ℂ) * ζ ^ 25 - ((1613 / 790) : ℂ) * ζ ^ 27 - ((294 / 395) : ℂ) * ζ ^ 28 + ((134 / 79) : ℂ) * ζ ^ 29 + ((2681 / 790) : ℂ) * ζ ^ 30 + ((1613 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep03CoefficientIdentity00 :
    row18_reducedY23_combinationStep03Coefficient00 =
      row18_reducedY23_combinationStep02Coefficient00 +
        row18_reducedY23_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep03Coefficient00 row18_reducedY23_combinationStep02Coefficient00 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 (-((29651 / 12482) : ℂ) - ((190691 / 37446) : ℂ) * ζ ^ 1 - ((59239 / 12482) : ℂ) * ζ ^ 2 - ((58555 / 37446) : ℂ) * ζ ^ 3 + ((16107 / 6241) : ℂ) * ζ ^ 4 + ((57621 / 12482) : ℂ) * ζ ^ 5 + ((25071 / 6241) : ℂ) * ζ ^ 6 + ((37129 / 37446) : ℂ) * ζ ^ 7 - ((99437 / 37446) : ℂ) * ζ ^ 8 - ((110923 / 37446) : ℂ) * ζ ^ 9 - ((17605 / 6241) : ℂ) * ζ ^ 10 - ((2374 / 18723) : ℂ) * ζ ^ 11 + ((58076 / 18723) : ℂ) * ζ ^ 12 + ((40877 / 12482) : ℂ) * ζ ^ 13 + ((52397 / 37446) : ℂ) * ζ ^ 14 - ((32408 / 18723) : ℂ) * ζ ^ 15 - ((60446 / 18723) : ℂ) * ζ ^ 16 - ((36244 / 18723) : ℂ) * ζ ^ 17 - ((6298 / 18723) : ℂ) * ζ ^ 18 + ((67279 / 37446) : ℂ) * ζ ^ 19 + ((40561 / 18723) : ℂ) * ζ ^ 20 + ((28787 / 37446) : ℂ) * ζ ^ 21 - ((3607 / 18723) : ℂ) * ζ ^ 22 - ((24071 / 18723) : ℂ) * ζ ^ 23 - ((66955 / 37446) : ℂ) * ζ ^ 24 - ((39485 / 37446) : ℂ) * ζ ^ 25 + ((2917 / 6241) : ℂ) * ζ ^ 26 + ((69919 / 37446) : ℂ) * ζ ^ 27 + ((11806 / 18723) : ℂ) * ζ ^ 28 - ((2265 / 6241) : ℂ) * ζ ^ 29 - ((1000 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep03Coefficient01 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep03CoefficientIdentity01 :
    row18_reducedY23_combinationStep03Coefficient01 =
      row18_reducedY23_combinationStep02Coefficient01 +
        row18_reducedY23_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep03Coefficient01 row18_reducedY23_combinationStep02Coefficient01 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 (((125615 / 37446) : ℂ) + ((132809 / 18723) : ℂ) * ζ ^ 1 + ((116279 / 37446) : ℂ) * ζ ^ 2 + ((13703 / 6241) : ℂ) * ζ ^ 3 + ((9478 / 18723) : ℂ) * ζ ^ 4 - ((179405 / 37446) : ℂ) * ζ ^ 5 - ((317713 / 37446) : ℂ) * ζ ^ 6 - ((95165 / 18723) : ℂ) * ζ ^ 7 + ((36957 / 12482) : ℂ) * ζ ^ 8 + ((336617 / 37446) : ℂ) * ζ ^ 9 + ((139136 / 18723) : ℂ) * ζ ^ 10 - ((15161 / 18723) : ℂ) * ζ ^ 11 - ((85401 / 12482) : ℂ) * ζ ^ 12 - ((144368 / 18723) : ℂ) * ζ ^ 13 - ((10394 / 18723) : ℂ) * ζ ^ 14 + ((178561 / 37446) : ℂ) * ζ ^ 15 + ((31804 / 6241) : ℂ) * ζ ^ 16 + ((66275 / 18723) : ℂ) * ζ ^ 17 + ((80807 / 37446) : ℂ) * ζ ^ 18 + ((6635 / 37446) : ℂ) * ζ ^ 19 - ((60241 / 18723) : ℂ) * ζ ^ 20 - ((58925 / 18723) : ℂ) * ζ ^ 21 + ((13997 / 6241) : ℂ) * ζ ^ 22 + ((73381 / 18723) : ℂ) * ζ ^ 23 + ((15100 / 6241) : ℂ) * ζ ^ 24 + ((7367 / 12482) : ℂ) * ζ ^ 25 - ((57562 / 18723) : ℂ) * ζ ^ 26 - ((7735 / 6241) : ℂ) * ζ ^ 27 - ((3224 / 18723) : ℂ) * ζ ^ 28 - ((436 / 18723) : ℂ) * ζ ^ 29 + ((5600 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep03Coefficient02 : ℂ :=
  (-((551 / 237) : ℂ) * ζ ^ 1 - ((585 / 79) : ℂ) * ζ ^ 2 - ((551 / 237) : ℂ) * ζ ^ 3 + ((577 / 237) : ℂ) * ζ ^ 5 + ((140 / 237) : ℂ) * ζ ^ 6 - ((1627 / 474) : ℂ) * ζ ^ 8 - ((865 / 237) : ℂ) * ζ ^ 9 + ((376 / 79) : ℂ) * ζ ^ 11 + ((859 / 237) : ℂ) * ζ ^ 12 + ((551 / 237) : ℂ) * ζ ^ 13 - ((647 / 237) : ℂ) * ζ ^ 15 + ((551 / 237) : ℂ) * ζ ^ 17 + ((585 / 158) : ℂ) * ζ ^ 18 + ((1198 / 237) : ℂ) * ζ ^ 21 + ((585 / 79) : ℂ) * ζ ^ 22 - ((859 / 237) : ℂ) * ζ ^ 24 - ((376 / 79) : ℂ) * ζ ^ 25 + ((865 / 237) : ℂ) * ζ ^ 27 + ((1627 / 474) : ℂ) * ζ ^ 28 - ((551 / 237) : ℂ) * ζ ^ 29 - ((1895 / 237) : ℂ) * ζ ^ 30 - ((376 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep03CoefficientIdentity02 :
    row18_reducedY23_combinationStep03Coefficient02 =
      row18_reducedY23_combinationStep02Coefficient02 +
        row18_reducedY23_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep03Coefficient02 row18_reducedY23_combinationStep02Coefficient02 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep03Coefficient03 : ℂ :=
  (((508 / 237) : ℂ) + ((617 / 158) : ℂ) * ζ ^ 1 + ((2167 / 474) : ℂ) * ζ ^ 2 + ((409 / 158) : ℂ) * ζ ^ 3 - ((725 / 474) : ℂ) * ζ ^ 6 + ((431 / 237) : ℂ) * ζ ^ 8 + ((596 / 237) : ℂ) * ζ ^ 9 - ((350 / 79) : ℂ) * ζ ^ 11 - ((482 / 79) : ℂ) * ζ ^ 12 - ((617 / 158) : ℂ) * ζ ^ 13 + ((409 / 158) : ℂ) * ζ ^ 15 - ((617 / 158) : ℂ) * ζ ^ 17 - ((1151 / 474) : ℂ) * ζ ^ 18 - ((617 / 158) : ℂ) * ζ ^ 21 - ((2167 / 474) : ℂ) * ζ ^ 22 + ((2167 / 474) : ℂ) * ζ ^ 24 + ((617 / 158) : ℂ) * ζ ^ 25 - ((350 / 79) : ℂ) * ζ ^ 27 - ((431 / 237) : ℂ) * ζ ^ 28 + ((617 / 158) : ℂ) * ζ ^ 29 + ((3029 / 474) : ℂ) * ζ ^ 30 + ((350 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep03CoefficientIdentity03 :
    row18_reducedY23_combinationStep03Coefficient03 =
      row18_reducedY23_combinationStep02Coefficient03 +
        row18_reducedY23_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep03Coefficient03 row18_reducedY23_combinationStep02Coefficient03 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep03Coefficient04 : ℂ :=
  (-((370133 / 187230) : ℂ) - ((17680 / 18723) : ℂ) * ζ ^ 1 - ((139707 / 62410) : ℂ) * ζ ^ 2 - ((136261 / 93615) : ℂ) * ζ ^ 3 + ((185821 / 187230) : ℂ) * ζ ^ 6 - ((56561 / 187230) : ℂ) * ζ ^ 8 - ((6085 / 6241) : ℂ) * ζ ^ 9 + ((67891 / 31205) : ℂ) * ζ ^ 11 + ((302471 / 93615) : ℂ) * ζ ^ 12 + ((17680 / 18723) : ℂ) * ζ ^ 13 - ((136261 / 93615) : ℂ) * ζ ^ 15 + ((17680 / 18723) : ℂ) * ζ ^ 17 + ((24494 / 93615) : ℂ) * ζ ^ 18 + ((17680 / 18723) : ℂ) * ζ ^ 21 + ((139707 / 62410) : ℂ) * ζ ^ 22 - ((139707 / 62410) : ℂ) * ζ ^ 24 - ((17680 / 18723) : ℂ) * ζ ^ 25 + ((67891 / 31205) : ℂ) * ζ ^ 27 + ((56561 / 187230) : ℂ) * ζ ^ 28 - ((17680 / 18723) : ℂ) * ζ ^ 29 - ((237841 / 93615) : ℂ) * ζ ^ 30 - ((67891 / 31205) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep03CoefficientIdentity04 :
    row18_reducedY23_combinationStep03Coefficient04 =
      row18_reducedY23_combinationStep02Coefficient04 +
        row18_reducedY23_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep03Coefficient04 row18_reducedY23_combinationStep02Coefficient04 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep03Coefficient05 : ℂ :=
  (((38282 / 18723) : ℂ) + ((11110 / 18723) : ℂ) * ζ ^ 1 - ((6376 / 18723) : ℂ) * ζ ^ 2 - ((37435 / 37446) : ℂ) * ζ ^ 3 + ((13042 / 18723) : ℂ) * ζ ^ 5 + ((2282 / 18723) : ℂ) * ζ ^ 6 - ((20977 / 18723) : ℂ) * ζ ^ 8 - ((28111 / 37446) : ℂ) * ζ ^ 9 + ((1554 / 6241) : ℂ) * ζ ^ 11 - ((20977 / 18723) : ℂ) * ζ ^ 12 - ((11110 / 18723) : ℂ) * ζ ^ 13 + ((41299 / 37446) : ℂ) * ζ ^ 15 - ((11110 / 18723) : ℂ) * ζ ^ 17 - ((2886 / 6241) : ℂ) * ζ ^ 18 + ((15215 / 37446) : ℂ) * ζ ^ 21 + ((6376 / 18723) : ℂ) * ζ ^ 22 - ((644 / 6241) : ℂ) * ζ ^ 25 - ((15215 / 37446) : ℂ) * ζ ^ 27 + ((20977 / 18723) : ℂ) * ζ ^ 28 + ((11110 / 18723) : ℂ) * ζ ^ 29 + ((1141 / 18723) : ℂ) * ζ ^ 30 - ((1554 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep03CoefficientIdentity05 :
    row18_reducedY23_combinationStep03Coefficient05 =
      row18_reducedY23_combinationStep02Coefficient05 +
        row18_reducedY23_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep03Coefficient05 row18_reducedY23_combinationStep02Coefficient05 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 (-((43454 / 18723) : ℂ) - ((3571 / 6241) : ℂ) * ζ ^ 1 - ((8289 / 6241) : ℂ) * ζ ^ 2 - ((2273 / 6241) : ℂ) * ζ ^ 3 + ((32649 / 12482) : ℂ) * ζ ^ 4 + ((8601 / 6241) : ℂ) * ζ ^ 5 - ((250 / 18723) : ℂ) * ζ ^ 6 - ((47327 / 37446) : ℂ) * ζ ^ 7 - ((57395 / 37446) : ℂ) * ζ ^ 8 + ((4136 / 6241) : ℂ) * ζ ^ 9 + ((2156 / 18723) : ℂ) * ζ ^ 10 + ((3041 / 37446) : ℂ) * ζ ^ 11 + ((28543 / 37446) : ℂ) * ζ ^ 12 - ((970 / 6241) : ℂ) * ζ ^ 13 + ((8752 / 18723) : ℂ) * ζ ^ 14 - ((56707 / 37446) : ℂ) * ζ ^ 15 - ((54343 / 37446) : ℂ) * ζ ^ 16 - ((11909 / 37446) : ℂ) * ζ ^ 17 - ((7085 / 18723) : ℂ) * ζ ^ 18 + ((22940 / 18723) : ℂ) * ζ ^ 19 + ((49985 / 37446) : ℂ) * ζ ^ 20 + ((609 / 12482) : ℂ) * ζ ^ 21 + ((17624 / 18723) : ℂ) * ζ ^ 22 + ((9863 / 37446) : ℂ) * ζ ^ 23 - ((6195 / 12482) : ℂ) * ζ ^ 24 - ((23677 / 37446) : ℂ) * ζ ^ 25 - ((2493 / 6241) : ℂ) * ζ ^ 26 + ((6394 / 18723) : ℂ) * ζ ^ 27 - ((124 / 18723) : ℂ) * ζ ^ 28 + ((5818 / 18723) : ℂ) * ζ ^ 29 - ((2800 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep03Coefficient06 : ℂ :=
  (-((408929 / 18723) : ℂ) - ((3821077 / 187230) : ℂ) * ζ ^ 1 + ((3821077 / 187230) : ℂ) * ζ ^ 3 - ((2550871 / 187230) : ℂ) * ζ ^ 5 - ((256774 / 18723) : ℂ) * ζ ^ 6 + ((408929 / 37446) : ℂ) * ζ ^ 8 + ((299584 / 31205) : ℂ) * ζ ^ 9 - ((211701 / 31205) : ℂ) * ζ ^ 11 + ((109123 / 6241) : ℂ) * ζ ^ 12 + ((3821077 / 187230) : ℂ) * ζ ^ 13 - ((2064559 / 93615) : ℂ) * ζ ^ 15 + ((3821077 / 187230) : ℂ) * ζ ^ 17 + ((274535 / 12482) : ℂ) * ζ ^ 18 - ((308041 / 187230) : ℂ) * ζ ^ 21 - ((81560 / 18723) : ℂ) * ζ ^ 24 - ((211701 / 31205) : ℂ) * ζ ^ 25 + ((299584 / 31205) : ℂ) * ζ ^ 27 - ((408929 / 37446) : ℂ) * ζ ^ 28 - ((3821077 / 187230) : ℂ) * ζ ^ 29 - ((256774 / 18723) : ℂ) * ζ ^ 30 + ((211701 / 31205) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep03CoefficientIdentity06 :
    row18_reducedY23_combinationStep03Coefficient06 =
      row18_reducedY23_combinationStep02Coefficient06 +
        row18_reducedY23_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep03Coefficient06 row18_reducedY23_combinationStep02Coefficient06 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep03Coefficient07 : ℂ :=
  (-((56197 / 37446) : ℂ) - ((174385 / 37446) : ℂ) * ζ ^ 1 - ((186577 / 37446) : ℂ) * ζ ^ 2 - ((52048 / 18723) : ℂ) * ζ ^ 3 + ((15125 / 12482) : ℂ) * ζ ^ 6 - ((28219 / 12482) : ℂ) * ζ ^ 8 - ((118093 / 37446) : ℂ) * ζ ^ 9 + ((53629 / 12482) : ℂ) * ζ ^ 11 + ((115976 / 18723) : ℂ) * ζ ^ 12 + ((174385 / 37446) : ℂ) * ζ ^ 13 - ((52048 / 18723) : ℂ) * ζ ^ 15 + ((174385 / 37446) : ℂ) * ζ ^ 17 + ((21730 / 6241) : ℂ) * ζ ^ 18 + ((174385 / 37446) : ℂ) * ζ ^ 21 + ((186577 / 37446) : ℂ) * ζ ^ 22 - ((186577 / 37446) : ℂ) * ζ ^ 24 - ((174385 / 37446) : ℂ) * ζ ^ 25 + ((53629 / 12482) : ℂ) * ζ ^ 27 + ((28219 / 12482) : ℂ) * ζ ^ 28 - ((174385 / 37446) : ℂ) * ζ ^ 29 - ((135617 / 18723) : ℂ) * ζ ^ 30 - ((53629 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep03CoefficientIdentity07 :
    row18_reducedY23_combinationStep03Coefficient07 =
      row18_reducedY23_combinationStep02Coefficient07 +
        row18_reducedY23_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep03Coefficient07 row18_reducedY23_combinationStep02Coefficient07 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 (((29651 / 12482) : ℂ) + ((190691 / 37446) : ℂ) * ζ ^ 1 + ((59239 / 12482) : ℂ) * ζ ^ 2 + ((58555 / 37446) : ℂ) * ζ ^ 3 - ((16107 / 6241) : ℂ) * ζ ^ 4 - ((57621 / 12482) : ℂ) * ζ ^ 5 - ((25071 / 6241) : ℂ) * ζ ^ 6 - ((37129 / 37446) : ℂ) * ζ ^ 7 + ((99437 / 37446) : ℂ) * ζ ^ 8 + ((110923 / 37446) : ℂ) * ζ ^ 9 + ((17605 / 6241) : ℂ) * ζ ^ 10 + ((2374 / 18723) : ℂ) * ζ ^ 11 - ((58076 / 18723) : ℂ) * ζ ^ 12 - ((40877 / 12482) : ℂ) * ζ ^ 13 - ((52397 / 37446) : ℂ) * ζ ^ 14 + ((32408 / 18723) : ℂ) * ζ ^ 15 + ((60446 / 18723) : ℂ) * ζ ^ 16 + ((36244 / 18723) : ℂ) * ζ ^ 17 + ((6298 / 18723) : ℂ) * ζ ^ 18 - ((67279 / 37446) : ℂ) * ζ ^ 19 - ((40561 / 18723) : ℂ) * ζ ^ 20 - ((28787 / 37446) : ℂ) * ζ ^ 21 + ((3607 / 18723) : ℂ) * ζ ^ 22 + ((24071 / 18723) : ℂ) * ζ ^ 23 + ((66955 / 37446) : ℂ) * ζ ^ 24 + ((39485 / 37446) : ℂ) * ζ ^ 25 - ((2917 / 6241) : ℂ) * ζ ^ 26 - ((69919 / 37446) : ℂ) * ζ ^ 27 - ((11806 / 18723) : ℂ) * ζ ^ 28 + ((2265 / 6241) : ℂ) * ζ ^ 29 + ((1000 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep03CoefficientIdentity08 :
    row18_reducedY23_combinationStep03Coefficient08 =
      row18_reducedY23_combinationStep02Coefficient08 +
        row18_reducedY23_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep03Coefficient08 row18_reducedY23_combinationStep02Coefficient08 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep03CoefficientIdentity09 :
    row18_reducedY23_combinationStep03Coefficient09 =
      row18_reducedY23_combinationStep02Coefficient09 +
        row18_reducedY23_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep03Coefficient09 row18_reducedY23_combinationStep02Coefficient09 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep03CoefficientIdentity10 :
    row18_reducedY23_combinationStep03Coefficient10 =
      row18_reducedY23_combinationStep02Coefficient10 +
        row18_reducedY23_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep03Coefficient10 row18_reducedY23_combinationStep02Coefficient10 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep03CoefficientIdentity11 :
    row18_reducedY23_combinationStep03Coefficient11 =
      row18_reducedY23_combinationStep02Coefficient11 +
        row18_reducedY23_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep03Coefficient11 row18_reducedY23_combinationStep02Coefficient11 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep03CoefficientIdentity12 :
    row18_reducedY23_combinationStep03Coefficient12 =
      row18_reducedY23_combinationStep02Coefficient12 +
        row18_reducedY23_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep03Coefficient12 row18_reducedY23_combinationStep02Coefficient12 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep03CoefficientIdentity13 :
    row18_reducedY23_combinationStep03Coefficient13 =
      row18_reducedY23_combinationStep02Coefficient13 +
        row18_reducedY23_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep03Coefficient13 row18_reducedY23_combinationStep02Coefficient13 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep03CoefficientIdentity14 :
    row18_reducedY23_combinationStep03Coefficient14 =
      row18_reducedY23_combinationStep02Coefficient14 +
        row18_reducedY23_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep03Coefficient14 row18_reducedY23_combinationStep02Coefficient14 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep03CoefficientIdentity15 :
    row18_reducedY23_combinationStep03Coefficient15 =
      row18_reducedY23_combinationStep02Coefficient15 +
        row18_reducedY23_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep03Coefficient15 row18_reducedY23_combinationStep02Coefficient15 row18_reducedY23_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY23_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY23_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY23_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY23_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY23_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY23_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY23_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY23_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY23_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY23_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY23_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY23_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY23_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY23_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY23_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY23_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY23_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY23_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY23_combinationStep03CoefficientIdentity00,
      row18_reducedY23_combinationStep03CoefficientIdentity01,
      row18_reducedY23_combinationStep03CoefficientIdentity02,
      row18_reducedY23_combinationStep03CoefficientIdentity03,
      row18_reducedY23_combinationStep03CoefficientIdentity04,
      row18_reducedY23_combinationStep03CoefficientIdentity05,
      row18_reducedY23_combinationStep03CoefficientIdentity06,
      row18_reducedY23_combinationStep03CoefficientIdentity07,
      row18_reducedY23_combinationStep03CoefficientIdentity08,
      row18_reducedY23_combinationStep03CoefficientIdentity09,
      row18_reducedY23_combinationStep03CoefficientIdentity10,
      row18_reducedY23_combinationStep03CoefficientIdentity11,
      row18_reducedY23_combinationStep03CoefficientIdentity12,
      row18_reducedY23_combinationStep03CoefficientIdentity13,
      row18_reducedY23_combinationStep03CoefficientIdentity14,
      row18_reducedY23_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY23_combinationStep03Multiplier * equation

private def row18_reducedY23_combinationStep04Multiplier : ℂ :=
  (((10396 / 1185) : ℂ) * ζ ^ 1 + ((2756 / 395) : ℂ) * ζ ^ 2 + ((10396 / 1185) : ℂ) * ζ ^ 3 + ((1588 / 1185) : ℂ) * ζ ^ 5 - ((4118 / 1185) : ℂ) * ζ ^ 6 + ((360 / 79) : ℂ) * ζ ^ 8 + ((7828 / 1185) : ℂ) * ζ ^ 9 - ((2936 / 395) : ℂ) * ζ ^ 11 - ((2650 / 237) : ℂ) * ζ ^ 12 - ((10396 / 1185) : ℂ) * ζ ^ 13 + ((1496 / 1185) : ℂ) * ζ ^ 15 - ((10396 / 1185) : ℂ) * ζ ^ 17 - ((1378 / 395) : ℂ) * ζ ^ 18 - ((3964 / 395) : ℂ) * ζ ^ 21 - ((2756 / 395) : ℂ) * ζ ^ 22 + ((2650 / 237) : ℂ) * ζ ^ 24 + ((2936 / 395) : ℂ) * ζ ^ 25 - ((7828 / 1185) : ℂ) * ζ ^ 27 - ((360 / 79) : ℂ) * ζ ^ 28 + ((10396 / 1185) : ℂ) * ζ ^ 29 + ((12386 / 1185) : ℂ) * ζ ^ 30 + ((2936 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY23_combinationStep04Coefficient00 : ℂ :=
  (((527 / 395) : ℂ) + ((134 / 79) : ℂ) * ζ ^ 1 + ((2093 / 790) : ℂ) * ζ ^ 2 + ((1301 / 790) : ℂ) * ζ ^ 3 - ((533 / 790) : ℂ) * ζ ^ 6 + ((294 / 395) : ℂ) * ζ ^ 8 + ((255 / 158) : ℂ) * ζ ^ 9 - ((1613 / 790) : ℂ) * ζ ^ 11 - ((1313 / 395) : ℂ) * ζ ^ 12 - ((134 / 79) : ℂ) * ζ ^ 13 + ((1301 / 790) : ℂ) * ζ ^ 15 - ((134 / 79) : ℂ) * ζ ^ 17 - ((1039 / 790) : ℂ) * ζ ^ 18 - ((134 / 79) : ℂ) * ζ ^ 21 - ((2093 / 790) : ℂ) * ζ ^ 22 + ((2093 / 790) : ℂ) * ζ ^ 24 + ((134 / 79) : ℂ) * ζ ^ 25 - ((1613 / 790) : ℂ) * ζ ^ 27 - ((294 / 395) : ℂ) * ζ ^ 28 + ((134 / 79) : ℂ) * ζ ^ 29 + ((2681 / 790) : ℂ) * ζ ^ 30 + ((1613 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep04CoefficientIdentity00 :
    row18_reducedY23_combinationStep04Coefficient00 =
      row18_reducedY23_combinationStep03Coefficient00 +
        row18_reducedY23_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep04Coefficient00 row18_reducedY23_combinationStep03Coefficient00 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep04Coefficient01 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep04CoefficientIdentity01 :
    row18_reducedY23_combinationStep04Coefficient01 =
      row18_reducedY23_combinationStep03Coefficient01 +
        row18_reducedY23_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep04Coefficient01 row18_reducedY23_combinationStep03Coefficient01 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep04Coefficient02 : ℂ :=
  (-((430939 / 187230) : ℂ) * ζ ^ 1 - ((160061 / 31205) : ℂ) * ζ ^ 2 - ((430939 / 187230) : ℂ) * ζ ^ 3 + ((284173 / 187230) : ℂ) * ζ ^ 5 + ((2186 / 31205) : ℂ) * ζ ^ 6 - ((119755 / 37446) : ℂ) * ζ ^ 8 - ((71582 / 31205) : ℂ) * ζ ^ 9 + ((357556 / 93615) : ℂ) * ζ ^ 11 + ((18253 / 6241) : ℂ) * ζ ^ 12 + ((430939 / 187230) : ℂ) * ζ ^ 13 - ((109112 / 93615) : ℂ) * ζ ^ 15 + ((430939 / 187230) : ℂ) * ζ ^ 17 + ((160061 / 62410) : ℂ) * ζ ^ 18 + ((649163 / 187230) : ℂ) * ζ ^ 21 + ((160061 / 31205) : ℂ) * ζ ^ 22 - ((18253 / 6241) : ℂ) * ζ ^ 24 - ((357556 / 93615) : ℂ) * ζ ^ 25 + ((71582 / 31205) : ℂ) * ζ ^ 27 + ((119755 / 37446) : ℂ) * ζ ^ 28 - ((430939 / 187230) : ℂ) * ζ ^ 29 - ((162247 / 31205) : ℂ) * ζ ^ 30 - ((357556 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep04CoefficientIdentity02 :
    row18_reducedY23_combinationStep04Coefficient02 =
      row18_reducedY23_combinationStep03Coefficient02 +
        row18_reducedY23_combinationStep04Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep04Coefficient02 row18_reducedY23_combinationStep03Coefficient02 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 (-((66727 / 187230) : ℂ) * ζ ^ 1 - ((209257 / 93615) : ℂ) * ζ ^ 2 - ((154361 / 62410) : ℂ) * ζ ^ 3 - ((141908 / 93615) : ℂ) * ζ ^ 4 - ((102353 / 93615) : ℂ) * ζ ^ 5 + ((230537 / 93615) : ℂ) * ζ ^ 6 + ((64031 / 93615) : ℂ) * ζ ^ 7 + ((153079 / 187230) : ℂ) * ζ ^ 8 - ((27472 / 93615) : ℂ) * ζ ^ 9 - ((290146 / 93615) : ℂ) * ζ ^ 10 - ((80461 / 187230) : ℂ) * ζ ^ 11 - ((10487 / 37446) : ℂ) * ζ ^ 12 + ((456953 / 187230) : ℂ) * ζ ^ 13 + ((71883 / 31205) : ℂ) * ζ ^ 14 - ((36668 / 31205) : ℂ) * ζ ^ 15 - ((290003 / 187230) : ℂ) * ζ ^ 16 - ((214759 / 93615) : ℂ) * ζ ^ 17 - ((247093 / 187230) : ℂ) * ζ ^ 18 - ((19843 / 187230) : ℂ) * ζ ^ 19 - ((65329 / 93615) : ℂ) * ζ ^ 20 + ((119467 / 93615) : ℂ) * ζ ^ 21 + ((223079 / 187230) : ℂ) * ζ ^ 22 + ((172317 / 62410) : ℂ) * ζ ^ 23 + ((145334 / 93615) : ℂ) * ζ ^ 24 - ((5649 / 12482) : ℂ) * ζ ^ 25 - ((175577 / 187230) : ℂ) * ζ ^ 26 - ((13799 / 12482) : ℂ) * ζ ^ 27 + ((3688 / 31205) : ℂ) * ζ ^ 28 + ((8119 / 93615) : ℂ) * ζ ^ 29 + ((10276 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep04Coefficient03 : ℂ :=
  (((56197 / 37446) : ℂ) + ((174385 / 37446) : ℂ) * ζ ^ 1 + ((186577 / 37446) : ℂ) * ζ ^ 2 + ((52048 / 18723) : ℂ) * ζ ^ 3 - ((15125 / 12482) : ℂ) * ζ ^ 6 + ((28219 / 12482) : ℂ) * ζ ^ 8 + ((118093 / 37446) : ℂ) * ζ ^ 9 - ((53629 / 12482) : ℂ) * ζ ^ 11 - ((115976 / 18723) : ℂ) * ζ ^ 12 - ((174385 / 37446) : ℂ) * ζ ^ 13 + ((52048 / 18723) : ℂ) * ζ ^ 15 - ((174385 / 37446) : ℂ) * ζ ^ 17 - ((21730 / 6241) : ℂ) * ζ ^ 18 - ((174385 / 37446) : ℂ) * ζ ^ 21 - ((186577 / 37446) : ℂ) * ζ ^ 22 + ((186577 / 37446) : ℂ) * ζ ^ 24 + ((174385 / 37446) : ℂ) * ζ ^ 25 - ((53629 / 12482) : ℂ) * ζ ^ 27 - ((28219 / 12482) : ℂ) * ζ ^ 28 + ((174385 / 37446) : ℂ) * ζ ^ 29 + ((135617 / 18723) : ℂ) * ζ ^ 30 + ((53629 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep04CoefficientIdentity03 :
    row18_reducedY23_combinationStep04Coefficient03 =
      row18_reducedY23_combinationStep03Coefficient03 +
        row18_reducedY23_combinationStep04Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep04Coefficient03 row18_reducedY23_combinationStep03Coefficient03 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 (((24067 / 37446) : ℂ) + ((1379 / 1185) : ℂ) * ζ ^ 1 - ((116752 / 93615) : ℂ) * ζ ^ 2 + ((18239 / 187230) : ℂ) * ζ ^ 3 - ((129937 / 62410) : ℂ) * ζ ^ 4 - ((883 / 18723) : ℂ) * ζ ^ 5 - ((342239 / 187230) : ℂ) * ζ ^ 6 + ((108988 / 93615) : ℂ) * ζ ^ 7 + ((376051 / 187230) : ℂ) * ζ ^ 8 - ((123763 / 187230) : ℂ) * ζ ^ 9 + ((28579 / 62410) : ℂ) * ζ ^ 10 - ((129299 / 93615) : ℂ) * ζ ^ 11 - ((5663 / 187230) : ℂ) * ζ ^ 12 + ((88663 / 93615) : ℂ) * ζ ^ 13 + ((54917 / 31205) : ℂ) * ζ ^ 14 + ((430517 / 187230) : ℂ) * ζ ^ 15 + ((39143 / 187230) : ℂ) * ζ ^ 16 - ((51152 / 93615) : ℂ) * ζ ^ 17 + ((333607 / 187230) : ℂ) * ζ ^ 18 + ((113536 / 93615) : ℂ) * ζ ^ 19 + ((473861 / 187230) : ℂ) * ζ ^ 20 + ((75382 / 93615) : ℂ) * ζ ^ 21 + ((866543 / 187230) : ℂ) * ζ ^ 22 + ((229213 / 93615) : ℂ) * ζ ^ 23 + ((19327 / 18723) : ℂ) * ζ ^ 24 + ((154807 / 187230) : ℂ) * ζ ^ 25 - ((88739 / 93615) : ℂ) * ζ ^ 26 + ((62699 / 187230) : ℂ) * ζ ^ 27 + ((13828 / 93615) : ℂ) * ζ ^ 28 + ((63665 / 37446) : ℂ) * ζ ^ 29 + ((9542 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep04Coefficient04 : ℂ :=
  (-((527 / 395) : ℂ) - ((134 / 79) : ℂ) * ζ ^ 1 - ((2093 / 790) : ℂ) * ζ ^ 2 - ((1301 / 790) : ℂ) * ζ ^ 3 + ((533 / 790) : ℂ) * ζ ^ 6 - ((294 / 395) : ℂ) * ζ ^ 8 - ((255 / 158) : ℂ) * ζ ^ 9 + ((1613 / 790) : ℂ) * ζ ^ 11 + ((1313 / 395) : ℂ) * ζ ^ 12 + ((134 / 79) : ℂ) * ζ ^ 13 - ((1301 / 790) : ℂ) * ζ ^ 15 + ((134 / 79) : ℂ) * ζ ^ 17 + ((1039 / 790) : ℂ) * ζ ^ 18 + ((134 / 79) : ℂ) * ζ ^ 21 + ((2093 / 790) : ℂ) * ζ ^ 22 - ((2093 / 790) : ℂ) * ζ ^ 24 - ((134 / 79) : ℂ) * ζ ^ 25 + ((1613 / 790) : ℂ) * ζ ^ 27 + ((294 / 395) : ℂ) * ζ ^ 28 - ((134 / 79) : ℂ) * ζ ^ 29 - ((2681 / 790) : ℂ) * ζ ^ 30 - ((1613 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep04CoefficientIdentity04 :
    row18_reducedY23_combinationStep04Coefficient04 =
      row18_reducedY23_combinationStep03Coefficient04 +
        row18_reducedY23_combinationStep04Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep04Coefficient04 row18_reducedY23_combinationStep03Coefficient04 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 (-((24067 / 37446) : ℂ) - ((1379 / 1185) : ℂ) * ζ ^ 1 + ((116752 / 93615) : ℂ) * ζ ^ 2 - ((18239 / 187230) : ℂ) * ζ ^ 3 + ((129937 / 62410) : ℂ) * ζ ^ 4 + ((883 / 18723) : ℂ) * ζ ^ 5 + ((342239 / 187230) : ℂ) * ζ ^ 6 - ((108988 / 93615) : ℂ) * ζ ^ 7 - ((376051 / 187230) : ℂ) * ζ ^ 8 + ((123763 / 187230) : ℂ) * ζ ^ 9 - ((28579 / 62410) : ℂ) * ζ ^ 10 + ((129299 / 93615) : ℂ) * ζ ^ 11 + ((5663 / 187230) : ℂ) * ζ ^ 12 - ((88663 / 93615) : ℂ) * ζ ^ 13 - ((54917 / 31205) : ℂ) * ζ ^ 14 - ((430517 / 187230) : ℂ) * ζ ^ 15 - ((39143 / 187230) : ℂ) * ζ ^ 16 + ((51152 / 93615) : ℂ) * ζ ^ 17 - ((333607 / 187230) : ℂ) * ζ ^ 18 - ((113536 / 93615) : ℂ) * ζ ^ 19 - ((473861 / 187230) : ℂ) * ζ ^ 20 - ((75382 / 93615) : ℂ) * ζ ^ 21 - ((866543 / 187230) : ℂ) * ζ ^ 22 - ((229213 / 93615) : ℂ) * ζ ^ 23 - ((19327 / 18723) : ℂ) * ζ ^ 24 - ((154807 / 187230) : ℂ) * ζ ^ 25 + ((88739 / 93615) : ℂ) * ζ ^ 26 - ((62699 / 187230) : ℂ) * ζ ^ 27 - ((13828 / 93615) : ℂ) * ζ ^ 28 - ((63665 / 37446) : ℂ) * ζ ^ 29 - ((9542 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep04Coefficient05 : ℂ :=
  (((38282 / 18723) : ℂ) + ((11110 / 18723) : ℂ) * ζ ^ 1 - ((6376 / 18723) : ℂ) * ζ ^ 2 - ((37435 / 37446) : ℂ) * ζ ^ 3 + ((13042 / 18723) : ℂ) * ζ ^ 5 + ((2282 / 18723) : ℂ) * ζ ^ 6 - ((20977 / 18723) : ℂ) * ζ ^ 8 - ((28111 / 37446) : ℂ) * ζ ^ 9 + ((1554 / 6241) : ℂ) * ζ ^ 11 - ((20977 / 18723) : ℂ) * ζ ^ 12 - ((11110 / 18723) : ℂ) * ζ ^ 13 + ((41299 / 37446) : ℂ) * ζ ^ 15 - ((11110 / 18723) : ℂ) * ζ ^ 17 - ((2886 / 6241) : ℂ) * ζ ^ 18 + ((15215 / 37446) : ℂ) * ζ ^ 21 + ((6376 / 18723) : ℂ) * ζ ^ 22 - ((644 / 6241) : ℂ) * ζ ^ 25 - ((15215 / 37446) : ℂ) * ζ ^ 27 + ((20977 / 18723) : ℂ) * ζ ^ 28 + ((11110 / 18723) : ℂ) * ζ ^ 29 + ((1141 / 18723) : ℂ) * ζ ^ 30 - ((1554 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep04CoefficientIdentity05 :
    row18_reducedY23_combinationStep04Coefficient05 =
      row18_reducedY23_combinationStep03Coefficient05 +
        row18_reducedY23_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep04Coefficient05 row18_reducedY23_combinationStep03Coefficient05 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep04Coefficient06 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep04CoefficientIdentity06 :
    row18_reducedY23_combinationStep04Coefficient06 =
      row18_reducedY23_combinationStep03Coefficient06 +
        row18_reducedY23_combinationStep04Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep04Coefficient06 row18_reducedY23_combinationStep03Coefficient06 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 (-((408929 / 18723) : ℂ) - ((3987413 / 187230) : ℂ) * ζ ^ 1 - ((71429 / 31205) : ℂ) * ζ ^ 2 + ((2644601 / 187230) : ℂ) * ζ ^ 3 + ((596214 / 31205) : ℂ) * ζ ^ 4 + ((95495 / 18723) : ℂ) * ζ ^ 5 - ((1113847 / 93615) : ℂ) * ζ ^ 6 - ((508446 / 31205) : ℂ) * ζ ^ 7 - ((293419 / 31205) : ℂ) * ζ ^ 8 + ((467239 / 187230) : ℂ) * ζ ^ 9 + ((514151 / 93615) : ℂ) * ζ ^ 10 + ((137620 / 18723) : ℂ) * ζ ^ 11 + ((218179 / 31205) : ℂ) * ζ ^ 12 + ((348779 / 93615) : ℂ) * ζ ^ 13 - ((69485 / 37446) : ℂ) * ζ ^ 14 - ((1898147 / 187230) : ℂ) * ζ ^ 15 - ((166858 / 18723) : ℂ) * ζ ^ 16 + ((39347 / 18723) : ℂ) * ζ ^ 17 + ((237499 / 18723) : ℂ) * ζ ^ 18 + ((549987 / 31205) : ℂ) * ζ ^ 19 + ((747073 / 187230) : ℂ) * ζ ^ 20 - ((1396319 / 187230) : ℂ) * ζ ^ 21 - ((272496 / 31205) : ℂ) * ζ ^ 22 - ((17897 / 18723) : ℂ) * ζ ^ 23 + ((259081 / 31205) : ℂ) * ζ ^ 24 + ((215737 / 31205) : ℂ) * ζ ^ 25 + ((258619 / 93615) : ℂ) * ζ ^ 26 - ((151667 / 62410) : ℂ) * ζ ^ 27 - ((272602 / 93615) : ℂ) * ζ ^ 28 - ((27910 / 18723) : ℂ) * ζ ^ 29 - ((20552 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep04Coefficient07 : ℂ :=
  (-((56197 / 37446) : ℂ) - ((174385 / 37446) : ℂ) * ζ ^ 1 - ((186577 / 37446) : ℂ) * ζ ^ 2 - ((52048 / 18723) : ℂ) * ζ ^ 3 + ((15125 / 12482) : ℂ) * ζ ^ 6 - ((28219 / 12482) : ℂ) * ζ ^ 8 - ((118093 / 37446) : ℂ) * ζ ^ 9 + ((53629 / 12482) : ℂ) * ζ ^ 11 + ((115976 / 18723) : ℂ) * ζ ^ 12 + ((174385 / 37446) : ℂ) * ζ ^ 13 - ((52048 / 18723) : ℂ) * ζ ^ 15 + ((174385 / 37446) : ℂ) * ζ ^ 17 + ((21730 / 6241) : ℂ) * ζ ^ 18 + ((174385 / 37446) : ℂ) * ζ ^ 21 + ((186577 / 37446) : ℂ) * ζ ^ 22 - ((186577 / 37446) : ℂ) * ζ ^ 24 - ((174385 / 37446) : ℂ) * ζ ^ 25 + ((53629 / 12482) : ℂ) * ζ ^ 27 + ((28219 / 12482) : ℂ) * ζ ^ 28 - ((174385 / 37446) : ℂ) * ζ ^ 29 - ((135617 / 18723) : ℂ) * ζ ^ 30 - ((53629 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep04CoefficientIdentity07 :
    row18_reducedY23_combinationStep04Coefficient07 =
      row18_reducedY23_combinationStep03Coefficient07 +
        row18_reducedY23_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep04Coefficient07 row18_reducedY23_combinationStep03Coefficient07 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep04Coefficient08 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep04CoefficientIdentity08 :
    row18_reducedY23_combinationStep04Coefficient08 =
      row18_reducedY23_combinationStep03Coefficient08 +
        row18_reducedY23_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep04Coefficient08 row18_reducedY23_combinationStep03Coefficient08 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep04Coefficient09 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep04CoefficientIdentity09 :
    row18_reducedY23_combinationStep04Coefficient09 =
      row18_reducedY23_combinationStep03Coefficient09 +
        row18_reducedY23_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep04Coefficient09 row18_reducedY23_combinationStep03Coefficient09 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep04Coefficient10 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep04CoefficientIdentity10 :
    row18_reducedY23_combinationStep04Coefficient10 =
      row18_reducedY23_combinationStep03Coefficient10 +
        row18_reducedY23_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep04Coefficient10 row18_reducedY23_combinationStep03Coefficient10 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep04Coefficient11 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep04CoefficientIdentity11 :
    row18_reducedY23_combinationStep04Coefficient11 =
      row18_reducedY23_combinationStep03Coefficient11 +
        row18_reducedY23_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep04Coefficient11 row18_reducedY23_combinationStep03Coefficient11 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep04Coefficient12 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep04CoefficientIdentity12 :
    row18_reducedY23_combinationStep04Coefficient12 =
      row18_reducedY23_combinationStep03Coefficient12 +
        row18_reducedY23_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep04Coefficient12 row18_reducedY23_combinationStep03Coefficient12 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep04Coefficient13 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep04CoefficientIdentity13 :
    row18_reducedY23_combinationStep04Coefficient13 =
      row18_reducedY23_combinationStep03Coefficient13 +
        row18_reducedY23_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep04Coefficient13 row18_reducedY23_combinationStep03Coefficient13 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep04Coefficient14 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep04CoefficientIdentity14 :
    row18_reducedY23_combinationStep04Coefficient14 =
      row18_reducedY23_combinationStep03Coefficient14 +
        row18_reducedY23_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep04Coefficient14 row18_reducedY23_combinationStep03Coefficient14 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep04Coefficient15 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep04CoefficientIdentity15 :
    row18_reducedY23_combinationStep04Coefficient15 =
      row18_reducedY23_combinationStep03Coefficient15 +
        row18_reducedY23_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep04Coefficient15 row18_reducedY23_combinationStep03Coefficient15 row18_reducedY23_combinationStep04Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY23_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY23_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY23_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY23_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY23_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY23_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY23_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY23_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY23_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY23_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY23_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY23_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY23_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY23_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY23_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY23_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY23_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY23_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY23_combinationStep04CoefficientIdentity00,
      row18_reducedY23_combinationStep04CoefficientIdentity01,
      row18_reducedY23_combinationStep04CoefficientIdentity02,
      row18_reducedY23_combinationStep04CoefficientIdentity03,
      row18_reducedY23_combinationStep04CoefficientIdentity04,
      row18_reducedY23_combinationStep04CoefficientIdentity05,
      row18_reducedY23_combinationStep04CoefficientIdentity06,
      row18_reducedY23_combinationStep04CoefficientIdentity07,
      row18_reducedY23_combinationStep04CoefficientIdentity08,
      row18_reducedY23_combinationStep04CoefficientIdentity09,
      row18_reducedY23_combinationStep04CoefficientIdentity10,
      row18_reducedY23_combinationStep04CoefficientIdentity11,
      row18_reducedY23_combinationStep04CoefficientIdentity12,
      row18_reducedY23_combinationStep04CoefficientIdentity13,
      row18_reducedY23_combinationStep04CoefficientIdentity14,
      row18_reducedY23_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY23_combinationStep04Multiplier * equation

private def row18_reducedY23_combinationStep05Multiplier : ℂ :=
  (-((480 / 79) : ℂ) - ((1364 / 237) : ℂ) * ζ ^ 1 + ((572 / 237) : ℂ) * ζ ^ 2 + ((1186 / 237) : ℂ) * ζ ^ 3 - ((1460 / 237) : ℂ) * ζ ^ 5 - ((724 / 237) : ℂ) * ζ ^ 6 + ((1136 / 237) : ℂ) * ζ ^ 8 + ((634 / 237) : ℂ) * ζ ^ 9 - ((742 / 237) : ℂ) * ζ ^ 11 + ((432 / 79) : ℂ) * ζ ^ 12 + ((1364 / 237) : ℂ) * ζ ^ 13 - ((1186 / 237) : ℂ) * ζ ^ 15 + ((1364 / 237) : ℂ) * ζ ^ 17 + ((868 / 237) : ℂ) * ζ ^ 18 + ((32 / 79) : ℂ) * ζ ^ 21 - ((572 / 237) : ℂ) * ζ ^ 22 - ((572 / 237) : ℂ) * ζ ^ 24 + ((32 / 79) : ℂ) * ζ ^ 25 + ((742 / 237) : ℂ) * ζ ^ 27 - ((1136 / 237) : ℂ) * ζ ^ 28 - ((1364 / 237) : ℂ) * ζ ^ 29 - ((188 / 79) : ℂ) * ζ ^ 30 + ((742 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY23_combinationStep05Coefficient00 : ℂ :=
  (((527 / 395) : ℂ) + ((134 / 79) : ℂ) * ζ ^ 1 + ((2093 / 790) : ℂ) * ζ ^ 2 + ((1301 / 790) : ℂ) * ζ ^ 3 - ((533 / 790) : ℂ) * ζ ^ 6 + ((294 / 395) : ℂ) * ζ ^ 8 + ((255 / 158) : ℂ) * ζ ^ 9 - ((1613 / 790) : ℂ) * ζ ^ 11 - ((1313 / 395) : ℂ) * ζ ^ 12 - ((134 / 79) : ℂ) * ζ ^ 13 + ((1301 / 790) : ℂ) * ζ ^ 15 - ((134 / 79) : ℂ) * ζ ^ 17 - ((1039 / 790) : ℂ) * ζ ^ 18 - ((134 / 79) : ℂ) * ζ ^ 21 - ((2093 / 790) : ℂ) * ζ ^ 22 + ((2093 / 790) : ℂ) * ζ ^ 24 + ((134 / 79) : ℂ) * ζ ^ 25 - ((1613 / 790) : ℂ) * ζ ^ 27 - ((294 / 395) : ℂ) * ζ ^ 28 + ((134 / 79) : ℂ) * ζ ^ 29 + ((2681 / 790) : ℂ) * ζ ^ 30 + ((1613 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep05CoefficientIdentity00 :
    row18_reducedY23_combinationStep05Coefficient00 =
      row18_reducedY23_combinationStep04Coefficient00 +
        row18_reducedY23_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep05Coefficient00 row18_reducedY23_combinationStep04Coefficient00 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep05Coefficient01 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep05CoefficientIdentity01 :
    row18_reducedY23_combinationStep05Coefficient01 =
      row18_reducedY23_combinationStep04Coefficient01 +
        row18_reducedY23_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep05Coefficient01 row18_reducedY23_combinationStep04Coefficient01 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep05Coefficient02 : ℂ :=
  (((84 / 395) : ℂ) * ζ ^ 1 - ((114 / 395) : ℂ) * ζ ^ 2 + ((84 / 395) : ℂ) * ζ ^ 3 - ((18 / 395) : ℂ) * ζ ^ 5 - ((51 / 395) : ℂ) * ζ ^ 6 - ((32 / 79) : ℂ) * ζ ^ 8 - ((198 / 395) : ℂ) * ζ ^ 9 - ((102 / 395) : ℂ) * ζ ^ 11 + ((20 / 79) : ℂ) * ζ ^ 12 - ((84 / 395) : ℂ) * ζ ^ 13 - ((206 / 395) : ℂ) * ζ ^ 15 - ((84 / 395) : ℂ) * ζ ^ 17 + ((57 / 395) : ℂ) * ζ ^ 18 + ((122 / 395) : ℂ) * ζ ^ 21 + ((114 / 395) : ℂ) * ζ ^ 22 - ((20 / 79) : ℂ) * ζ ^ 24 + ((102 / 395) : ℂ) * ζ ^ 25 + ((198 / 395) : ℂ) * ζ ^ 27 + ((32 / 79) : ℂ) * ζ ^ 28 + ((84 / 395) : ℂ) * ζ ^ 29 - ((63 / 395) : ℂ) * ζ ^ 30 + ((102 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep05CoefficientIdentity02 :
    row18_reducedY23_combinationStep05Coefficient02 =
      row18_reducedY23_combinationStep04Coefficient02 +
        row18_reducedY23_combinationStep05Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep05Coefficient02 row18_reducedY23_combinationStep04Coefficient02 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 (-((4560 / 6241) : ℂ) - ((110707 / 37446) : ℂ) * ζ ^ 1 - ((28242 / 6241) : ℂ) * ζ ^ 2 - ((65557 / 37446) : ℂ) * ζ ^ 3 + ((13055 / 12482) : ℂ) * ζ ^ 4 + ((141167 / 37446) : ℂ) * ζ ^ 5 + ((22322 / 6241) : ℂ) * ζ ^ 6 + ((13015 / 12482) : ℂ) * ζ ^ 7 - ((28213 / 18723) : ℂ) * ζ ^ 8 - ((74065 / 37446) : ℂ) * ζ ^ 9 - ((91391 / 37446) : ℂ) * ζ ^ 10 - ((5227 / 37446) : ℂ) * ζ ^ 11 + ((62033 / 37446) : ℂ) * ζ ^ 12 + ((15539 / 6241) : ℂ) * ζ ^ 13 + ((18851 / 18723) : ℂ) * ζ ^ 14 - ((13069 / 12482) : ℂ) * ζ ^ 15 - ((13212 / 6241) : ℂ) * ζ ^ 16 - ((66703 / 37446) : ℂ) * ζ ^ 17 - ((25681 / 37446) : ℂ) * ζ ^ 18 + ((8125 / 6241) : ℂ) * ζ ^ 19 + ((22253 / 12482) : ℂ) * ζ ^ 20 + ((15985 / 12482) : ℂ) * ζ ^ 21 - ((104 / 6241) : ℂ) * ζ ^ 22 - ((43709 / 37446) : ℂ) * ζ ^ 23 - ((73051 / 37446) : ℂ) * ζ ^ 24 - ((20657 / 18723) : ℂ) * ζ ^ 25 + ((25057 / 37446) : ℂ) * ζ ^ 26 + ((66811 / 37446) : ℂ) * ζ ^ 27 + ((18943 / 37446) : ℂ) * ζ ^ 28 - ((2263 / 6241) : ℂ) * ζ ^ 29 - ((1855 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep05Coefficient03 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep05CoefficientIdentity03 :
    row18_reducedY23_combinationStep05Coefficient03 =
      row18_reducedY23_combinationStep04Coefficient03 +
        row18_reducedY23_combinationStep05Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep05Coefficient03 row18_reducedY23_combinationStep04Coefficient03 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 (((33157 / 37446) : ℂ) + ((111521 / 37446) : ℂ) * ζ ^ 1 + ((16525 / 12482) : ℂ) * ζ ^ 2 + ((46598 / 18723) : ℂ) * ζ ^ 3 + ((15962 / 6241) : ℂ) * ζ ^ 4 - ((69553 / 18723) : ℂ) * ζ ^ 5 - ((260641 / 37446) : ℂ) * ζ ^ 6 - ((97286 / 18723) : ℂ) * ζ ^ 7 + ((76087 / 37446) : ℂ) * ζ ^ 8 + ((260177 / 37446) : ℂ) * ζ ^ 9 + ((108380 / 18723) : ℂ) * ζ ^ 10 + ((16454 / 18723) : ℂ) * ζ ^ 11 - ((180901 / 37446) : ℂ) * ζ ^ 12 - ((93320 / 18723) : ℂ) * ζ ^ 13 - ((18517 / 18723) : ℂ) * ζ ^ 14 + ((43031 / 18723) : ℂ) * ζ ^ 15 + ((23738 / 6241) : ℂ) * ζ ^ 16 + ((136909 / 37446) : ℂ) * ζ ^ 17 + ((61034 / 18723) : ℂ) * ζ ^ 18 + ((16708 / 18723) : ℂ) * ζ ^ 19 - ((85606 / 18723) : ℂ) * ζ ^ 20 - ((104497 / 37446) : ℂ) * ζ ^ 21 + ((30838 / 18723) : ℂ) * ζ ^ 22 + ((76454 / 18723) : ℂ) * ζ ^ 23 + ((96569 / 37446) : ℂ) * ζ ^ 24 + ((854 / 6241) : ℂ) * ζ ^ 25 - ((52802 / 18723) : ℂ) * ζ ^ 26 - ((21947 / 18723) : ℂ) * ζ ^ 27 - ((4717 / 37446) : ℂ) * ζ ^ 28 + ((168 / 6241) : ℂ) * ζ ^ 29 + ((5194 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep05Coefficient04 : ℂ :=
  (-((527 / 395) : ℂ) - ((134 / 79) : ℂ) * ζ ^ 1 - ((2093 / 790) : ℂ) * ζ ^ 2 - ((1301 / 790) : ℂ) * ζ ^ 3 + ((533 / 790) : ℂ) * ζ ^ 6 - ((294 / 395) : ℂ) * ζ ^ 8 - ((255 / 158) : ℂ) * ζ ^ 9 + ((1613 / 790) : ℂ) * ζ ^ 11 + ((1313 / 395) : ℂ) * ζ ^ 12 + ((134 / 79) : ℂ) * ζ ^ 13 - ((1301 / 790) : ℂ) * ζ ^ 15 + ((134 / 79) : ℂ) * ζ ^ 17 + ((1039 / 790) : ℂ) * ζ ^ 18 + ((134 / 79) : ℂ) * ζ ^ 21 + ((2093 / 790) : ℂ) * ζ ^ 22 - ((2093 / 790) : ℂ) * ζ ^ 24 - ((134 / 79) : ℂ) * ζ ^ 25 + ((1613 / 790) : ℂ) * ζ ^ 27 + ((294 / 395) : ℂ) * ζ ^ 28 - ((134 / 79) : ℂ) * ζ ^ 29 - ((2681 / 790) : ℂ) * ζ ^ 30 - ((1613 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep05CoefficientIdentity04 :
    row18_reducedY23_combinationStep05Coefficient04 =
      row18_reducedY23_combinationStep04Coefficient04 +
        row18_reducedY23_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep05Coefficient04 row18_reducedY23_combinationStep04Coefficient04 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep05Coefficient05 : ℂ :=
  (((148 / 79) : ℂ) + ((75 / 79) : ℂ) * ζ ^ 1 - ((89 / 158) : ℂ) * ζ ^ 2 - ((181 / 158) : ℂ) * ζ ^ 3 + ((179 / 158) : ℂ) * ζ ^ 5 + ((26 / 79) : ℂ) * ζ ^ 6 - ((205 / 158) : ℂ) * ζ ^ 8 - ((99 / 158) : ℂ) * ζ ^ 9 + ((41 / 79) : ℂ) * ζ ^ 11 - ((205 / 158) : ℂ) * ζ ^ 12 - ((75 / 79) : ℂ) * ζ ^ 13 + ((105 / 79) : ℂ) * ζ ^ 15 - ((75 / 79) : ℂ) * ζ ^ 17 - ((141 / 158) : ℂ) * ζ ^ 18 + ((31 / 158) : ℂ) * ζ ^ 21 + ((89 / 158) : ℂ) * ζ ^ 22 - ((29 / 158) : ℂ) * ζ ^ 25 - ((31 / 158) : ℂ) * ζ ^ 27 + ((205 / 158) : ℂ) * ζ ^ 28 + ((75 / 79) : ℂ) * ζ ^ 29 + ((13 / 79) : ℂ) * ζ ^ 30 - ((41 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY23_combinationStep05CoefficientIdentity05 :
    row18_reducedY23_combinationStep05Coefficient05 =
      row18_reducedY23_combinationStep04Coefficient05 +
        row18_reducedY23_combinationStep05Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep05Coefficient05 row18_reducedY23_combinationStep04Coefficient05 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 (((28046 / 18723) : ℂ) - ((13736 / 18723) : ℂ) * ζ ^ 1 - ((20961 / 12482) : ℂ) * ζ ^ 2 + ((4571 / 12482) : ℂ) * ζ ^ 3 + ((3157 / 12482) : ℂ) * ζ ^ 4 - ((6235 / 18723) : ℂ) * ζ ^ 5 + ((823 / 37446) : ℂ) * ζ ^ 6 + ((39593 / 37446) : ℂ) * ζ ^ 7 - ((47857 / 37446) : ℂ) * ζ ^ 8 + ((1797 / 12482) : ℂ) * ζ ^ 9 + ((19619 / 18723) : ℂ) * ζ ^ 10 - ((2971 / 37446) : ℂ) * ζ ^ 11 - ((3704 / 6241) : ℂ) * ζ ^ 12 + ((15859 / 18723) : ℂ) * ζ ^ 13 + ((48661 / 37446) : ℂ) * ζ ^ 14 + ((1525 / 6241) : ℂ) * ζ ^ 15 - ((19876 / 18723) : ℂ) * ζ ^ 16 + ((4535 / 37446) : ℂ) * ζ ^ 17 + ((26943 / 12482) : ℂ) * ζ ^ 18 + ((17290 / 18723) : ℂ) * ζ ^ 19 + ((4988 / 18723) : ℂ) * ζ ^ 20 + ((18885 / 12482) : ℂ) * ζ ^ 21 + ((29192 / 18723) : ℂ) * ζ ^ 22 - ((58721 / 37446) : ℂ) * ζ ^ 23 + ((12521 / 18723) : ℂ) * ζ ^ 24 + ((1753 / 18723) : ℂ) * ζ ^ 25 - ((4135 / 18723) : ℂ) * ζ ^ 26 - ((4348 / 18723) : ℂ) * ζ ^ 27 + ((18543 / 12482) : ℂ) * ζ ^ 28 - ((2728 / 6241) : ℂ) * ζ ^ 29 - ((4823 / 37446) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep05Coefficient06 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep05CoefficientIdentity06 :
    row18_reducedY23_combinationStep05Coefficient06 =
      row18_reducedY23_combinationStep04Coefficient06 +
        row18_reducedY23_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep05Coefficient06 row18_reducedY23_combinationStep04Coefficient06 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep05Coefficient07 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep05CoefficientIdentity07 :
    row18_reducedY23_combinationStep05Coefficient07 =
      row18_reducedY23_combinationStep04Coefficient07 +
        row18_reducedY23_combinationStep05Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep05Coefficient07 row18_reducedY23_combinationStep04Coefficient07 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 (-((33157 / 37446) : ℂ) - ((111521 / 37446) : ℂ) * ζ ^ 1 - ((16525 / 12482) : ℂ) * ζ ^ 2 - ((46598 / 18723) : ℂ) * ζ ^ 3 - ((15962 / 6241) : ℂ) * ζ ^ 4 + ((69553 / 18723) : ℂ) * ζ ^ 5 + ((260641 / 37446) : ℂ) * ζ ^ 6 + ((97286 / 18723) : ℂ) * ζ ^ 7 - ((76087 / 37446) : ℂ) * ζ ^ 8 - ((260177 / 37446) : ℂ) * ζ ^ 9 - ((108380 / 18723) : ℂ) * ζ ^ 10 - ((16454 / 18723) : ℂ) * ζ ^ 11 + ((180901 / 37446) : ℂ) * ζ ^ 12 + ((93320 / 18723) : ℂ) * ζ ^ 13 + ((18517 / 18723) : ℂ) * ζ ^ 14 - ((43031 / 18723) : ℂ) * ζ ^ 15 - ((23738 / 6241) : ℂ) * ζ ^ 16 - ((136909 / 37446) : ℂ) * ζ ^ 17 - ((61034 / 18723) : ℂ) * ζ ^ 18 - ((16708 / 18723) : ℂ) * ζ ^ 19 + ((85606 / 18723) : ℂ) * ζ ^ 20 + ((104497 / 37446) : ℂ) * ζ ^ 21 - ((30838 / 18723) : ℂ) * ζ ^ 22 - ((76454 / 18723) : ℂ) * ζ ^ 23 - ((96569 / 37446) : ℂ) * ζ ^ 24 - ((854 / 6241) : ℂ) * ζ ^ 25 + ((52802 / 18723) : ℂ) * ζ ^ 26 + ((21947 / 18723) : ℂ) * ζ ^ 27 + ((4717 / 37446) : ℂ) * ζ ^ 28 - ((168 / 6241) : ℂ) * ζ ^ 29 - ((5194 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep05Coefficient08 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep05CoefficientIdentity08 :
    row18_reducedY23_combinationStep05Coefficient08 =
      row18_reducedY23_combinationStep04Coefficient08 +
        row18_reducedY23_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep05Coefficient08 row18_reducedY23_combinationStep04Coefficient08 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep05Coefficient09 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep05CoefficientIdentity09 :
    row18_reducedY23_combinationStep05Coefficient09 =
      row18_reducedY23_combinationStep04Coefficient09 +
        row18_reducedY23_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep05Coefficient09 row18_reducedY23_combinationStep04Coefficient09 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep05Coefficient10 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep05CoefficientIdentity10 :
    row18_reducedY23_combinationStep05Coefficient10 =
      row18_reducedY23_combinationStep04Coefficient10 +
        row18_reducedY23_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep05Coefficient10 row18_reducedY23_combinationStep04Coefficient10 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep05Coefficient11 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep05CoefficientIdentity11 :
    row18_reducedY23_combinationStep05Coefficient11 =
      row18_reducedY23_combinationStep04Coefficient11 +
        row18_reducedY23_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep05Coefficient11 row18_reducedY23_combinationStep04Coefficient11 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep05Coefficient12 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep05CoefficientIdentity12 :
    row18_reducedY23_combinationStep05Coefficient12 =
      row18_reducedY23_combinationStep04Coefficient12 +
        row18_reducedY23_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep05Coefficient12 row18_reducedY23_combinationStep04Coefficient12 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep05Coefficient13 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep05CoefficientIdentity13 :
    row18_reducedY23_combinationStep05Coefficient13 =
      row18_reducedY23_combinationStep04Coefficient13 +
        row18_reducedY23_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep05Coefficient13 row18_reducedY23_combinationStep04Coefficient13 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep05Coefficient14 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep05CoefficientIdentity14 :
    row18_reducedY23_combinationStep05Coefficient14 =
      row18_reducedY23_combinationStep04Coefficient14 +
        row18_reducedY23_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep05Coefficient14 row18_reducedY23_combinationStep04Coefficient14 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep05Coefficient15 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep05CoefficientIdentity15 :
    row18_reducedY23_combinationStep05Coefficient15 =
      row18_reducedY23_combinationStep04Coefficient15 +
        row18_reducedY23_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep05Coefficient15 row18_reducedY23_combinationStep04Coefficient15 row18_reducedY23_combinationStep05Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY23_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY23_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY23_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY23_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY23_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY23_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY23_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY23_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY23_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY23_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY23_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY23_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY23_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY23_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY23_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY23_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY23_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY23_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY23_combinationStep05CoefficientIdentity00,
      row18_reducedY23_combinationStep05CoefficientIdentity01,
      row18_reducedY23_combinationStep05CoefficientIdentity02,
      row18_reducedY23_combinationStep05CoefficientIdentity03,
      row18_reducedY23_combinationStep05CoefficientIdentity04,
      row18_reducedY23_combinationStep05CoefficientIdentity05,
      row18_reducedY23_combinationStep05CoefficientIdentity06,
      row18_reducedY23_combinationStep05CoefficientIdentity07,
      row18_reducedY23_combinationStep05CoefficientIdentity08,
      row18_reducedY23_combinationStep05CoefficientIdentity09,
      row18_reducedY23_combinationStep05CoefficientIdentity10,
      row18_reducedY23_combinationStep05CoefficientIdentity11,
      row18_reducedY23_combinationStep05CoefficientIdentity12,
      row18_reducedY23_combinationStep05CoefficientIdentity13,
      row18_reducedY23_combinationStep05CoefficientIdentity14,
      row18_reducedY23_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY23_combinationStep05Multiplier * equation

private def row18_reducedY23_combinationStep06Multiplier : ℂ :=
  (((42 / 395) : ℂ) - ((654 / 79) : ℂ) * ζ ^ 1 - ((2836 / 395) : ℂ) * ζ ^ 2 - ((1066 / 395) : ℂ) * ζ ^ 3 - ((4 / 395) : ℂ) * ζ ^ 6 - ((1666 / 395) : ℂ) * ζ ^ 8 - ((288 / 79) : ℂ) * ζ ^ 9 + ((2108 / 395) : ℂ) * ζ ^ 11 + ((2832 / 395) : ℂ) * ζ ^ 12 + ((654 / 79) : ℂ) * ζ ^ 13 - ((1066 / 395) : ℂ) * ζ ^ 15 + ((654 / 79) : ℂ) * ζ ^ 17 + ((2878 / 395) : ℂ) * ζ ^ 18 + ((654 / 79) : ℂ) * ζ ^ 21 + ((2836 / 395) : ℂ) * ζ ^ 22 - ((2836 / 395) : ℂ) * ζ ^ 24 - ((654 / 79) : ℂ) * ζ ^ 25 + ((2108 / 395) : ℂ) * ζ ^ 27 + ((1666 / 395) : ℂ) * ζ ^ 28 - ((654 / 79) : ℂ) * ζ ^ 29 - ((4502 / 395) : ℂ) * ζ ^ 30 - ((2108 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY23_combinationStep06Coefficient00 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity00 :
    row18_reducedY23_combinationStep06Coefficient00 =
      row18_reducedY23_combinationStep05Coefficient00 +
        row18_reducedY23_combinationStep06Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep06Coefficient00 row18_reducedY23_combinationStep05Coefficient00 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 (((41759 / 31205) : ℂ) + ((86009 / 62410) : ℂ) * ζ ^ 1 + ((164531 / 62410) : ℂ) * ζ ^ 2 + ((50187 / 12482) : ℂ) * ζ ^ 3 + ((4451 / 6241) : ℂ) * ζ ^ 4 - ((19958 / 31205) : ℂ) * ζ ^ 5 - ((157751 / 62410) : ℂ) * ζ ^ 6 - ((156053 / 62410) : ℂ) * ζ ^ 7 + ((52747 / 62410) : ℂ) * ζ ^ 8 + ((21572 / 6241) : ℂ) * ζ ^ 9 + ((264851 / 62410) : ℂ) * ζ ^ 10 + ((51941 / 31205) : ℂ) * ζ ^ 11 - ((509 / 158) : ℂ) * ζ ^ 12 - ((258523 / 62410) : ℂ) * ζ ^ 13 - ((16721 / 6241) : ℂ) * ζ ^ 14 + ((64369 / 31205) : ℂ) * ζ ^ 15 + ((354413 / 62410) : ℂ) * ζ ^ 16 + ((227571 / 62410) : ℂ) * ζ ^ 17 - ((21431 / 62410) : ℂ) * ζ ^ 18 - ((218497 / 62410) : ℂ) * ζ ^ 19 - ((22909 / 6241) : ℂ) * ζ ^ 20 - ((15312 / 31205) : ℂ) * ζ ^ 21 + ((43976 / 31205) : ℂ) * ζ ^ 22 + ((13884 / 31205) : ℂ) * ζ ^ 23 - ((6091 / 12482) : ℂ) * ζ ^ 24 - ((52309 / 31205) : ℂ) * ζ ^ 25 - ((45496 / 31205) : ℂ) * ζ ^ 26 + ((2369 / 62410) : ℂ) * ζ ^ 27 + ((7050 / 6241) : ℂ) * ζ ^ 28 + ((24189 / 31205) : ℂ) * ζ ^ 29 + ((7378 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep06Coefficient01 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity01 :
    row18_reducedY23_combinationStep06Coefficient01 =
      row18_reducedY23_combinationStep05Coefficient01 +
        row18_reducedY23_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep06Coefficient01 row18_reducedY23_combinationStep05Coefficient01 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep06Coefficient02 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity02 :
    row18_reducedY23_combinationStep06Coefficient02 =
      row18_reducedY23_combinationStep05Coefficient02 +
        row18_reducedY23_combinationStep06Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep06Coefficient02 row18_reducedY23_combinationStep05Coefficient02 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 (-((399 / 31205) : ℂ) + ((74583 / 62410) : ℂ) * ζ ^ 1 + ((49934 / 31205) : ℂ) * ζ ^ 2 + ((34403 / 31205) : ℂ) * ζ ^ 3 + ((82291 / 31205) : ℂ) * ζ ^ 4 + ((26624 / 31205) : ℂ) * ζ ^ 5 + ((4609 / 12482) : ℂ) * ζ ^ 6 - ((28127 / 31205) : ℂ) * ζ ^ 7 - ((179619 / 62410) : ℂ) * ζ ^ 8 - ((138763 / 62410) : ℂ) * ζ ^ 9 - ((22463 / 12482) : ℂ) * ζ ^ 10 + ((2211 / 6241) : ℂ) * ζ ^ 11 + ((23661 / 62410) : ℂ) * ζ ^ 12 + ((5361 / 6241) : ℂ) * ζ ^ 13 - ((8047 / 62410) : ℂ) * ζ ^ 14 - ((150481 / 62410) : ℂ) * ζ ^ 15 - ((138403 / 31205) : ℂ) * ζ ^ 16 - ((115523 / 31205) : ℂ) * ζ ^ 17 - ((82769 / 62410) : ℂ) * ζ ^ 18 + ((36588 / 31205) : ℂ) * ζ ^ 19 + ((142749 / 62410) : ℂ) * ζ ^ 20 + ((106937 / 62410) : ℂ) * ζ ^ 21 - ((2943 / 12482) : ℂ) * ζ ^ 22 - ((50857 / 31205) : ℂ) * ζ ^ 23 - ((111553 / 62410) : ℂ) * ζ ^ 24 - ((18603 / 31205) : ℂ) * ζ ^ 25 + ((34027 / 31205) : ℂ) * ζ ^ 26 + ((158483 / 62410) : ℂ) * ζ ^ 27 + ((143247 / 31205) : ℂ) * ζ ^ 28 + ((119838 / 31205) : ℂ) * ζ ^ 29 + ((44268 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep06Coefficient03 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity03 :
    row18_reducedY23_combinationStep06Coefficient03 =
      row18_reducedY23_combinationStep05Coefficient03 +
        row18_reducedY23_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep06Coefficient03 row18_reducedY23_combinationStep05Coefficient03 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep06Coefficient04 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity04 :
    row18_reducedY23_combinationStep06Coefficient04 =
      row18_reducedY23_combinationStep05Coefficient04 +
        row18_reducedY23_combinationStep06Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep06Coefficient04 row18_reducedY23_combinationStep05Coefficient04 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 (-((41759 / 31205) : ℂ) - ((86009 / 62410) : ℂ) * ζ ^ 1 - ((164531 / 62410) : ℂ) * ζ ^ 2 - ((50187 / 12482) : ℂ) * ζ ^ 3 - ((4451 / 6241) : ℂ) * ζ ^ 4 + ((19958 / 31205) : ℂ) * ζ ^ 5 + ((157751 / 62410) : ℂ) * ζ ^ 6 + ((156053 / 62410) : ℂ) * ζ ^ 7 - ((52747 / 62410) : ℂ) * ζ ^ 8 - ((21572 / 6241) : ℂ) * ζ ^ 9 - ((264851 / 62410) : ℂ) * ζ ^ 10 - ((51941 / 31205) : ℂ) * ζ ^ 11 + ((509 / 158) : ℂ) * ζ ^ 12 + ((258523 / 62410) : ℂ) * ζ ^ 13 + ((16721 / 6241) : ℂ) * ζ ^ 14 - ((64369 / 31205) : ℂ) * ζ ^ 15 - ((354413 / 62410) : ℂ) * ζ ^ 16 - ((227571 / 62410) : ℂ) * ζ ^ 17 + ((21431 / 62410) : ℂ) * ζ ^ 18 + ((218497 / 62410) : ℂ) * ζ ^ 19 + ((22909 / 6241) : ℂ) * ζ ^ 20 + ((15312 / 31205) : ℂ) * ζ ^ 21 - ((43976 / 31205) : ℂ) * ζ ^ 22 - ((13884 / 31205) : ℂ) * ζ ^ 23 + ((6091 / 12482) : ℂ) * ζ ^ 24 + ((52309 / 31205) : ℂ) * ζ ^ 25 + ((45496 / 31205) : ℂ) * ζ ^ 26 - ((2369 / 62410) : ℂ) * ζ ^ 27 - ((7050 / 6241) : ℂ) * ζ ^ 28 - ((24189 / 31205) : ℂ) * ζ ^ 29 - ((7378 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep06Coefficient05 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY23_combinationStep06CoefficientIdentity05 :
    row18_reducedY23_combinationStep06Coefficient05 =
      row18_reducedY23_combinationStep05Coefficient05 +
        row18_reducedY23_combinationStep06Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY23_combinationStep06Coefficient05 row18_reducedY23_combinationStep05Coefficient05 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 (((55959 / 62410) : ℂ) - ((53943 / 62410) : ℂ) * ζ ^ 1 - ((51878 / 31205) : ℂ) * ζ ^ 2 - ((68033 / 62410) : ℂ) * ζ ^ 3 - ((33603 / 62410) : ℂ) * ζ ^ 4 + ((129277 / 62410) : ℂ) * ζ ^ 5 + ((13560 / 6241) : ℂ) * ζ ^ 6 + ((206943 / 62410) : ℂ) * ζ ^ 7 + ((8399 / 62410) : ℂ) * ζ ^ 8 - ((17066 / 31205) : ℂ) * ζ ^ 9 + ((8541 / 62410) : ℂ) * ζ ^ 10 - ((38633 / 62410) : ℂ) * ζ ^ 11 - ((245067 / 62410) : ℂ) * ζ ^ 12 - ((105089 / 31205) : ℂ) * ζ ^ 13 - ((174919 / 62410) : ℂ) * ζ ^ 14 + ((47287 / 62410) : ℂ) * ζ ^ 15 + ((18499 / 6241) : ℂ) * ζ ^ 16 + ((96323 / 31205) : ℂ) * ζ ^ 17 + ((27613 / 62410) : ℂ) * ζ ^ 18 - ((267201 / 62410) : ℂ) * ζ ^ 19 - ((171433 / 31205) : ℂ) * ζ ^ 20 - ((49713 / 31205) : ℂ) * ζ ^ 21 + ((245873 / 62410) : ℂ) * ζ ^ 22 + ((71073 / 12482) : ℂ) * ζ ^ 23 + ((54991 / 62410) : ℂ) * ζ ^ 24 - ((470201 / 62410) : ℂ) * ζ ^ 25 - ((48098 / 6241) : ℂ) * ζ ^ 26 - ((51672 / 31205) : ℂ) * ζ ^ 27 + ((217413 / 31205) : ℂ) * ζ ^ 28 + ((231048 / 31205) : ℂ) * ζ ^ 29 + ((18972 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY23_combinationStep06Coefficient06 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity06 :
    row18_reducedY23_combinationStep06Coefficient06 =
      row18_reducedY23_combinationStep05Coefficient06 +
        row18_reducedY23_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep06Coefficient06 row18_reducedY23_combinationStep05Coefficient06 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep06Coefficient07 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity07 :
    row18_reducedY23_combinationStep06Coefficient07 =
      row18_reducedY23_combinationStep05Coefficient07 +
        row18_reducedY23_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep06Coefficient07 row18_reducedY23_combinationStep05Coefficient07 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep06Coefficient08 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity08 :
    row18_reducedY23_combinationStep06Coefficient08 =
      row18_reducedY23_combinationStep05Coefficient08 +
        row18_reducedY23_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep06Coefficient08 row18_reducedY23_combinationStep05Coefficient08 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep06Coefficient09 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity09 :
    row18_reducedY23_combinationStep06Coefficient09 =
      row18_reducedY23_combinationStep05Coefficient09 +
        row18_reducedY23_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep06Coefficient09 row18_reducedY23_combinationStep05Coefficient09 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep06Coefficient10 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity10 :
    row18_reducedY23_combinationStep06Coefficient10 =
      row18_reducedY23_combinationStep05Coefficient10 +
        row18_reducedY23_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep06Coefficient10 row18_reducedY23_combinationStep05Coefficient10 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep06Coefficient11 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity11 :
    row18_reducedY23_combinationStep06Coefficient11 =
      row18_reducedY23_combinationStep05Coefficient11 +
        row18_reducedY23_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep06Coefficient11 row18_reducedY23_combinationStep05Coefficient11 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep06Coefficient12 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity12 :
    row18_reducedY23_combinationStep06Coefficient12 =
      row18_reducedY23_combinationStep05Coefficient12 +
        row18_reducedY23_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep06Coefficient12 row18_reducedY23_combinationStep05Coefficient12 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep06Coefficient13 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity13 :
    row18_reducedY23_combinationStep06Coefficient13 =
      row18_reducedY23_combinationStep05Coefficient13 +
        row18_reducedY23_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep06Coefficient13 row18_reducedY23_combinationStep05Coefficient13 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep06Coefficient14 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity14 :
    row18_reducedY23_combinationStep06Coefficient14 =
      row18_reducedY23_combinationStep05Coefficient14 +
        row18_reducedY23_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep06Coefficient14 row18_reducedY23_combinationStep05Coefficient14 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY23_combinationStep06Coefficient15 : ℂ :=
  0

private theorem row18_reducedY23_combinationStep06CoefficientIdentity15 :
    row18_reducedY23_combinationStep06Coefficient15 =
      row18_reducedY23_combinationStep05Coefficient15 +
        row18_reducedY23_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY23_combinationStep06Coefficient15 row18_reducedY23_combinationStep05Coefficient15 row18_reducedY23_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY23_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY23_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY23_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY23_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY23_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY23_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY23_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY23_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY23_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY23_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY23_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY23_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY23_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY23_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY23_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY23_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY23_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY23_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY23_combinationStep06CoefficientIdentity00,
      row18_reducedY23_combinationStep06CoefficientIdentity01,
      row18_reducedY23_combinationStep06CoefficientIdentity02,
      row18_reducedY23_combinationStep06CoefficientIdentity03,
      row18_reducedY23_combinationStep06CoefficientIdentity04,
      row18_reducedY23_combinationStep06CoefficientIdentity05,
      row18_reducedY23_combinationStep06CoefficientIdentity06,
      row18_reducedY23_combinationStep06CoefficientIdentity07,
      row18_reducedY23_combinationStep06CoefficientIdentity08,
      row18_reducedY23_combinationStep06CoefficientIdentity09,
      row18_reducedY23_combinationStep06CoefficientIdentity10,
      row18_reducedY23_combinationStep06CoefficientIdentity11,
      row18_reducedY23_combinationStep06CoefficientIdentity12,
      row18_reducedY23_combinationStep06CoefficientIdentity13,
      row18_reducedY23_combinationStep06CoefficientIdentity14,
      row18_reducedY23_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY23_combinationStep06Multiplier * equation

theorem row18_reducedY23
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 2 3 = 0 := by
  have reduced :=
    row18_reducedY23_combinationStep06 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY23_combinationStep06Coefficient00,
      row18_reducedY23_combinationStep06Coefficient01,
      row18_reducedY23_combinationStep06Coefficient02,
      row18_reducedY23_combinationStep06Coefficient03,
      row18_reducedY23_combinationStep06Coefficient04,
      row18_reducedY23_combinationStep06Coefficient05,
      row18_reducedY23_combinationStep06Coefficient06,
      row18_reducedY23_combinationStep06Coefficient07,
      row18_reducedY23_combinationStep06Coefficient08,
      row18_reducedY23_combinationStep06Coefficient09,
      row18_reducedY23_combinationStep06Coefficient10,
      row18_reducedY23_combinationStep06Coefficient11,
      row18_reducedY23_combinationStep06Coefficient12,
      row18_reducedY23_combinationStep06Coefficient13,
      row18_reducedY23_combinationStep06Coefficient14,
      row18_reducedY23_combinationStep06Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
