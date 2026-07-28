/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction11

/-!
# Ambient row 18 commutant reduction 12

This generated module checks the reduced relation `reducedY66` for
matrix coordinate (6, 6).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY66_combinationStep00Multiplier : ℂ :=
  (-((34416 / 395) : ℂ) + ((28558 / 395) : ℂ) * ζ ^ 1 + ((25850 / 237) : ℂ) * ζ ^ 2 - ((103594 / 1185) : ℂ) * ζ ^ 3 + ((54444 / 395) : ℂ) * ζ ^ 5 + ((54618 / 395) : ℂ) * ζ ^ 8 - ((24578 / 1185) : ℂ) * ζ ^ 9 + ((42724 / 395) : ℂ) * ζ ^ 11 + ((14214 / 395) : ℂ) * ζ ^ 12 - ((28558 / 395) : ℂ) * ζ ^ 13 + ((25936 / 1185) : ℂ) * ζ ^ 15 - ((28558 / 395) : ℂ) * ζ ^ 17 - ((25850 / 237) : ℂ) * ζ ^ 18 - ((189268 / 1185) : ℂ) * ζ ^ 21 - ((25850 / 237) : ℂ) * ζ ^ 22 - ((68832 / 395) : ℂ) * ζ ^ 24 - ((25886 / 395) : ℂ) * ζ ^ 25 - ((189268 / 1185) : ℂ) * ζ ^ 27 - ((54618 / 395) : ℂ) * ζ ^ 28 + ((28558 / 395) : ℂ) * ζ ^ 29 - ((5036 / 79) : ℂ) * ζ ^ 30 - ((42724 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY66_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep00CoefficientIdentity00 :
    row18_reducedY66_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep00Coefficient00 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep00Coefficient01 : ℂ :=
  (((1069 / 474) : ℂ) - ((1084 / 237) : ℂ) * ζ ^ 1 + ((317 / 158) : ℂ) * ζ ^ 2 + ((1988 / 237) : ℂ) * ζ ^ 3 - ((1084 / 237) : ℂ) * ζ ^ 5 + ((1010 / 237) : ℂ) * ζ ^ 6 - ((1010 / 237) : ℂ) * ζ ^ 8 + ((1084 / 237) : ℂ) * ζ ^ 9 - ((994 / 237) : ℂ) * ζ ^ 11 + ((391 / 237) : ℂ) * ζ ^ 12 + ((1084 / 237) : ℂ) * ζ ^ 13 + ((73 / 158) : ℂ) * ζ ^ 15 + ((1084 / 237) : ℂ) * ζ ^ 17 + ((335 / 237) : ℂ) * ζ ^ 18 + ((23 / 474) : ℂ) * ζ ^ 21 - ((317 / 158) : ℂ) * ζ ^ 22 + ((1345 / 237) : ℂ) * ζ ^ 24 + ((4195 / 474) : ℂ) * ζ ^ 27 + ((1010 / 237) : ℂ) * ζ ^ 28 - ((1084 / 237) : ℂ) * ζ ^ 29 + ((467 / 79) : ℂ) * ζ ^ 30 + ((994 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep00CoefficientIdentity01 :
    row18_reducedY66_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep00Coefficient01 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 (-((4758671 / 187230) : ℂ) + ((1995026 / 93615) : ℂ) * ζ ^ 1 + ((527822 / 31205) : ℂ) * ζ ^ 2 - ((691003 / 37446) : ℂ) * ζ ^ 3 + ((1189333 / 31205) : ℂ) * ζ ^ 4 + ((2659492 / 93615) : ℂ) * ζ ^ 5 - ((4377653 / 187230) : ℂ) * ζ ^ 6 + ((243982 / 93615) : ℂ) * ζ ^ 7 + ((260567 / 12482) : ℂ) * ζ ^ 8 - ((2240077 / 187230) : ℂ) * ζ ^ 9 - ((270059 / 12482) : ℂ) * ζ ^ 10 - ((4412263 / 187230) : ℂ) * ζ ^ 11 + ((1216057 / 62410) : ℂ) * ζ ^ 12 - ((1317497 / 93615) : ℂ) * ζ ^ 13 - ((2982517 / 62410) : ℂ) * ζ ^ 14 - ((467863 / 187230) : ℂ) * ζ ^ 15 + ((37411 / 187230) : ℂ) * ζ ^ 16 - ((925516 / 93615) : ℂ) * ζ ^ 17 + ((143919 / 31205) : ℂ) * ζ ^ 18 - ((1640093 / 187230) : ℂ) * ζ ^ 19 - ((2053408 / 93615) : ℂ) * ζ ^ 20 - ((38047 / 93615) : ℂ) * ζ ^ 21 + ((1814401 / 187230) : ℂ) * ζ ^ 22 - ((1182223 / 93615) : ℂ) * ζ ^ 23 - ((187259 / 6241) : ℂ) * ζ ^ 24 + ((151167 / 62410) : ℂ) * ζ ^ 25 + ((1805252 / 93615) : ℂ) * ζ ^ 26 + ((254951 / 12482) : ℂ) * ζ ^ 27 - ((150316 / 6241) : ℂ) * ζ ^ 28 + ((139673 / 31205) : ℂ) * ζ ^ 29 + ((726308 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep00Coefficient02 : ℂ :=
  (((188 / 79) : ℂ) - ((674 / 237) : ℂ) * ζ ^ 1 - ((193 / 474) : ℂ) * ζ ^ 2 + ((1621 / 474) : ℂ) * ζ ^ 3 - ((3473 / 237) : ℂ) * ζ ^ 5 + ((460 / 237) : ℂ) * ζ ^ 6 - ((985 / 237) : ℂ) * ζ ^ 8 - ((2125 / 474) : ℂ) * ζ ^ 9 - ((1173 / 79) : ℂ) * ζ ^ 11 - ((371 / 158) : ℂ) * ζ ^ 12 + ((674 / 237) : ℂ) * ζ ^ 13 - ((1621 / 474) : ℂ) * ζ ^ 15 + ((674 / 237) : ℂ) * ζ ^ 17 - ((935 / 474) : ℂ) * ζ ^ 18 + ((933 / 79) : ℂ) * ζ ^ 21 + ((193 / 474) : ℂ) * ζ ^ 22 + ((193 / 474) : ℂ) * ζ ^ 24 + ((933 / 79) : ℂ) * ζ ^ 25 + ((1173 / 79) : ℂ) * ζ ^ 27 + ((985 / 237) : ℂ) * ζ ^ 28 - ((674 / 237) : ℂ) * ζ ^ 29 + ((1777 / 474) : ℂ) * ζ ^ 30 + ((1173 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep00CoefficientIdentity02 :
    row18_reducedY66_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep00Coefficient02 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 (-((779788 / 31205) : ℂ) + ((1686991 / 93615) : ℂ) * ζ ^ 1 + ((417715 / 18723) : ℂ) * ζ ^ 2 - ((135209 / 18723) : ℂ) * ζ ^ 3 + ((1724843 / 62410) : ℂ) * ζ ^ 4 + ((1377101 / 93615) : ℂ) * ζ ^ 5 - ((1401814 / 93615) : ℂ) * ζ ^ 6 + ((4599941 / 187230) : ℂ) * ζ ^ 7 + ((422159 / 18723) : ℂ) * ζ ^ 8 - ((610061 / 93615) : ℂ) * ζ ^ 9 - ((841337 / 93615) : ℂ) * ζ ^ 10 - ((44762 / 18723) : ℂ) * ζ ^ 11 + ((39289 / 93615) : ℂ) * ζ ^ 12 - ((1321283 / 187230) : ℂ) * ζ ^ 13 - ((694501 / 37446) : ℂ) * ζ ^ 14 + ((143021 / 93615) : ℂ) * ζ ^ 15 - ((2513389 / 187230) : ℂ) * ζ ^ 16 - ((586824 / 31205) : ℂ) * ζ ^ 17 - ((2661457 / 187230) : ℂ) * ζ ^ 18 - ((1270271 / 187230) : ℂ) * ζ ^ 19 - ((39101 / 31205) : ℂ) * ζ ^ 20 - ((470263 / 62410) : ℂ) * ζ ^ 21 + ((5808 / 6241) : ℂ) * ζ ^ 22 - ((274646 / 18723) : ℂ) * ζ ^ 23 - ((2690017 / 93615) : ℂ) * ζ ^ 24 + ((206617 / 31205) : ℂ) * ζ ^ 25 - ((1271 / 6241) : ℂ) * ζ ^ 26 - ((144265 / 6241) : ℂ) * ζ ^ 27 - ((151961 / 62410) : ℂ) * ζ ^ 28 + ((382812 / 31205) : ℂ) * ζ ^ 29 + ((32043 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep00CoefficientIdentity03 :
    row18_reducedY66_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep00Coefficient03 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep00CoefficientIdentity04 :
    row18_reducedY66_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep00Coefficient04 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep00CoefficientIdentity05 :
    row18_reducedY66_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep00Coefficient05 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep00CoefficientIdentity06 :
    row18_reducedY66_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep00Coefficient06 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep00CoefficientIdentity07 :
    row18_reducedY66_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep00Coefficient07 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep00CoefficientIdentity08 :
    row18_reducedY66_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep00Coefficient08 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep00CoefficientIdentity09 :
    row18_reducedY66_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep00Coefficient09 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep00CoefficientIdentity10 :
    row18_reducedY66_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep00Coefficient10 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep00CoefficientIdentity11 :
    row18_reducedY66_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep00Coefficient11 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep00CoefficientIdentity12 :
    row18_reducedY66_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep00Coefficient12 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep00CoefficientIdentity13 :
    row18_reducedY66_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep00Coefficient13 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep00CoefficientIdentity14 :
    row18_reducedY66_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep00Coefficient14 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep00CoefficientIdentity15 :
    row18_reducedY66_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY66_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep00Coefficient15 row18_reducedY66_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY66_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY66_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY66_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY66_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY66_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY66_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY66_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY66_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY66_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY66_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY66_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY66_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY66_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY66_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY66_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY66_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY66_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY66_combinationStep00CoefficientIdentity00,
      row18_reducedY66_combinationStep00CoefficientIdentity01,
      row18_reducedY66_combinationStep00CoefficientIdentity02,
      row18_reducedY66_combinationStep00CoefficientIdentity03,
      row18_reducedY66_combinationStep00CoefficientIdentity04,
      row18_reducedY66_combinationStep00CoefficientIdentity05,
      row18_reducedY66_combinationStep00CoefficientIdentity06,
      row18_reducedY66_combinationStep00CoefficientIdentity07,
      row18_reducedY66_combinationStep00CoefficientIdentity08,
      row18_reducedY66_combinationStep00CoefficientIdentity09,
      row18_reducedY66_combinationStep00CoefficientIdentity10,
      row18_reducedY66_combinationStep00CoefficientIdentity11,
      row18_reducedY66_combinationStep00CoefficientIdentity12,
      row18_reducedY66_combinationStep00CoefficientIdentity13,
      row18_reducedY66_combinationStep00CoefficientIdentity14,
      row18_reducedY66_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY66_combinationStep00Multiplier * equation

private def row18_reducedY66_combinationStep01Multiplier : ℂ :=
  (-((326 / 79) : ℂ) - ((314 / 395) : ℂ) * ζ ^ 1 + ((1600 / 237) : ℂ) * ζ ^ 2 + ((5954 / 1185) : ℂ) * ζ ^ 5 + ((2578 / 237) : ℂ) * ζ ^ 6 + ((2578 / 237) : ℂ) * ζ ^ 8 + ((5954 / 1185) : ℂ) * ζ ^ 9 + ((1268 / 79) : ℂ) * ζ ^ 11 + ((1036 / 79) : ℂ) * ζ ^ 12 + ((314 / 395) : ℂ) * ζ ^ 13 + ((1612 / 237) : ℂ) * ζ ^ 15 + ((314 / 395) : ℂ) * ζ ^ 17 - ((466 / 237) : ℂ) * ζ ^ 18 - ((2506 / 1185) : ℂ) * ζ ^ 21 - ((1600 / 237) : ℂ) * ζ ^ 22 - ((704 / 79) : ℂ) * ζ ^ 24 - ((6896 / 1185) : ℂ) * ζ ^ 25 - ((1612 / 237) : ℂ) * ζ ^ 27 - ((2578 / 237) : ℂ) * ζ ^ 28 - ((314 / 395) : ℂ) * ζ ^ 29 - ((530 / 237) : ℂ) * ζ ^ 30 - ((1268 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY66_combinationStep01Coefficient00 : ℂ :=
  (((245 / 79) : ℂ) + ((61 / 237) : ℂ) * ζ ^ 1 - ((113 / 474) : ℂ) * ζ ^ 2 - ((1231 / 474) : ℂ) * ζ ^ 3 + ((179 / 237) : ℂ) * ζ ^ 5 + ((41 / 237) : ℂ) * ζ ^ 6 - ((76 / 79) : ℂ) * ζ ^ 8 - ((194 / 237) : ℂ) * ζ ^ 9 + ((281 / 158) : ℂ) * ζ ^ 11 - ((76 / 79) : ℂ) * ζ ^ 12 - ((61 / 237) : ℂ) * ζ ^ 13 + ((489 / 158) : ℂ) * ζ ^ 15 - ((61 / 237) : ℂ) * ζ ^ 17 - ((65 / 158) : ℂ) * ζ ^ 18 + ((1109 / 474) : ℂ) * ζ ^ 21 + ((113 / 474) : ℂ) * ζ ^ 22 - ((118 / 237) : ℂ) * ζ ^ 25 - ((1109 / 474) : ℂ) * ζ ^ 27 + ((76 / 79) : ℂ) * ζ ^ 28 + ((61 / 237) : ℂ) * ζ ^ 29 + ((41 / 474) : ℂ) * ζ ^ 30 - ((281 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep01CoefficientIdentity00 :
    row18_reducedY66_combinationStep01Coefficient00 =
      row18_reducedY66_combinationStep00Coefficient00 +
        row18_reducedY66_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep01Coefficient00 row18_reducedY66_combinationStep00Coefficient00 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 (-((12672 / 6241) : ℂ) + ((22217 / 187230) : ℂ) * ζ ^ 1 - ((32352 / 31205) : ℂ) * ζ ^ 2 + ((391579 / 187230) : ℂ) * ζ ^ 3 + ((116428 / 93615) : ℂ) * ζ ^ 4 - ((311741 / 187230) : ℂ) * ζ ^ 5 - ((189287 / 93615) : ℂ) * ζ ^ 6 - ((190467 / 62410) : ℂ) * ζ ^ 7 - ((307351 / 62410) : ℂ) * ζ ^ 8 + ((82121 / 187230) : ℂ) * ζ ^ 9 + ((109963 / 62410) : ℂ) * ζ ^ 10 - ((94007 / 93615) : ℂ) * ζ ^ 11 - ((7 / 15) : ℂ) * ζ ^ 12 - ((395707 / 187230) : ℂ) * ζ ^ 13 + ((20787 / 62410) : ℂ) * ζ ^ 14 + ((277637 / 187230) : ℂ) * ζ ^ 15 + ((23617 / 18723) : ℂ) * ζ ^ 16 + ((189553 / 62410) : ℂ) * ζ ^ 17 + ((30553 / 93615) : ℂ) * ζ ^ 18 + ((178319 / 187230) : ℂ) * ζ ^ 19 - ((18775 / 37446) : ℂ) * ζ ^ 20 - ((304799 / 187230) : ℂ) * ζ ^ 21 - ((61948 / 93615) : ℂ) * ζ ^ 22 + ((289 / 2370) : ℂ) * ζ ^ 23 + ((44372 / 18723) : ℂ) * ζ ^ 24 + ((150113 / 93615) : ℂ) * ζ ^ 25 + ((137783 / 187230) : ℂ) * ζ ^ 26 + ((487943 / 187230) : ℂ) * ζ ^ 27 + ((2693 / 6241) : ℂ) * ζ ^ 28 - ((18443 / 12482) : ℂ) * ζ ^ 29 - ((4755 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep01Coefficient01 : ℂ :=
  (((349 / 79) : ℂ) - ((1511 / 158) : ℂ) * ζ ^ 1 - ((76 / 79) : ℂ) * ζ ^ 2 + ((2116 / 237) : ℂ) * ζ ^ 3 - ((1511 / 158) : ℂ) * ζ ^ 5 + ((273 / 79) : ℂ) * ζ ^ 6 - ((273 / 79) : ℂ) * ζ ^ 8 + ((1511 / 158) : ℂ) * ζ ^ 9 - ((1058 / 237) : ℂ) * ζ ^ 11 + ((1927 / 474) : ℂ) * ζ ^ 12 + ((1511 / 158) : ℂ) * ζ ^ 13 + ((455 / 474) : ℂ) * ζ ^ 15 + ((1511 / 158) : ℂ) * ζ ^ 17 + ((3481 / 474) : ℂ) * ζ ^ 18 + ((5087 / 474) : ℂ) * ζ ^ 21 + ((76 / 79) : ℂ) * ζ ^ 22 + ((5119 / 474) : ℂ) * ζ ^ 24 + ((4687 / 474) : ℂ) * ζ ^ 27 + ((273 / 79) : ℂ) * ζ ^ 28 - ((1511 / 158) : ℂ) * ζ ^ 29 + ((3565 / 474) : ℂ) * ζ ^ 30 + ((1058 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep01CoefficientIdentity01 :
    row18_reducedY66_combinationStep01Coefficient01 =
      row18_reducedY66_combinationStep00Coefficient01 +
        row18_reducedY66_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep01Coefficient01 row18_reducedY66_combinationStep00Coefficient01 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 (-((65327 / 37446) : ℂ) + ((1003037 / 187230) : ℂ) * ζ ^ 1 + ((423221 / 93615) : ℂ) * ζ ^ 2 + ((12152 / 31205) : ℂ) * ζ ^ 3 - ((30604 / 18723) : ℂ) * ζ ^ 4 - ((278518 / 93615) : ℂ) * ζ ^ 5 - ((492592 / 93615) : ℂ) * ζ ^ 6 - ((559861 / 187230) : ℂ) * ζ ^ 7 - ((138002 / 18723) : ℂ) * ζ ^ 8 - ((90337 / 12482) : ℂ) * ζ ^ 9 - ((22006 / 93615) : ℂ) * ζ ^ 10 + ((16979 / 62410) : ℂ) * ζ ^ 11 - ((64659 / 62410) : ℂ) * ζ ^ 12 - ((259913 / 187230) : ℂ) * ζ ^ 13 - ((436013 / 187230) : ℂ) * ζ ^ 14 - ((73226 / 93615) : ℂ) * ζ ^ 15 - ((107192 / 93615) : ℂ) * ζ ^ 16 + ((5903 / 18723) : ℂ) * ζ ^ 17 - ((26064 / 6241) : ℂ) * ζ ^ 18 - ((308731 / 187230) : ℂ) * ζ ^ 19 + ((91878 / 31205) : ℂ) * ζ ^ 20 - ((1512077 / 187230) : ℂ) * ζ ^ 21 - ((42211 / 31205) : ℂ) * ζ ^ 22 + ((895987 / 187230) : ℂ) * ζ ^ 23 + ((166929 / 62410) : ℂ) * ζ ^ 24 + ((386287 / 187230) : ℂ) * ζ ^ 25 + ((264526 / 93615) : ℂ) * ζ ^ 26 - ((24247 / 93615) : ℂ) * ζ ^ 27 + ((27372 / 31205) : ℂ) * ζ ^ 28 - ((26534 / 18723) : ℂ) * ζ ^ 29 - ((8876 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep01Coefficient02 : ℂ :=
  (((188 / 79) : ℂ) - ((674 / 237) : ℂ) * ζ ^ 1 - ((193 / 474) : ℂ) * ζ ^ 2 + ((1621 / 474) : ℂ) * ζ ^ 3 - ((3473 / 237) : ℂ) * ζ ^ 5 + ((460 / 237) : ℂ) * ζ ^ 6 - ((985 / 237) : ℂ) * ζ ^ 8 - ((2125 / 474) : ℂ) * ζ ^ 9 - ((1173 / 79) : ℂ) * ζ ^ 11 - ((371 / 158) : ℂ) * ζ ^ 12 + ((674 / 237) : ℂ) * ζ ^ 13 - ((1621 / 474) : ℂ) * ζ ^ 15 + ((674 / 237) : ℂ) * ζ ^ 17 - ((935 / 474) : ℂ) * ζ ^ 18 + ((933 / 79) : ℂ) * ζ ^ 21 + ((193 / 474) : ℂ) * ζ ^ 22 + ((193 / 474) : ℂ) * ζ ^ 24 + ((933 / 79) : ℂ) * ζ ^ 25 + ((1173 / 79) : ℂ) * ζ ^ 27 + ((985 / 237) : ℂ) * ζ ^ 28 - ((674 / 237) : ℂ) * ζ ^ 29 + ((1777 / 474) : ℂ) * ζ ^ 30 + ((1173 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep01CoefficientIdentity02 :
    row18_reducedY66_combinationStep01Coefficient02 =
      row18_reducedY66_combinationStep00Coefficient02 +
        row18_reducedY66_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep01Coefficient02 row18_reducedY66_combinationStep00Coefficient02 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep01Coefficient03 : ℂ :=
  (-((245 / 79) : ℂ) - ((61 / 237) : ℂ) * ζ ^ 1 + ((113 / 474) : ℂ) * ζ ^ 2 + ((1231 / 474) : ℂ) * ζ ^ 3 - ((179 / 237) : ℂ) * ζ ^ 5 - ((41 / 237) : ℂ) * ζ ^ 6 + ((76 / 79) : ℂ) * ζ ^ 8 + ((194 / 237) : ℂ) * ζ ^ 9 - ((281 / 158) : ℂ) * ζ ^ 11 + ((76 / 79) : ℂ) * ζ ^ 12 + ((61 / 237) : ℂ) * ζ ^ 13 - ((489 / 158) : ℂ) * ζ ^ 15 + ((61 / 237) : ℂ) * ζ ^ 17 + ((65 / 158) : ℂ) * ζ ^ 18 - ((1109 / 474) : ℂ) * ζ ^ 21 - ((113 / 474) : ℂ) * ζ ^ 22 + ((118 / 237) : ℂ) * ζ ^ 25 + ((1109 / 474) : ℂ) * ζ ^ 27 - ((76 / 79) : ℂ) * ζ ^ 28 - ((61 / 237) : ℂ) * ζ ^ 29 - ((41 / 474) : ℂ) * ζ ^ 30 + ((281 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep01CoefficientIdentity03 :
    row18_reducedY66_combinationStep01Coefficient03 =
      row18_reducedY66_combinationStep00Coefficient03 +
        row18_reducedY66_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep01Coefficient03 row18_reducedY66_combinationStep00Coefficient03 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 (((12672 / 6241) : ℂ) - ((22217 / 187230) : ℂ) * ζ ^ 1 + ((32352 / 31205) : ℂ) * ζ ^ 2 - ((391579 / 187230) : ℂ) * ζ ^ 3 - ((116428 / 93615) : ℂ) * ζ ^ 4 + ((311741 / 187230) : ℂ) * ζ ^ 5 + ((189287 / 93615) : ℂ) * ζ ^ 6 + ((190467 / 62410) : ℂ) * ζ ^ 7 + ((307351 / 62410) : ℂ) * ζ ^ 8 - ((82121 / 187230) : ℂ) * ζ ^ 9 - ((109963 / 62410) : ℂ) * ζ ^ 10 + ((94007 / 93615) : ℂ) * ζ ^ 11 + ((7 / 15) : ℂ) * ζ ^ 12 + ((395707 / 187230) : ℂ) * ζ ^ 13 - ((20787 / 62410) : ℂ) * ζ ^ 14 - ((277637 / 187230) : ℂ) * ζ ^ 15 - ((23617 / 18723) : ℂ) * ζ ^ 16 - ((189553 / 62410) : ℂ) * ζ ^ 17 - ((30553 / 93615) : ℂ) * ζ ^ 18 - ((178319 / 187230) : ℂ) * ζ ^ 19 + ((18775 / 37446) : ℂ) * ζ ^ 20 + ((304799 / 187230) : ℂ) * ζ ^ 21 + ((61948 / 93615) : ℂ) * ζ ^ 22 - ((289 / 2370) : ℂ) * ζ ^ 23 - ((44372 / 18723) : ℂ) * ζ ^ 24 - ((150113 / 93615) : ℂ) * ζ ^ 25 - ((137783 / 187230) : ℂ) * ζ ^ 26 - ((487943 / 187230) : ℂ) * ζ ^ 27 - ((2693 / 6241) : ℂ) * ζ ^ 28 + ((18443 / 12482) : ℂ) * ζ ^ 29 + ((4755 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep01CoefficientIdentity04 :
    row18_reducedY66_combinationStep01Coefficient04 =
      row18_reducedY66_combinationStep00Coefficient04 +
        row18_reducedY66_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep01Coefficient04 row18_reducedY66_combinationStep00Coefficient04 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep01CoefficientIdentity05 :
    row18_reducedY66_combinationStep01Coefficient05 =
      row18_reducedY66_combinationStep00Coefficient05 +
        row18_reducedY66_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep01Coefficient05 row18_reducedY66_combinationStep00Coefficient05 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep01CoefficientIdentity06 :
    row18_reducedY66_combinationStep01Coefficient06 =
      row18_reducedY66_combinationStep00Coefficient06 +
        row18_reducedY66_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep01Coefficient06 row18_reducedY66_combinationStep00Coefficient06 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep01CoefficientIdentity07 :
    row18_reducedY66_combinationStep01Coefficient07 =
      row18_reducedY66_combinationStep00Coefficient07 +
        row18_reducedY66_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep01Coefficient07 row18_reducedY66_combinationStep00Coefficient07 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep01CoefficientIdentity08 :
    row18_reducedY66_combinationStep01Coefficient08 =
      row18_reducedY66_combinationStep00Coefficient08 +
        row18_reducedY66_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep01Coefficient08 row18_reducedY66_combinationStep00Coefficient08 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep01CoefficientIdentity09 :
    row18_reducedY66_combinationStep01Coefficient09 =
      row18_reducedY66_combinationStep00Coefficient09 +
        row18_reducedY66_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep01Coefficient09 row18_reducedY66_combinationStep00Coefficient09 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep01CoefficientIdentity10 :
    row18_reducedY66_combinationStep01Coefficient10 =
      row18_reducedY66_combinationStep00Coefficient10 +
        row18_reducedY66_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep01Coefficient10 row18_reducedY66_combinationStep00Coefficient10 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep01CoefficientIdentity11 :
    row18_reducedY66_combinationStep01Coefficient11 =
      row18_reducedY66_combinationStep00Coefficient11 +
        row18_reducedY66_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep01Coefficient11 row18_reducedY66_combinationStep00Coefficient11 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep01CoefficientIdentity12 :
    row18_reducedY66_combinationStep01Coefficient12 =
      row18_reducedY66_combinationStep00Coefficient12 +
        row18_reducedY66_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep01Coefficient12 row18_reducedY66_combinationStep00Coefficient12 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep01CoefficientIdentity13 :
    row18_reducedY66_combinationStep01Coefficient13 =
      row18_reducedY66_combinationStep00Coefficient13 +
        row18_reducedY66_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep01Coefficient13 row18_reducedY66_combinationStep00Coefficient13 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep01CoefficientIdentity14 :
    row18_reducedY66_combinationStep01Coefficient14 =
      row18_reducedY66_combinationStep00Coefficient14 +
        row18_reducedY66_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep01Coefficient14 row18_reducedY66_combinationStep00Coefficient14 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep01CoefficientIdentity15 :
    row18_reducedY66_combinationStep01Coefficient15 =
      row18_reducedY66_combinationStep00Coefficient15 +
        row18_reducedY66_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep01Coefficient15 row18_reducedY66_combinationStep00Coefficient15 row18_reducedY66_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY66_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY66_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY66_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY66_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY66_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY66_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY66_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY66_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY66_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY66_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY66_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY66_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY66_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY66_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY66_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY66_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY66_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY66_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY66_combinationStep01CoefficientIdentity00,
      row18_reducedY66_combinationStep01CoefficientIdentity01,
      row18_reducedY66_combinationStep01CoefficientIdentity02,
      row18_reducedY66_combinationStep01CoefficientIdentity03,
      row18_reducedY66_combinationStep01CoefficientIdentity04,
      row18_reducedY66_combinationStep01CoefficientIdentity05,
      row18_reducedY66_combinationStep01CoefficientIdentity06,
      row18_reducedY66_combinationStep01CoefficientIdentity07,
      row18_reducedY66_combinationStep01CoefficientIdentity08,
      row18_reducedY66_combinationStep01CoefficientIdentity09,
      row18_reducedY66_combinationStep01CoefficientIdentity10,
      row18_reducedY66_combinationStep01CoefficientIdentity11,
      row18_reducedY66_combinationStep01CoefficientIdentity12,
      row18_reducedY66_combinationStep01CoefficientIdentity13,
      row18_reducedY66_combinationStep01CoefficientIdentity14,
      row18_reducedY66_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY66_combinationStep01Multiplier * equation

private def row18_reducedY66_combinationStep02Multiplier : ℂ :=
  (-((1020 / 79) : ℂ) + ((262 / 79) : ℂ) * ζ ^ 1 - ((6496 / 395) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 3 - ((986 / 79) : ℂ) * ζ ^ 5 - ((33152 / 1185) : ℂ) * ζ ^ 6 - ((2530 / 237) : ℂ) * ζ ^ 8 - ((4292 / 237) : ℂ) * ζ ^ 9 - ((4304 / 237) : ℂ) * ζ ^ 11 - ((2530 / 237) : ℂ) * ζ ^ 12 - ((262 / 79) : ℂ) * ζ ^ 13 - ((1252 / 79) : ℂ) * ζ ^ 15 - ((262 / 79) : ℂ) * ζ ^ 17 + ((13664 / 1185) : ℂ) * ζ ^ 18 - ((266 / 79) : ℂ) * ζ ^ 21 + ((6496 / 395) : ℂ) * ζ ^ 22 + ((1248 / 79) : ℂ) * ζ ^ 25 + ((266 / 79) : ℂ) * ζ ^ 27 + ((2530 / 237) : ℂ) * ζ ^ 28 + ((262 / 79) : ℂ) * ζ ^ 29 - ((16576 / 1185) : ℂ) * ζ ^ 30 + ((4304 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY66_combinationStep02Coefficient00 : ℂ :=
  (((615 / 158) : ℂ) - ((3349 / 1185) : ℂ) * ζ ^ 1 + ((16547 / 2370) : ℂ) * ζ ^ 2 + ((229 / 790) : ℂ) * ζ ^ 3 + ((11051 / 2370) : ℂ) * ζ ^ 5 + ((10919 / 1185) : ℂ) * ζ ^ 6 + ((2657 / 474) : ℂ) * ζ ^ 8 + ((20401 / 2370) : ℂ) * ζ ^ 9 + ((9857 / 1185) : ℂ) * ζ ^ 11 + ((2657 / 474) : ℂ) * ζ ^ 12 + ((3349 / 1185) : ℂ) * ζ ^ 13 + ((8531 / 1185) : ℂ) * ζ ^ 15 + ((3349 / 1185) : ℂ) * ζ ^ 17 - ((5291 / 2370) : ℂ) * ζ ^ 18 + ((6011 / 2370) : ℂ) * ζ ^ 21 - ((16547 / 2370) : ℂ) * ζ ^ 22 - ((17749 / 2370) : ℂ) * ζ ^ 25 - ((6011 / 2370) : ℂ) * ζ ^ 27 - ((2657 / 474) : ℂ) * ζ ^ 28 - ((3349 / 1185) : ℂ) * ζ ^ 29 + ((10919 / 2370) : ℂ) * ζ ^ 30 - ((9857 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep02CoefficientIdentity00 :
    row18_reducedY66_combinationStep02Coefficient00 =
      row18_reducedY66_combinationStep01Coefficient00 +
        row18_reducedY66_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep02Coefficient00 row18_reducedY66_combinationStep01Coefficient00 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 (-((3755 / 12482) : ℂ) + ((78267 / 31205) : ℂ) * ζ ^ 1 - ((37537 / 12482) : ℂ) * ζ ^ 2 - ((830387 / 187230) : ℂ) * ζ ^ 3 + ((59255 / 12482) : ℂ) * ζ ^ 4 - ((329723 / 62410) : ℂ) * ζ ^ 5 - ((160933 / 37446) : ℂ) * ζ ^ 6 + ((233147 / 31205) : ℂ) * ζ ^ 7 - ((100817 / 31205) : ℂ) * ζ ^ 8 - ((295061 / 93615) : ℂ) * ζ ^ 9 + ((200029 / 37446) : ℂ) * ζ ^ 10 - ((272707 / 62410) : ℂ) * ζ ^ 11 - ((255083 / 93615) : ℂ) * ζ ^ 12 + ((750844 / 93615) : ℂ) * ζ ^ 13 - ((101129 / 12482) : ℂ) * ζ ^ 14 + ((190831 / 93615) : ℂ) * ζ ^ 15 + ((1258831 / 187230) : ℂ) * ζ ^ 16 - ((248563 / 37446) : ℂ) * ζ ^ 17 + ((41357 / 12482) : ℂ) * ζ ^ 18 + ((77843 / 37446) : ℂ) * ζ ^ 19 - ((848141 / 187230) : ℂ) * ζ ^ 20 + ((381919 / 93615) : ℂ) * ζ ^ 21 - ((3982 / 18723) : ℂ) * ζ ^ 22 + ((12329 / 93615) : ℂ) * ζ ^ 23 + ((1477 / 187230) : ℂ) * ζ ^ 24 + ((24888 / 31205) : ℂ) * ζ ^ 25 + ((45533 / 37446) : ℂ) * ζ ^ 26 - ((68443 / 31205) : ℂ) * ζ ^ 27 + ((46413 / 31205) : ℂ) * ζ ^ 28 - ((608 / 395) : ℂ) * ζ ^ 29 + ((15064 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep02Coefficient01 : ℂ :=
  (-((8081 / 474) : ℂ) + ((5437 / 474) : ℂ) * ζ ^ 1 + ((2029 / 474) : ℂ) * ζ ^ 2 - ((917 / 79) : ℂ) * ζ ^ 3 + ((5437 / 474) : ℂ) * ζ ^ 5 - ((3026 / 237) : ℂ) * ζ ^ 6 + ((3026 / 237) : ℂ) * ζ ^ 8 - ((5437 / 474) : ℂ) * ζ ^ 9 + ((917 / 158) : ℂ) * ζ ^ 11 - ((65 / 474) : ℂ) * ζ ^ 12 - ((5437 / 474) : ℂ) * ζ ^ 13 - ((3149 / 474) : ℂ) * ζ ^ 15 - ((5437 / 474) : ℂ) * ζ ^ 17 - ((1750 / 237) : ℂ) * ζ ^ 18 - ((3573 / 158) : ℂ) * ζ ^ 21 - ((2029 / 474) : ℂ) * ζ ^ 22 - ((1592 / 79) : ℂ) * ζ ^ 24 - ((8651 / 474) : ℂ) * ζ ^ 27 - ((3026 / 237) : ℂ) * ζ ^ 28 + ((5437 / 474) : ℂ) * ζ ^ 29 - ((2039 / 158) : ℂ) * ζ ^ 30 - ((917 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep02CoefficientIdentity01 :
    row18_reducedY66_combinationStep02Coefficient01 =
      row18_reducedY66_combinationStep01Coefficient01 +
        row18_reducedY66_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep02Coefficient01 row18_reducedY66_combinationStep01Coefficient01 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 (((698255 / 37446) : ℂ) - ((630463 / 37446) : ℂ) * ζ ^ 1 - ((944893 / 93615) : ℂ) * ζ ^ 2 + ((898805 / 37446) : ℂ) * ζ ^ 3 - ((44689 / 2370) : ℂ) * ζ ^ 4 - ((149819 / 31205) : ℂ) * ζ ^ 5 + ((1824611 / 93615) : ℂ) * ζ ^ 6 - ((72337 / 6241) : ℂ) * ζ ^ 7 - ((45088 / 18723) : ℂ) * ζ ^ 8 + ((3402163 / 187230) : ℂ) * ζ ^ 9 - ((247693 / 37446) : ℂ) * ζ ^ 10 - ((43653 / 12482) : ℂ) * ζ ^ 11 + ((1265289 / 62410) : ℂ) * ζ ^ 12 - ((1767431 / 187230) : ℂ) * ζ ^ 13 + ((662563 / 187230) : ℂ) * ζ ^ 14 + ((187013 / 12482) : ℂ) * ζ ^ 15 - ((808349 / 93615) : ℂ) * ζ ^ 16 + ((450009 / 62410) : ℂ) * ζ ^ 17 + ((263237 / 18723) : ℂ) * ζ ^ 18 - ((164539 / 12482) : ℂ) * ζ ^ 19 + ((256901 / 31205) : ℂ) * ζ ^ 20 + ((301662 / 31205) : ℂ) * ζ ^ 21 - ((211018 / 31205) : ℂ) * ζ ^ 22 + ((17333 / 12482) : ℂ) * ζ ^ 23 + ((898891 / 93615) : ℂ) * ζ ^ 24 - ((54415 / 12482) : ℂ) * ζ ^ 25 - ((249902 / 93615) : ℂ) * ζ ^ 26 + ((115473 / 12482) : ℂ) * ζ ^ 27 - ((1336607 / 187230) : ℂ) * ζ ^ 28 + ((236648 / 93615) : ℂ) * ζ ^ 29 + ((13988 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep02Coefficient02 : ℂ :=
  (((188 / 79) : ℂ) - ((674 / 237) : ℂ) * ζ ^ 1 - ((193 / 474) : ℂ) * ζ ^ 2 + ((1621 / 474) : ℂ) * ζ ^ 3 - ((3473 / 237) : ℂ) * ζ ^ 5 + ((460 / 237) : ℂ) * ζ ^ 6 - ((985 / 237) : ℂ) * ζ ^ 8 - ((2125 / 474) : ℂ) * ζ ^ 9 - ((1173 / 79) : ℂ) * ζ ^ 11 - ((371 / 158) : ℂ) * ζ ^ 12 + ((674 / 237) : ℂ) * ζ ^ 13 - ((1621 / 474) : ℂ) * ζ ^ 15 + ((674 / 237) : ℂ) * ζ ^ 17 - ((935 / 474) : ℂ) * ζ ^ 18 + ((933 / 79) : ℂ) * ζ ^ 21 + ((193 / 474) : ℂ) * ζ ^ 22 + ((193 / 474) : ℂ) * ζ ^ 24 + ((933 / 79) : ℂ) * ζ ^ 25 + ((1173 / 79) : ℂ) * ζ ^ 27 + ((985 / 237) : ℂ) * ζ ^ 28 - ((674 / 237) : ℂ) * ζ ^ 29 + ((1777 / 474) : ℂ) * ζ ^ 30 + ((1173 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep02CoefficientIdentity02 :
    row18_reducedY66_combinationStep02Coefficient02 =
      row18_reducedY66_combinationStep01Coefficient02 +
        row18_reducedY66_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep02Coefficient02 row18_reducedY66_combinationStep01Coefficient02 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep02Coefficient03 : ℂ :=
  (-((245 / 79) : ℂ) - ((61 / 237) : ℂ) * ζ ^ 1 + ((113 / 474) : ℂ) * ζ ^ 2 + ((1231 / 474) : ℂ) * ζ ^ 3 - ((179 / 237) : ℂ) * ζ ^ 5 - ((41 / 237) : ℂ) * ζ ^ 6 + ((76 / 79) : ℂ) * ζ ^ 8 + ((194 / 237) : ℂ) * ζ ^ 9 - ((281 / 158) : ℂ) * ζ ^ 11 + ((76 / 79) : ℂ) * ζ ^ 12 + ((61 / 237) : ℂ) * ζ ^ 13 - ((489 / 158) : ℂ) * ζ ^ 15 + ((61 / 237) : ℂ) * ζ ^ 17 + ((65 / 158) : ℂ) * ζ ^ 18 - ((1109 / 474) : ℂ) * ζ ^ 21 - ((113 / 474) : ℂ) * ζ ^ 22 + ((118 / 237) : ℂ) * ζ ^ 25 + ((1109 / 474) : ℂ) * ζ ^ 27 - ((76 / 79) : ℂ) * ζ ^ 28 - ((61 / 237) : ℂ) * ζ ^ 29 - ((41 / 474) : ℂ) * ζ ^ 30 + ((281 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep02CoefficientIdentity03 :
    row18_reducedY66_combinationStep02Coefficient03 =
      row18_reducedY66_combinationStep01Coefficient03 +
        row18_reducedY66_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep02Coefficient03 row18_reducedY66_combinationStep01Coefficient03 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep02Coefficient04 : ℂ :=
  (-((125 / 158) : ℂ) + ((1218 / 395) : ℂ) * ζ ^ 1 - ((2852 / 395) : ℂ) * ζ ^ 2 - ((3421 / 1185) : ℂ) * ζ ^ 3 - ((3087 / 790) : ℂ) * ζ ^ 5 - ((10714 / 1185) : ℂ) * ζ ^ 6 - ((3113 / 474) : ℂ) * ζ ^ 8 - ((7447 / 790) : ℂ) * ζ ^ 9 - ((15499 / 2370) : ℂ) * ζ ^ 11 - ((3113 / 474) : ℂ) * ζ ^ 12 - ((1218 / 395) : ℂ) * ζ ^ 13 - ((9727 / 2370) : ℂ) * ζ ^ 15 - ((1218 / 395) : ℂ) * ζ ^ 17 + ((2158 / 1185) : ℂ) * ζ ^ 18 - ((233 / 1185) : ℂ) * ζ ^ 21 + ((2852 / 395) : ℂ) * ζ ^ 22 + ((5523 / 790) : ℂ) * ζ ^ 25 + ((233 / 1185) : ℂ) * ζ ^ 27 + ((3113 / 474) : ℂ) * ζ ^ 28 + ((1218 / 395) : ℂ) * ζ ^ 29 - ((5357 / 1185) : ℂ) * ζ ^ 30 + ((15499 / 2370) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep02CoefficientIdentity04 :
    row18_reducedY66_combinationStep02Coefficient04 =
      row18_reducedY66_combinationStep01Coefficient04 +
        row18_reducedY66_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep02Coefficient04 row18_reducedY66_combinationStep01Coefficient04 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 (((3755 / 12482) : ℂ) - ((78267 / 31205) : ℂ) * ζ ^ 1 + ((37537 / 12482) : ℂ) * ζ ^ 2 + ((830387 / 187230) : ℂ) * ζ ^ 3 - ((59255 / 12482) : ℂ) * ζ ^ 4 + ((329723 / 62410) : ℂ) * ζ ^ 5 + ((160933 / 37446) : ℂ) * ζ ^ 6 - ((233147 / 31205) : ℂ) * ζ ^ 7 + ((100817 / 31205) : ℂ) * ζ ^ 8 + ((295061 / 93615) : ℂ) * ζ ^ 9 - ((200029 / 37446) : ℂ) * ζ ^ 10 + ((272707 / 62410) : ℂ) * ζ ^ 11 + ((255083 / 93615) : ℂ) * ζ ^ 12 - ((750844 / 93615) : ℂ) * ζ ^ 13 + ((101129 / 12482) : ℂ) * ζ ^ 14 - ((190831 / 93615) : ℂ) * ζ ^ 15 - ((1258831 / 187230) : ℂ) * ζ ^ 16 + ((248563 / 37446) : ℂ) * ζ ^ 17 - ((41357 / 12482) : ℂ) * ζ ^ 18 - ((77843 / 37446) : ℂ) * ζ ^ 19 + ((848141 / 187230) : ℂ) * ζ ^ 20 - ((381919 / 93615) : ℂ) * ζ ^ 21 + ((3982 / 18723) : ℂ) * ζ ^ 22 - ((12329 / 93615) : ℂ) * ζ ^ 23 - ((1477 / 187230) : ℂ) * ζ ^ 24 - ((24888 / 31205) : ℂ) * ζ ^ 25 - ((45533 / 37446) : ℂ) * ζ ^ 26 + ((68443 / 31205) : ℂ) * ζ ^ 27 - ((46413 / 31205) : ℂ) * ζ ^ 28 + ((608 / 395) : ℂ) * ζ ^ 29 - ((15064 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep02CoefficientIdentity05 :
    row18_reducedY66_combinationStep02Coefficient05 =
      row18_reducedY66_combinationStep01Coefficient05 +
        row18_reducedY66_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep02Coefficient05 row18_reducedY66_combinationStep01Coefficient05 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep02Coefficient06 : ℂ :=
  (-((577 / 237) : ℂ) - ((695 / 474) : ℂ) * ζ ^ 1 - ((1007 / 237) : ℂ) * ζ ^ 2 - ((1336 / 395) : ℂ) * ζ ^ 3 - ((3 / 79) : ℂ) * ζ ^ 6 - ((124 / 79) : ℂ) * ζ ^ 8 - ((713 / 158) : ℂ) * ζ ^ 9 + ((6353 / 2370) : ℂ) * ζ ^ 11 + ((998 / 237) : ℂ) * ζ ^ 12 + ((695 / 474) : ℂ) * ζ ^ 13 - ((1336 / 395) : ℂ) * ζ ^ 15 + ((695 / 474) : ℂ) * ζ ^ 17 + ((430 / 237) : ℂ) * ζ ^ 18 + ((695 / 474) : ℂ) * ζ ^ 21 + ((1007 / 237) : ℂ) * ζ ^ 22 - ((1007 / 237) : ℂ) * ζ ^ 24 - ((695 / 474) : ℂ) * ζ ^ 25 + ((6353 / 2370) : ℂ) * ζ ^ 27 + ((124 / 79) : ℂ) * ζ ^ 28 - ((695 / 474) : ℂ) * ζ ^ 29 - ((1379 / 237) : ℂ) * ζ ^ 30 - ((6353 / 2370) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep02CoefficientIdentity06 :
    row18_reducedY66_combinationStep02Coefficient06 =
      row18_reducedY66_combinationStep01Coefficient06 +
        row18_reducedY66_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep02Coefficient06 row18_reducedY66_combinationStep01Coefficient06 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 (((74653 / 18723) : ℂ) + ((20081 / 37446) : ℂ) * ζ ^ 1 + ((1275497 / 187230) : ℂ) * ζ ^ 2 + ((100079 / 62410) : ℂ) * ζ ^ 3 - ((295898 / 93615) : ℂ) * ζ ^ 4 - ((53581 / 187230) : ℂ) * ζ ^ 5 - ((78969 / 31205) : ℂ) * ζ ^ 6 - ((50119 / 18723) : ℂ) * ζ ^ 7 + ((505414 / 93615) : ℂ) * ζ ^ 8 + ((149246 / 93615) : ℂ) * ζ ^ 9 - ((1979 / 62410) : ℂ) * ζ ^ 10 - ((76133 / 187230) : ℂ) * ζ ^ 11 - ((497189 / 187230) : ℂ) * ζ ^ 12 - ((597697 / 187230) : ℂ) * ζ ^ 13 - ((39591 / 62410) : ℂ) * ζ ^ 14 + ((151087 / 187230) : ℂ) * ζ ^ 15 + ((89071 / 62410) : ℂ) * ζ ^ 16 + ((6749 / 37446) : ℂ) * ζ ^ 17 + ((43073 / 187230) : ℂ) * ζ ^ 18 - ((425659 / 187230) : ℂ) * ζ ^ 19 - ((7289 / 12482) : ℂ) * ζ ^ 20 - ((2132 / 18723) : ℂ) * ζ ^ 21 - ((52799 / 31205) : ℂ) * ζ ^ 22 + ((37599 / 12482) : ℂ) * ζ ^ 23 + ((66017 / 93615) : ℂ) * ζ ^ 24 - ((20579 / 18723) : ℂ) * ζ ^ 25 + ((262631 / 93615) : ℂ) * ζ ^ 26 - ((184463 / 62410) : ℂ) * ζ ^ 27 - ((228469 / 187230) : ℂ) * ζ ^ 28 + ((13072 / 6241) : ℂ) * ζ ^ 29 + ((5380 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep02CoefficientIdentity07 :
    row18_reducedY66_combinationStep02Coefficient07 =
      row18_reducedY66_combinationStep01Coefficient07 +
        row18_reducedY66_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep02Coefficient07 row18_reducedY66_combinationStep01Coefficient07 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep02CoefficientIdentity08 :
    row18_reducedY66_combinationStep02Coefficient08 =
      row18_reducedY66_combinationStep01Coefficient08 +
        row18_reducedY66_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep02Coefficient08 row18_reducedY66_combinationStep01Coefficient08 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep02CoefficientIdentity09 :
    row18_reducedY66_combinationStep02Coefficient09 =
      row18_reducedY66_combinationStep01Coefficient09 +
        row18_reducedY66_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep02Coefficient09 row18_reducedY66_combinationStep01Coefficient09 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep02CoefficientIdentity10 :
    row18_reducedY66_combinationStep02Coefficient10 =
      row18_reducedY66_combinationStep01Coefficient10 +
        row18_reducedY66_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep02Coefficient10 row18_reducedY66_combinationStep01Coefficient10 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep02CoefficientIdentity11 :
    row18_reducedY66_combinationStep02Coefficient11 =
      row18_reducedY66_combinationStep01Coefficient11 +
        row18_reducedY66_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep02Coefficient11 row18_reducedY66_combinationStep01Coefficient11 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep02CoefficientIdentity12 :
    row18_reducedY66_combinationStep02Coefficient12 =
      row18_reducedY66_combinationStep01Coefficient12 +
        row18_reducedY66_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep02Coefficient12 row18_reducedY66_combinationStep01Coefficient12 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep02CoefficientIdentity13 :
    row18_reducedY66_combinationStep02Coefficient13 =
      row18_reducedY66_combinationStep01Coefficient13 +
        row18_reducedY66_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep02Coefficient13 row18_reducedY66_combinationStep01Coefficient13 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep02CoefficientIdentity14 :
    row18_reducedY66_combinationStep02Coefficient14 =
      row18_reducedY66_combinationStep01Coefficient14 +
        row18_reducedY66_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep02Coefficient14 row18_reducedY66_combinationStep01Coefficient14 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep02CoefficientIdentity15 :
    row18_reducedY66_combinationStep02Coefficient15 =
      row18_reducedY66_combinationStep01Coefficient15 +
        row18_reducedY66_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep02Coefficient15 row18_reducedY66_combinationStep01Coefficient15 row18_reducedY66_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY66_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY66_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY66_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY66_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY66_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY66_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY66_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY66_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY66_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY66_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY66_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY66_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY66_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY66_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY66_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY66_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY66_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY66_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY66_combinationStep02CoefficientIdentity00,
      row18_reducedY66_combinationStep02CoefficientIdentity01,
      row18_reducedY66_combinationStep02CoefficientIdentity02,
      row18_reducedY66_combinationStep02CoefficientIdentity03,
      row18_reducedY66_combinationStep02CoefficientIdentity04,
      row18_reducedY66_combinationStep02CoefficientIdentity05,
      row18_reducedY66_combinationStep02CoefficientIdentity06,
      row18_reducedY66_combinationStep02CoefficientIdentity07,
      row18_reducedY66_combinationStep02CoefficientIdentity08,
      row18_reducedY66_combinationStep02CoefficientIdentity09,
      row18_reducedY66_combinationStep02CoefficientIdentity10,
      row18_reducedY66_combinationStep02CoefficientIdentity11,
      row18_reducedY66_combinationStep02CoefficientIdentity12,
      row18_reducedY66_combinationStep02CoefficientIdentity13,
      row18_reducedY66_combinationStep02CoefficientIdentity14,
      row18_reducedY66_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY66_combinationStep02Multiplier * equation

private def row18_reducedY66_combinationStep03Multiplier : ℂ :=
  (-((148 / 79) : ℂ) + ((526 / 237) : ℂ) * ζ ^ 1 - ((1284 / 79) : ℂ) * ζ ^ 2 - ((1426 / 79) : ℂ) * ζ ^ 5 - ((1136 / 79) : ℂ) * ζ ^ 6 - ((1136 / 79) : ℂ) * ζ ^ 8 - ((1426 / 79) : ℂ) * ζ ^ 9 - ((4148 / 237) : ℂ) * ζ ^ 11 - ((1898 / 237) : ℂ) * ζ ^ 12 - ((526 / 237) : ℂ) * ζ ^ 13 - ((3056 / 237) : ℂ) * ζ ^ 15 - ((526 / 237) : ℂ) * ζ ^ 17 + ((572 / 79) : ℂ) * ζ ^ 18 + ((1876 / 237) : ℂ) * ζ ^ 21 + ((1284 / 79) : ℂ) * ζ ^ 22 + ((564 / 79) : ℂ) * ζ ^ 24 + ((4804 / 237) : ℂ) * ζ ^ 25 + ((3056 / 237) : ℂ) * ζ ^ 27 + ((1136 / 79) : ℂ) * ζ ^ 28 + ((526 / 237) : ℂ) * ζ ^ 29 - ((1510 / 237) : ℂ) * ζ ^ 30 + ((4148 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY66_combinationStep03Coefficient00 : ℂ :=
  (((226 / 79) : ℂ) - ((1608 / 395) : ℂ) * ζ ^ 1 + ((8049 / 790) : ℂ) * ζ ^ 2 + ((1017 / 395) : ℂ) * ζ ^ 3 + ((1596 / 395) : ℂ) * ζ ^ 5 + ((4558 / 395) : ℂ) * ζ ^ 6 + ((1315 / 158) : ℂ) * ζ ^ 8 + ((3911 / 395) : ℂ) * ζ ^ 9 + ((2894 / 395) : ℂ) * ζ ^ 11 + ((1315 / 158) : ℂ) * ζ ^ 12 + ((1608 / 395) : ℂ) * ζ ^ 13 + ((2187 / 395) : ℂ) * ζ ^ 15 + ((1608 / 395) : ℂ) * ζ ^ 17 - ((1067 / 790) : ℂ) * ζ ^ 18 + ((591 / 395) : ℂ) * ζ ^ 21 - ((8049 / 790) : ℂ) * ζ ^ 22 - ((3204 / 395) : ℂ) * ζ ^ 25 - ((591 / 395) : ℂ) * ζ ^ 27 - ((1315 / 158) : ℂ) * ζ ^ 28 - ((1608 / 395) : ℂ) * ζ ^ 29 + ((2279 / 395) : ℂ) * ζ ^ 30 - ((2894 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep03CoefficientIdentity00 :
    row18_reducedY66_combinationStep03Coefficient00 =
      row18_reducedY66_combinationStep02Coefficient00 +
        row18_reducedY66_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep03Coefficient00 row18_reducedY66_combinationStep02Coefficient00 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 (((10065 / 12482) : ℂ) + ((9915 / 6241) : ℂ) * ζ ^ 1 - ((199129 / 37446) : ℂ) * ζ ^ 2 - ((331 / 237) : ℂ) * ζ ^ 3 - ((19231 / 12482) : ℂ) * ζ ^ 4 - ((71243 / 37446) : ℂ) * ζ ^ 5 + ((11263 / 6241) : ℂ) * ζ ^ 6 + ((59863 / 37446) : ℂ) * ζ ^ 7 - ((128605 / 37446) : ℂ) * ζ ^ 8 + ((2571 / 12482) : ℂ) * ζ ^ 9 + ((11009 / 12482) : ℂ) * ζ ^ 10 + ((775 / 18723) : ℂ) * ζ ^ 11 + ((40187 / 37446) : ℂ) * ζ ^ 12 + ((14195 / 6241) : ℂ) * ζ ^ 13 - ((8003 / 37446) : ℂ) * ζ ^ 14 + ((20923 / 37446) : ℂ) * ζ ^ 15 + ((10315 / 18723) : ℂ) * ζ ^ 16 - ((2933 / 37446) : ℂ) * ζ ^ 17 - ((2013 / 12482) : ℂ) * ζ ^ 18 + ((3395 / 6241) : ℂ) * ζ ^ 19 - ((2719 / 37446) : ℂ) * ζ ^ 20 + ((31417 / 18723) : ℂ) * ζ ^ 21 + ((14909 / 18723) : ℂ) * ζ ^ 22 - ((36821 / 18723) : ℂ) * ζ ^ 23 + ((8146 / 18723) : ℂ) * ζ ^ 24 - ((3077 / 37446) : ℂ) * ζ ^ 25 - ((15076 / 6241) : ℂ) * ζ ^ 26 + ((93997 / 37446) : ℂ) * ζ ^ 27 + ((5333 / 37446) : ℂ) * ζ ^ 28 - ((29409 / 12482) : ℂ) * ζ ^ 29 - ((5185 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep03Coefficient01 : ℂ :=
  (-((33 / 79) : ℂ) + ((23 / 79) : ℂ) * ζ ^ 1 - ((7 / 79) : ℂ) * ζ ^ 2 - ((28 / 79) : ℂ) * ζ ^ 3 + ((23 / 79) : ℂ) * ζ ^ 5 - ((40 / 79) : ℂ) * ζ ^ 6 + ((40 / 79) : ℂ) * ζ ^ 8 - ((23 / 79) : ℂ) * ζ ^ 9 + ((14 / 79) : ℂ) * ζ ^ 11 + ((45 / 79) : ℂ) * ζ ^ 12 - ((23 / 79) : ℂ) * ζ ^ 13 - ((11 / 79) : ℂ) * ζ ^ 15 - ((23 / 79) : ℂ) * ζ ^ 17 + ((32 / 79) : ℂ) * ζ ^ 18 - ((58 / 79) : ℂ) * ζ ^ 21 + ((7 / 79) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 - ((39 / 79) : ℂ) * ζ ^ 27 - ((40 / 79) : ℂ) * ζ ^ 28 + ((23 / 79) : ℂ) * ζ ^ 29 + ((5 / 79) : ℂ) * ζ ^ 30 - ((14 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep03CoefficientIdentity01 :
    row18_reducedY66_combinationStep03Coefficient01 =
      row18_reducedY66_combinationStep02Coefficient01 +
        row18_reducedY66_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep03Coefficient01 row18_reducedY66_combinationStep02Coefficient01 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 (-((629861 / 37446) : ℂ) + ((414383 / 37446) : ℂ) * ζ ^ 1 + ((41945 / 18723) : ℂ) * ζ ^ 2 - ((474887 / 37446) : ℂ) * ζ ^ 3 + ((2042 / 237) : ℂ) * ζ ^ 4 + ((31168 / 18723) : ℂ) * ζ ^ 5 - ((693715 / 37446) : ℂ) * ζ ^ 6 - ((64850 / 18723) : ℂ) * ζ ^ 7 - ((1515 / 12482) : ℂ) * ζ ^ 8 - ((180597 / 12482) : ℂ) * ζ ^ 9 + ((159001 / 37446) : ℂ) * ζ ^ 10 - ((138242 / 18723) : ℂ) * ζ ^ 11 - ((315742 / 18723) : ℂ) * ζ ^ 12 + ((38800 / 18723) : ℂ) * ζ ^ 13 - ((133471 / 12482) : ℂ) * ζ ^ 14 - ((267050 / 18723) : ℂ) * ζ ^ 15 + ((23995 / 6241) : ℂ) * ζ ^ 16 - ((199793 / 18723) : ℂ) * ζ ^ 17 - ((196355 / 18723) : ℂ) * ζ ^ 18 + ((179555 / 37446) : ℂ) * ζ ^ 19 - ((305303 / 37446) : ℂ) * ζ ^ 20 - ((73429 / 6241) : ℂ) * ζ ^ 21 + ((23290 / 6241) : ℂ) * ζ ^ 22 - ((425 / 18723) : ℂ) * ζ ^ 23 - ((8823 / 6241) : ℂ) * ζ ^ 24 + ((34915 / 6241) : ℂ) * ζ ^ 25 - ((246377 / 37446) : ℂ) * ζ ^ 26 + ((11959 / 12482) : ℂ) * ζ ^ 27 + ((53731 / 18723) : ℂ) * ζ ^ 28 + ((14318 / 18723) : ℂ) * ζ ^ 29 + ((29036 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep03Coefficient02 : ℂ :=
  (((188 / 79) : ℂ) - ((674 / 237) : ℂ) * ζ ^ 1 - ((193 / 474) : ℂ) * ζ ^ 2 + ((1621 / 474) : ℂ) * ζ ^ 3 - ((3473 / 237) : ℂ) * ζ ^ 5 + ((460 / 237) : ℂ) * ζ ^ 6 - ((985 / 237) : ℂ) * ζ ^ 8 - ((2125 / 474) : ℂ) * ζ ^ 9 - ((1173 / 79) : ℂ) * ζ ^ 11 - ((371 / 158) : ℂ) * ζ ^ 12 + ((674 / 237) : ℂ) * ζ ^ 13 - ((1621 / 474) : ℂ) * ζ ^ 15 + ((674 / 237) : ℂ) * ζ ^ 17 - ((935 / 474) : ℂ) * ζ ^ 18 + ((933 / 79) : ℂ) * ζ ^ 21 + ((193 / 474) : ℂ) * ζ ^ 22 + ((193 / 474) : ℂ) * ζ ^ 24 + ((933 / 79) : ℂ) * ζ ^ 25 + ((1173 / 79) : ℂ) * ζ ^ 27 + ((985 / 237) : ℂ) * ζ ^ 28 - ((674 / 237) : ℂ) * ζ ^ 29 + ((1777 / 474) : ℂ) * ζ ^ 30 + ((1173 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep03CoefficientIdentity02 :
    row18_reducedY66_combinationStep03Coefficient02 =
      row18_reducedY66_combinationStep02Coefficient02 +
        row18_reducedY66_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep03Coefficient02 row18_reducedY66_combinationStep02Coefficient02 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep03Coefficient03 : ℂ :=
  (-((245 / 79) : ℂ) - ((61 / 237) : ℂ) * ζ ^ 1 + ((113 / 474) : ℂ) * ζ ^ 2 + ((1231 / 474) : ℂ) * ζ ^ 3 - ((179 / 237) : ℂ) * ζ ^ 5 - ((41 / 237) : ℂ) * ζ ^ 6 + ((76 / 79) : ℂ) * ζ ^ 8 + ((194 / 237) : ℂ) * ζ ^ 9 - ((281 / 158) : ℂ) * ζ ^ 11 + ((76 / 79) : ℂ) * ζ ^ 12 + ((61 / 237) : ℂ) * ζ ^ 13 - ((489 / 158) : ℂ) * ζ ^ 15 + ((61 / 237) : ℂ) * ζ ^ 17 + ((65 / 158) : ℂ) * ζ ^ 18 - ((1109 / 474) : ℂ) * ζ ^ 21 - ((113 / 474) : ℂ) * ζ ^ 22 + ((118 / 237) : ℂ) * ζ ^ 25 + ((1109 / 474) : ℂ) * ζ ^ 27 - ((76 / 79) : ℂ) * ζ ^ 28 - ((61 / 237) : ℂ) * ζ ^ 29 - ((41 / 474) : ℂ) * ζ ^ 30 + ((281 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep03CoefficientIdentity03 :
    row18_reducedY66_combinationStep03Coefficient03 =
      row18_reducedY66_combinationStep02Coefficient03 +
        row18_reducedY66_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep03Coefficient03 row18_reducedY66_combinationStep02Coefficient03 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep03Coefficient04 : ℂ :=
  (-((125 / 158) : ℂ) + ((1218 / 395) : ℂ) * ζ ^ 1 - ((2852 / 395) : ℂ) * ζ ^ 2 - ((3421 / 1185) : ℂ) * ζ ^ 3 - ((3087 / 790) : ℂ) * ζ ^ 5 - ((10714 / 1185) : ℂ) * ζ ^ 6 - ((3113 / 474) : ℂ) * ζ ^ 8 - ((7447 / 790) : ℂ) * ζ ^ 9 - ((15499 / 2370) : ℂ) * ζ ^ 11 - ((3113 / 474) : ℂ) * ζ ^ 12 - ((1218 / 395) : ℂ) * ζ ^ 13 - ((9727 / 2370) : ℂ) * ζ ^ 15 - ((1218 / 395) : ℂ) * ζ ^ 17 + ((2158 / 1185) : ℂ) * ζ ^ 18 - ((233 / 1185) : ℂ) * ζ ^ 21 + ((2852 / 395) : ℂ) * ζ ^ 22 + ((5523 / 790) : ℂ) * ζ ^ 25 + ((233 / 1185) : ℂ) * ζ ^ 27 + ((3113 / 474) : ℂ) * ζ ^ 28 + ((1218 / 395) : ℂ) * ζ ^ 29 - ((5357 / 1185) : ℂ) * ζ ^ 30 + ((15499 / 2370) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep03CoefficientIdentity04 :
    row18_reducedY66_combinationStep03Coefficient04 =
      row18_reducedY66_combinationStep02Coefficient04 +
        row18_reducedY66_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep03Coefficient04 row18_reducedY66_combinationStep02Coefficient04 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep03Coefficient05 : ℂ :=
  (-((177 / 158) : ℂ) + ((827 / 474) : ℂ) * ζ ^ 1 - ((580 / 79) : ℂ) * ζ ^ 2 - ((2573 / 474) : ℂ) * ζ ^ 5 - ((983 / 158) : ℂ) * ζ ^ 6 - ((983 / 158) : ℂ) * ζ ^ 8 - ((2573 / 474) : ℂ) * ζ ^ 9 - ((1847 / 237) : ℂ) * ζ ^ 11 - ((1085 / 237) : ℂ) * ζ ^ 12 - ((827 / 474) : ℂ) * ζ ^ 13 - ((2135 / 474) : ℂ) * ζ ^ 15 - ((827 / 474) : ℂ) * ζ ^ 17 + ((1541 / 474) : ℂ) * ζ ^ 18 + ((291 / 158) : ℂ) * ζ ^ 21 + ((580 / 79) : ℂ) * ζ ^ 22 + ((704 / 237) : ℂ) * ζ ^ 24 + ((1700 / 237) : ℂ) * ζ ^ 25 + ((2135 / 474) : ℂ) * ζ ^ 27 + ((983 / 158) : ℂ) * ζ ^ 28 + ((827 / 474) : ℂ) * ζ ^ 29 - ((779 / 474) : ℂ) * ζ ^ 30 + ((1847 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep03CoefficientIdentity05 :
    row18_reducedY66_combinationStep03Coefficient05 =
      row18_reducedY66_combinationStep02Coefficient05 +
        row18_reducedY66_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep03Coefficient05 row18_reducedY66_combinationStep02Coefficient05 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 (((13095 / 12482) : ℂ) - ((59735 / 37446) : ℂ) * ζ ^ 1 + ((230045 / 37446) : ℂ) * ζ ^ 2 + ((43985 / 37446) : ℂ) * ζ ^ 3 - ((203521 / 37446) : ℂ) * ζ ^ 4 + ((118484 / 18723) : ℂ) * ζ ^ 5 + ((650 / 6241) : ℂ) * ζ ^ 6 - ((117617 / 18723) : ℂ) * ζ ^ 7 + ((110810 / 18723) : ℂ) * ζ ^ 8 - ((8181 / 6241) : ℂ) * ζ ^ 9 - ((15881 / 6241) : ℂ) * ζ ^ 10 + ((196721 / 37446) : ℂ) * ζ ^ 11 - ((12759 / 12482) : ℂ) * ζ ^ 12 - ((36815 / 12482) : ℂ) * ζ ^ 13 + ((260813 / 37446) : ℂ) * ζ ^ 14 - ((70025 / 18723) : ℂ) * ζ ^ 15 - ((109921 / 37446) : ℂ) * ζ ^ 16 + ((29488 / 6241) : ℂ) * ζ ^ 17 - ((166157 / 37446) : ℂ) * ζ ^ 18 - ((68665 / 37446) : ℂ) * ζ ^ 19 + ((13204 / 6241) : ℂ) * ζ ^ 20 - ((80290 / 18723) : ℂ) * ζ ^ 21 - ((9634 / 18723) : ℂ) * ζ ^ 22 + ((19319 / 37446) : ℂ) * ζ ^ 23 - ((5953 / 12482) : ℂ) * ζ ^ 24 - ((9515 / 18723) : ℂ) * ζ ^ 25 - ((3562 / 6241) : ℂ) * ζ ^ 26 + ((61247 / 37446) : ℂ) * ζ ^ 27 - ((19288 / 18723) : ℂ) * ζ ^ 28 + ((21877 / 18723) : ℂ) * ζ ^ 29 - ((14518 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep03Coefficient06 : ℂ :=
  (-((577 / 237) : ℂ) - ((695 / 474) : ℂ) * ζ ^ 1 - ((1007 / 237) : ℂ) * ζ ^ 2 - ((1336 / 395) : ℂ) * ζ ^ 3 - ((3 / 79) : ℂ) * ζ ^ 6 - ((124 / 79) : ℂ) * ζ ^ 8 - ((713 / 158) : ℂ) * ζ ^ 9 + ((6353 / 2370) : ℂ) * ζ ^ 11 + ((998 / 237) : ℂ) * ζ ^ 12 + ((695 / 474) : ℂ) * ζ ^ 13 - ((1336 / 395) : ℂ) * ζ ^ 15 + ((695 / 474) : ℂ) * ζ ^ 17 + ((430 / 237) : ℂ) * ζ ^ 18 + ((695 / 474) : ℂ) * ζ ^ 21 + ((1007 / 237) : ℂ) * ζ ^ 22 - ((1007 / 237) : ℂ) * ζ ^ 24 - ((695 / 474) : ℂ) * ζ ^ 25 + ((6353 / 2370) : ℂ) * ζ ^ 27 + ((124 / 79) : ℂ) * ζ ^ 28 - ((695 / 474) : ℂ) * ζ ^ 29 - ((1379 / 237) : ℂ) * ζ ^ 30 - ((6353 / 2370) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep03CoefficientIdentity06 :
    row18_reducedY66_combinationStep03Coefficient06 =
      row18_reducedY66_combinationStep02Coefficient06 +
        row18_reducedY66_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep03Coefficient06 row18_reducedY66_combinationStep02Coefficient06 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep03Coefficient07 : ℂ :=
  (((163 / 158) : ℂ) + ((295 / 237) : ℂ) * ζ ^ 1 - ((760 / 237) : ℂ) * ζ ^ 2 - ((361 / 158) : ℂ) * ζ ^ 3 + ((295 / 474) : ℂ) * ζ ^ 5 - ((551 / 237) : ℂ) * ζ ^ 6 - ((644 / 237) : ℂ) * ζ ^ 8 - ((613 / 474) : ℂ) * ζ ^ 9 + ((235 / 237) : ℂ) * ζ ^ 11 - ((644 / 237) : ℂ) * ζ ^ 12 - ((295 / 237) : ℂ) * ζ ^ 13 + ((394 / 237) : ℂ) * ζ ^ 15 - ((295 / 237) : ℂ) * ζ ^ 17 - ((209 / 237) : ℂ) * ζ ^ 18 + ((493 / 474) : ℂ) * ζ ^ 21 + ((760 / 237) : ℂ) * ζ ^ 22 + ((295 / 474) : ℂ) * ζ ^ 25 - ((493 / 474) : ℂ) * ζ ^ 27 + ((644 / 237) : ℂ) * ζ ^ 28 + ((295 / 237) : ℂ) * ζ ^ 29 - ((551 / 474) : ℂ) * ζ ^ 30 - ((235 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep03CoefficientIdentity07 :
    row18_reducedY66_combinationStep03Coefficient07 =
      row18_reducedY66_combinationStep02Coefficient07 +
        row18_reducedY66_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep03Coefficient07 row18_reducedY66_combinationStep02Coefficient07 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 (-((10065 / 12482) : ℂ) - ((9915 / 6241) : ℂ) * ζ ^ 1 + ((199129 / 37446) : ℂ) * ζ ^ 2 + ((331 / 237) : ℂ) * ζ ^ 3 + ((19231 / 12482) : ℂ) * ζ ^ 4 + ((71243 / 37446) : ℂ) * ζ ^ 5 - ((11263 / 6241) : ℂ) * ζ ^ 6 - ((59863 / 37446) : ℂ) * ζ ^ 7 + ((128605 / 37446) : ℂ) * ζ ^ 8 - ((2571 / 12482) : ℂ) * ζ ^ 9 - ((11009 / 12482) : ℂ) * ζ ^ 10 - ((775 / 18723) : ℂ) * ζ ^ 11 - ((40187 / 37446) : ℂ) * ζ ^ 12 - ((14195 / 6241) : ℂ) * ζ ^ 13 + ((8003 / 37446) : ℂ) * ζ ^ 14 - ((20923 / 37446) : ℂ) * ζ ^ 15 - ((10315 / 18723) : ℂ) * ζ ^ 16 + ((2933 / 37446) : ℂ) * ζ ^ 17 + ((2013 / 12482) : ℂ) * ζ ^ 18 - ((3395 / 6241) : ℂ) * ζ ^ 19 + ((2719 / 37446) : ℂ) * ζ ^ 20 - ((31417 / 18723) : ℂ) * ζ ^ 21 - ((14909 / 18723) : ℂ) * ζ ^ 22 + ((36821 / 18723) : ℂ) * ζ ^ 23 - ((8146 / 18723) : ℂ) * ζ ^ 24 + ((3077 / 37446) : ℂ) * ζ ^ 25 + ((15076 / 6241) : ℂ) * ζ ^ 26 - ((93997 / 37446) : ℂ) * ζ ^ 27 - ((5333 / 37446) : ℂ) * ζ ^ 28 + ((29409 / 12482) : ℂ) * ζ ^ 29 + ((5185 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep03CoefficientIdentity08 :
    row18_reducedY66_combinationStep03Coefficient08 =
      row18_reducedY66_combinationStep02Coefficient08 +
        row18_reducedY66_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep03Coefficient08 row18_reducedY66_combinationStep02Coefficient08 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep03CoefficientIdentity09 :
    row18_reducedY66_combinationStep03Coefficient09 =
      row18_reducedY66_combinationStep02Coefficient09 +
        row18_reducedY66_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep03Coefficient09 row18_reducedY66_combinationStep02Coefficient09 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep03CoefficientIdentity10 :
    row18_reducedY66_combinationStep03Coefficient10 =
      row18_reducedY66_combinationStep02Coefficient10 +
        row18_reducedY66_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep03Coefficient10 row18_reducedY66_combinationStep02Coefficient10 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep03CoefficientIdentity11 :
    row18_reducedY66_combinationStep03Coefficient11 =
      row18_reducedY66_combinationStep02Coefficient11 +
        row18_reducedY66_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep03Coefficient11 row18_reducedY66_combinationStep02Coefficient11 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep03CoefficientIdentity12 :
    row18_reducedY66_combinationStep03Coefficient12 =
      row18_reducedY66_combinationStep02Coefficient12 +
        row18_reducedY66_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep03Coefficient12 row18_reducedY66_combinationStep02Coefficient12 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep03CoefficientIdentity13 :
    row18_reducedY66_combinationStep03Coefficient13 =
      row18_reducedY66_combinationStep02Coefficient13 +
        row18_reducedY66_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep03Coefficient13 row18_reducedY66_combinationStep02Coefficient13 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep03CoefficientIdentity14 :
    row18_reducedY66_combinationStep03Coefficient14 =
      row18_reducedY66_combinationStep02Coefficient14 +
        row18_reducedY66_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep03Coefficient14 row18_reducedY66_combinationStep02Coefficient14 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep03CoefficientIdentity15 :
    row18_reducedY66_combinationStep03Coefficient15 =
      row18_reducedY66_combinationStep02Coefficient15 +
        row18_reducedY66_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep03Coefficient15 row18_reducedY66_combinationStep02Coefficient15 row18_reducedY66_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY66_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY66_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY66_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY66_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY66_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY66_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY66_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY66_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY66_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY66_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY66_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY66_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY66_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY66_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY66_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY66_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY66_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY66_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY66_combinationStep03CoefficientIdentity00,
      row18_reducedY66_combinationStep03CoefficientIdentity01,
      row18_reducedY66_combinationStep03CoefficientIdentity02,
      row18_reducedY66_combinationStep03CoefficientIdentity03,
      row18_reducedY66_combinationStep03CoefficientIdentity04,
      row18_reducedY66_combinationStep03CoefficientIdentity05,
      row18_reducedY66_combinationStep03CoefficientIdentity06,
      row18_reducedY66_combinationStep03CoefficientIdentity07,
      row18_reducedY66_combinationStep03CoefficientIdentity08,
      row18_reducedY66_combinationStep03CoefficientIdentity09,
      row18_reducedY66_combinationStep03CoefficientIdentity10,
      row18_reducedY66_combinationStep03CoefficientIdentity11,
      row18_reducedY66_combinationStep03CoefficientIdentity12,
      row18_reducedY66_combinationStep03CoefficientIdentity13,
      row18_reducedY66_combinationStep03CoefficientIdentity14,
      row18_reducedY66_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY66_combinationStep03Multiplier * equation

private def row18_reducedY66_combinationStep04Multiplier : ℂ :=
  (((42 / 79) : ℂ) + ((80 / 79) : ℂ) * ζ ^ 1 + ((216 / 79) : ℂ) * ζ ^ 2 + ((36 / 79) : ℂ) * ζ ^ 3 - ((26 / 79) : ℂ) * ζ ^ 5 + ((204 / 79) : ℂ) * ζ ^ 6 - ((4 / 79) : ℂ) * ζ ^ 8 - ((152 / 79) : ℂ) * ζ ^ 9 - ((188 / 79) : ℂ) * ζ ^ 11 - ((4 / 79) : ℂ) * ζ ^ 12 - ((80 / 79) : ℂ) * ζ ^ 13 - ((142 / 79) : ℂ) * ζ ^ 15 - ((80 / 79) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((116 / 79) : ℂ) * ζ ^ 21 - ((216 / 79) : ℂ) * ζ ^ 22 + ((106 / 79) : ℂ) * ζ ^ 25 + ((116 / 79) : ℂ) * ζ ^ 27 + ((4 / 79) : ℂ) * ζ ^ 28 + ((80 / 79) : ℂ) * ζ ^ 29 + ((102 / 79) : ℂ) * ζ ^ 30 + ((188 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY66_combinationStep04Coefficient00 : ℂ :=
  (((180 / 79) : ℂ) - ((1728 / 395) : ℂ) * ζ ^ 1 + ((3977 / 395) : ℂ) * ζ ^ 2 + ((2419 / 790) : ℂ) * ζ ^ 3 + ((3287 / 790) : ℂ) * ζ ^ 5 + ((4568 / 395) : ℂ) * ζ ^ 6 + ((660 / 79) : ℂ) * ζ ^ 8 + ((8297 / 790) : ℂ) * ζ ^ 9 + ((2939 / 395) : ℂ) * ζ ^ 11 + ((660 / 79) : ℂ) * ζ ^ 12 + ((1728 / 395) : ℂ) * ζ ^ 13 + ((2162 / 395) : ℂ) * ζ ^ 15 + ((1728 / 395) : ℂ) * ζ ^ 17 - ((591 / 395) : ℂ) * ζ ^ 18 + ((1037 / 790) : ℂ) * ζ ^ 21 - ((3977 / 395) : ℂ) * ζ ^ 22 - ((6743 / 790) : ℂ) * ζ ^ 25 - ((1037 / 790) : ℂ) * ζ ^ 27 - ((660 / 79) : ℂ) * ζ ^ 28 - ((1728 / 395) : ℂ) * ζ ^ 29 + ((2284 / 395) : ℂ) * ζ ^ 30 - ((2939 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep04CoefficientIdentity00 :
    row18_reducedY66_combinationStep04Coefficient00 =
      row18_reducedY66_combinationStep03Coefficient00 +
        row18_reducedY66_combinationStep04Multiplier *
          (((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((73 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((105 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((73 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep04Coefficient00 row18_reducedY66_combinationStep03Coefficient00 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 (((3760 / 6241) : ℂ) + ((57 / 158) : ℂ) * ζ ^ 1 + ((852 / 6241) : ℂ) * ζ ^ 2 - ((7557 / 12482) : ℂ) * ζ ^ 3 - ((7563 / 6241) : ℂ) * ζ ^ 4 - ((7657 / 12482) : ℂ) * ζ ^ 5 - ((991 / 12482) : ℂ) * ζ ^ 6 + ((4428 / 6241) : ℂ) * ζ ^ 7 + ((4807 / 6241) : ℂ) * ζ ^ 8 - ((827 / 6241) : ℂ) * ζ ^ 9 - ((1856 / 6241) : ℂ) * ζ ^ 10 - ((5218 / 6241) : ℂ) * ζ ^ 11 - ((973 / 6241) : ℂ) * ζ ^ 12 + ((6075 / 12482) : ℂ) * ζ ^ 13 - ((786 / 6241) : ℂ) * ζ ^ 14 - ((413 / 12482) : ℂ) * ζ ^ 15 - ((5961 / 12482) : ℂ) * ζ ^ 16 - ((6632 / 6241) : ℂ) * ζ ^ 17 - ((724 / 6241) : ℂ) * ζ ^ 18 + ((113 / 6241) : ℂ) * ζ ^ 19 + ((5 / 6241) : ℂ) * ζ ^ 20 + ((3235 / 6241) : ℂ) * ζ ^ 21 - ((219 / 6241) : ℂ) * ζ ^ 22 - ((85 / 12482) : ℂ) * ζ ^ 23 + ((1190 / 6241) : ℂ) * ζ ^ 24 + ((795 / 12482) : ℂ) * ζ ^ 25 + ((2975 / 12482) : ℂ) * ζ ^ 26 + ((4519 / 12482) : ℂ) * ζ ^ 27 + ((1205 / 6241) : ℂ) * ζ ^ 28 + ((1109 / 6241) : ℂ) * ζ ^ 29 + ((658 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep04Coefficient01 : ℂ :=
  (-((33 / 158) : ℂ) + ((23 / 158) : ℂ) * ζ ^ 1 - ((7 / 158) : ℂ) * ζ ^ 2 - ((14 / 79) : ℂ) * ζ ^ 3 + ((23 / 158) : ℂ) * ζ ^ 5 - ((20 / 79) : ℂ) * ζ ^ 6 + ((20 / 79) : ℂ) * ζ ^ 8 - ((23 / 158) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((45 / 158) : ℂ) * ζ ^ 12 - ((23 / 158) : ℂ) * ζ ^ 13 - ((11 / 158) : ℂ) * ζ ^ 15 - ((23 / 158) : ℂ) * ζ ^ 17 + ((16 / 79) : ℂ) * ζ ^ 18 - ((29 / 79) : ℂ) * ζ ^ 21 + ((7 / 158) : ℂ) * ζ ^ 22 - ((4 / 79) : ℂ) * ζ ^ 24 - ((39 / 158) : ℂ) * ζ ^ 27 - ((20 / 79) : ℂ) * ζ ^ 28 + ((23 / 158) : ℂ) * ζ ^ 29 + ((5 / 158) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep04CoefficientIdentity01 :
    row18_reducedY66_combinationStep04Coefficient01 =
      row18_reducedY66_combinationStep03Coefficient01 +
        row18_reducedY66_combinationStep04Multiplier *
          (-((5 / 316) : ℂ) + ((3 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((33 / 158) : ℂ) * ζ ^ 3 + ((3 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 + ((10 / 79) : ℂ) * ζ ^ 8 - ((3 / 316) : ℂ) * ζ ^ 9 - ((33 / 316) : ℂ) * ζ ^ 11 - ((3 / 79) : ℂ) * ζ ^ 12 - ((3 / 316) : ℂ) * ζ ^ 13 - ((35 / 158) : ℂ) * ζ ^ 15 - ((3 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 - ((45 / 158) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((59 / 316) : ℂ) * ζ ^ 24 - ((1 / 79) : ℂ) * ζ ^ 27 - ((10 / 79) : ℂ) * ζ ^ 28 + ((3 / 316) : ℂ) * ζ ^ 29 - ((13 / 79) : ℂ) * ζ ^ 30 + ((33 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep04Coefficient01 row18_reducedY66_combinationStep03Coefficient01 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 (-((1356 / 6241) : ℂ) + ((840 / 6241) : ℂ) * ζ ^ 1 - ((854 / 6241) : ℂ) * ζ ^ 2 - ((996 / 6241) : ℂ) * ζ ^ 3 + ((813 / 6241) : ℂ) * ζ ^ 4 + ((6763 / 12482) : ℂ) * ζ ^ 5 - ((1533 / 12482) : ℂ) * ζ ^ 6 + ((1477 / 12482) : ℂ) * ζ ^ 7 - ((3155 / 6241) : ℂ) * ζ ^ 8 - ((657 / 12482) : ℂ) * ζ ^ 9 + ((2768 / 6241) : ℂ) * ζ ^ 10 + ((1578 / 6241) : ℂ) * ζ ^ 11 - ((3841 / 12482) : ℂ) * ζ ^ 12 - ((629 / 12482) : ℂ) * ζ ^ 13 - ((11537 / 12482) : ℂ) * ζ ^ 14 - ((1835 / 6241) : ℂ) * ζ ^ 15 - ((2885 / 12482) : ℂ) * ζ ^ 16 - ((173 / 12482) : ℂ) * ζ ^ 17 + ((1606 / 6241) : ℂ) * ζ ^ 18 + ((1089 / 12482) : ℂ) * ζ ^ 19 - ((3018 / 6241) : ℂ) * ζ ^ 20 - ((3145 / 12482) : ℂ) * ζ ^ 21 + ((253 / 6241) : ℂ) * ζ ^ 22 - ((5009 / 12482) : ℂ) * ζ ^ 23 + ((2733 / 12482) : ℂ) * ζ ^ 24 - ((1609 / 12482) : ℂ) * ζ ^ 25 - ((1794 / 6241) : ℂ) * ζ ^ 26 - ((5621 / 12482) : ℂ) * ζ ^ 27 - ((525 / 6241) : ℂ) * ζ ^ 28 - ((3205 / 12482) : ℂ) * ζ ^ 29 + ((1551 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep04Coefficient02 : ℂ :=
  (((188 / 79) : ℂ) - ((674 / 237) : ℂ) * ζ ^ 1 - ((193 / 474) : ℂ) * ζ ^ 2 + ((1621 / 474) : ℂ) * ζ ^ 3 - ((3473 / 237) : ℂ) * ζ ^ 5 + ((460 / 237) : ℂ) * ζ ^ 6 - ((985 / 237) : ℂ) * ζ ^ 8 - ((2125 / 474) : ℂ) * ζ ^ 9 - ((1173 / 79) : ℂ) * ζ ^ 11 - ((371 / 158) : ℂ) * ζ ^ 12 + ((674 / 237) : ℂ) * ζ ^ 13 - ((1621 / 474) : ℂ) * ζ ^ 15 + ((674 / 237) : ℂ) * ζ ^ 17 - ((935 / 474) : ℂ) * ζ ^ 18 + ((933 / 79) : ℂ) * ζ ^ 21 + ((193 / 474) : ℂ) * ζ ^ 22 + ((193 / 474) : ℂ) * ζ ^ 24 + ((933 / 79) : ℂ) * ζ ^ 25 + ((1173 / 79) : ℂ) * ζ ^ 27 + ((985 / 237) : ℂ) * ζ ^ 28 - ((674 / 237) : ℂ) * ζ ^ 29 + ((1777 / 474) : ℂ) * ζ ^ 30 + ((1173 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep04CoefficientIdentity02 :
    row18_reducedY66_combinationStep04Coefficient02 =
      row18_reducedY66_combinationStep03Coefficient02 +
        row18_reducedY66_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep04Coefficient02 row18_reducedY66_combinationStep03Coefficient02 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep04Coefficient03 : ℂ :=
  (-((245 / 79) : ℂ) - ((61 / 237) : ℂ) * ζ ^ 1 + ((113 / 474) : ℂ) * ζ ^ 2 + ((1231 / 474) : ℂ) * ζ ^ 3 - ((179 / 237) : ℂ) * ζ ^ 5 - ((41 / 237) : ℂ) * ζ ^ 6 + ((76 / 79) : ℂ) * ζ ^ 8 + ((194 / 237) : ℂ) * ζ ^ 9 - ((281 / 158) : ℂ) * ζ ^ 11 + ((76 / 79) : ℂ) * ζ ^ 12 + ((61 / 237) : ℂ) * ζ ^ 13 - ((489 / 158) : ℂ) * ζ ^ 15 + ((61 / 237) : ℂ) * ζ ^ 17 + ((65 / 158) : ℂ) * ζ ^ 18 - ((1109 / 474) : ℂ) * ζ ^ 21 - ((113 / 474) : ℂ) * ζ ^ 22 + ((118 / 237) : ℂ) * ζ ^ 25 + ((1109 / 474) : ℂ) * ζ ^ 27 - ((76 / 79) : ℂ) * ζ ^ 28 - ((61 / 237) : ℂ) * ζ ^ 29 - ((41 / 474) : ℂ) * ζ ^ 30 + ((281 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep04CoefficientIdentity03 :
    row18_reducedY66_combinationStep04Coefficient03 =
      row18_reducedY66_combinationStep03Coefficient03 +
        row18_reducedY66_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep04Coefficient03 row18_reducedY66_combinationStep03Coefficient03 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep04Coefficient04 : ℂ :=
  (-((125 / 158) : ℂ) + ((1218 / 395) : ℂ) * ζ ^ 1 - ((2852 / 395) : ℂ) * ζ ^ 2 - ((3421 / 1185) : ℂ) * ζ ^ 3 - ((3087 / 790) : ℂ) * ζ ^ 5 - ((10714 / 1185) : ℂ) * ζ ^ 6 - ((3113 / 474) : ℂ) * ζ ^ 8 - ((7447 / 790) : ℂ) * ζ ^ 9 - ((15499 / 2370) : ℂ) * ζ ^ 11 - ((3113 / 474) : ℂ) * ζ ^ 12 - ((1218 / 395) : ℂ) * ζ ^ 13 - ((9727 / 2370) : ℂ) * ζ ^ 15 - ((1218 / 395) : ℂ) * ζ ^ 17 + ((2158 / 1185) : ℂ) * ζ ^ 18 - ((233 / 1185) : ℂ) * ζ ^ 21 + ((2852 / 395) : ℂ) * ζ ^ 22 + ((5523 / 790) : ℂ) * ζ ^ 25 + ((233 / 1185) : ℂ) * ζ ^ 27 + ((3113 / 474) : ℂ) * ζ ^ 28 + ((1218 / 395) : ℂ) * ζ ^ 29 - ((5357 / 1185) : ℂ) * ζ ^ 30 + ((15499 / 2370) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep04CoefficientIdentity04 :
    row18_reducedY66_combinationStep04Coefficient04 =
      row18_reducedY66_combinationStep03Coefficient04 +
        row18_reducedY66_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep04Coefficient04 row18_reducedY66_combinationStep03Coefficient04 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep04Coefficient05 : ℂ :=
  (-((177 / 158) : ℂ) + ((827 / 474) : ℂ) * ζ ^ 1 - ((580 / 79) : ℂ) * ζ ^ 2 - ((2573 / 474) : ℂ) * ζ ^ 5 - ((983 / 158) : ℂ) * ζ ^ 6 - ((983 / 158) : ℂ) * ζ ^ 8 - ((2573 / 474) : ℂ) * ζ ^ 9 - ((1847 / 237) : ℂ) * ζ ^ 11 - ((1085 / 237) : ℂ) * ζ ^ 12 - ((827 / 474) : ℂ) * ζ ^ 13 - ((2135 / 474) : ℂ) * ζ ^ 15 - ((827 / 474) : ℂ) * ζ ^ 17 + ((1541 / 474) : ℂ) * ζ ^ 18 + ((291 / 158) : ℂ) * ζ ^ 21 + ((580 / 79) : ℂ) * ζ ^ 22 + ((704 / 237) : ℂ) * ζ ^ 24 + ((1700 / 237) : ℂ) * ζ ^ 25 + ((2135 / 474) : ℂ) * ζ ^ 27 + ((983 / 158) : ℂ) * ζ ^ 28 + ((827 / 474) : ℂ) * ζ ^ 29 - ((779 / 474) : ℂ) * ζ ^ 30 + ((1847 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep04CoefficientIdentity05 :
    row18_reducedY66_combinationStep04Coefficient05 =
      row18_reducedY66_combinationStep03Coefficient05 +
        row18_reducedY66_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep04Coefficient05 row18_reducedY66_combinationStep03Coefficient05 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep04Coefficient06 : ℂ :=
  (-((577 / 237) : ℂ) - ((695 / 474) : ℂ) * ζ ^ 1 - ((1007 / 237) : ℂ) * ζ ^ 2 - ((1336 / 395) : ℂ) * ζ ^ 3 - ((3 / 79) : ℂ) * ζ ^ 6 - ((124 / 79) : ℂ) * ζ ^ 8 - ((713 / 158) : ℂ) * ζ ^ 9 + ((6353 / 2370) : ℂ) * ζ ^ 11 + ((998 / 237) : ℂ) * ζ ^ 12 + ((695 / 474) : ℂ) * ζ ^ 13 - ((1336 / 395) : ℂ) * ζ ^ 15 + ((695 / 474) : ℂ) * ζ ^ 17 + ((430 / 237) : ℂ) * ζ ^ 18 + ((695 / 474) : ℂ) * ζ ^ 21 + ((1007 / 237) : ℂ) * ζ ^ 22 - ((1007 / 237) : ℂ) * ζ ^ 24 - ((695 / 474) : ℂ) * ζ ^ 25 + ((6353 / 2370) : ℂ) * ζ ^ 27 + ((124 / 79) : ℂ) * ζ ^ 28 - ((695 / 474) : ℂ) * ζ ^ 29 - ((1379 / 237) : ℂ) * ζ ^ 30 - ((6353 / 2370) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep04CoefficientIdentity06 :
    row18_reducedY66_combinationStep04Coefficient06 =
      row18_reducedY66_combinationStep03Coefficient06 +
        row18_reducedY66_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep04Coefficient06 row18_reducedY66_combinationStep03Coefficient06 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep04Coefficient07 : ℂ :=
  (((163 / 158) : ℂ) + ((295 / 237) : ℂ) * ζ ^ 1 - ((760 / 237) : ℂ) * ζ ^ 2 - ((361 / 158) : ℂ) * ζ ^ 3 + ((295 / 474) : ℂ) * ζ ^ 5 - ((551 / 237) : ℂ) * ζ ^ 6 - ((644 / 237) : ℂ) * ζ ^ 8 - ((613 / 474) : ℂ) * ζ ^ 9 + ((235 / 237) : ℂ) * ζ ^ 11 - ((644 / 237) : ℂ) * ζ ^ 12 - ((295 / 237) : ℂ) * ζ ^ 13 + ((394 / 237) : ℂ) * ζ ^ 15 - ((295 / 237) : ℂ) * ζ ^ 17 - ((209 / 237) : ℂ) * ζ ^ 18 + ((493 / 474) : ℂ) * ζ ^ 21 + ((760 / 237) : ℂ) * ζ ^ 22 + ((295 / 474) : ℂ) * ζ ^ 25 - ((493 / 474) : ℂ) * ζ ^ 27 + ((644 / 237) : ℂ) * ζ ^ 28 + ((295 / 237) : ℂ) * ζ ^ 29 - ((551 / 474) : ℂ) * ζ ^ 30 - ((235 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep04CoefficientIdentity07 :
    row18_reducedY66_combinationStep04Coefficient07 =
      row18_reducedY66_combinationStep03Coefficient07 +
        row18_reducedY66_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep04Coefficient07 row18_reducedY66_combinationStep03Coefficient07 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep04Coefficient08 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep04CoefficientIdentity08 :
    row18_reducedY66_combinationStep04Coefficient08 =
      row18_reducedY66_combinationStep03Coefficient08 +
        row18_reducedY66_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep04Coefficient08 row18_reducedY66_combinationStep03Coefficient08 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep04Coefficient09 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep04CoefficientIdentity09 :
    row18_reducedY66_combinationStep04Coefficient09 =
      row18_reducedY66_combinationStep03Coefficient09 +
        row18_reducedY66_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep04Coefficient09 row18_reducedY66_combinationStep03Coefficient09 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep04Coefficient10 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep04CoefficientIdentity10 :
    row18_reducedY66_combinationStep04Coefficient10 =
      row18_reducedY66_combinationStep03Coefficient10 +
        row18_reducedY66_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep04Coefficient10 row18_reducedY66_combinationStep03Coefficient10 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep04Coefficient11 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep04CoefficientIdentity11 :
    row18_reducedY66_combinationStep04Coefficient11 =
      row18_reducedY66_combinationStep03Coefficient11 +
        row18_reducedY66_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep04Coefficient11 row18_reducedY66_combinationStep03Coefficient11 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep04Coefficient12 : ℂ :=
  (((46 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep04CoefficientIdentity12 :
    row18_reducedY66_combinationStep04Coefficient12 =
      row18_reducedY66_combinationStep03Coefficient12 +
        row18_reducedY66_combinationStep04Multiplier *
          (-((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((73 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((105 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((73 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep04Coefficient12 row18_reducedY66_combinationStep03Coefficient12 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 (-((3760 / 6241) : ℂ) - ((57 / 158) : ℂ) * ζ ^ 1 - ((852 / 6241) : ℂ) * ζ ^ 2 + ((7557 / 12482) : ℂ) * ζ ^ 3 + ((7563 / 6241) : ℂ) * ζ ^ 4 + ((7657 / 12482) : ℂ) * ζ ^ 5 + ((991 / 12482) : ℂ) * ζ ^ 6 - ((4428 / 6241) : ℂ) * ζ ^ 7 - ((4807 / 6241) : ℂ) * ζ ^ 8 + ((827 / 6241) : ℂ) * ζ ^ 9 + ((1856 / 6241) : ℂ) * ζ ^ 10 + ((5218 / 6241) : ℂ) * ζ ^ 11 + ((973 / 6241) : ℂ) * ζ ^ 12 - ((6075 / 12482) : ℂ) * ζ ^ 13 + ((786 / 6241) : ℂ) * ζ ^ 14 + ((413 / 12482) : ℂ) * ζ ^ 15 + ((5961 / 12482) : ℂ) * ζ ^ 16 + ((6632 / 6241) : ℂ) * ζ ^ 17 + ((724 / 6241) : ℂ) * ζ ^ 18 - ((113 / 6241) : ℂ) * ζ ^ 19 - ((5 / 6241) : ℂ) * ζ ^ 20 - ((3235 / 6241) : ℂ) * ζ ^ 21 + ((219 / 6241) : ℂ) * ζ ^ 22 + ((85 / 12482) : ℂ) * ζ ^ 23 - ((1190 / 6241) : ℂ) * ζ ^ 24 - ((795 / 12482) : ℂ) * ζ ^ 25 - ((2975 / 12482) : ℂ) * ζ ^ 26 - ((4519 / 12482) : ℂ) * ζ ^ 27 - ((1205 / 6241) : ℂ) * ζ ^ 28 - ((1109 / 6241) : ℂ) * ζ ^ 29 - ((658 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep04Coefficient13 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep04CoefficientIdentity13 :
    row18_reducedY66_combinationStep04Coefficient13 =
      row18_reducedY66_combinationStep03Coefficient13 +
        row18_reducedY66_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep04Coefficient13 row18_reducedY66_combinationStep03Coefficient13 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep04Coefficient14 : ℂ :=
  (-((9 / 79) : ℂ) + ((2 / 79) : ℂ) * ζ ^ 1 - ((33 / 79) : ℂ) * ζ ^ 2 - ((33 / 79) : ℂ) * ζ ^ 6 + ((9 / 79) : ℂ) * ζ ^ 8 + ((19 / 79) : ℂ) * ζ ^ 9 - ((2 / 79) : ℂ) * ζ ^ 13 - ((2 / 79) : ℂ) * ζ ^ 17 + ((24 / 79) : ℂ) * ζ ^ 18 - ((2 / 79) : ℂ) * ζ ^ 21 + ((33 / 79) : ℂ) * ζ ^ 22 - ((33 / 79) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 25 - ((9 / 79) : ℂ) * ζ ^ 28 + ((2 / 79) : ℂ) * ζ ^ 29 - ((24 / 79) : ℂ) * ζ ^ 30)

private theorem row18_reducedY66_combinationStep04CoefficientIdentity14 :
    row18_reducedY66_combinationStep04Coefficient14 =
      row18_reducedY66_combinationStep03Coefficient14 +
        row18_reducedY66_combinationStep04Multiplier *
          (((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep04Coefficient14 row18_reducedY66_combinationStep03Coefficient14 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 (((1110 / 6241) : ℂ) + ((1477 / 12482) : ℂ) * ζ ^ 1 + ((10069 / 12482) : ℂ) * ζ ^ 2 + ((1516 / 6241) : ℂ) * ζ ^ 3 + ((81 / 6241) : ℂ) * ζ ^ 4 + ((819 / 12482) : ℂ) * ζ ^ 5 - ((1 / 6241) : ℂ) * ζ ^ 6 - ((489 / 12482) : ℂ) * ζ ^ 7 + ((1583 / 12482) : ℂ) * ζ ^ 8 - ((4271 / 12482) : ℂ) * ζ ^ 9 - ((2010 / 6241) : ℂ) * ζ ^ 10 + ((1643 / 6241) : ℂ) * ζ ^ 11 + ((1189 / 6241) : ℂ) * ζ ^ 12 + ((1639 / 6241) : ℂ) * ζ ^ 13 + ((5807 / 12482) : ℂ) * ζ ^ 14 + ((1029 / 6241) : ℂ) * ζ ^ 15 - ((420 / 6241) : ℂ) * ζ ^ 16 - ((1357 / 12482) : ℂ) * ζ ^ 17 - ((2493 / 6241) : ℂ) * ζ ^ 18 + ((2689 / 12482) : ℂ) * ζ ^ 19 - ((403 / 12482) : ℂ) * ζ ^ 20 - ((1645 / 12482) : ℂ) * ζ ^ 21 - ((583 / 12482) : ℂ) * ζ ^ 22 - ((887 / 6241) : ℂ) * ζ ^ 23 + ((2915 / 12482) : ℂ) * ζ ^ 24 + ((1292 / 6241) : ℂ) * ζ ^ 25 + ((1483 / 12482) : ℂ) * ζ ^ 26 + ((4319 / 12482) : ℂ) * ζ ^ 27 - ((313 / 6241) : ℂ) * ζ ^ 28 - ((3747 / 12482) : ℂ) * ζ ^ 29 + ((705 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep04Coefficient15 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep04CoefficientIdentity15 :
    row18_reducedY66_combinationStep04Coefficient15 =
      row18_reducedY66_combinationStep03Coefficient15 +
        row18_reducedY66_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep04Coefficient15 row18_reducedY66_combinationStep03Coefficient15 row18_reducedY66_combinationStep04Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY66_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY66_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY66_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY66_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY66_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY66_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY66_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY66_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY66_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY66_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY66_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY66_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY66_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY66_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY66_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY66_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY66_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY66_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation06
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY66_combinationStep04CoefficientIdentity00,
      row18_reducedY66_combinationStep04CoefficientIdentity01,
      row18_reducedY66_combinationStep04CoefficientIdentity02,
      row18_reducedY66_combinationStep04CoefficientIdentity03,
      row18_reducedY66_combinationStep04CoefficientIdentity04,
      row18_reducedY66_combinationStep04CoefficientIdentity05,
      row18_reducedY66_combinationStep04CoefficientIdentity06,
      row18_reducedY66_combinationStep04CoefficientIdentity07,
      row18_reducedY66_combinationStep04CoefficientIdentity08,
      row18_reducedY66_combinationStep04CoefficientIdentity09,
      row18_reducedY66_combinationStep04CoefficientIdentity10,
      row18_reducedY66_combinationStep04CoefficientIdentity11,
      row18_reducedY66_combinationStep04CoefficientIdentity12,
      row18_reducedY66_combinationStep04CoefficientIdentity13,
      row18_reducedY66_combinationStep04CoefficientIdentity14,
      row18_reducedY66_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY66_combinationStep04Multiplier * equation

private def row18_reducedY66_combinationStep05Multiplier : ℂ :=
  (-((14 / 79) : ℂ) - ((120 / 79) : ℂ) * ζ ^ 1 - ((218 / 79) : ℂ) * ζ ^ 2 + ((52 / 79) : ℂ) * ζ ^ 5 - ((204 / 79) : ℂ) * ζ ^ 6 - ((204 / 79) : ℂ) * ζ ^ 8 + ((52 / 79) : ℂ) * ζ ^ 9 + ((94 / 79) : ℂ) * ζ ^ 11 - ((2 / 79) : ℂ) * ζ ^ 12 + ((120 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 + ((120 / 79) : ℂ) * ζ ^ 17 + ((148 / 79) : ℂ) * ζ ^ 18 + ((34 / 79) : ℂ) * ζ ^ 21 + ((218 / 79) : ℂ) * ζ ^ 22 + ((56 / 79) : ℂ) * ζ ^ 24 - ((172 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((204 / 79) : ℂ) * ζ ^ 28 - ((120 / 79) : ℂ) * ζ ^ 29 - ((202 / 79) : ℂ) * ζ ^ 30 - ((94 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY66_combinationStep05Coefficient00 : ℂ :=
  (((213 / 79) : ℂ) - ((1848 / 395) : ℂ) * ζ ^ 1 + ((7859 / 790) : ℂ) * ζ ^ 2 + ((1402 / 395) : ℂ) * ζ ^ 3 + ((1691 / 395) : ℂ) * ζ ^ 5 + ((4578 / 395) : ℂ) * ζ ^ 6 + ((1325 / 158) : ℂ) * ζ ^ 8 + ((4386 / 395) : ℂ) * ζ ^ 9 + ((2984 / 395) : ℂ) * ζ ^ 11 + ((1325 / 158) : ℂ) * ζ ^ 12 + ((1848 / 395) : ℂ) * ζ ^ 13 + ((2137 / 395) : ℂ) * ζ ^ 15 + ((1848 / 395) : ℂ) * ζ ^ 17 - ((1297 / 790) : ℂ) * ζ ^ 18 + ((446 / 395) : ℂ) * ζ ^ 21 - ((7859 / 790) : ℂ) * ζ ^ 22 - ((3539 / 395) : ℂ) * ζ ^ 25 - ((446 / 395) : ℂ) * ζ ^ 27 - ((1325 / 158) : ℂ) * ζ ^ 28 - ((1848 / 395) : ℂ) * ζ ^ 29 + ((2289 / 395) : ℂ) * ζ ^ 30 - ((2984 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep05CoefficientIdentity00 :
    row18_reducedY66_combinationStep05Coefficient00 =
      row18_reducedY66_combinationStep04Coefficient00 +
        row18_reducedY66_combinationStep05Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep05Coefficient00 row18_reducedY66_combinationStep04Coefficient00 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 (-((2474 / 6241) : ℂ) + ((6163 / 12482) : ℂ) * ζ ^ 1 + ((3250 / 6241) : ℂ) * ζ ^ 2 - ((1919 / 6241) : ℂ) * ζ ^ 3 + ((7587 / 12482) : ℂ) * ζ ^ 4 - ((3018 / 6241) : ℂ) * ζ ^ 5 - ((1520 / 6241) : ℂ) * ζ ^ 6 + ((3459 / 6241) : ℂ) * ζ ^ 7 - ((315 / 12482) : ℂ) * ζ ^ 8 - ((1635 / 12482) : ℂ) * ζ ^ 9 + ((2433 / 12482) : ℂ) * ζ ^ 10 + ((203 / 12482) : ℂ) * ζ ^ 11 - ((1748 / 6241) : ℂ) * ζ ^ 12 + ((1205 / 6241) : ℂ) * ζ ^ 13 - ((837 / 12482) : ℂ) * ζ ^ 14 + ((894 / 6241) : ℂ) * ζ ^ 15 + ((247 / 12482) : ℂ) * ζ ^ 16 + ((163 / 6241) : ℂ) * ζ ^ 17 + ((1985 / 12482) : ℂ) * ζ ^ 18 - ((1125 / 6241) : ℂ) * ζ ^ 19 + ((871 / 12482) : ℂ) * ζ ^ 20 + ((706 / 6241) : ℂ) * ζ ^ 21 - ((3236 / 6241) : ℂ) * ζ ^ 22 + ((2 / 79) : ℂ) * ζ ^ 23 - ((710 / 6241) : ℂ) * ζ ^ 24 + ((240 / 6241) : ℂ) * ζ ^ 25 + ((10525 / 12482) : ℂ) * ζ ^ 26 - ((162 / 6241) : ℂ) * ζ ^ 27 - ((3337 / 12482) : ℂ) * ζ ^ 28 - ((741 / 12482) : ℂ) * ζ ^ 29 + ((705 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep05Coefficient01 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep05CoefficientIdentity01 :
    row18_reducedY66_combinationStep05Coefficient01 =
      row18_reducedY66_combinationStep04Coefficient01 +
        row18_reducedY66_combinationStep05Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep05Coefficient01 row18_reducedY66_combinationStep04Coefficient01 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 (-((2719 / 12482) : ℂ) + ((390 / 6241) : ℂ) * ζ ^ 1 - ((1601 / 6241) : ℂ) * ζ ^ 2 - ((2752 / 6241) : ℂ) * ζ ^ 3 - ((518 / 6241) : ℂ) * ζ ^ 4 + ((676 / 6241) : ℂ) * ζ ^ 5 - ((1552 / 6241) : ℂ) * ζ ^ 6 + ((1011 / 6241) : ℂ) * ζ ^ 7 - ((495 / 6241) : ℂ) * ζ ^ 8 - ((1661 / 6241) : ℂ) * ζ ^ 9 + ((1017 / 6241) : ℂ) * ζ ^ 10 - ((893 / 12482) : ℂ) * ζ ^ 11 + ((1643 / 12482) : ℂ) * ζ ^ 12 + ((887 / 6241) : ℂ) * ζ ^ 13 - ((55 / 6241) : ℂ) * ζ ^ 14 - ((204 / 6241) : ℂ) * ζ ^ 15 - ((886 / 6241) : ℂ) * ζ ^ 16 + ((638 / 6241) : ℂ) * ζ ^ 17 + ((2889 / 12482) : ℂ) * ζ ^ 18 + ((2551 / 12482) : ℂ) * ζ ^ 19 + ((5915 / 12482) : ℂ) * ζ ^ 20 - ((4831 / 12482) : ℂ) * ζ ^ 21 - ((1303 / 6241) : ℂ) * ζ ^ 22 + ((594 / 6241) : ℂ) * ζ ^ 23 + ((2049 / 6241) : ℂ) * ζ ^ 24 + ((442 / 6241) : ℂ) * ζ ^ 25 + ((72 / 6241) : ℂ) * ζ ^ 26 - ((3541 / 12482) : ℂ) * ζ ^ 27 - ((889 / 12482) : ℂ) * ζ ^ 28 + ((425 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep05Coefficient02 : ℂ :=
  (((188 / 79) : ℂ) - ((674 / 237) : ℂ) * ζ ^ 1 - ((193 / 474) : ℂ) * ζ ^ 2 + ((1621 / 474) : ℂ) * ζ ^ 3 - ((3473 / 237) : ℂ) * ζ ^ 5 + ((460 / 237) : ℂ) * ζ ^ 6 - ((985 / 237) : ℂ) * ζ ^ 8 - ((2125 / 474) : ℂ) * ζ ^ 9 - ((1173 / 79) : ℂ) * ζ ^ 11 - ((371 / 158) : ℂ) * ζ ^ 12 + ((674 / 237) : ℂ) * ζ ^ 13 - ((1621 / 474) : ℂ) * ζ ^ 15 + ((674 / 237) : ℂ) * ζ ^ 17 - ((935 / 474) : ℂ) * ζ ^ 18 + ((933 / 79) : ℂ) * ζ ^ 21 + ((193 / 474) : ℂ) * ζ ^ 22 + ((193 / 474) : ℂ) * ζ ^ 24 + ((933 / 79) : ℂ) * ζ ^ 25 + ((1173 / 79) : ℂ) * ζ ^ 27 + ((985 / 237) : ℂ) * ζ ^ 28 - ((674 / 237) : ℂ) * ζ ^ 29 + ((1777 / 474) : ℂ) * ζ ^ 30 + ((1173 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep05CoefficientIdentity02 :
    row18_reducedY66_combinationStep05Coefficient02 =
      row18_reducedY66_combinationStep04Coefficient02 +
        row18_reducedY66_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep05Coefficient02 row18_reducedY66_combinationStep04Coefficient02 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep05Coefficient03 : ℂ :=
  (-((245 / 79) : ℂ) - ((61 / 237) : ℂ) * ζ ^ 1 + ((113 / 474) : ℂ) * ζ ^ 2 + ((1231 / 474) : ℂ) * ζ ^ 3 - ((179 / 237) : ℂ) * ζ ^ 5 - ((41 / 237) : ℂ) * ζ ^ 6 + ((76 / 79) : ℂ) * ζ ^ 8 + ((194 / 237) : ℂ) * ζ ^ 9 - ((281 / 158) : ℂ) * ζ ^ 11 + ((76 / 79) : ℂ) * ζ ^ 12 + ((61 / 237) : ℂ) * ζ ^ 13 - ((489 / 158) : ℂ) * ζ ^ 15 + ((61 / 237) : ℂ) * ζ ^ 17 + ((65 / 158) : ℂ) * ζ ^ 18 - ((1109 / 474) : ℂ) * ζ ^ 21 - ((113 / 474) : ℂ) * ζ ^ 22 + ((118 / 237) : ℂ) * ζ ^ 25 + ((1109 / 474) : ℂ) * ζ ^ 27 - ((76 / 79) : ℂ) * ζ ^ 28 - ((61 / 237) : ℂ) * ζ ^ 29 - ((41 / 474) : ℂ) * ζ ^ 30 + ((281 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep05CoefficientIdentity03 :
    row18_reducedY66_combinationStep05Coefficient03 =
      row18_reducedY66_combinationStep04Coefficient03 +
        row18_reducedY66_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep05Coefficient03 row18_reducedY66_combinationStep04Coefficient03 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep05Coefficient04 : ℂ :=
  (-((125 / 158) : ℂ) + ((1218 / 395) : ℂ) * ζ ^ 1 - ((2852 / 395) : ℂ) * ζ ^ 2 - ((3421 / 1185) : ℂ) * ζ ^ 3 - ((3087 / 790) : ℂ) * ζ ^ 5 - ((10714 / 1185) : ℂ) * ζ ^ 6 - ((3113 / 474) : ℂ) * ζ ^ 8 - ((7447 / 790) : ℂ) * ζ ^ 9 - ((15499 / 2370) : ℂ) * ζ ^ 11 - ((3113 / 474) : ℂ) * ζ ^ 12 - ((1218 / 395) : ℂ) * ζ ^ 13 - ((9727 / 2370) : ℂ) * ζ ^ 15 - ((1218 / 395) : ℂ) * ζ ^ 17 + ((2158 / 1185) : ℂ) * ζ ^ 18 - ((233 / 1185) : ℂ) * ζ ^ 21 + ((2852 / 395) : ℂ) * ζ ^ 22 + ((5523 / 790) : ℂ) * ζ ^ 25 + ((233 / 1185) : ℂ) * ζ ^ 27 + ((3113 / 474) : ℂ) * ζ ^ 28 + ((1218 / 395) : ℂ) * ζ ^ 29 - ((5357 / 1185) : ℂ) * ζ ^ 30 + ((15499 / 2370) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep05CoefficientIdentity04 :
    row18_reducedY66_combinationStep05Coefficient04 =
      row18_reducedY66_combinationStep04Coefficient04 +
        row18_reducedY66_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep05Coefficient04 row18_reducedY66_combinationStep04Coefficient04 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep05Coefficient05 : ℂ :=
  (-((177 / 158) : ℂ) + ((827 / 474) : ℂ) * ζ ^ 1 - ((580 / 79) : ℂ) * ζ ^ 2 - ((2573 / 474) : ℂ) * ζ ^ 5 - ((983 / 158) : ℂ) * ζ ^ 6 - ((983 / 158) : ℂ) * ζ ^ 8 - ((2573 / 474) : ℂ) * ζ ^ 9 - ((1847 / 237) : ℂ) * ζ ^ 11 - ((1085 / 237) : ℂ) * ζ ^ 12 - ((827 / 474) : ℂ) * ζ ^ 13 - ((2135 / 474) : ℂ) * ζ ^ 15 - ((827 / 474) : ℂ) * ζ ^ 17 + ((1541 / 474) : ℂ) * ζ ^ 18 + ((291 / 158) : ℂ) * ζ ^ 21 + ((580 / 79) : ℂ) * ζ ^ 22 + ((704 / 237) : ℂ) * ζ ^ 24 + ((1700 / 237) : ℂ) * ζ ^ 25 + ((2135 / 474) : ℂ) * ζ ^ 27 + ((983 / 158) : ℂ) * ζ ^ 28 + ((827 / 474) : ℂ) * ζ ^ 29 - ((779 / 474) : ℂ) * ζ ^ 30 + ((1847 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep05CoefficientIdentity05 :
    row18_reducedY66_combinationStep05Coefficient05 =
      row18_reducedY66_combinationStep04Coefficient05 +
        row18_reducedY66_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep05Coefficient05 row18_reducedY66_combinationStep04Coefficient05 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep05Coefficient06 : ℂ :=
  (-((577 / 237) : ℂ) - ((695 / 474) : ℂ) * ζ ^ 1 - ((1007 / 237) : ℂ) * ζ ^ 2 - ((1336 / 395) : ℂ) * ζ ^ 3 - ((3 / 79) : ℂ) * ζ ^ 6 - ((124 / 79) : ℂ) * ζ ^ 8 - ((713 / 158) : ℂ) * ζ ^ 9 + ((6353 / 2370) : ℂ) * ζ ^ 11 + ((998 / 237) : ℂ) * ζ ^ 12 + ((695 / 474) : ℂ) * ζ ^ 13 - ((1336 / 395) : ℂ) * ζ ^ 15 + ((695 / 474) : ℂ) * ζ ^ 17 + ((430 / 237) : ℂ) * ζ ^ 18 + ((695 / 474) : ℂ) * ζ ^ 21 + ((1007 / 237) : ℂ) * ζ ^ 22 - ((1007 / 237) : ℂ) * ζ ^ 24 - ((695 / 474) : ℂ) * ζ ^ 25 + ((6353 / 2370) : ℂ) * ζ ^ 27 + ((124 / 79) : ℂ) * ζ ^ 28 - ((695 / 474) : ℂ) * ζ ^ 29 - ((1379 / 237) : ℂ) * ζ ^ 30 - ((6353 / 2370) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep05CoefficientIdentity06 :
    row18_reducedY66_combinationStep05Coefficient06 =
      row18_reducedY66_combinationStep04Coefficient06 +
        row18_reducedY66_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep05Coefficient06 row18_reducedY66_combinationStep04Coefficient06 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep05Coefficient07 : ℂ :=
  (((163 / 158) : ℂ) + ((295 / 237) : ℂ) * ζ ^ 1 - ((760 / 237) : ℂ) * ζ ^ 2 - ((361 / 158) : ℂ) * ζ ^ 3 + ((295 / 474) : ℂ) * ζ ^ 5 - ((551 / 237) : ℂ) * ζ ^ 6 - ((644 / 237) : ℂ) * ζ ^ 8 - ((613 / 474) : ℂ) * ζ ^ 9 + ((235 / 237) : ℂ) * ζ ^ 11 - ((644 / 237) : ℂ) * ζ ^ 12 - ((295 / 237) : ℂ) * ζ ^ 13 + ((394 / 237) : ℂ) * ζ ^ 15 - ((295 / 237) : ℂ) * ζ ^ 17 - ((209 / 237) : ℂ) * ζ ^ 18 + ((493 / 474) : ℂ) * ζ ^ 21 + ((760 / 237) : ℂ) * ζ ^ 22 + ((295 / 474) : ℂ) * ζ ^ 25 - ((493 / 474) : ℂ) * ζ ^ 27 + ((644 / 237) : ℂ) * ζ ^ 28 + ((295 / 237) : ℂ) * ζ ^ 29 - ((551 / 474) : ℂ) * ζ ^ 30 - ((235 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep05CoefficientIdentity07 :
    row18_reducedY66_combinationStep05Coefficient07 =
      row18_reducedY66_combinationStep04Coefficient07 +
        row18_reducedY66_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep05Coefficient07 row18_reducedY66_combinationStep04Coefficient07 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep05Coefficient08 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep05CoefficientIdentity08 :
    row18_reducedY66_combinationStep05Coefficient08 =
      row18_reducedY66_combinationStep04Coefficient08 +
        row18_reducedY66_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep05Coefficient08 row18_reducedY66_combinationStep04Coefficient08 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep05Coefficient09 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep05CoefficientIdentity09 :
    row18_reducedY66_combinationStep05Coefficient09 =
      row18_reducedY66_combinationStep04Coefficient09 +
        row18_reducedY66_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep05Coefficient09 row18_reducedY66_combinationStep04Coefficient09 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep05Coefficient10 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep05CoefficientIdentity10 :
    row18_reducedY66_combinationStep05Coefficient10 =
      row18_reducedY66_combinationStep04Coefficient10 +
        row18_reducedY66_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep05Coefficient10 row18_reducedY66_combinationStep04Coefficient10 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep05Coefficient11 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep05CoefficientIdentity11 :
    row18_reducedY66_combinationStep05Coefficient11 =
      row18_reducedY66_combinationStep04Coefficient11 +
        row18_reducedY66_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep05Coefficient11 row18_reducedY66_combinationStep04Coefficient11 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep05Coefficient12 : ℂ :=
  (((46 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep05CoefficientIdentity12 :
    row18_reducedY66_combinationStep05Coefficient12 =
      row18_reducedY66_combinationStep04Coefficient12 +
        row18_reducedY66_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep05Coefficient12 row18_reducedY66_combinationStep04Coefficient12 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep05Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep05CoefficientIdentity13 :
    row18_reducedY66_combinationStep05Coefficient13 =
      row18_reducedY66_combinationStep04Coefficient13 +
        row18_reducedY66_combinationStep05Multiplier *
          (-((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((73 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((105 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((73 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep05Coefficient13 row18_reducedY66_combinationStep04Coefficient13 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 (-((3276 / 6241) : ℂ) - ((625 / 12482) : ℂ) * ζ ^ 1 + ((689 / 6241) : ℂ) * ζ ^ 2 - ((3167 / 12482) : ℂ) * ζ ^ 3 - ((1285 / 12482) : ℂ) * ζ ^ 4 - ((117 / 6241) : ℂ) * ζ ^ 5 + ((5201 / 12482) : ℂ) * ζ ^ 6 + ((3018 / 6241) : ℂ) * ζ ^ 7 + ((4811 / 12482) : ℂ) * ζ ^ 8 - ((784 / 6241) : ℂ) * ζ ^ 9 - ((8487 / 6241) : ℂ) * ζ ^ 10 - ((4803 / 12482) : ℂ) * ζ ^ 11 + ((6691 / 12482) : ℂ) * ζ ^ 12 + ((178 / 6241) : ℂ) * ζ ^ 13 + ((6775 / 6241) : ℂ) * ζ ^ 14 - ((4021 / 12482) : ℂ) * ζ ^ 15 - ((19101 / 12482) : ℂ) * ζ ^ 16 - ((4973 / 12482) : ℂ) * ζ ^ 17 - ((4376 / 6241) : ℂ) * ζ ^ 18 + ((66 / 6241) : ℂ) * ζ ^ 19 + ((8447 / 12482) : ℂ) * ζ ^ 20 + ((551 / 6241) : ℂ) * ζ ^ 21 - ((119 / 6241) : ℂ) * ζ ^ 22 + ((550 / 6241) : ℂ) * ζ ^ 23 - ((2929 / 12482) : ℂ) * ζ ^ 24 + ((445 / 12482) : ℂ) * ζ ^ 25 + ((1398 / 6241) : ℂ) * ζ ^ 26 + ((1144 / 6241) : ℂ) * ζ ^ 27 + ((2973 / 12482) : ℂ) * ζ ^ 28 + ((1083 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep05Coefficient14 : ℂ :=
  (-((9 / 79) : ℂ) + ((2 / 79) : ℂ) * ζ ^ 1 - ((33 / 79) : ℂ) * ζ ^ 2 - ((33 / 79) : ℂ) * ζ ^ 6 + ((9 / 79) : ℂ) * ζ ^ 8 + ((19 / 79) : ℂ) * ζ ^ 9 - ((2 / 79) : ℂ) * ζ ^ 13 - ((2 / 79) : ℂ) * ζ ^ 17 + ((24 / 79) : ℂ) * ζ ^ 18 - ((2 / 79) : ℂ) * ζ ^ 21 + ((33 / 79) : ℂ) * ζ ^ 22 - ((33 / 79) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 25 - ((9 / 79) : ℂ) * ζ ^ 28 + ((2 / 79) : ℂ) * ζ ^ 29 - ((24 / 79) : ℂ) * ζ ^ 30)

private theorem row18_reducedY66_combinationStep05CoefficientIdentity14 :
    row18_reducedY66_combinationStep05Coefficient14 =
      row18_reducedY66_combinationStep04Coefficient14 +
        row18_reducedY66_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep05Coefficient14 row18_reducedY66_combinationStep04Coefficient14 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep05Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep05CoefficientIdentity15 :
    row18_reducedY66_combinationStep05Coefficient15 =
      row18_reducedY66_combinationStep04Coefficient15 +
        row18_reducedY66_combinationStep05Multiplier *
          (((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep05Coefficient15 row18_reducedY66_combinationStep04Coefficient15 row18_reducedY66_combinationStep05Multiplier
  close_cyclotomic_row18 (((2474 / 6241) : ℂ) - ((6163 / 12482) : ℂ) * ζ ^ 1 - ((3250 / 6241) : ℂ) * ζ ^ 2 + ((1919 / 6241) : ℂ) * ζ ^ 3 - ((7587 / 12482) : ℂ) * ζ ^ 4 + ((3018 / 6241) : ℂ) * ζ ^ 5 + ((1520 / 6241) : ℂ) * ζ ^ 6 - ((3459 / 6241) : ℂ) * ζ ^ 7 + ((315 / 12482) : ℂ) * ζ ^ 8 + ((1635 / 12482) : ℂ) * ζ ^ 9 - ((2433 / 12482) : ℂ) * ζ ^ 10 - ((203 / 12482) : ℂ) * ζ ^ 11 + ((1748 / 6241) : ℂ) * ζ ^ 12 - ((1205 / 6241) : ℂ) * ζ ^ 13 + ((837 / 12482) : ℂ) * ζ ^ 14 - ((894 / 6241) : ℂ) * ζ ^ 15 - ((247 / 12482) : ℂ) * ζ ^ 16 - ((163 / 6241) : ℂ) * ζ ^ 17 - ((1985 / 12482) : ℂ) * ζ ^ 18 + ((1125 / 6241) : ℂ) * ζ ^ 19 - ((871 / 12482) : ℂ) * ζ ^ 20 - ((706 / 6241) : ℂ) * ζ ^ 21 + ((3236 / 6241) : ℂ) * ζ ^ 22 - ((2 / 79) : ℂ) * ζ ^ 23 + ((710 / 6241) : ℂ) * ζ ^ 24 - ((240 / 6241) : ℂ) * ζ ^ 25 - ((10525 / 12482) : ℂ) * ζ ^ 26 + ((162 / 6241) : ℂ) * ζ ^ 27 + ((3337 / 12482) : ℂ) * ζ ^ 28 + ((741 / 12482) : ℂ) * ζ ^ 29 - ((705 / 12482) : ℂ) * ζ ^ 30)

private theorem row18_reducedY66_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY66_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY66_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY66_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY66_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY66_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY66_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY66_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY66_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY66_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY66_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY66_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY66_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY66_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY66_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY66_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY66_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY66_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation07
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY66_combinationStep05CoefficientIdentity00,
      row18_reducedY66_combinationStep05CoefficientIdentity01,
      row18_reducedY66_combinationStep05CoefficientIdentity02,
      row18_reducedY66_combinationStep05CoefficientIdentity03,
      row18_reducedY66_combinationStep05CoefficientIdentity04,
      row18_reducedY66_combinationStep05CoefficientIdentity05,
      row18_reducedY66_combinationStep05CoefficientIdentity06,
      row18_reducedY66_combinationStep05CoefficientIdentity07,
      row18_reducedY66_combinationStep05CoefficientIdentity08,
      row18_reducedY66_combinationStep05CoefficientIdentity09,
      row18_reducedY66_combinationStep05CoefficientIdentity10,
      row18_reducedY66_combinationStep05CoefficientIdentity11,
      row18_reducedY66_combinationStep05CoefficientIdentity12,
      row18_reducedY66_combinationStep05CoefficientIdentity13,
      row18_reducedY66_combinationStep05CoefficientIdentity14,
      row18_reducedY66_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY66_combinationStep05Multiplier * equation

private def row18_reducedY66_combinationStep06Multiplier : ℂ :=
  (-((2512 / 395) : ℂ) - ((2374 / 395) : ℂ) * ζ ^ 1 + ((10172 / 1185) : ℂ) * ζ ^ 2 + ((258 / 79) : ℂ) * ζ ^ 3 - ((10856 / 1185) : ℂ) * ζ ^ 5 + ((298 / 1185) : ℂ) * ζ ^ 6 + ((3766 / 395) : ℂ) * ζ ^ 8 + ((1694 / 1185) : ℂ) * ζ ^ 9 - ((1084 / 237) : ℂ) * ζ ^ 11 + ((9874 / 1185) : ℂ) * ζ ^ 12 + ((2374 / 395) : ℂ) * ζ ^ 13 - ((258 / 79) : ℂ) * ζ ^ 15 + ((2374 / 395) : ℂ) * ζ ^ 17 - ((2636 / 1185) : ℂ) * ζ ^ 18 + ((3734 / 1185) : ℂ) * ζ ^ 21 - ((10172 / 1185) : ℂ) * ζ ^ 22 - ((10172 / 1185) : ℂ) * ζ ^ 24 + ((3734 / 1185) : ℂ) * ζ ^ 25 + ((1084 / 237) : ℂ) * ζ ^ 27 - ((3766 / 395) : ℂ) * ζ ^ 28 - ((2374 / 395) : ℂ) * ζ ^ 29 - ((1126 / 1185) : ℂ) * ζ ^ 30 + ((1084 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY66_combinationStep06Coefficient00 : ℂ :=
  (((213 / 79) : ℂ) - ((1848 / 395) : ℂ) * ζ ^ 1 + ((7859 / 790) : ℂ) * ζ ^ 2 + ((1402 / 395) : ℂ) * ζ ^ 3 + ((1691 / 395) : ℂ) * ζ ^ 5 + ((4578 / 395) : ℂ) * ζ ^ 6 + ((1325 / 158) : ℂ) * ζ ^ 8 + ((4386 / 395) : ℂ) * ζ ^ 9 + ((2984 / 395) : ℂ) * ζ ^ 11 + ((1325 / 158) : ℂ) * ζ ^ 12 + ((1848 / 395) : ℂ) * ζ ^ 13 + ((2137 / 395) : ℂ) * ζ ^ 15 + ((1848 / 395) : ℂ) * ζ ^ 17 - ((1297 / 790) : ℂ) * ζ ^ 18 + ((446 / 395) : ℂ) * ζ ^ 21 - ((7859 / 790) : ℂ) * ζ ^ 22 - ((3539 / 395) : ℂ) * ζ ^ 25 - ((446 / 395) : ℂ) * ζ ^ 27 - ((1325 / 158) : ℂ) * ζ ^ 28 - ((1848 / 395) : ℂ) * ζ ^ 29 + ((2289 / 395) : ℂ) * ζ ^ 30 - ((2984 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep06CoefficientIdentity00 :
    row18_reducedY66_combinationStep06Coefficient00 =
      row18_reducedY66_combinationStep05Coefficient00 +
        row18_reducedY66_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep06Coefficient00 row18_reducedY66_combinationStep05Coefficient00 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep06Coefficient01 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep06CoefficientIdentity01 :
    row18_reducedY66_combinationStep06Coefficient01 =
      row18_reducedY66_combinationStep05Coefficient01 +
        row18_reducedY66_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep06Coefficient01 row18_reducedY66_combinationStep05Coefficient01 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep06Coefficient02 : ℂ :=
  (((2794 / 1185) : ℂ) - ((5773 / 2370) : ℂ) * ζ ^ 1 - ((781 / 395) : ℂ) * ζ ^ 2 + ((416 / 79) : ℂ) * ζ ^ 3 - ((17882 / 1185) : ℂ) * ζ ^ 5 + ((421 / 395) : ℂ) * ζ ^ 6 - ((4877 / 1185) : ℂ) * ζ ^ 8 - ((12109 / 2370) : ℂ) * ζ ^ 9 - ((2487 / 158) : ℂ) * ζ ^ 11 - ((1202 / 395) : ℂ) * ζ ^ 12 + ((5773 / 2370) : ℂ) * ζ ^ 13 - ((416 / 79) : ℂ) * ζ ^ 15 + ((5773 / 2370) : ℂ) * ζ ^ 17 - ((451 / 1185) : ℂ) * ζ ^ 18 + ((9997 / 790) : ℂ) * ζ ^ 21 + ((781 / 395) : ℂ) * ζ ^ 22 + ((781 / 395) : ℂ) * ζ ^ 24 + ((9997 / 790) : ℂ) * ζ ^ 25 + ((2487 / 158) : ℂ) * ζ ^ 27 + ((4877 / 1185) : ℂ) * ζ ^ 28 - ((5773 / 2370) : ℂ) * ζ ^ 29 + ((2534 / 1185) : ℂ) * ζ ^ 30 + ((2487 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep06CoefficientIdentity02 :
    row18_reducedY66_combinationStep06Coefficient02 =
      row18_reducedY66_combinationStep05Coefficient02 +
        row18_reducedY66_combinationStep06Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep06Coefficient02 row18_reducedY66_combinationStep05Coefficient02 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 (((24662 / 93615) : ℂ) - ((75109 / 187230) : ℂ) * ζ ^ 1 + ((257018 / 93615) : ℂ) * ζ ^ 2 - ((1775 / 18723) : ℂ) * ζ ^ 3 - ((467471 / 187230) : ℂ) * ζ ^ 4 + ((13922 / 18723) : ℂ) * ζ ^ 5 - ((219581 / 187230) : ℂ) * ζ ^ 6 + ((166029 / 62410) : ℂ) * ζ ^ 7 + ((37181 / 187230) : ℂ) * ζ ^ 8 - ((11105 / 18723) : ℂ) * ζ ^ 9 + ((72607 / 187230) : ℂ) * ζ ^ 10 - ((128869 / 187230) : ℂ) * ζ ^ 11 - ((27559 / 93615) : ℂ) * ζ ^ 12 - ((32481 / 62410) : ℂ) * ζ ^ 13 + ((59558 / 93615) : ℂ) * ζ ^ 14 + ((48436 / 31205) : ℂ) * ζ ^ 15 + ((20336 / 93615) : ℂ) * ζ ^ 16 + ((547 / 93615) : ℂ) * ζ ^ 17 - ((6554 / 18723) : ℂ) * ζ ^ 18 - ((47367 / 31205) : ℂ) * ζ ^ 19 + ((1384 / 31205) : ℂ) * ζ ^ 20 - ((97337 / 93615) : ℂ) * ζ ^ 21 - ((15167 / 37446) : ℂ) * ζ ^ 22 - ((16310 / 18723) : ℂ) * ζ ^ 23 + ((49951 / 31205) : ℂ) * ζ ^ 24 + ((63059 / 187230) : ℂ) * ζ ^ 25 + ((53074 / 93615) : ℂ) * ζ ^ 26 - ((41051 / 62410) : ℂ) * ζ ^ 27 - ((5518 / 93615) : ℂ) * ζ ^ 28 - ((25621 / 93615) : ℂ) * ζ ^ 29 + ((3794 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep06Coefficient03 : ℂ :=
  (-((189 / 158) : ℂ) - ((439 / 237) : ℂ) * ζ ^ 1 + ((703 / 237) : ℂ) * ζ ^ 2 + ((515 / 158) : ℂ) * ζ ^ 3 - ((181 / 474) : ℂ) * ζ ^ 5 + ((563 / 237) : ℂ) * ζ ^ 6 + ((659 / 237) : ℂ) * ζ ^ 8 + ((1183 / 474) : ℂ) * ζ ^ 9 - ((181 / 237) : ℂ) * ζ ^ 11 + ((659 / 237) : ℂ) * ζ ^ 12 + ((439 / 237) : ℂ) * ζ ^ 13 - ((424 / 237) : ℂ) * ζ ^ 15 + ((439 / 237) : ℂ) * ζ ^ 17 + ((140 / 237) : ℂ) * ζ ^ 18 - ((667 / 474) : ℂ) * ζ ^ 21 - ((703 / 237) : ℂ) * ζ ^ 22 - ((697 / 474) : ℂ) * ζ ^ 25 + ((667 / 474) : ℂ) * ζ ^ 27 - ((659 / 237) : ℂ) * ζ ^ 28 - ((439 / 237) : ℂ) * ζ ^ 29 + ((563 / 474) : ℂ) * ζ ^ 30 + ((181 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep06CoefficientIdentity03 :
    row18_reducedY66_combinationStep06Coefficient03 =
      row18_reducedY66_combinationStep05Coefficient03 +
        row18_reducedY66_combinationStep06Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep06Coefficient03 row18_reducedY66_combinationStep05Coefficient03 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 (-((205559 / 62410) : ℂ) + ((124397 / 62410) : ℂ) * ζ ^ 1 + ((18162 / 31205) : ℂ) * ζ ^ 2 - ((3499 / 1185) : ℂ) * ζ ^ 3 + ((13513 / 6241) : ℂ) * ζ ^ 4 - ((347707 / 187230) : ℂ) * ζ ^ 5 - ((1846 / 6241) : ℂ) * ζ ^ 6 - ((218743 / 187230) : ℂ) * ζ ^ 7 + ((30251 / 187230) : ℂ) * ζ ^ 8 - ((137879 / 93615) : ℂ) * ζ ^ 9 - ((67929 / 62410) : ℂ) * ζ ^ 10 - ((10943 / 18723) : ℂ) * ζ ^ 11 - ((81571 / 187230) : ℂ) * ζ ^ 12 - ((102856 / 93615) : ℂ) * ζ ^ 13 - ((285116 / 93615) : ℂ) * ζ ^ 14 - ((64298 / 93615) : ℂ) * ζ ^ 15 + ((7207 / 6241) : ℂ) * ζ ^ 16 - ((113183 / 62410) : ℂ) * ζ ^ 17 - ((656251 / 187230) : ℂ) * ζ ^ 18 + ((43153 / 37446) : ℂ) * ζ ^ 19 - ((88673 / 37446) : ℂ) * ζ ^ 20 - ((141553 / 187230) : ℂ) * ζ ^ 21 - ((454061 / 187230) : ℂ) * ζ ^ 22 + ((264937 / 93615) : ℂ) * ζ ^ 23 - ((184072 / 93615) : ℂ) * ζ ^ 24 + ((102611 / 93615) : ℂ) * ζ ^ 25 - ((4919 / 37446) : ℂ) * ζ ^ 26 - ((3248 / 93615) : ℂ) * ζ ^ 27 - ((61409 / 37446) : ℂ) * ζ ^ 28 + ((139021 / 187230) : ℂ) * ζ ^ 29 + ((3523 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep06Coefficient04 : ℂ :=
  (-((213 / 79) : ℂ) + ((1848 / 395) : ℂ) * ζ ^ 1 - ((7859 / 790) : ℂ) * ζ ^ 2 - ((1402 / 395) : ℂ) * ζ ^ 3 - ((1691 / 395) : ℂ) * ζ ^ 5 - ((4578 / 395) : ℂ) * ζ ^ 6 - ((1325 / 158) : ℂ) * ζ ^ 8 - ((4386 / 395) : ℂ) * ζ ^ 9 - ((2984 / 395) : ℂ) * ζ ^ 11 - ((1325 / 158) : ℂ) * ζ ^ 12 - ((1848 / 395) : ℂ) * ζ ^ 13 - ((2137 / 395) : ℂ) * ζ ^ 15 - ((1848 / 395) : ℂ) * ζ ^ 17 + ((1297 / 790) : ℂ) * ζ ^ 18 - ((446 / 395) : ℂ) * ζ ^ 21 + ((7859 / 790) : ℂ) * ζ ^ 22 + ((3539 / 395) : ℂ) * ζ ^ 25 + ((446 / 395) : ℂ) * ζ ^ 27 + ((1325 / 158) : ℂ) * ζ ^ 28 + ((1848 / 395) : ℂ) * ζ ^ 29 - ((2289 / 395) : ℂ) * ζ ^ 30 + ((2984 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep06CoefficientIdentity04 :
    row18_reducedY66_combinationStep06Coefficient04 =
      row18_reducedY66_combinationStep05Coefficient04 +
        row18_reducedY66_combinationStep06Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep06Coefficient04 row18_reducedY66_combinationStep05Coefficient04 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 (((205559 / 62410) : ℂ) - ((124397 / 62410) : ℂ) * ζ ^ 1 - ((18162 / 31205) : ℂ) * ζ ^ 2 + ((3499 / 1185) : ℂ) * ζ ^ 3 - ((13513 / 6241) : ℂ) * ζ ^ 4 + ((347707 / 187230) : ℂ) * ζ ^ 5 + ((1846 / 6241) : ℂ) * ζ ^ 6 + ((218743 / 187230) : ℂ) * ζ ^ 7 - ((30251 / 187230) : ℂ) * ζ ^ 8 + ((137879 / 93615) : ℂ) * ζ ^ 9 + ((67929 / 62410) : ℂ) * ζ ^ 10 + ((10943 / 18723) : ℂ) * ζ ^ 11 + ((81571 / 187230) : ℂ) * ζ ^ 12 + ((102856 / 93615) : ℂ) * ζ ^ 13 + ((285116 / 93615) : ℂ) * ζ ^ 14 + ((64298 / 93615) : ℂ) * ζ ^ 15 - ((7207 / 6241) : ℂ) * ζ ^ 16 + ((113183 / 62410) : ℂ) * ζ ^ 17 + ((656251 / 187230) : ℂ) * ζ ^ 18 - ((43153 / 37446) : ℂ) * ζ ^ 19 + ((88673 / 37446) : ℂ) * ζ ^ 20 + ((141553 / 187230) : ℂ) * ζ ^ 21 + ((454061 / 187230) : ℂ) * ζ ^ 22 - ((264937 / 93615) : ℂ) * ζ ^ 23 + ((184072 / 93615) : ℂ) * ζ ^ 24 - ((102611 / 93615) : ℂ) * ζ ^ 25 + ((4919 / 37446) : ℂ) * ζ ^ 26 + ((3248 / 93615) : ℂ) * ζ ^ 27 + ((61409 / 37446) : ℂ) * ζ ^ 28 - ((139021 / 187230) : ℂ) * ζ ^ 29 - ((3523 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep06Coefficient05 : ℂ :=
  (-((177 / 158) : ℂ) + ((827 / 474) : ℂ) * ζ ^ 1 - ((580 / 79) : ℂ) * ζ ^ 2 - ((2573 / 474) : ℂ) * ζ ^ 5 - ((983 / 158) : ℂ) * ζ ^ 6 - ((983 / 158) : ℂ) * ζ ^ 8 - ((2573 / 474) : ℂ) * ζ ^ 9 - ((1847 / 237) : ℂ) * ζ ^ 11 - ((1085 / 237) : ℂ) * ζ ^ 12 - ((827 / 474) : ℂ) * ζ ^ 13 - ((2135 / 474) : ℂ) * ζ ^ 15 - ((827 / 474) : ℂ) * ζ ^ 17 + ((1541 / 474) : ℂ) * ζ ^ 18 + ((291 / 158) : ℂ) * ζ ^ 21 + ((580 / 79) : ℂ) * ζ ^ 22 + ((704 / 237) : ℂ) * ζ ^ 24 + ((1700 / 237) : ℂ) * ζ ^ 25 + ((2135 / 474) : ℂ) * ζ ^ 27 + ((983 / 158) : ℂ) * ζ ^ 28 + ((827 / 474) : ℂ) * ζ ^ 29 - ((779 / 474) : ℂ) * ζ ^ 30 + ((1847 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep06CoefficientIdentity05 :
    row18_reducedY66_combinationStep06Coefficient05 =
      row18_reducedY66_combinationStep05Coefficient05 +
        row18_reducedY66_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep06Coefficient05 row18_reducedY66_combinationStep05Coefficient05 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep06Coefficient06 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep06CoefficientIdentity06 :
    row18_reducedY66_combinationStep06Coefficient06 =
      row18_reducedY66_combinationStep05Coefficient06 +
        row18_reducedY66_combinationStep06Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep06Coefficient06 row18_reducedY66_combinationStep05Coefficient06 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 (-((167627 / 93615) : ℂ) + ((54203 / 187230) : ℂ) * ζ ^ 1 - ((193873 / 187230) : ℂ) * ζ ^ 2 - ((248211 / 62410) : ℂ) * ζ ^ 3 - ((403526 / 93615) : ℂ) * ζ ^ 4 + ((296032 / 93615) : ℂ) * ζ ^ 5 + ((164894 / 31205) : ℂ) * ζ ^ 6 + ((174414 / 31205) : ℂ) * ζ ^ 7 - ((342599 / 187230) : ℂ) * ζ ^ 8 - ((94779 / 12482) : ℂ) * ζ ^ 9 - ((912463 / 187230) : ℂ) * ζ ^ 10 - ((780023 / 187230) : ℂ) * ζ ^ 11 + ((358651 / 187230) : ℂ) * ζ ^ 12 + ((147094 / 31205) : ℂ) * ζ ^ 13 + ((175727 / 187230) : ℂ) * ζ ^ 14 - ((58623 / 62410) : ℂ) * ζ ^ 15 - ((69659 / 18723) : ℂ) * ζ ^ 16 - ((765086 / 93615) : ℂ) * ζ ^ 17 - ((461981 / 93615) : ℂ) * ζ ^ 18 - ((5619 / 12482) : ℂ) * ζ ^ 19 + ((6737 / 790) : ℂ) * ζ ^ 20 + ((89412 / 31205) : ℂ) * ζ ^ 21 - ((439633 / 187230) : ℂ) * ζ ^ 22 - ((565808 / 93615) : ℂ) * ζ ^ 23 - ((231886 / 93615) : ℂ) * ζ ^ 24 + ((91173 / 62410) : ℂ) * ζ ^ 25 + ((708449 / 187230) : ℂ) * ζ ^ 26 + ((81069 / 62410) : ℂ) * ζ ^ 27 - ((1375 / 6241) : ℂ) * ζ ^ 28 - ((24638 / 93615) : ℂ) * ζ ^ 29 - ((7588 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep06Coefficient07 : ℂ :=
  (((163 / 158) : ℂ) + ((295 / 237) : ℂ) * ζ ^ 1 - ((760 / 237) : ℂ) * ζ ^ 2 - ((361 / 158) : ℂ) * ζ ^ 3 + ((295 / 474) : ℂ) * ζ ^ 5 - ((551 / 237) : ℂ) * ζ ^ 6 - ((644 / 237) : ℂ) * ζ ^ 8 - ((613 / 474) : ℂ) * ζ ^ 9 + ((235 / 237) : ℂ) * ζ ^ 11 - ((644 / 237) : ℂ) * ζ ^ 12 - ((295 / 237) : ℂ) * ζ ^ 13 + ((394 / 237) : ℂ) * ζ ^ 15 - ((295 / 237) : ℂ) * ζ ^ 17 - ((209 / 237) : ℂ) * ζ ^ 18 + ((493 / 474) : ℂ) * ζ ^ 21 + ((760 / 237) : ℂ) * ζ ^ 22 + ((295 / 474) : ℂ) * ζ ^ 25 - ((493 / 474) : ℂ) * ζ ^ 27 + ((644 / 237) : ℂ) * ζ ^ 28 + ((295 / 237) : ℂ) * ζ ^ 29 - ((551 / 474) : ℂ) * ζ ^ 30 - ((235 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep06CoefficientIdentity07 :
    row18_reducedY66_combinationStep06Coefficient07 =
      row18_reducedY66_combinationStep05Coefficient07 +
        row18_reducedY66_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep06Coefficient07 row18_reducedY66_combinationStep05Coefficient07 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep06Coefficient08 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep06CoefficientIdentity08 :
    row18_reducedY66_combinationStep06Coefficient08 =
      row18_reducedY66_combinationStep05Coefficient08 +
        row18_reducedY66_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep06Coefficient08 row18_reducedY66_combinationStep05Coefficient08 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep06Coefficient09 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep06CoefficientIdentity09 :
    row18_reducedY66_combinationStep06Coefficient09 =
      row18_reducedY66_combinationStep05Coefficient09 +
        row18_reducedY66_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep06Coefficient09 row18_reducedY66_combinationStep05Coefficient09 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep06Coefficient10 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep06CoefficientIdentity10 :
    row18_reducedY66_combinationStep06Coefficient10 =
      row18_reducedY66_combinationStep05Coefficient10 +
        row18_reducedY66_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep06Coefficient10 row18_reducedY66_combinationStep05Coefficient10 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep06Coefficient11 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep06CoefficientIdentity11 :
    row18_reducedY66_combinationStep06Coefficient11 =
      row18_reducedY66_combinationStep05Coefficient11 +
        row18_reducedY66_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep06Coefficient11 row18_reducedY66_combinationStep05Coefficient11 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep06Coefficient12 : ℂ :=
  (((46 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep06CoefficientIdentity12 :
    row18_reducedY66_combinationStep06Coefficient12 =
      row18_reducedY66_combinationStep05Coefficient12 +
        row18_reducedY66_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep06Coefficient12 row18_reducedY66_combinationStep05Coefficient12 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep06Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep06CoefficientIdentity13 :
    row18_reducedY66_combinationStep06Coefficient13 =
      row18_reducedY66_combinationStep05Coefficient13 +
        row18_reducedY66_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep06Coefficient13 row18_reducedY66_combinationStep05Coefficient13 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep06Coefficient14 : ℂ :=
  (-((9 / 79) : ℂ) + ((2 / 79) : ℂ) * ζ ^ 1 - ((33 / 79) : ℂ) * ζ ^ 2 - ((33 / 79) : ℂ) * ζ ^ 6 + ((9 / 79) : ℂ) * ζ ^ 8 + ((19 / 79) : ℂ) * ζ ^ 9 - ((2 / 79) : ℂ) * ζ ^ 13 - ((2 / 79) : ℂ) * ζ ^ 17 + ((24 / 79) : ℂ) * ζ ^ 18 - ((2 / 79) : ℂ) * ζ ^ 21 + ((33 / 79) : ℂ) * ζ ^ 22 - ((33 / 79) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 25 - ((9 / 79) : ℂ) * ζ ^ 28 + ((2 / 79) : ℂ) * ζ ^ 29 - ((24 / 79) : ℂ) * ζ ^ 30)

private theorem row18_reducedY66_combinationStep06CoefficientIdentity14 :
    row18_reducedY66_combinationStep06Coefficient14 =
      row18_reducedY66_combinationStep05Coefficient14 +
        row18_reducedY66_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep06Coefficient14 row18_reducedY66_combinationStep05Coefficient14 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep06Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep06CoefficientIdentity15 :
    row18_reducedY66_combinationStep06Coefficient15 =
      row18_reducedY66_combinationStep05Coefficient15 +
        row18_reducedY66_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep06Coefficient15 row18_reducedY66_combinationStep05Coefficient15 row18_reducedY66_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY66_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY66_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY66_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY66_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY66_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY66_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY66_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY66_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY66_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY66_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY66_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY66_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY66_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY66_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY66_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY66_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY66_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY66_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY66_combinationStep06CoefficientIdentity00,
      row18_reducedY66_combinationStep06CoefficientIdentity01,
      row18_reducedY66_combinationStep06CoefficientIdentity02,
      row18_reducedY66_combinationStep06CoefficientIdentity03,
      row18_reducedY66_combinationStep06CoefficientIdentity04,
      row18_reducedY66_combinationStep06CoefficientIdentity05,
      row18_reducedY66_combinationStep06CoefficientIdentity06,
      row18_reducedY66_combinationStep06CoefficientIdentity07,
      row18_reducedY66_combinationStep06CoefficientIdentity08,
      row18_reducedY66_combinationStep06CoefficientIdentity09,
      row18_reducedY66_combinationStep06CoefficientIdentity10,
      row18_reducedY66_combinationStep06CoefficientIdentity11,
      row18_reducedY66_combinationStep06CoefficientIdentity12,
      row18_reducedY66_combinationStep06CoefficientIdentity13,
      row18_reducedY66_combinationStep06CoefficientIdentity14,
      row18_reducedY66_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY66_combinationStep06Multiplier * equation

private def row18_reducedY66_combinationStep07Multiplier : ℂ :=
  (((1042 / 237) : ℂ) + ((354 / 79) : ℂ) * ζ ^ 1 - ((2222 / 237) : ℂ) * ζ ^ 2 - ((694 / 79) : ℂ) * ζ ^ 3 + ((3368 / 237) : ℂ) * ζ ^ 5 - ((624 / 79) : ℂ) * ζ ^ 8 - ((74 / 237) : ℂ) * ζ ^ 9 + ((2156 / 237) : ℂ) * ζ ^ 11 - ((212 / 237) : ℂ) * ζ ^ 12 - ((354 / 79) : ℂ) * ζ ^ 13 - ((224 / 237) : ℂ) * ζ ^ 15 - ((354 / 79) : ℂ) * ζ ^ 17 + ((2222 / 237) : ℂ) * ζ ^ 18 - ((1048 / 79) : ℂ) * ζ ^ 21 + ((2222 / 237) : ℂ) * ζ ^ 22 + ((2084 / 237) : ℂ) * ζ ^ 24 - ((2306 / 237) : ℂ) * ζ ^ 25 - ((1048 / 79) : ℂ) * ζ ^ 27 + ((624 / 79) : ℂ) * ζ ^ 28 + ((354 / 79) : ℂ) * ζ ^ 29 + ((922 / 237) : ℂ) * ζ ^ 30 - ((2156 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY66_combinationStep07Coefficient00 : ℂ :=
  (((213 / 79) : ℂ) - ((1848 / 395) : ℂ) * ζ ^ 1 + ((7859 / 790) : ℂ) * ζ ^ 2 + ((1402 / 395) : ℂ) * ζ ^ 3 + ((1691 / 395) : ℂ) * ζ ^ 5 + ((4578 / 395) : ℂ) * ζ ^ 6 + ((1325 / 158) : ℂ) * ζ ^ 8 + ((4386 / 395) : ℂ) * ζ ^ 9 + ((2984 / 395) : ℂ) * ζ ^ 11 + ((1325 / 158) : ℂ) * ζ ^ 12 + ((1848 / 395) : ℂ) * ζ ^ 13 + ((2137 / 395) : ℂ) * ζ ^ 15 + ((1848 / 395) : ℂ) * ζ ^ 17 - ((1297 / 790) : ℂ) * ζ ^ 18 + ((446 / 395) : ℂ) * ζ ^ 21 - ((7859 / 790) : ℂ) * ζ ^ 22 - ((3539 / 395) : ℂ) * ζ ^ 25 - ((446 / 395) : ℂ) * ζ ^ 27 - ((1325 / 158) : ℂ) * ζ ^ 28 - ((1848 / 395) : ℂ) * ζ ^ 29 + ((2289 / 395) : ℂ) * ζ ^ 30 - ((2984 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep07CoefficientIdentity00 :
    row18_reducedY66_combinationStep07Coefficient00 =
      row18_reducedY66_combinationStep06Coefficient00 +
        row18_reducedY66_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep07Coefficient00 row18_reducedY66_combinationStep06Coefficient00 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep07Coefficient01 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep07CoefficientIdentity01 :
    row18_reducedY66_combinationStep07Coefficient01 =
      row18_reducedY66_combinationStep06Coefficient01 +
        row18_reducedY66_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep07Coefficient01 row18_reducedY66_combinationStep06Coefficient01 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep07Coefficient02 : ℂ :=
  (((1508 / 395) : ℂ) - ((893 / 395) : ℂ) * ζ ^ 1 - ((7297 / 790) : ℂ) * ζ ^ 2 + ((551 / 158) : ℂ) * ζ ^ 3 - ((3779 / 395) : ℂ) * ζ ^ 5 - ((3343 / 790) : ℂ) * ζ ^ 6 - ((4254 / 395) : ℂ) * ζ ^ 8 - ((1993 / 790) : ℂ) * ζ ^ 9 - ((1281 / 158) : ℂ) * ζ ^ 11 - ((1977 / 395) : ℂ) * ζ ^ 12 + ((893 / 395) : ℂ) * ζ ^ 13 - ((551 / 158) : ℂ) * ζ ^ 15 + ((893 / 395) : ℂ) * ζ ^ 17 + ((4281 / 790) : ℂ) * ζ ^ 18 + ((2886 / 395) : ℂ) * ζ ^ 21 + ((7297 / 790) : ℂ) * ζ ^ 22 + ((7297 / 790) : ℂ) * ζ ^ 24 + ((2886 / 395) : ℂ) * ζ ^ 25 + ((1281 / 158) : ℂ) * ζ ^ 27 + ((4254 / 395) : ℂ) * ζ ^ 28 - ((893 / 395) : ℂ) * ζ ^ 29 + ((1211 / 790) : ℂ) * ζ ^ 30 + ((1281 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep07CoefficientIdentity02 :
    row18_reducedY66_combinationStep07Coefficient02 =
      row18_reducedY66_combinationStep06Coefficient02 +
        row18_reducedY66_combinationStep07Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep07Coefficient02 row18_reducedY66_combinationStep06Coefficient02 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 (-((17435 / 18723) : ℂ) + ((3424 / 18723) : ℂ) * ζ ^ 1 + ((228449 / 37446) : ℂ) * ζ ^ 2 + ((34819 / 37446) : ℂ) * ζ ^ 3 + ((11719 / 18723) : ℂ) * ζ ^ 4 - ((134465 / 37446) : ℂ) * ζ ^ 5 - ((4637 / 18723) : ℂ) * ζ ^ 6 + ((1759 / 37446) : ℂ) * ζ ^ 7 + ((27077 / 12482) : ℂ) * ζ ^ 8 - ((31057 / 18723) : ℂ) * ζ ^ 9 + ((10202 / 18723) : ℂ) * ζ ^ 10 - ((791 / 6241) : ℂ) * ζ ^ 11 + ((15869 / 12482) : ℂ) * ζ ^ 12 - ((4743 / 6241) : ℂ) * ζ ^ 13 - ((6545 / 12482) : ℂ) * ζ ^ 14 - ((28911 / 12482) : ℂ) * ζ ^ 15 + ((4684 / 18723) : ℂ) * ζ ^ 16 + ((37808 / 18723) : ℂ) * ζ ^ 17 + ((70399 / 18723) : ℂ) * ζ ^ 18 + ((7225 / 37446) : ℂ) * ζ ^ 19 - ((34977 / 12482) : ℂ) * ζ ^ 20 - ((74705 / 18723) : ℂ) * ζ ^ 21 - ((27047 / 37446) : ℂ) * ζ ^ 22 + ((8713 / 6241) : ℂ) * ζ ^ 23 + ((43671 / 12482) : ℂ) * ζ ^ 24 + ((18901 / 12482) : ℂ) * ζ ^ 25 - ((16696 / 18723) : ℂ) * ζ ^ 26 - ((109123 / 37446) : ℂ) * ζ ^ 27 - ((16079 / 37446) : ℂ) * ζ ^ 28 + ((14943 / 12482) : ℂ) * ζ ^ 29 + ((2695 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep07Coefficient03 : ℂ :=
  (-((13 / 79) : ℂ) - ((48 / 79) : ℂ) * ζ ^ 1 - ((19 / 79) : ℂ) * ζ ^ 2 + ((77 / 79) : ℂ) * ζ ^ 3 + ((19 / 79) : ℂ) * ζ ^ 5 + ((4 / 79) : ℂ) * ζ ^ 6 + ((5 / 79) : ℂ) * ζ ^ 8 + ((95 / 79) : ℂ) * ζ ^ 9 + ((18 / 79) : ℂ) * ζ ^ 11 + ((5 / 79) : ℂ) * ζ ^ 12 + ((48 / 79) : ℂ) * ζ ^ 13 - ((10 / 79) : ℂ) * ζ ^ 15 + ((48 / 79) : ℂ) * ζ ^ 17 - ((23 / 79) : ℂ) * ζ ^ 18 - ((29 / 79) : ℂ) * ζ ^ 21 + ((19 / 79) : ℂ) * ζ ^ 22 - ((67 / 79) : ℂ) * ζ ^ 25 + ((29 / 79) : ℂ) * ζ ^ 27 - ((5 / 79) : ℂ) * ζ ^ 28 - ((48 / 79) : ℂ) * ζ ^ 29 + ((2 / 79) : ℂ) * ζ ^ 30 - ((18 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep07CoefficientIdentity03 :
    row18_reducedY66_combinationStep07Coefficient03 =
      row18_reducedY66_combinationStep06Coefficient03 +
        row18_reducedY66_combinationStep07Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep07Coefficient03 row18_reducedY66_combinationStep06Coefficient03 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 (-((21959 / 37446) : ℂ) + ((1 / 474) : ℂ) * ζ ^ 1 + ((96212 / 18723) : ℂ) * ζ ^ 2 + ((13960 / 18723) : ℂ) * ζ ^ 3 - ((40634 / 6241) : ℂ) * ζ ^ 4 + ((2000 / 6241) : ℂ) * ζ ^ 5 + ((40939 / 12482) : ℂ) * ζ ^ 6 + ((57059 / 18723) : ℂ) * ζ ^ 7 + ((38833 / 18723) : ℂ) * ζ ^ 8 + ((15112 / 18723) : ℂ) * ζ ^ 9 - ((30271 / 37446) : ℂ) * ζ ^ 10 - ((84472 / 18723) : ℂ) * ζ ^ 11 - ((88235 / 37446) : ℂ) * ζ ^ 12 + ((7958 / 18723) : ℂ) * ζ ^ 13 + ((107825 / 12482) : ℂ) * ζ ^ 14 + ((98143 / 18723) : ℂ) * ζ ^ 15 + ((2576 / 18723) : ℂ) * ζ ^ 16 - ((42732 / 6241) : ℂ) * ζ ^ 17 - ((129293 / 18723) : ℂ) * ζ ^ 18 - ((36280 / 18723) : ℂ) * ζ ^ 19 + ((451871 / 37446) : ℂ) * ζ ^ 20 + ((43285 / 6241) : ℂ) * ζ ^ 21 - ((11215 / 37446) : ℂ) * ζ ^ 22 - ((141485 / 18723) : ℂ) * ζ ^ 23 - ((51049 / 18723) : ℂ) * ζ ^ 24 - ((4469 / 6241) : ℂ) * ζ ^ 25 + ((62961 / 12482) : ℂ) * ζ ^ 26 + ((17431 / 12482) : ℂ) * ζ ^ 27 - ((5919 / 6241) : ℂ) * ζ ^ 28 - ((6482 / 18723) : ℂ) * ζ ^ 29 - ((15092 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep07Coefficient04 : ℂ :=
  (-((213 / 79) : ℂ) + ((1848 / 395) : ℂ) * ζ ^ 1 - ((7859 / 790) : ℂ) * ζ ^ 2 - ((1402 / 395) : ℂ) * ζ ^ 3 - ((1691 / 395) : ℂ) * ζ ^ 5 - ((4578 / 395) : ℂ) * ζ ^ 6 - ((1325 / 158) : ℂ) * ζ ^ 8 - ((4386 / 395) : ℂ) * ζ ^ 9 - ((2984 / 395) : ℂ) * ζ ^ 11 - ((1325 / 158) : ℂ) * ζ ^ 12 - ((1848 / 395) : ℂ) * ζ ^ 13 - ((2137 / 395) : ℂ) * ζ ^ 15 - ((1848 / 395) : ℂ) * ζ ^ 17 + ((1297 / 790) : ℂ) * ζ ^ 18 - ((446 / 395) : ℂ) * ζ ^ 21 + ((7859 / 790) : ℂ) * ζ ^ 22 + ((3539 / 395) : ℂ) * ζ ^ 25 + ((446 / 395) : ℂ) * ζ ^ 27 + ((1325 / 158) : ℂ) * ζ ^ 28 + ((1848 / 395) : ℂ) * ζ ^ 29 - ((2289 / 395) : ℂ) * ζ ^ 30 + ((2984 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep07CoefficientIdentity04 :
    row18_reducedY66_combinationStep07Coefficient04 =
      row18_reducedY66_combinationStep06Coefficient04 +
        row18_reducedY66_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep07Coefficient04 row18_reducedY66_combinationStep06Coefficient04 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep07Coefficient05 : ℂ :=
  (-((32 / 79) : ℂ) + ((213 / 79) : ℂ) * ζ ^ 1 - ((1195 / 158) : ℂ) * ζ ^ 2 - ((748 / 79) : ℂ) * ζ ^ 5 - ((1131 / 158) : ℂ) * ζ ^ 6 - ((1131 / 158) : ℂ) * ζ ^ 8 - ((748 / 79) : ℂ) * ζ ^ 9 - ((1665 / 158) : ℂ) * ζ ^ 11 - ((382 / 79) : ℂ) * ζ ^ 12 - ((213 / 79) : ℂ) * ζ ^ 13 - ((482 / 79) : ℂ) * ζ ^ 15 - ((213 / 79) : ℂ) * ζ ^ 17 + ((235 / 79) : ℂ) * ζ ^ 18 + ((535 / 158) : ℂ) * ζ ^ 21 + ((1195 / 158) : ℂ) * ζ ^ 22 + ((661 / 158) : ℂ) * ζ ^ 24 + ((961 / 79) : ℂ) * ζ ^ 25 + ((482 / 79) : ℂ) * ζ ^ 27 + ((1131 / 158) : ℂ) * ζ ^ 28 + ((213 / 79) : ℂ) * ζ ^ 29 - ((367 / 158) : ℂ) * ζ ^ 30 + ((1665 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep07CoefficientIdentity05 :
    row18_reducedY66_combinationStep07Coefficient05 =
      row18_reducedY66_combinationStep06Coefficient05 +
        row18_reducedY66_combinationStep07Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep07Coefficient05 row18_reducedY66_combinationStep06Coefficient05 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 (-((10455 / 6241) : ℂ) - ((27983 / 37446) : ℂ) * ζ ^ 1 + ((20900 / 6241) : ℂ) * ζ ^ 2 - ((40931 / 37446) : ℂ) * ζ ^ 3 - ((4927 / 6241) : ℂ) * ζ ^ 4 + ((72806 / 18723) : ℂ) * ζ ^ 5 + ((84379 / 37446) : ℂ) * ζ ^ 6 - ((55039 / 18723) : ℂ) * ζ ^ 7 + ((124249 / 37446) : ℂ) * ζ ^ 8 + ((6997 / 37446) : ℂ) * ζ ^ 9 - ((67753 / 37446) : ℂ) * ζ ^ 10 + ((25901 / 18723) : ℂ) * ζ ^ 11 + ((30457 / 37446) : ℂ) * ζ ^ 12 + ((4064 / 6241) : ℂ) * ζ ^ 13 - ((12555 / 12482) : ℂ) * ζ ^ 14 + ((32024 / 18723) : ℂ) * ζ ^ 15 + ((3349 / 6241) : ℂ) * ζ ^ 16 + ((21039 / 6241) : ℂ) * ζ ^ 17 - ((123185 / 37446) : ℂ) * ζ ^ 18 + ((23385 / 12482) : ℂ) * ζ ^ 19 + ((15885 / 12482) : ℂ) * ζ ^ 20 + ((24047 / 37446) : ℂ) * ζ ^ 21 - ((56745 / 12482) : ℂ) * ζ ^ 22 + ((209699 / 37446) : ℂ) * ζ ^ 23 - ((36230 / 18723) : ℂ) * ζ ^ 24 + ((67123 / 37446) : ℂ) * ζ ^ 25 - ((26321 / 37446) : ℂ) * ζ ^ 26 + ((82427 / 37446) : ℂ) * ζ ^ 27 - ((123427 / 37446) : ℂ) * ζ ^ 28 + ((661 / 474) : ℂ) * ζ ^ 29 + ((7007 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep07Coefficient06 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep07CoefficientIdentity06 :
    row18_reducedY66_combinationStep07Coefficient06 =
      row18_reducedY66_combinationStep06Coefficient06 +
        row18_reducedY66_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep07Coefficient06 row18_reducedY66_combinationStep06Coefficient06 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep07Coefficient07 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep07CoefficientIdentity07 :
    row18_reducedY66_combinationStep07Coefficient07 =
      row18_reducedY66_combinationStep06Coefficient07 +
        row18_reducedY66_combinationStep07Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep07Coefficient07 row18_reducedY66_combinationStep06Coefficient07 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 (((21959 / 37446) : ℂ) - ((1 / 474) : ℂ) * ζ ^ 1 - ((96212 / 18723) : ℂ) * ζ ^ 2 - ((13960 / 18723) : ℂ) * ζ ^ 3 + ((40634 / 6241) : ℂ) * ζ ^ 4 - ((2000 / 6241) : ℂ) * ζ ^ 5 - ((40939 / 12482) : ℂ) * ζ ^ 6 - ((57059 / 18723) : ℂ) * ζ ^ 7 - ((38833 / 18723) : ℂ) * ζ ^ 8 - ((15112 / 18723) : ℂ) * ζ ^ 9 + ((30271 / 37446) : ℂ) * ζ ^ 10 + ((84472 / 18723) : ℂ) * ζ ^ 11 + ((88235 / 37446) : ℂ) * ζ ^ 12 - ((7958 / 18723) : ℂ) * ζ ^ 13 - ((107825 / 12482) : ℂ) * ζ ^ 14 - ((98143 / 18723) : ℂ) * ζ ^ 15 - ((2576 / 18723) : ℂ) * ζ ^ 16 + ((42732 / 6241) : ℂ) * ζ ^ 17 + ((129293 / 18723) : ℂ) * ζ ^ 18 + ((36280 / 18723) : ℂ) * ζ ^ 19 - ((451871 / 37446) : ℂ) * ζ ^ 20 - ((43285 / 6241) : ℂ) * ζ ^ 21 + ((11215 / 37446) : ℂ) * ζ ^ 22 + ((141485 / 18723) : ℂ) * ζ ^ 23 + ((51049 / 18723) : ℂ) * ζ ^ 24 + ((4469 / 6241) : ℂ) * ζ ^ 25 - ((62961 / 12482) : ℂ) * ζ ^ 26 - ((17431 / 12482) : ℂ) * ζ ^ 27 + ((5919 / 6241) : ℂ) * ζ ^ 28 + ((6482 / 18723) : ℂ) * ζ ^ 29 + ((15092 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep07Coefficient08 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep07CoefficientIdentity08 :
    row18_reducedY66_combinationStep07Coefficient08 =
      row18_reducedY66_combinationStep06Coefficient08 +
        row18_reducedY66_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep07Coefficient08 row18_reducedY66_combinationStep06Coefficient08 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep07Coefficient09 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep07CoefficientIdentity09 :
    row18_reducedY66_combinationStep07Coefficient09 =
      row18_reducedY66_combinationStep06Coefficient09 +
        row18_reducedY66_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep07Coefficient09 row18_reducedY66_combinationStep06Coefficient09 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep07Coefficient10 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep07CoefficientIdentity10 :
    row18_reducedY66_combinationStep07Coefficient10 =
      row18_reducedY66_combinationStep06Coefficient10 +
        row18_reducedY66_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep07Coefficient10 row18_reducedY66_combinationStep06Coefficient10 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep07Coefficient11 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep07CoefficientIdentity11 :
    row18_reducedY66_combinationStep07Coefficient11 =
      row18_reducedY66_combinationStep06Coefficient11 +
        row18_reducedY66_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep07Coefficient11 row18_reducedY66_combinationStep06Coefficient11 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep07Coefficient12 : ℂ :=
  (((46 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep07CoefficientIdentity12 :
    row18_reducedY66_combinationStep07Coefficient12 =
      row18_reducedY66_combinationStep06Coefficient12 +
        row18_reducedY66_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep07Coefficient12 row18_reducedY66_combinationStep06Coefficient12 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep07Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep07CoefficientIdentity13 :
    row18_reducedY66_combinationStep07Coefficient13 =
      row18_reducedY66_combinationStep06Coefficient13 +
        row18_reducedY66_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep07Coefficient13 row18_reducedY66_combinationStep06Coefficient13 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep07Coefficient14 : ℂ :=
  (-((9 / 79) : ℂ) + ((2 / 79) : ℂ) * ζ ^ 1 - ((33 / 79) : ℂ) * ζ ^ 2 - ((33 / 79) : ℂ) * ζ ^ 6 + ((9 / 79) : ℂ) * ζ ^ 8 + ((19 / 79) : ℂ) * ζ ^ 9 - ((2 / 79) : ℂ) * ζ ^ 13 - ((2 / 79) : ℂ) * ζ ^ 17 + ((24 / 79) : ℂ) * ζ ^ 18 - ((2 / 79) : ℂ) * ζ ^ 21 + ((33 / 79) : ℂ) * ζ ^ 22 - ((33 / 79) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 25 - ((9 / 79) : ℂ) * ζ ^ 28 + ((2 / 79) : ℂ) * ζ ^ 29 - ((24 / 79) : ℂ) * ζ ^ 30)

private theorem row18_reducedY66_combinationStep07CoefficientIdentity14 :
    row18_reducedY66_combinationStep07Coefficient14 =
      row18_reducedY66_combinationStep06Coefficient14 +
        row18_reducedY66_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep07Coefficient14 row18_reducedY66_combinationStep06Coefficient14 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep07Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep07CoefficientIdentity15 :
    row18_reducedY66_combinationStep07Coefficient15 =
      row18_reducedY66_combinationStep06Coefficient15 +
        row18_reducedY66_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep07Coefficient15 row18_reducedY66_combinationStep06Coefficient15 row18_reducedY66_combinationStep07Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY66_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY66_combinationStep07Coefficient00) * Y 0 0
      + (row18_reducedY66_combinationStep07Coefficient01) * Y 0 1
      + (row18_reducedY66_combinationStep07Coefficient02) * Y 1 0
      + (row18_reducedY66_combinationStep07Coefficient03) * Y 1 1
      + (row18_reducedY66_combinationStep07Coefficient04) * Y 2 2
      + (row18_reducedY66_combinationStep07Coefficient05) * Y 2 3
      + (row18_reducedY66_combinationStep07Coefficient06) * Y 3 2
      + (row18_reducedY66_combinationStep07Coefficient07) * Y 3 3
      + (row18_reducedY66_combinationStep07Coefficient08) * Y 4 4
      + (row18_reducedY66_combinationStep07Coefficient09) * Y 4 5
      + (row18_reducedY66_combinationStep07Coefficient10) * Y 5 4
      + (row18_reducedY66_combinationStep07Coefficient11) * Y 5 5
      + (row18_reducedY66_combinationStep07Coefficient12) * Y 6 6
      + (row18_reducedY66_combinationStep07Coefficient13) * Y 6 7
      + (row18_reducedY66_combinationStep07Coefficient14) * Y 7 6
      + (row18_reducedY66_combinationStep07Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY66_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY66_combinationStep07CoefficientIdentity00,
      row18_reducedY66_combinationStep07CoefficientIdentity01,
      row18_reducedY66_combinationStep07CoefficientIdentity02,
      row18_reducedY66_combinationStep07CoefficientIdentity03,
      row18_reducedY66_combinationStep07CoefficientIdentity04,
      row18_reducedY66_combinationStep07CoefficientIdentity05,
      row18_reducedY66_combinationStep07CoefficientIdentity06,
      row18_reducedY66_combinationStep07CoefficientIdentity07,
      row18_reducedY66_combinationStep07CoefficientIdentity08,
      row18_reducedY66_combinationStep07CoefficientIdentity09,
      row18_reducedY66_combinationStep07CoefficientIdentity10,
      row18_reducedY66_combinationStep07CoefficientIdentity11,
      row18_reducedY66_combinationStep07CoefficientIdentity12,
      row18_reducedY66_combinationStep07CoefficientIdentity13,
      row18_reducedY66_combinationStep07CoefficientIdentity14,
      row18_reducedY66_combinationStep07CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY66_combinationStep07Multiplier * equation

private def row18_reducedY66_combinationStep08Multiplier : ℂ :=
  (-((54 / 79) : ℂ) - ((18 / 79) : ℂ) * ζ ^ 1 - ((80 / 79) : ℂ) * ζ ^ 2 - ((142 / 79) : ℂ) * ζ ^ 3 + ((148 / 79) : ℂ) * ζ ^ 5 + ((40 / 79) : ℂ) * ζ ^ 6 - ((70 / 79) : ℂ) * ζ ^ 8 + ((92 / 79) : ℂ) * ζ ^ 9 + ((136 / 79) : ℂ) * ζ ^ 11 - ((120 / 79) : ℂ) * ζ ^ 12 + ((18 / 79) : ℂ) * ζ ^ 13 + ((142 / 79) : ℂ) * ζ ^ 15 + ((18 / 79) : ℂ) * ζ ^ 17 + ((134 / 79) : ℂ) * ζ ^ 18 - ((166 / 79) : ℂ) * ζ ^ 21 + ((80 / 79) : ℂ) * ζ ^ 22 + ((80 / 79) : ℂ) * ζ ^ 24 - ((166 / 79) : ℂ) * ζ ^ 25 - ((136 / 79) : ℂ) * ζ ^ 27 + ((70 / 79) : ℂ) * ζ ^ 28 - ((18 / 79) : ℂ) * ζ ^ 29 - ((10 / 79) : ℂ) * ζ ^ 30 - ((136 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY66_combinationStep08Coefficient00 : ℂ :=
  (((213 / 79) : ℂ) - ((1848 / 395) : ℂ) * ζ ^ 1 + ((7859 / 790) : ℂ) * ζ ^ 2 + ((1402 / 395) : ℂ) * ζ ^ 3 + ((1691 / 395) : ℂ) * ζ ^ 5 + ((4578 / 395) : ℂ) * ζ ^ 6 + ((1325 / 158) : ℂ) * ζ ^ 8 + ((4386 / 395) : ℂ) * ζ ^ 9 + ((2984 / 395) : ℂ) * ζ ^ 11 + ((1325 / 158) : ℂ) * ζ ^ 12 + ((1848 / 395) : ℂ) * ζ ^ 13 + ((2137 / 395) : ℂ) * ζ ^ 15 + ((1848 / 395) : ℂ) * ζ ^ 17 - ((1297 / 790) : ℂ) * ζ ^ 18 + ((446 / 395) : ℂ) * ζ ^ 21 - ((7859 / 790) : ℂ) * ζ ^ 22 - ((3539 / 395) : ℂ) * ζ ^ 25 - ((446 / 395) : ℂ) * ζ ^ 27 - ((1325 / 158) : ℂ) * ζ ^ 28 - ((1848 / 395) : ℂ) * ζ ^ 29 + ((2289 / 395) : ℂ) * ζ ^ 30 - ((2984 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep08CoefficientIdentity00 :
    row18_reducedY66_combinationStep08Coefficient00 =
      row18_reducedY66_combinationStep07Coefficient00 +
        row18_reducedY66_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep08Coefficient00 row18_reducedY66_combinationStep07Coefficient00 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep08Coefficient01 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep08CoefficientIdentity01 :
    row18_reducedY66_combinationStep08Coefficient01 =
      row18_reducedY66_combinationStep07Coefficient01 +
        row18_reducedY66_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep08Coefficient01 row18_reducedY66_combinationStep07Coefficient01 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep08Coefficient02 : ℂ :=
  (((1318 / 395) : ℂ) - ((708 / 395) : ℂ) * ζ ^ 1 - ((3496 / 395) : ℂ) * ζ ^ 2 + ((305 / 79) : ℂ) * ζ ^ 3 - ((3764 / 395) : ℂ) * ζ ^ 5 - ((1699 / 395) : ℂ) * ζ ^ 6 - ((4194 / 395) : ℂ) * ζ ^ 8 - ((1174 / 395) : ℂ) * ζ ^ 9 - ((686 / 79) : ℂ) * ζ ^ 11 - ((1797 / 395) : ℂ) * ζ ^ 12 + ((708 / 395) : ℂ) * ζ ^ 13 - ((305 / 79) : ℂ) * ζ ^ 15 + ((708 / 395) : ℂ) * ζ ^ 17 + ((2178 / 395) : ℂ) * ζ ^ 18 + ((3056 / 395) : ℂ) * ζ ^ 21 + ((3496 / 395) : ℂ) * ζ ^ 22 + ((3496 / 395) : ℂ) * ζ ^ 24 + ((3056 / 395) : ℂ) * ζ ^ 25 + ((686 / 79) : ℂ) * ζ ^ 27 + ((4194 / 395) : ℂ) * ζ ^ 28 - ((708 / 395) : ℂ) * ζ ^ 29 + ((698 / 395) : ℂ) * ζ ^ 30 + ((686 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep08CoefficientIdentity02 :
    row18_reducedY66_combinationStep08Coefficient02 =
      row18_reducedY66_combinationStep07Coefficient02 +
        row18_reducedY66_combinationStep08Multiplier *
          (((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((73 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((105 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((73 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep08Coefficient02 row18_reducedY66_combinationStep07Coefficient02 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 (((2840 / 6241) : ℂ) - ((6251 / 12482) : ℂ) * ζ ^ 1 - ((3427 / 12482) : ℂ) * ζ ^ 2 - ((2675 / 6241) : ℂ) * ζ ^ 3 - ((3559 / 12482) : ℂ) * ζ ^ 4 + ((12281 / 12482) : ℂ) * ζ ^ 5 + ((4515 / 12482) : ℂ) * ζ ^ 6 + ((320 / 6241) : ℂ) * ζ ^ 7 + ((945 / 12482) : ℂ) * ζ ^ 8 - ((4049 / 6241) : ℂ) * ζ ^ 9 - ((676 / 6241) : ℂ) * ζ ^ 10 + ((4634 / 6241) : ℂ) * ζ ^ 11 + ((865 / 6241) : ℂ) * ζ ^ 12 + ((712 / 6241) : ℂ) * ζ ^ 13 + ((1451 / 12482) : ℂ) * ζ ^ 14 - ((4861 / 12482) : ℂ) * ζ ^ 15 + ((578 / 6241) : ℂ) * ζ ^ 16 + ((3105 / 6241) : ℂ) * ζ ^ 17 + ((273 / 6241) : ℂ) * ζ ^ 18 - ((103 / 6241) : ℂ) * ζ ^ 19 + ((83 / 6241) : ℂ) * ζ ^ 20 - ((2947 / 6241) : ℂ) * ζ ^ 21 - ((829 / 12482) : ℂ) * ζ ^ 22 - ((377 / 6241) : ℂ) * ζ ^ 23 - ((944 / 6241) : ℂ) * ζ ^ 24 + ((75 / 12482) : ℂ) * ζ ^ 25 - ((299 / 6241) : ℂ) * ζ ^ 26 - ((2089 / 12482) : ℂ) * ζ ^ 27 - ((477 / 6241) : ℂ) * ζ ^ 28 - ((579 / 6241) : ℂ) * ζ ^ 29 - ((476 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep08Coefficient03 : ℂ :=
  (-((46 / 79) : ℂ) - ((24 / 79) : ℂ) * ζ ^ 1 - ((19 / 158) : ℂ) * ζ ^ 2 + ((77 / 158) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((2 / 79) : ℂ) * ζ ^ 6 + ((5 / 158) : ℂ) * ζ ^ 8 + ((95 / 158) : ℂ) * ζ ^ 9 + ((9 / 79) : ℂ) * ζ ^ 11 + ((5 / 158) : ℂ) * ζ ^ 12 + ((24 / 79) : ℂ) * ζ ^ 13 - ((5 / 79) : ℂ) * ζ ^ 15 + ((24 / 79) : ℂ) * ζ ^ 17 - ((23 / 158) : ℂ) * ζ ^ 18 - ((29 / 158) : ℂ) * ζ ^ 21 + ((19 / 158) : ℂ) * ζ ^ 22 - ((67 / 158) : ℂ) * ζ ^ 25 + ((29 / 158) : ℂ) * ζ ^ 27 - ((5 / 158) : ℂ) * ζ ^ 28 - ((24 / 79) : ℂ) * ζ ^ 29 + ((1 / 79) : ℂ) * ζ ^ 30 - ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep08CoefficientIdentity03 :
    row18_reducedY66_combinationStep08Coefficient03 =
      row18_reducedY66_combinationStep07Coefficient03 +
        row18_reducedY66_combinationStep08Multiplier *
          (-((5 / 316) : ℂ) + ((3 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((33 / 158) : ℂ) * ζ ^ 3 + ((3 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 + ((10 / 79) : ℂ) * ζ ^ 8 - ((3 / 316) : ℂ) * ζ ^ 9 - ((33 / 316) : ℂ) * ζ ^ 11 - ((3 / 79) : ℂ) * ζ ^ 12 - ((3 / 316) : ℂ) * ζ ^ 13 - ((35 / 158) : ℂ) * ζ ^ 15 - ((3 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 - ((45 / 158) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((59 / 316) : ℂ) * ζ ^ 24 - ((1 / 79) : ℂ) * ζ ^ 27 - ((10 / 79) : ℂ) * ζ ^ 28 + ((3 / 316) : ℂ) * ζ ^ 29 - ((13 / 79) : ℂ) * ζ ^ 30 + ((33 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep08Coefficient03 row18_reducedY66_combinationStep07Coefficient03 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 (((5349 / 12482) : ℂ) - ((1914 / 6241) : ℂ) * ζ ^ 1 - ((383 / 12482) : ℂ) * ζ ^ 2 + ((4851 / 12482) : ℂ) * ζ ^ 3 - ((2378 / 6241) : ℂ) * ζ ^ 4 + ((4723 / 12482) : ℂ) * ζ ^ 5 - ((1406 / 6241) : ℂ) * ζ ^ 6 - ((7141 / 12482) : ℂ) * ζ ^ 7 + ((9817 / 12482) : ℂ) * ζ ^ 8 + ((3164 / 6241) : ℂ) * ζ ^ 9 + ((1412 / 6241) : ℂ) * ζ ^ 10 - ((213 / 6241) : ℂ) * ζ ^ 11 - ((499 / 12482) : ℂ) * ζ ^ 12 - ((4605 / 12482) : ℂ) * ζ ^ 13 + ((53 / 79) : ℂ) * ζ ^ 14 + ((819 / 12482) : ℂ) * ζ ^ 15 - ((448 / 6241) : ℂ) * ζ ^ 16 + ((3570 / 6241) : ℂ) * ζ ^ 17 - ((1671 / 12482) : ℂ) * ζ ^ 18 + ((523 / 12482) : ℂ) * ζ ^ 19 + ((1859 / 12482) : ℂ) * ζ ^ 20 + ((2261 / 12482) : ℂ) * ζ ^ 21 - ((387 / 12482) : ℂ) * ζ ^ 22 + ((50 / 79) : ℂ) * ζ ^ 23 - ((2033 / 6241) : ℂ) * ζ ^ 24 + ((325 / 6241) : ℂ) * ζ ^ 25 - ((1375 / 12482) : ℂ) * ζ ^ 26 + ((2164 / 6241) : ℂ) * ζ ^ 27 - ((241 / 12482) : ℂ) * ζ ^ 28 + ((3371 / 12482) : ℂ) * ζ ^ 29 - ((1122 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep08Coefficient04 : ℂ :=
  (-((213 / 79) : ℂ) + ((1848 / 395) : ℂ) * ζ ^ 1 - ((7859 / 790) : ℂ) * ζ ^ 2 - ((1402 / 395) : ℂ) * ζ ^ 3 - ((1691 / 395) : ℂ) * ζ ^ 5 - ((4578 / 395) : ℂ) * ζ ^ 6 - ((1325 / 158) : ℂ) * ζ ^ 8 - ((4386 / 395) : ℂ) * ζ ^ 9 - ((2984 / 395) : ℂ) * ζ ^ 11 - ((1325 / 158) : ℂ) * ζ ^ 12 - ((1848 / 395) : ℂ) * ζ ^ 13 - ((2137 / 395) : ℂ) * ζ ^ 15 - ((1848 / 395) : ℂ) * ζ ^ 17 + ((1297 / 790) : ℂ) * ζ ^ 18 - ((446 / 395) : ℂ) * ζ ^ 21 + ((7859 / 790) : ℂ) * ζ ^ 22 + ((3539 / 395) : ℂ) * ζ ^ 25 + ((446 / 395) : ℂ) * ζ ^ 27 + ((1325 / 158) : ℂ) * ζ ^ 28 + ((1848 / 395) : ℂ) * ζ ^ 29 - ((2289 / 395) : ℂ) * ζ ^ 30 + ((2984 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep08CoefficientIdentity04 :
    row18_reducedY66_combinationStep08Coefficient04 =
      row18_reducedY66_combinationStep07Coefficient04 +
        row18_reducedY66_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep08Coefficient04 row18_reducedY66_combinationStep07Coefficient04 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep08Coefficient05 : ℂ :=
  (-((32 / 79) : ℂ) + ((213 / 79) : ℂ) * ζ ^ 1 - ((1195 / 158) : ℂ) * ζ ^ 2 - ((748 / 79) : ℂ) * ζ ^ 5 - ((1131 / 158) : ℂ) * ζ ^ 6 - ((1131 / 158) : ℂ) * ζ ^ 8 - ((748 / 79) : ℂ) * ζ ^ 9 - ((1665 / 158) : ℂ) * ζ ^ 11 - ((382 / 79) : ℂ) * ζ ^ 12 - ((213 / 79) : ℂ) * ζ ^ 13 - ((482 / 79) : ℂ) * ζ ^ 15 - ((213 / 79) : ℂ) * ζ ^ 17 + ((235 / 79) : ℂ) * ζ ^ 18 + ((535 / 158) : ℂ) * ζ ^ 21 + ((1195 / 158) : ℂ) * ζ ^ 22 + ((661 / 158) : ℂ) * ζ ^ 24 + ((961 / 79) : ℂ) * ζ ^ 25 + ((482 / 79) : ℂ) * ζ ^ 27 + ((1131 / 158) : ℂ) * ζ ^ 28 + ((213 / 79) : ℂ) * ζ ^ 29 - ((367 / 158) : ℂ) * ζ ^ 30 + ((1665 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep08CoefficientIdentity05 :
    row18_reducedY66_combinationStep08Coefficient05 =
      row18_reducedY66_combinationStep07Coefficient05 +
        row18_reducedY66_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep08Coefficient05 row18_reducedY66_combinationStep07Coefficient05 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep08Coefficient06 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep08CoefficientIdentity06 :
    row18_reducedY66_combinationStep08Coefficient06 =
      row18_reducedY66_combinationStep07Coefficient06 +
        row18_reducedY66_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep08Coefficient06 row18_reducedY66_combinationStep07Coefficient06 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep08Coefficient07 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep08CoefficientIdentity07 :
    row18_reducedY66_combinationStep08Coefficient07 =
      row18_reducedY66_combinationStep07Coefficient07 +
        row18_reducedY66_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep08Coefficient07 row18_reducedY66_combinationStep07Coefficient07 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep08Coefficient08 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep08CoefficientIdentity08 :
    row18_reducedY66_combinationStep08Coefficient08 =
      row18_reducedY66_combinationStep07Coefficient08 +
        row18_reducedY66_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep08Coefficient08 row18_reducedY66_combinationStep07Coefficient08 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep08Coefficient09 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep08CoefficientIdentity09 :
    row18_reducedY66_combinationStep08Coefficient09 =
      row18_reducedY66_combinationStep07Coefficient09 +
        row18_reducedY66_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep08Coefficient09 row18_reducedY66_combinationStep07Coefficient09 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep08Coefficient10 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep08CoefficientIdentity10 :
    row18_reducedY66_combinationStep08Coefficient10 =
      row18_reducedY66_combinationStep07Coefficient10 +
        row18_reducedY66_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep08Coefficient10 row18_reducedY66_combinationStep07Coefficient10 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep08Coefficient11 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep08CoefficientIdentity11 :
    row18_reducedY66_combinationStep08Coefficient11 =
      row18_reducedY66_combinationStep07Coefficient11 +
        row18_reducedY66_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep08Coefficient11 row18_reducedY66_combinationStep07Coefficient11 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep08Coefficient12 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY66_combinationStep08CoefficientIdentity12 :
    row18_reducedY66_combinationStep08Coefficient12 =
      row18_reducedY66_combinationStep07Coefficient12 +
        row18_reducedY66_combinationStep08Multiplier *
          (((5 / 316) : ℂ) - ((3 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((33 / 158) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 + ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 + ((3 / 316) : ℂ) * ζ ^ 9 + ((33 / 316) : ℂ) * ζ ^ 11 + ((3 / 79) : ℂ) * ζ ^ 12 + ((3 / 316) : ℂ) * ζ ^ 13 + ((35 / 158) : ℂ) * ζ ^ 15 + ((3 / 316) : ℂ) * ζ ^ 17 + ((19 / 316) : ℂ) * ζ ^ 18 + ((45 / 158) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((1 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 - ((3 / 316) : ℂ) * ζ ^ 29 + ((13 / 79) : ℂ) * ζ ^ 30 - ((33 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep08Coefficient12 row18_reducedY66_combinationStep07Coefficient12 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 (-((5349 / 12482) : ℂ) + ((1914 / 6241) : ℂ) * ζ ^ 1 + ((383 / 12482) : ℂ) * ζ ^ 2 - ((4851 / 12482) : ℂ) * ζ ^ 3 + ((2378 / 6241) : ℂ) * ζ ^ 4 - ((4723 / 12482) : ℂ) * ζ ^ 5 + ((1406 / 6241) : ℂ) * ζ ^ 6 + ((7141 / 12482) : ℂ) * ζ ^ 7 - ((9817 / 12482) : ℂ) * ζ ^ 8 - ((3164 / 6241) : ℂ) * ζ ^ 9 - ((1412 / 6241) : ℂ) * ζ ^ 10 + ((213 / 6241) : ℂ) * ζ ^ 11 + ((499 / 12482) : ℂ) * ζ ^ 12 + ((4605 / 12482) : ℂ) * ζ ^ 13 - ((53 / 79) : ℂ) * ζ ^ 14 - ((819 / 12482) : ℂ) * ζ ^ 15 + ((448 / 6241) : ℂ) * ζ ^ 16 - ((3570 / 6241) : ℂ) * ζ ^ 17 + ((1671 / 12482) : ℂ) * ζ ^ 18 - ((523 / 12482) : ℂ) * ζ ^ 19 - ((1859 / 12482) : ℂ) * ζ ^ 20 - ((2261 / 12482) : ℂ) * ζ ^ 21 + ((387 / 12482) : ℂ) * ζ ^ 22 - ((50 / 79) : ℂ) * ζ ^ 23 + ((2033 / 6241) : ℂ) * ζ ^ 24 - ((325 / 6241) : ℂ) * ζ ^ 25 + ((1375 / 12482) : ℂ) * ζ ^ 26 - ((2164 / 6241) : ℂ) * ζ ^ 27 + ((241 / 12482) : ℂ) * ζ ^ 28 - ((3371 / 12482) : ℂ) * ζ ^ 29 + ((1122 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep08Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep08CoefficientIdentity13 :
    row18_reducedY66_combinationStep08Coefficient13 =
      row18_reducedY66_combinationStep07Coefficient13 +
        row18_reducedY66_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep08Coefficient13 row18_reducedY66_combinationStep07Coefficient13 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep08Coefficient14 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep08CoefficientIdentity14 :
    row18_reducedY66_combinationStep08Coefficient14 =
      row18_reducedY66_combinationStep07Coefficient14 +
        row18_reducedY66_combinationStep08Multiplier *
          (-((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((35 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep08Coefficient14 row18_reducedY66_combinationStep07Coefficient14 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 (-((495 / 6241) : ℂ) + ((757 / 12482) : ℂ) * ζ ^ 1 - ((1765 / 6241) : ℂ) * ζ ^ 2 + ((932 / 6241) : ℂ) * ζ ^ 3 + ((1581 / 6241) : ℂ) * ζ ^ 4 + ((657 / 6241) : ℂ) * ζ ^ 5 - ((2619 / 12482) : ℂ) * ζ ^ 6 - ((1737 / 6241) : ℂ) * ζ ^ 7 + ((81 / 6241) : ℂ) * ζ ^ 8 + ((476 / 6241) : ℂ) * ζ ^ 9 + ((761 / 12482) : ℂ) * ζ ^ 10 - ((427 / 12482) : ℂ) * ζ ^ 11 - ((2393 / 12482) : ℂ) * ζ ^ 12 - ((426 / 6241) : ℂ) * ζ ^ 13 - ((2665 / 12482) : ℂ) * ζ ^ 14 - ((866 / 6241) : ℂ) * ζ ^ 15 - ((218 / 6241) : ℂ) * ζ ^ 16 + ((1113 / 6241) : ℂ) * ζ ^ 17 - ((726 / 6241) : ℂ) * ζ ^ 18 - ((567 / 12482) : ℂ) * ζ ^ 19 - ((3575 / 12482) : ℂ) * ζ ^ 20 - ((244 / 6241) : ℂ) * ζ ^ 21 + ((713 / 12482) : ℂ) * ζ ^ 22 + ((1702 / 6241) : ℂ) * ζ ^ 23 - ((1353 / 6241) : ℂ) * ζ ^ 24 - ((321 / 12482) : ℂ) * ζ ^ 25 - ((1107 / 12482) : ℂ) * ζ ^ 26 + ((1061 / 12482) : ℂ) * ζ ^ 27 + ((341 / 6241) : ℂ) * ζ ^ 28 + ((373 / 6241) : ℂ) * ζ ^ 29 - ((476 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep08Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep08CoefficientIdentity15 :
    row18_reducedY66_combinationStep08Coefficient15 =
      row18_reducedY66_combinationStep07Coefficient15 +
        row18_reducedY66_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep08Coefficient15 row18_reducedY66_combinationStep07Coefficient15 row18_reducedY66_combinationStep08Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY66_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY66_combinationStep08Coefficient00) * Y 0 0
      + (row18_reducedY66_combinationStep08Coefficient01) * Y 0 1
      + (row18_reducedY66_combinationStep08Coefficient02) * Y 1 0
      + (row18_reducedY66_combinationStep08Coefficient03) * Y 1 1
      + (row18_reducedY66_combinationStep08Coefficient04) * Y 2 2
      + (row18_reducedY66_combinationStep08Coefficient05) * Y 2 3
      + (row18_reducedY66_combinationStep08Coefficient06) * Y 3 2
      + (row18_reducedY66_combinationStep08Coefficient07) * Y 3 3
      + (row18_reducedY66_combinationStep08Coefficient08) * Y 4 4
      + (row18_reducedY66_combinationStep08Coefficient09) * Y 4 5
      + (row18_reducedY66_combinationStep08Coefficient10) * Y 5 4
      + (row18_reducedY66_combinationStep08Coefficient11) * Y 5 5
      + (row18_reducedY66_combinationStep08Coefficient12) * Y 6 6
      + (row18_reducedY66_combinationStep08Coefficient13) * Y 6 7
      + (row18_reducedY66_combinationStep08Coefficient14) * Y 7 6
      + (row18_reducedY66_combinationStep08Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY66_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation16
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY66_combinationStep08CoefficientIdentity00,
      row18_reducedY66_combinationStep08CoefficientIdentity01,
      row18_reducedY66_combinationStep08CoefficientIdentity02,
      row18_reducedY66_combinationStep08CoefficientIdentity03,
      row18_reducedY66_combinationStep08CoefficientIdentity04,
      row18_reducedY66_combinationStep08CoefficientIdentity05,
      row18_reducedY66_combinationStep08CoefficientIdentity06,
      row18_reducedY66_combinationStep08CoefficientIdentity07,
      row18_reducedY66_combinationStep08CoefficientIdentity08,
      row18_reducedY66_combinationStep08CoefficientIdentity09,
      row18_reducedY66_combinationStep08CoefficientIdentity10,
      row18_reducedY66_combinationStep08CoefficientIdentity11,
      row18_reducedY66_combinationStep08CoefficientIdentity12,
      row18_reducedY66_combinationStep08CoefficientIdentity13,
      row18_reducedY66_combinationStep08CoefficientIdentity14,
      row18_reducedY66_combinationStep08CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY66_combinationStep08Multiplier * equation

private def row18_reducedY66_combinationStep09Multiplier : ℂ :=
  (-((208 / 79) : ℂ) - ((380 / 79) : ℂ) * ζ ^ 1 + ((60 / 79) : ℂ) * ζ ^ 2 - ((132 / 79) : ℂ) * ζ ^ 3 - ((306 / 79) : ℂ) * ζ ^ 5 + ((236 / 79) : ℂ) * ζ ^ 8 + ((156 / 79) : ℂ) * ζ ^ 9 - ((24 / 79) : ℂ) * ζ ^ 11 + ((180 / 79) : ℂ) * ζ ^ 12 + ((380 / 79) : ℂ) * ζ ^ 13 + ((58 / 79) : ℂ) * ζ ^ 15 + ((380 / 79) : ℂ) * ζ ^ 17 - ((60 / 79) : ℂ) * ζ ^ 18 + ((248 / 79) : ℂ) * ζ ^ 21 - ((60 / 79) : ℂ) * ζ ^ 22 - ((416 / 79) : ℂ) * ζ ^ 24 - ((74 / 79) : ℂ) * ζ ^ 25 + ((248 / 79) : ℂ) * ζ ^ 27 - ((236 / 79) : ℂ) * ζ ^ 28 - ((380 / 79) : ℂ) * ζ ^ 29 - ((160 / 79) : ℂ) * ζ ^ 30 + ((24 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY66_combinationStep09Coefficient00 : ℂ :=
  (((213 / 79) : ℂ) - ((1848 / 395) : ℂ) * ζ ^ 1 + ((7859 / 790) : ℂ) * ζ ^ 2 + ((1402 / 395) : ℂ) * ζ ^ 3 + ((1691 / 395) : ℂ) * ζ ^ 5 + ((4578 / 395) : ℂ) * ζ ^ 6 + ((1325 / 158) : ℂ) * ζ ^ 8 + ((4386 / 395) : ℂ) * ζ ^ 9 + ((2984 / 395) : ℂ) * ζ ^ 11 + ((1325 / 158) : ℂ) * ζ ^ 12 + ((1848 / 395) : ℂ) * ζ ^ 13 + ((2137 / 395) : ℂ) * ζ ^ 15 + ((1848 / 395) : ℂ) * ζ ^ 17 - ((1297 / 790) : ℂ) * ζ ^ 18 + ((446 / 395) : ℂ) * ζ ^ 21 - ((7859 / 790) : ℂ) * ζ ^ 22 - ((3539 / 395) : ℂ) * ζ ^ 25 - ((446 / 395) : ℂ) * ζ ^ 27 - ((1325 / 158) : ℂ) * ζ ^ 28 - ((1848 / 395) : ℂ) * ζ ^ 29 + ((2289 / 395) : ℂ) * ζ ^ 30 - ((2984 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep09CoefficientIdentity00 :
    row18_reducedY66_combinationStep09Coefficient00 =
      row18_reducedY66_combinationStep08Coefficient00 +
        row18_reducedY66_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep09Coefficient00 row18_reducedY66_combinationStep08Coefficient00 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep09Coefficient01 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep09CoefficientIdentity01 :
    row18_reducedY66_combinationStep09Coefficient01 =
      row18_reducedY66_combinationStep08Coefficient01 +
        row18_reducedY66_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep09Coefficient01 row18_reducedY66_combinationStep08Coefficient01 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep09Coefficient02 : ℂ :=
  (((1128 / 395) : ℂ) - ((523 / 395) : ℂ) * ζ ^ 1 - ((6687 / 790) : ℂ) * ζ ^ 2 + ((669 / 158) : ℂ) * ζ ^ 3 - ((3749 / 395) : ℂ) * ζ ^ 5 - ((3453 / 790) : ℂ) * ζ ^ 6 - ((4134 / 395) : ℂ) * ζ ^ 8 - ((2703 / 790) : ℂ) * ζ ^ 9 - ((1463 / 158) : ℂ) * ζ ^ 11 - ((1617 / 395) : ℂ) * ζ ^ 12 + ((523 / 395) : ℂ) * ζ ^ 13 - ((669 / 158) : ℂ) * ζ ^ 15 + ((523 / 395) : ℂ) * ζ ^ 17 + ((4431 / 790) : ℂ) * ζ ^ 18 + ((3226 / 395) : ℂ) * ζ ^ 21 + ((6687 / 790) : ℂ) * ζ ^ 22 + ((6687 / 790) : ℂ) * ζ ^ 24 + ((3226 / 395) : ℂ) * ζ ^ 25 + ((1463 / 158) : ℂ) * ζ ^ 27 + ((4134 / 395) : ℂ) * ζ ^ 28 - ((523 / 395) : ℂ) * ζ ^ 29 + ((1581 / 790) : ℂ) * ζ ^ 30 + ((1463 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep09CoefficientIdentity02 :
    row18_reducedY66_combinationStep09Coefficient02 =
      row18_reducedY66_combinationStep08Coefficient02 +
        row18_reducedY66_combinationStep09Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep09Coefficient02 row18_reducedY66_combinationStep08Coefficient02 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 (((4978 / 6241) : ℂ) + ((1363 / 6241) : ℂ) * ζ ^ 1 - ((2345 / 12482) : ℂ) * ζ ^ 2 + ((2043 / 12482) : ℂ) * ζ ^ 3 - ((2434 / 6241) : ℂ) * ζ ^ 4 + ((1310 / 6241) : ℂ) * ζ ^ 5 + ((10323 / 12482) : ℂ) * ζ ^ 6 + ((3050 / 6241) : ℂ) * ζ ^ 7 - ((2498 / 6241) : ℂ) * ζ ^ 8 - ((1739 / 12482) : ℂ) * ζ ^ 9 + ((5095 / 12482) : ℂ) * ζ ^ 10 - ((4917 / 12482) : ℂ) * ζ ^ 11 + ((4607 / 6241) : ℂ) * ζ ^ 12 - ((1753 / 6241) : ℂ) * ζ ^ 13 - ((2961 / 6241) : ℂ) * ζ ^ 14 + ((8021 / 12482) : ℂ) * ζ ^ 15 - ((347 / 6241) : ℂ) * ζ ^ 16 + ((1852 / 6241) : ℂ) * ζ ^ 17 + ((505 / 6241) : ℂ) * ζ ^ 18 - ((728 / 6241) : ℂ) * ζ ^ 19 + ((1667 / 6241) : ℂ) * ζ ^ 20 - ((6627 / 12482) : ℂ) * ζ ^ 21 - ((4319 / 12482) : ℂ) * ζ ^ 22 + ((92 / 6241) : ℂ) * ζ ^ 23 + ((4045 / 12482) : ℂ) * ζ ^ 24 + ((7860 / 6241) : ℂ) * ζ ^ 25 + ((13 / 6241) : ℂ) * ζ ^ 26 - ((3509 / 6241) : ℂ) * ζ ^ 27 - ((573 / 6241) : ℂ) * ζ ^ 28 + ((888 / 6241) : ℂ) * ζ ^ 29 - ((90 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep09Coefficient03 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep09CoefficientIdentity03 :
    row18_reducedY66_combinationStep09Coefficient03 =
      row18_reducedY66_combinationStep08Coefficient03 +
        row18_reducedY66_combinationStep09Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep09Coefficient03 row18_reducedY66_combinationStep08Coefficient03 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 (-((4466 / 6241) : ℂ) - ((3988 / 6241) : ℂ) * ζ ^ 1 - ((6751 / 12482) : ℂ) * ζ ^ 2 - ((1189 / 12482) : ℂ) * ζ ^ 3 + ((4723 / 6241) : ℂ) * ζ ^ 4 + ((1569 / 12482) : ℂ) * ζ ^ 5 - ((125 / 6241) : ℂ) * ζ ^ 6 - ((1633 / 6241) : ℂ) * ζ ^ 7 - ((4183 / 6241) : ℂ) * ζ ^ 8 + ((5487 / 6241) : ℂ) * ζ ^ 9 + ((1469 / 6241) : ℂ) * ζ ^ 10 + ((2829 / 6241) : ℂ) * ζ ^ 11 + ((1961 / 12482) : ℂ) * ζ ^ 12 - ((293 / 6241) : ℂ) * ζ ^ 13 + ((139 / 6241) : ℂ) * ζ ^ 14 + ((2645 / 12482) : ℂ) * ζ ^ 15 - ((191 / 6241) : ℂ) * ζ ^ 16 + ((3653 / 6241) : ℂ) * ζ ^ 17 + ((2886 / 6241) : ℂ) * ζ ^ 18 + ((3632 / 6241) : ℂ) * ζ ^ 19 - ((3885 / 6241) : ℂ) * ζ ^ 20 - ((2547 / 6241) : ℂ) * ζ ^ 21 + ((2357 / 12482) : ℂ) * ζ ^ 22 + ((3984 / 6241) : ℂ) * ζ ^ 23 + ((697 / 6241) : ℂ) * ζ ^ 24 - ((627 / 6241) : ℂ) * ζ ^ 25 - ((2849 / 6241) : ℂ) * ζ ^ 26 - ((718 / 6241) : ℂ) * ζ ^ 27 + ((916 / 6241) : ℂ) * ζ ^ 28 + ((8 / 79) : ℂ) * ζ ^ 29 - ((84 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep09Coefficient04 : ℂ :=
  (-((213 / 79) : ℂ) + ((1848 / 395) : ℂ) * ζ ^ 1 - ((7859 / 790) : ℂ) * ζ ^ 2 - ((1402 / 395) : ℂ) * ζ ^ 3 - ((1691 / 395) : ℂ) * ζ ^ 5 - ((4578 / 395) : ℂ) * ζ ^ 6 - ((1325 / 158) : ℂ) * ζ ^ 8 - ((4386 / 395) : ℂ) * ζ ^ 9 - ((2984 / 395) : ℂ) * ζ ^ 11 - ((1325 / 158) : ℂ) * ζ ^ 12 - ((1848 / 395) : ℂ) * ζ ^ 13 - ((2137 / 395) : ℂ) * ζ ^ 15 - ((1848 / 395) : ℂ) * ζ ^ 17 + ((1297 / 790) : ℂ) * ζ ^ 18 - ((446 / 395) : ℂ) * ζ ^ 21 + ((7859 / 790) : ℂ) * ζ ^ 22 + ((3539 / 395) : ℂ) * ζ ^ 25 + ((446 / 395) : ℂ) * ζ ^ 27 + ((1325 / 158) : ℂ) * ζ ^ 28 + ((1848 / 395) : ℂ) * ζ ^ 29 - ((2289 / 395) : ℂ) * ζ ^ 30 + ((2984 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep09CoefficientIdentity04 :
    row18_reducedY66_combinationStep09Coefficient04 =
      row18_reducedY66_combinationStep08Coefficient04 +
        row18_reducedY66_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep09Coefficient04 row18_reducedY66_combinationStep08Coefficient04 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep09Coefficient05 : ℂ :=
  (-((32 / 79) : ℂ) + ((213 / 79) : ℂ) * ζ ^ 1 - ((1195 / 158) : ℂ) * ζ ^ 2 - ((748 / 79) : ℂ) * ζ ^ 5 - ((1131 / 158) : ℂ) * ζ ^ 6 - ((1131 / 158) : ℂ) * ζ ^ 8 - ((748 / 79) : ℂ) * ζ ^ 9 - ((1665 / 158) : ℂ) * ζ ^ 11 - ((382 / 79) : ℂ) * ζ ^ 12 - ((213 / 79) : ℂ) * ζ ^ 13 - ((482 / 79) : ℂ) * ζ ^ 15 - ((213 / 79) : ℂ) * ζ ^ 17 + ((235 / 79) : ℂ) * ζ ^ 18 + ((535 / 158) : ℂ) * ζ ^ 21 + ((1195 / 158) : ℂ) * ζ ^ 22 + ((661 / 158) : ℂ) * ζ ^ 24 + ((961 / 79) : ℂ) * ζ ^ 25 + ((482 / 79) : ℂ) * ζ ^ 27 + ((1131 / 158) : ℂ) * ζ ^ 28 + ((213 / 79) : ℂ) * ζ ^ 29 - ((367 / 158) : ℂ) * ζ ^ 30 + ((1665 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY66_combinationStep09CoefficientIdentity05 :
    row18_reducedY66_combinationStep09Coefficient05 =
      row18_reducedY66_combinationStep08Coefficient05 +
        row18_reducedY66_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep09Coefficient05 row18_reducedY66_combinationStep08Coefficient05 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep09Coefficient06 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep09CoefficientIdentity06 :
    row18_reducedY66_combinationStep09Coefficient06 =
      row18_reducedY66_combinationStep08Coefficient06 +
        row18_reducedY66_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep09Coefficient06 row18_reducedY66_combinationStep08Coefficient06 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep09Coefficient07 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep09CoefficientIdentity07 :
    row18_reducedY66_combinationStep09Coefficient07 =
      row18_reducedY66_combinationStep08Coefficient07 +
        row18_reducedY66_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep09Coefficient07 row18_reducedY66_combinationStep08Coefficient07 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep09Coefficient08 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep09CoefficientIdentity08 :
    row18_reducedY66_combinationStep09Coefficient08 =
      row18_reducedY66_combinationStep08Coefficient08 +
        row18_reducedY66_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep09Coefficient08 row18_reducedY66_combinationStep08Coefficient08 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep09Coefficient09 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep09CoefficientIdentity09 :
    row18_reducedY66_combinationStep09Coefficient09 =
      row18_reducedY66_combinationStep08Coefficient09 +
        row18_reducedY66_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep09Coefficient09 row18_reducedY66_combinationStep08Coefficient09 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep09Coefficient10 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep09CoefficientIdentity10 :
    row18_reducedY66_combinationStep09Coefficient10 =
      row18_reducedY66_combinationStep08Coefficient10 +
        row18_reducedY66_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep09Coefficient10 row18_reducedY66_combinationStep08Coefficient10 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep09Coefficient11 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep09CoefficientIdentity11 :
    row18_reducedY66_combinationStep09Coefficient11 =
      row18_reducedY66_combinationStep08Coefficient11 +
        row18_reducedY66_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep09Coefficient11 row18_reducedY66_combinationStep08Coefficient11 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep09Coefficient12 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY66_combinationStep09CoefficientIdentity12 :
    row18_reducedY66_combinationStep09Coefficient12 =
      row18_reducedY66_combinationStep08Coefficient12 +
        row18_reducedY66_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep09Coefficient12 row18_reducedY66_combinationStep08Coefficient12 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep09Coefficient13 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep09CoefficientIdentity13 :
    row18_reducedY66_combinationStep09Coefficient13 =
      row18_reducedY66_combinationStep08Coefficient13 +
        row18_reducedY66_combinationStep09Multiplier *
          (((5 / 316) : ℂ) - ((3 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((33 / 158) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 + ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 + ((3 / 316) : ℂ) * ζ ^ 9 + ((33 / 316) : ℂ) * ζ ^ 11 + ((3 / 79) : ℂ) * ζ ^ 12 + ((3 / 316) : ℂ) * ζ ^ 13 + ((35 / 158) : ℂ) * ζ ^ 15 + ((3 / 316) : ℂ) * ζ ^ 17 + ((19 / 316) : ℂ) * ζ ^ 18 + ((45 / 158) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((1 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 - ((3 / 316) : ℂ) * ζ ^ 29 + ((13 / 79) : ℂ) * ζ ^ 30 - ((33 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep09Coefficient13 row18_reducedY66_combinationStep08Coefficient13 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 (((3058 / 6241) : ℂ) + ((392 / 6241) : ℂ) * ζ ^ 1 - ((2841 / 12482) : ℂ) * ζ ^ 2 - ((103 / 6241) : ℂ) * ζ ^ 3 + ((3836 / 6241) : ℂ) * ζ ^ 4 - ((4895 / 12482) : ℂ) * ζ ^ 5 - ((2491 / 12482) : ℂ) * ζ ^ 6 - ((12839 / 12482) : ℂ) * ζ ^ 7 + ((2017 / 12482) : ℂ) * ζ ^ 8 + ((10211 / 12482) : ℂ) * ζ ^ 9 + ((2538 / 6241) : ℂ) * ζ ^ 10 - ((1486 / 6241) : ℂ) * ζ ^ 11 - ((24711 / 12482) : ℂ) * ζ ^ 12 - ((6425 / 12482) : ℂ) * ζ ^ 13 - ((1453 / 6241) : ℂ) * ζ ^ 14 + ((5079 / 12482) : ℂ) * ζ ^ 15 + ((2641 / 12482) : ℂ) * ζ ^ 16 - ((707 / 12482) : ℂ) * ζ ^ 17 - ((12423 / 12482) : ℂ) * ζ ^ 18 - ((1465 / 6241) : ℂ) * ζ ^ 19 - ((10497 / 12482) : ℂ) * ζ ^ 20 - ((3557 / 6241) : ℂ) * ζ ^ 21 - ((2515 / 12482) : ℂ) * ζ ^ 22 + ((7701 / 6241) : ℂ) * ζ ^ 23 - ((6705 / 12482) : ℂ) * ζ ^ 24 - ((2191 / 6241) : ℂ) * ζ ^ 25 - ((6207 / 6241) : ℂ) * ζ ^ 26 - ((2633 / 6241) : ℂ) * ζ ^ 27 + ((1037 / 6241) : ℂ) * ζ ^ 28 + ((1632 / 6241) : ℂ) * ζ ^ 29 - ((198 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep09Coefficient14 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep09CoefficientIdentity14 :
    row18_reducedY66_combinationStep09Coefficient14 =
      row18_reducedY66_combinationStep08Coefficient14 +
        row18_reducedY66_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep09Coefficient14 row18_reducedY66_combinationStep08Coefficient14 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep09Coefficient15 : ℂ :=
  (-(1 : ℂ))

private theorem row18_reducedY66_combinationStep09CoefficientIdentity15 :
    row18_reducedY66_combinationStep09Coefficient15 =
      row18_reducedY66_combinationStep08Coefficient15 +
        row18_reducedY66_combinationStep09Multiplier *
          (-((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((35 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep09Coefficient15 row18_reducedY66_combinationStep08Coefficient15 row18_reducedY66_combinationStep09Multiplier
  close_cyclotomic_row18 (((4466 / 6241) : ℂ) + ((3988 / 6241) : ℂ) * ζ ^ 1 + ((6751 / 12482) : ℂ) * ζ ^ 2 + ((1189 / 12482) : ℂ) * ζ ^ 3 - ((4723 / 6241) : ℂ) * ζ ^ 4 - ((1569 / 12482) : ℂ) * ζ ^ 5 + ((125 / 6241) : ℂ) * ζ ^ 6 + ((1633 / 6241) : ℂ) * ζ ^ 7 + ((4183 / 6241) : ℂ) * ζ ^ 8 - ((5487 / 6241) : ℂ) * ζ ^ 9 - ((1469 / 6241) : ℂ) * ζ ^ 10 - ((2829 / 6241) : ℂ) * ζ ^ 11 - ((1961 / 12482) : ℂ) * ζ ^ 12 + ((293 / 6241) : ℂ) * ζ ^ 13 - ((139 / 6241) : ℂ) * ζ ^ 14 - ((2645 / 12482) : ℂ) * ζ ^ 15 + ((191 / 6241) : ℂ) * ζ ^ 16 - ((3653 / 6241) : ℂ) * ζ ^ 17 - ((2886 / 6241) : ℂ) * ζ ^ 18 - ((3632 / 6241) : ℂ) * ζ ^ 19 + ((3885 / 6241) : ℂ) * ζ ^ 20 + ((2547 / 6241) : ℂ) * ζ ^ 21 - ((2357 / 12482) : ℂ) * ζ ^ 22 - ((3984 / 6241) : ℂ) * ζ ^ 23 - ((697 / 6241) : ℂ) * ζ ^ 24 + ((627 / 6241) : ℂ) * ζ ^ 25 + ((2849 / 6241) : ℂ) * ζ ^ 26 + ((718 / 6241) : ℂ) * ζ ^ 27 - ((916 / 6241) : ℂ) * ζ ^ 28 - ((8 / 79) : ℂ) * ζ ^ 29 + ((84 / 6241) : ℂ) * ζ ^ 30)

private theorem row18_reducedY66_combinationStep09
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY66_combinationStep09Coefficient00) * Y 0 0
      + (row18_reducedY66_combinationStep09Coefficient01) * Y 0 1
      + (row18_reducedY66_combinationStep09Coefficient02) * Y 1 0
      + (row18_reducedY66_combinationStep09Coefficient03) * Y 1 1
      + (row18_reducedY66_combinationStep09Coefficient04) * Y 2 2
      + (row18_reducedY66_combinationStep09Coefficient05) * Y 2 3
      + (row18_reducedY66_combinationStep09Coefficient06) * Y 3 2
      + (row18_reducedY66_combinationStep09Coefficient07) * Y 3 3
      + (row18_reducedY66_combinationStep09Coefficient08) * Y 4 4
      + (row18_reducedY66_combinationStep09Coefficient09) * Y 4 5
      + (row18_reducedY66_combinationStep09Coefficient10) * Y 5 4
      + (row18_reducedY66_combinationStep09Coefficient11) * Y 5 5
      + (row18_reducedY66_combinationStep09Coefficient12) * Y 6 6
      + (row18_reducedY66_combinationStep09Coefficient13) * Y 6 7
      + (row18_reducedY66_combinationStep09Coefficient14) * Y 7 6
      + (row18_reducedY66_combinationStep09Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY66_combinationStep08 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation17
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY66_combinationStep09CoefficientIdentity00,
      row18_reducedY66_combinationStep09CoefficientIdentity01,
      row18_reducedY66_combinationStep09CoefficientIdentity02,
      row18_reducedY66_combinationStep09CoefficientIdentity03,
      row18_reducedY66_combinationStep09CoefficientIdentity04,
      row18_reducedY66_combinationStep09CoefficientIdentity05,
      row18_reducedY66_combinationStep09CoefficientIdentity06,
      row18_reducedY66_combinationStep09CoefficientIdentity07,
      row18_reducedY66_combinationStep09CoefficientIdentity08,
      row18_reducedY66_combinationStep09CoefficientIdentity09,
      row18_reducedY66_combinationStep09CoefficientIdentity10,
      row18_reducedY66_combinationStep09CoefficientIdentity11,
      row18_reducedY66_combinationStep09CoefficientIdentity12,
      row18_reducedY66_combinationStep09CoefficientIdentity13,
      row18_reducedY66_combinationStep09CoefficientIdentity14,
      row18_reducedY66_combinationStep09CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY66_combinationStep09Multiplier * equation

private def row18_reducedY66_combinationStep10Multiplier : ℂ :=
  (((864 / 79) : ℂ) - ((2044 / 395) : ℂ) * ζ ^ 1 + ((7532 / 395) : ℂ) * ζ ^ 2 + ((1036 / 395) : ℂ) * ζ ^ 3 + ((4378 / 395) : ℂ) * ζ ^ 5 + ((10888 / 395) : ℂ) * ζ ^ 6 + ((956 / 79) : ℂ) * ζ ^ 8 + ((7688 / 395) : ℂ) * ζ ^ 9 + ((6652 / 395) : ℂ) * ζ ^ 11 + ((956 / 79) : ℂ) * ζ ^ 12 + ((2044 / 395) : ℂ) * ζ ^ 13 + ((5386 / 395) : ℂ) * ζ ^ 15 + ((2044 / 395) : ℂ) * ζ ^ 17 - ((3356 / 395) : ℂ) * ζ ^ 18 + ((1008 / 395) : ℂ) * ζ ^ 21 - ((7532 / 395) : ℂ) * ζ ^ 22 - ((6422 / 395) : ℂ) * ζ ^ 25 - ((1008 / 395) : ℂ) * ζ ^ 27 - ((956 / 79) : ℂ) * ζ ^ 28 - ((2044 / 395) : ℂ) * ζ ^ 29 + ((5444 / 395) : ℂ) * ζ ^ 30 - ((6652 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY66_combinationStep10Coefficient00 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep10CoefficientIdentity00 :
    row18_reducedY66_combinationStep10Coefficient00 =
      row18_reducedY66_combinationStep09Coefficient00 +
        row18_reducedY66_combinationStep10Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep10Coefficient00 row18_reducedY66_combinationStep09Coefficient00 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 (((19419 / 6241) : ℂ) - ((2076 / 395) : ℂ) * ζ ^ 1 + ((98739 / 12482) : ℂ) * ζ ^ 2 + ((135508 / 31205) : ℂ) * ζ ^ 3 - ((259488 / 31205) : ℂ) * ζ ^ 4 + ((254429 / 31205) : ℂ) * ζ ^ 5 + ((23190 / 6241) : ℂ) * ζ ^ 6 - ((597241 / 62410) : ℂ) * ζ ^ 7 + ((39445 / 6241) : ℂ) * ζ ^ 8 + ((122899 / 31205) : ℂ) * ζ ^ 9 - ((68810 / 6241) : ℂ) * ζ ^ 10 + ((121439 / 12482) : ℂ) * ζ ^ 11 + ((53983 / 62410) : ℂ) * ζ ^ 12 - ((614619 / 62410) : ℂ) * ζ ^ 13 + ((237197 / 31205) : ℂ) * ζ ^ 14 - ((123297 / 62410) : ℂ) * ζ ^ 15 - ((269052 / 31205) : ℂ) * ζ ^ 16 + ((544783 / 62410) : ℂ) * ζ ^ 17 - ((122004 / 31205) : ℂ) * ζ ^ 18 - ((115759 / 31205) : ℂ) * ζ ^ 19 + ((182519 / 31205) : ℂ) * ζ ^ 20 - ((338593 / 62410) : ℂ) * ζ ^ 21 - ((24641 / 12482) : ℂ) * ζ ^ 22 + ((105337 / 31205) : ℂ) * ζ ^ 23 - ((45712 / 31205) : ℂ) * ζ ^ 24 - ((24594 / 31205) : ℂ) * ζ ^ 25 + ((72578 / 31205) : ℂ) * ζ ^ 26 - ((9654 / 6241) : ℂ) * ζ ^ 27 + ((3671 / 31205) : ℂ) * ζ ^ 28 + ((7554 / 31205) : ℂ) * ζ ^ 29 + ((23282 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep10Coefficient01 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep10CoefficientIdentity01 :
    row18_reducedY66_combinationStep10Coefficient01 =
      row18_reducedY66_combinationStep09Coefficient01 +
        row18_reducedY66_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep10Coefficient01 row18_reducedY66_combinationStep09Coefficient01 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep10Coefficient02 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep10CoefficientIdentity02 :
    row18_reducedY66_combinationStep10Coefficient02 =
      row18_reducedY66_combinationStep09Coefficient02 +
        row18_reducedY66_combinationStep10Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep10Coefficient02 row18_reducedY66_combinationStep09Coefficient02 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 (((48072 / 31205) : ℂ) - ((64019 / 31205) : ℂ) * ζ ^ 1 - ((607763 / 62410) : ℂ) * ζ ^ 2 - ((24613 / 12482) : ℂ) * ζ ^ 3 + ((12107 / 31205) : ℂ) * ζ ^ 4 - ((101077 / 6241) : ℂ) * ζ ^ 5 + ((114983 / 62410) : ℂ) * ζ ^ 6 - ((140344 / 31205) : ℂ) * ζ ^ 7 - ((138007 / 12482) : ℂ) * ζ ^ 8 + ((19597 / 62410) : ℂ) * ζ ^ 9 - ((136817 / 62410) : ℂ) * ζ ^ 10 - ((106305 / 12482) : ℂ) * ζ ^ 11 - ((5371 / 62410) : ℂ) * ζ ^ 12 + ((27806 / 6241) : ℂ) * ζ ^ 13 - ((639321 / 62410) : ℂ) * ζ ^ 14 + ((378119 / 62410) : ℂ) * ζ ^ 15 + ((3937 / 31205) : ℂ) * ζ ^ 16 - ((112973 / 31205) : ℂ) * ζ ^ 17 + ((189003 / 31205) : ℂ) * ζ ^ 18 + ((5815 / 6241) : ℂ) * ζ ^ 19 - ((15682 / 31205) : ℂ) * ζ ^ 20 + ((514059 / 62410) : ℂ) * ζ ^ 21 + ((92109 / 62410) : ℂ) * ζ ^ 22 + ((52908 / 31205) : ℂ) * ζ ^ 23 + ((200699 / 31205) : ℂ) * ζ ^ 24 + ((9026 / 31205) : ℂ) * ζ ^ 25 + ((18158 / 31205) : ℂ) * ζ ^ 26 + ((169946 / 31205) : ℂ) * ζ ^ 27 + ((42453 / 31205) : ℂ) * ζ ^ 28 - ((6900 / 6241) : ℂ) * ζ ^ 29 + ((139692 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep10Coefficient03 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep10CoefficientIdentity03 :
    row18_reducedY66_combinationStep10Coefficient03 =
      row18_reducedY66_combinationStep09Coefficient03 +
        row18_reducedY66_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep10Coefficient03 row18_reducedY66_combinationStep09Coefficient03 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep10Coefficient04 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep10CoefficientIdentity04 :
    row18_reducedY66_combinationStep10Coefficient04 =
      row18_reducedY66_combinationStep09Coefficient04 +
        row18_reducedY66_combinationStep10Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep10Coefficient04 row18_reducedY66_combinationStep09Coefficient04 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 (-((19419 / 6241) : ℂ) + ((2076 / 395) : ℂ) * ζ ^ 1 - ((98739 / 12482) : ℂ) * ζ ^ 2 - ((135508 / 31205) : ℂ) * ζ ^ 3 + ((259488 / 31205) : ℂ) * ζ ^ 4 - ((254429 / 31205) : ℂ) * ζ ^ 5 - ((23190 / 6241) : ℂ) * ζ ^ 6 + ((597241 / 62410) : ℂ) * ζ ^ 7 - ((39445 / 6241) : ℂ) * ζ ^ 8 - ((122899 / 31205) : ℂ) * ζ ^ 9 + ((68810 / 6241) : ℂ) * ζ ^ 10 - ((121439 / 12482) : ℂ) * ζ ^ 11 - ((53983 / 62410) : ℂ) * ζ ^ 12 + ((614619 / 62410) : ℂ) * ζ ^ 13 - ((237197 / 31205) : ℂ) * ζ ^ 14 + ((123297 / 62410) : ℂ) * ζ ^ 15 + ((269052 / 31205) : ℂ) * ζ ^ 16 - ((544783 / 62410) : ℂ) * ζ ^ 17 + ((122004 / 31205) : ℂ) * ζ ^ 18 + ((115759 / 31205) : ℂ) * ζ ^ 19 - ((182519 / 31205) : ℂ) * ζ ^ 20 + ((338593 / 62410) : ℂ) * ζ ^ 21 + ((24641 / 12482) : ℂ) * ζ ^ 22 - ((105337 / 31205) : ℂ) * ζ ^ 23 + ((45712 / 31205) : ℂ) * ζ ^ 24 + ((24594 / 31205) : ℂ) * ζ ^ 25 - ((72578 / 31205) : ℂ) * ζ ^ 26 + ((9654 / 6241) : ℂ) * ζ ^ 27 - ((3671 / 31205) : ℂ) * ζ ^ 28 - ((7554 / 31205) : ℂ) * ζ ^ 29 - ((23282 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep10Coefficient05 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep10CoefficientIdentity05 :
    row18_reducedY66_combinationStep10Coefficient05 =
      row18_reducedY66_combinationStep09Coefficient05 +
        row18_reducedY66_combinationStep10Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY66_combinationStep10Coefficient05 row18_reducedY66_combinationStep09Coefficient05 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 (((12376 / 6241) : ℂ) + ((29436 / 31205) : ℂ) * ζ ^ 1 - ((42643 / 12482) : ℂ) * ζ ^ 2 - ((11424 / 31205) : ℂ) * ζ ^ 3 - ((83489 / 31205) : ℂ) * ζ ^ 4 - ((520693 / 62410) : ℂ) * ζ ^ 5 - ((5760 / 6241) : ℂ) * ζ ^ 6 - ((45257 / 62410) : ℂ) * ζ ^ 7 - ((126045 / 12482) : ℂ) * ζ ^ 8 + ((174021 / 62410) : ℂ) * ζ ^ 9 - ((168093 / 31205) : ℂ) * ζ ^ 10 - ((156773 / 31205) : ℂ) * ζ ^ 11 - ((107329 / 62410) : ℂ) * ζ ^ 12 + ((265571 / 62410) : ℂ) * ζ ^ 13 - ((591791 / 62410) : ℂ) * ζ ^ 14 - ((17891 / 62410) : ℂ) * ζ ^ 15 + ((119083 / 62410) : ℂ) * ζ ^ 16 - ((160507 / 62410) : ℂ) * ζ ^ 17 - ((708 / 6241) : ℂ) * ζ ^ 18 + ((26953 / 6241) : ℂ) * ζ ^ 19 - ((336453 / 62410) : ℂ) * ζ ^ 20 + ((115132 / 31205) : ℂ) * ζ ^ 21 + ((150127 / 31205) : ℂ) * ζ ^ 22 - ((131373 / 31205) : ℂ) * ζ ^ 23 + ((211961 / 31205) : ℂ) * ζ ^ 24 + ((34753 / 31205) : ℂ) * ζ ^ 25 + ((67261 / 31205) : ℂ) * ζ ^ 26 + ((88482 / 31205) : ℂ) * ζ ^ 27 + ((9684 / 6241) : ℂ) * ζ ^ 28 - ((155178 / 31205) : ℂ) * ζ ^ 29 + ((59868 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY66_combinationStep10Coefficient06 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep10CoefficientIdentity06 :
    row18_reducedY66_combinationStep10Coefficient06 =
      row18_reducedY66_combinationStep09Coefficient06 +
        row18_reducedY66_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep10Coefficient06 row18_reducedY66_combinationStep09Coefficient06 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep10Coefficient07 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep10CoefficientIdentity07 :
    row18_reducedY66_combinationStep10Coefficient07 =
      row18_reducedY66_combinationStep09Coefficient07 +
        row18_reducedY66_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep10Coefficient07 row18_reducedY66_combinationStep09Coefficient07 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep10Coefficient08 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep10CoefficientIdentity08 :
    row18_reducedY66_combinationStep10Coefficient08 =
      row18_reducedY66_combinationStep09Coefficient08 +
        row18_reducedY66_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep10Coefficient08 row18_reducedY66_combinationStep09Coefficient08 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep10Coefficient09 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep10CoefficientIdentity09 :
    row18_reducedY66_combinationStep10Coefficient09 =
      row18_reducedY66_combinationStep09Coefficient09 +
        row18_reducedY66_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep10Coefficient09 row18_reducedY66_combinationStep09Coefficient09 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep10Coefficient10 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep10CoefficientIdentity10 :
    row18_reducedY66_combinationStep10Coefficient10 =
      row18_reducedY66_combinationStep09Coefficient10 +
        row18_reducedY66_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep10Coefficient10 row18_reducedY66_combinationStep09Coefficient10 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep10Coefficient11 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep10CoefficientIdentity11 :
    row18_reducedY66_combinationStep10Coefficient11 =
      row18_reducedY66_combinationStep09Coefficient11 +
        row18_reducedY66_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep10Coefficient11 row18_reducedY66_combinationStep09Coefficient11 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep10Coefficient12 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY66_combinationStep10CoefficientIdentity12 :
    row18_reducedY66_combinationStep10Coefficient12 =
      row18_reducedY66_combinationStep09Coefficient12 +
        row18_reducedY66_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep10Coefficient12 row18_reducedY66_combinationStep09Coefficient12 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep10Coefficient13 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep10CoefficientIdentity13 :
    row18_reducedY66_combinationStep10Coefficient13 =
      row18_reducedY66_combinationStep09Coefficient13 +
        row18_reducedY66_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep10Coefficient13 row18_reducedY66_combinationStep09Coefficient13 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep10Coefficient14 : ℂ :=
  0

private theorem row18_reducedY66_combinationStep10CoefficientIdentity14 :
    row18_reducedY66_combinationStep10Coefficient14 =
      row18_reducedY66_combinationStep09Coefficient14 +
        row18_reducedY66_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep10Coefficient14 row18_reducedY66_combinationStep09Coefficient14 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY66_combinationStep10Coefficient15 : ℂ :=
  (-(1 : ℂ))

private theorem row18_reducedY66_combinationStep10CoefficientIdentity15 :
    row18_reducedY66_combinationStep10Coefficient15 =
      row18_reducedY66_combinationStep09Coefficient15 +
        row18_reducedY66_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY66_combinationStep10Coefficient15 row18_reducedY66_combinationStep09Coefficient15 row18_reducedY66_combinationStep10Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY66_combinationStep10
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY66_combinationStep10Coefficient00) * Y 0 0
      + (row18_reducedY66_combinationStep10Coefficient01) * Y 0 1
      + (row18_reducedY66_combinationStep10Coefficient02) * Y 1 0
      + (row18_reducedY66_combinationStep10Coefficient03) * Y 1 1
      + (row18_reducedY66_combinationStep10Coefficient04) * Y 2 2
      + (row18_reducedY66_combinationStep10Coefficient05) * Y 2 3
      + (row18_reducedY66_combinationStep10Coefficient06) * Y 3 2
      + (row18_reducedY66_combinationStep10Coefficient07) * Y 3 3
      + (row18_reducedY66_combinationStep10Coefficient08) * Y 4 4
      + (row18_reducedY66_combinationStep10Coefficient09) * Y 4 5
      + (row18_reducedY66_combinationStep10Coefficient10) * Y 5 4
      + (row18_reducedY66_combinationStep10Coefficient11) * Y 5 5
      + (row18_reducedY66_combinationStep10Coefficient12) * Y 6 6
      + (row18_reducedY66_combinationStep10Coefficient13) * Y 6 7
      + (row18_reducedY66_combinationStep10Coefficient14) * Y 7 6
      + (row18_reducedY66_combinationStep10Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY66_combinationStep09 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY66_combinationStep10CoefficientIdentity00,
      row18_reducedY66_combinationStep10CoefficientIdentity01,
      row18_reducedY66_combinationStep10CoefficientIdentity02,
      row18_reducedY66_combinationStep10CoefficientIdentity03,
      row18_reducedY66_combinationStep10CoefficientIdentity04,
      row18_reducedY66_combinationStep10CoefficientIdentity05,
      row18_reducedY66_combinationStep10CoefficientIdentity06,
      row18_reducedY66_combinationStep10CoefficientIdentity07,
      row18_reducedY66_combinationStep10CoefficientIdentity08,
      row18_reducedY66_combinationStep10CoefficientIdentity09,
      row18_reducedY66_combinationStep10CoefficientIdentity10,
      row18_reducedY66_combinationStep10CoefficientIdentity11,
      row18_reducedY66_combinationStep10CoefficientIdentity12,
      row18_reducedY66_combinationStep10CoefficientIdentity13,
      row18_reducedY66_combinationStep10CoefficientIdentity14,
      row18_reducedY66_combinationStep10CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY66_combinationStep10Multiplier * equation

theorem row18_reducedY66
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 6 6 = Y 7 7 := by
  have reduced :=
    row18_reducedY66_combinationStep10 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY66_combinationStep10Coefficient00,
      row18_reducedY66_combinationStep10Coefficient01,
      row18_reducedY66_combinationStep10Coefficient02,
      row18_reducedY66_combinationStep10Coefficient03,
      row18_reducedY66_combinationStep10Coefficient04,
      row18_reducedY66_combinationStep10Coefficient05,
      row18_reducedY66_combinationStep10Coefficient06,
      row18_reducedY66_combinationStep10Coefficient07,
      row18_reducedY66_combinationStep10Coefficient08,
      row18_reducedY66_combinationStep10Coefficient09,
      row18_reducedY66_combinationStep10Coefficient10,
      row18_reducedY66_combinationStep10Coefficient11,
      row18_reducedY66_combinationStep10Coefficient12,
      row18_reducedY66_combinationStep10Coefficient13,
      row18_reducedY66_combinationStep10Coefficient14,
      row18_reducedY66_combinationStep10Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
