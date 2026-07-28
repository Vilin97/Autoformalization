/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction12

/-!
# Ambient row 18 commutant reduction 13

This generated module checks the reduced relation `reducedY67` for
matrix coordinate (6, 7).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY67_combinationStep00Multiplier : ℂ :=
  (-((1232 / 237) : ℂ) + ((6926 / 1185) : ℂ) * ζ ^ 1 + ((7432 / 237) : ℂ) * ζ ^ 2 - ((4864 / 237) : ℂ) * ζ ^ 3 + ((45788 / 1185) : ℂ) * ζ ^ 5 + ((3622 / 237) : ℂ) * ζ ^ 6 + ((8566 / 237) : ℂ) * ζ ^ 8 + ((15968 / 1185) : ℂ) * ζ ^ 9 + ((12218 / 237) : ℂ) * ζ ^ 11 + ((1270 / 79) : ℂ) * ζ ^ 12 - ((6926 / 1185) : ℂ) * ζ ^ 13 + ((4864 / 237) : ℂ) * ζ ^ 15 - ((6926 / 1185) : ℂ) * ζ ^ 17 - ((6200 / 237) : ℂ) * ζ ^ 18 - ((12954 / 395) : ℂ) * ζ ^ 21 - ((7432 / 237) : ℂ) * ζ ^ 22 - ((7432 / 237) : ℂ) * ζ ^ 24 - ((12954 / 395) : ℂ) * ζ ^ 25 - ((12218 / 237) : ℂ) * ζ ^ 27 - ((8566 / 237) : ℂ) * ζ ^ 28 + ((6926 / 1185) : ℂ) * ζ ^ 29 - ((378 / 79) : ℂ) * ζ ^ 30 - ((12218 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY67_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep00CoefficientIdentity00 :
    row18_reducedY67_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep00Coefficient00 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep00Coefficient01 : ℂ :=
  (((1993 / 474) : ℂ) + ((86 / 79) : ℂ) * ζ ^ 1 + ((1759 / 474) : ℂ) * ζ ^ 2 + ((279 / 158) : ℂ) * ζ ^ 3 - ((1963 / 474) : ℂ) * ζ ^ 5 - ((485 / 79) : ℂ) * ζ ^ 8 - ((1009 / 237) : ℂ) * ζ ^ 9 + ((1181 / 474) : ℂ) * ζ ^ 11 - ((538 / 237) : ℂ) * ζ ^ 12 - ((86 / 79) : ℂ) * ζ ^ 13 + ((821 / 237) : ℂ) * ζ ^ 15 - ((86 / 79) : ℂ) * ζ ^ 17 - ((1759 / 474) : ℂ) * ζ ^ 18 + ((107 / 158) : ℂ) * ζ ^ 21 - ((1759 / 474) : ℂ) * ζ ^ 22 + ((1993 / 237) : ℂ) * ζ ^ 24 + ((2479 / 474) : ℂ) * ζ ^ 25 + ((107 / 158) : ℂ) * ζ ^ 27 + ((485 / 79) : ℂ) * ζ ^ 28 + ((86 / 79) : ℂ) * ζ ^ 29 - ((28 / 237) : ℂ) * ζ ^ 30 - ((1181 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep00CoefficientIdentity01 :
    row18_reducedY67_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep00Coefficient01 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 (-((209191 / 37446) : ℂ) + ((9892 / 31205) : ℂ) * ζ ^ 1 + ((126927 / 31205) : ℂ) * ζ ^ 2 - ((1032463 / 187230) : ℂ) * ζ ^ 3 + ((350807 / 37446) : ℂ) * ζ ^ 4 + ((778363 / 62410) : ℂ) * ζ ^ 5 + ((68579 / 187230) : ℂ) * ζ ^ 6 + ((294637 / 93615) : ℂ) * ζ ^ 7 + ((376939 / 37446) : ℂ) * ζ ^ 8 - ((47854 / 93615) : ℂ) * ζ ^ 9 - ((887219 / 93615) : ℂ) * ζ ^ 10 - ((425059 / 93615) : ℂ) * ζ ^ 11 - ((146327 / 62410) : ℂ) * ζ ^ 12 + ((11649 / 62410) : ℂ) * ζ ^ 13 - ((1356812 / 93615) : ℂ) * ζ ^ 14 - ((273466 / 93615) : ℂ) * ζ ^ 15 + ((19223 / 93615) : ℂ) * ζ ^ 16 - ((266278 / 93615) : ℂ) * ζ ^ 17 + ((47579 / 18723) : ℂ) * ζ ^ 18 - ((129701 / 187230) : ℂ) * ζ ^ 19 - ((73805 / 12482) : ℂ) * ζ ^ 20 + ((49976 / 93615) : ℂ) * ζ ^ 21 + ((17921 / 31205) : ℂ) * ζ ^ 22 - ((199693 / 31205) : ℂ) * ζ ^ 23 - ((684077 / 62410) : ℂ) * ζ ^ 24 - ((6307 / 37446) : ℂ) * ζ ^ 25 + ((830491 / 93615) : ℂ) * ζ ^ 26 + ((50401 / 31205) : ℂ) * ζ ^ 27 - ((293467 / 93615) : ℂ) * ζ ^ 28 - ((42129 / 12482) : ℂ) * ζ ^ 29 + ((207706 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep00Coefficient02 : ℂ :=
  (((52 / 237) : ℂ) * ζ ^ 1 - ((775 / 237) : ℂ) * ζ ^ 2 + ((52 / 237) : ℂ) * ζ ^ 3 + ((319 / 237) : ℂ) * ζ ^ 5 - ((565 / 237) : ℂ) * ζ ^ 6 - ((3383 / 474) : ℂ) * ζ ^ 8 - ((96 / 79) : ℂ) * ζ ^ 9 + ((89 / 79) : ℂ) * ζ ^ 11 - ((982 / 237) : ℂ) * ζ ^ 12 - ((52 / 237) : ℂ) * ζ ^ 13 + ((403 / 237) : ℂ) * ζ ^ 15 - ((52 / 237) : ℂ) * ζ ^ 17 + ((775 / 474) : ℂ) * ζ ^ 18 - ((455 / 237) : ℂ) * ζ ^ 21 + ((775 / 237) : ℂ) * ζ ^ 22 + ((982 / 237) : ℂ) * ζ ^ 24 - ((89 / 79) : ℂ) * ζ ^ 25 + ((96 / 79) : ℂ) * ζ ^ 27 + ((3383 / 474) : ℂ) * ζ ^ 28 + ((52 / 237) : ℂ) * ζ ^ 29 - ((70 / 79) : ℂ) * ζ ^ 30 - ((89 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep00CoefficientIdentity02 :
    row18_reducedY67_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep00Coefficient02 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 (-((25256 / 18723) : ℂ) + ((101423 / 93615) : ℂ) * ζ ^ 1 + ((2076109 / 187230) : ℂ) * ζ ^ 2 - ((100833 / 31205) : ℂ) * ζ ^ 3 + ((321544 / 93615) : ℂ) * ζ ^ 4 + ((281546 / 93615) : ℂ) * ζ ^ 5 - ((331667 / 187230) : ℂ) * ζ ^ 6 + ((769601 / 93615) : ℂ) * ζ ^ 7 + ((2599901 / 187230) : ℂ) * ζ ^ 8 + ((131554 / 93615) : ℂ) * ζ ^ 9 - ((226073 / 187230) : ℂ) * ζ ^ 10 + ((14088 / 31205) : ℂ) * ζ ^ 11 + ((16034 / 93615) : ℂ) * ζ ^ 12 - ((49706 / 31205) : ℂ) * ζ ^ 13 - ((408886 / 93615) : ℂ) * ζ ^ 14 - ((137884 / 31205) : ℂ) * ζ ^ 15 - ((19219 / 12482) : ℂ) * ζ ^ 16 - ((648814 / 93615) : ℂ) * ζ ^ 17 - ((244717 / 187230) : ℂ) * ζ ^ 18 - ((165439 / 93615) : ℂ) * ζ ^ 19 + ((12115 / 18723) : ℂ) * ζ ^ 20 - ((59026 / 93615) : ℂ) * ζ ^ 21 - ((84201 / 62410) : ℂ) * ζ ^ 22 - ((392071 / 93615) : ℂ) * ζ ^ 23 - ((46153 / 6241) : ℂ) * ζ ^ 24 - ((25367 / 31205) : ℂ) * ζ ^ 25 - ((3943 / 93615) : ℂ) * ζ ^ 26 - ((836188 / 93615) : ℂ) * ζ ^ 27 - ((943 / 474) : ℂ) * ζ ^ 28 + ((28908 / 6241) : ℂ) * ζ ^ 29 + ((30545 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep00CoefficientIdentity03 :
    row18_reducedY67_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep00Coefficient03 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep00CoefficientIdentity04 :
    row18_reducedY67_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep00Coefficient04 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep00CoefficientIdentity05 :
    row18_reducedY67_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep00Coefficient05 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep00CoefficientIdentity06 :
    row18_reducedY67_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep00Coefficient06 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep00CoefficientIdentity07 :
    row18_reducedY67_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep00Coefficient07 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep00CoefficientIdentity08 :
    row18_reducedY67_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep00Coefficient08 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep00CoefficientIdentity09 :
    row18_reducedY67_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep00Coefficient09 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep00CoefficientIdentity10 :
    row18_reducedY67_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep00Coefficient10 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep00CoefficientIdentity11 :
    row18_reducedY67_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep00Coefficient11 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep00CoefficientIdentity12 :
    row18_reducedY67_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep00Coefficient12 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep00CoefficientIdentity13 :
    row18_reducedY67_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep00Coefficient13 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep00CoefficientIdentity14 :
    row18_reducedY67_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep00Coefficient14 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep00CoefficientIdentity15 :
    row18_reducedY67_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY67_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep00Coefficient15 row18_reducedY67_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY67_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY67_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY67_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY67_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY67_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY67_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY67_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY67_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY67_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY67_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY67_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY67_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY67_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY67_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY67_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY67_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY67_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY67_combinationStep00CoefficientIdentity00,
      row18_reducedY67_combinationStep00CoefficientIdentity01,
      row18_reducedY67_combinationStep00CoefficientIdentity02,
      row18_reducedY67_combinationStep00CoefficientIdentity03,
      row18_reducedY67_combinationStep00CoefficientIdentity04,
      row18_reducedY67_combinationStep00CoefficientIdentity05,
      row18_reducedY67_combinationStep00CoefficientIdentity06,
      row18_reducedY67_combinationStep00CoefficientIdentity07,
      row18_reducedY67_combinationStep00CoefficientIdentity08,
      row18_reducedY67_combinationStep00CoefficientIdentity09,
      row18_reducedY67_combinationStep00CoefficientIdentity10,
      row18_reducedY67_combinationStep00CoefficientIdentity11,
      row18_reducedY67_combinationStep00CoefficientIdentity12,
      row18_reducedY67_combinationStep00CoefficientIdentity13,
      row18_reducedY67_combinationStep00CoefficientIdentity14,
      row18_reducedY67_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY67_combinationStep00Multiplier * equation

private def row18_reducedY67_combinationStep01Multiplier : ℂ :=
  (((410 / 237) : ℂ) - ((4138 / 1185) : ℂ) * ζ ^ 1 - ((1898 / 1185) : ℂ) * ζ ^ 2 + ((544 / 395) : ℂ) * ζ ^ 3 - ((2074 / 1185) : ℂ) * ζ ^ 5 - ((2012 / 1185) : ℂ) * ζ ^ 6 + ((1240 / 237) : ℂ) * ζ ^ 8 + ((1792 / 395) : ℂ) * ζ ^ 9 + ((1248 / 395) : ℂ) * ζ ^ 11 + ((1240 / 237) : ℂ) * ζ ^ 12 + ((4138 / 1185) : ℂ) * ζ ^ 13 + ((144 / 395) : ℂ) * ζ ^ 15 + ((4138 / 1185) : ℂ) * ζ ^ 17 + ((38 / 395) : ℂ) * ζ ^ 18 + ((2506 / 1185) : ℂ) * ζ ^ 21 + ((1898 / 1185) : ℂ) * ζ ^ 22 - ((688 / 395) : ℂ) * ζ ^ 25 - ((2506 / 1185) : ℂ) * ζ ^ 27 - ((1240 / 237) : ℂ) * ζ ^ 28 - ((4138 / 1185) : ℂ) * ζ ^ 29 - ((1006 / 1185) : ℂ) * ζ ^ 30 - ((1248 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY67_combinationStep01Coefficient00 : ℂ :=
  (-((17 / 237) : ℂ) - ((577 / 474) : ℂ) * ζ ^ 1 - ((265 / 158) : ℂ) * ζ ^ 2 - ((355 / 474) : ℂ) * ζ ^ 3 - ((103 / 158) : ℂ) * ζ ^ 6 + ((92 / 79) : ℂ) * ζ ^ 8 + ((281 / 237) : ℂ) * ζ ^ 9 - ((52 / 237) : ℂ) * ζ ^ 11 + ((81 / 79) : ℂ) * ζ ^ 12 + ((577 / 474) : ℂ) * ζ ^ 13 - ((355 / 474) : ℂ) * ζ ^ 15 + ((577 / 474) : ℂ) * ζ ^ 17 + ((761 / 474) : ℂ) * ζ ^ 18 + ((577 / 474) : ℂ) * ζ ^ 21 + ((265 / 158) : ℂ) * ζ ^ 22 - ((265 / 158) : ℂ) * ζ ^ 24 - ((577 / 474) : ℂ) * ζ ^ 25 - ((52 / 237) : ℂ) * ζ ^ 27 - ((92 / 79) : ℂ) * ζ ^ 28 - ((577 / 474) : ℂ) * ζ ^ 29 - ((81 / 158) : ℂ) * ζ ^ 30 + ((52 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep01CoefficientIdentity00 :
    row18_reducedY67_combinationStep01Coefficient00 =
      row18_reducedY67_combinationStep00Coefficient00 +
        row18_reducedY67_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep01Coefficient00 row18_reducedY67_combinationStep00Coefficient00 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 (-((2354 / 6241) : ℂ) + ((192124 / 93615) : ℂ) * ζ ^ 1 + ((38389 / 18723) : ℂ) * ζ ^ 2 + ((90298 / 93615) : ℂ) * ζ ^ 3 + ((21311 / 93615) : ℂ) * ζ ^ 4 - ((58289 / 31205) : ℂ) * ζ ^ 5 - ((157553 / 187230) : ℂ) * ζ ^ 6 - ((109501 / 187230) : ℂ) * ζ ^ 7 - ((72097 / 31205) : ℂ) * ζ ^ 8 - ((216451 / 187230) : ℂ) * ζ ^ 9 - ((96893 / 93615) : ℂ) * ζ ^ 10 - ((44333 / 187230) : ℂ) * ζ ^ 11 + ((41014 / 93615) : ℂ) * ζ ^ 12 + ((2649 / 31205) : ℂ) * ζ ^ 13 + ((85713 / 62410) : ℂ) * ζ ^ 14 + ((55703 / 37446) : ℂ) * ζ ^ 15 + ((34143 / 62410) : ℂ) * ζ ^ 16 - ((31733 / 187230) : ℂ) * ζ ^ 17 - ((47684 / 31205) : ℂ) * ζ ^ 18 - ((159677 / 187230) : ℂ) * ζ ^ 19 - ((125411 / 187230) : ℂ) * ζ ^ 20 - ((24709 / 62410) : ℂ) * ζ ^ 21 + ((4331 / 12482) : ℂ) * ζ ^ 22 + ((73444 / 93615) : ℂ) * ζ ^ 23 + ((8852 / 6241) : ℂ) * ζ ^ 24 + ((33052 / 31205) : ℂ) * ζ ^ 25 + ((2249 / 37446) : ℂ) * ζ ^ 26 + ((9184 / 93615) : ℂ) * ζ ^ 27 - ((676 / 6241) : ℂ) * ζ ^ 28 - ((19363 / 62410) : ℂ) * ζ ^ 29 - ((936 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep01Coefficient01 : ℂ :=
  (((261 / 158) : ℂ) - ((311 / 237) : ℂ) * ζ ^ 1 - ((104 / 79) : ℂ) * ζ ^ 2 + ((767 / 474) : ℂ) * ζ ^ 3 - ((481 / 158) : ℂ) * ζ ^ 5 - ((527 / 237) : ℂ) * ζ ^ 8 + ((671 / 474) : ℂ) * ζ ^ 9 - ((719 / 237) : ℂ) * ζ ^ 11 - ((256 / 237) : ℂ) * ζ ^ 12 + ((311 / 237) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 + ((311 / 237) : ℂ) * ζ ^ 17 + ((104 / 79) : ℂ) * ζ ^ 18 + ((463 / 158) : ℂ) * ζ ^ 21 + ((104 / 79) : ℂ) * ζ ^ 22 + ((261 / 79) : ℂ) * ζ ^ 24 + ((821 / 474) : ℂ) * ζ ^ 25 + ((463 / 158) : ℂ) * ζ ^ 27 + ((527 / 237) : ℂ) * ζ ^ 28 - ((311 / 237) : ℂ) * ζ ^ 29 + ((1111 / 474) : ℂ) * ζ ^ 30 + ((719 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep01CoefficientIdentity01 :
    row18_reducedY67_combinationStep01Coefficient01 =
      row18_reducedY67_combinationStep00Coefficient01 +
        row18_reducedY67_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep01Coefficient01 row18_reducedY67_combinationStep00Coefficient01 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 (((44515 / 18723) : ℂ) + ((246584 / 93615) : ℂ) * ζ ^ 1 + ((422998 / 93615) : ℂ) * ζ ^ 2 + ((145532 / 93615) : ℂ) * ζ ^ 3 - ((74722 / 93615) : ℂ) * ζ ^ 4 - ((691531 / 187230) : ℂ) * ζ ^ 5 - ((465406 / 93615) : ℂ) * ζ ^ 6 - ((26363 / 37446) : ℂ) * ζ ^ 7 - ((393791 / 187230) : ℂ) * ζ ^ 8 - ((122881 / 62410) : ℂ) * ζ ^ 9 + ((6005 / 12482) : ℂ) * ζ ^ 10 + ((270137 / 187230) : ℂ) * ζ ^ 11 + ((469457 / 187230) : ℂ) * ζ ^ 12 + ((4053 / 62410) : ℂ) * ζ ^ 13 - ((8215 / 18723) : ℂ) * ζ ^ 14 - ((3437 / 187230) : ℂ) * ζ ^ 15 - ((209389 / 187230) : ℂ) * ζ ^ 16 - ((310397 / 187230) : ℂ) * ζ ^ 17 - ((98206 / 31205) : ℂ) * ζ ^ 18 - ((21232 / 6241) : ℂ) * ζ ^ 19 + ((19114 / 31205) : ℂ) * ζ ^ 20 - ((103879 / 187230) : ℂ) * ζ ^ 21 + ((50581 / 62410) : ℂ) * ζ ^ 22 + ((2579 / 1185) : ℂ) * ζ ^ 23 + ((286667 / 187230) : ℂ) * ζ ^ 24 + ((148627 / 187230) : ℂ) * ζ ^ 25 + ((15617 / 31205) : ℂ) * ζ ^ 26 - ((51463 / 93615) : ℂ) * ζ ^ 27 - ((2882 / 18723) : ℂ) * ζ ^ 28 - ((29506 / 93615) : ℂ) * ζ ^ 29 - ((8736 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep01Coefficient02 : ℂ :=
  (((52 / 237) : ℂ) * ζ ^ 1 - ((775 / 237) : ℂ) * ζ ^ 2 + ((52 / 237) : ℂ) * ζ ^ 3 + ((319 / 237) : ℂ) * ζ ^ 5 - ((565 / 237) : ℂ) * ζ ^ 6 - ((3383 / 474) : ℂ) * ζ ^ 8 - ((96 / 79) : ℂ) * ζ ^ 9 + ((89 / 79) : ℂ) * ζ ^ 11 - ((982 / 237) : ℂ) * ζ ^ 12 - ((52 / 237) : ℂ) * ζ ^ 13 + ((403 / 237) : ℂ) * ζ ^ 15 - ((52 / 237) : ℂ) * ζ ^ 17 + ((775 / 474) : ℂ) * ζ ^ 18 - ((455 / 237) : ℂ) * ζ ^ 21 + ((775 / 237) : ℂ) * ζ ^ 22 + ((982 / 237) : ℂ) * ζ ^ 24 - ((89 / 79) : ℂ) * ζ ^ 25 + ((96 / 79) : ℂ) * ζ ^ 27 + ((3383 / 474) : ℂ) * ζ ^ 28 + ((52 / 237) : ℂ) * ζ ^ 29 - ((70 / 79) : ℂ) * ζ ^ 30 - ((89 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep01CoefficientIdentity02 :
    row18_reducedY67_combinationStep01Coefficient02 =
      row18_reducedY67_combinationStep00Coefficient02 +
        row18_reducedY67_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep01Coefficient02 row18_reducedY67_combinationStep00Coefficient02 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep01Coefficient03 : ℂ :=
  (((17 / 237) : ℂ) + ((577 / 474) : ℂ) * ζ ^ 1 + ((265 / 158) : ℂ) * ζ ^ 2 + ((355 / 474) : ℂ) * ζ ^ 3 + ((103 / 158) : ℂ) * ζ ^ 6 - ((92 / 79) : ℂ) * ζ ^ 8 - ((281 / 237) : ℂ) * ζ ^ 9 + ((52 / 237) : ℂ) * ζ ^ 11 - ((81 / 79) : ℂ) * ζ ^ 12 - ((577 / 474) : ℂ) * ζ ^ 13 + ((355 / 474) : ℂ) * ζ ^ 15 - ((577 / 474) : ℂ) * ζ ^ 17 - ((761 / 474) : ℂ) * ζ ^ 18 - ((577 / 474) : ℂ) * ζ ^ 21 - ((265 / 158) : ℂ) * ζ ^ 22 + ((265 / 158) : ℂ) * ζ ^ 24 + ((577 / 474) : ℂ) * ζ ^ 25 + ((52 / 237) : ℂ) * ζ ^ 27 + ((92 / 79) : ℂ) * ζ ^ 28 + ((577 / 474) : ℂ) * ζ ^ 29 + ((81 / 158) : ℂ) * ζ ^ 30 - ((52 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep01CoefficientIdentity03 :
    row18_reducedY67_combinationStep01Coefficient03 =
      row18_reducedY67_combinationStep00Coefficient03 +
        row18_reducedY67_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep01Coefficient03 row18_reducedY67_combinationStep00Coefficient03 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 (((2354 / 6241) : ℂ) - ((192124 / 93615) : ℂ) * ζ ^ 1 - ((38389 / 18723) : ℂ) * ζ ^ 2 - ((90298 / 93615) : ℂ) * ζ ^ 3 - ((21311 / 93615) : ℂ) * ζ ^ 4 + ((58289 / 31205) : ℂ) * ζ ^ 5 + ((157553 / 187230) : ℂ) * ζ ^ 6 + ((109501 / 187230) : ℂ) * ζ ^ 7 + ((72097 / 31205) : ℂ) * ζ ^ 8 + ((216451 / 187230) : ℂ) * ζ ^ 9 + ((96893 / 93615) : ℂ) * ζ ^ 10 + ((44333 / 187230) : ℂ) * ζ ^ 11 - ((41014 / 93615) : ℂ) * ζ ^ 12 - ((2649 / 31205) : ℂ) * ζ ^ 13 - ((85713 / 62410) : ℂ) * ζ ^ 14 - ((55703 / 37446) : ℂ) * ζ ^ 15 - ((34143 / 62410) : ℂ) * ζ ^ 16 + ((31733 / 187230) : ℂ) * ζ ^ 17 + ((47684 / 31205) : ℂ) * ζ ^ 18 + ((159677 / 187230) : ℂ) * ζ ^ 19 + ((125411 / 187230) : ℂ) * ζ ^ 20 + ((24709 / 62410) : ℂ) * ζ ^ 21 - ((4331 / 12482) : ℂ) * ζ ^ 22 - ((73444 / 93615) : ℂ) * ζ ^ 23 - ((8852 / 6241) : ℂ) * ζ ^ 24 - ((33052 / 31205) : ℂ) * ζ ^ 25 - ((2249 / 37446) : ℂ) * ζ ^ 26 - ((9184 / 93615) : ℂ) * ζ ^ 27 + ((676 / 6241) : ℂ) * ζ ^ 28 + ((19363 / 62410) : ℂ) * ζ ^ 29 + ((936 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep01CoefficientIdentity04 :
    row18_reducedY67_combinationStep01Coefficient04 =
      row18_reducedY67_combinationStep00Coefficient04 +
        row18_reducedY67_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep01Coefficient04 row18_reducedY67_combinationStep00Coefficient04 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep01CoefficientIdentity05 :
    row18_reducedY67_combinationStep01Coefficient05 =
      row18_reducedY67_combinationStep00Coefficient05 +
        row18_reducedY67_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep01Coefficient05 row18_reducedY67_combinationStep00Coefficient05 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep01CoefficientIdentity06 :
    row18_reducedY67_combinationStep01Coefficient06 =
      row18_reducedY67_combinationStep00Coefficient06 +
        row18_reducedY67_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep01Coefficient06 row18_reducedY67_combinationStep00Coefficient06 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep01CoefficientIdentity07 :
    row18_reducedY67_combinationStep01Coefficient07 =
      row18_reducedY67_combinationStep00Coefficient07 +
        row18_reducedY67_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep01Coefficient07 row18_reducedY67_combinationStep00Coefficient07 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep01CoefficientIdentity08 :
    row18_reducedY67_combinationStep01Coefficient08 =
      row18_reducedY67_combinationStep00Coefficient08 +
        row18_reducedY67_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep01Coefficient08 row18_reducedY67_combinationStep00Coefficient08 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep01CoefficientIdentity09 :
    row18_reducedY67_combinationStep01Coefficient09 =
      row18_reducedY67_combinationStep00Coefficient09 +
        row18_reducedY67_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep01Coefficient09 row18_reducedY67_combinationStep00Coefficient09 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep01CoefficientIdentity10 :
    row18_reducedY67_combinationStep01Coefficient10 =
      row18_reducedY67_combinationStep00Coefficient10 +
        row18_reducedY67_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep01Coefficient10 row18_reducedY67_combinationStep00Coefficient10 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep01CoefficientIdentity11 :
    row18_reducedY67_combinationStep01Coefficient11 =
      row18_reducedY67_combinationStep00Coefficient11 +
        row18_reducedY67_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep01Coefficient11 row18_reducedY67_combinationStep00Coefficient11 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep01CoefficientIdentity12 :
    row18_reducedY67_combinationStep01Coefficient12 =
      row18_reducedY67_combinationStep00Coefficient12 +
        row18_reducedY67_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep01Coefficient12 row18_reducedY67_combinationStep00Coefficient12 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep01CoefficientIdentity13 :
    row18_reducedY67_combinationStep01Coefficient13 =
      row18_reducedY67_combinationStep00Coefficient13 +
        row18_reducedY67_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep01Coefficient13 row18_reducedY67_combinationStep00Coefficient13 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep01CoefficientIdentity14 :
    row18_reducedY67_combinationStep01Coefficient14 =
      row18_reducedY67_combinationStep00Coefficient14 +
        row18_reducedY67_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep01Coefficient14 row18_reducedY67_combinationStep00Coefficient14 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep01CoefficientIdentity15 :
    row18_reducedY67_combinationStep01Coefficient15 =
      row18_reducedY67_combinationStep00Coefficient15 +
        row18_reducedY67_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep01Coefficient15 row18_reducedY67_combinationStep00Coefficient15 row18_reducedY67_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY67_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY67_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY67_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY67_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY67_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY67_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY67_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY67_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY67_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY67_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY67_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY67_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY67_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY67_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY67_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY67_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY67_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY67_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY67_combinationStep01CoefficientIdentity00,
      row18_reducedY67_combinationStep01CoefficientIdentity01,
      row18_reducedY67_combinationStep01CoefficientIdentity02,
      row18_reducedY67_combinationStep01CoefficientIdentity03,
      row18_reducedY67_combinationStep01CoefficientIdentity04,
      row18_reducedY67_combinationStep01CoefficientIdentity05,
      row18_reducedY67_combinationStep01CoefficientIdentity06,
      row18_reducedY67_combinationStep01CoefficientIdentity07,
      row18_reducedY67_combinationStep01CoefficientIdentity08,
      row18_reducedY67_combinationStep01CoefficientIdentity09,
      row18_reducedY67_combinationStep01CoefficientIdentity10,
      row18_reducedY67_combinationStep01CoefficientIdentity11,
      row18_reducedY67_combinationStep01CoefficientIdentity12,
      row18_reducedY67_combinationStep01CoefficientIdentity13,
      row18_reducedY67_combinationStep01CoefficientIdentity14,
      row18_reducedY67_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY67_combinationStep01Multiplier * equation

private def row18_reducedY67_combinationStep02Multiplier : ℂ :=
  (-((2032 / 1185) : ℂ) + ((1084 / 237) : ℂ) * ζ ^ 1 - ((664 / 1185) : ℂ) * ζ ^ 2 - ((2486 / 1185) : ℂ) * ζ ^ 3 - ((1992 / 395) : ℂ) * ζ ^ 6 - ((408 / 395) : ℂ) * ζ ^ 8 - ((1394 / 237) : ℂ) * ζ ^ 9 - ((1174 / 395) : ℂ) * ζ ^ 11 - ((5312 / 1185) : ℂ) * ζ ^ 12 - ((1084 / 237) : ℂ) * ζ ^ 13 - ((2486 / 1185) : ℂ) * ζ ^ 15 - ((1084 / 237) : ℂ) * ζ ^ 17 - ((456 / 395) : ℂ) * ζ ^ 18 - ((1084 / 237) : ℂ) * ζ ^ 21 + ((664 / 1185) : ℂ) * ζ ^ 22 - ((664 / 1185) : ℂ) * ζ ^ 24 + ((1084 / 237) : ℂ) * ζ ^ 25 - ((1174 / 395) : ℂ) * ζ ^ 27 + ((408 / 395) : ℂ) * ζ ^ 28 + ((1084 / 237) : ℂ) * ζ ^ 29 - ((1888 / 1185) : ℂ) * ζ ^ 30 + ((1174 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY67_combinationStep02Coefficient00 : ℂ :=
  (((737 / 790) : ℂ) - ((991 / 474) : ℂ) * ζ ^ 1 - ((284 / 1185) : ℂ) * ζ ^ 2 + ((1151 / 2370) : ℂ) * ζ ^ 3 + ((2039 / 1185) : ℂ) * ζ ^ 6 + ((3817 / 2370) : ℂ) * ζ ^ 8 + ((803 / 237) : ℂ) * ζ ^ 9 + ((257 / 395) : ℂ) * ζ ^ 11 + ((2323 / 1185) : ℂ) * ζ ^ 12 + ((991 / 474) : ℂ) * ζ ^ 13 + ((1151 / 2370) : ℂ) * ζ ^ 15 + ((991 / 474) : ℂ) * ζ ^ 17 + ((2779 / 2370) : ℂ) * ζ ^ 18 + ((991 / 474) : ℂ) * ζ ^ 21 + ((284 / 1185) : ℂ) * ζ ^ 22 - ((284 / 1185) : ℂ) * ζ ^ 24 - ((991 / 474) : ℂ) * ζ ^ 25 + ((257 / 395) : ℂ) * ζ ^ 27 - ((3817 / 2370) : ℂ) * ζ ^ 28 - ((991 / 474) : ℂ) * ζ ^ 29 + ((1083 / 790) : ℂ) * ζ ^ 30 - ((257 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep02CoefficientIdentity00 :
    row18_reducedY67_combinationStep02Coefficient00 =
      row18_reducedY67_combinationStep01Coefficient00 +
        row18_reducedY67_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep02Coefficient00 row18_reducedY67_combinationStep01Coefficient00 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 (-((175907 / 187230) : ℂ) + ((59917 / 93615) : ℂ) * ζ ^ 1 - ((148999 / 187230) : ℂ) * ζ ^ 2 - ((226136 / 93615) : ℂ) * ζ ^ 3 + ((97937 / 93615) : ℂ) * ζ ^ 4 + ((1487 / 62410) : ℂ) * ζ ^ 5 - ((140413 / 93615) : ℂ) * ζ ^ 6 + ((169496 / 93615) : ℂ) * ζ ^ 7 - ((9686 / 93615) : ℂ) * ζ ^ 8 - ((240911 / 187230) : ℂ) * ζ ^ 9 + ((83457 / 62410) : ℂ) * ζ ^ 10 - ((77141 / 93615) : ℂ) * ζ ^ 11 - ((144518 / 93615) : ℂ) * ζ ^ 12 + ((78751 / 31205) : ℂ) * ζ ^ 13 - ((249751 / 187230) : ℂ) * ζ ^ 14 - ((29831 / 37446) : ℂ) * ζ ^ 15 + ((114451 / 93615) : ℂ) * ζ ^ 16 - ((317749 / 187230) : ℂ) * ζ ^ 17 + ((7214 / 93615) : ℂ) * ζ ^ 18 + ((30874 / 31205) : ℂ) * ζ ^ 19 - ((55053 / 62410) : ℂ) * ζ ^ 20 + ((105013 / 187230) : ℂ) * ζ ^ 21 + ((33443 / 93615) : ℂ) * ζ ^ 22 + ((16679 / 31205) : ℂ) * ζ ^ 23 + ((6397 / 93615) : ℂ) * ζ ^ 24 - ((5137 / 31205) : ℂ) * ζ ^ 25 + ((8881 / 62410) : ℂ) * ζ ^ 26 - ((106811 / 187230) : ℂ) * ζ ^ 27 + ((14483 / 37446) : ℂ) * ζ ^ 28 - ((20696 / 93615) : ℂ) * ζ ^ 29 + ((4109 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep02Coefficient01 : ℂ :=
  (-((437 / 158) : ℂ) + ((734 / 237) : ℂ) * ζ ^ 1 + ((655 / 158) : ℂ) * ζ ^ 2 - ((511 / 158) : ℂ) * ζ ^ 3 + ((1270 / 237) : ℂ) * ζ ^ 5 + ((2437 / 474) : ℂ) * ζ ^ 8 - ((163 / 474) : ℂ) * ζ ^ 9 + ((848 / 237) : ℂ) * ζ ^ 11 + ((185 / 474) : ℂ) * ζ ^ 12 - ((734 / 237) : ℂ) * ζ ^ 13 + ((461 / 474) : ℂ) * ζ ^ 15 - ((734 / 237) : ℂ) * ζ ^ 17 - ((655 / 158) : ℂ) * ζ ^ 18 - ((3001 / 474) : ℂ) * ζ ^ 21 - ((655 / 158) : ℂ) * ζ ^ 22 - ((437 / 79) : ℂ) * ζ ^ 24 - ((536 / 237) : ℂ) * ζ ^ 25 - ((3001 / 474) : ℂ) * ζ ^ 27 - ((2437 / 474) : ℂ) * ζ ^ 28 + ((734 / 237) : ℂ) * ζ ^ 29 - ((193 / 158) : ℂ) * ζ ^ 30 - ((848 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep02CoefficientIdentity01 :
    row18_reducedY67_combinationStep02Coefficient01 =
      row18_reducedY67_combinationStep01Coefficient01 +
        row18_reducedY67_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep02Coefficient01 row18_reducedY67_combinationStep01Coefficient01 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 (((126171 / 31205) : ℂ) - ((55220 / 18723) : ℂ) * ζ ^ 1 - ((1285057 / 187230) : ℂ) * ζ ^ 2 + ((848927 / 187230) : ℂ) * ζ ^ 3 - ((194633 / 62410) : ℂ) * ζ ^ 4 - ((477272 / 93615) : ℂ) * ζ ^ 5 + ((736969 / 187230) : ℂ) * ζ ^ 6 - ((118449 / 62410) : ℂ) * ζ ^ 7 - ((235053 / 62410) : ℂ) * ζ ^ 8 + ((623147 / 187230) : ℂ) * ζ ^ 9 - ((95003 / 93615) : ℂ) * ζ ^ 10 - ((715447 / 187230) : ℂ) * ζ ^ 11 + ((356558 / 93615) : ℂ) * ζ ^ 12 - ((42194 / 18723) : ℂ) * ζ ^ 13 - ((198361 / 187230) : ℂ) * ζ ^ 14 + ((359243 / 93615) : ℂ) * ζ ^ 15 - ((76968 / 31205) : ℂ) * ζ ^ 16 - ((190759 / 187230) : ℂ) * ζ ^ 17 + ((833501 / 187230) : ℂ) * ζ ^ 18 - ((214156 / 93615) : ℂ) * ζ ^ 19 - ((272 / 1185) : ℂ) * ζ ^ 20 + ((115333 / 37446) : ℂ) * ζ ^ 21 - ((7207 / 18723) : ℂ) * ζ ^ 22 - ((152773 / 187230) : ℂ) * ζ ^ 23 + ((209881 / 93615) : ℂ) * ζ ^ 24 - ((13054 / 93615) : ℂ) * ζ ^ 25 - ((151316 / 93615) : ℂ) * ζ ^ 26 + ((185947 / 93615) : ℂ) * ζ ^ 27 - ((165431 / 187230) : ℂ) * ζ ^ 28 + ((41411 / 93615) : ℂ) * ζ ^ 29 + ((7631 / 62410) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep02Coefficient02 : ℂ :=
  (((52 / 237) : ℂ) * ζ ^ 1 - ((775 / 237) : ℂ) * ζ ^ 2 + ((52 / 237) : ℂ) * ζ ^ 3 + ((319 / 237) : ℂ) * ζ ^ 5 - ((565 / 237) : ℂ) * ζ ^ 6 - ((3383 / 474) : ℂ) * ζ ^ 8 - ((96 / 79) : ℂ) * ζ ^ 9 + ((89 / 79) : ℂ) * ζ ^ 11 - ((982 / 237) : ℂ) * ζ ^ 12 - ((52 / 237) : ℂ) * ζ ^ 13 + ((403 / 237) : ℂ) * ζ ^ 15 - ((52 / 237) : ℂ) * ζ ^ 17 + ((775 / 474) : ℂ) * ζ ^ 18 - ((455 / 237) : ℂ) * ζ ^ 21 + ((775 / 237) : ℂ) * ζ ^ 22 + ((982 / 237) : ℂ) * ζ ^ 24 - ((89 / 79) : ℂ) * ζ ^ 25 + ((96 / 79) : ℂ) * ζ ^ 27 + ((3383 / 474) : ℂ) * ζ ^ 28 + ((52 / 237) : ℂ) * ζ ^ 29 - ((70 / 79) : ℂ) * ζ ^ 30 - ((89 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep02CoefficientIdentity02 :
    row18_reducedY67_combinationStep02Coefficient02 =
      row18_reducedY67_combinationStep01Coefficient02 +
        row18_reducedY67_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep02Coefficient02 row18_reducedY67_combinationStep01Coefficient02 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep02Coefficient03 : ℂ :=
  (((17 / 237) : ℂ) + ((577 / 474) : ℂ) * ζ ^ 1 + ((265 / 158) : ℂ) * ζ ^ 2 + ((355 / 474) : ℂ) * ζ ^ 3 + ((103 / 158) : ℂ) * ζ ^ 6 - ((92 / 79) : ℂ) * ζ ^ 8 - ((281 / 237) : ℂ) * ζ ^ 9 + ((52 / 237) : ℂ) * ζ ^ 11 - ((81 / 79) : ℂ) * ζ ^ 12 - ((577 / 474) : ℂ) * ζ ^ 13 + ((355 / 474) : ℂ) * ζ ^ 15 - ((577 / 474) : ℂ) * ζ ^ 17 - ((761 / 474) : ℂ) * ζ ^ 18 - ((577 / 474) : ℂ) * ζ ^ 21 - ((265 / 158) : ℂ) * ζ ^ 22 + ((265 / 158) : ℂ) * ζ ^ 24 + ((577 / 474) : ℂ) * ζ ^ 25 + ((52 / 237) : ℂ) * ζ ^ 27 + ((92 / 79) : ℂ) * ζ ^ 28 + ((577 / 474) : ℂ) * ζ ^ 29 + ((81 / 158) : ℂ) * ζ ^ 30 - ((52 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep02CoefficientIdentity03 :
    row18_reducedY67_combinationStep02Coefficient03 =
      row18_reducedY67_combinationStep01Coefficient03 +
        row18_reducedY67_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep02Coefficient03 row18_reducedY67_combinationStep01Coefficient03 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep02Coefficient04 : ℂ :=
  (-((2381 / 2370) : ℂ) + ((69 / 79) : ℂ) * ζ ^ 1 - ((3407 / 2370) : ℂ) * ζ ^ 2 - ((1463 / 1185) : ℂ) * ζ ^ 3 - ((5623 / 2370) : ℂ) * ζ ^ 6 - ((1057 / 2370) : ℂ) * ζ ^ 8 - ((174 / 79) : ℂ) * ζ ^ 9 - ((1031 / 1185) : ℂ) * ζ ^ 11 - ((1108 / 1185) : ℂ) * ζ ^ 12 - ((69 / 79) : ℂ) * ζ ^ 13 - ((1463 / 1185) : ℂ) * ζ ^ 15 - ((69 / 79) : ℂ) * ζ ^ 17 + ((171 / 395) : ℂ) * ζ ^ 18 - ((69 / 79) : ℂ) * ζ ^ 21 + ((3407 / 2370) : ℂ) * ζ ^ 22 - ((3407 / 2370) : ℂ) * ζ ^ 24 + ((69 / 79) : ℂ) * ζ ^ 25 - ((1031 / 1185) : ℂ) * ζ ^ 27 + ((1057 / 2370) : ℂ) * ζ ^ 28 + ((69 / 79) : ℂ) * ζ ^ 29 - ((744 / 395) : ℂ) * ζ ^ 30 + ((1031 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep02CoefficientIdentity04 :
    row18_reducedY67_combinationStep02Coefficient04 =
      row18_reducedY67_combinationStep01Coefficient04 +
        row18_reducedY67_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep02Coefficient04 row18_reducedY67_combinationStep01Coefficient04 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 (((175907 / 187230) : ℂ) - ((59917 / 93615) : ℂ) * ζ ^ 1 + ((148999 / 187230) : ℂ) * ζ ^ 2 + ((226136 / 93615) : ℂ) * ζ ^ 3 - ((97937 / 93615) : ℂ) * ζ ^ 4 - ((1487 / 62410) : ℂ) * ζ ^ 5 + ((140413 / 93615) : ℂ) * ζ ^ 6 - ((169496 / 93615) : ℂ) * ζ ^ 7 + ((9686 / 93615) : ℂ) * ζ ^ 8 + ((240911 / 187230) : ℂ) * ζ ^ 9 - ((83457 / 62410) : ℂ) * ζ ^ 10 + ((77141 / 93615) : ℂ) * ζ ^ 11 + ((144518 / 93615) : ℂ) * ζ ^ 12 - ((78751 / 31205) : ℂ) * ζ ^ 13 + ((249751 / 187230) : ℂ) * ζ ^ 14 + ((29831 / 37446) : ℂ) * ζ ^ 15 - ((114451 / 93615) : ℂ) * ζ ^ 16 + ((317749 / 187230) : ℂ) * ζ ^ 17 - ((7214 / 93615) : ℂ) * ζ ^ 18 - ((30874 / 31205) : ℂ) * ζ ^ 19 + ((55053 / 62410) : ℂ) * ζ ^ 20 - ((105013 / 187230) : ℂ) * ζ ^ 21 - ((33443 / 93615) : ℂ) * ζ ^ 22 - ((16679 / 31205) : ℂ) * ζ ^ 23 - ((6397 / 93615) : ℂ) * ζ ^ 24 + ((5137 / 31205) : ℂ) * ζ ^ 25 - ((8881 / 62410) : ℂ) * ζ ^ 26 + ((106811 / 187230) : ℂ) * ζ ^ 27 - ((14483 / 37446) : ℂ) * ζ ^ 28 + ((20696 / 93615) : ℂ) * ζ ^ 29 - ((4109 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep02CoefficientIdentity05 :
    row18_reducedY67_combinationStep02Coefficient05 =
      row18_reducedY67_combinationStep01Coefficient05 +
        row18_reducedY67_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep02Coefficient05 row18_reducedY67_combinationStep01Coefficient05 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep02Coefficient06 : ℂ :=
  (-((1009 / 395) : ℂ) - ((3547 / 2370) : ℂ) * ζ ^ 1 + ((3547 / 2370) : ℂ) * ζ ^ 3 - ((3091 / 2370) : ℂ) * ζ ^ 5 - ((383 / 237) : ℂ) * ζ ^ 6 + ((1009 / 790) : ℂ) * ζ ^ 8 + ((254 / 395) : ℂ) * ζ ^ 9 - ((76 / 395) : ℂ) * ζ ^ 11 + ((656 / 395) : ℂ) * ζ ^ 12 + ((3547 / 2370) : ℂ) * ζ ^ 13 - ((768 / 395) : ℂ) * ζ ^ 15 + ((3547 / 2370) : ℂ) * ζ ^ 17 + ((617 / 474) : ℂ) * ζ ^ 18 - ((1061 / 2370) : ℂ) * ζ ^ 21 - ((353 / 395) : ℂ) * ζ ^ 24 - ((76 / 395) : ℂ) * ζ ^ 25 + ((254 / 395) : ℂ) * ζ ^ 27 - ((1009 / 790) : ℂ) * ζ ^ 28 - ((3547 / 2370) : ℂ) * ζ ^ 29 - ((383 / 237) : ℂ) * ζ ^ 30 + ((76 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep02CoefficientIdentity06 :
    row18_reducedY67_combinationStep02Coefficient06 =
      row18_reducedY67_combinationStep01Coefficient06 +
        row18_reducedY67_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep02Coefficient06 row18_reducedY67_combinationStep01Coefficient06 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 (((258437 / 93615) : ℂ) + ((10935 / 12482) : ℂ) * ζ ^ 1 + ((9837 / 31205) : ℂ) * ζ ^ 2 - ((97163 / 62410) : ℂ) * ζ ^ 3 - ((464341 / 187230) : ℂ) * ζ ^ 4 + ((28623 / 62410) : ℂ) * ζ ^ 5 + ((180902 / 93615) : ℂ) * ζ ^ 6 + ((32101 / 37446) : ℂ) * ζ ^ 7 + ((116338 / 93615) : ℂ) * ζ ^ 8 - ((7339 / 37446) : ℂ) * ζ ^ 9 - ((38465 / 37446) : ℂ) * ζ ^ 10 - ((39967 / 62410) : ℂ) * ζ ^ 11 - ((52453 / 187230) : ℂ) * ζ ^ 12 - ((17906 / 93615) : ℂ) * ζ ^ 13 + ((19318 / 93615) : ℂ) * ζ ^ 14 + ((81763 / 187230) : ℂ) * ζ ^ 15 + ((34439 / 93615) : ℂ) * ζ ^ 16 - ((24943 / 187230) : ℂ) * ζ ^ 17 - ((23979 / 62410) : ℂ) * ζ ^ 18 - ((37403 / 31205) : ℂ) * ζ ^ 19 - ((18113 / 62410) : ℂ) * ζ ^ 20 + ((130961 / 187230) : ℂ) * ζ ^ 21 + ((25133 / 93615) : ℂ) * ζ ^ 22 + ((55029 / 62410) : ℂ) * ζ ^ 23 - ((18113 / 62410) : ℂ) * ζ ^ 24 - ((29267 / 18723) : ℂ) * ζ ^ 25 + ((41057 / 187230) : ℂ) * ζ ^ 26 + ((23089 / 187230) : ℂ) * ζ ^ 27 + ((6077 / 62410) : ℂ) * ζ ^ 28 + ((11728 / 31205) : ℂ) * ζ ^ 29 + ((1761 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep02CoefficientIdentity07 :
    row18_reducedY67_combinationStep02Coefficient07 =
      row18_reducedY67_combinationStep01Coefficient07 +
        row18_reducedY67_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep02Coefficient07 row18_reducedY67_combinationStep01Coefficient07 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep02CoefficientIdentity08 :
    row18_reducedY67_combinationStep02Coefficient08 =
      row18_reducedY67_combinationStep01Coefficient08 +
        row18_reducedY67_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep02Coefficient08 row18_reducedY67_combinationStep01Coefficient08 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep02CoefficientIdentity09 :
    row18_reducedY67_combinationStep02Coefficient09 =
      row18_reducedY67_combinationStep01Coefficient09 +
        row18_reducedY67_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep02Coefficient09 row18_reducedY67_combinationStep01Coefficient09 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep02CoefficientIdentity10 :
    row18_reducedY67_combinationStep02Coefficient10 =
      row18_reducedY67_combinationStep01Coefficient10 +
        row18_reducedY67_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep02Coefficient10 row18_reducedY67_combinationStep01Coefficient10 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep02CoefficientIdentity11 :
    row18_reducedY67_combinationStep02Coefficient11 =
      row18_reducedY67_combinationStep01Coefficient11 +
        row18_reducedY67_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep02Coefficient11 row18_reducedY67_combinationStep01Coefficient11 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep02CoefficientIdentity12 :
    row18_reducedY67_combinationStep02Coefficient12 =
      row18_reducedY67_combinationStep01Coefficient12 +
        row18_reducedY67_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep02Coefficient12 row18_reducedY67_combinationStep01Coefficient12 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep02CoefficientIdentity13 :
    row18_reducedY67_combinationStep02Coefficient13 =
      row18_reducedY67_combinationStep01Coefficient13 +
        row18_reducedY67_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep02Coefficient13 row18_reducedY67_combinationStep01Coefficient13 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep02CoefficientIdentity14 :
    row18_reducedY67_combinationStep02Coefficient14 =
      row18_reducedY67_combinationStep01Coefficient14 +
        row18_reducedY67_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep02Coefficient14 row18_reducedY67_combinationStep01Coefficient14 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep02CoefficientIdentity15 :
    row18_reducedY67_combinationStep02Coefficient15 =
      row18_reducedY67_combinationStep01Coefficient15 +
        row18_reducedY67_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep02Coefficient15 row18_reducedY67_combinationStep01Coefficient15 row18_reducedY67_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY67_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY67_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY67_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY67_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY67_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY67_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY67_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY67_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY67_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY67_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY67_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY67_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY67_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY67_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY67_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY67_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY67_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY67_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY67_combinationStep02CoefficientIdentity00,
      row18_reducedY67_combinationStep02CoefficientIdentity01,
      row18_reducedY67_combinationStep02CoefficientIdentity02,
      row18_reducedY67_combinationStep02CoefficientIdentity03,
      row18_reducedY67_combinationStep02CoefficientIdentity04,
      row18_reducedY67_combinationStep02CoefficientIdentity05,
      row18_reducedY67_combinationStep02CoefficientIdentity06,
      row18_reducedY67_combinationStep02CoefficientIdentity07,
      row18_reducedY67_combinationStep02CoefficientIdentity08,
      row18_reducedY67_combinationStep02CoefficientIdentity09,
      row18_reducedY67_combinationStep02CoefficientIdentity10,
      row18_reducedY67_combinationStep02CoefficientIdentity11,
      row18_reducedY67_combinationStep02CoefficientIdentity12,
      row18_reducedY67_combinationStep02CoefficientIdentity13,
      row18_reducedY67_combinationStep02CoefficientIdentity14,
      row18_reducedY67_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY67_combinationStep02Multiplier * equation

private def row18_reducedY67_combinationStep03Multiplier : ℂ :=
  (-(2 : ℂ) + ((76 / 237) : ℂ) * ζ ^ 1 - ((1438 / 237) : ℂ) * ζ ^ 2 - ((320 / 237) : ℂ) * ζ ^ 3 - ((910 / 237) : ℂ) * ζ ^ 5 - ((1876 / 237) : ℂ) * ζ ^ 6 - (2 : ℂ) * ζ ^ 8 - ((704 / 237) : ℂ) * ζ ^ 9 - ((128 / 79) : ℂ) * ζ ^ 11 - (2 : ℂ) * ζ ^ 12 - ((76 / 237) : ℂ) * ζ ^ 13 - ((222 / 79) : ℂ) * ζ ^ 15 - ((76 / 237) : ℂ) * ζ ^ 17 + ((146 / 79) : ℂ) * ζ ^ 18 + ((244 / 237) : ℂ) * ζ ^ 21 + ((1438 / 237) : ℂ) * ζ ^ 22 + ((986 / 237) : ℂ) * ζ ^ 25 - ((244 / 237) : ℂ) * ζ ^ 27 + (2 : ℂ) * ζ ^ 28 + ((76 / 237) : ℂ) * ζ ^ 29 - ((938 / 237) : ℂ) * ζ ^ 30 + ((128 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY67_combinationStep03Coefficient00 : ℂ :=
  (((461 / 395) : ℂ) - ((143 / 79) : ℂ) * ζ ^ 1 + ((649 / 790) : ℂ) * ζ ^ 2 + ((1267 / 790) : ℂ) * ζ ^ 3 + ((1511 / 790) : ℂ) * ζ ^ 6 + ((382 / 395) : ℂ) * ζ ^ 8 + ((601 / 158) : ℂ) * ζ ^ 9 + ((719 / 790) : ℂ) * ζ ^ 11 + ((431 / 395) : ℂ) * ζ ^ 12 + ((143 / 79) : ℂ) * ζ ^ 13 + ((1267 / 790) : ℂ) * ζ ^ 15 + ((143 / 79) : ℂ) * ζ ^ 17 + ((273 / 790) : ℂ) * ζ ^ 18 + ((143 / 79) : ℂ) * ζ ^ 21 - ((649 / 790) : ℂ) * ζ ^ 22 + ((649 / 790) : ℂ) * ζ ^ 24 - ((143 / 79) : ℂ) * ζ ^ 25 + ((719 / 790) : ℂ) * ζ ^ 27 - ((382 / 395) : ℂ) * ζ ^ 28 - ((143 / 79) : ℂ) * ζ ^ 29 + ((1413 / 790) : ℂ) * ζ ^ 30 - ((719 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep03CoefficientIdentity00 :
    row18_reducedY67_combinationStep03Coefficient00 =
      row18_reducedY67_combinationStep02Coefficient00 +
        row18_reducedY67_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep03Coefficient00 row18_reducedY67_combinationStep02Coefficient00 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 (-((75 / 158) : ℂ) - ((997 / 6241) : ℂ) * ζ ^ 1 - ((35080 / 18723) : ℂ) * ζ ^ 2 - ((32497 / 37446) : ℂ) * ζ ^ 3 + ((1839 / 6241) : ℂ) * ζ ^ 4 + ((698 / 6241) : ℂ) * ζ ^ 5 + ((14512 / 18723) : ℂ) * ζ ^ 6 + ((20489 / 18723) : ℂ) * ζ ^ 7 - ((2903 / 18723) : ℂ) * ζ ^ 8 + ((782 / 6241) : ℂ) * ζ ^ 9 + ((2029 / 6241) : ℂ) * ζ ^ 10 - ((894 / 6241) : ℂ) * ζ ^ 11 - ((136 / 6241) : ℂ) * ζ ^ 12 + ((13211 / 37446) : ℂ) * ζ ^ 13 - ((6389 / 18723) : ℂ) * ζ ^ 14 - ((2817 / 6241) : ℂ) * ζ ^ 15 + ((1741 / 18723) : ℂ) * ζ ^ 16 + ((14183 / 37446) : ℂ) * ζ ^ 17 + ((5687 / 18723) : ℂ) * ζ ^ 18 + ((4042 / 18723) : ℂ) * ζ ^ 19 - ((3901 / 37446) : ℂ) * ζ ^ 20 + ((6682 / 18723) : ℂ) * ζ ^ 21 + ((18059 / 37446) : ℂ) * ζ ^ 22 - ((15572 / 18723) : ℂ) * ζ ^ 23 - ((6599 / 18723) : ℂ) * ζ ^ 24 + ((163 / 37446) : ℂ) * ζ ^ 25 - ((31951 / 37446) : ℂ) * ζ ^ 26 + ((6023 / 18723) : ℂ) * ζ ^ 27 + ((3241 / 6241) : ℂ) * ζ ^ 28 - ((727 / 12482) : ℂ) * ζ ^ 29 - ((480 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep03Coefficient01 : ℂ :=
  (((25 / 79) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((22 / 79) : ℂ) * ζ ^ 5 - ((6 / 79) : ℂ) * ζ ^ 9 + ((16 / 79) : ℂ) * ζ ^ 15 - ((25 / 79) : ℂ) * ζ ^ 18 + ((6 / 79) : ℂ) * ζ ^ 21 - ((25 / 79) : ℂ) * ζ ^ 22 + ((22 / 79) : ℂ) * ζ ^ 25 + ((6 / 79) : ℂ) * ζ ^ 27 - ((14 / 79) : ℂ) * ζ ^ 30)

private theorem row18_reducedY67_combinationStep03CoefficientIdentity01 :
    row18_reducedY67_combinationStep03Coefficient01 =
      row18_reducedY67_combinationStep02Coefficient01 +
        row18_reducedY67_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep03Coefficient01 row18_reducedY67_combinationStep02Coefficient01 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 (-((469 / 158) : ℂ) + ((103679 / 37446) : ℂ) * ζ ^ 1 + ((43615 / 18723) : ℂ) * ζ ^ 2 - ((146143 / 37446) : ℂ) * ζ ^ 3 - ((4012 / 18723) : ℂ) * ζ ^ 4 + ((50573 / 18723) : ℂ) * ζ ^ 5 - ((42379 / 12482) : ℂ) * ζ ^ 6 - ((22790 / 18723) : ℂ) * ζ ^ 7 + ((37700 / 18723) : ℂ) * ζ ^ 8 - ((29689 / 12482) : ℂ) * ζ ^ 9 + ((19894 / 18723) : ℂ) * ζ ^ 10 - ((9821 / 18723) : ℂ) * ζ ^ 11 - ((1069 / 237) : ℂ) * ζ ^ 12 + ((7890 / 6241) : ℂ) * ζ ^ 13 - ((3283 / 18723) : ℂ) * ζ ^ 14 - ((76727 / 18723) : ℂ) * ζ ^ 15 + ((6821 / 6241) : ℂ) * ζ ^ 16 - ((7829 / 18723) : ℂ) * ζ ^ 17 - ((84829 / 37446) : ℂ) * ζ ^ 18 + ((22093 / 12482) : ℂ) * ζ ^ 19 + ((22955 / 37446) : ℂ) * ζ ^ 20 - ((46126 / 18723) : ℂ) * ζ ^ 21 + ((45169 / 37446) : ℂ) * ζ ^ 22 + ((13504 / 18723) : ℂ) * ζ ^ 23 - ((2011 / 18723) : ℂ) * ζ ^ 24 + ((27469 / 12482) : ℂ) * ζ ^ 25 - ((16147 / 18723) : ℂ) * ζ ^ 26 - ((5627 / 12482) : ℂ) * ζ ^ 27 + ((376 / 18723) : ℂ) * ζ ^ 28 - ((4262 / 18723) : ℂ) * ζ ^ 29 + ((896 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep03Coefficient02 : ℂ :=
  (((52 / 237) : ℂ) * ζ ^ 1 - ((775 / 237) : ℂ) * ζ ^ 2 + ((52 / 237) : ℂ) * ζ ^ 3 + ((319 / 237) : ℂ) * ζ ^ 5 - ((565 / 237) : ℂ) * ζ ^ 6 - ((3383 / 474) : ℂ) * ζ ^ 8 - ((96 / 79) : ℂ) * ζ ^ 9 + ((89 / 79) : ℂ) * ζ ^ 11 - ((982 / 237) : ℂ) * ζ ^ 12 - ((52 / 237) : ℂ) * ζ ^ 13 + ((403 / 237) : ℂ) * ζ ^ 15 - ((52 / 237) : ℂ) * ζ ^ 17 + ((775 / 474) : ℂ) * ζ ^ 18 - ((455 / 237) : ℂ) * ζ ^ 21 + ((775 / 237) : ℂ) * ζ ^ 22 + ((982 / 237) : ℂ) * ζ ^ 24 - ((89 / 79) : ℂ) * ζ ^ 25 + ((96 / 79) : ℂ) * ζ ^ 27 + ((3383 / 474) : ℂ) * ζ ^ 28 + ((52 / 237) : ℂ) * ζ ^ 29 - ((70 / 79) : ℂ) * ζ ^ 30 - ((89 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep03CoefficientIdentity02 :
    row18_reducedY67_combinationStep03Coefficient02 =
      row18_reducedY67_combinationStep02Coefficient02 +
        row18_reducedY67_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep03Coefficient02 row18_reducedY67_combinationStep02Coefficient02 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep03Coefficient03 : ℂ :=
  (((17 / 237) : ℂ) + ((577 / 474) : ℂ) * ζ ^ 1 + ((265 / 158) : ℂ) * ζ ^ 2 + ((355 / 474) : ℂ) * ζ ^ 3 + ((103 / 158) : ℂ) * ζ ^ 6 - ((92 / 79) : ℂ) * ζ ^ 8 - ((281 / 237) : ℂ) * ζ ^ 9 + ((52 / 237) : ℂ) * ζ ^ 11 - ((81 / 79) : ℂ) * ζ ^ 12 - ((577 / 474) : ℂ) * ζ ^ 13 + ((355 / 474) : ℂ) * ζ ^ 15 - ((577 / 474) : ℂ) * ζ ^ 17 - ((761 / 474) : ℂ) * ζ ^ 18 - ((577 / 474) : ℂ) * ζ ^ 21 - ((265 / 158) : ℂ) * ζ ^ 22 + ((265 / 158) : ℂ) * ζ ^ 24 + ((577 / 474) : ℂ) * ζ ^ 25 + ((52 / 237) : ℂ) * ζ ^ 27 + ((92 / 79) : ℂ) * ζ ^ 28 + ((577 / 474) : ℂ) * ζ ^ 29 + ((81 / 158) : ℂ) * ζ ^ 30 - ((52 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep03CoefficientIdentity03 :
    row18_reducedY67_combinationStep03Coefficient03 =
      row18_reducedY67_combinationStep02Coefficient03 +
        row18_reducedY67_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep03Coefficient03 row18_reducedY67_combinationStep02Coefficient03 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep03Coefficient04 : ℂ :=
  (-((2381 / 2370) : ℂ) + ((69 / 79) : ℂ) * ζ ^ 1 - ((3407 / 2370) : ℂ) * ζ ^ 2 - ((1463 / 1185) : ℂ) * ζ ^ 3 - ((5623 / 2370) : ℂ) * ζ ^ 6 - ((1057 / 2370) : ℂ) * ζ ^ 8 - ((174 / 79) : ℂ) * ζ ^ 9 - ((1031 / 1185) : ℂ) * ζ ^ 11 - ((1108 / 1185) : ℂ) * ζ ^ 12 - ((69 / 79) : ℂ) * ζ ^ 13 - ((1463 / 1185) : ℂ) * ζ ^ 15 - ((69 / 79) : ℂ) * ζ ^ 17 + ((171 / 395) : ℂ) * ζ ^ 18 - ((69 / 79) : ℂ) * ζ ^ 21 + ((3407 / 2370) : ℂ) * ζ ^ 22 - ((3407 / 2370) : ℂ) * ζ ^ 24 + ((69 / 79) : ℂ) * ζ ^ 25 - ((1031 / 1185) : ℂ) * ζ ^ 27 + ((1057 / 2370) : ℂ) * ζ ^ 28 + ((69 / 79) : ℂ) * ζ ^ 29 - ((744 / 395) : ℂ) * ζ ^ 30 + ((1031 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep03CoefficientIdentity04 :
    row18_reducedY67_combinationStep03Coefficient04 =
      row18_reducedY67_combinationStep02Coefficient04 +
        row18_reducedY67_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep03Coefficient04 row18_reducedY67_combinationStep02Coefficient04 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep03Coefficient05 : ℂ :=
  (-((244 / 237) : ℂ) + ((329 / 237) : ℂ) * ζ ^ 1 - ((403 / 474) : ℂ) * ζ ^ 2 - ((35 / 237) : ℂ) * ζ ^ 3 + ((11 / 158) : ℂ) * ζ ^ 5 - ((232 / 237) : ℂ) * ζ ^ 6 - ((815 / 474) : ℂ) * ζ ^ 8 - ((168 / 79) : ℂ) * ζ ^ 9 - ((469 / 237) : ℂ) * ζ ^ 11 - ((815 / 474) : ℂ) * ζ ^ 12 - ((329 / 237) : ℂ) * ζ ^ 13 - ((185 / 158) : ℂ) * ζ ^ 15 - ((329 / 237) : ℂ) * ζ ^ 17 + ((61 / 474) : ℂ) * ζ ^ 18 - ((98 / 79) : ℂ) * ζ ^ 21 + ((403 / 474) : ℂ) * ζ ^ 22 + ((625 / 474) : ℂ) * ζ ^ 25 + ((98 / 79) : ℂ) * ζ ^ 27 + ((815 / 474) : ℂ) * ζ ^ 28 + ((329 / 237) : ℂ) * ζ ^ 29 - ((116 / 237) : ℂ) * ζ ^ 30 + ((469 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep03CoefficientIdentity05 :
    row18_reducedY67_combinationStep03Coefficient05 =
      row18_reducedY67_combinationStep02Coefficient05 +
        row18_reducedY67_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep03Coefficient05 row18_reducedY67_combinationStep02Coefficient05 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 (((226 / 237) : ℂ) - ((48919 / 37446) : ℂ) * ζ ^ 1 + ((441 / 6241) : ℂ) * ζ ^ 2 + ((15223 / 37446) : ℂ) * ζ ^ 3 - ((31713 / 12482) : ℂ) * ζ ^ 4 + ((24187 / 37446) : ℂ) * ζ ^ 5 + ((21217 / 37446) : ℂ) * ζ ^ 6 - ((18675 / 12482) : ℂ) * ζ ^ 7 + ((60107 / 37446) : ℂ) * ζ ^ 8 + ((7735 / 6241) : ℂ) * ζ ^ 9 - ((3419 / 6241) : ℂ) * ζ ^ 10 + ((19883 / 12482) : ℂ) * ζ ^ 11 + ((16849 / 37446) : ℂ) * ζ ^ 12 - ((60097 / 37446) : ℂ) * ζ ^ 13 + ((20129 / 18723) : ℂ) * ζ ^ 14 - ((19873 / 18723) : ℂ) * ζ ^ 15 - ((12468 / 6241) : ℂ) * ζ ^ 16 + ((11531 / 12482) : ℂ) * ζ ^ 17 - ((3245 / 6241) : ℂ) * ζ ^ 18 - ((10361 / 18723) : ℂ) * ζ ^ 19 + ((42779 / 37446) : ℂ) * ζ ^ 20 - ((3157 / 12482) : ℂ) * ζ ^ 21 + ((3082 / 18723) : ℂ) * ζ ^ 22 + ((2719 / 18723) : ℂ) * ζ ^ 23 + ((6629 / 37446) : ℂ) * ζ ^ 24 - ((3385 / 18723) : ℂ) * ζ ^ 25 - ((11141 / 37446) : ℂ) * ζ ^ 26 + ((9169 / 37446) : ℂ) * ζ ^ 27 - ((5074 / 18723) : ℂ) * ζ ^ 28 + ((61 / 237) : ℂ) * ζ ^ 29 - ((448 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep03Coefficient06 : ℂ :=
  (-((1009 / 395) : ℂ) - ((3547 / 2370) : ℂ) * ζ ^ 1 + ((3547 / 2370) : ℂ) * ζ ^ 3 - ((3091 / 2370) : ℂ) * ζ ^ 5 - ((383 / 237) : ℂ) * ζ ^ 6 + ((1009 / 790) : ℂ) * ζ ^ 8 + ((254 / 395) : ℂ) * ζ ^ 9 - ((76 / 395) : ℂ) * ζ ^ 11 + ((656 / 395) : ℂ) * ζ ^ 12 + ((3547 / 2370) : ℂ) * ζ ^ 13 - ((768 / 395) : ℂ) * ζ ^ 15 + ((3547 / 2370) : ℂ) * ζ ^ 17 + ((617 / 474) : ℂ) * ζ ^ 18 - ((1061 / 2370) : ℂ) * ζ ^ 21 - ((353 / 395) : ℂ) * ζ ^ 24 - ((76 / 395) : ℂ) * ζ ^ 25 + ((254 / 395) : ℂ) * ζ ^ 27 - ((1009 / 790) : ℂ) * ζ ^ 28 - ((3547 / 2370) : ℂ) * ζ ^ 29 - ((383 / 237) : ℂ) * ζ ^ 30 + ((76 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep03CoefficientIdentity06 :
    row18_reducedY67_combinationStep03Coefficient06 =
      row18_reducedY67_combinationStep02Coefficient06 +
        row18_reducedY67_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep03Coefficient06 row18_reducedY67_combinationStep02Coefficient06 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep03Coefficient07 : ℂ :=
  (-((37 / 158) : ℂ) - ((133 / 474) : ℂ) * ζ ^ 1 - ((503 / 474) : ℂ) * ζ ^ 2 - ((265 / 237) : ℂ) * ζ ^ 3 - ((91 / 474) : ℂ) * ζ ^ 6 + ((305 / 474) : ℂ) * ζ ^ 8 - ((197 / 474) : ℂ) * ζ ^ 9 - ((41 / 158) : ℂ) * ζ ^ 11 + ((206 / 237) : ℂ) * ζ ^ 12 + ((133 / 474) : ℂ) * ζ ^ 13 - ((265 / 237) : ℂ) * ζ ^ 15 + ((133 / 474) : ℂ) * ζ ^ 17 + ((196 / 237) : ℂ) * ζ ^ 18 + ((133 / 474) : ℂ) * ζ ^ 21 + ((503 / 474) : ℂ) * ζ ^ 22 - ((503 / 474) : ℂ) * ζ ^ 24 - ((133 / 474) : ℂ) * ζ ^ 25 - ((41 / 158) : ℂ) * ζ ^ 27 - ((305 / 474) : ℂ) * ζ ^ 28 - ((133 / 474) : ℂ) * ζ ^ 29 - ((33 / 79) : ℂ) * ζ ^ 30 + ((41 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep03CoefficientIdentity07 :
    row18_reducedY67_combinationStep03Coefficient07 =
      row18_reducedY67_combinationStep02Coefficient07 +
        row18_reducedY67_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep03Coefficient07 row18_reducedY67_combinationStep02Coefficient07 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 (((75 / 158) : ℂ) + ((997 / 6241) : ℂ) * ζ ^ 1 + ((35080 / 18723) : ℂ) * ζ ^ 2 + ((32497 / 37446) : ℂ) * ζ ^ 3 - ((1839 / 6241) : ℂ) * ζ ^ 4 - ((698 / 6241) : ℂ) * ζ ^ 5 - ((14512 / 18723) : ℂ) * ζ ^ 6 - ((20489 / 18723) : ℂ) * ζ ^ 7 + ((2903 / 18723) : ℂ) * ζ ^ 8 - ((782 / 6241) : ℂ) * ζ ^ 9 - ((2029 / 6241) : ℂ) * ζ ^ 10 + ((894 / 6241) : ℂ) * ζ ^ 11 + ((136 / 6241) : ℂ) * ζ ^ 12 - ((13211 / 37446) : ℂ) * ζ ^ 13 + ((6389 / 18723) : ℂ) * ζ ^ 14 + ((2817 / 6241) : ℂ) * ζ ^ 15 - ((1741 / 18723) : ℂ) * ζ ^ 16 - ((14183 / 37446) : ℂ) * ζ ^ 17 - ((5687 / 18723) : ℂ) * ζ ^ 18 - ((4042 / 18723) : ℂ) * ζ ^ 19 + ((3901 / 37446) : ℂ) * ζ ^ 20 - ((6682 / 18723) : ℂ) * ζ ^ 21 - ((18059 / 37446) : ℂ) * ζ ^ 22 + ((15572 / 18723) : ℂ) * ζ ^ 23 + ((6599 / 18723) : ℂ) * ζ ^ 24 - ((163 / 37446) : ℂ) * ζ ^ 25 + ((31951 / 37446) : ℂ) * ζ ^ 26 - ((6023 / 18723) : ℂ) * ζ ^ 27 - ((3241 / 6241) : ℂ) * ζ ^ 28 + ((727 / 12482) : ℂ) * ζ ^ 29 + ((480 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep03CoefficientIdentity08 :
    row18_reducedY67_combinationStep03Coefficient08 =
      row18_reducedY67_combinationStep02Coefficient08 +
        row18_reducedY67_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep03Coefficient08 row18_reducedY67_combinationStep02Coefficient08 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep03CoefficientIdentity09 :
    row18_reducedY67_combinationStep03Coefficient09 =
      row18_reducedY67_combinationStep02Coefficient09 +
        row18_reducedY67_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep03Coefficient09 row18_reducedY67_combinationStep02Coefficient09 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep03CoefficientIdentity10 :
    row18_reducedY67_combinationStep03Coefficient10 =
      row18_reducedY67_combinationStep02Coefficient10 +
        row18_reducedY67_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep03Coefficient10 row18_reducedY67_combinationStep02Coefficient10 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep03CoefficientIdentity11 :
    row18_reducedY67_combinationStep03Coefficient11 =
      row18_reducedY67_combinationStep02Coefficient11 +
        row18_reducedY67_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep03Coefficient11 row18_reducedY67_combinationStep02Coefficient11 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep03CoefficientIdentity12 :
    row18_reducedY67_combinationStep03Coefficient12 =
      row18_reducedY67_combinationStep02Coefficient12 +
        row18_reducedY67_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep03Coefficient12 row18_reducedY67_combinationStep02Coefficient12 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep03CoefficientIdentity13 :
    row18_reducedY67_combinationStep03Coefficient13 =
      row18_reducedY67_combinationStep02Coefficient13 +
        row18_reducedY67_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep03Coefficient13 row18_reducedY67_combinationStep02Coefficient13 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep03CoefficientIdentity14 :
    row18_reducedY67_combinationStep03Coefficient14 =
      row18_reducedY67_combinationStep02Coefficient14 +
        row18_reducedY67_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep03Coefficient14 row18_reducedY67_combinationStep02Coefficient14 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep03CoefficientIdentity15 :
    row18_reducedY67_combinationStep03Coefficient15 =
      row18_reducedY67_combinationStep02Coefficient15 +
        row18_reducedY67_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep03Coefficient15 row18_reducedY67_combinationStep02Coefficient15 row18_reducedY67_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY67_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY67_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY67_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY67_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY67_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY67_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY67_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY67_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY67_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY67_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY67_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY67_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY67_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY67_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY67_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY67_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY67_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY67_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY67_combinationStep03CoefficientIdentity00,
      row18_reducedY67_combinationStep03CoefficientIdentity01,
      row18_reducedY67_combinationStep03CoefficientIdentity02,
      row18_reducedY67_combinationStep03CoefficientIdentity03,
      row18_reducedY67_combinationStep03CoefficientIdentity04,
      row18_reducedY67_combinationStep03CoefficientIdentity05,
      row18_reducedY67_combinationStep03CoefficientIdentity06,
      row18_reducedY67_combinationStep03CoefficientIdentity07,
      row18_reducedY67_combinationStep03CoefficientIdentity08,
      row18_reducedY67_combinationStep03CoefficientIdentity09,
      row18_reducedY67_combinationStep03CoefficientIdentity10,
      row18_reducedY67_combinationStep03CoefficientIdentity11,
      row18_reducedY67_combinationStep03CoefficientIdentity12,
      row18_reducedY67_combinationStep03CoefficientIdentity13,
      row18_reducedY67_combinationStep03CoefficientIdentity14,
      row18_reducedY67_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY67_combinationStep03Multiplier * equation

private def row18_reducedY67_combinationStep04Multiplier : ℂ :=
  (((42 / 79) : ℂ) + ((80 / 79) : ℂ) * ζ ^ 1 + ((216 / 79) : ℂ) * ζ ^ 2 + ((36 / 79) : ℂ) * ζ ^ 3 - ((26 / 79) : ℂ) * ζ ^ 5 + ((204 / 79) : ℂ) * ζ ^ 6 - ((4 / 79) : ℂ) * ζ ^ 8 - ((152 / 79) : ℂ) * ζ ^ 9 - ((188 / 79) : ℂ) * ζ ^ 11 - ((4 / 79) : ℂ) * ζ ^ 12 - ((80 / 79) : ℂ) * ζ ^ 13 - ((142 / 79) : ℂ) * ζ ^ 15 - ((80 / 79) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((116 / 79) : ℂ) * ζ ^ 21 - ((216 / 79) : ℂ) * ζ ^ 22 + ((106 / 79) : ℂ) * ζ ^ 25 + ((116 / 79) : ℂ) * ζ ^ 27 + ((4 / 79) : ℂ) * ζ ^ 28 + ((80 / 79) : ℂ) * ζ ^ 29 + ((102 / 79) : ℂ) * ζ ^ 30 + ((188 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY67_combinationStep04Coefficient00 : ℂ :=
  (((506 / 395) : ℂ) - ((145 / 79) : ℂ) * ζ ^ 1 + ((979 / 790) : ℂ) * ζ ^ 2 + ((1267 / 790) : ℂ) * ζ ^ 3 + ((1841 / 790) : ℂ) * ζ ^ 6 + ((337 / 395) : ℂ) * ζ ^ 8 + ((563 / 158) : ℂ) * ζ ^ 9 + ((719 / 790) : ℂ) * ζ ^ 11 + ((431 / 395) : ℂ) * ζ ^ 12 + ((145 / 79) : ℂ) * ζ ^ 13 + ((1267 / 790) : ℂ) * ζ ^ 15 + ((145 / 79) : ℂ) * ζ ^ 17 + ((33 / 790) : ℂ) * ζ ^ 18 + ((145 / 79) : ℂ) * ζ ^ 21 - ((979 / 790) : ℂ) * ζ ^ 22 + ((979 / 790) : ℂ) * ζ ^ 24 - ((145 / 79) : ℂ) * ζ ^ 25 + ((719 / 790) : ℂ) * ζ ^ 27 - ((337 / 395) : ℂ) * ζ ^ 28 - ((145 / 79) : ℂ) * ζ ^ 29 + ((1653 / 790) : ℂ) * ζ ^ 30 - ((719 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep04CoefficientIdentity00 :
    row18_reducedY67_combinationStep04Coefficient00 =
      row18_reducedY67_combinationStep03Coefficient00 +
        row18_reducedY67_combinationStep04Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep04Coefficient00 row18_reducedY67_combinationStep03Coefficient00 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 (-((1110 / 6241) : ℂ) - ((1477 / 12482) : ℂ) * ζ ^ 1 - ((10069 / 12482) : ℂ) * ζ ^ 2 - ((1516 / 6241) : ℂ) * ζ ^ 3 - ((81 / 6241) : ℂ) * ζ ^ 4 - ((819 / 12482) : ℂ) * ζ ^ 5 + ((1 / 6241) : ℂ) * ζ ^ 6 + ((489 / 12482) : ℂ) * ζ ^ 7 - ((1583 / 12482) : ℂ) * ζ ^ 8 + ((4271 / 12482) : ℂ) * ζ ^ 9 + ((2010 / 6241) : ℂ) * ζ ^ 10 - ((1643 / 6241) : ℂ) * ζ ^ 11 - ((1189 / 6241) : ℂ) * ζ ^ 12 - ((1639 / 6241) : ℂ) * ζ ^ 13 - ((5807 / 12482) : ℂ) * ζ ^ 14 - ((1029 / 6241) : ℂ) * ζ ^ 15 + ((420 / 6241) : ℂ) * ζ ^ 16 + ((1357 / 12482) : ℂ) * ζ ^ 17 + ((2493 / 6241) : ℂ) * ζ ^ 18 - ((2689 / 12482) : ℂ) * ζ ^ 19 + ((403 / 12482) : ℂ) * ζ ^ 20 + ((1645 / 12482) : ℂ) * ζ ^ 21 + ((583 / 12482) : ℂ) * ζ ^ 22 + ((887 / 6241) : ℂ) * ζ ^ 23 - ((2915 / 12482) : ℂ) * ζ ^ 24 - ((1292 / 6241) : ℂ) * ζ ^ 25 - ((1483 / 12482) : ℂ) * ζ ^ 26 - ((4319 / 12482) : ℂ) * ζ ^ 27 + ((313 / 6241) : ℂ) * ζ ^ 28 + ((3747 / 12482) : ℂ) * ζ ^ 29 - ((705 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep04Coefficient01 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep04CoefficientIdentity01 :
    row18_reducedY67_combinationStep04Coefficient01 =
      row18_reducedY67_combinationStep03Coefficient01 +
        row18_reducedY67_combinationStep04Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep04Coefficient01 row18_reducedY67_combinationStep03Coefficient01 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 (((168 / 6241) : ℂ) + ((871 / 12482) : ℂ) * ζ ^ 1 + ((6853 / 12482) : ℂ) * ζ ^ 2 + ((3803 / 12482) : ℂ) * ζ ^ 3 + ((1801 / 6241) : ℂ) * ζ ^ 4 - ((3403 / 12482) : ℂ) * ζ ^ 5 - ((2091 / 6241) : ℂ) * ζ ^ 6 + ((52 / 6241) : ℂ) * ζ ^ 7 + ((363 / 12482) : ℂ) * ζ ^ 8 + ((301 / 6241) : ℂ) * ζ ^ 9 + ((859 / 6241) : ℂ) * ζ ^ 10 - ((1212 / 6241) : ℂ) * ζ ^ 11 - ((1237 / 12482) : ℂ) * ζ ^ 12 - ((1712 / 6241) : ℂ) * ζ ^ 13 - ((500 / 6241) : ℂ) * ζ ^ 14 + ((2861 / 12482) : ℂ) * ζ ^ 15 + ((263 / 6241) : ℂ) * ζ ^ 16 - ((1110 / 6241) : ℂ) * ζ ^ 17 - ((2386 / 6241) : ℂ) * ζ ^ 18 - ((1731 / 6241) : ℂ) * ζ ^ 19 - ((1627 / 12482) : ℂ) * ζ ^ 20 - ((75 / 6241) : ℂ) * ζ ^ 21 + ((613 / 12482) : ℂ) * ζ ^ 22 + ((9 / 79) : ℂ) * ζ ^ 23 - ((1722 / 6241) : ℂ) * ζ ^ 24 - ((34 / 6241) : ℂ) * ζ ^ 25 + ((73 / 6241) : ℂ) * ζ ^ 26 + ((1577 / 12482) : ℂ) * ζ ^ 27 + ((543 / 6241) : ℂ) * ζ ^ 28 + ((207 / 6241) : ℂ) * ζ ^ 29 - ((658 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep04Coefficient02 : ℂ :=
  (((52 / 237) : ℂ) * ζ ^ 1 - ((775 / 237) : ℂ) * ζ ^ 2 + ((52 / 237) : ℂ) * ζ ^ 3 + ((319 / 237) : ℂ) * ζ ^ 5 - ((565 / 237) : ℂ) * ζ ^ 6 - ((3383 / 474) : ℂ) * ζ ^ 8 - ((96 / 79) : ℂ) * ζ ^ 9 + ((89 / 79) : ℂ) * ζ ^ 11 - ((982 / 237) : ℂ) * ζ ^ 12 - ((52 / 237) : ℂ) * ζ ^ 13 + ((403 / 237) : ℂ) * ζ ^ 15 - ((52 / 237) : ℂ) * ζ ^ 17 + ((775 / 474) : ℂ) * ζ ^ 18 - ((455 / 237) : ℂ) * ζ ^ 21 + ((775 / 237) : ℂ) * ζ ^ 22 + ((982 / 237) : ℂ) * ζ ^ 24 - ((89 / 79) : ℂ) * ζ ^ 25 + ((96 / 79) : ℂ) * ζ ^ 27 + ((3383 / 474) : ℂ) * ζ ^ 28 + ((52 / 237) : ℂ) * ζ ^ 29 - ((70 / 79) : ℂ) * ζ ^ 30 - ((89 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep04CoefficientIdentity02 :
    row18_reducedY67_combinationStep04Coefficient02 =
      row18_reducedY67_combinationStep03Coefficient02 +
        row18_reducedY67_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep04Coefficient02 row18_reducedY67_combinationStep03Coefficient02 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep04Coefficient03 : ℂ :=
  (((17 / 237) : ℂ) + ((577 / 474) : ℂ) * ζ ^ 1 + ((265 / 158) : ℂ) * ζ ^ 2 + ((355 / 474) : ℂ) * ζ ^ 3 + ((103 / 158) : ℂ) * ζ ^ 6 - ((92 / 79) : ℂ) * ζ ^ 8 - ((281 / 237) : ℂ) * ζ ^ 9 + ((52 / 237) : ℂ) * ζ ^ 11 - ((81 / 79) : ℂ) * ζ ^ 12 - ((577 / 474) : ℂ) * ζ ^ 13 + ((355 / 474) : ℂ) * ζ ^ 15 - ((577 / 474) : ℂ) * ζ ^ 17 - ((761 / 474) : ℂ) * ζ ^ 18 - ((577 / 474) : ℂ) * ζ ^ 21 - ((265 / 158) : ℂ) * ζ ^ 22 + ((265 / 158) : ℂ) * ζ ^ 24 + ((577 / 474) : ℂ) * ζ ^ 25 + ((52 / 237) : ℂ) * ζ ^ 27 + ((92 / 79) : ℂ) * ζ ^ 28 + ((577 / 474) : ℂ) * ζ ^ 29 + ((81 / 158) : ℂ) * ζ ^ 30 - ((52 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep04CoefficientIdentity03 :
    row18_reducedY67_combinationStep04Coefficient03 =
      row18_reducedY67_combinationStep03Coefficient03 +
        row18_reducedY67_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep04Coefficient03 row18_reducedY67_combinationStep03Coefficient03 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep04Coefficient04 : ℂ :=
  (-((2381 / 2370) : ℂ) + ((69 / 79) : ℂ) * ζ ^ 1 - ((3407 / 2370) : ℂ) * ζ ^ 2 - ((1463 / 1185) : ℂ) * ζ ^ 3 - ((5623 / 2370) : ℂ) * ζ ^ 6 - ((1057 / 2370) : ℂ) * ζ ^ 8 - ((174 / 79) : ℂ) * ζ ^ 9 - ((1031 / 1185) : ℂ) * ζ ^ 11 - ((1108 / 1185) : ℂ) * ζ ^ 12 - ((69 / 79) : ℂ) * ζ ^ 13 - ((1463 / 1185) : ℂ) * ζ ^ 15 - ((69 / 79) : ℂ) * ζ ^ 17 + ((171 / 395) : ℂ) * ζ ^ 18 - ((69 / 79) : ℂ) * ζ ^ 21 + ((3407 / 2370) : ℂ) * ζ ^ 22 - ((3407 / 2370) : ℂ) * ζ ^ 24 + ((69 / 79) : ℂ) * ζ ^ 25 - ((1031 / 1185) : ℂ) * ζ ^ 27 + ((1057 / 2370) : ℂ) * ζ ^ 28 + ((69 / 79) : ℂ) * ζ ^ 29 - ((744 / 395) : ℂ) * ζ ^ 30 + ((1031 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep04CoefficientIdentity04 :
    row18_reducedY67_combinationStep04Coefficient04 =
      row18_reducedY67_combinationStep03Coefficient04 +
        row18_reducedY67_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep04Coefficient04 row18_reducedY67_combinationStep03Coefficient04 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep04Coefficient05 : ℂ :=
  (-((244 / 237) : ℂ) + ((329 / 237) : ℂ) * ζ ^ 1 - ((403 / 474) : ℂ) * ζ ^ 2 - ((35 / 237) : ℂ) * ζ ^ 3 + ((11 / 158) : ℂ) * ζ ^ 5 - ((232 / 237) : ℂ) * ζ ^ 6 - ((815 / 474) : ℂ) * ζ ^ 8 - ((168 / 79) : ℂ) * ζ ^ 9 - ((469 / 237) : ℂ) * ζ ^ 11 - ((815 / 474) : ℂ) * ζ ^ 12 - ((329 / 237) : ℂ) * ζ ^ 13 - ((185 / 158) : ℂ) * ζ ^ 15 - ((329 / 237) : ℂ) * ζ ^ 17 + ((61 / 474) : ℂ) * ζ ^ 18 - ((98 / 79) : ℂ) * ζ ^ 21 + ((403 / 474) : ℂ) * ζ ^ 22 + ((625 / 474) : ℂ) * ζ ^ 25 + ((98 / 79) : ℂ) * ζ ^ 27 + ((815 / 474) : ℂ) * ζ ^ 28 + ((329 / 237) : ℂ) * ζ ^ 29 - ((116 / 237) : ℂ) * ζ ^ 30 + ((469 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep04CoefficientIdentity05 :
    row18_reducedY67_combinationStep04Coefficient05 =
      row18_reducedY67_combinationStep03Coefficient05 +
        row18_reducedY67_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep04Coefficient05 row18_reducedY67_combinationStep03Coefficient05 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep04Coefficient06 : ℂ :=
  (-((1009 / 395) : ℂ) - ((3547 / 2370) : ℂ) * ζ ^ 1 + ((3547 / 2370) : ℂ) * ζ ^ 3 - ((3091 / 2370) : ℂ) * ζ ^ 5 - ((383 / 237) : ℂ) * ζ ^ 6 + ((1009 / 790) : ℂ) * ζ ^ 8 + ((254 / 395) : ℂ) * ζ ^ 9 - ((76 / 395) : ℂ) * ζ ^ 11 + ((656 / 395) : ℂ) * ζ ^ 12 + ((3547 / 2370) : ℂ) * ζ ^ 13 - ((768 / 395) : ℂ) * ζ ^ 15 + ((3547 / 2370) : ℂ) * ζ ^ 17 + ((617 / 474) : ℂ) * ζ ^ 18 - ((1061 / 2370) : ℂ) * ζ ^ 21 - ((353 / 395) : ℂ) * ζ ^ 24 - ((76 / 395) : ℂ) * ζ ^ 25 + ((254 / 395) : ℂ) * ζ ^ 27 - ((1009 / 790) : ℂ) * ζ ^ 28 - ((3547 / 2370) : ℂ) * ζ ^ 29 - ((383 / 237) : ℂ) * ζ ^ 30 + ((76 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep04CoefficientIdentity06 :
    row18_reducedY67_combinationStep04Coefficient06 =
      row18_reducedY67_combinationStep03Coefficient06 +
        row18_reducedY67_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep04Coefficient06 row18_reducedY67_combinationStep03Coefficient06 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep04Coefficient07 : ℂ :=
  (-((37 / 158) : ℂ) - ((133 / 474) : ℂ) * ζ ^ 1 - ((503 / 474) : ℂ) * ζ ^ 2 - ((265 / 237) : ℂ) * ζ ^ 3 - ((91 / 474) : ℂ) * ζ ^ 6 + ((305 / 474) : ℂ) * ζ ^ 8 - ((197 / 474) : ℂ) * ζ ^ 9 - ((41 / 158) : ℂ) * ζ ^ 11 + ((206 / 237) : ℂ) * ζ ^ 12 + ((133 / 474) : ℂ) * ζ ^ 13 - ((265 / 237) : ℂ) * ζ ^ 15 + ((133 / 474) : ℂ) * ζ ^ 17 + ((196 / 237) : ℂ) * ζ ^ 18 + ((133 / 474) : ℂ) * ζ ^ 21 + ((503 / 474) : ℂ) * ζ ^ 22 - ((503 / 474) : ℂ) * ζ ^ 24 - ((133 / 474) : ℂ) * ζ ^ 25 - ((41 / 158) : ℂ) * ζ ^ 27 - ((305 / 474) : ℂ) * ζ ^ 28 - ((133 / 474) : ℂ) * ζ ^ 29 - ((33 / 79) : ℂ) * ζ ^ 30 + ((41 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep04CoefficientIdentity07 :
    row18_reducedY67_combinationStep04Coefficient07 =
      row18_reducedY67_combinationStep03Coefficient07 +
        row18_reducedY67_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep04Coefficient07 row18_reducedY67_combinationStep03Coefficient07 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep04Coefficient08 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep04CoefficientIdentity08 :
    row18_reducedY67_combinationStep04Coefficient08 =
      row18_reducedY67_combinationStep03Coefficient08 +
        row18_reducedY67_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep04Coefficient08 row18_reducedY67_combinationStep03Coefficient08 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep04Coefficient09 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep04CoefficientIdentity09 :
    row18_reducedY67_combinationStep04Coefficient09 =
      row18_reducedY67_combinationStep03Coefficient09 +
        row18_reducedY67_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep04Coefficient09 row18_reducedY67_combinationStep03Coefficient09 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep04Coefficient10 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep04CoefficientIdentity10 :
    row18_reducedY67_combinationStep04Coefficient10 =
      row18_reducedY67_combinationStep03Coefficient10 +
        row18_reducedY67_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep04Coefficient10 row18_reducedY67_combinationStep03Coefficient10 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep04Coefficient11 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep04CoefficientIdentity11 :
    row18_reducedY67_combinationStep04Coefficient11 =
      row18_reducedY67_combinationStep03Coefficient11 +
        row18_reducedY67_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep04Coefficient11 row18_reducedY67_combinationStep03Coefficient11 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep04Coefficient12 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep04CoefficientIdentity12 :
    row18_reducedY67_combinationStep04Coefficient12 =
      row18_reducedY67_combinationStep03Coefficient12 +
        row18_reducedY67_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep04Coefficient12 row18_reducedY67_combinationStep03Coefficient12 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep04Coefficient13 : ℂ :=
  (((46 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep04CoefficientIdentity13 :
    row18_reducedY67_combinationStep04Coefficient13 =
      row18_reducedY67_combinationStep03Coefficient13 +
        row18_reducedY67_combinationStep04Multiplier *
          (-((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((73 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((105 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((73 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep04Coefficient13 row18_reducedY67_combinationStep03Coefficient13 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 (-((3760 / 6241) : ℂ) - ((57 / 158) : ℂ) * ζ ^ 1 - ((852 / 6241) : ℂ) * ζ ^ 2 + ((7557 / 12482) : ℂ) * ζ ^ 3 + ((7563 / 6241) : ℂ) * ζ ^ 4 + ((7657 / 12482) : ℂ) * ζ ^ 5 + ((991 / 12482) : ℂ) * ζ ^ 6 - ((4428 / 6241) : ℂ) * ζ ^ 7 - ((4807 / 6241) : ℂ) * ζ ^ 8 + ((827 / 6241) : ℂ) * ζ ^ 9 + ((1856 / 6241) : ℂ) * ζ ^ 10 + ((5218 / 6241) : ℂ) * ζ ^ 11 + ((973 / 6241) : ℂ) * ζ ^ 12 - ((6075 / 12482) : ℂ) * ζ ^ 13 + ((786 / 6241) : ℂ) * ζ ^ 14 + ((413 / 12482) : ℂ) * ζ ^ 15 + ((5961 / 12482) : ℂ) * ζ ^ 16 + ((6632 / 6241) : ℂ) * ζ ^ 17 + ((724 / 6241) : ℂ) * ζ ^ 18 - ((113 / 6241) : ℂ) * ζ ^ 19 - ((5 / 6241) : ℂ) * ζ ^ 20 - ((3235 / 6241) : ℂ) * ζ ^ 21 + ((219 / 6241) : ℂ) * ζ ^ 22 + ((85 / 12482) : ℂ) * ζ ^ 23 - ((1190 / 6241) : ℂ) * ζ ^ 24 - ((795 / 12482) : ℂ) * ζ ^ 25 - ((2975 / 12482) : ℂ) * ζ ^ 26 - ((4519 / 12482) : ℂ) * ζ ^ 27 - ((1205 / 6241) : ℂ) * ζ ^ 28 - ((1109 / 6241) : ℂ) * ζ ^ 29 - ((658 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep04Coefficient14 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep04CoefficientIdentity14 :
    row18_reducedY67_combinationStep04Coefficient14 =
      row18_reducedY67_combinationStep03Coefficient14 +
        row18_reducedY67_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep04Coefficient14 row18_reducedY67_combinationStep03Coefficient14 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep04Coefficient15 : ℂ :=
  (-((9 / 79) : ℂ) + ((2 / 79) : ℂ) * ζ ^ 1 - ((33 / 79) : ℂ) * ζ ^ 2 - ((33 / 79) : ℂ) * ζ ^ 6 + ((9 / 79) : ℂ) * ζ ^ 8 + ((19 / 79) : ℂ) * ζ ^ 9 - ((2 / 79) : ℂ) * ζ ^ 13 - ((2 / 79) : ℂ) * ζ ^ 17 + ((24 / 79) : ℂ) * ζ ^ 18 - ((2 / 79) : ℂ) * ζ ^ 21 + ((33 / 79) : ℂ) * ζ ^ 22 - ((33 / 79) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 25 - ((9 / 79) : ℂ) * ζ ^ 28 + ((2 / 79) : ℂ) * ζ ^ 29 - ((24 / 79) : ℂ) * ζ ^ 30)

private theorem row18_reducedY67_combinationStep04CoefficientIdentity15 :
    row18_reducedY67_combinationStep04Coefficient15 =
      row18_reducedY67_combinationStep03Coefficient15 +
        row18_reducedY67_combinationStep04Multiplier *
          (((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep04Coefficient15 row18_reducedY67_combinationStep03Coefficient15 row18_reducedY67_combinationStep04Multiplier
  close_cyclotomic_row18 (((1110 / 6241) : ℂ) + ((1477 / 12482) : ℂ) * ζ ^ 1 + ((10069 / 12482) : ℂ) * ζ ^ 2 + ((1516 / 6241) : ℂ) * ζ ^ 3 + ((81 / 6241) : ℂ) * ζ ^ 4 + ((819 / 12482) : ℂ) * ζ ^ 5 - ((1 / 6241) : ℂ) * ζ ^ 6 - ((489 / 12482) : ℂ) * ζ ^ 7 + ((1583 / 12482) : ℂ) * ζ ^ 8 - ((4271 / 12482) : ℂ) * ζ ^ 9 - ((2010 / 6241) : ℂ) * ζ ^ 10 + ((1643 / 6241) : ℂ) * ζ ^ 11 + ((1189 / 6241) : ℂ) * ζ ^ 12 + ((1639 / 6241) : ℂ) * ζ ^ 13 + ((5807 / 12482) : ℂ) * ζ ^ 14 + ((1029 / 6241) : ℂ) * ζ ^ 15 - ((420 / 6241) : ℂ) * ζ ^ 16 - ((1357 / 12482) : ℂ) * ζ ^ 17 - ((2493 / 6241) : ℂ) * ζ ^ 18 + ((2689 / 12482) : ℂ) * ζ ^ 19 - ((403 / 12482) : ℂ) * ζ ^ 20 - ((1645 / 12482) : ℂ) * ζ ^ 21 - ((583 / 12482) : ℂ) * ζ ^ 22 - ((887 / 6241) : ℂ) * ζ ^ 23 + ((2915 / 12482) : ℂ) * ζ ^ 24 + ((1292 / 6241) : ℂ) * ζ ^ 25 + ((1483 / 12482) : ℂ) * ζ ^ 26 + ((4319 / 12482) : ℂ) * ζ ^ 27 - ((313 / 6241) : ℂ) * ζ ^ 28 - ((3747 / 12482) : ℂ) * ζ ^ 29 + ((705 / 6241) : ℂ) * ζ ^ 30)

private theorem row18_reducedY67_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY67_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY67_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY67_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY67_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY67_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY67_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY67_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY67_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY67_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY67_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY67_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY67_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY67_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY67_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY67_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY67_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY67_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation07
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY67_combinationStep04CoefficientIdentity00,
      row18_reducedY67_combinationStep04CoefficientIdentity01,
      row18_reducedY67_combinationStep04CoefficientIdentity02,
      row18_reducedY67_combinationStep04CoefficientIdentity03,
      row18_reducedY67_combinationStep04CoefficientIdentity04,
      row18_reducedY67_combinationStep04CoefficientIdentity05,
      row18_reducedY67_combinationStep04CoefficientIdentity06,
      row18_reducedY67_combinationStep04CoefficientIdentity07,
      row18_reducedY67_combinationStep04CoefficientIdentity08,
      row18_reducedY67_combinationStep04CoefficientIdentity09,
      row18_reducedY67_combinationStep04CoefficientIdentity10,
      row18_reducedY67_combinationStep04CoefficientIdentity11,
      row18_reducedY67_combinationStep04CoefficientIdentity12,
      row18_reducedY67_combinationStep04CoefficientIdentity13,
      row18_reducedY67_combinationStep04CoefficientIdentity14,
      row18_reducedY67_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY67_combinationStep04Multiplier * equation

private def row18_reducedY67_combinationStep05Multiplier : ℂ :=
  (-((1052 / 1185) : ℂ) * ζ ^ 1 - ((828 / 395) : ℂ) * ζ ^ 2 - ((1052 / 1185) : ℂ) * ζ ^ 3 + ((2084 / 1185) : ℂ) * ζ ^ 5 - ((1202 / 395) : ℂ) * ζ ^ 6 - ((200 / 237) : ℂ) * ζ ^ 8 + ((1488 / 395) : ℂ) * ζ ^ 9 + ((3136 / 1185) : ℂ) * ζ ^ 11 - ((90 / 79) : ℂ) * ζ ^ 12 + ((1052 / 1185) : ℂ) * ζ ^ 13 + ((2608 / 1185) : ℂ) * ζ ^ 15 + ((1052 / 1185) : ℂ) * ζ ^ 17 + ((414 / 395) : ℂ) * ζ ^ 18 - ((1556 / 1185) : ℂ) * ζ ^ 21 + ((828 / 395) : ℂ) * ζ ^ 22 + ((90 / 79) : ℂ) * ζ ^ 24 - ((3136 / 1185) : ℂ) * ζ ^ 25 - ((1488 / 395) : ℂ) * ζ ^ 27 + ((200 / 237) : ℂ) * ζ ^ 28 - ((1052 / 1185) : ℂ) * ζ ^ 29 + ((374 / 395) : ℂ) * ζ ^ 30 - ((3136 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY67_combinationStep05Coefficient00 : ℂ :=
  (((506 / 395) : ℂ) - ((145 / 79) : ℂ) * ζ ^ 1 + ((979 / 790) : ℂ) * ζ ^ 2 + ((1267 / 790) : ℂ) * ζ ^ 3 + ((1841 / 790) : ℂ) * ζ ^ 6 + ((337 / 395) : ℂ) * ζ ^ 8 + ((563 / 158) : ℂ) * ζ ^ 9 + ((719 / 790) : ℂ) * ζ ^ 11 + ((431 / 395) : ℂ) * ζ ^ 12 + ((145 / 79) : ℂ) * ζ ^ 13 + ((1267 / 790) : ℂ) * ζ ^ 15 + ((145 / 79) : ℂ) * ζ ^ 17 + ((33 / 790) : ℂ) * ζ ^ 18 + ((145 / 79) : ℂ) * ζ ^ 21 - ((979 / 790) : ℂ) * ζ ^ 22 + ((979 / 790) : ℂ) * ζ ^ 24 - ((145 / 79) : ℂ) * ζ ^ 25 + ((719 / 790) : ℂ) * ζ ^ 27 - ((337 / 395) : ℂ) * ζ ^ 28 - ((145 / 79) : ℂ) * ζ ^ 29 + ((1653 / 790) : ℂ) * ζ ^ 30 - ((719 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep05CoefficientIdentity00 :
    row18_reducedY67_combinationStep05Coefficient00 =
      row18_reducedY67_combinationStep04Coefficient00 +
        row18_reducedY67_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep05Coefficient00 row18_reducedY67_combinationStep04Coefficient00 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep05Coefficient01 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep05CoefficientIdentity01 :
    row18_reducedY67_combinationStep05Coefficient01 =
      row18_reducedY67_combinationStep04Coefficient01 +
        row18_reducedY67_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep05Coefficient01 row18_reducedY67_combinationStep04Coefficient01 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep05Coefficient02 : ℂ :=
  (((243 / 790) : ℂ) * ζ ^ 1 - ((319 / 79) : ℂ) * ζ ^ 2 + ((243 / 790) : ℂ) * ζ ^ 3 + ((2627 / 2370) : ℂ) * ζ ^ 5 - ((688 / 237) : ℂ) * ζ ^ 6 - ((3101 / 474) : ℂ) * ζ ^ 8 - ((1244 / 1185) : ℂ) * ζ ^ 9 + ((949 / 1185) : ℂ) * ζ ^ 11 - ((1001 / 237) : ℂ) * ζ ^ 12 - ((243 / 790) : ℂ) * ζ ^ 13 + ((439 / 395) : ℂ) * ζ ^ 15 - ((243 / 790) : ℂ) * ζ ^ 17 + ((319 / 158) : ℂ) * ζ ^ 18 - ((1121 / 790) : ℂ) * ζ ^ 21 + ((319 / 79) : ℂ) * ζ ^ 22 + ((1001 / 237) : ℂ) * ζ ^ 24 - ((949 / 1185) : ℂ) * ζ ^ 25 + ((1244 / 1185) : ℂ) * ζ ^ 27 + ((3101 / 474) : ℂ) * ζ ^ 28 + ((243 / 790) : ℂ) * ζ ^ 29 - ((269 / 237) : ℂ) * ζ ^ 30 - ((949 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep05CoefficientIdentity02 :
    row18_reducedY67_combinationStep05Coefficient02 =
      row18_reducedY67_combinationStep04Coefficient02 +
        row18_reducedY67_combinationStep05Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep05Coefficient02 row18_reducedY67_combinationStep04Coefficient02 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 (-((10199 / 187230) : ℂ) * ζ ^ 1 + ((25483 / 31205) : ℂ) * ζ ^ 2 + ((20849 / 187230) : ℂ) * ζ ^ 3 + ((49366 / 93615) : ℂ) * ζ ^ 4 + ((42199 / 93615) : ℂ) * ζ ^ 5 - ((6844 / 93615) : ℂ) * ζ ^ 6 - ((44411 / 93615) : ℂ) * ζ ^ 7 + ((191 / 37446) : ℂ) * ζ ^ 8 - ((76417 / 93615) : ℂ) * ζ ^ 9 + ((3964 / 31205) : ℂ) * ζ ^ 10 - ((20773 / 62410) : ℂ) * ζ ^ 11 + ((38413 / 62410) : ℂ) * ζ ^ 12 + ((57077 / 187230) : ℂ) * ζ ^ 13 + ((31537 / 93615) : ℂ) * ζ ^ 14 + ((12868 / 31205) : ℂ) * ζ ^ 15 - ((40373 / 187230) : ℂ) * ζ ^ 16 + ((32353 / 93615) : ℂ) * ζ ^ 17 - ((61939 / 187230) : ℂ) * ζ ^ 18 - ((76639 / 187230) : ℂ) * ζ ^ 19 + ((1063 / 18723) : ℂ) * ζ ^ 20 - ((7256 / 18723) : ℂ) * ζ ^ 21 - ((9743 / 187230) : ℂ) * ζ ^ 22 + ((59521 / 187230) : ℂ) * ζ ^ 23 - ((14049 / 31205) : ℂ) * ζ ^ 24 + ((33973 / 187230) : ℂ) * ζ ^ 25 - ((63101 / 187230) : ℂ) * ζ ^ 26 + ((25489 / 62410) : ℂ) * ζ ^ 27 - ((5598 / 31205) : ℂ) * ζ ^ 28 + ((16471 / 93615) : ℂ) * ζ ^ 29 - ((10976 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep05Coefficient03 : ℂ :=
  (((55 / 158) : ℂ) + ((121 / 474) : ℂ) * ζ ^ 1 + ((701 / 474) : ℂ) * ζ ^ 2 + ((265 / 237) : ℂ) * ζ ^ 3 + ((289 / 474) : ℂ) * ζ ^ 6 - ((359 / 474) : ℂ) * ζ ^ 8 + ((83 / 474) : ℂ) * ζ ^ 9 + ((41 / 158) : ℂ) * ζ ^ 11 - ((206 / 237) : ℂ) * ζ ^ 12 - ((121 / 474) : ℂ) * ζ ^ 13 + ((265 / 237) : ℂ) * ζ ^ 15 - ((121 / 474) : ℂ) * ζ ^ 17 - ((268 / 237) : ℂ) * ζ ^ 18 - ((121 / 474) : ℂ) * ζ ^ 21 - ((701 / 474) : ℂ) * ζ ^ 22 + ((701 / 474) : ℂ) * ζ ^ 24 + ((121 / 474) : ℂ) * ζ ^ 25 + ((41 / 158) : ℂ) * ζ ^ 27 + ((359 / 474) : ℂ) * ζ ^ 28 + ((121 / 474) : ℂ) * ζ ^ 29 + ((57 / 79) : ℂ) * ζ ^ 30 - ((41 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep05CoefficientIdentity03 :
    row18_reducedY67_combinationStep05Coefficient03 =
      row18_reducedY67_combinationStep04Coefficient03 +
        row18_reducedY67_combinationStep05Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep05Coefficient03 row18_reducedY67_combinationStep04Coefficient03 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 (-((131 / 474) : ℂ) + ((23971 / 31205) : ℂ) * ζ ^ 1 - ((643 / 31205) : ℂ) * ζ ^ 2 - ((4583 / 187230) : ℂ) * ζ ^ 3 + ((23867 / 62410) : ℂ) * ζ ^ 4 - ((18159 / 31205) : ℂ) * ζ ^ 5 - ((34037 / 37446) : ℂ) * ζ ^ 6 + ((115879 / 93615) : ℂ) * ζ ^ 7 - ((223637 / 187230) : ℂ) * ζ ^ 8 + ((3809 / 187230) : ℂ) * ζ ^ 9 - ((60439 / 187230) : ℂ) * ζ ^ 10 + ((23003 / 93615) : ℂ) * ζ ^ 11 - ((157667 / 187230) : ℂ) * ζ ^ 12 + ((9612 / 31205) : ℂ) * ζ ^ 13 + ((19492 / 93615) : ℂ) * ζ ^ 14 - ((114659 / 187230) : ℂ) * ζ ^ 15 - ((20903 / 62410) : ℂ) * ζ ^ 16 - ((17102 / 18723) : ℂ) * ζ ^ 17 - ((80899 / 187230) : ℂ) * ζ ^ 18 - ((30692 / 93615) : ℂ) * ζ ^ 19 - ((178121 / 187230) : ℂ) * ζ ^ 20 - ((14971 / 31205) : ℂ) * ζ ^ 21 + ((41447 / 62410) : ℂ) * ζ ^ 22 - ((120346 / 93615) : ℂ) * ζ ^ 23 + ((23696 / 93615) : ℂ) * ζ ^ 24 - ((122189 / 187230) : ℂ) * ζ ^ 25 + ((47146 / 93615) : ℂ) * ζ ^ 26 - ((191893 / 187230) : ℂ) * ζ ^ 27 + ((992 / 1185) : ℂ) * ζ ^ 28 - ((25793 / 62410) : ℂ) * ζ ^ 29 - ((10192 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep05Coefficient04 : ℂ :=
  (-((506 / 395) : ℂ) + ((145 / 79) : ℂ) * ζ ^ 1 - ((979 / 790) : ℂ) * ζ ^ 2 - ((1267 / 790) : ℂ) * ζ ^ 3 - ((1841 / 790) : ℂ) * ζ ^ 6 - ((337 / 395) : ℂ) * ζ ^ 8 - ((563 / 158) : ℂ) * ζ ^ 9 - ((719 / 790) : ℂ) * ζ ^ 11 - ((431 / 395) : ℂ) * ζ ^ 12 - ((145 / 79) : ℂ) * ζ ^ 13 - ((1267 / 790) : ℂ) * ζ ^ 15 - ((145 / 79) : ℂ) * ζ ^ 17 - ((33 / 790) : ℂ) * ζ ^ 18 - ((145 / 79) : ℂ) * ζ ^ 21 + ((979 / 790) : ℂ) * ζ ^ 22 - ((979 / 790) : ℂ) * ζ ^ 24 + ((145 / 79) : ℂ) * ζ ^ 25 - ((719 / 790) : ℂ) * ζ ^ 27 + ((337 / 395) : ℂ) * ζ ^ 28 + ((145 / 79) : ℂ) * ζ ^ 29 - ((1653 / 790) : ℂ) * ζ ^ 30 + ((719 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep05CoefficientIdentity04 :
    row18_reducedY67_combinationStep05Coefficient04 =
      row18_reducedY67_combinationStep04Coefficient04 +
        row18_reducedY67_combinationStep05Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep05Coefficient04 row18_reducedY67_combinationStep04Coefficient04 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 (((131 / 474) : ℂ) - ((23971 / 31205) : ℂ) * ζ ^ 1 + ((643 / 31205) : ℂ) * ζ ^ 2 + ((4583 / 187230) : ℂ) * ζ ^ 3 - ((23867 / 62410) : ℂ) * ζ ^ 4 + ((18159 / 31205) : ℂ) * ζ ^ 5 + ((34037 / 37446) : ℂ) * ζ ^ 6 - ((115879 / 93615) : ℂ) * ζ ^ 7 + ((223637 / 187230) : ℂ) * ζ ^ 8 - ((3809 / 187230) : ℂ) * ζ ^ 9 + ((60439 / 187230) : ℂ) * ζ ^ 10 - ((23003 / 93615) : ℂ) * ζ ^ 11 + ((157667 / 187230) : ℂ) * ζ ^ 12 - ((9612 / 31205) : ℂ) * ζ ^ 13 - ((19492 / 93615) : ℂ) * ζ ^ 14 + ((114659 / 187230) : ℂ) * ζ ^ 15 + ((20903 / 62410) : ℂ) * ζ ^ 16 + ((17102 / 18723) : ℂ) * ζ ^ 17 + ((80899 / 187230) : ℂ) * ζ ^ 18 + ((30692 / 93615) : ℂ) * ζ ^ 19 + ((178121 / 187230) : ℂ) * ζ ^ 20 + ((14971 / 31205) : ℂ) * ζ ^ 21 - ((41447 / 62410) : ℂ) * ζ ^ 22 + ((120346 / 93615) : ℂ) * ζ ^ 23 - ((23696 / 93615) : ℂ) * ζ ^ 24 + ((122189 / 187230) : ℂ) * ζ ^ 25 - ((47146 / 93615) : ℂ) * ζ ^ 26 + ((191893 / 187230) : ℂ) * ζ ^ 27 - ((992 / 1185) : ℂ) * ζ ^ 28 + ((25793 / 62410) : ℂ) * ζ ^ 29 + ((10192 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep05Coefficient05 : ℂ :=
  (-((244 / 237) : ℂ) + ((329 / 237) : ℂ) * ζ ^ 1 - ((403 / 474) : ℂ) * ζ ^ 2 - ((35 / 237) : ℂ) * ζ ^ 3 + ((11 / 158) : ℂ) * ζ ^ 5 - ((232 / 237) : ℂ) * ζ ^ 6 - ((815 / 474) : ℂ) * ζ ^ 8 - ((168 / 79) : ℂ) * ζ ^ 9 - ((469 / 237) : ℂ) * ζ ^ 11 - ((815 / 474) : ℂ) * ζ ^ 12 - ((329 / 237) : ℂ) * ζ ^ 13 - ((185 / 158) : ℂ) * ζ ^ 15 - ((329 / 237) : ℂ) * ζ ^ 17 + ((61 / 474) : ℂ) * ζ ^ 18 - ((98 / 79) : ℂ) * ζ ^ 21 + ((403 / 474) : ℂ) * ζ ^ 22 + ((625 / 474) : ℂ) * ζ ^ 25 + ((98 / 79) : ℂ) * ζ ^ 27 + ((815 / 474) : ℂ) * ζ ^ 28 + ((329 / 237) : ℂ) * ζ ^ 29 - ((116 / 237) : ℂ) * ζ ^ 30 + ((469 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep05CoefficientIdentity05 :
    row18_reducedY67_combinationStep05Coefficient05 =
      row18_reducedY67_combinationStep04Coefficient05 +
        row18_reducedY67_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep05Coefficient05 row18_reducedY67_combinationStep04Coefficient05 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep05Coefficient06 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep05CoefficientIdentity06 :
    row18_reducedY67_combinationStep05Coefficient06 =
      row18_reducedY67_combinationStep04Coefficient06 +
        row18_reducedY67_combinationStep05Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep05Coefficient06 row18_reducedY67_combinationStep04Coefficient06 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 (-((1009 / 395) : ℂ) - ((263381 / 187230) : ℂ) * ζ ^ 1 + ((11621 / 31205) : ℂ) * ζ ^ 2 + ((446213 / 187230) : ℂ) * ζ ^ 3 + ((326402 / 93615) : ℂ) * ζ ^ 4 - ((15706 / 93615) : ℂ) * ζ ^ 5 - ((181474 / 93615) : ℂ) * ζ ^ 6 - ((188492 / 93615) : ℂ) * ζ ^ 7 + ((1379 / 93615) : ℂ) * ζ ^ 8 - ((36259 / 187230) : ℂ) * ζ ^ 9 + ((124217 / 93615) : ℂ) * ζ ^ 10 + ((110254 / 93615) : ℂ) * ζ ^ 11 - ((2549 / 18723) : ℂ) * ζ ^ 12 - ((26587 / 31205) : ℂ) * ζ ^ 13 - ((89291 / 37446) : ℂ) * ζ ^ 14 - ((43847 / 37446) : ℂ) * ζ ^ 15 + ((12334 / 93615) : ℂ) * ζ ^ 16 + ((12766 / 18723) : ℂ) * ζ ^ 17 + ((58093 / 93615) : ℂ) * ζ ^ 18 - ((7243 / 18723) : ℂ) * ζ ^ 19 - ((415987 / 187230) : ℂ) * ζ ^ 20 - ((318533 / 187230) : ℂ) * ζ ^ 21 - ((51556 / 93615) : ℂ) * ζ ^ 22 + ((125203 / 93615) : ℂ) * ζ ^ 23 - ((30142 / 93615) : ℂ) * ζ ^ 24 + ((2821 / 6241) : ℂ) * ζ ^ 25 - ((6009 / 6241) : ℂ) * ζ ^ 26 - ((14537 / 187230) : ℂ) * ζ ^ 27 + ((9064 / 18723) : ℂ) * ζ ^ 28 + ((3654 / 31205) : ℂ) * ζ ^ 29 + ((21952 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep05Coefficient07 : ℂ :=
  (-((37 / 158) : ℂ) - ((133 / 474) : ℂ) * ζ ^ 1 - ((503 / 474) : ℂ) * ζ ^ 2 - ((265 / 237) : ℂ) * ζ ^ 3 - ((91 / 474) : ℂ) * ζ ^ 6 + ((305 / 474) : ℂ) * ζ ^ 8 - ((197 / 474) : ℂ) * ζ ^ 9 - ((41 / 158) : ℂ) * ζ ^ 11 + ((206 / 237) : ℂ) * ζ ^ 12 + ((133 / 474) : ℂ) * ζ ^ 13 - ((265 / 237) : ℂ) * ζ ^ 15 + ((133 / 474) : ℂ) * ζ ^ 17 + ((196 / 237) : ℂ) * ζ ^ 18 + ((133 / 474) : ℂ) * ζ ^ 21 + ((503 / 474) : ℂ) * ζ ^ 22 - ((503 / 474) : ℂ) * ζ ^ 24 - ((133 / 474) : ℂ) * ζ ^ 25 - ((41 / 158) : ℂ) * ζ ^ 27 - ((305 / 474) : ℂ) * ζ ^ 28 - ((133 / 474) : ℂ) * ζ ^ 29 - ((33 / 79) : ℂ) * ζ ^ 30 + ((41 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep05CoefficientIdentity07 :
    row18_reducedY67_combinationStep05Coefficient07 =
      row18_reducedY67_combinationStep04Coefficient07 +
        row18_reducedY67_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep05Coefficient07 row18_reducedY67_combinationStep04Coefficient07 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep05Coefficient08 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep05CoefficientIdentity08 :
    row18_reducedY67_combinationStep05Coefficient08 =
      row18_reducedY67_combinationStep04Coefficient08 +
        row18_reducedY67_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep05Coefficient08 row18_reducedY67_combinationStep04Coefficient08 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep05Coefficient09 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep05CoefficientIdentity09 :
    row18_reducedY67_combinationStep05Coefficient09 =
      row18_reducedY67_combinationStep04Coefficient09 +
        row18_reducedY67_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep05Coefficient09 row18_reducedY67_combinationStep04Coefficient09 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep05Coefficient10 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep05CoefficientIdentity10 :
    row18_reducedY67_combinationStep05Coefficient10 =
      row18_reducedY67_combinationStep04Coefficient10 +
        row18_reducedY67_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep05Coefficient10 row18_reducedY67_combinationStep04Coefficient10 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep05Coefficient11 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep05CoefficientIdentity11 :
    row18_reducedY67_combinationStep05Coefficient11 =
      row18_reducedY67_combinationStep04Coefficient11 +
        row18_reducedY67_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep05Coefficient11 row18_reducedY67_combinationStep04Coefficient11 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep05Coefficient12 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep05CoefficientIdentity12 :
    row18_reducedY67_combinationStep05Coefficient12 =
      row18_reducedY67_combinationStep04Coefficient12 +
        row18_reducedY67_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep05Coefficient12 row18_reducedY67_combinationStep04Coefficient12 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep05Coefficient13 : ℂ :=
  (((46 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep05CoefficientIdentity13 :
    row18_reducedY67_combinationStep05Coefficient13 =
      row18_reducedY67_combinationStep04Coefficient13 +
        row18_reducedY67_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep05Coefficient13 row18_reducedY67_combinationStep04Coefficient13 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep05Coefficient14 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep05CoefficientIdentity14 :
    row18_reducedY67_combinationStep05Coefficient14 =
      row18_reducedY67_combinationStep04Coefficient14 +
        row18_reducedY67_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep05Coefficient14 row18_reducedY67_combinationStep04Coefficient14 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep05Coefficient15 : ℂ :=
  (-((9 / 79) : ℂ) + ((2 / 79) : ℂ) * ζ ^ 1 - ((33 / 79) : ℂ) * ζ ^ 2 - ((33 / 79) : ℂ) * ζ ^ 6 + ((9 / 79) : ℂ) * ζ ^ 8 + ((19 / 79) : ℂ) * ζ ^ 9 - ((2 / 79) : ℂ) * ζ ^ 13 - ((2 / 79) : ℂ) * ζ ^ 17 + ((24 / 79) : ℂ) * ζ ^ 18 - ((2 / 79) : ℂ) * ζ ^ 21 + ((33 / 79) : ℂ) * ζ ^ 22 - ((33 / 79) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 25 - ((9 / 79) : ℂ) * ζ ^ 28 + ((2 / 79) : ℂ) * ζ ^ 29 - ((24 / 79) : ℂ) * ζ ^ 30)

private theorem row18_reducedY67_combinationStep05CoefficientIdentity15 :
    row18_reducedY67_combinationStep05Coefficient15 =
      row18_reducedY67_combinationStep04Coefficient15 +
        row18_reducedY67_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep05Coefficient15 row18_reducedY67_combinationStep04Coefficient15 row18_reducedY67_combinationStep05Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY67_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY67_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY67_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY67_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY67_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY67_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY67_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY67_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY67_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY67_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY67_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY67_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY67_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY67_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY67_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY67_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY67_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY67_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY67_combinationStep05CoefficientIdentity00,
      row18_reducedY67_combinationStep05CoefficientIdentity01,
      row18_reducedY67_combinationStep05CoefficientIdentity02,
      row18_reducedY67_combinationStep05CoefficientIdentity03,
      row18_reducedY67_combinationStep05CoefficientIdentity04,
      row18_reducedY67_combinationStep05CoefficientIdentity05,
      row18_reducedY67_combinationStep05CoefficientIdentity06,
      row18_reducedY67_combinationStep05CoefficientIdentity07,
      row18_reducedY67_combinationStep05CoefficientIdentity08,
      row18_reducedY67_combinationStep05CoefficientIdentity09,
      row18_reducedY67_combinationStep05CoefficientIdentity10,
      row18_reducedY67_combinationStep05CoefficientIdentity11,
      row18_reducedY67_combinationStep05CoefficientIdentity12,
      row18_reducedY67_combinationStep05CoefficientIdentity13,
      row18_reducedY67_combinationStep05CoefficientIdentity14,
      row18_reducedY67_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY67_combinationStep05Multiplier * equation

private def row18_reducedY67_combinationStep06Multiplier : ℂ :=
  (-((350 / 79) : ℂ) - ((122 / 237) : ℂ) * ζ ^ 1 + ((1720 / 237) : ℂ) * ζ ^ 2 + ((932 / 237) : ℂ) * ζ ^ 3 - ((296 / 237) : ℂ) * ζ ^ 5 + ((1480 / 237) : ℂ) * ζ ^ 6 + ((1298 / 237) : ℂ) * ζ ^ 8 - ((26 / 237) : ℂ) * ζ ^ 9 - ((730 / 79) : ℂ) * ζ ^ 11 + ((80 / 79) : ℂ) * ζ ^ 12 + ((122 / 237) : ℂ) * ζ ^ 13 - ((932 / 237) : ℂ) * ζ ^ 15 + ((122 / 237) : ℂ) * ζ ^ 17 - ((670 / 237) : ℂ) * ζ ^ 18 + ((58 / 79) : ℂ) * ζ ^ 21 - ((1720 / 237) : ℂ) * ζ ^ 22 - ((1720 / 237) : ℂ) * ζ ^ 24 + ((58 / 79) : ℂ) * ζ ^ 25 + ((730 / 79) : ℂ) * ζ ^ 27 - ((1298 / 237) : ℂ) * ζ ^ 28 - ((122 / 237) : ℂ) * ζ ^ 29 + ((422 / 237) : ℂ) * ζ ^ 30 + ((730 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY67_combinationStep06Coefficient00 : ℂ :=
  (((506 / 395) : ℂ) - ((145 / 79) : ℂ) * ζ ^ 1 + ((979 / 790) : ℂ) * ζ ^ 2 + ((1267 / 790) : ℂ) * ζ ^ 3 + ((1841 / 790) : ℂ) * ζ ^ 6 + ((337 / 395) : ℂ) * ζ ^ 8 + ((563 / 158) : ℂ) * ζ ^ 9 + ((719 / 790) : ℂ) * ζ ^ 11 + ((431 / 395) : ℂ) * ζ ^ 12 + ((145 / 79) : ℂ) * ζ ^ 13 + ((1267 / 790) : ℂ) * ζ ^ 15 + ((145 / 79) : ℂ) * ζ ^ 17 + ((33 / 790) : ℂ) * ζ ^ 18 + ((145 / 79) : ℂ) * ζ ^ 21 - ((979 / 790) : ℂ) * ζ ^ 22 + ((979 / 790) : ℂ) * ζ ^ 24 - ((145 / 79) : ℂ) * ζ ^ 25 + ((719 / 790) : ℂ) * ζ ^ 27 - ((337 / 395) : ℂ) * ζ ^ 28 - ((145 / 79) : ℂ) * ζ ^ 29 + ((1653 / 790) : ℂ) * ζ ^ 30 - ((719 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep06CoefficientIdentity00 :
    row18_reducedY67_combinationStep06Coefficient00 =
      row18_reducedY67_combinationStep05Coefficient00 +
        row18_reducedY67_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep06Coefficient00 row18_reducedY67_combinationStep05Coefficient00 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep06Coefficient01 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep06CoefficientIdentity01 :
    row18_reducedY67_combinationStep06Coefficient01 =
      row18_reducedY67_combinationStep05Coefficient01 +
        row18_reducedY67_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep06Coefficient01 row18_reducedY67_combinationStep05Coefficient01 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep06Coefficient02 : ℂ :=
  (-((131 / 395) : ℂ) * ζ ^ 1 - ((200 / 79) : ℂ) * ζ ^ 2 - ((131 / 395) : ℂ) * ζ ^ 3 - ((1048 / 395) : ℂ) * ζ ^ 5 - ((156 / 79) : ℂ) * ζ ^ 6 - ((124 / 79) : ℂ) * ζ ^ 8 - ((708 / 395) : ℂ) * ζ ^ 9 - ((917 / 395) : ℂ) * ζ ^ 11 - ((120 / 79) : ℂ) * ζ ^ 12 + ((131 / 395) : ℂ) * ζ ^ 13 - ((451 / 395) : ℂ) * ζ ^ 15 + ((131 / 395) : ℂ) * ζ ^ 17 + ((100 / 79) : ℂ) * ζ ^ 18 + ((582 / 395) : ℂ) * ζ ^ 21 + ((200 / 79) : ℂ) * ζ ^ 22 + ((120 / 79) : ℂ) * ζ ^ 24 + ((917 / 395) : ℂ) * ζ ^ 25 + ((708 / 395) : ℂ) * ζ ^ 27 + ((124 / 79) : ℂ) * ζ ^ 28 - ((131 / 395) : ℂ) * ζ ^ 29 - ((44 / 79) : ℂ) * ζ ^ 30 + ((917 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep06CoefficientIdentity02 :
    row18_reducedY67_combinationStep06Coefficient02 =
      row18_reducedY67_combinationStep05Coefficient02 +
        row18_reducedY67_combinationStep06Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep06Coefficient02 row18_reducedY67_combinationStep05Coefficient02 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 (-((3325 / 6241) : ℂ) + ((14222 / 18723) : ℂ) * ζ ^ 1 - ((14354 / 18723) : ℂ) * ζ ^ 2 + ((21197 / 18723) : ℂ) * ζ ^ 3 + ((4136 / 6241) : ℂ) * ζ ^ 4 + ((30425 / 12482) : ℂ) * ζ ^ 5 - ((2521 / 18723) : ℂ) * ζ ^ 6 - ((9286 / 6241) : ℂ) * ζ ^ 7 - ((19075 / 6241) : ℂ) * ζ ^ 8 - ((26615 / 37446) : ℂ) * ζ ^ 9 - ((16633 / 18723) : ℂ) * ζ ^ 10 + ((1333 / 18723) : ℂ) * ζ ^ 11 - ((14645 / 37446) : ℂ) * ζ ^ 12 + ((33239 / 37446) : ℂ) * ζ ^ 13 + ((8030 / 6241) : ℂ) * ζ ^ 14 + ((76079 / 37446) : ℂ) * ζ ^ 15 - ((4442 / 18723) : ℂ) * ζ ^ 16 - ((51013 / 37446) : ℂ) * ζ ^ 17 - ((10325 / 6241) : ℂ) * ζ ^ 18 + ((5596 / 18723) : ℂ) * ζ ^ 19 + ((8871 / 12482) : ℂ) * ζ ^ 20 + ((6883 / 18723) : ℂ) * ζ ^ 21 - ((377 / 12482) : ℂ) * ζ ^ 22 - ((543 / 12482) : ℂ) * ζ ^ 23 - ((45533 / 37446) : ℂ) * ζ ^ 24 + ((5584 / 18723) : ℂ) * ζ ^ 25 + ((20273 / 12482) : ℂ) * ζ ^ 26 + ((74525 / 37446) : ℂ) * ζ ^ 27 - ((3908 / 6241) : ℂ) * ζ ^ 28 - ((18575 / 12482) : ℂ) * ζ ^ 29 - ((5475 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep06Coefficient03 : ℂ :=
  (((9 / 79) : ℂ) - ((2 / 79) : ℂ) * ζ ^ 1 + ((33 / 79) : ℂ) * ζ ^ 2 + ((33 / 79) : ℂ) * ζ ^ 6 - ((9 / 79) : ℂ) * ζ ^ 8 - ((19 / 79) : ℂ) * ζ ^ 9 + ((2 / 79) : ℂ) * ζ ^ 13 + ((2 / 79) : ℂ) * ζ ^ 17 - ((24 / 79) : ℂ) * ζ ^ 18 + ((2 / 79) : ℂ) * ζ ^ 21 - ((33 / 79) : ℂ) * ζ ^ 22 + ((33 / 79) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 25 + ((9 / 79) : ℂ) * ζ ^ 28 - ((2 / 79) : ℂ) * ζ ^ 29 + ((24 / 79) : ℂ) * ζ ^ 30)

private theorem row18_reducedY67_combinationStep06CoefficientIdentity03 :
    row18_reducedY67_combinationStep06Coefficient03 =
      row18_reducedY67_combinationStep05Coefficient03 +
        row18_reducedY67_combinationStep06Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep06Coefficient03 row18_reducedY67_combinationStep05Coefficient03 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 (-((2677 / 12482) : ℂ) - ((10685 / 18723) : ℂ) * ζ ^ 1 - ((4815 / 12482) : ℂ) * ζ ^ 2 + ((68569 / 18723) : ℂ) * ζ ^ 3 + ((27905 / 6241) : ℂ) * ζ ^ 4 - ((5267 / 6241) : ℂ) * ζ ^ 5 - ((2491 / 18723) : ℂ) * ζ ^ 6 - ((5455 / 6241) : ℂ) * ζ ^ 7 + ((2867 / 37446) : ℂ) * ζ ^ 8 - ((27631 / 37446) : ℂ) * ζ ^ 9 + ((69713 / 37446) : ℂ) * ζ ^ 10 + ((42475 / 12482) : ℂ) * ζ ^ 11 - ((3847 / 6241) : ℂ) * ζ ^ 12 - ((533 / 237) : ℂ) * ζ ^ 13 - ((58471 / 37446) : ℂ) * ζ ^ 14 + ((3678 / 6241) : ℂ) * ζ ^ 15 + ((5755 / 18723) : ℂ) * ζ ^ 16 + ((81175 / 37446) : ℂ) * ζ ^ 17 + ((54881 / 18723) : ℂ) * ζ ^ 18 - ((14809 / 37446) : ℂ) * ζ ^ 19 - ((86451 / 12482) : ℂ) * ζ ^ 20 - ((140599 / 37446) : ℂ) * ζ ^ 21 + ((5615 / 12482) : ℂ) * ζ ^ 22 + ((67006 / 18723) : ℂ) * ζ ^ 23 - ((15143 / 12482) : ℂ) * ζ ^ 24 - ((23969 / 12482) : ℂ) * ζ ^ 25 - ((54417 / 12482) : ℂ) * ζ ^ 26 + ((5531 / 37446) : ℂ) * ζ ^ 27 + ((65771 / 37446) : ℂ) * ζ ^ 28 + ((16094 / 18723) : ℂ) * ζ ^ 29 + ((5110 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep06Coefficient04 : ℂ :=
  (-((506 / 395) : ℂ) + ((145 / 79) : ℂ) * ζ ^ 1 - ((979 / 790) : ℂ) * ζ ^ 2 - ((1267 / 790) : ℂ) * ζ ^ 3 - ((1841 / 790) : ℂ) * ζ ^ 6 - ((337 / 395) : ℂ) * ζ ^ 8 - ((563 / 158) : ℂ) * ζ ^ 9 - ((719 / 790) : ℂ) * ζ ^ 11 - ((431 / 395) : ℂ) * ζ ^ 12 - ((145 / 79) : ℂ) * ζ ^ 13 - ((1267 / 790) : ℂ) * ζ ^ 15 - ((145 / 79) : ℂ) * ζ ^ 17 - ((33 / 790) : ℂ) * ζ ^ 18 - ((145 / 79) : ℂ) * ζ ^ 21 + ((979 / 790) : ℂ) * ζ ^ 22 - ((979 / 790) : ℂ) * ζ ^ 24 + ((145 / 79) : ℂ) * ζ ^ 25 - ((719 / 790) : ℂ) * ζ ^ 27 + ((337 / 395) : ℂ) * ζ ^ 28 + ((145 / 79) : ℂ) * ζ ^ 29 - ((1653 / 790) : ℂ) * ζ ^ 30 + ((719 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep06CoefficientIdentity04 :
    row18_reducedY67_combinationStep06Coefficient04 =
      row18_reducedY67_combinationStep05Coefficient04 +
        row18_reducedY67_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep06Coefficient04 row18_reducedY67_combinationStep05Coefficient04 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep06Coefficient05 : ℂ :=
  (-((63 / 79) : ℂ) + ((41 / 79) : ℂ) * ζ ^ 1 - ((537 / 158) : ℂ) * ζ ^ 2 - ((179 / 158) : ℂ) * ζ ^ 3 - ((235 / 158) : ℂ) * ζ ^ 5 - ((326 / 79) : ℂ) * ζ ^ 6 - ((225 / 158) : ℂ) * ζ ^ 8 - ((269 / 158) : ℂ) * ζ ^ 9 - ((45 / 79) : ℂ) * ζ ^ 11 - ((225 / 158) : ℂ) * ζ ^ 12 - ((41 / 79) : ℂ) * ζ ^ 13 - ((69 / 79) : ℂ) * ζ ^ 15 - ((41 / 79) : ℂ) * ζ ^ 17 + ((115 / 158) : ℂ) * ζ ^ 18 + ((97 / 158) : ℂ) * ζ ^ 21 + ((537 / 158) : ℂ) * ζ ^ 22 + ((317 / 158) : ℂ) * ζ ^ 25 - ((97 / 158) : ℂ) * ζ ^ 27 + ((225 / 158) : ℂ) * ζ ^ 28 + ((41 / 79) : ℂ) * ζ ^ 29 - ((163 / 79) : ℂ) * ζ ^ 30 + ((45 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep06CoefficientIdentity05 :
    row18_reducedY67_combinationStep06Coefficient05 =
      row18_reducedY67_combinationStep05Coefficient05 +
        row18_reducedY67_combinationStep06Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep06Coefficient05 row18_reducedY67_combinationStep05Coefficient05 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 (((27535 / 37446) : ℂ) - ((3934 / 18723) : ℂ) * ζ ^ 1 + ((17816 / 18723) : ℂ) * ζ ^ 2 + ((46019 / 18723) : ℂ) * ζ ^ 3 + ((5921 / 37446) : ℂ) * ζ ^ 4 + ((5203 / 37446) : ℂ) * ζ ^ 5 + ((42245 / 37446) : ℂ) * ζ ^ 6 + ((8342 / 6241) : ℂ) * ζ ^ 7 - ((66497 / 18723) : ℂ) * ζ ^ 8 + ((19259 / 37446) : ℂ) * ζ ^ 9 + ((1749 / 6241) : ℂ) * ζ ^ 10 - ((13159 / 37446) : ℂ) * ζ ^ 11 - ((20757 / 12482) : ℂ) * ζ ^ 12 + ((54133 / 37446) : ℂ) * ζ ^ 13 + ((108169 / 37446) : ℂ) * ζ ^ 14 - ((10709 / 37446) : ℂ) * ζ ^ 15 - ((15277 / 18723) : ℂ) * ζ ^ 16 + ((16243 / 37446) : ℂ) * ζ ^ 17 + ((25028 / 18723) : ℂ) * ζ ^ 18 - ((30485 / 12482) : ℂ) * ζ ^ 19 - ((66857 / 37446) : ℂ) * ζ ^ 20 - ((1120 / 18723) : ℂ) * ζ ^ 21 + ((15323 / 37446) : ℂ) * ζ ^ 22 - ((148297 / 37446) : ℂ) * ζ ^ 23 + ((30290 / 18723) : ℂ) * ζ ^ 24 - ((24676 / 18723) : ℂ) * ζ ^ 25 + ((4643 / 37446) : ℂ) * ζ ^ 26 - ((27872 / 18723) : ℂ) * ζ ^ 27 + ((41237 / 18723) : ℂ) * ζ ^ 28 - ((61873 / 37446) : ℂ) * ζ ^ 29 - ((4745 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep06Coefficient06 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep06CoefficientIdentity06 :
    row18_reducedY67_combinationStep06Coefficient06 =
      row18_reducedY67_combinationStep05Coefficient06 +
        row18_reducedY67_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep06Coefficient06 row18_reducedY67_combinationStep05Coefficient06 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep06Coefficient07 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep06CoefficientIdentity07 :
    row18_reducedY67_combinationStep06Coefficient07 =
      row18_reducedY67_combinationStep05Coefficient07 +
        row18_reducedY67_combinationStep06Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep06Coefficient07 row18_reducedY67_combinationStep05Coefficient07 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 (((2677 / 12482) : ℂ) + ((10685 / 18723) : ℂ) * ζ ^ 1 + ((4815 / 12482) : ℂ) * ζ ^ 2 - ((68569 / 18723) : ℂ) * ζ ^ 3 - ((27905 / 6241) : ℂ) * ζ ^ 4 + ((5267 / 6241) : ℂ) * ζ ^ 5 + ((2491 / 18723) : ℂ) * ζ ^ 6 + ((5455 / 6241) : ℂ) * ζ ^ 7 - ((2867 / 37446) : ℂ) * ζ ^ 8 + ((27631 / 37446) : ℂ) * ζ ^ 9 - ((69713 / 37446) : ℂ) * ζ ^ 10 - ((42475 / 12482) : ℂ) * ζ ^ 11 + ((3847 / 6241) : ℂ) * ζ ^ 12 + ((533 / 237) : ℂ) * ζ ^ 13 + ((58471 / 37446) : ℂ) * ζ ^ 14 - ((3678 / 6241) : ℂ) * ζ ^ 15 - ((5755 / 18723) : ℂ) * ζ ^ 16 - ((81175 / 37446) : ℂ) * ζ ^ 17 - ((54881 / 18723) : ℂ) * ζ ^ 18 + ((14809 / 37446) : ℂ) * ζ ^ 19 + ((86451 / 12482) : ℂ) * ζ ^ 20 + ((140599 / 37446) : ℂ) * ζ ^ 21 - ((5615 / 12482) : ℂ) * ζ ^ 22 - ((67006 / 18723) : ℂ) * ζ ^ 23 + ((15143 / 12482) : ℂ) * ζ ^ 24 + ((23969 / 12482) : ℂ) * ζ ^ 25 + ((54417 / 12482) : ℂ) * ζ ^ 26 - ((5531 / 37446) : ℂ) * ζ ^ 27 - ((65771 / 37446) : ℂ) * ζ ^ 28 - ((16094 / 18723) : ℂ) * ζ ^ 29 - ((5110 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep06Coefficient08 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep06CoefficientIdentity08 :
    row18_reducedY67_combinationStep06Coefficient08 =
      row18_reducedY67_combinationStep05Coefficient08 +
        row18_reducedY67_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep06Coefficient08 row18_reducedY67_combinationStep05Coefficient08 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep06Coefficient09 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep06CoefficientIdentity09 :
    row18_reducedY67_combinationStep06Coefficient09 =
      row18_reducedY67_combinationStep05Coefficient09 +
        row18_reducedY67_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep06Coefficient09 row18_reducedY67_combinationStep05Coefficient09 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep06Coefficient10 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep06CoefficientIdentity10 :
    row18_reducedY67_combinationStep06Coefficient10 =
      row18_reducedY67_combinationStep05Coefficient10 +
        row18_reducedY67_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep06Coefficient10 row18_reducedY67_combinationStep05Coefficient10 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep06Coefficient11 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep06CoefficientIdentity11 :
    row18_reducedY67_combinationStep06Coefficient11 =
      row18_reducedY67_combinationStep05Coefficient11 +
        row18_reducedY67_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep06Coefficient11 row18_reducedY67_combinationStep05Coefficient11 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep06Coefficient12 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep06CoefficientIdentity12 :
    row18_reducedY67_combinationStep06Coefficient12 =
      row18_reducedY67_combinationStep05Coefficient12 +
        row18_reducedY67_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep06Coefficient12 row18_reducedY67_combinationStep05Coefficient12 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep06Coefficient13 : ℂ :=
  (((46 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep06CoefficientIdentity13 :
    row18_reducedY67_combinationStep06Coefficient13 =
      row18_reducedY67_combinationStep05Coefficient13 +
        row18_reducedY67_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep06Coefficient13 row18_reducedY67_combinationStep05Coefficient13 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep06Coefficient14 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep06CoefficientIdentity14 :
    row18_reducedY67_combinationStep06Coefficient14 =
      row18_reducedY67_combinationStep05Coefficient14 +
        row18_reducedY67_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep06Coefficient14 row18_reducedY67_combinationStep05Coefficient14 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep06Coefficient15 : ℂ :=
  (-((9 / 79) : ℂ) + ((2 / 79) : ℂ) * ζ ^ 1 - ((33 / 79) : ℂ) * ζ ^ 2 - ((33 / 79) : ℂ) * ζ ^ 6 + ((9 / 79) : ℂ) * ζ ^ 8 + ((19 / 79) : ℂ) * ζ ^ 9 - ((2 / 79) : ℂ) * ζ ^ 13 - ((2 / 79) : ℂ) * ζ ^ 17 + ((24 / 79) : ℂ) * ζ ^ 18 - ((2 / 79) : ℂ) * ζ ^ 21 + ((33 / 79) : ℂ) * ζ ^ 22 - ((33 / 79) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 25 - ((9 / 79) : ℂ) * ζ ^ 28 + ((2 / 79) : ℂ) * ζ ^ 29 - ((24 / 79) : ℂ) * ζ ^ 30)

private theorem row18_reducedY67_combinationStep06CoefficientIdentity15 :
    row18_reducedY67_combinationStep06Coefficient15 =
      row18_reducedY67_combinationStep05Coefficient15 +
        row18_reducedY67_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep06Coefficient15 row18_reducedY67_combinationStep05Coefficient15 row18_reducedY67_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY67_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY67_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY67_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY67_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY67_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY67_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY67_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY67_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY67_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY67_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY67_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY67_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY67_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY67_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY67_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY67_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY67_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY67_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY67_combinationStep06CoefficientIdentity00,
      row18_reducedY67_combinationStep06CoefficientIdentity01,
      row18_reducedY67_combinationStep06CoefficientIdentity02,
      row18_reducedY67_combinationStep06CoefficientIdentity03,
      row18_reducedY67_combinationStep06CoefficientIdentity04,
      row18_reducedY67_combinationStep06CoefficientIdentity05,
      row18_reducedY67_combinationStep06CoefficientIdentity06,
      row18_reducedY67_combinationStep06CoefficientIdentity07,
      row18_reducedY67_combinationStep06CoefficientIdentity08,
      row18_reducedY67_combinationStep06CoefficientIdentity09,
      row18_reducedY67_combinationStep06CoefficientIdentity10,
      row18_reducedY67_combinationStep06CoefficientIdentity11,
      row18_reducedY67_combinationStep06CoefficientIdentity12,
      row18_reducedY67_combinationStep06CoefficientIdentity13,
      row18_reducedY67_combinationStep06CoefficientIdentity14,
      row18_reducedY67_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY67_combinationStep06Multiplier * equation

private def row18_reducedY67_combinationStep07Multiplier : ℂ :=
  (-((54 / 79) : ℂ) - ((18 / 79) : ℂ) * ζ ^ 1 - ((80 / 79) : ℂ) * ζ ^ 2 - ((142 / 79) : ℂ) * ζ ^ 3 + ((148 / 79) : ℂ) * ζ ^ 5 + ((40 / 79) : ℂ) * ζ ^ 6 - ((70 / 79) : ℂ) * ζ ^ 8 + ((92 / 79) : ℂ) * ζ ^ 9 + ((136 / 79) : ℂ) * ζ ^ 11 - ((120 / 79) : ℂ) * ζ ^ 12 + ((18 / 79) : ℂ) * ζ ^ 13 + ((142 / 79) : ℂ) * ζ ^ 15 + ((18 / 79) : ℂ) * ζ ^ 17 + ((134 / 79) : ℂ) * ζ ^ 18 - ((166 / 79) : ℂ) * ζ ^ 21 + ((80 / 79) : ℂ) * ζ ^ 22 + ((80 / 79) : ℂ) * ζ ^ 24 - ((166 / 79) : ℂ) * ζ ^ 25 - ((136 / 79) : ℂ) * ζ ^ 27 + ((70 / 79) : ℂ) * ζ ^ 28 - ((18 / 79) : ℂ) * ζ ^ 29 - ((10 / 79) : ℂ) * ζ ^ 30 - ((136 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY67_combinationStep07Coefficient00 : ℂ :=
  (((506 / 395) : ℂ) - ((145 / 79) : ℂ) * ζ ^ 1 + ((979 / 790) : ℂ) * ζ ^ 2 + ((1267 / 790) : ℂ) * ζ ^ 3 + ((1841 / 790) : ℂ) * ζ ^ 6 + ((337 / 395) : ℂ) * ζ ^ 8 + ((563 / 158) : ℂ) * ζ ^ 9 + ((719 / 790) : ℂ) * ζ ^ 11 + ((431 / 395) : ℂ) * ζ ^ 12 + ((145 / 79) : ℂ) * ζ ^ 13 + ((1267 / 790) : ℂ) * ζ ^ 15 + ((145 / 79) : ℂ) * ζ ^ 17 + ((33 / 790) : ℂ) * ζ ^ 18 + ((145 / 79) : ℂ) * ζ ^ 21 - ((979 / 790) : ℂ) * ζ ^ 22 + ((979 / 790) : ℂ) * ζ ^ 24 - ((145 / 79) : ℂ) * ζ ^ 25 + ((719 / 790) : ℂ) * ζ ^ 27 - ((337 / 395) : ℂ) * ζ ^ 28 - ((145 / 79) : ℂ) * ζ ^ 29 + ((1653 / 790) : ℂ) * ζ ^ 30 - ((719 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep07CoefficientIdentity00 :
    row18_reducedY67_combinationStep07Coefficient00 =
      row18_reducedY67_combinationStep06Coefficient00 +
        row18_reducedY67_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep07Coefficient00 row18_reducedY67_combinationStep06Coefficient00 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep07Coefficient01 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep07CoefficientIdentity01 :
    row18_reducedY67_combinationStep07Coefficient01 =
      row18_reducedY67_combinationStep06Coefficient01 +
        row18_reducedY67_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep07Coefficient01 row18_reducedY67_combinationStep06Coefficient01 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep07Coefficient02 : ℂ :=
  (((49 / 395) : ℂ) * ζ ^ 1 - ((200 / 79) : ℂ) * ζ ^ 2 + ((49 / 395) : ℂ) * ζ ^ 3 - ((998 / 395) : ℂ) * ζ ^ 5 - ((156 / 79) : ℂ) * ζ ^ 6 - ((192 / 79) : ℂ) * ζ ^ 8 - ((708 / 395) : ℂ) * ζ ^ 9 - ((1047 / 395) : ℂ) * ζ ^ 11 - ((117 / 79) : ℂ) * ζ ^ 12 - ((49 / 395) : ℂ) * ζ ^ 13 - ((581 / 395) : ℂ) * ζ ^ 15 - ((49 / 395) : ℂ) * ζ ^ 17 + ((100 / 79) : ℂ) * ζ ^ 18 + ((532 / 395) : ℂ) * ζ ^ 21 + ((200 / 79) : ℂ) * ζ ^ 22 + ((117 / 79) : ℂ) * ζ ^ 24 + ((1047 / 395) : ℂ) * ζ ^ 25 + ((708 / 395) : ℂ) * ζ ^ 27 + ((192 / 79) : ℂ) * ζ ^ 28 + ((49 / 395) : ℂ) * ζ ^ 29 - ((44 / 79) : ℂ) * ζ ^ 30 + ((1047 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep07CoefficientIdentity02 :
    row18_reducedY67_combinationStep07Coefficient02 =
      row18_reducedY67_combinationStep06Coefficient02 +
        row18_reducedY67_combinationStep07Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep07Coefficient02 row18_reducedY67_combinationStep06Coefficient02 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 (((513 / 6241) : ℂ) - ((4995 / 12482) : ℂ) * ζ ^ 1 + ((967 / 6241) : ℂ) * ζ ^ 2 - ((1723 / 12482) : ℂ) * ζ ^ 3 + ((7 / 158) : ℂ) * ζ ^ 4 + ((1172 / 6241) : ℂ) * ζ ^ 5 - ((517 / 6241) : ℂ) * ζ ^ 6 + ((955 / 12482) : ℂ) * ζ ^ 7 + ((4646 / 6241) : ℂ) * ζ ^ 8 + ((17 / 6241) : ℂ) * ζ ^ 9 - ((783 / 12482) : ℂ) * ζ ^ 10 - ((2847 / 12482) : ℂ) * ζ ^ 11 - ((1339 / 6241) : ℂ) * ζ ^ 12 + ((3971 / 12482) : ℂ) * ζ ^ 13 - ((1240 / 6241) : ℂ) * ζ ^ 14 + ((1196 / 6241) : ℂ) * ζ ^ 15 + ((728 / 6241) : ℂ) * ζ ^ 16 + ((246 / 6241) : ℂ) * ζ ^ 17 + ((7 / 12482) : ℂ) * ζ ^ 18 - ((483 / 6241) : ℂ) * ζ ^ 19 - ((457 / 6241) : ℂ) * ζ ^ 20 + ((2747 / 12482) : ℂ) * ζ ^ 21 + ((1079 / 12482) : ℂ) * ζ ^ 22 - ((1177 / 6241) : ℂ) * ζ ^ 23 + ((17 / 6241) : ℂ) * ζ ^ 24 - ((37 / 6241) : ℂ) * ζ ^ 25 + ((536 / 6241) : ℂ) * ζ ^ 26 + ((1560 / 6241) : ℂ) * ζ ^ 27 + ((779 / 12482) : ℂ) * ζ ^ 28 - ((3189 / 12482) : ℂ) * ζ ^ 29 + ((510 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep07Coefficient03 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep07CoefficientIdentity03 :
    row18_reducedY67_combinationStep07Coefficient03 =
      row18_reducedY67_combinationStep06Coefficient03 +
        row18_reducedY67_combinationStep07Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep07Coefficient03 row18_reducedY67_combinationStep06Coefficient03 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 (((495 / 6241) : ℂ) - ((757 / 12482) : ℂ) * ζ ^ 1 + ((1765 / 6241) : ℂ) * ζ ^ 2 - ((932 / 6241) : ℂ) * ζ ^ 3 - ((1581 / 6241) : ℂ) * ζ ^ 4 - ((657 / 6241) : ℂ) * ζ ^ 5 + ((2619 / 12482) : ℂ) * ζ ^ 6 + ((1737 / 6241) : ℂ) * ζ ^ 7 - ((81 / 6241) : ℂ) * ζ ^ 8 - ((476 / 6241) : ℂ) * ζ ^ 9 - ((761 / 12482) : ℂ) * ζ ^ 10 + ((427 / 12482) : ℂ) * ζ ^ 11 + ((2393 / 12482) : ℂ) * ζ ^ 12 + ((426 / 6241) : ℂ) * ζ ^ 13 + ((2665 / 12482) : ℂ) * ζ ^ 14 + ((866 / 6241) : ℂ) * ζ ^ 15 + ((218 / 6241) : ℂ) * ζ ^ 16 - ((1113 / 6241) : ℂ) * ζ ^ 17 + ((726 / 6241) : ℂ) * ζ ^ 18 + ((567 / 12482) : ℂ) * ζ ^ 19 + ((3575 / 12482) : ℂ) * ζ ^ 20 + ((244 / 6241) : ℂ) * ζ ^ 21 - ((713 / 12482) : ℂ) * ζ ^ 22 - ((1702 / 6241) : ℂ) * ζ ^ 23 + ((1353 / 6241) : ℂ) * ζ ^ 24 + ((321 / 12482) : ℂ) * ζ ^ 25 + ((1107 / 12482) : ℂ) * ζ ^ 26 - ((1061 / 12482) : ℂ) * ζ ^ 27 - ((341 / 6241) : ℂ) * ζ ^ 28 - ((373 / 6241) : ℂ) * ζ ^ 29 + ((476 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep07Coefficient04 : ℂ :=
  (-((506 / 395) : ℂ) + ((145 / 79) : ℂ) * ζ ^ 1 - ((979 / 790) : ℂ) * ζ ^ 2 - ((1267 / 790) : ℂ) * ζ ^ 3 - ((1841 / 790) : ℂ) * ζ ^ 6 - ((337 / 395) : ℂ) * ζ ^ 8 - ((563 / 158) : ℂ) * ζ ^ 9 - ((719 / 790) : ℂ) * ζ ^ 11 - ((431 / 395) : ℂ) * ζ ^ 12 - ((145 / 79) : ℂ) * ζ ^ 13 - ((1267 / 790) : ℂ) * ζ ^ 15 - ((145 / 79) : ℂ) * ζ ^ 17 - ((33 / 790) : ℂ) * ζ ^ 18 - ((145 / 79) : ℂ) * ζ ^ 21 + ((979 / 790) : ℂ) * ζ ^ 22 - ((979 / 790) : ℂ) * ζ ^ 24 + ((145 / 79) : ℂ) * ζ ^ 25 - ((719 / 790) : ℂ) * ζ ^ 27 + ((337 / 395) : ℂ) * ζ ^ 28 + ((145 / 79) : ℂ) * ζ ^ 29 - ((1653 / 790) : ℂ) * ζ ^ 30 + ((719 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep07CoefficientIdentity04 :
    row18_reducedY67_combinationStep07Coefficient04 =
      row18_reducedY67_combinationStep06Coefficient04 +
        row18_reducedY67_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep07Coefficient04 row18_reducedY67_combinationStep06Coefficient04 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep07Coefficient05 : ℂ :=
  (-((63 / 79) : ℂ) + ((41 / 79) : ℂ) * ζ ^ 1 - ((537 / 158) : ℂ) * ζ ^ 2 - ((179 / 158) : ℂ) * ζ ^ 3 - ((235 / 158) : ℂ) * ζ ^ 5 - ((326 / 79) : ℂ) * ζ ^ 6 - ((225 / 158) : ℂ) * ζ ^ 8 - ((269 / 158) : ℂ) * ζ ^ 9 - ((45 / 79) : ℂ) * ζ ^ 11 - ((225 / 158) : ℂ) * ζ ^ 12 - ((41 / 79) : ℂ) * ζ ^ 13 - ((69 / 79) : ℂ) * ζ ^ 15 - ((41 / 79) : ℂ) * ζ ^ 17 + ((115 / 158) : ℂ) * ζ ^ 18 + ((97 / 158) : ℂ) * ζ ^ 21 + ((537 / 158) : ℂ) * ζ ^ 22 + ((317 / 158) : ℂ) * ζ ^ 25 - ((97 / 158) : ℂ) * ζ ^ 27 + ((225 / 158) : ℂ) * ζ ^ 28 + ((41 / 79) : ℂ) * ζ ^ 29 - ((163 / 79) : ℂ) * ζ ^ 30 + ((45 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY67_combinationStep07CoefficientIdentity05 :
    row18_reducedY67_combinationStep07Coefficient05 =
      row18_reducedY67_combinationStep06Coefficient05 +
        row18_reducedY67_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep07Coefficient05 row18_reducedY67_combinationStep06Coefficient05 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep07Coefficient06 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep07CoefficientIdentity06 :
    row18_reducedY67_combinationStep07Coefficient06 =
      row18_reducedY67_combinationStep06Coefficient06 +
        row18_reducedY67_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep07Coefficient06 row18_reducedY67_combinationStep06Coefficient06 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep07Coefficient07 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep07CoefficientIdentity07 :
    row18_reducedY67_combinationStep07Coefficient07 =
      row18_reducedY67_combinationStep06Coefficient07 +
        row18_reducedY67_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep07Coefficient07 row18_reducedY67_combinationStep06Coefficient07 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep07Coefficient08 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep07CoefficientIdentity08 :
    row18_reducedY67_combinationStep07Coefficient08 =
      row18_reducedY67_combinationStep06Coefficient08 +
        row18_reducedY67_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep07Coefficient08 row18_reducedY67_combinationStep06Coefficient08 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep07Coefficient09 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep07CoefficientIdentity09 :
    row18_reducedY67_combinationStep07Coefficient09 =
      row18_reducedY67_combinationStep06Coefficient09 +
        row18_reducedY67_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep07Coefficient09 row18_reducedY67_combinationStep06Coefficient09 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep07Coefficient10 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep07CoefficientIdentity10 :
    row18_reducedY67_combinationStep07Coefficient10 =
      row18_reducedY67_combinationStep06Coefficient10 +
        row18_reducedY67_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep07Coefficient10 row18_reducedY67_combinationStep06Coefficient10 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep07Coefficient11 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep07CoefficientIdentity11 :
    row18_reducedY67_combinationStep07Coefficient11 =
      row18_reducedY67_combinationStep06Coefficient11 +
        row18_reducedY67_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep07Coefficient11 row18_reducedY67_combinationStep06Coefficient11 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep07Coefficient12 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep07CoefficientIdentity12 :
    row18_reducedY67_combinationStep07Coefficient12 =
      row18_reducedY67_combinationStep06Coefficient12 +
        row18_reducedY67_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep07Coefficient12 row18_reducedY67_combinationStep06Coefficient12 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep07Coefficient13 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY67_combinationStep07CoefficientIdentity13 :
    row18_reducedY67_combinationStep07Coefficient13 =
      row18_reducedY67_combinationStep06Coefficient13 +
        row18_reducedY67_combinationStep07Multiplier *
          (((5 / 316) : ℂ) - ((3 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((33 / 158) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 + ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 + ((3 / 316) : ℂ) * ζ ^ 9 + ((33 / 316) : ℂ) * ζ ^ 11 + ((3 / 79) : ℂ) * ζ ^ 12 + ((3 / 316) : ℂ) * ζ ^ 13 + ((35 / 158) : ℂ) * ζ ^ 15 + ((3 / 316) : ℂ) * ζ ^ 17 + ((19 / 316) : ℂ) * ζ ^ 18 + ((45 / 158) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((1 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 - ((3 / 316) : ℂ) * ζ ^ 29 + ((13 / 79) : ℂ) * ζ ^ 30 - ((33 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep07Coefficient13 row18_reducedY67_combinationStep06Coefficient13 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 (-((5349 / 12482) : ℂ) + ((1914 / 6241) : ℂ) * ζ ^ 1 + ((383 / 12482) : ℂ) * ζ ^ 2 - ((4851 / 12482) : ℂ) * ζ ^ 3 + ((2378 / 6241) : ℂ) * ζ ^ 4 - ((4723 / 12482) : ℂ) * ζ ^ 5 + ((1406 / 6241) : ℂ) * ζ ^ 6 + ((7141 / 12482) : ℂ) * ζ ^ 7 - ((9817 / 12482) : ℂ) * ζ ^ 8 - ((3164 / 6241) : ℂ) * ζ ^ 9 - ((1412 / 6241) : ℂ) * ζ ^ 10 + ((213 / 6241) : ℂ) * ζ ^ 11 + ((499 / 12482) : ℂ) * ζ ^ 12 + ((4605 / 12482) : ℂ) * ζ ^ 13 - ((53 / 79) : ℂ) * ζ ^ 14 - ((819 / 12482) : ℂ) * ζ ^ 15 + ((448 / 6241) : ℂ) * ζ ^ 16 - ((3570 / 6241) : ℂ) * ζ ^ 17 + ((1671 / 12482) : ℂ) * ζ ^ 18 - ((523 / 12482) : ℂ) * ζ ^ 19 - ((1859 / 12482) : ℂ) * ζ ^ 20 - ((2261 / 12482) : ℂ) * ζ ^ 21 + ((387 / 12482) : ℂ) * ζ ^ 22 - ((50 / 79) : ℂ) * ζ ^ 23 + ((2033 / 6241) : ℂ) * ζ ^ 24 - ((325 / 6241) : ℂ) * ζ ^ 25 + ((1375 / 12482) : ℂ) * ζ ^ 26 - ((2164 / 6241) : ℂ) * ζ ^ 27 + ((241 / 12482) : ℂ) * ζ ^ 28 - ((3371 / 12482) : ℂ) * ζ ^ 29 + ((1122 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep07Coefficient14 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep07CoefficientIdentity14 :
    row18_reducedY67_combinationStep07Coefficient14 =
      row18_reducedY67_combinationStep06Coefficient14 +
        row18_reducedY67_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep07Coefficient14 row18_reducedY67_combinationStep06Coefficient14 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep07Coefficient15 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep07CoefficientIdentity15 :
    row18_reducedY67_combinationStep07Coefficient15 =
      row18_reducedY67_combinationStep06Coefficient15 +
        row18_reducedY67_combinationStep07Multiplier *
          (-((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((35 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep07Coefficient15 row18_reducedY67_combinationStep06Coefficient15 row18_reducedY67_combinationStep07Multiplier
  close_cyclotomic_row18 (-((495 / 6241) : ℂ) + ((757 / 12482) : ℂ) * ζ ^ 1 - ((1765 / 6241) : ℂ) * ζ ^ 2 + ((932 / 6241) : ℂ) * ζ ^ 3 + ((1581 / 6241) : ℂ) * ζ ^ 4 + ((657 / 6241) : ℂ) * ζ ^ 5 - ((2619 / 12482) : ℂ) * ζ ^ 6 - ((1737 / 6241) : ℂ) * ζ ^ 7 + ((81 / 6241) : ℂ) * ζ ^ 8 + ((476 / 6241) : ℂ) * ζ ^ 9 + ((761 / 12482) : ℂ) * ζ ^ 10 - ((427 / 12482) : ℂ) * ζ ^ 11 - ((2393 / 12482) : ℂ) * ζ ^ 12 - ((426 / 6241) : ℂ) * ζ ^ 13 - ((2665 / 12482) : ℂ) * ζ ^ 14 - ((866 / 6241) : ℂ) * ζ ^ 15 - ((218 / 6241) : ℂ) * ζ ^ 16 + ((1113 / 6241) : ℂ) * ζ ^ 17 - ((726 / 6241) : ℂ) * ζ ^ 18 - ((567 / 12482) : ℂ) * ζ ^ 19 - ((3575 / 12482) : ℂ) * ζ ^ 20 - ((244 / 6241) : ℂ) * ζ ^ 21 + ((713 / 12482) : ℂ) * ζ ^ 22 + ((1702 / 6241) : ℂ) * ζ ^ 23 - ((1353 / 6241) : ℂ) * ζ ^ 24 - ((321 / 12482) : ℂ) * ζ ^ 25 - ((1107 / 12482) : ℂ) * ζ ^ 26 + ((1061 / 12482) : ℂ) * ζ ^ 27 + ((341 / 6241) : ℂ) * ζ ^ 28 + ((373 / 6241) : ℂ) * ζ ^ 29 - ((476 / 6241) : ℂ) * ζ ^ 30)

private theorem row18_reducedY67_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY67_combinationStep07Coefficient00) * Y 0 0
      + (row18_reducedY67_combinationStep07Coefficient01) * Y 0 1
      + (row18_reducedY67_combinationStep07Coefficient02) * Y 1 0
      + (row18_reducedY67_combinationStep07Coefficient03) * Y 1 1
      + (row18_reducedY67_combinationStep07Coefficient04) * Y 2 2
      + (row18_reducedY67_combinationStep07Coefficient05) * Y 2 3
      + (row18_reducedY67_combinationStep07Coefficient06) * Y 3 2
      + (row18_reducedY67_combinationStep07Coefficient07) * Y 3 3
      + (row18_reducedY67_combinationStep07Coefficient08) * Y 4 4
      + (row18_reducedY67_combinationStep07Coefficient09) * Y 4 5
      + (row18_reducedY67_combinationStep07Coefficient10) * Y 5 4
      + (row18_reducedY67_combinationStep07Coefficient11) * Y 5 5
      + (row18_reducedY67_combinationStep07Coefficient12) * Y 6 6
      + (row18_reducedY67_combinationStep07Coefficient13) * Y 6 7
      + (row18_reducedY67_combinationStep07Coefficient14) * Y 7 6
      + (row18_reducedY67_combinationStep07Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY67_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation17
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY67_combinationStep07CoefficientIdentity00,
      row18_reducedY67_combinationStep07CoefficientIdentity01,
      row18_reducedY67_combinationStep07CoefficientIdentity02,
      row18_reducedY67_combinationStep07CoefficientIdentity03,
      row18_reducedY67_combinationStep07CoefficientIdentity04,
      row18_reducedY67_combinationStep07CoefficientIdentity05,
      row18_reducedY67_combinationStep07CoefficientIdentity06,
      row18_reducedY67_combinationStep07CoefficientIdentity07,
      row18_reducedY67_combinationStep07CoefficientIdentity08,
      row18_reducedY67_combinationStep07CoefficientIdentity09,
      row18_reducedY67_combinationStep07CoefficientIdentity10,
      row18_reducedY67_combinationStep07CoefficientIdentity11,
      row18_reducedY67_combinationStep07CoefficientIdentity12,
      row18_reducedY67_combinationStep07CoefficientIdentity13,
      row18_reducedY67_combinationStep07CoefficientIdentity14,
      row18_reducedY67_combinationStep07CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY67_combinationStep07Multiplier * equation

private def row18_reducedY67_combinationStep08Multiplier : ℂ :=
  (((902 / 395) : ℂ) - ((310 / 79) : ℂ) * ζ ^ 1 + ((864 / 395) : ℂ) * ζ ^ 2 + ((242 / 79) : ℂ) * ζ ^ 3 + ((2096 / 395) : ℂ) * ζ ^ 6 + ((34 / 395) : ℂ) * ζ ^ 8 + ((452 / 79) : ℂ) * ζ ^ 9 + ((224 / 79) : ℂ) * ζ ^ 11 + ((1232 / 395) : ℂ) * ζ ^ 12 + ((310 / 79) : ℂ) * ζ ^ 13 + ((242 / 79) : ℂ) * ζ ^ 15 + ((310 / 79) : ℂ) * ζ ^ 17 + ((38 / 395) : ℂ) * ζ ^ 18 + ((310 / 79) : ℂ) * ζ ^ 21 - ((864 / 395) : ℂ) * ζ ^ 22 + ((864 / 395) : ℂ) * ζ ^ 24 - ((310 / 79) : ℂ) * ζ ^ 25 + ((224 / 79) : ℂ) * ζ ^ 27 - ((34 / 395) : ℂ) * ζ ^ 28 - ((310 / 79) : ℂ) * ζ ^ 29 + ((898 / 395) : ℂ) * ζ ^ 30 - ((224 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY67_combinationStep08Coefficient00 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity00 :
    row18_reducedY67_combinationStep08Coefficient00 =
      row18_reducedY67_combinationStep07Coefficient00 +
        row18_reducedY67_combinationStep08Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep08Coefficient00 row18_reducedY67_combinationStep07Coefficient00 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 (((8536 / 6241) : ℂ) - ((128811 / 62410) : ℂ) * ζ ^ 1 + ((10543 / 12482) : ℂ) * ζ ^ 2 + ((33605 / 12482) : ℂ) * ζ ^ 3 - ((12796 / 6241) : ℂ) * ζ ^ 4 + ((31712 / 31205) : ℂ) * ζ ^ 5 + ((113513 / 62410) : ℂ) * ζ ^ 6 - ((167713 / 62410) : ℂ) * ζ ^ 7 + ((44571 / 62410) : ℂ) * ζ ^ 8 + ((92457 / 31205) : ℂ) * ζ ^ 9 - ((152583 / 62410) : ℂ) * ζ ^ 10 + ((47241 / 31205) : ℂ) * ζ ^ 11 + ((56683 / 62410) : ℂ) * ζ ^ 12 - ((206627 / 62410) : ℂ) * ζ ^ 13 + ((28777 / 31205) : ℂ) * ζ ^ 14 + ((33664 / 31205) : ℂ) * ζ ^ 15 - ((103503 / 62410) : ℂ) * ζ ^ 16 + ((149793 / 62410) : ℂ) * ζ ^ 17 - ((5891 / 62410) : ℂ) * ζ ^ 18 - ((119907 / 62410) : ℂ) * ζ ^ 19 + ((34819 / 31205) : ℂ) * ζ ^ 20 - ((14896 / 31205) : ℂ) * ζ ^ 21 - ((17692 / 31205) : ℂ) * ζ ^ 22 + ((23294 / 31205) : ℂ) * ζ ^ 23 - ((7071 / 62410) : ℂ) * ζ ^ 24 - ((4396 / 6241) : ℂ) * ζ ^ 25 + ((7776 / 31205) : ℂ) * ζ ^ 26 - ((11901 / 62410) : ℂ) * ζ ^ 27 + ((4913 / 31205) : ℂ) * ζ ^ 28 + ((1337 / 31205) : ℂ) * ζ ^ 29 + ((784 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep08Coefficient01 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity01 :
    row18_reducedY67_combinationStep08Coefficient01 =
      row18_reducedY67_combinationStep07Coefficient01 +
        row18_reducedY67_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep08Coefficient01 row18_reducedY67_combinationStep07Coefficient01 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep08Coefficient02 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity02 :
    row18_reducedY67_combinationStep08Coefficient02 =
      row18_reducedY67_combinationStep07Coefficient02 +
        row18_reducedY67_combinationStep08Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep08Coefficient02 row18_reducedY67_combinationStep07Coefficient02 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 (-((8569 / 31205) : ℂ) + ((19603 / 62410) : ℂ) * ζ ^ 1 - ((13923 / 6241) : ℂ) * ζ ^ 2 - ((42184 / 31205) : ℂ) * ζ ^ 3 + ((93 / 79) : ℂ) * ζ ^ 4 - ((117092 / 31205) : ℂ) * ζ ^ 5 - ((5997 / 12482) : ℂ) * ζ ^ 6 - ((359 / 6241) : ℂ) * ζ ^ 7 - ((202011 / 62410) : ℂ) * ζ ^ 8 - ((41329 / 62410) : ℂ) * ζ ^ 9 - ((7 / 12482) : ℂ) * ζ ^ 10 - ((14258 / 6241) : ℂ) * ζ ^ 11 - ((93181 / 62410) : ℂ) * ζ ^ 12 + ((38381 / 31205) : ℂ) * ζ ^ 13 - ((39627 / 12482) : ℂ) * ζ ^ 14 - ((6983 / 62410) : ℂ) * ζ ^ 15 - ((13357 / 31205) : ℂ) * ζ ^ 16 - ((58979 / 31205) : ℂ) * ζ ^ 17 + ((7103 / 12482) : ℂ) * ζ ^ 18 + ((12211 / 31205) : ℂ) * ζ ^ 19 - ((48439 / 62410) : ℂ) * ζ ^ 20 + ((87069 / 62410) : ℂ) * ζ ^ 21 - ((1395 / 12482) : ℂ) * ζ ^ 22 - ((37328 / 31205) : ℂ) * ζ ^ 23 + ((7787 / 12482) : ℂ) * ζ ^ 24 - ((3686 / 31205) : ℂ) * ζ ^ 25 - ((4249 / 6241) : ℂ) * ζ ^ 26 + ((54157 / 62410) : ℂ) * ζ ^ 27 + ((32694 / 31205) : ℂ) * ζ ^ 28 - ((5418 / 31205) : ℂ) * ζ ^ 29 + ((4704 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep08Coefficient03 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity03 :
    row18_reducedY67_combinationStep08Coefficient03 =
      row18_reducedY67_combinationStep07Coefficient03 +
        row18_reducedY67_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep08Coefficient03 row18_reducedY67_combinationStep07Coefficient03 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep08Coefficient04 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity04 :
    row18_reducedY67_combinationStep08Coefficient04 =
      row18_reducedY67_combinationStep07Coefficient04 +
        row18_reducedY67_combinationStep08Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep08Coefficient04 row18_reducedY67_combinationStep07Coefficient04 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 (-((8536 / 6241) : ℂ) + ((128811 / 62410) : ℂ) * ζ ^ 1 - ((10543 / 12482) : ℂ) * ζ ^ 2 - ((33605 / 12482) : ℂ) * ζ ^ 3 + ((12796 / 6241) : ℂ) * ζ ^ 4 - ((31712 / 31205) : ℂ) * ζ ^ 5 - ((113513 / 62410) : ℂ) * ζ ^ 6 + ((167713 / 62410) : ℂ) * ζ ^ 7 - ((44571 / 62410) : ℂ) * ζ ^ 8 - ((92457 / 31205) : ℂ) * ζ ^ 9 + ((152583 / 62410) : ℂ) * ζ ^ 10 - ((47241 / 31205) : ℂ) * ζ ^ 11 - ((56683 / 62410) : ℂ) * ζ ^ 12 + ((206627 / 62410) : ℂ) * ζ ^ 13 - ((28777 / 31205) : ℂ) * ζ ^ 14 - ((33664 / 31205) : ℂ) * ζ ^ 15 + ((103503 / 62410) : ℂ) * ζ ^ 16 - ((149793 / 62410) : ℂ) * ζ ^ 17 + ((5891 / 62410) : ℂ) * ζ ^ 18 + ((119907 / 62410) : ℂ) * ζ ^ 19 - ((34819 / 31205) : ℂ) * ζ ^ 20 + ((14896 / 31205) : ℂ) * ζ ^ 21 + ((17692 / 31205) : ℂ) * ζ ^ 22 - ((23294 / 31205) : ℂ) * ζ ^ 23 + ((7071 / 62410) : ℂ) * ζ ^ 24 + ((4396 / 6241) : ℂ) * ζ ^ 25 - ((7776 / 31205) : ℂ) * ζ ^ 26 + ((11901 / 62410) : ℂ) * ζ ^ 27 - ((4913 / 31205) : ℂ) * ζ ^ 28 - ((1337 / 31205) : ℂ) * ζ ^ 29 - ((784 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep08Coefficient05 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity05 :
    row18_reducedY67_combinationStep08Coefficient05 =
      row18_reducedY67_combinationStep07Coefficient05 +
        row18_reducedY67_combinationStep08Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY67_combinationStep08Coefficient05 row18_reducedY67_combinationStep07Coefficient05 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 (-((18651 / 62410) : ℂ) - ((29203 / 62410) : ℂ) * ζ ^ 1 - ((86208 / 31205) : ℂ) * ζ ^ 2 - ((29761 / 62410) : ℂ) * ζ ^ 3 + ((3873 / 62410) : ℂ) * ζ ^ 4 - ((14535 / 12482) : ℂ) * ζ ^ 5 - ((4179 / 6241) : ℂ) * ζ ^ 6 + ((67891 / 62410) : ℂ) * ζ ^ 7 - ((174721 / 62410) : ℂ) * ζ ^ 8 + ((26868 / 31205) : ℂ) * ζ ^ 9 - ((6199 / 62410) : ℂ) * ζ ^ 10 - ((52821 / 62410) : ℂ) * ζ ^ 11 - ((137289 / 62410) : ℂ) * ζ ^ 12 + ((2636 / 6241) : ℂ) * ζ ^ 13 - ((193239 / 62410) : ℂ) * ζ ^ 14 - ((61613 / 62410) : ℂ) * ζ ^ 15 + ((5083 / 6241) : ℂ) * ζ ^ 16 - ((8002 / 31205) : ℂ) * ζ ^ 17 - ((57637 / 62410) : ℂ) * ζ ^ 18 + ((49771 / 62410) : ℂ) * ζ ^ 19 - ((50849 / 31205) : ℂ) * ζ ^ 20 - ((4796 / 31205) : ℂ) * ζ ^ 21 + ((108313 / 62410) : ℂ) * ζ ^ 22 - ((697 / 790) : ℂ) * ζ ^ 23 + ((14847 / 12482) : ℂ) * ζ ^ 24 - ((77969 / 62410) : ℂ) * ζ ^ 25 - ((10411 / 6241) : ℂ) * ζ ^ 26 - ((3426 / 31205) : ℂ) * ζ ^ 27 + ((62667 / 31205) : ℂ) * ζ ^ 28 - ((5058 / 6241) : ℂ) * ζ ^ 29 + ((10080 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY67_combinationStep08Coefficient06 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity06 :
    row18_reducedY67_combinationStep08Coefficient06 =
      row18_reducedY67_combinationStep07Coefficient06 +
        row18_reducedY67_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep08Coefficient06 row18_reducedY67_combinationStep07Coefficient06 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep08Coefficient07 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity07 :
    row18_reducedY67_combinationStep08Coefficient07 =
      row18_reducedY67_combinationStep07Coefficient07 +
        row18_reducedY67_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep08Coefficient07 row18_reducedY67_combinationStep07Coefficient07 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep08Coefficient08 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity08 :
    row18_reducedY67_combinationStep08Coefficient08 =
      row18_reducedY67_combinationStep07Coefficient08 +
        row18_reducedY67_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep08Coefficient08 row18_reducedY67_combinationStep07Coefficient08 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep08Coefficient09 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity09 :
    row18_reducedY67_combinationStep08Coefficient09 =
      row18_reducedY67_combinationStep07Coefficient09 +
        row18_reducedY67_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep08Coefficient09 row18_reducedY67_combinationStep07Coefficient09 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep08Coefficient10 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity10 :
    row18_reducedY67_combinationStep08Coefficient10 =
      row18_reducedY67_combinationStep07Coefficient10 +
        row18_reducedY67_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep08Coefficient10 row18_reducedY67_combinationStep07Coefficient10 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep08Coefficient11 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity11 :
    row18_reducedY67_combinationStep08Coefficient11 =
      row18_reducedY67_combinationStep07Coefficient11 +
        row18_reducedY67_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep08Coefficient11 row18_reducedY67_combinationStep07Coefficient11 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep08Coefficient12 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity12 :
    row18_reducedY67_combinationStep08Coefficient12 =
      row18_reducedY67_combinationStep07Coefficient12 +
        row18_reducedY67_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep08Coefficient12 row18_reducedY67_combinationStep07Coefficient12 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep08Coefficient13 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY67_combinationStep08CoefficientIdentity13 :
    row18_reducedY67_combinationStep08Coefficient13 =
      row18_reducedY67_combinationStep07Coefficient13 +
        row18_reducedY67_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep08Coefficient13 row18_reducedY67_combinationStep07Coefficient13 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep08Coefficient14 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity14 :
    row18_reducedY67_combinationStep08Coefficient14 =
      row18_reducedY67_combinationStep07Coefficient14 +
        row18_reducedY67_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep08Coefficient14 row18_reducedY67_combinationStep07Coefficient14 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY67_combinationStep08Coefficient15 : ℂ :=
  0

private theorem row18_reducedY67_combinationStep08CoefficientIdentity15 :
    row18_reducedY67_combinationStep08Coefficient15 =
      row18_reducedY67_combinationStep07Coefficient15 +
        row18_reducedY67_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY67_combinationStep08Coefficient15 row18_reducedY67_combinationStep07Coefficient15 row18_reducedY67_combinationStep08Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY67_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY67_combinationStep08Coefficient00) * Y 0 0
      + (row18_reducedY67_combinationStep08Coefficient01) * Y 0 1
      + (row18_reducedY67_combinationStep08Coefficient02) * Y 1 0
      + (row18_reducedY67_combinationStep08Coefficient03) * Y 1 1
      + (row18_reducedY67_combinationStep08Coefficient04) * Y 2 2
      + (row18_reducedY67_combinationStep08Coefficient05) * Y 2 3
      + (row18_reducedY67_combinationStep08Coefficient06) * Y 3 2
      + (row18_reducedY67_combinationStep08Coefficient07) * Y 3 3
      + (row18_reducedY67_combinationStep08Coefficient08) * Y 4 4
      + (row18_reducedY67_combinationStep08Coefficient09) * Y 4 5
      + (row18_reducedY67_combinationStep08Coefficient10) * Y 5 4
      + (row18_reducedY67_combinationStep08Coefficient11) * Y 5 5
      + (row18_reducedY67_combinationStep08Coefficient12) * Y 6 6
      + (row18_reducedY67_combinationStep08Coefficient13) * Y 6 7
      + (row18_reducedY67_combinationStep08Coefficient14) * Y 7 6
      + (row18_reducedY67_combinationStep08Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY67_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY67_combinationStep08CoefficientIdentity00,
      row18_reducedY67_combinationStep08CoefficientIdentity01,
      row18_reducedY67_combinationStep08CoefficientIdentity02,
      row18_reducedY67_combinationStep08CoefficientIdentity03,
      row18_reducedY67_combinationStep08CoefficientIdentity04,
      row18_reducedY67_combinationStep08CoefficientIdentity05,
      row18_reducedY67_combinationStep08CoefficientIdentity06,
      row18_reducedY67_combinationStep08CoefficientIdentity07,
      row18_reducedY67_combinationStep08CoefficientIdentity08,
      row18_reducedY67_combinationStep08CoefficientIdentity09,
      row18_reducedY67_combinationStep08CoefficientIdentity10,
      row18_reducedY67_combinationStep08CoefficientIdentity11,
      row18_reducedY67_combinationStep08CoefficientIdentity12,
      row18_reducedY67_combinationStep08CoefficientIdentity13,
      row18_reducedY67_combinationStep08CoefficientIdentity14,
      row18_reducedY67_combinationStep08CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY67_combinationStep08Multiplier * equation

theorem row18_reducedY67
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 6 7 = 0 := by
  have reduced :=
    row18_reducedY67_combinationStep08 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY67_combinationStep08Coefficient00,
      row18_reducedY67_combinationStep08Coefficient01,
      row18_reducedY67_combinationStep08Coefficient02,
      row18_reducedY67_combinationStep08Coefficient03,
      row18_reducedY67_combinationStep08Coefficient04,
      row18_reducedY67_combinationStep08Coefficient05,
      row18_reducedY67_combinationStep08Coefficient06,
      row18_reducedY67_combinationStep08Coefficient07,
      row18_reducedY67_combinationStep08Coefficient08,
      row18_reducedY67_combinationStep08Coefficient09,
      row18_reducedY67_combinationStep08Coefficient10,
      row18_reducedY67_combinationStep08Coefficient11,
      row18_reducedY67_combinationStep08Coefficient12,
      row18_reducedY67_combinationStep08Coefficient13,
      row18_reducedY67_combinationStep08Coefficient14,
      row18_reducedY67_combinationStep08Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
