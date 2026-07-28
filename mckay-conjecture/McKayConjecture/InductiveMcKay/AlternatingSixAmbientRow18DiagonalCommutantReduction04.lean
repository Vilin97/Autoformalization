/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction03

/-!
# Ambient row 18 commutant reduction 04

This generated module checks the reduced relation `reducedY22` for
matrix coordinate (2, 2).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY22_combinationStep00Multiplier : ℂ :=
  (-((7788 / 395) : ℂ) + ((2126 / 237) : ℂ) * ζ ^ 1 + ((1550 / 79) : ℂ) * ζ ^ 2 - ((4646 / 237) : ℂ) * ζ ^ 3 + ((5396 / 237) : ℂ) * ζ ^ 5 + ((32422 / 1185) : ℂ) * ζ ^ 8 - ((330 / 79) : ℂ) * ζ ^ 9 + ((5636 / 237) : ℂ) * ζ ^ 11 + ((14306 / 1185) : ℂ) * ζ ^ 12 - ((2126 / 237) : ℂ) * ζ ^ 13 + ((1376 / 237) : ℂ) * ζ ^ 15 - ((2126 / 237) : ℂ) * ζ ^ 17 - ((1550 / 79) : ℂ) * ζ ^ 18 - ((6772 / 237) : ℂ) * ζ ^ 21 - ((1550 / 79) : ℂ) * ζ ^ 22 - ((15576 / 395) : ℂ) * ζ ^ 24 - ((1090 / 79) : ℂ) * ζ ^ 25 - ((6772 / 237) : ℂ) * ζ ^ 27 - ((32422 / 1185) : ℂ) * ζ ^ 28 + ((2126 / 237) : ℂ) * ζ ^ 29 - ((3868 / 237) : ℂ) * ζ ^ 30 - ((5636 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY22_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep00CoefficientIdentity00 :
    row18_reducedY22_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep00Coefficient00 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep00Coefficient01 : ℂ :=
  (((1067 / 474) : ℂ) - ((86 / 237) : ℂ) * ζ ^ 1 + ((137 / 158) : ℂ) * ζ ^ 2 - ((508 / 237) : ℂ) * ζ ^ 3 - ((86 / 237) : ℂ) * ζ ^ 5 + ((739 / 237) : ℂ) * ζ ^ 6 - ((739 / 237) : ℂ) * ζ ^ 8 + ((86 / 237) : ℂ) * ζ ^ 9 + ((254 / 237) : ℂ) * ζ ^ 11 - ((74 / 237) : ℂ) * ζ ^ 12 + ((86 / 237) : ℂ) * ζ ^ 13 + ((1463 / 474) : ℂ) * ζ ^ 15 + ((86 / 237) : ℂ) * ζ ^ 17 - ((206 / 79) : ℂ) * ζ ^ 18 + ((61 / 158) : ℂ) * ζ ^ 21 - ((137 / 158) : ℂ) * ζ ^ 22 + ((121 / 237) : ℂ) * ζ ^ 24 + ((149 / 158) : ℂ) * ζ ^ 27 + ((739 / 237) : ℂ) * ζ ^ 28 - ((86 / 237) : ℂ) * ζ ^ 29 + ((665 / 237) : ℂ) * ζ ^ 30 - ((254 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep00CoefficientIdentity01 :
    row18_reducedY22_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep00Coefficient01 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 (-((1402753 / 187230) : ℂ) + ((204631 / 93615) : ℂ) * ζ ^ 1 + ((57997 / 31205) : ℂ) * ζ ^ 2 - ((47171 / 37446) : ℂ) * ζ ^ 3 + ((904859 / 93615) : ℂ) * ζ ^ 4 + ((578464 / 93615) : ℂ) * ζ ^ 5 - ((741727 / 187230) : ℂ) * ζ ^ 6 - ((8502 / 6241) : ℂ) * ζ ^ 7 + ((336407 / 62410) : ℂ) * ζ ^ 8 - ((158719 / 187230) : ℂ) * ζ ^ 9 - ((442639 / 187230) : ℂ) * ζ ^ 10 - ((612191 / 187230) : ℂ) * ζ ^ 11 + ((389387 / 187230) : ℂ) * ζ ^ 12 - ((238987 / 93615) : ℂ) * ζ ^ 13 - ((677859 / 62410) : ℂ) * ζ ^ 14 - ((261701 / 187230) : ℂ) * ζ ^ 15 - ((230857 / 187230) : ℂ) * ζ ^ 16 - ((225484 / 93615) : ℂ) * ζ ^ 17 + ((57182 / 18723) : ℂ) * ζ ^ 18 - ((21961 / 187230) : ℂ) * ζ ^ 19 - ((135144 / 31205) : ℂ) * ζ ^ 20 - ((121168 / 93615) : ℂ) * ζ ^ 21 - ((9697 / 62410) : ℂ) * ζ ^ 22 - ((31595 / 18723) : ℂ) * ζ ^ 23 - ((457 / 79) : ℂ) * ζ ^ 24 + ((67381 / 187230) : ℂ) * ζ ^ 25 + ((243649 / 93615) : ℂ) * ζ ^ 26 + ((595223 / 187230) : ℂ) * ζ ^ 27 - ((74932 / 18723) : ℂ) * ζ ^ 28 + ((27713 / 18723) : ℂ) * ζ ^ 29 + ((95812 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep00Coefficient02 : ℂ :=
  (-((491 / 237) : ℂ) - ((302 / 79) : ℂ) * ζ ^ 1 + ((611 / 474) : ℂ) * ζ ^ 2 + ((883 / 474) : ℂ) * ζ ^ 3 - ((475 / 79) : ℂ) * ζ ^ 5 - ((122 / 237) : ℂ) * ζ ^ 6 + ((281 / 237) : ℂ) * ζ ^ 8 + ((129 / 158) : ℂ) * ζ ^ 9 - ((1007 / 237) : ℂ) * ζ ^ 11 + ((285 / 158) : ℂ) * ζ ^ 12 + ((302 / 79) : ℂ) * ζ ^ 13 - ((883 / 474) : ℂ) * ζ ^ 15 + ((302 / 79) : ℂ) * ζ ^ 17 + ((371 / 474) : ℂ) * ζ ^ 18 + ((173 / 79) : ℂ) * ζ ^ 21 - ((611 / 474) : ℂ) * ζ ^ 22 - ((611 / 474) : ℂ) * ζ ^ 24 + ((173 / 79) : ℂ) * ζ ^ 25 + ((1007 / 237) : ℂ) * ζ ^ 27 - ((281 / 237) : ℂ) * ζ ^ 28 - ((302 / 79) : ℂ) * ζ ^ 29 + ((49 / 474) : ℂ) * ζ ^ 30 + ((1007 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep00CoefficientIdentity02 :
    row18_reducedY22_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep00Coefficient02 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 (-((285017 / 93615) : ℂ) + ((499852 / 93615) : ℂ) * ζ ^ 1 + ((191906 / 93615) : ℂ) * ζ ^ 2 - ((344506 / 93615) : ℂ) * ζ ^ 3 + ((686729 / 187230) : ℂ) * ζ ^ 4 + ((279158 / 93615) : ℂ) * ζ ^ 5 + ((6366 / 31205) : ℂ) * ζ ^ 6 + ((1206137 / 187230) : ℂ) * ζ ^ 7 + ((93730 / 18723) : ℂ) * ζ ^ 8 - ((29090 / 18723) : ℂ) * ζ ^ 9 - ((310816 / 93615) : ℂ) * ζ ^ 10 + ((46492 / 93615) : ℂ) * ζ ^ 11 + ((95989 / 93615) : ℂ) * ζ ^ 12 + ((92189 / 187230) : ℂ) * ζ ^ 13 - ((163081 / 62410) : ℂ) * ζ ^ 14 - ((13435 / 18723) : ℂ) * ζ ^ 15 - ((666089 / 187230) : ℂ) * ζ ^ 16 - ((149972 / 31205) : ℂ) * ζ ^ 17 - ((604807 / 187230) : ℂ) * ζ ^ 18 - ((50231 / 37446) : ℂ) * ζ ^ 19 - ((8557 / 31205) : ℂ) * ζ ^ 20 - ((79057 / 187230) : ℂ) * ζ ^ 21 + ((43791 / 31205) : ℂ) * ζ ^ 22 - ((42394 / 18723) : ℂ) * ζ ^ 23 - ((197996 / 31205) : ℂ) * ζ ^ 24 - ((16658 / 31205) : ℂ) * ζ ^ 25 - ((125914 / 93615) : ℂ) * ζ ^ 26 - ((29518 / 6241) : ℂ) * ζ ^ 27 - ((361 / 37446) : ℂ) * ζ ^ 28 + ((17516 / 6241) : ℂ) * ζ ^ 29 + ((7045 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep00CoefficientIdentity03 :
    row18_reducedY22_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep00Coefficient03 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep00CoefficientIdentity04 :
    row18_reducedY22_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep00Coefficient04 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep00CoefficientIdentity05 :
    row18_reducedY22_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep00Coefficient05 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep00CoefficientIdentity06 :
    row18_reducedY22_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep00Coefficient06 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep00CoefficientIdentity07 :
    row18_reducedY22_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep00Coefficient07 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep00CoefficientIdentity08 :
    row18_reducedY22_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep00Coefficient08 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep00CoefficientIdentity09 :
    row18_reducedY22_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep00Coefficient09 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep00CoefficientIdentity10 :
    row18_reducedY22_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep00Coefficient10 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep00CoefficientIdentity11 :
    row18_reducedY22_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep00Coefficient11 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep00CoefficientIdentity12 :
    row18_reducedY22_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep00Coefficient12 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep00CoefficientIdentity13 :
    row18_reducedY22_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep00Coefficient13 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep00CoefficientIdentity14 :
    row18_reducedY22_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep00Coefficient14 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep00CoefficientIdentity15 :
    row18_reducedY22_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY22_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep00Coefficient15 row18_reducedY22_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY22_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY22_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY22_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY22_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY22_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY22_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY22_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY22_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY22_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY22_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY22_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY22_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY22_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY22_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY22_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY22_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY22_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY22_combinationStep00CoefficientIdentity00,
      row18_reducedY22_combinationStep00CoefficientIdentity01,
      row18_reducedY22_combinationStep00CoefficientIdentity02,
      row18_reducedY22_combinationStep00CoefficientIdentity03,
      row18_reducedY22_combinationStep00CoefficientIdentity04,
      row18_reducedY22_combinationStep00CoefficientIdentity05,
      row18_reducedY22_combinationStep00CoefficientIdentity06,
      row18_reducedY22_combinationStep00CoefficientIdentity07,
      row18_reducedY22_combinationStep00CoefficientIdentity08,
      row18_reducedY22_combinationStep00CoefficientIdentity09,
      row18_reducedY22_combinationStep00CoefficientIdentity10,
      row18_reducedY22_combinationStep00CoefficientIdentity11,
      row18_reducedY22_combinationStep00CoefficientIdentity12,
      row18_reducedY22_combinationStep00CoefficientIdentity13,
      row18_reducedY22_combinationStep00CoefficientIdentity14,
      row18_reducedY22_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY22_combinationStep00Multiplier * equation

private def row18_reducedY22_combinationStep01Multiplier : ℂ :=
  (-((758 / 1185) : ℂ) + ((5038 / 1185) : ℂ) * ζ ^ 1 + ((2296 / 1185) : ℂ) * ζ ^ 2 + ((1414 / 1185) : ℂ) * ζ ^ 5 + ((1018 / 395) : ℂ) * ζ ^ 6 + ((1018 / 395) : ℂ) * ζ ^ 8 + ((1414 / 1185) : ℂ) * ζ ^ 9 + ((280 / 237) : ℂ) * ζ ^ 11 - ((136 / 395) : ℂ) * ζ ^ 12 - ((5038 / 1185) : ℂ) * ζ ^ 13 + ((536 / 237) : ℂ) * ζ ^ 15 - ((5038 / 1185) : ℂ) * ζ ^ 17 - ((4738 / 1185) : ℂ) * ζ ^ 18 - ((3226 / 1185) : ℂ) * ζ ^ 21 - ((2296 / 1185) : ℂ) * ζ ^ 22 + ((1684 / 1185) : ℂ) * ζ ^ 24 + ((1208 / 395) : ℂ) * ζ ^ 25 - ((536 / 237) : ℂ) * ζ ^ 27 - ((1018 / 395) : ℂ) * ζ ^ 28 + ((5038 / 1185) : ℂ) * ζ ^ 29 + ((1154 / 395) : ℂ) * ζ ^ 30 - ((280 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY22_combinationStep01Coefficient00 : ℂ :=
  (-((112 / 237) : ℂ) - ((422 / 237) : ℂ) * ζ ^ 1 + ((175 / 474) : ℂ) * ζ ^ 2 + ((703 / 474) : ℂ) * ζ ^ 3 - ((278 / 237) : ℂ) * ζ ^ 5 - ((455 / 237) : ℂ) * ζ ^ 6 + ((116 / 237) : ℂ) * ζ ^ 8 + ((58 / 79) : ℂ) * ζ ^ 9 - ((355 / 474) : ℂ) * ζ ^ 11 + ((116 / 237) : ℂ) * ζ ^ 12 + ((422 / 237) : ℂ) * ζ ^ 13 - ((415 / 474) : ℂ) * ζ ^ 15 + ((422 / 237) : ℂ) * ζ ^ 17 + ((1085 / 474) : ℂ) * ζ ^ 18 + ((47 / 158) : ℂ) * ζ ^ 21 - ((175 / 474) : ℂ) * ζ ^ 22 - ((48 / 79) : ℂ) * ζ ^ 25 - ((47 / 158) : ℂ) * ζ ^ 27 - ((116 / 237) : ℂ) * ζ ^ 28 - ((422 / 237) : ℂ) * ζ ^ 29 - ((455 / 474) : ℂ) * ζ ^ 30 + ((355 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep01CoefficientIdentity00 :
    row18_reducedY22_combinationStep01Coefficient00 =
      row18_reducedY22_combinationStep00Coefficient00 +
        row18_reducedY22_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep01Coefficient00 row18_reducedY22_combinationStep00Coefficient00 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 (((59779 / 93615) : ℂ) + ((131749 / 187230) : ℂ) * ζ ^ 1 - ((1159 / 1185) : ℂ) * ζ ^ 2 - ((129117 / 62410) : ℂ) * ζ ^ 3 - ((49067 / 93615) : ℂ) * ζ ^ 4 + ((57449 / 187230) : ℂ) * ζ ^ 5 + ((206168 / 93615) : ℂ) * ζ ^ 6 + ((105251 / 62410) : ℂ) * ζ ^ 7 - ((63139 / 62410) : ℂ) * ζ ^ 8 - ((110473 / 187230) : ℂ) * ζ ^ 9 - ((72337 / 62410) : ℂ) * ζ ^ 10 - ((68729 / 93615) : ℂ) * ζ ^ 11 + ((29772 / 31205) : ℂ) * ζ ^ 12 + ((57723 / 62410) : ℂ) * ζ ^ 13 + ((278191 / 187230) : ℂ) * ζ ^ 14 - ((4049 / 187230) : ℂ) * ζ ^ 15 - ((46043 / 93615) : ℂ) * ζ ^ 16 + ((8053 / 187230) : ℂ) * ζ ^ 17 - ((11429 / 31205) : ℂ) * ζ ^ 18 + ((10261 / 187230) : ℂ) * ζ ^ 19 - ((10027 / 62410) : ℂ) * ζ ^ 20 - ((1685 / 12482) : ℂ) * ζ ^ 21 + ((17724 / 31205) : ℂ) * ζ ^ 22 + ((102191 / 187230) : ℂ) * ζ ^ 23 + ((1544 / 18723) : ℂ) * ζ ^ 24 - ((101509 / 93615) : ℂ) * ζ ^ 25 - ((178667 / 187230) : ℂ) * ζ ^ 26 + ((13061 / 37446) : ℂ) * ζ ^ 27 + ((46811 / 93615) : ℂ) * ζ ^ 28 + ((471 / 12482) : ℂ) * ζ ^ 29 - ((350 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep01Coefficient01 : ℂ :=
  (((241 / 79) : ℂ) - ((139 / 474) : ℂ) * ζ ^ 1 - ((100 / 237) : ℂ) * ζ ^ 2 - ((622 / 237) : ℂ) * ζ ^ 3 - ((139 / 474) : ℂ) * ζ ^ 5 + ((623 / 237) : ℂ) * ζ ^ 6 - ((623 / 237) : ℂ) * ζ ^ 8 + ((139 / 474) : ℂ) * ζ ^ 9 + ((311 / 237) : ℂ) * ζ ^ 11 - ((125 / 474) : ℂ) * ζ ^ 12 + ((139 / 474) : ℂ) * ζ ^ 13 + ((1475 / 474) : ℂ) * ζ ^ 15 + ((139 / 474) : ℂ) * ζ ^ 17 - ((239 / 158) : ℂ) * ζ ^ 18 + ((1247 / 474) : ℂ) * ζ ^ 21 + ((100 / 237) : ℂ) * ζ ^ 22 + ((529 / 474) : ℂ) * ζ ^ 24 + ((77 / 158) : ℂ) * ζ ^ 27 + ((623 / 237) : ℂ) * ζ ^ 28 - ((139 / 474) : ℂ) * ζ ^ 29 + ((1121 / 474) : ℂ) * ζ ^ 30 - ((311 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep01CoefficientIdentity01 :
    row18_reducedY22_combinationStep01Coefficient01 =
      row18_reducedY22_combinationStep00Coefficient01 +
        row18_reducedY22_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep01Coefficient01 row18_reducedY22_combinationStep00Coefficient01 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 (-((45859 / 62410) : ℂ) - ((5687 / 12482) : ℂ) * ζ ^ 1 + ((35414 / 31205) : ℂ) * ζ ^ 2 - ((54574 / 31205) : ℂ) * ζ ^ 3 - ((121532 / 93615) : ℂ) * ζ ^ 4 - ((8476 / 31205) : ℂ) * ζ ^ 5 - ((8954 / 18723) : ℂ) * ζ ^ 6 + ((14627 / 12482) : ℂ) * ζ ^ 7 - ((105011 / 93615) : ℂ) * ζ ^ 8 - ((115661 / 187230) : ℂ) * ζ ^ 9 + ((19846 / 31205) : ℂ) * ζ ^ 10 - ((110849 / 62410) : ℂ) * ζ ^ 11 - ((88777 / 187230) : ℂ) * ζ ^ 12 + ((56201 / 62410) : ℂ) * ζ ^ 13 + ((121173 / 62410) : ℂ) * ζ ^ 14 + ((285154 / 93615) : ℂ) * ζ ^ 15 - ((34753 / 93615) : ℂ) * ζ ^ 16 - ((136999 / 93615) : ℂ) * ζ ^ 17 - ((175336 / 93615) : ℂ) * ζ ^ 18 + ((239611 / 187230) : ℂ) * ζ ^ 19 + ((222946 / 93615) : ℂ) * ζ ^ 20 - ((106703 / 187230) : ℂ) * ζ ^ 21 - ((58451 / 93615) : ℂ) * ζ ^ 22 + ((38999 / 62410) : ℂ) * ζ ^ 23 - ((120443 / 187230) : ℂ) * ζ ^ 24 - ((10147 / 12482) : ℂ) * ζ ^ 25 - ((46829 / 93615) : ℂ) * ζ ^ 26 - ((1997 / 31205) : ℂ) * ζ ^ 27 + ((21246 / 31205) : ℂ) * ζ ^ 28 + ((5278 / 31205) : ℂ) * ζ ^ 29 - ((1960 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep01Coefficient02 : ℂ :=
  (-((491 / 237) : ℂ) - ((302 / 79) : ℂ) * ζ ^ 1 + ((611 / 474) : ℂ) * ζ ^ 2 + ((883 / 474) : ℂ) * ζ ^ 3 - ((475 / 79) : ℂ) * ζ ^ 5 - ((122 / 237) : ℂ) * ζ ^ 6 + ((281 / 237) : ℂ) * ζ ^ 8 + ((129 / 158) : ℂ) * ζ ^ 9 - ((1007 / 237) : ℂ) * ζ ^ 11 + ((285 / 158) : ℂ) * ζ ^ 12 + ((302 / 79) : ℂ) * ζ ^ 13 - ((883 / 474) : ℂ) * ζ ^ 15 + ((302 / 79) : ℂ) * ζ ^ 17 + ((371 / 474) : ℂ) * ζ ^ 18 + ((173 / 79) : ℂ) * ζ ^ 21 - ((611 / 474) : ℂ) * ζ ^ 22 - ((611 / 474) : ℂ) * ζ ^ 24 + ((173 / 79) : ℂ) * ζ ^ 25 + ((1007 / 237) : ℂ) * ζ ^ 27 - ((281 / 237) : ℂ) * ζ ^ 28 - ((302 / 79) : ℂ) * ζ ^ 29 + ((49 / 474) : ℂ) * ζ ^ 30 + ((1007 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep01CoefficientIdentity02 :
    row18_reducedY22_combinationStep01Coefficient02 =
      row18_reducedY22_combinationStep00Coefficient02 +
        row18_reducedY22_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep01Coefficient02 row18_reducedY22_combinationStep00Coefficient02 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep01Coefficient03 : ℂ :=
  (((112 / 237) : ℂ) + ((422 / 237) : ℂ) * ζ ^ 1 - ((175 / 474) : ℂ) * ζ ^ 2 - ((703 / 474) : ℂ) * ζ ^ 3 + ((278 / 237) : ℂ) * ζ ^ 5 + ((455 / 237) : ℂ) * ζ ^ 6 - ((116 / 237) : ℂ) * ζ ^ 8 - ((58 / 79) : ℂ) * ζ ^ 9 + ((355 / 474) : ℂ) * ζ ^ 11 - ((116 / 237) : ℂ) * ζ ^ 12 - ((422 / 237) : ℂ) * ζ ^ 13 + ((415 / 474) : ℂ) * ζ ^ 15 - ((422 / 237) : ℂ) * ζ ^ 17 - ((1085 / 474) : ℂ) * ζ ^ 18 - ((47 / 158) : ℂ) * ζ ^ 21 + ((175 / 474) : ℂ) * ζ ^ 22 + ((48 / 79) : ℂ) * ζ ^ 25 + ((47 / 158) : ℂ) * ζ ^ 27 + ((116 / 237) : ℂ) * ζ ^ 28 + ((422 / 237) : ℂ) * ζ ^ 29 + ((455 / 474) : ℂ) * ζ ^ 30 - ((355 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep01CoefficientIdentity03 :
    row18_reducedY22_combinationStep01Coefficient03 =
      row18_reducedY22_combinationStep00Coefficient03 +
        row18_reducedY22_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep01Coefficient03 row18_reducedY22_combinationStep00Coefficient03 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 (-((59779 / 93615) : ℂ) - ((131749 / 187230) : ℂ) * ζ ^ 1 + ((1159 / 1185) : ℂ) * ζ ^ 2 + ((129117 / 62410) : ℂ) * ζ ^ 3 + ((49067 / 93615) : ℂ) * ζ ^ 4 - ((57449 / 187230) : ℂ) * ζ ^ 5 - ((206168 / 93615) : ℂ) * ζ ^ 6 - ((105251 / 62410) : ℂ) * ζ ^ 7 + ((63139 / 62410) : ℂ) * ζ ^ 8 + ((110473 / 187230) : ℂ) * ζ ^ 9 + ((72337 / 62410) : ℂ) * ζ ^ 10 + ((68729 / 93615) : ℂ) * ζ ^ 11 - ((29772 / 31205) : ℂ) * ζ ^ 12 - ((57723 / 62410) : ℂ) * ζ ^ 13 - ((278191 / 187230) : ℂ) * ζ ^ 14 + ((4049 / 187230) : ℂ) * ζ ^ 15 + ((46043 / 93615) : ℂ) * ζ ^ 16 - ((8053 / 187230) : ℂ) * ζ ^ 17 + ((11429 / 31205) : ℂ) * ζ ^ 18 - ((10261 / 187230) : ℂ) * ζ ^ 19 + ((10027 / 62410) : ℂ) * ζ ^ 20 + ((1685 / 12482) : ℂ) * ζ ^ 21 - ((17724 / 31205) : ℂ) * ζ ^ 22 - ((102191 / 187230) : ℂ) * ζ ^ 23 - ((1544 / 18723) : ℂ) * ζ ^ 24 + ((101509 / 93615) : ℂ) * ζ ^ 25 + ((178667 / 187230) : ℂ) * ζ ^ 26 - ((13061 / 37446) : ℂ) * ζ ^ 27 - ((46811 / 93615) : ℂ) * ζ ^ 28 - ((471 / 12482) : ℂ) * ζ ^ 29 + ((350 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep01CoefficientIdentity04 :
    row18_reducedY22_combinationStep01Coefficient04 =
      row18_reducedY22_combinationStep00Coefficient04 +
        row18_reducedY22_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep01Coefficient04 row18_reducedY22_combinationStep00Coefficient04 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep01CoefficientIdentity05 :
    row18_reducedY22_combinationStep01Coefficient05 =
      row18_reducedY22_combinationStep00Coefficient05 +
        row18_reducedY22_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep01Coefficient05 row18_reducedY22_combinationStep00Coefficient05 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep01CoefficientIdentity06 :
    row18_reducedY22_combinationStep01Coefficient06 =
      row18_reducedY22_combinationStep00Coefficient06 +
        row18_reducedY22_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep01Coefficient06 row18_reducedY22_combinationStep00Coefficient06 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep01CoefficientIdentity07 :
    row18_reducedY22_combinationStep01Coefficient07 =
      row18_reducedY22_combinationStep00Coefficient07 +
        row18_reducedY22_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep01Coefficient07 row18_reducedY22_combinationStep00Coefficient07 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep01CoefficientIdentity08 :
    row18_reducedY22_combinationStep01Coefficient08 =
      row18_reducedY22_combinationStep00Coefficient08 +
        row18_reducedY22_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep01Coefficient08 row18_reducedY22_combinationStep00Coefficient08 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep01CoefficientIdentity09 :
    row18_reducedY22_combinationStep01Coefficient09 =
      row18_reducedY22_combinationStep00Coefficient09 +
        row18_reducedY22_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep01Coefficient09 row18_reducedY22_combinationStep00Coefficient09 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep01CoefficientIdentity10 :
    row18_reducedY22_combinationStep01Coefficient10 =
      row18_reducedY22_combinationStep00Coefficient10 +
        row18_reducedY22_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep01Coefficient10 row18_reducedY22_combinationStep00Coefficient10 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep01CoefficientIdentity11 :
    row18_reducedY22_combinationStep01Coefficient11 =
      row18_reducedY22_combinationStep00Coefficient11 +
        row18_reducedY22_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep01Coefficient11 row18_reducedY22_combinationStep00Coefficient11 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep01CoefficientIdentity12 :
    row18_reducedY22_combinationStep01Coefficient12 =
      row18_reducedY22_combinationStep00Coefficient12 +
        row18_reducedY22_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep01Coefficient12 row18_reducedY22_combinationStep00Coefficient12 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep01CoefficientIdentity13 :
    row18_reducedY22_combinationStep01Coefficient13 =
      row18_reducedY22_combinationStep00Coefficient13 +
        row18_reducedY22_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep01Coefficient13 row18_reducedY22_combinationStep00Coefficient13 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep01CoefficientIdentity14 :
    row18_reducedY22_combinationStep01Coefficient14 =
      row18_reducedY22_combinationStep00Coefficient14 +
        row18_reducedY22_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep01Coefficient14 row18_reducedY22_combinationStep00Coefficient14 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep01CoefficientIdentity15 :
    row18_reducedY22_combinationStep01Coefficient15 =
      row18_reducedY22_combinationStep00Coefficient15 +
        row18_reducedY22_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep01Coefficient15 row18_reducedY22_combinationStep00Coefficient15 row18_reducedY22_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY22_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY22_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY22_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY22_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY22_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY22_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY22_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY22_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY22_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY22_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY22_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY22_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY22_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY22_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY22_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY22_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY22_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY22_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY22_combinationStep01CoefficientIdentity00,
      row18_reducedY22_combinationStep01CoefficientIdentity01,
      row18_reducedY22_combinationStep01CoefficientIdentity02,
      row18_reducedY22_combinationStep01CoefficientIdentity03,
      row18_reducedY22_combinationStep01CoefficientIdentity04,
      row18_reducedY22_combinationStep01CoefficientIdentity05,
      row18_reducedY22_combinationStep01CoefficientIdentity06,
      row18_reducedY22_combinationStep01CoefficientIdentity07,
      row18_reducedY22_combinationStep01CoefficientIdentity08,
      row18_reducedY22_combinationStep01CoefficientIdentity09,
      row18_reducedY22_combinationStep01CoefficientIdentity10,
      row18_reducedY22_combinationStep01CoefficientIdentity11,
      row18_reducedY22_combinationStep01CoefficientIdentity12,
      row18_reducedY22_combinationStep01CoefficientIdentity13,
      row18_reducedY22_combinationStep01CoefficientIdentity14,
      row18_reducedY22_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY22_combinationStep01Multiplier * equation

private def row18_reducedY22_combinationStep02Multiplier : ℂ :=
  (((1330 / 237) : ℂ) + ((4762 / 1185) : ℂ) * ζ ^ 1 - ((4348 / 1185) : ℂ) * ζ ^ 2 - ((7408 / 1185) : ℂ) * ζ ^ 3 + ((856 / 1185) : ℂ) * ζ ^ 5 - ((1164 / 395) : ℂ) * ζ ^ 6 - ((1654 / 237) : ℂ) * ζ ^ 8 - ((8384 / 1185) : ℂ) * ζ ^ 9 - ((976 / 1185) : ℂ) * ζ ^ 11 - ((1654 / 237) : ℂ) * ζ ^ 12 - ((4762 / 1185) : ℂ) * ζ ^ 13 + ((3502 / 1185) : ℂ) * ζ ^ 15 - ((4762 / 1185) : ℂ) * ζ ^ 17 - ((856 / 1185) : ℂ) * ζ ^ 18 + ((882 / 395) : ℂ) * ζ ^ 21 + ((4348 / 1185) : ℂ) * ζ ^ 22 + ((1302 / 395) : ℂ) * ζ ^ 25 - ((882 / 395) : ℂ) * ζ ^ 27 + ((1654 / 237) : ℂ) * ζ ^ 28 + ((4762 / 1185) : ℂ) * ζ ^ 29 - ((582 / 395) : ℂ) * ζ ^ 30 + ((976 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY22_combinationStep02Coefficient00 : ℂ :=
  (-((26531 / 37446) : ℂ) - ((40549 / 31205) : ℂ) * ζ ^ 1 + ((41882 / 31205) : ℂ) * ζ ^ 2 + ((78988 / 93615) : ℂ) * ζ ^ 3 - ((6206 / 93615) : ℂ) * ζ ^ 5 + ((34903 / 31205) : ℂ) * ζ ^ 6 + ((36535 / 18723) : ℂ) * ζ ^ 8 + ((213214 / 93615) : ℂ) * ζ ^ 9 + ((44742 / 31205) : ℂ) * ζ ^ 11 + ((36535 / 18723) : ℂ) * ζ ^ 12 + ((40549 / 31205) : ℂ) * ζ ^ 13 + ((12151 / 31205) : ℂ) * ζ ^ 15 + ((40549 / 31205) : ℂ) * ζ ^ 17 + ((6979 / 31205) : ℂ) * ζ ^ 18 + ((42659 / 93615) : ℂ) * ζ ^ 21 - ((41882 / 31205) : ℂ) * ζ ^ 22 - ((115441 / 93615) : ℂ) * ζ ^ 25 - ((42659 / 93615) : ℂ) * ζ ^ 27 - ((36535 / 18723) : ℂ) * ζ ^ 28 - ((40549 / 31205) : ℂ) * ζ ^ 29 + ((34903 / 62410) : ℂ) * ζ ^ 30 - ((44742 / 31205) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep02CoefficientIdentity00 :
    row18_reducedY22_combinationStep02Coefficient00 =
      row18_reducedY22_combinationStep01Coefficient00 +
        row18_reducedY22_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep02Coefficient00 row18_reducedY22_combinationStep01Coefficient00 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 (((285 / 12482) : ℂ) - ((27361 / 62410) : ℂ) * ζ ^ 1 - ((412513 / 187230) : ℂ) * ζ ^ 2 - ((27746 / 93615) : ℂ) * ζ ^ 3 + ((144533 / 187230) : ℂ) * ζ ^ 4 + ((58528 / 93615) : ℂ) * ζ ^ 5 - ((144871 / 93615) : ℂ) * ζ ^ 6 - ((1166 / 6241) : ℂ) * ζ ^ 7 + ((18481 / 93615) : ℂ) * ζ ^ 8 - ((121367 / 93615) : ℂ) * ζ ^ 9 + ((482311 / 187230) : ℂ) * ζ ^ 10 - ((30083 / 37446) : ℂ) * ζ ^ 11 - ((14528 / 31205) : ℂ) * ζ ^ 12 + ((89209 / 37446) : ℂ) * ζ ^ 13 - ((475219 / 187230) : ℂ) * ζ ^ 14 - ((5167 / 37446) : ℂ) * ζ ^ 15 + ((36791 / 93615) : ℂ) * ζ ^ 16 - ((123917 / 62410) : ℂ) * ζ ^ 17 + ((73423 / 62410) : ℂ) * ζ ^ 18 + ((166969 / 187230) : ℂ) * ζ ^ 19 + ((27901 / 187230) : ℂ) * ζ ^ 20 + ((22602 / 31205) : ℂ) * ζ ^ 21 + ((52069 / 93615) : ℂ) * ζ ^ 22 + ((49511 / 187230) : ℂ) * ζ ^ 23 - ((139013 / 187230) : ℂ) * ζ ^ 24 - ((2667 / 62410) : ℂ) * ζ ^ 25 - ((14212 / 93615) : ℂ) * ζ ^ 26 - ((6889 / 187230) : ℂ) * ζ ^ 27 + ((5267 / 18723) : ℂ) * ζ ^ 28 - ((2003 / 18723) : ℂ) * ζ ^ 29 + ((3416 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep02Coefficient01 : ℂ :=
  (-((8678 / 18723) : ℂ) + ((82025 / 18723) : ℂ) * ζ ^ 1 - ((1552 / 6241) : ℂ) * ζ ^ 2 - ((111595 / 18723) : ℂ) * ζ ^ 3 + ((82025 / 18723) : ℂ) * ζ ^ 5 - ((13334 / 18723) : ℂ) * ζ ^ 6 + ((13334 / 18723) : ℂ) * ζ ^ 8 - ((82025 / 18723) : ℂ) * ζ ^ 9 + ((111595 / 37446) : ℂ) * ζ ^ 11 - ((8633 / 6241) : ℂ) * ζ ^ 12 - ((82025 / 18723) : ℂ) * ζ ^ 13 + ((25823 / 18723) : ℂ) * ζ ^ 15 - ((82025 / 18723) : ℂ) * ζ ^ 17 - ((73298 / 18723) : ℂ) * ζ ^ 18 - ((132283 / 37446) : ℂ) * ζ ^ 21 + ((1552 / 6241) : ℂ) * ζ ^ 22 - ((86632 / 18723) : ℂ) * ζ ^ 24 - ((85772 / 18723) : ℂ) * ζ ^ 27 - ((13334 / 18723) : ℂ) * ζ ^ 28 + ((82025 / 18723) : ℂ) * ζ ^ 29 - ((39233 / 18723) : ℂ) * ζ ^ 30 - ((111595 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep02CoefficientIdentity01 :
    row18_reducedY22_combinationStep02Coefficient01 =
      row18_reducedY22_combinationStep01Coefficient01 +
        row18_reducedY22_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep02Coefficient01 row18_reducedY22_combinationStep01Coefficient01 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 (((177475 / 37446) : ℂ) - ((993491 / 187230) : ℂ) * ζ ^ 1 - ((59151 / 31205) : ℂ) * ζ ^ 2 + ((661663 / 187230) : ℂ) * ζ ^ 3 - ((106039 / 37446) : ℂ) * ζ ^ 4 - ((224617 / 187230) : ℂ) * ζ ^ 5 + ((784223 / 187230) : ℂ) * ζ ^ 6 - ((138893 / 187230) : ℂ) * ζ ^ 7 - ((249649 / 93615) : ℂ) * ζ ^ 8 + ((462299 / 93615) : ℂ) * ζ ^ 9 - ((129541 / 187230) : ℂ) * ζ ^ 10 - ((36537 / 62410) : ℂ) * ζ ^ 11 + ((68168 / 18723) : ℂ) * ζ ^ 12 - ((48051 / 31205) : ℂ) * ζ ^ 13 + ((72698 / 31205) : ℂ) * ζ ^ 14 + ((456419 / 187230) : ℂ) * ζ ^ 15 - ((534493 / 187230) : ℂ) * ζ ^ 16 + ((209959 / 93615) : ℂ) * ζ ^ 17 + ((334237 / 93615) : ℂ) * ζ ^ 18 - ((124088 / 93615) : ℂ) * ζ ^ 19 + ((20089 / 18723) : ℂ) * ζ ^ 20 + ((718729 / 187230) : ℂ) * ζ ^ 21 - ((35608 / 31205) : ℂ) * ζ ^ 22 - ((100589 / 93615) : ℂ) * ζ ^ 23 + ((537091 / 187230) : ℂ) * ζ ^ 24 - ((129593 / 93615) : ℂ) * ζ ^ 25 - ((11138 / 31205) : ℂ) * ζ ^ 26 + ((147299 / 93615) : ℂ) * ζ ^ 27 - ((19223 / 62410) : ℂ) * ζ ^ 28 + ((5001 / 62410) : ℂ) * ζ ^ 29 + ((3172 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep02Coefficient02 : ℂ :=
  (-((491 / 237) : ℂ) - ((302 / 79) : ℂ) * ζ ^ 1 + ((611 / 474) : ℂ) * ζ ^ 2 + ((883 / 474) : ℂ) * ζ ^ 3 - ((475 / 79) : ℂ) * ζ ^ 5 - ((122 / 237) : ℂ) * ζ ^ 6 + ((281 / 237) : ℂ) * ζ ^ 8 + ((129 / 158) : ℂ) * ζ ^ 9 - ((1007 / 237) : ℂ) * ζ ^ 11 + ((285 / 158) : ℂ) * ζ ^ 12 + ((302 / 79) : ℂ) * ζ ^ 13 - ((883 / 474) : ℂ) * ζ ^ 15 + ((302 / 79) : ℂ) * ζ ^ 17 + ((371 / 474) : ℂ) * ζ ^ 18 + ((173 / 79) : ℂ) * ζ ^ 21 - ((611 / 474) : ℂ) * ζ ^ 22 - ((611 / 474) : ℂ) * ζ ^ 24 + ((173 / 79) : ℂ) * ζ ^ 25 + ((1007 / 237) : ℂ) * ζ ^ 27 - ((281 / 237) : ℂ) * ζ ^ 28 - ((302 / 79) : ℂ) * ζ ^ 29 + ((49 / 474) : ℂ) * ζ ^ 30 + ((1007 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep02CoefficientIdentity02 :
    row18_reducedY22_combinationStep02Coefficient02 =
      row18_reducedY22_combinationStep01Coefficient02 +
        row18_reducedY22_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep02Coefficient02 row18_reducedY22_combinationStep01Coefficient02 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep02Coefficient03 : ℂ :=
  (((112 / 237) : ℂ) + ((422 / 237) : ℂ) * ζ ^ 1 - ((175 / 474) : ℂ) * ζ ^ 2 - ((703 / 474) : ℂ) * ζ ^ 3 + ((278 / 237) : ℂ) * ζ ^ 5 + ((455 / 237) : ℂ) * ζ ^ 6 - ((116 / 237) : ℂ) * ζ ^ 8 - ((58 / 79) : ℂ) * ζ ^ 9 + ((355 / 474) : ℂ) * ζ ^ 11 - ((116 / 237) : ℂ) * ζ ^ 12 - ((422 / 237) : ℂ) * ζ ^ 13 + ((415 / 474) : ℂ) * ζ ^ 15 - ((422 / 237) : ℂ) * ζ ^ 17 - ((1085 / 474) : ℂ) * ζ ^ 18 - ((47 / 158) : ℂ) * ζ ^ 21 + ((175 / 474) : ℂ) * ζ ^ 22 + ((48 / 79) : ℂ) * ζ ^ 25 + ((47 / 158) : ℂ) * ζ ^ 27 + ((116 / 237) : ℂ) * ζ ^ 28 + ((422 / 237) : ℂ) * ζ ^ 29 + ((455 / 474) : ℂ) * ζ ^ 30 - ((355 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep02CoefficientIdentity03 :
    row18_reducedY22_combinationStep02Coefficient03 =
      row18_reducedY22_combinationStep01Coefficient03 +
        row18_reducedY22_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep02Coefficient03 row18_reducedY22_combinationStep01Coefficient03 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep02Coefficient04 : ℂ :=
  (((2945 / 12482) : ℂ) - ((45043 / 93615) : ℂ) * ζ ^ 1 - ((182167 / 187230) : ℂ) * ζ ^ 2 + ((39903 / 62410) : ℂ) * ζ ^ 3 - ((103604 / 93615) : ℂ) * ζ ^ 5 - ((284434 / 93615) : ℂ) * ζ ^ 6 - ((27371 / 18723) : ℂ) * ζ ^ 8 - ((144484 / 93615) : ℂ) * ζ ^ 9 - ((408677 / 187230) : ℂ) * ζ ^ 11 - ((27371 / 18723) : ℂ) * ζ ^ 12 + ((45043 / 93615) : ℂ) * ζ ^ 13 - ((236831 / 187230) : ℂ) * ζ ^ 15 + ((45043 / 93615) : ℂ) * ζ ^ 17 + ((386701 / 187230) : ℂ) * ζ ^ 18 - ((29623 / 187230) : ℂ) * ζ ^ 21 + ((182167 / 187230) : ℂ) * ζ ^ 22 + ((58561 / 93615) : ℂ) * ζ ^ 25 + ((29623 / 187230) : ℂ) * ζ ^ 27 + ((27371 / 18723) : ℂ) * ζ ^ 28 - ((45043 / 93615) : ℂ) * ζ ^ 29 - ((142217 / 93615) : ℂ) * ζ ^ 30 + ((408677 / 187230) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep02CoefficientIdentity04 :
    row18_reducedY22_combinationStep02Coefficient04 =
      row18_reducedY22_combinationStep01Coefficient04 +
        row18_reducedY22_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep02Coefficient04 row18_reducedY22_combinationStep01Coefficient04 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 (-((285 / 12482) : ℂ) + ((27361 / 62410) : ℂ) * ζ ^ 1 + ((412513 / 187230) : ℂ) * ζ ^ 2 + ((27746 / 93615) : ℂ) * ζ ^ 3 - ((144533 / 187230) : ℂ) * ζ ^ 4 - ((58528 / 93615) : ℂ) * ζ ^ 5 + ((144871 / 93615) : ℂ) * ζ ^ 6 + ((1166 / 6241) : ℂ) * ζ ^ 7 - ((18481 / 93615) : ℂ) * ζ ^ 8 + ((121367 / 93615) : ℂ) * ζ ^ 9 - ((482311 / 187230) : ℂ) * ζ ^ 10 + ((30083 / 37446) : ℂ) * ζ ^ 11 + ((14528 / 31205) : ℂ) * ζ ^ 12 - ((89209 / 37446) : ℂ) * ζ ^ 13 + ((475219 / 187230) : ℂ) * ζ ^ 14 + ((5167 / 37446) : ℂ) * ζ ^ 15 - ((36791 / 93615) : ℂ) * ζ ^ 16 + ((123917 / 62410) : ℂ) * ζ ^ 17 - ((73423 / 62410) : ℂ) * ζ ^ 18 - ((166969 / 187230) : ℂ) * ζ ^ 19 - ((27901 / 187230) : ℂ) * ζ ^ 20 - ((22602 / 31205) : ℂ) * ζ ^ 21 - ((52069 / 93615) : ℂ) * ζ ^ 22 - ((49511 / 187230) : ℂ) * ζ ^ 23 + ((139013 / 187230) : ℂ) * ζ ^ 24 + ((2667 / 62410) : ℂ) * ζ ^ 25 + ((14212 / 93615) : ℂ) * ζ ^ 26 + ((6889 / 187230) : ℂ) * ζ ^ 27 - ((5267 / 18723) : ℂ) * ζ ^ 28 + ((2003 / 18723) : ℂ) * ζ ^ 29 - ((3416 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep02CoefficientIdentity05 :
    row18_reducedY22_combinationStep02Coefficient05 =
      row18_reducedY22_combinationStep01Coefficient05 +
        row18_reducedY22_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep02Coefficient05 row18_reducedY22_combinationStep01Coefficient05 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep02Coefficient06 : ℂ :=
  (-((13834 / 93615) : ℂ) + ((130777 / 37446) : ℂ) * ζ ^ 1 + ((258317 / 93615) : ℂ) * ζ ^ 2 + ((31236 / 31205) : ℂ) * ζ ^ 3 - ((28157 / 93615) : ℂ) * ζ ^ 6 + ((56209 / 31205) : ℂ) * ζ ^ 8 + ((65795 / 37446) : ℂ) * ζ ^ 9 - ((427763 / 187230) : ℂ) * ζ ^ 11 - ((286474 / 93615) : ℂ) * ζ ^ 12 - ((130777 / 37446) : ℂ) * ζ ^ 13 + ((31236 / 31205) : ℂ) * ζ ^ 15 - ((130777 / 37446) : ℂ) * ζ ^ 17 - ((90717 / 31205) : ℂ) * ζ ^ 18 - ((130777 / 37446) : ℂ) * ζ ^ 21 - ((258317 / 93615) : ℂ) * ζ ^ 22 + ((258317 / 93615) : ℂ) * ζ ^ 24 + ((130777 / 37446) : ℂ) * ζ ^ 25 - ((427763 / 187230) : ℂ) * ζ ^ 27 - ((56209 / 31205) : ℂ) * ζ ^ 28 + ((130777 / 37446) : ℂ) * ζ ^ 29 + ((426944 / 93615) : ℂ) * ζ ^ 30 + ((427763 / 187230) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep02CoefficientIdentity06 :
    row18_reducedY22_combinationStep02Coefficient06 =
      row18_reducedY22_combinationStep01Coefficient06 +
        row18_reducedY22_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep02Coefficient06 row18_reducedY22_combinationStep01Coefficient06 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 (-((16447 / 31205) : ℂ) - ((350569 / 93615) : ℂ) * ζ ^ 1 - ((73274 / 31205) : ℂ) * ζ ^ 2 - ((21317 / 187230) : ℂ) * ζ ^ 3 + ((65794 / 93615) : ℂ) * ζ ^ 4 + ((336721 / 93615) : ℂ) * ζ ^ 5 + ((182962 / 93615) : ℂ) * ζ ^ 6 - ((87043 / 187230) : ℂ) * ζ ^ 7 - ((12143 / 187230) : ℂ) * ζ ^ 8 - ((78613 / 37446) : ℂ) * ζ ^ 9 - ((303197 / 187230) : ℂ) * ζ ^ 10 + ((4881 / 62410) : ℂ) * ζ ^ 11 + ((34525 / 37446) : ℂ) * ζ ^ 12 + ((347777 / 187230) : ℂ) * ζ ^ 13 + ((1451 / 18723) : ℂ) * ζ ^ 14 - ((34769 / 37446) : ℂ) * ζ ^ 15 - ((319189 / 187230) : ℂ) * ζ ^ 16 - ((153751 / 93615) : ℂ) * ζ ^ 17 + ((96839 / 187230) : ℂ) * ζ ^ 18 + ((31162 / 31205) : ℂ) * ζ ^ 19 + ((138833 / 93615) : ℂ) * ζ ^ 20 + ((97777 / 187230) : ℂ) * ζ ^ 21 - ((10711 / 12482) : ℂ) * ζ ^ 22 - ((14371 / 62410) : ℂ) * ζ ^ 23 - ((52279 / 37446) : ℂ) * ζ ^ 24 - ((24577 / 31205) : ℂ) * ζ ^ 25 + ((49291 / 37446) : ℂ) * ζ ^ 26 + ((68086 / 93615) : ℂ) * ζ ^ 27 + ((31 / 37446) : ℂ) * ζ ^ 28 + ((3443 / 62410) : ℂ) * ζ ^ 29 + ((244 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep02CoefficientIdentity07 :
    row18_reducedY22_combinationStep02Coefficient07 =
      row18_reducedY22_combinationStep01Coefficient07 +
        row18_reducedY22_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep02Coefficient07 row18_reducedY22_combinationStep01Coefficient07 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep02CoefficientIdentity08 :
    row18_reducedY22_combinationStep02Coefficient08 =
      row18_reducedY22_combinationStep01Coefficient08 +
        row18_reducedY22_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep02Coefficient08 row18_reducedY22_combinationStep01Coefficient08 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep02CoefficientIdentity09 :
    row18_reducedY22_combinationStep02Coefficient09 =
      row18_reducedY22_combinationStep01Coefficient09 +
        row18_reducedY22_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep02Coefficient09 row18_reducedY22_combinationStep01Coefficient09 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep02CoefficientIdentity10 :
    row18_reducedY22_combinationStep02Coefficient10 =
      row18_reducedY22_combinationStep01Coefficient10 +
        row18_reducedY22_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep02Coefficient10 row18_reducedY22_combinationStep01Coefficient10 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep02CoefficientIdentity11 :
    row18_reducedY22_combinationStep02Coefficient11 =
      row18_reducedY22_combinationStep01Coefficient11 +
        row18_reducedY22_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep02Coefficient11 row18_reducedY22_combinationStep01Coefficient11 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep02CoefficientIdentity12 :
    row18_reducedY22_combinationStep02Coefficient12 =
      row18_reducedY22_combinationStep01Coefficient12 +
        row18_reducedY22_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep02Coefficient12 row18_reducedY22_combinationStep01Coefficient12 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep02CoefficientIdentity13 :
    row18_reducedY22_combinationStep02Coefficient13 =
      row18_reducedY22_combinationStep01Coefficient13 +
        row18_reducedY22_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep02Coefficient13 row18_reducedY22_combinationStep01Coefficient13 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep02CoefficientIdentity14 :
    row18_reducedY22_combinationStep02Coefficient14 =
      row18_reducedY22_combinationStep01Coefficient14 +
        row18_reducedY22_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep02Coefficient14 row18_reducedY22_combinationStep01Coefficient14 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep02CoefficientIdentity15 :
    row18_reducedY22_combinationStep02Coefficient15 =
      row18_reducedY22_combinationStep01Coefficient15 +
        row18_reducedY22_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep02Coefficient15 row18_reducedY22_combinationStep01Coefficient15 row18_reducedY22_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY22_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY22_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY22_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY22_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY22_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY22_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY22_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY22_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY22_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY22_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY22_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY22_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY22_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY22_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY22_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY22_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY22_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY22_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY22_combinationStep02CoefficientIdentity00,
      row18_reducedY22_combinationStep02CoefficientIdentity01,
      row18_reducedY22_combinationStep02CoefficientIdentity02,
      row18_reducedY22_combinationStep02CoefficientIdentity03,
      row18_reducedY22_combinationStep02CoefficientIdentity04,
      row18_reducedY22_combinationStep02CoefficientIdentity05,
      row18_reducedY22_combinationStep02CoefficientIdentity06,
      row18_reducedY22_combinationStep02CoefficientIdentity07,
      row18_reducedY22_combinationStep02CoefficientIdentity08,
      row18_reducedY22_combinationStep02CoefficientIdentity09,
      row18_reducedY22_combinationStep02CoefficientIdentity10,
      row18_reducedY22_combinationStep02CoefficientIdentity11,
      row18_reducedY22_combinationStep02CoefficientIdentity12,
      row18_reducedY22_combinationStep02CoefficientIdentity13,
      row18_reducedY22_combinationStep02CoefficientIdentity14,
      row18_reducedY22_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY22_combinationStep02Multiplier * equation

private def row18_reducedY22_combinationStep03Multiplier : ℂ :=
  (((68 / 79) : ℂ) + ((226 / 79) : ℂ) * ζ ^ 1 - ((424 / 237) : ℂ) * ζ ^ 2 - ((910 / 237) : ℂ) * ζ ^ 5 - ((628 / 237) : ℂ) * ζ ^ 6 - ((628 / 237) : ℂ) * ζ ^ 8 - ((910 / 237) : ℂ) * ζ ^ 9 - ((348 / 79) : ℂ) * ζ ^ 11 - ((254 / 79) : ℂ) * ζ ^ 12 - ((226 / 79) : ℂ) * ζ ^ 13 - ((256 / 237) : ℂ) * ζ ^ 15 - ((226 / 79) : ℂ) * ζ ^ 17 - ((92 / 237) : ℂ) * ζ ^ 18 + ((116 / 237) : ℂ) * ζ ^ 21 + ((424 / 237) : ℂ) * ζ ^ 22 + ((240 / 79) : ℂ) * ζ ^ 24 + ((1588 / 237) : ℂ) * ζ ^ 25 + ((256 / 237) : ℂ) * ζ ^ 27 + ((628 / 237) : ℂ) * ζ ^ 28 + ((226 / 79) : ℂ) * ζ ^ 29 + ((134 / 237) : ℂ) * ζ ^ 30 + ((348 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY22_combinationStep03Coefficient00 : ℂ :=
  (((103 / 79) : ℂ) + ((124 / 395) : ℂ) * ζ ^ 1 + ((743 / 395) : ℂ) * ζ ^ 2 - ((757 / 790) : ℂ) * ζ ^ 3 + ((1069 / 790) : ℂ) * ζ ^ 5 + ((1382 / 395) : ℂ) * ζ ^ 6 + ((88 / 79) : ℂ) * ζ ^ 8 + ((809 / 790) : ℂ) * ζ ^ 9 + ((783 / 395) : ℂ) * ζ ^ 11 + ((88 / 79) : ℂ) * ζ ^ 12 - ((124 / 395) : ℂ) * ζ ^ 13 + ((789 / 395) : ℂ) * ζ ^ 15 - ((124 / 395) : ℂ) * ζ ^ 17 - ((639 / 395) : ℂ) * ζ ^ 18 + ((509 / 790) : ℂ) * ζ ^ 21 - ((743 / 395) : ℂ) * ζ ^ 22 - ((821 / 790) : ℂ) * ζ ^ 25 - ((509 / 790) : ℂ) * ζ ^ 27 - ((88 / 79) : ℂ) * ζ ^ 28 + ((124 / 395) : ℂ) * ζ ^ 29 + ((691 / 395) : ℂ) * ζ ^ 30 - ((783 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep03CoefficientIdentity00 :
    row18_reducedY22_combinationStep03Coefficient00 =
      row18_reducedY22_combinationStep02Coefficient00 +
        row18_reducedY22_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep03Coefficient00 row18_reducedY22_combinationStep02Coefficient00 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 (-((71477 / 37446) : ℂ) - ((8143 / 6241) : ℂ) * ζ ^ 1 - ((31519 / 37446) : ℂ) * ζ ^ 2 + ((11919 / 6241) : ℂ) * ζ ^ 3 + ((61009 / 37446) : ℂ) * ζ ^ 4 - ((5499 / 12482) : ℂ) * ζ ^ 5 - ((30080 / 18723) : ℂ) * ζ ^ 6 - ((60911 / 37446) : ℂ) * ζ ^ 7 - ((15781 / 12482) : ℂ) * ζ ^ 8 + ((29195 / 37446) : ℂ) * ζ ^ 9 + ((15551 / 12482) : ℂ) * ζ ^ 10 + ((13468 / 18723) : ℂ) * ζ ^ 11 + ((7207 / 37446) : ℂ) * ζ ^ 12 + ((739 / 18723) : ℂ) * ζ ^ 13 - ((6609 / 12482) : ℂ) * ζ ^ 14 - ((9385 / 37446) : ℂ) * ζ ^ 15 - ((2155 / 18723) : ℂ) * ζ ^ 16 + ((2001 / 12482) : ℂ) * ζ ^ 17 + ((22121 / 37446) : ℂ) * ζ ^ 18 + ((16867 / 18723) : ℂ) * ζ ^ 19 + ((11605 / 37446) : ℂ) * ζ ^ 20 - ((25 / 237) : ℂ) * ζ ^ 21 - ((13783 / 18723) : ℂ) * ζ ^ 22 - ((17662 / 18723) : ℂ) * ζ ^ 23 + ((9169 / 18723) : ℂ) * ζ ^ 24 + ((36841 / 37446) : ℂ) * ζ ^ 25 - ((893 / 18723) : ℂ) * ζ ^ 26 + ((8945 / 37446) : ℂ) * ζ ^ 27 - ((5029 / 12482) : ℂ) * ζ ^ 28 - ((8687 / 12482) : ℂ) * ζ ^ 29 - ((1305 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep03Coefficient01 : ℂ :=
  (-((33 / 158) : ℂ) + ((23 / 158) : ℂ) * ζ ^ 1 - ((7 / 158) : ℂ) * ζ ^ 2 - ((14 / 79) : ℂ) * ζ ^ 3 + ((23 / 158) : ℂ) * ζ ^ 5 - ((20 / 79) : ℂ) * ζ ^ 6 + ((20 / 79) : ℂ) * ζ ^ 8 - ((23 / 158) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((45 / 158) : ℂ) * ζ ^ 12 - ((23 / 158) : ℂ) * ζ ^ 13 - ((11 / 158) : ℂ) * ζ ^ 15 - ((23 / 158) : ℂ) * ζ ^ 17 + ((16 / 79) : ℂ) * ζ ^ 18 - ((29 / 79) : ℂ) * ζ ^ 21 + ((7 / 158) : ℂ) * ζ ^ 22 - ((4 / 79) : ℂ) * ζ ^ 24 - ((39 / 158) : ℂ) * ζ ^ 27 - ((20 / 79) : ℂ) * ζ ^ 28 + ((23 / 158) : ℂ) * ζ ^ 29 + ((5 / 158) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep03CoefficientIdentity01 :
    row18_reducedY22_combinationStep03Coefficient01 =
      row18_reducedY22_combinationStep02Coefficient01 +
        row18_reducedY22_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep03Coefficient01 row18_reducedY22_combinationStep02Coefficient01 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 (-((6271 / 37446) : ℂ) + ((175261 / 37446) : ℂ) * ζ ^ 1 + ((10042 / 18723) : ℂ) * ζ ^ 2 - ((185981 / 37446) : ℂ) * ζ ^ 3 - ((8570 / 6241) : ℂ) * ζ ^ 4 - ((817 / 6241) : ℂ) * ζ ^ 5 - ((40033 / 37446) : ℂ) * ζ ^ 6 + ((13252 / 6241) : ℂ) * ζ ^ 7 + ((15195 / 12482) : ℂ) * ζ ^ 8 - ((155335 / 37446) : ℂ) * ζ ^ 9 - ((39139 / 37446) : ℂ) * ζ ^ 10 - ((14574 / 6241) : ℂ) * ζ ^ 11 - ((22671 / 6241) : ℂ) * ζ ^ 12 + ((9418 / 18723) : ℂ) * ζ ^ 13 - ((73571 / 37446) : ℂ) * ζ ^ 14 - ((43384 / 18723) : ℂ) * ζ ^ 15 + ((37349 / 18723) : ℂ) * ζ ^ 16 - ((41419 / 18723) : ℂ) * ζ ^ 17 - ((30792 / 6241) : ℂ) * ζ ^ 18 - ((78307 / 37446) : ℂ) * ζ ^ 19 - ((28687 / 12482) : ℂ) * ζ ^ 20 - ((17314 / 18723) : ℂ) * ζ ^ 21 + ((40226 / 18723) : ℂ) * ζ ^ 22 - ((3877 / 18723) : ℂ) * ζ ^ 23 - ((37193 / 18723) : ℂ) * ζ ^ 24 + ((276 / 6241) : ℂ) * ζ ^ 25 - ((53317 / 37446) : ℂ) * ζ ^ 26 + ((27011 / 37446) : ℂ) * ζ ^ 27 + ((6809 / 6241) : ℂ) * ζ ^ 28 + ((7202 / 18723) : ℂ) * ζ ^ 29 + ((2436 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep03Coefficient02 : ℂ :=
  (-((491 / 237) : ℂ) - ((302 / 79) : ℂ) * ζ ^ 1 + ((611 / 474) : ℂ) * ζ ^ 2 + ((883 / 474) : ℂ) * ζ ^ 3 - ((475 / 79) : ℂ) * ζ ^ 5 - ((122 / 237) : ℂ) * ζ ^ 6 + ((281 / 237) : ℂ) * ζ ^ 8 + ((129 / 158) : ℂ) * ζ ^ 9 - ((1007 / 237) : ℂ) * ζ ^ 11 + ((285 / 158) : ℂ) * ζ ^ 12 + ((302 / 79) : ℂ) * ζ ^ 13 - ((883 / 474) : ℂ) * ζ ^ 15 + ((302 / 79) : ℂ) * ζ ^ 17 + ((371 / 474) : ℂ) * ζ ^ 18 + ((173 / 79) : ℂ) * ζ ^ 21 - ((611 / 474) : ℂ) * ζ ^ 22 - ((611 / 474) : ℂ) * ζ ^ 24 + ((173 / 79) : ℂ) * ζ ^ 25 + ((1007 / 237) : ℂ) * ζ ^ 27 - ((281 / 237) : ℂ) * ζ ^ 28 - ((302 / 79) : ℂ) * ζ ^ 29 + ((49 / 474) : ℂ) * ζ ^ 30 + ((1007 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep03CoefficientIdentity02 :
    row18_reducedY22_combinationStep03Coefficient02 =
      row18_reducedY22_combinationStep02Coefficient02 +
        row18_reducedY22_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep03Coefficient02 row18_reducedY22_combinationStep02Coefficient02 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep03Coefficient03 : ℂ :=
  (((112 / 237) : ℂ) + ((422 / 237) : ℂ) * ζ ^ 1 - ((175 / 474) : ℂ) * ζ ^ 2 - ((703 / 474) : ℂ) * ζ ^ 3 + ((278 / 237) : ℂ) * ζ ^ 5 + ((455 / 237) : ℂ) * ζ ^ 6 - ((116 / 237) : ℂ) * ζ ^ 8 - ((58 / 79) : ℂ) * ζ ^ 9 + ((355 / 474) : ℂ) * ζ ^ 11 - ((116 / 237) : ℂ) * ζ ^ 12 - ((422 / 237) : ℂ) * ζ ^ 13 + ((415 / 474) : ℂ) * ζ ^ 15 - ((422 / 237) : ℂ) * ζ ^ 17 - ((1085 / 474) : ℂ) * ζ ^ 18 - ((47 / 158) : ℂ) * ζ ^ 21 + ((175 / 474) : ℂ) * ζ ^ 22 + ((48 / 79) : ℂ) * ζ ^ 25 + ((47 / 158) : ℂ) * ζ ^ 27 + ((116 / 237) : ℂ) * ζ ^ 28 + ((422 / 237) : ℂ) * ζ ^ 29 + ((455 / 474) : ℂ) * ζ ^ 30 - ((355 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep03CoefficientIdentity03 :
    row18_reducedY22_combinationStep03Coefficient03 =
      row18_reducedY22_combinationStep02Coefficient03 +
        row18_reducedY22_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep03Coefficient03 row18_reducedY22_combinationStep02Coefficient03 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep03Coefficient04 : ℂ :=
  (((2945 / 12482) : ℂ) - ((45043 / 93615) : ℂ) * ζ ^ 1 - ((182167 / 187230) : ℂ) * ζ ^ 2 + ((39903 / 62410) : ℂ) * ζ ^ 3 - ((103604 / 93615) : ℂ) * ζ ^ 5 - ((284434 / 93615) : ℂ) * ζ ^ 6 - ((27371 / 18723) : ℂ) * ζ ^ 8 - ((144484 / 93615) : ℂ) * ζ ^ 9 - ((408677 / 187230) : ℂ) * ζ ^ 11 - ((27371 / 18723) : ℂ) * ζ ^ 12 + ((45043 / 93615) : ℂ) * ζ ^ 13 - ((236831 / 187230) : ℂ) * ζ ^ 15 + ((45043 / 93615) : ℂ) * ζ ^ 17 + ((386701 / 187230) : ℂ) * ζ ^ 18 - ((29623 / 187230) : ℂ) * ζ ^ 21 + ((182167 / 187230) : ℂ) * ζ ^ 22 + ((58561 / 93615) : ℂ) * ζ ^ 25 + ((29623 / 187230) : ℂ) * ζ ^ 27 + ((27371 / 18723) : ℂ) * ζ ^ 28 - ((45043 / 93615) : ℂ) * ζ ^ 29 - ((142217 / 93615) : ℂ) * ζ ^ 30 + ((408677 / 187230) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep03CoefficientIdentity04 :
    row18_reducedY22_combinationStep03Coefficient04 =
      row18_reducedY22_combinationStep02Coefficient04 +
        row18_reducedY22_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep03Coefficient04 row18_reducedY22_combinationStep02Coefficient04 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep03Coefficient05 : ℂ :=
  (-((19921 / 37446) : ℂ) - ((89 / 37446) : ℂ) * ζ ^ 1 - ((31622 / 18723) : ℂ) * ζ ^ 2 - ((12463 / 12482) : ℂ) * ζ ^ 5 - ((14441 / 12482) : ℂ) * ζ ^ 6 - ((14441 / 12482) : ℂ) * ζ ^ 8 - ((12463 / 12482) : ℂ) * ζ ^ 9 - ((10313 / 6241) : ℂ) * ζ ^ 11 - ((13673 / 18723) : ℂ) * ζ ^ 12 + ((89 / 37446) : ℂ) * ζ ^ 13 - ((17109 / 12482) : ℂ) * ζ ^ 15 + ((89 / 37446) : ℂ) * ζ ^ 17 + ((11565 / 12482) : ℂ) * ζ ^ 18 + ((18739 / 37446) : ℂ) * ζ ^ 21 + ((31622 / 18723) : ℂ) * ζ ^ 22 + ((1438 / 6241) : ℂ) * ζ ^ 24 + ((18650 / 18723) : ℂ) * ζ ^ 25 + ((17109 / 12482) : ℂ) * ζ ^ 27 + ((14441 / 12482) : ℂ) * ζ ^ 28 - ((89 / 37446) : ℂ) * ζ ^ 29 - ((15977 / 37446) : ℂ) * ζ ^ 30 + ((10313 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep03CoefficientIdentity05 :
    row18_reducedY22_combinationStep03Coefficient05 =
      row18_reducedY22_combinationStep02Coefficient05 +
        row18_reducedY22_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep03Coefficient05 row18_reducedY22_combinationStep02Coefficient05 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 (((21145 / 37446) : ℂ) + ((3035 / 37446) : ℂ) * ζ ^ 1 + ((65641 / 37446) : ℂ) * ζ ^ 2 + ((30943 / 37446) : ℂ) * ζ ^ 3 - ((13281 / 12482) : ℂ) * ζ ^ 4 + ((15628 / 18723) : ℂ) * ζ ^ 5 - ((24 / 79) : ℂ) * ζ ^ 6 - ((29672 / 18723) : ℂ) * ζ ^ 7 + ((21632 / 18723) : ℂ) * ζ ^ 8 - ((981 / 6241) : ℂ) * ζ ^ 9 - ((3733 / 18723) : ℂ) * ζ ^ 10 + ((18423 / 12482) : ℂ) * ζ ^ 11 - ((1565 / 37446) : ℂ) * ζ ^ 12 - ((39167 / 37446) : ℂ) * ζ ^ 13 + ((43481 / 37446) : ℂ) * ζ ^ 14 - ((9992 / 18723) : ℂ) * ζ ^ 15 - ((9497 / 37446) : ℂ) * ζ ^ 16 + ((26251 / 18723) : ℂ) * ζ ^ 17 - ((9817 / 12482) : ℂ) * ζ ^ 18 - ((7173 / 12482) : ℂ) * ζ ^ 19 + ((7147 / 18723) : ℂ) * ζ ^ 20 - ((17551 / 18723) : ℂ) * ζ ^ 21 - ((2863 / 6241) : ℂ) * ζ ^ 22 - ((12509 / 37446) : ℂ) * ζ ^ 23 - ((12185 / 37446) : ℂ) * ζ ^ 24 + ((1087 / 18723) : ℂ) * ζ ^ 25 + ((5 / 79) : ℂ) * ζ ^ 26 + ((6187 / 12482) : ℂ) * ζ ^ 27 - ((4708 / 18723) : ℂ) * ζ ^ 28 + ((3707 / 18723) : ℂ) * ζ ^ 29 - ((1218 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep03Coefficient06 : ℂ :=
  (-((13834 / 93615) : ℂ) + ((130777 / 37446) : ℂ) * ζ ^ 1 + ((258317 / 93615) : ℂ) * ζ ^ 2 + ((31236 / 31205) : ℂ) * ζ ^ 3 - ((28157 / 93615) : ℂ) * ζ ^ 6 + ((56209 / 31205) : ℂ) * ζ ^ 8 + ((65795 / 37446) : ℂ) * ζ ^ 9 - ((427763 / 187230) : ℂ) * ζ ^ 11 - ((286474 / 93615) : ℂ) * ζ ^ 12 - ((130777 / 37446) : ℂ) * ζ ^ 13 + ((31236 / 31205) : ℂ) * ζ ^ 15 - ((130777 / 37446) : ℂ) * ζ ^ 17 - ((90717 / 31205) : ℂ) * ζ ^ 18 - ((130777 / 37446) : ℂ) * ζ ^ 21 - ((258317 / 93615) : ℂ) * ζ ^ 22 + ((258317 / 93615) : ℂ) * ζ ^ 24 + ((130777 / 37446) : ℂ) * ζ ^ 25 - ((427763 / 187230) : ℂ) * ζ ^ 27 - ((56209 / 31205) : ℂ) * ζ ^ 28 + ((130777 / 37446) : ℂ) * ζ ^ 29 + ((426944 / 93615) : ℂ) * ζ ^ 30 + ((427763 / 187230) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep03CoefficientIdentity06 :
    row18_reducedY22_combinationStep03Coefficient06 =
      row18_reducedY22_combinationStep02Coefficient06 +
        row18_reducedY22_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep03Coefficient06 row18_reducedY22_combinationStep02Coefficient06 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep03Coefficient07 : ℂ :=
  (-((75353 / 37446) : ℂ) - ((10069 / 6241) : ℂ) * ζ ^ 1 - ((3363 / 6241) : ℂ) * ζ ^ 2 + ((67477 / 37446) : ℂ) * ζ ^ 3 - ((53153 / 37446) : ℂ) * ζ ^ 5 - ((14855 / 6241) : ℂ) * ζ ^ 6 + ((15679 / 18723) : ℂ) * ζ ^ 8 + ((46939 / 37446) : ℂ) * ζ ^ 9 - ((3423 / 6241) : ℂ) * ζ ^ 11 + ((15679 / 18723) : ℂ) * ζ ^ 12 + ((10069 / 6241) : ℂ) * ζ ^ 13 - ((10036 / 6241) : ℂ) * ζ ^ 15 + ((10069 / 6241) : ℂ) * ζ ^ 17 + ((11492 / 6241) : ℂ) * ζ ^ 18 - ((7063 / 37446) : ℂ) * ζ ^ 21 + ((3363 / 6241) : ℂ) * ζ ^ 22 - ((7261 / 37446) : ℂ) * ζ ^ 25 + ((7063 / 37446) : ℂ) * ζ ^ 27 - ((15679 / 18723) : ℂ) * ζ ^ 28 - ((10069 / 6241) : ℂ) * ζ ^ 29 - ((14855 / 12482) : ℂ) * ζ ^ 30 + ((3423 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep03CoefficientIdentity07 :
    row18_reducedY22_combinationStep03Coefficient07 =
      row18_reducedY22_combinationStep02Coefficient07 +
        row18_reducedY22_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep03Coefficient07 row18_reducedY22_combinationStep02Coefficient07 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 (((71477 / 37446) : ℂ) + ((8143 / 6241) : ℂ) * ζ ^ 1 + ((31519 / 37446) : ℂ) * ζ ^ 2 - ((11919 / 6241) : ℂ) * ζ ^ 3 - ((61009 / 37446) : ℂ) * ζ ^ 4 + ((5499 / 12482) : ℂ) * ζ ^ 5 + ((30080 / 18723) : ℂ) * ζ ^ 6 + ((60911 / 37446) : ℂ) * ζ ^ 7 + ((15781 / 12482) : ℂ) * ζ ^ 8 - ((29195 / 37446) : ℂ) * ζ ^ 9 - ((15551 / 12482) : ℂ) * ζ ^ 10 - ((13468 / 18723) : ℂ) * ζ ^ 11 - ((7207 / 37446) : ℂ) * ζ ^ 12 - ((739 / 18723) : ℂ) * ζ ^ 13 + ((6609 / 12482) : ℂ) * ζ ^ 14 + ((9385 / 37446) : ℂ) * ζ ^ 15 + ((2155 / 18723) : ℂ) * ζ ^ 16 - ((2001 / 12482) : ℂ) * ζ ^ 17 - ((22121 / 37446) : ℂ) * ζ ^ 18 - ((16867 / 18723) : ℂ) * ζ ^ 19 - ((11605 / 37446) : ℂ) * ζ ^ 20 + ((25 / 237) : ℂ) * ζ ^ 21 + ((13783 / 18723) : ℂ) * ζ ^ 22 + ((17662 / 18723) : ℂ) * ζ ^ 23 - ((9169 / 18723) : ℂ) * ζ ^ 24 - ((36841 / 37446) : ℂ) * ζ ^ 25 + ((893 / 18723) : ℂ) * ζ ^ 26 - ((8945 / 37446) : ℂ) * ζ ^ 27 + ((5029 / 12482) : ℂ) * ζ ^ 28 + ((8687 / 12482) : ℂ) * ζ ^ 29 + ((1305 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep03CoefficientIdentity08 :
    row18_reducedY22_combinationStep03Coefficient08 =
      row18_reducedY22_combinationStep02Coefficient08 +
        row18_reducedY22_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep03Coefficient08 row18_reducedY22_combinationStep02Coefficient08 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep03CoefficientIdentity09 :
    row18_reducedY22_combinationStep03Coefficient09 =
      row18_reducedY22_combinationStep02Coefficient09 +
        row18_reducedY22_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep03Coefficient09 row18_reducedY22_combinationStep02Coefficient09 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep03CoefficientIdentity10 :
    row18_reducedY22_combinationStep03Coefficient10 =
      row18_reducedY22_combinationStep02Coefficient10 +
        row18_reducedY22_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep03Coefficient10 row18_reducedY22_combinationStep02Coefficient10 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep03CoefficientIdentity11 :
    row18_reducedY22_combinationStep03Coefficient11 =
      row18_reducedY22_combinationStep02Coefficient11 +
        row18_reducedY22_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep03Coefficient11 row18_reducedY22_combinationStep02Coefficient11 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep03CoefficientIdentity12 :
    row18_reducedY22_combinationStep03Coefficient12 =
      row18_reducedY22_combinationStep02Coefficient12 +
        row18_reducedY22_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep03Coefficient12 row18_reducedY22_combinationStep02Coefficient12 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep03CoefficientIdentity13 :
    row18_reducedY22_combinationStep03Coefficient13 =
      row18_reducedY22_combinationStep02Coefficient13 +
        row18_reducedY22_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep03Coefficient13 row18_reducedY22_combinationStep02Coefficient13 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep03CoefficientIdentity14 :
    row18_reducedY22_combinationStep03Coefficient14 =
      row18_reducedY22_combinationStep02Coefficient14 +
        row18_reducedY22_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep03Coefficient14 row18_reducedY22_combinationStep02Coefficient14 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep03CoefficientIdentity15 :
    row18_reducedY22_combinationStep03Coefficient15 =
      row18_reducedY22_combinationStep02Coefficient15 +
        row18_reducedY22_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep03Coefficient15 row18_reducedY22_combinationStep02Coefficient15 row18_reducedY22_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY22_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY22_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY22_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY22_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY22_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY22_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY22_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY22_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY22_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY22_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY22_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY22_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY22_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY22_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY22_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY22_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY22_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY22_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY22_combinationStep03CoefficientIdentity00,
      row18_reducedY22_combinationStep03CoefficientIdentity01,
      row18_reducedY22_combinationStep03CoefficientIdentity02,
      row18_reducedY22_combinationStep03CoefficientIdentity03,
      row18_reducedY22_combinationStep03CoefficientIdentity04,
      row18_reducedY22_combinationStep03CoefficientIdentity05,
      row18_reducedY22_combinationStep03CoefficientIdentity06,
      row18_reducedY22_combinationStep03CoefficientIdentity07,
      row18_reducedY22_combinationStep03CoefficientIdentity08,
      row18_reducedY22_combinationStep03CoefficientIdentity09,
      row18_reducedY22_combinationStep03CoefficientIdentity10,
      row18_reducedY22_combinationStep03CoefficientIdentity11,
      row18_reducedY22_combinationStep03CoefficientIdentity12,
      row18_reducedY22_combinationStep03CoefficientIdentity13,
      row18_reducedY22_combinationStep03CoefficientIdentity14,
      row18_reducedY22_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY22_combinationStep03Multiplier * equation

private def row18_reducedY22_combinationStep04Multiplier : ℂ :=
  (-((14 / 79) : ℂ) - ((120 / 79) : ℂ) * ζ ^ 1 - ((218 / 79) : ℂ) * ζ ^ 2 + ((52 / 79) : ℂ) * ζ ^ 5 - ((204 / 79) : ℂ) * ζ ^ 6 - ((204 / 79) : ℂ) * ζ ^ 8 + ((52 / 79) : ℂ) * ζ ^ 9 + ((94 / 79) : ℂ) * ζ ^ 11 - ((2 / 79) : ℂ) * ζ ^ 12 + ((120 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 + ((120 / 79) : ℂ) * ζ ^ 17 + ((148 / 79) : ℂ) * ζ ^ 18 + ((34 / 79) : ℂ) * ζ ^ 21 + ((218 / 79) : ℂ) * ζ ^ 22 + ((56 / 79) : ℂ) * ζ ^ 24 - ((172 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((204 / 79) : ℂ) * ζ ^ 28 - ((120 / 79) : ℂ) * ζ ^ 29 - ((202 / 79) : ℂ) * ζ ^ 30 - ((94 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY22_combinationStep04Coefficient00 : ℂ :=
  (((136 / 79) : ℂ) + ((4 / 395) : ℂ) * ζ ^ 1 + ((1391 / 790) : ℂ) * ζ ^ 2 - ((186 / 395) : ℂ) * ζ ^ 3 + ((582 / 395) : ℂ) * ζ ^ 5 + ((1392 / 395) : ℂ) * ζ ^ 6 + ((181 / 158) : ℂ) * ζ ^ 8 + ((642 / 395) : ℂ) * ζ ^ 9 + ((828 / 395) : ℂ) * ζ ^ 11 + ((181 / 158) : ℂ) * ζ ^ 12 - ((4 / 395) : ℂ) * ζ ^ 13 + ((764 / 395) : ℂ) * ζ ^ 15 - ((4 / 395) : ℂ) * ζ ^ 17 - ((1393 / 790) : ℂ) * ζ ^ 18 + ((182 / 395) : ℂ) * ζ ^ 21 - ((1391 / 790) : ℂ) * ζ ^ 22 - ((578 / 395) : ℂ) * ζ ^ 25 - ((182 / 395) : ℂ) * ζ ^ 27 - ((181 / 158) : ℂ) * ζ ^ 28 + ((4 / 395) : ℂ) * ζ ^ 29 + ((696 / 395) : ℂ) * ζ ^ 30 - ((828 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep04CoefficientIdentity00 :
    row18_reducedY22_combinationStep04Coefficient00 =
      row18_reducedY22_combinationStep03Coefficient00 +
        row18_reducedY22_combinationStep04Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep04Coefficient00 row18_reducedY22_combinationStep03Coefficient00 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 (-((2474 / 6241) : ℂ) + ((6163 / 12482) : ℂ) * ζ ^ 1 + ((3250 / 6241) : ℂ) * ζ ^ 2 - ((1919 / 6241) : ℂ) * ζ ^ 3 + ((7587 / 12482) : ℂ) * ζ ^ 4 - ((3018 / 6241) : ℂ) * ζ ^ 5 - ((1520 / 6241) : ℂ) * ζ ^ 6 + ((3459 / 6241) : ℂ) * ζ ^ 7 - ((315 / 12482) : ℂ) * ζ ^ 8 - ((1635 / 12482) : ℂ) * ζ ^ 9 + ((2433 / 12482) : ℂ) * ζ ^ 10 + ((203 / 12482) : ℂ) * ζ ^ 11 - ((1748 / 6241) : ℂ) * ζ ^ 12 + ((1205 / 6241) : ℂ) * ζ ^ 13 - ((837 / 12482) : ℂ) * ζ ^ 14 + ((894 / 6241) : ℂ) * ζ ^ 15 + ((247 / 12482) : ℂ) * ζ ^ 16 + ((163 / 6241) : ℂ) * ζ ^ 17 + ((1985 / 12482) : ℂ) * ζ ^ 18 - ((1125 / 6241) : ℂ) * ζ ^ 19 + ((871 / 12482) : ℂ) * ζ ^ 20 + ((706 / 6241) : ℂ) * ζ ^ 21 - ((3236 / 6241) : ℂ) * ζ ^ 22 + ((2 / 79) : ℂ) * ζ ^ 23 - ((710 / 6241) : ℂ) * ζ ^ 24 + ((240 / 6241) : ℂ) * ζ ^ 25 + ((10525 / 12482) : ℂ) * ζ ^ 26 - ((162 / 6241) : ℂ) * ζ ^ 27 - ((3337 / 12482) : ℂ) * ζ ^ 28 - ((741 / 12482) : ℂ) * ζ ^ 29 + ((705 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep04Coefficient01 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep04CoefficientIdentity01 :
    row18_reducedY22_combinationStep04Coefficient01 =
      row18_reducedY22_combinationStep03Coefficient01 +
        row18_reducedY22_combinationStep04Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep04Coefficient01 row18_reducedY22_combinationStep03Coefficient01 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 (-((2719 / 12482) : ℂ) + ((390 / 6241) : ℂ) * ζ ^ 1 - ((1601 / 6241) : ℂ) * ζ ^ 2 - ((2752 / 6241) : ℂ) * ζ ^ 3 - ((518 / 6241) : ℂ) * ζ ^ 4 + ((676 / 6241) : ℂ) * ζ ^ 5 - ((1552 / 6241) : ℂ) * ζ ^ 6 + ((1011 / 6241) : ℂ) * ζ ^ 7 - ((495 / 6241) : ℂ) * ζ ^ 8 - ((1661 / 6241) : ℂ) * ζ ^ 9 + ((1017 / 6241) : ℂ) * ζ ^ 10 - ((893 / 12482) : ℂ) * ζ ^ 11 + ((1643 / 12482) : ℂ) * ζ ^ 12 + ((887 / 6241) : ℂ) * ζ ^ 13 - ((55 / 6241) : ℂ) * ζ ^ 14 - ((204 / 6241) : ℂ) * ζ ^ 15 - ((886 / 6241) : ℂ) * ζ ^ 16 + ((638 / 6241) : ℂ) * ζ ^ 17 + ((2889 / 12482) : ℂ) * ζ ^ 18 + ((2551 / 12482) : ℂ) * ζ ^ 19 + ((5915 / 12482) : ℂ) * ζ ^ 20 - ((4831 / 12482) : ℂ) * ζ ^ 21 - ((1303 / 6241) : ℂ) * ζ ^ 22 + ((594 / 6241) : ℂ) * ζ ^ 23 + ((2049 / 6241) : ℂ) * ζ ^ 24 + ((442 / 6241) : ℂ) * ζ ^ 25 + ((72 / 6241) : ℂ) * ζ ^ 26 - ((3541 / 12482) : ℂ) * ζ ^ 27 - ((889 / 12482) : ℂ) * ζ ^ 28 + ((425 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep04Coefficient02 : ℂ :=
  (-((491 / 237) : ℂ) - ((302 / 79) : ℂ) * ζ ^ 1 + ((611 / 474) : ℂ) * ζ ^ 2 + ((883 / 474) : ℂ) * ζ ^ 3 - ((475 / 79) : ℂ) * ζ ^ 5 - ((122 / 237) : ℂ) * ζ ^ 6 + ((281 / 237) : ℂ) * ζ ^ 8 + ((129 / 158) : ℂ) * ζ ^ 9 - ((1007 / 237) : ℂ) * ζ ^ 11 + ((285 / 158) : ℂ) * ζ ^ 12 + ((302 / 79) : ℂ) * ζ ^ 13 - ((883 / 474) : ℂ) * ζ ^ 15 + ((302 / 79) : ℂ) * ζ ^ 17 + ((371 / 474) : ℂ) * ζ ^ 18 + ((173 / 79) : ℂ) * ζ ^ 21 - ((611 / 474) : ℂ) * ζ ^ 22 - ((611 / 474) : ℂ) * ζ ^ 24 + ((173 / 79) : ℂ) * ζ ^ 25 + ((1007 / 237) : ℂ) * ζ ^ 27 - ((281 / 237) : ℂ) * ζ ^ 28 - ((302 / 79) : ℂ) * ζ ^ 29 + ((49 / 474) : ℂ) * ζ ^ 30 + ((1007 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep04CoefficientIdentity02 :
    row18_reducedY22_combinationStep04Coefficient02 =
      row18_reducedY22_combinationStep03Coefficient02 +
        row18_reducedY22_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep04Coefficient02 row18_reducedY22_combinationStep03Coefficient02 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep04Coefficient03 : ℂ :=
  (((112 / 237) : ℂ) + ((422 / 237) : ℂ) * ζ ^ 1 - ((175 / 474) : ℂ) * ζ ^ 2 - ((703 / 474) : ℂ) * ζ ^ 3 + ((278 / 237) : ℂ) * ζ ^ 5 + ((455 / 237) : ℂ) * ζ ^ 6 - ((116 / 237) : ℂ) * ζ ^ 8 - ((58 / 79) : ℂ) * ζ ^ 9 + ((355 / 474) : ℂ) * ζ ^ 11 - ((116 / 237) : ℂ) * ζ ^ 12 - ((422 / 237) : ℂ) * ζ ^ 13 + ((415 / 474) : ℂ) * ζ ^ 15 - ((422 / 237) : ℂ) * ζ ^ 17 - ((1085 / 474) : ℂ) * ζ ^ 18 - ((47 / 158) : ℂ) * ζ ^ 21 + ((175 / 474) : ℂ) * ζ ^ 22 + ((48 / 79) : ℂ) * ζ ^ 25 + ((47 / 158) : ℂ) * ζ ^ 27 + ((116 / 237) : ℂ) * ζ ^ 28 + ((422 / 237) : ℂ) * ζ ^ 29 + ((455 / 474) : ℂ) * ζ ^ 30 - ((355 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep04CoefficientIdentity03 :
    row18_reducedY22_combinationStep04Coefficient03 =
      row18_reducedY22_combinationStep03Coefficient03 +
        row18_reducedY22_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep04Coefficient03 row18_reducedY22_combinationStep03Coefficient03 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep04Coefficient04 : ℂ :=
  (((2945 / 12482) : ℂ) - ((45043 / 93615) : ℂ) * ζ ^ 1 - ((182167 / 187230) : ℂ) * ζ ^ 2 + ((39903 / 62410) : ℂ) * ζ ^ 3 - ((103604 / 93615) : ℂ) * ζ ^ 5 - ((284434 / 93615) : ℂ) * ζ ^ 6 - ((27371 / 18723) : ℂ) * ζ ^ 8 - ((144484 / 93615) : ℂ) * ζ ^ 9 - ((408677 / 187230) : ℂ) * ζ ^ 11 - ((27371 / 18723) : ℂ) * ζ ^ 12 + ((45043 / 93615) : ℂ) * ζ ^ 13 - ((236831 / 187230) : ℂ) * ζ ^ 15 + ((45043 / 93615) : ℂ) * ζ ^ 17 + ((386701 / 187230) : ℂ) * ζ ^ 18 - ((29623 / 187230) : ℂ) * ζ ^ 21 + ((182167 / 187230) : ℂ) * ζ ^ 22 + ((58561 / 93615) : ℂ) * ζ ^ 25 + ((29623 / 187230) : ℂ) * ζ ^ 27 + ((27371 / 18723) : ℂ) * ζ ^ 28 - ((45043 / 93615) : ℂ) * ζ ^ 29 - ((142217 / 93615) : ℂ) * ζ ^ 30 + ((408677 / 187230) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep04CoefficientIdentity04 :
    row18_reducedY22_combinationStep04Coefficient04 =
      row18_reducedY22_combinationStep03Coefficient04 +
        row18_reducedY22_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep04Coefficient04 row18_reducedY22_combinationStep03Coefficient04 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep04Coefficient05 : ℂ :=
  (-((19921 / 37446) : ℂ) - ((89 / 37446) : ℂ) * ζ ^ 1 - ((31622 / 18723) : ℂ) * ζ ^ 2 - ((12463 / 12482) : ℂ) * ζ ^ 5 - ((14441 / 12482) : ℂ) * ζ ^ 6 - ((14441 / 12482) : ℂ) * ζ ^ 8 - ((12463 / 12482) : ℂ) * ζ ^ 9 - ((10313 / 6241) : ℂ) * ζ ^ 11 - ((13673 / 18723) : ℂ) * ζ ^ 12 + ((89 / 37446) : ℂ) * ζ ^ 13 - ((17109 / 12482) : ℂ) * ζ ^ 15 + ((89 / 37446) : ℂ) * ζ ^ 17 + ((11565 / 12482) : ℂ) * ζ ^ 18 + ((18739 / 37446) : ℂ) * ζ ^ 21 + ((31622 / 18723) : ℂ) * ζ ^ 22 + ((1438 / 6241) : ℂ) * ζ ^ 24 + ((18650 / 18723) : ℂ) * ζ ^ 25 + ((17109 / 12482) : ℂ) * ζ ^ 27 + ((14441 / 12482) : ℂ) * ζ ^ 28 - ((89 / 37446) : ℂ) * ζ ^ 29 - ((15977 / 37446) : ℂ) * ζ ^ 30 + ((10313 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep04CoefficientIdentity05 :
    row18_reducedY22_combinationStep04Coefficient05 =
      row18_reducedY22_combinationStep03Coefficient05 +
        row18_reducedY22_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep04Coefficient05 row18_reducedY22_combinationStep03Coefficient05 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep04Coefficient06 : ℂ :=
  (-((13834 / 93615) : ℂ) + ((130777 / 37446) : ℂ) * ζ ^ 1 + ((258317 / 93615) : ℂ) * ζ ^ 2 + ((31236 / 31205) : ℂ) * ζ ^ 3 - ((28157 / 93615) : ℂ) * ζ ^ 6 + ((56209 / 31205) : ℂ) * ζ ^ 8 + ((65795 / 37446) : ℂ) * ζ ^ 9 - ((427763 / 187230) : ℂ) * ζ ^ 11 - ((286474 / 93615) : ℂ) * ζ ^ 12 - ((130777 / 37446) : ℂ) * ζ ^ 13 + ((31236 / 31205) : ℂ) * ζ ^ 15 - ((130777 / 37446) : ℂ) * ζ ^ 17 - ((90717 / 31205) : ℂ) * ζ ^ 18 - ((130777 / 37446) : ℂ) * ζ ^ 21 - ((258317 / 93615) : ℂ) * ζ ^ 22 + ((258317 / 93615) : ℂ) * ζ ^ 24 + ((130777 / 37446) : ℂ) * ζ ^ 25 - ((427763 / 187230) : ℂ) * ζ ^ 27 - ((56209 / 31205) : ℂ) * ζ ^ 28 + ((130777 / 37446) : ℂ) * ζ ^ 29 + ((426944 / 93615) : ℂ) * ζ ^ 30 + ((427763 / 187230) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep04CoefficientIdentity06 :
    row18_reducedY22_combinationStep04Coefficient06 =
      row18_reducedY22_combinationStep03Coefficient06 +
        row18_reducedY22_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep04Coefficient06 row18_reducedY22_combinationStep03Coefficient06 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep04Coefficient07 : ℂ :=
  (-((75353 / 37446) : ℂ) - ((10069 / 6241) : ℂ) * ζ ^ 1 - ((3363 / 6241) : ℂ) * ζ ^ 2 + ((67477 / 37446) : ℂ) * ζ ^ 3 - ((53153 / 37446) : ℂ) * ζ ^ 5 - ((14855 / 6241) : ℂ) * ζ ^ 6 + ((15679 / 18723) : ℂ) * ζ ^ 8 + ((46939 / 37446) : ℂ) * ζ ^ 9 - ((3423 / 6241) : ℂ) * ζ ^ 11 + ((15679 / 18723) : ℂ) * ζ ^ 12 + ((10069 / 6241) : ℂ) * ζ ^ 13 - ((10036 / 6241) : ℂ) * ζ ^ 15 + ((10069 / 6241) : ℂ) * ζ ^ 17 + ((11492 / 6241) : ℂ) * ζ ^ 18 - ((7063 / 37446) : ℂ) * ζ ^ 21 + ((3363 / 6241) : ℂ) * ζ ^ 22 - ((7261 / 37446) : ℂ) * ζ ^ 25 + ((7063 / 37446) : ℂ) * ζ ^ 27 - ((15679 / 18723) : ℂ) * ζ ^ 28 - ((10069 / 6241) : ℂ) * ζ ^ 29 - ((14855 / 12482) : ℂ) * ζ ^ 30 + ((3423 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep04CoefficientIdentity07 :
    row18_reducedY22_combinationStep04Coefficient07 =
      row18_reducedY22_combinationStep03Coefficient07 +
        row18_reducedY22_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep04Coefficient07 row18_reducedY22_combinationStep03Coefficient07 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep04Coefficient08 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep04CoefficientIdentity08 :
    row18_reducedY22_combinationStep04Coefficient08 =
      row18_reducedY22_combinationStep03Coefficient08 +
        row18_reducedY22_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep04Coefficient08 row18_reducedY22_combinationStep03Coefficient08 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep04Coefficient09 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep04CoefficientIdentity09 :
    row18_reducedY22_combinationStep04Coefficient09 =
      row18_reducedY22_combinationStep03Coefficient09 +
        row18_reducedY22_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep04Coefficient09 row18_reducedY22_combinationStep03Coefficient09 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep04Coefficient10 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep04CoefficientIdentity10 :
    row18_reducedY22_combinationStep04Coefficient10 =
      row18_reducedY22_combinationStep03Coefficient10 +
        row18_reducedY22_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep04Coefficient10 row18_reducedY22_combinationStep03Coefficient10 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep04Coefficient11 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep04CoefficientIdentity11 :
    row18_reducedY22_combinationStep04Coefficient11 =
      row18_reducedY22_combinationStep03Coefficient11 +
        row18_reducedY22_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep04Coefficient11 row18_reducedY22_combinationStep03Coefficient11 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep04Coefficient12 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep04CoefficientIdentity12 :
    row18_reducedY22_combinationStep04Coefficient12 =
      row18_reducedY22_combinationStep03Coefficient12 +
        row18_reducedY22_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep04Coefficient12 row18_reducedY22_combinationStep03Coefficient12 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep04Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep04CoefficientIdentity13 :
    row18_reducedY22_combinationStep04Coefficient13 =
      row18_reducedY22_combinationStep03Coefficient13 +
        row18_reducedY22_combinationStep04Multiplier *
          (-((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((73 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((105 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((73 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep04Coefficient13 row18_reducedY22_combinationStep03Coefficient13 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 (-((3276 / 6241) : ℂ) - ((625 / 12482) : ℂ) * ζ ^ 1 + ((689 / 6241) : ℂ) * ζ ^ 2 - ((3167 / 12482) : ℂ) * ζ ^ 3 - ((1285 / 12482) : ℂ) * ζ ^ 4 - ((117 / 6241) : ℂ) * ζ ^ 5 + ((5201 / 12482) : ℂ) * ζ ^ 6 + ((3018 / 6241) : ℂ) * ζ ^ 7 + ((4811 / 12482) : ℂ) * ζ ^ 8 - ((784 / 6241) : ℂ) * ζ ^ 9 - ((8487 / 6241) : ℂ) * ζ ^ 10 - ((4803 / 12482) : ℂ) * ζ ^ 11 + ((6691 / 12482) : ℂ) * ζ ^ 12 + ((178 / 6241) : ℂ) * ζ ^ 13 + ((6775 / 6241) : ℂ) * ζ ^ 14 - ((4021 / 12482) : ℂ) * ζ ^ 15 - ((19101 / 12482) : ℂ) * ζ ^ 16 - ((4973 / 12482) : ℂ) * ζ ^ 17 - ((4376 / 6241) : ℂ) * ζ ^ 18 + ((66 / 6241) : ℂ) * ζ ^ 19 + ((8447 / 12482) : ℂ) * ζ ^ 20 + ((551 / 6241) : ℂ) * ζ ^ 21 - ((119 / 6241) : ℂ) * ζ ^ 22 + ((550 / 6241) : ℂ) * ζ ^ 23 - ((2929 / 12482) : ℂ) * ζ ^ 24 + ((445 / 12482) : ℂ) * ζ ^ 25 + ((1398 / 6241) : ℂ) * ζ ^ 26 + ((1144 / 6241) : ℂ) * ζ ^ 27 + ((2973 / 12482) : ℂ) * ζ ^ 28 + ((1083 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep04Coefficient14 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep04CoefficientIdentity14 :
    row18_reducedY22_combinationStep04Coefficient14 =
      row18_reducedY22_combinationStep03Coefficient14 +
        row18_reducedY22_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep04Coefficient14 row18_reducedY22_combinationStep03Coefficient14 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep04Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep04CoefficientIdentity15 :
    row18_reducedY22_combinationStep04Coefficient15 =
      row18_reducedY22_combinationStep03Coefficient15 +
        row18_reducedY22_combinationStep04Multiplier *
          (((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep04Coefficient15 row18_reducedY22_combinationStep03Coefficient15 row18_reducedY22_combinationStep04Multiplier
  close_cyclotomic_row18 (((2474 / 6241) : ℂ) - ((6163 / 12482) : ℂ) * ζ ^ 1 - ((3250 / 6241) : ℂ) * ζ ^ 2 + ((1919 / 6241) : ℂ) * ζ ^ 3 - ((7587 / 12482) : ℂ) * ζ ^ 4 + ((3018 / 6241) : ℂ) * ζ ^ 5 + ((1520 / 6241) : ℂ) * ζ ^ 6 - ((3459 / 6241) : ℂ) * ζ ^ 7 + ((315 / 12482) : ℂ) * ζ ^ 8 + ((1635 / 12482) : ℂ) * ζ ^ 9 - ((2433 / 12482) : ℂ) * ζ ^ 10 - ((203 / 12482) : ℂ) * ζ ^ 11 + ((1748 / 6241) : ℂ) * ζ ^ 12 - ((1205 / 6241) : ℂ) * ζ ^ 13 + ((837 / 12482) : ℂ) * ζ ^ 14 - ((894 / 6241) : ℂ) * ζ ^ 15 - ((247 / 12482) : ℂ) * ζ ^ 16 - ((163 / 6241) : ℂ) * ζ ^ 17 - ((1985 / 12482) : ℂ) * ζ ^ 18 + ((1125 / 6241) : ℂ) * ζ ^ 19 - ((871 / 12482) : ℂ) * ζ ^ 20 - ((706 / 6241) : ℂ) * ζ ^ 21 + ((3236 / 6241) : ℂ) * ζ ^ 22 - ((2 / 79) : ℂ) * ζ ^ 23 + ((710 / 6241) : ℂ) * ζ ^ 24 - ((240 / 6241) : ℂ) * ζ ^ 25 - ((10525 / 12482) : ℂ) * ζ ^ 26 + ((162 / 6241) : ℂ) * ζ ^ 27 + ((3337 / 12482) : ℂ) * ζ ^ 28 + ((741 / 12482) : ℂ) * ζ ^ 29 - ((705 / 12482) : ℂ) * ζ ^ 30)

private theorem row18_reducedY22_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY22_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY22_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY22_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY22_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY22_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY22_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY22_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY22_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY22_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY22_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY22_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY22_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY22_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY22_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY22_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY22_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY22_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation07
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY22_combinationStep04CoefficientIdentity00,
      row18_reducedY22_combinationStep04CoefficientIdentity01,
      row18_reducedY22_combinationStep04CoefficientIdentity02,
      row18_reducedY22_combinationStep04CoefficientIdentity03,
      row18_reducedY22_combinationStep04CoefficientIdentity04,
      row18_reducedY22_combinationStep04CoefficientIdentity05,
      row18_reducedY22_combinationStep04CoefficientIdentity06,
      row18_reducedY22_combinationStep04CoefficientIdentity07,
      row18_reducedY22_combinationStep04CoefficientIdentity08,
      row18_reducedY22_combinationStep04CoefficientIdentity09,
      row18_reducedY22_combinationStep04CoefficientIdentity10,
      row18_reducedY22_combinationStep04CoefficientIdentity11,
      row18_reducedY22_combinationStep04CoefficientIdentity12,
      row18_reducedY22_combinationStep04CoefficientIdentity13,
      row18_reducedY22_combinationStep04CoefficientIdentity14,
      row18_reducedY22_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY22_combinationStep04Multiplier * equation

private def row18_reducedY22_combinationStep05Multiplier : ℂ :=
  (((2878 / 1185) : ℂ) + ((384 / 395) : ℂ) * ζ ^ 1 + ((2324 / 1185) : ℂ) * ζ ^ 2 - ((1160 / 237) : ℂ) * ζ ^ 3 + ((956 / 1185) : ℂ) * ζ ^ 5 + ((1082 / 395) : ℂ) * ζ ^ 6 - ((1624 / 1185) : ℂ) * ζ ^ 8 - ((674 / 1185) : ℂ) * ζ ^ 9 + ((84 / 79) : ℂ) * ζ ^ 11 - ((922 / 1185) : ℂ) * ζ ^ 12 - ((384 / 395) : ℂ) * ζ ^ 13 + ((1160 / 237) : ℂ) * ζ ^ 15 - ((384 / 395) : ℂ) * ζ ^ 17 - ((1734 / 395) : ℂ) * ζ ^ 18 + ((196 / 1185) : ℂ) * ζ ^ 21 - ((2324 / 1185) : ℂ) * ζ ^ 22 - ((2324 / 1185) : ℂ) * ζ ^ 24 + ((196 / 1185) : ℂ) * ζ ^ 25 - ((84 / 79) : ℂ) * ζ ^ 27 + ((1624 / 1185) : ℂ) * ζ ^ 28 + ((384 / 395) : ℂ) * ζ ^ 29 + ((1316 / 395) : ℂ) * ζ ^ 30 - ((84 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY22_combinationStep05Coefficient00 : ℂ :=
  (((136 / 79) : ℂ) + ((4 / 395) : ℂ) * ζ ^ 1 + ((1391 / 790) : ℂ) * ζ ^ 2 - ((186 / 395) : ℂ) * ζ ^ 3 + ((582 / 395) : ℂ) * ζ ^ 5 + ((1392 / 395) : ℂ) * ζ ^ 6 + ((181 / 158) : ℂ) * ζ ^ 8 + ((642 / 395) : ℂ) * ζ ^ 9 + ((828 / 395) : ℂ) * ζ ^ 11 + ((181 / 158) : ℂ) * ζ ^ 12 - ((4 / 395) : ℂ) * ζ ^ 13 + ((764 / 395) : ℂ) * ζ ^ 15 - ((4 / 395) : ℂ) * ζ ^ 17 - ((1393 / 790) : ℂ) * ζ ^ 18 + ((182 / 395) : ℂ) * ζ ^ 21 - ((1391 / 790) : ℂ) * ζ ^ 22 - ((578 / 395) : ℂ) * ζ ^ 25 - ((182 / 395) : ℂ) * ζ ^ 27 - ((181 / 158) : ℂ) * ζ ^ 28 + ((4 / 395) : ℂ) * ζ ^ 29 + ((696 / 395) : ℂ) * ζ ^ 30 - ((828 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep05CoefficientIdentity00 :
    row18_reducedY22_combinationStep05Coefficient00 =
      row18_reducedY22_combinationStep04Coefficient00 +
        row18_reducedY22_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep05Coefficient00 row18_reducedY22_combinationStep04Coefficient00 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep05Coefficient01 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep05CoefficientIdentity01 :
    row18_reducedY22_combinationStep05Coefficient01 =
      row18_reducedY22_combinationStep04Coefficient01 +
        row18_reducedY22_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep05Coefficient01 row18_reducedY22_combinationStep04Coefficient01 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep05Coefficient02 : ℂ :=
  (-((142112 / 93615) : ℂ) - ((89713 / 37446) : ℂ) * ζ ^ 1 + ((102733 / 187230) : ℂ) * ζ ^ 2 + ((101209 / 37446) : ℂ) * ζ ^ 3 - ((89573 / 18723) : ℂ) * ζ ^ 5 + ((7597 / 187230) : ℂ) * ζ ^ 6 + ((33277 / 31205) : ℂ) * ζ ^ 8 + ((70 / 18723) : ℂ) * ζ ^ 9 - ((91400 / 18723) : ℂ) * ζ ^ 11 + ((15856 / 31205) : ℂ) * ζ ^ 12 + ((89713 / 37446) : ℂ) * ζ ^ 13 - ((101209 / 37446) : ℂ) * ζ ^ 15 + ((89713 / 37446) : ℂ) * ζ ^ 17 + ((60497 / 62410) : ℂ) * ζ ^ 18 + ((29811 / 12482) : ℂ) * ζ ^ 21 - ((102733 / 187230) : ℂ) * ζ ^ 22 - ((102733 / 187230) : ℂ) * ζ ^ 24 + ((29811 / 12482) : ℂ) * ζ ^ 25 + ((91400 / 18723) : ℂ) * ζ ^ 27 - ((33277 / 31205) : ℂ) * ζ ^ 28 - ((89713 / 37446) : ℂ) * ζ ^ 29 - ((96929 / 187230) : ℂ) * ζ ^ 30 + ((91400 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep05CoefficientIdentity02 :
    row18_reducedY22_combinationStep05Coefficient02 =
      row18_reducedY22_combinationStep04Coefficient02 +
        row18_reducedY22_combinationStep05Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep05Coefficient02 row18_reducedY22_combinationStep04Coefficient02 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 (-((60467 / 93615) : ℂ) - ((43043 / 31205) : ℂ) * ζ ^ 1 + ((8689 / 187230) : ℂ) * ζ ^ 2 - ((5192 / 6241) : ℂ) * ζ ^ 3 - ((4292 / 93615) : ℂ) * ζ ^ 4 + ((48797 / 37446) : ℂ) * ζ ^ 5 - ((94838 / 93615) : ℂ) * ζ ^ 6 + ((92473 / 187230) : ℂ) * ζ ^ 7 - ((4677 / 31205) : ℂ) * ζ ^ 8 + ((223 / 18723) : ℂ) * ζ ^ 9 + ((55933 / 37446) : ℂ) * ζ ^ 10 - ((27253 / 37446) : ℂ) * ζ ^ 11 + ((18667 / 18723) : ℂ) * ζ ^ 12 - ((8267 / 62410) : ℂ) * ζ ^ 13 - ((26159 / 62410) : ℂ) * ζ ^ 14 - ((18019 / 187230) : ℂ) * ζ ^ 15 - ((159527 / 93615) : ℂ) * ζ ^ 16 - ((17171 / 93615) : ℂ) * ζ ^ 17 - ((7648 / 93615) : ℂ) * ζ ^ 18 - ((17116 / 93615) : ℂ) * ζ ^ 19 + ((38988 / 31205) : ℂ) * ζ ^ 20 - ((8078 / 31205) : ℂ) * ζ ^ 21 + ((56348 / 93615) : ℂ) * ζ ^ 22 + ((4679 / 31205) : ℂ) * ζ ^ 23 - ((498 / 6241) : ℂ) * ζ ^ 24 - ((6601 / 93615) : ℂ) * ζ ^ 25 - ((41968 / 93615) : ℂ) * ζ ^ 26 + ((22958 / 93615) : ℂ) * ζ ^ 27 - ((1015 / 6241) : ℂ) * ζ ^ 28 + ((6286 / 31205) : ℂ) * ζ ^ 29 - ((294 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep05Coefficient03 : ℂ :=
  (((53549 / 37446) : ℂ) + ((8173 / 6241) : ℂ) * ζ ^ 1 + ((5225 / 12482) : ℂ) * ζ ^ 2 - ((24614 / 18723) : ℂ) * ζ ^ 3 + ((28828 / 18723) : ℂ) * ζ ^ 5 + ((15013 / 6241) : ℂ) * ζ ^ 6 - ((30173 / 37446) : ℂ) * ζ ^ 8 - ((12212 / 18723) : ℂ) * ζ ^ 9 + ((4134 / 6241) : ℂ) * ζ ^ 11 - ((30173 / 37446) : ℂ) * ζ ^ 12 - ((8173 / 6241) : ℂ) * ζ ^ 13 + ((9641 / 6241) : ℂ) * ζ ^ 15 - ((8173 / 6241) : ℂ) * ζ ^ 17 - ((24801 / 12482) : ℂ) * ζ ^ 18 + ((95 / 18723) : ℂ) * ζ ^ 21 - ((5225 / 12482) : ℂ) * ζ ^ 22 - ((4309 / 18723) : ℂ) * ζ ^ 25 - ((95 / 18723) : ℂ) * ζ ^ 27 + ((30173 / 37446) : ℂ) * ζ ^ 28 + ((8173 / 6241) : ℂ) * ζ ^ 29 + ((15013 / 12482) : ℂ) * ζ ^ 30 - ((4134 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep05CoefficientIdentity03 :
    row18_reducedY22_combinationStep05Coefficient03 =
      row18_reducedY22_combinationStep04Coefficient03 +
        row18_reducedY22_combinationStep05Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep05Coefficient03 row18_reducedY22_combinationStep04Coefficient03 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 (-((13329 / 31205) : ℂ) + ((1873 / 62410) : ℂ) * ζ ^ 1 - ((103331 / 187230) : ℂ) * ζ ^ 2 - ((95939 / 62410) : ℂ) * ζ ^ 3 + ((175954 / 93615) : ℂ) * ζ ^ 4 - ((15950 / 18723) : ℂ) * ζ ^ 5 + ((7163 / 18723) : ℂ) * ζ ^ 6 + ((50161 / 93615) : ℂ) * ζ ^ 7 - ((48391 / 93615) : ℂ) * ζ ^ 8 + ((41656 / 93615) : ℂ) * ζ ^ 9 - ((132599 / 187230) : ℂ) * ζ ^ 10 + ((14080 / 18723) : ℂ) * ζ ^ 11 - ((30003 / 31205) : ℂ) * ζ ^ 12 - ((35651 / 187230) : ℂ) * ζ ^ 13 + ((14288 / 93615) : ℂ) * ζ ^ 14 - ((23371 / 37446) : ℂ) * ζ ^ 15 - ((2094 / 6241) : ℂ) * ζ ^ 16 - ((7043 / 12482) : ℂ) * ζ ^ 17 - ((4292 / 31205) : ℂ) * ζ ^ 18 + ((32209 / 18723) : ℂ) * ζ ^ 19 - ((70499 / 93615) : ℂ) * ζ ^ 20 + ((99742 / 93615) : ℂ) * ζ ^ 21 + ((7484 / 93615) : ℂ) * ζ ^ 22 + ((23921 / 93615) : ℂ) * ζ ^ 23 - ((22433 / 93615) : ℂ) * ζ ^ 24 - ((16981 / 93615) : ℂ) * ζ ^ 25 + ((4794 / 6241) : ℂ) * ζ ^ 26 - ((17527 / 18723) : ℂ) * ζ ^ 27 + ((27939 / 31205) : ℂ) * ζ ^ 28 - ((1393 / 31205) : ℂ) * ζ ^ 29 - ((273 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep05Coefficient04 : ℂ :=
  (-((57 / 79) : ℂ) - ((4 / 395) : ℂ) * ζ ^ 1 - ((1391 / 790) : ℂ) * ζ ^ 2 + ((186 / 395) : ℂ) * ζ ^ 3 - ((582 / 395) : ℂ) * ζ ^ 5 - ((1392 / 395) : ℂ) * ζ ^ 6 - ((181 / 158) : ℂ) * ζ ^ 8 - ((642 / 395) : ℂ) * ζ ^ 9 - ((828 / 395) : ℂ) * ζ ^ 11 - ((181 / 158) : ℂ) * ζ ^ 12 + ((4 / 395) : ℂ) * ζ ^ 13 - ((764 / 395) : ℂ) * ζ ^ 15 + ((4 / 395) : ℂ) * ζ ^ 17 + ((1393 / 790) : ℂ) * ζ ^ 18 - ((182 / 395) : ℂ) * ζ ^ 21 + ((1391 / 790) : ℂ) * ζ ^ 22 + ((578 / 395) : ℂ) * ζ ^ 25 + ((182 / 395) : ℂ) * ζ ^ 27 + ((181 / 158) : ℂ) * ζ ^ 28 - ((4 / 395) : ℂ) * ζ ^ 29 - ((696 / 395) : ℂ) * ζ ^ 30 + ((828 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep05CoefficientIdentity04 :
    row18_reducedY22_combinationStep05Coefficient04 =
      row18_reducedY22_combinationStep04Coefficient04 +
        row18_reducedY22_combinationStep05Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep05Coefficient04 row18_reducedY22_combinationStep04Coefficient04 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 (((13329 / 31205) : ℂ) - ((1873 / 62410) : ℂ) * ζ ^ 1 + ((103331 / 187230) : ℂ) * ζ ^ 2 + ((95939 / 62410) : ℂ) * ζ ^ 3 - ((175954 / 93615) : ℂ) * ζ ^ 4 + ((15950 / 18723) : ℂ) * ζ ^ 5 - ((7163 / 18723) : ℂ) * ζ ^ 6 - ((50161 / 93615) : ℂ) * ζ ^ 7 + ((48391 / 93615) : ℂ) * ζ ^ 8 - ((41656 / 93615) : ℂ) * ζ ^ 9 + ((132599 / 187230) : ℂ) * ζ ^ 10 - ((14080 / 18723) : ℂ) * ζ ^ 11 + ((30003 / 31205) : ℂ) * ζ ^ 12 + ((35651 / 187230) : ℂ) * ζ ^ 13 - ((14288 / 93615) : ℂ) * ζ ^ 14 + ((23371 / 37446) : ℂ) * ζ ^ 15 + ((2094 / 6241) : ℂ) * ζ ^ 16 + ((7043 / 12482) : ℂ) * ζ ^ 17 + ((4292 / 31205) : ℂ) * ζ ^ 18 - ((32209 / 18723) : ℂ) * ζ ^ 19 + ((70499 / 93615) : ℂ) * ζ ^ 20 - ((99742 / 93615) : ℂ) * ζ ^ 21 - ((7484 / 93615) : ℂ) * ζ ^ 22 - ((23921 / 93615) : ℂ) * ζ ^ 23 + ((22433 / 93615) : ℂ) * ζ ^ 24 + ((16981 / 93615) : ℂ) * ζ ^ 25 - ((4794 / 6241) : ℂ) * ζ ^ 26 + ((17527 / 18723) : ℂ) * ζ ^ 27 - ((27939 / 31205) : ℂ) * ζ ^ 28 + ((1393 / 31205) : ℂ) * ζ ^ 29 + ((273 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep05Coefficient05 : ℂ :=
  (-((19921 / 37446) : ℂ) - ((89 / 37446) : ℂ) * ζ ^ 1 - ((31622 / 18723) : ℂ) * ζ ^ 2 - ((12463 / 12482) : ℂ) * ζ ^ 5 - ((14441 / 12482) : ℂ) * ζ ^ 6 - ((14441 / 12482) : ℂ) * ζ ^ 8 - ((12463 / 12482) : ℂ) * ζ ^ 9 - ((10313 / 6241) : ℂ) * ζ ^ 11 - ((13673 / 18723) : ℂ) * ζ ^ 12 + ((89 / 37446) : ℂ) * ζ ^ 13 - ((17109 / 12482) : ℂ) * ζ ^ 15 + ((89 / 37446) : ℂ) * ζ ^ 17 + ((11565 / 12482) : ℂ) * ζ ^ 18 + ((18739 / 37446) : ℂ) * ζ ^ 21 + ((31622 / 18723) : ℂ) * ζ ^ 22 + ((1438 / 6241) : ℂ) * ζ ^ 24 + ((18650 / 18723) : ℂ) * ζ ^ 25 + ((17109 / 12482) : ℂ) * ζ ^ 27 + ((14441 / 12482) : ℂ) * ζ ^ 28 - ((89 / 37446) : ℂ) * ζ ^ 29 - ((15977 / 37446) : ℂ) * ζ ^ 30 + ((10313 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep05CoefficientIdentity05 :
    row18_reducedY22_combinationStep05Coefficient05 =
      row18_reducedY22_combinationStep04Coefficient05 +
        row18_reducedY22_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep05Coefficient05 row18_reducedY22_combinationStep04Coefficient05 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep05Coefficient06 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep05CoefficientIdentity06 :
    row18_reducedY22_combinationStep05Coefficient06 =
      row18_reducedY22_combinationStep04Coefficient06 +
        row18_reducedY22_combinationStep05Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep05Coefficient06 row18_reducedY22_combinationStep04Coefficient06 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 (-((12286 / 31205) : ℂ) + ((55343 / 18723) : ℂ) * ζ ^ 1 + ((232207 / 187230) : ℂ) * ζ ^ 2 + ((238961 / 187230) : ℂ) * ζ ^ 3 + ((11023 / 18723) : ℂ) * ζ ^ 4 - ((94087 / 93615) : ℂ) * ζ ^ 5 - ((215817 / 62410) : ℂ) * ζ ^ 6 - ((17219 / 6241) : ℂ) * ζ ^ 7 + ((23297 / 12482) : ℂ) * ζ ^ 8 + ((111001 / 37446) : ℂ) * ζ ^ 9 + ((347134 / 93615) : ℂ) * ζ ^ 10 - ((109618 / 93615) : ℂ) * ζ ^ 11 - ((64777 / 18723) : ℂ) * ζ ^ 12 - ((79133 / 31205) : ℂ) * ζ ^ 13 - ((148831 / 93615) : ℂ) * ζ ^ 14 + ((19757 / 12482) : ℂ) * ζ ^ 15 + ((38416 / 31205) : ℂ) * ζ ^ 16 + ((4693 / 93615) : ℂ) * ζ ^ 17 + ((116299 / 93615) : ℂ) * ζ ^ 18 - ((3683 / 6241) : ℂ) * ζ ^ 19 + ((40879 / 93615) : ℂ) * ζ ^ 20 - ((26644 / 18723) : ℂ) * ζ ^ 21 - ((147 / 6241) : ℂ) * ζ ^ 22 + ((204662 / 93615) : ℂ) * ζ ^ 23 + ((10237 / 18723) : ℂ) * ζ ^ 24 + ((44432 / 31205) : ℂ) * ζ ^ 25 - ((26738 / 31205) : ℂ) * ζ ^ 26 - ((70759 / 93615) : ℂ) * ζ ^ 27 - ((4599 / 31205) : ℂ) * ζ ^ 28 - ((6692 / 31205) : ℂ) * ζ ^ 29 + ((588 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep05Coefficient07 : ℂ :=
  (-((75353 / 37446) : ℂ) - ((10069 / 6241) : ℂ) * ζ ^ 1 - ((3363 / 6241) : ℂ) * ζ ^ 2 + ((67477 / 37446) : ℂ) * ζ ^ 3 - ((53153 / 37446) : ℂ) * ζ ^ 5 - ((14855 / 6241) : ℂ) * ζ ^ 6 + ((15679 / 18723) : ℂ) * ζ ^ 8 + ((46939 / 37446) : ℂ) * ζ ^ 9 - ((3423 / 6241) : ℂ) * ζ ^ 11 + ((15679 / 18723) : ℂ) * ζ ^ 12 + ((10069 / 6241) : ℂ) * ζ ^ 13 - ((10036 / 6241) : ℂ) * ζ ^ 15 + ((10069 / 6241) : ℂ) * ζ ^ 17 + ((11492 / 6241) : ℂ) * ζ ^ 18 - ((7063 / 37446) : ℂ) * ζ ^ 21 + ((3363 / 6241) : ℂ) * ζ ^ 22 - ((7261 / 37446) : ℂ) * ζ ^ 25 + ((7063 / 37446) : ℂ) * ζ ^ 27 - ((15679 / 18723) : ℂ) * ζ ^ 28 - ((10069 / 6241) : ℂ) * ζ ^ 29 - ((14855 / 12482) : ℂ) * ζ ^ 30 + ((3423 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep05CoefficientIdentity07 :
    row18_reducedY22_combinationStep05Coefficient07 =
      row18_reducedY22_combinationStep04Coefficient07 +
        row18_reducedY22_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep05Coefficient07 row18_reducedY22_combinationStep04Coefficient07 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep05Coefficient08 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep05CoefficientIdentity08 :
    row18_reducedY22_combinationStep05Coefficient08 =
      row18_reducedY22_combinationStep04Coefficient08 +
        row18_reducedY22_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep05Coefficient08 row18_reducedY22_combinationStep04Coefficient08 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep05Coefficient09 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep05CoefficientIdentity09 :
    row18_reducedY22_combinationStep05Coefficient09 =
      row18_reducedY22_combinationStep04Coefficient09 +
        row18_reducedY22_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep05Coefficient09 row18_reducedY22_combinationStep04Coefficient09 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep05Coefficient10 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep05CoefficientIdentity10 :
    row18_reducedY22_combinationStep05Coefficient10 =
      row18_reducedY22_combinationStep04Coefficient10 +
        row18_reducedY22_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep05Coefficient10 row18_reducedY22_combinationStep04Coefficient10 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep05Coefficient11 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep05CoefficientIdentity11 :
    row18_reducedY22_combinationStep05Coefficient11 =
      row18_reducedY22_combinationStep04Coefficient11 +
        row18_reducedY22_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep05Coefficient11 row18_reducedY22_combinationStep04Coefficient11 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep05Coefficient12 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep05CoefficientIdentity12 :
    row18_reducedY22_combinationStep05Coefficient12 =
      row18_reducedY22_combinationStep04Coefficient12 +
        row18_reducedY22_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep05Coefficient12 row18_reducedY22_combinationStep04Coefficient12 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep05Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep05CoefficientIdentity13 :
    row18_reducedY22_combinationStep05Coefficient13 =
      row18_reducedY22_combinationStep04Coefficient13 +
        row18_reducedY22_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep05Coefficient13 row18_reducedY22_combinationStep04Coefficient13 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep05Coefficient14 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep05CoefficientIdentity14 :
    row18_reducedY22_combinationStep05Coefficient14 =
      row18_reducedY22_combinationStep04Coefficient14 +
        row18_reducedY22_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep05Coefficient14 row18_reducedY22_combinationStep04Coefficient14 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep05Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep05CoefficientIdentity15 :
    row18_reducedY22_combinationStep05Coefficient15 =
      row18_reducedY22_combinationStep04Coefficient15 +
        row18_reducedY22_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep05Coefficient15 row18_reducedY22_combinationStep04Coefficient15 row18_reducedY22_combinationStep05Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY22_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY22_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY22_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY22_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY22_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY22_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY22_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY22_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY22_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY22_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY22_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY22_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY22_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY22_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY22_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY22_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY22_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY22_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY22_combinationStep05CoefficientIdentity00,
      row18_reducedY22_combinationStep05CoefficientIdentity01,
      row18_reducedY22_combinationStep05CoefficientIdentity02,
      row18_reducedY22_combinationStep05CoefficientIdentity03,
      row18_reducedY22_combinationStep05CoefficientIdentity04,
      row18_reducedY22_combinationStep05CoefficientIdentity05,
      row18_reducedY22_combinationStep05CoefficientIdentity06,
      row18_reducedY22_combinationStep05CoefficientIdentity07,
      row18_reducedY22_combinationStep05CoefficientIdentity08,
      row18_reducedY22_combinationStep05CoefficientIdentity09,
      row18_reducedY22_combinationStep05CoefficientIdentity10,
      row18_reducedY22_combinationStep05CoefficientIdentity11,
      row18_reducedY22_combinationStep05CoefficientIdentity12,
      row18_reducedY22_combinationStep05CoefficientIdentity13,
      row18_reducedY22_combinationStep05CoefficientIdentity14,
      row18_reducedY22_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY22_combinationStep05Multiplier * equation

private def row18_reducedY22_combinationStep06Multiplier : ℂ :=
  (((142 / 79) : ℂ) + ((194 / 79) : ℂ) * ζ ^ 1 - ((670 / 237) : ℂ) * ζ ^ 2 - ((674 / 237) : ℂ) * ζ ^ 3 + ((420 / 79) : ℂ) * ζ ^ 5 - ((152 / 79) : ℂ) * ζ ^ 8 + ((278 / 237) : ℂ) * ζ ^ 9 + ((132 / 79) : ℂ) * ζ ^ 11 - ((132 / 79) : ℂ) * ζ ^ 12 - ((194 / 79) : ℂ) * ζ ^ 13 - ((4 / 237) : ℂ) * ζ ^ 15 - ((194 / 79) : ℂ) * ζ ^ 17 + ((670 / 237) : ℂ) * ζ ^ 18 - ((1256 / 237) : ℂ) * ζ ^ 21 + ((670 / 237) : ℂ) * ζ ^ 22 + ((284 / 79) : ℂ) * ζ ^ 24 - ((226 / 79) : ℂ) * ζ ^ 25 - ((1256 / 237) : ℂ) * ζ ^ 27 + ((152 / 79) : ℂ) * ζ ^ 28 + ((194 / 79) : ℂ) * ζ ^ 29 + ((262 / 79) : ℂ) * ζ ^ 30 - ((132 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY22_combinationStep06Coefficient00 : ℂ :=
  (((136 / 79) : ℂ) + ((4 / 395) : ℂ) * ζ ^ 1 + ((1391 / 790) : ℂ) * ζ ^ 2 - ((186 / 395) : ℂ) * ζ ^ 3 + ((582 / 395) : ℂ) * ζ ^ 5 + ((1392 / 395) : ℂ) * ζ ^ 6 + ((181 / 158) : ℂ) * ζ ^ 8 + ((642 / 395) : ℂ) * ζ ^ 9 + ((828 / 395) : ℂ) * ζ ^ 11 + ((181 / 158) : ℂ) * ζ ^ 12 - ((4 / 395) : ℂ) * ζ ^ 13 + ((764 / 395) : ℂ) * ζ ^ 15 - ((4 / 395) : ℂ) * ζ ^ 17 - ((1393 / 790) : ℂ) * ζ ^ 18 + ((182 / 395) : ℂ) * ζ ^ 21 - ((1391 / 790) : ℂ) * ζ ^ 22 - ((578 / 395) : ℂ) * ζ ^ 25 - ((182 / 395) : ℂ) * ζ ^ 27 - ((181 / 158) : ℂ) * ζ ^ 28 + ((4 / 395) : ℂ) * ζ ^ 29 + ((696 / 395) : ℂ) * ζ ^ 30 - ((828 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep06CoefficientIdentity00 :
    row18_reducedY22_combinationStep06Coefficient00 =
      row18_reducedY22_combinationStep05Coefficient00 +
        row18_reducedY22_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep06Coefficient00 row18_reducedY22_combinationStep05Coefficient00 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep06Coefficient01 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep06CoefficientIdentity01 :
    row18_reducedY22_combinationStep06Coefficient01 =
      row18_reducedY22_combinationStep05Coefficient01 +
        row18_reducedY22_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep06Coefficient01 row18_reducedY22_combinationStep05Coefficient01 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep06Coefficient02 : ℂ :=
  (((374 / 395) : ℂ) - ((74 / 79) : ℂ) * ζ ^ 1 - ((908 / 395) : ℂ) * ζ ^ 2 + ((21 / 79) : ℂ) * ζ ^ 3 - ((164 / 79) : ℂ) * ζ ^ 5 - ((397 / 395) : ℂ) * ζ ^ 6 - ((852 / 395) : ℂ) * ζ ^ 8 - ((8 / 79) : ℂ) * ζ ^ 9 - ((98 / 79) : ℂ) * ζ ^ 11 - ((511 / 395) : ℂ) * ζ ^ 12 + ((74 / 79) : ℂ) * ζ ^ 13 - ((21 / 79) : ℂ) * ζ ^ 15 + ((74 / 79) : ℂ) * ζ ^ 17 + ((534 / 395) : ℂ) * ζ ^ 18 + ((90 / 79) : ℂ) * ζ ^ 21 + ((908 / 395) : ℂ) * ζ ^ 22 + ((908 / 395) : ℂ) * ζ ^ 24 + ((90 / 79) : ℂ) * ζ ^ 25 + ((98 / 79) : ℂ) * ζ ^ 27 + ((852 / 395) : ℂ) * ζ ^ 28 - ((74 / 79) : ℂ) * ζ ^ 29 - ((56 / 395) : ℂ) * ζ ^ 30 + ((98 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep06CoefficientIdentity02 :
    row18_reducedY22_combinationStep06Coefficient02 =
      row18_reducedY22_combinationStep05Coefficient02 +
        row18_reducedY22_combinationStep06Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep06Coefficient02 row18_reducedY22_combinationStep05Coefficient02 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 (-((42103 / 18723) : ℂ) - ((23174 / 18723) : ℂ) * ζ ^ 1 + ((92455 / 37446) : ℂ) * ζ ^ 2 + ((80893 / 37446) : ℂ) * ζ ^ 3 + ((38959 / 18723) : ℂ) * ζ ^ 4 - ((26789 / 37446) : ℂ) * ζ ^ 5 - ((23080 / 18723) : ℂ) * ζ ^ 6 - ((811 / 474) : ℂ) * ζ ^ 7 - ((4957 / 37446) : ℂ) * ζ ^ 8 - ((3776 / 18723) : ℂ) * ζ ^ 9 + ((18583 / 18723) : ℂ) * ζ ^ 10 + ((7442 / 18723) : ℂ) * ζ ^ 11 + ((12359 / 37446) : ℂ) * ζ ^ 12 - ((11599 / 18723) : ℂ) * ζ ^ 13 - ((17507 / 37446) : ℂ) * ζ ^ 14 - ((36263 / 37446) : ℂ) * ζ ^ 15 - ((50 / 18723) : ℂ) * ζ ^ 16 + ((6100 / 6241) : ℂ) * ζ ^ 17 + ((36721 / 18723) : ℂ) * ζ ^ 18 + ((24037 / 37446) : ℂ) * ζ ^ 19 - ((12377 / 12482) : ℂ) * ζ ^ 20 - ((12464 / 6241) : ℂ) * ζ ^ 21 - ((12287 / 12482) : ℂ) * ζ ^ 22 + ((1571 / 18723) : ℂ) * ζ ^ 23 + ((54295 / 37446) : ℂ) * ζ ^ 24 + ((15545 / 12482) : ℂ) * ζ ^ 25 + ((1990 / 6241) : ℂ) * ζ ^ 26 - ((11393 / 12482) : ℂ) * ζ ^ 27 - ((6885 / 12482) : ℂ) * ζ ^ 28 + ((1203 / 12482) : ℂ) * ζ ^ 29 + ((495 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep06Coefficient03 : ℂ :=
  (-((46 / 79) : ℂ) - ((24 / 79) : ℂ) * ζ ^ 1 - ((19 / 158) : ℂ) * ζ ^ 2 + ((77 / 158) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((2 / 79) : ℂ) * ζ ^ 6 + ((5 / 158) : ℂ) * ζ ^ 8 + ((95 / 158) : ℂ) * ζ ^ 9 + ((9 / 79) : ℂ) * ζ ^ 11 + ((5 / 158) : ℂ) * ζ ^ 12 + ((24 / 79) : ℂ) * ζ ^ 13 - ((5 / 79) : ℂ) * ζ ^ 15 + ((24 / 79) : ℂ) * ζ ^ 17 - ((23 / 158) : ℂ) * ζ ^ 18 - ((29 / 158) : ℂ) * ζ ^ 21 + ((19 / 158) : ℂ) * ζ ^ 22 - ((67 / 158) : ℂ) * ζ ^ 25 + ((29 / 158) : ℂ) * ζ ^ 27 - ((5 / 158) : ℂ) * ζ ^ 28 - ((24 / 79) : ℂ) * ζ ^ 29 + ((1 / 79) : ℂ) * ζ ^ 30 - ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep06CoefficientIdentity03 :
    row18_reducedY22_combinationStep06Coefficient03 =
      row18_reducedY22_combinationStep05Coefficient03 +
        row18_reducedY22_combinationStep06Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep06Coefficient03 row18_reducedY22_combinationStep05Coefficient03 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 (((82169 / 37446) : ℂ) + ((27289 / 12482) : ℂ) * ζ ^ 1 + ((28891 / 18723) : ℂ) * ζ ^ 2 - ((11733 / 6241) : ℂ) * ζ ^ 3 - ((28950 / 6241) : ℂ) * ζ ^ 4 - ((6049 / 18723) : ℂ) * ζ ^ 5 + ((40575 / 12482) : ℂ) * ζ ^ 6 + ((65719 / 18723) : ℂ) * ζ ^ 7 + ((25477 / 18723) : ℂ) * ζ ^ 8 - ((4086 / 6241) : ℂ) * ζ ^ 9 - ((17153 / 12482) : ℂ) * ζ ^ 10 - ((17232 / 6241) : ℂ) * ζ ^ 11 - ((60505 / 37446) : ℂ) * ζ ^ 12 + ((3538 / 18723) : ℂ) * ζ ^ 13 + ((137947 / 37446) : ℂ) * ζ ^ 14 + ((18220 / 6241) : ℂ) * ζ ^ 15 + ((4242 / 6241) : ℂ) * ζ ^ 16 - ((54652 / 18723) : ℂ) * ζ ^ 17 - ((23899 / 6241) : ℂ) * ζ ^ 18 - ((46400 / 18723) : ℂ) * ζ ^ 19 + ((129031 / 37446) : ℂ) * ζ ^ 20 + ((62935 / 18723) : ℂ) * ζ ^ 21 + ((15669 / 12482) : ℂ) * ζ ^ 22 - ((16079 / 6241) : ℂ) * ζ ^ 23 - ((13287 / 6241) : ℂ) * ζ ^ 24 - ((9583 / 6241) : ℂ) * ζ ^ 25 + ((41267 / 37446) : ℂ) * ζ ^ 26 + ((11131 / 12482) : ℂ) * ζ ^ 27 + ((1049 / 6241) : ℂ) * ζ ^ 28 + ((1042 / 6241) : ℂ) * ζ ^ 29 - ((924 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep06Coefficient04 : ℂ :=
  (-((57 / 79) : ℂ) - ((4 / 395) : ℂ) * ζ ^ 1 - ((1391 / 790) : ℂ) * ζ ^ 2 + ((186 / 395) : ℂ) * ζ ^ 3 - ((582 / 395) : ℂ) * ζ ^ 5 - ((1392 / 395) : ℂ) * ζ ^ 6 - ((181 / 158) : ℂ) * ζ ^ 8 - ((642 / 395) : ℂ) * ζ ^ 9 - ((828 / 395) : ℂ) * ζ ^ 11 - ((181 / 158) : ℂ) * ζ ^ 12 + ((4 / 395) : ℂ) * ζ ^ 13 - ((764 / 395) : ℂ) * ζ ^ 15 + ((4 / 395) : ℂ) * ζ ^ 17 + ((1393 / 790) : ℂ) * ζ ^ 18 - ((182 / 395) : ℂ) * ζ ^ 21 + ((1391 / 790) : ℂ) * ζ ^ 22 + ((578 / 395) : ℂ) * ζ ^ 25 + ((182 / 395) : ℂ) * ζ ^ 27 + ((181 / 158) : ℂ) * ζ ^ 28 - ((4 / 395) : ℂ) * ζ ^ 29 - ((696 / 395) : ℂ) * ζ ^ 30 + ((828 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep06CoefficientIdentity04 :
    row18_reducedY22_combinationStep06Coefficient04 =
      row18_reducedY22_combinationStep05Coefficient04 +
        row18_reducedY22_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep06Coefficient04 row18_reducedY22_combinationStep05Coefficient04 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep06Coefficient05 : ℂ :=
  (-((6 / 79) : ℂ) + ((20 / 79) : ℂ) * ζ ^ 1 - ((229 / 158) : ℂ) * ζ ^ 2 - ((193 / 79) : ℂ) * ζ ^ 5 - ((217 / 158) : ℂ) * ζ ^ 6 - ((217 / 158) : ℂ) * ζ ^ 8 - ((193 / 79) : ℂ) * ζ ^ 9 - ((311 / 158) : ℂ) * ζ ^ 11 - ((42 / 79) : ℂ) * ζ ^ 12 - ((20 / 79) : ℂ) * ζ ^ 13 - ((125 / 79) : ℂ) * ζ ^ 15 - ((20 / 79) : ℂ) * ζ ^ 17 + ((49 / 79) : ℂ) * ζ ^ 18 + ((173 / 158) : ℂ) * ζ ^ 21 + ((229 / 158) : ℂ) * ζ ^ 22 + ((119 / 158) : ℂ) * ζ ^ 24 + ((213 / 79) : ℂ) * ζ ^ 25 + ((125 / 79) : ℂ) * ζ ^ 27 + ((217 / 158) : ℂ) * ζ ^ 28 + ((20 / 79) : ℂ) * ζ ^ 29 - ((133 / 158) : ℂ) * ζ ^ 30 + ((311 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep06CoefficientIdentity05 :
    row18_reducedY22_combinationStep06Coefficient05 =
      row18_reducedY22_combinationStep05Coefficient05 +
        row18_reducedY22_combinationStep06Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep06Coefficient05 row18_reducedY22_combinationStep05Coefficient05 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 (-((15887 / 18723) : ℂ) - ((11543 / 37446) : ℂ) * ζ ^ 1 + ((18481 / 18723) : ℂ) * ζ ^ 2 - ((13379 / 37446) : ℂ) * ζ ^ 3 - ((3 / 79) : ℂ) * ζ ^ 4 + ((8669 / 6241) : ℂ) * ζ ^ 5 + ((13859 / 12482) : ℂ) * ζ ^ 6 - ((7244 / 6241) : ℂ) * ζ ^ 7 + ((22979 / 37446) : ℂ) * ζ ^ 8 + ((1329 / 12482) : ℂ) * ζ ^ 9 - ((25025 / 37446) : ℂ) * ζ ^ 10 + ((1063 / 18723) : ℂ) * ζ ^ 11 + ((2227 / 37446) : ℂ) * ζ ^ 12 + ((4895 / 18723) : ℂ) * ζ ^ 13 - ((27221 / 37446) : ℂ) * ζ ^ 14 + ((6851 / 18723) : ℂ) * ζ ^ 15 + ((2182 / 6241) : ℂ) * ζ ^ 16 + ((24640 / 18723) : ℂ) * ζ ^ 17 - ((44759 / 37446) : ℂ) * ζ ^ 18 + ((12271 / 37446) : ℂ) * ζ ^ 19 - ((1147 / 37446) : ℂ) * ζ ^ 20 + ((19 / 37446) : ℂ) * ζ ^ 21 - ((82505 / 37446) : ℂ) * ζ ^ 22 + ((17773 / 12482) : ℂ) * ζ ^ 23 - ((13625 / 18723) : ℂ) * ζ ^ 24 + ((7289 / 12482) : ℂ) * ζ ^ 25 - ((11057 / 37446) : ℂ) * ζ ^ 26 + ((10057 / 12482) : ℂ) * ζ ^ 27 - ((13945 / 12482) : ℂ) * ζ ^ 28 + ((1861 / 12482) : ℂ) * ζ ^ 29 + ((429 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep06Coefficient06 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep06CoefficientIdentity06 :
    row18_reducedY22_combinationStep06Coefficient06 =
      row18_reducedY22_combinationStep05Coefficient06 +
        row18_reducedY22_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep06Coefficient06 row18_reducedY22_combinationStep05Coefficient06 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep06Coefficient07 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep06CoefficientIdentity07 :
    row18_reducedY22_combinationStep06Coefficient07 =
      row18_reducedY22_combinationStep05Coefficient07 +
        row18_reducedY22_combinationStep06Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep06Coefficient07 row18_reducedY22_combinationStep05Coefficient07 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 (-((82169 / 37446) : ℂ) - ((27289 / 12482) : ℂ) * ζ ^ 1 - ((28891 / 18723) : ℂ) * ζ ^ 2 + ((11733 / 6241) : ℂ) * ζ ^ 3 + ((28950 / 6241) : ℂ) * ζ ^ 4 + ((6049 / 18723) : ℂ) * ζ ^ 5 - ((40575 / 12482) : ℂ) * ζ ^ 6 - ((65719 / 18723) : ℂ) * ζ ^ 7 - ((25477 / 18723) : ℂ) * ζ ^ 8 + ((4086 / 6241) : ℂ) * ζ ^ 9 + ((17153 / 12482) : ℂ) * ζ ^ 10 + ((17232 / 6241) : ℂ) * ζ ^ 11 + ((60505 / 37446) : ℂ) * ζ ^ 12 - ((3538 / 18723) : ℂ) * ζ ^ 13 - ((137947 / 37446) : ℂ) * ζ ^ 14 - ((18220 / 6241) : ℂ) * ζ ^ 15 - ((4242 / 6241) : ℂ) * ζ ^ 16 + ((54652 / 18723) : ℂ) * ζ ^ 17 + ((23899 / 6241) : ℂ) * ζ ^ 18 + ((46400 / 18723) : ℂ) * ζ ^ 19 - ((129031 / 37446) : ℂ) * ζ ^ 20 - ((62935 / 18723) : ℂ) * ζ ^ 21 - ((15669 / 12482) : ℂ) * ζ ^ 22 + ((16079 / 6241) : ℂ) * ζ ^ 23 + ((13287 / 6241) : ℂ) * ζ ^ 24 + ((9583 / 6241) : ℂ) * ζ ^ 25 - ((41267 / 37446) : ℂ) * ζ ^ 26 - ((11131 / 12482) : ℂ) * ζ ^ 27 - ((1049 / 6241) : ℂ) * ζ ^ 28 - ((1042 / 6241) : ℂ) * ζ ^ 29 + ((924 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep06Coefficient08 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep06CoefficientIdentity08 :
    row18_reducedY22_combinationStep06Coefficient08 =
      row18_reducedY22_combinationStep05Coefficient08 +
        row18_reducedY22_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep06Coefficient08 row18_reducedY22_combinationStep05Coefficient08 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep06Coefficient09 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep06CoefficientIdentity09 :
    row18_reducedY22_combinationStep06Coefficient09 =
      row18_reducedY22_combinationStep05Coefficient09 +
        row18_reducedY22_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep06Coefficient09 row18_reducedY22_combinationStep05Coefficient09 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep06Coefficient10 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep06CoefficientIdentity10 :
    row18_reducedY22_combinationStep06Coefficient10 =
      row18_reducedY22_combinationStep05Coefficient10 +
        row18_reducedY22_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep06Coefficient10 row18_reducedY22_combinationStep05Coefficient10 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep06Coefficient11 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep06CoefficientIdentity11 :
    row18_reducedY22_combinationStep06Coefficient11 =
      row18_reducedY22_combinationStep05Coefficient11 +
        row18_reducedY22_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep06Coefficient11 row18_reducedY22_combinationStep05Coefficient11 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep06Coefficient12 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep06CoefficientIdentity12 :
    row18_reducedY22_combinationStep06Coefficient12 =
      row18_reducedY22_combinationStep05Coefficient12 +
        row18_reducedY22_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep06Coefficient12 row18_reducedY22_combinationStep05Coefficient12 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep06Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep06CoefficientIdentity13 :
    row18_reducedY22_combinationStep06Coefficient13 =
      row18_reducedY22_combinationStep05Coefficient13 +
        row18_reducedY22_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep06Coefficient13 row18_reducedY22_combinationStep05Coefficient13 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep06Coefficient14 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep06CoefficientIdentity14 :
    row18_reducedY22_combinationStep06Coefficient14 =
      row18_reducedY22_combinationStep05Coefficient14 +
        row18_reducedY22_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep06Coefficient14 row18_reducedY22_combinationStep05Coefficient14 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep06Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep06CoefficientIdentity15 :
    row18_reducedY22_combinationStep06Coefficient15 =
      row18_reducedY22_combinationStep05Coefficient15 +
        row18_reducedY22_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep06Coefficient15 row18_reducedY22_combinationStep05Coefficient15 row18_reducedY22_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY22_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY22_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY22_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY22_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY22_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY22_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY22_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY22_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY22_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY22_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY22_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY22_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY22_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY22_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY22_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY22_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY22_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY22_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY22_combinationStep06CoefficientIdentity00,
      row18_reducedY22_combinationStep06CoefficientIdentity01,
      row18_reducedY22_combinationStep06CoefficientIdentity02,
      row18_reducedY22_combinationStep06CoefficientIdentity03,
      row18_reducedY22_combinationStep06CoefficientIdentity04,
      row18_reducedY22_combinationStep06CoefficientIdentity05,
      row18_reducedY22_combinationStep06CoefficientIdentity06,
      row18_reducedY22_combinationStep06CoefficientIdentity07,
      row18_reducedY22_combinationStep06CoefficientIdentity08,
      row18_reducedY22_combinationStep06CoefficientIdentity09,
      row18_reducedY22_combinationStep06CoefficientIdentity10,
      row18_reducedY22_combinationStep06CoefficientIdentity11,
      row18_reducedY22_combinationStep06CoefficientIdentity12,
      row18_reducedY22_combinationStep06CoefficientIdentity13,
      row18_reducedY22_combinationStep06CoefficientIdentity14,
      row18_reducedY22_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY22_combinationStep06Multiplier * equation

private def row18_reducedY22_combinationStep07Multiplier : ℂ :=
  (-((208 / 79) : ℂ) - ((380 / 79) : ℂ) * ζ ^ 1 + ((60 / 79) : ℂ) * ζ ^ 2 - ((132 / 79) : ℂ) * ζ ^ 3 - ((306 / 79) : ℂ) * ζ ^ 5 + ((236 / 79) : ℂ) * ζ ^ 8 + ((156 / 79) : ℂ) * ζ ^ 9 - ((24 / 79) : ℂ) * ζ ^ 11 + ((180 / 79) : ℂ) * ζ ^ 12 + ((380 / 79) : ℂ) * ζ ^ 13 + ((58 / 79) : ℂ) * ζ ^ 15 + ((380 / 79) : ℂ) * ζ ^ 17 - ((60 / 79) : ℂ) * ζ ^ 18 + ((248 / 79) : ℂ) * ζ ^ 21 - ((60 / 79) : ℂ) * ζ ^ 22 - ((416 / 79) : ℂ) * ζ ^ 24 - ((74 / 79) : ℂ) * ζ ^ 25 + ((248 / 79) : ℂ) * ζ ^ 27 - ((236 / 79) : ℂ) * ζ ^ 28 - ((380 / 79) : ℂ) * ζ ^ 29 - ((160 / 79) : ℂ) * ζ ^ 30 + ((24 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY22_combinationStep07Coefficient00 : ℂ :=
  (((136 / 79) : ℂ) + ((4 / 395) : ℂ) * ζ ^ 1 + ((1391 / 790) : ℂ) * ζ ^ 2 - ((186 / 395) : ℂ) * ζ ^ 3 + ((582 / 395) : ℂ) * ζ ^ 5 + ((1392 / 395) : ℂ) * ζ ^ 6 + ((181 / 158) : ℂ) * ζ ^ 8 + ((642 / 395) : ℂ) * ζ ^ 9 + ((828 / 395) : ℂ) * ζ ^ 11 + ((181 / 158) : ℂ) * ζ ^ 12 - ((4 / 395) : ℂ) * ζ ^ 13 + ((764 / 395) : ℂ) * ζ ^ 15 - ((4 / 395) : ℂ) * ζ ^ 17 - ((1393 / 790) : ℂ) * ζ ^ 18 + ((182 / 395) : ℂ) * ζ ^ 21 - ((1391 / 790) : ℂ) * ζ ^ 22 - ((578 / 395) : ℂ) * ζ ^ 25 - ((182 / 395) : ℂ) * ζ ^ 27 - ((181 / 158) : ℂ) * ζ ^ 28 + ((4 / 395) : ℂ) * ζ ^ 29 + ((696 / 395) : ℂ) * ζ ^ 30 - ((828 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep07CoefficientIdentity00 :
    row18_reducedY22_combinationStep07Coefficient00 =
      row18_reducedY22_combinationStep06Coefficient00 +
        row18_reducedY22_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep07Coefficient00 row18_reducedY22_combinationStep06Coefficient00 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep07Coefficient01 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep07CoefficientIdentity01 :
    row18_reducedY22_combinationStep07Coefficient01 =
      row18_reducedY22_combinationStep06Coefficient01 +
        row18_reducedY22_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep07Coefficient01 row18_reducedY22_combinationStep06Coefficient01 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep07Coefficient02 : ℂ :=
  (((184 / 395) : ℂ) - ((37 / 79) : ℂ) * ζ ^ 1 - ((1511 / 790) : ℂ) * ζ ^ 2 + ((101 / 158) : ℂ) * ζ ^ 3 - ((161 / 79) : ℂ) * ζ ^ 5 - ((849 / 790) : ℂ) * ζ ^ 6 - ((792 / 395) : ℂ) * ζ ^ 8 - ((87 / 158) : ℂ) * ζ ^ 9 - ((287 / 158) : ℂ) * ζ ^ 11 - ((331 / 395) : ℂ) * ζ ^ 12 + ((37 / 79) : ℂ) * ζ ^ 13 - ((101 / 158) : ℂ) * ζ ^ 15 + ((37 / 79) : ℂ) * ζ ^ 17 + ((1143 / 790) : ℂ) * ζ ^ 18 + ((124 / 79) : ℂ) * ζ ^ 21 + ((1511 / 790) : ℂ) * ζ ^ 22 + ((1511 / 790) : ℂ) * ζ ^ 24 + ((124 / 79) : ℂ) * ζ ^ 25 + ((287 / 158) : ℂ) * ζ ^ 27 + ((792 / 395) : ℂ) * ζ ^ 28 - ((37 / 79) : ℂ) * ζ ^ 29 + ((73 / 790) : ℂ) * ζ ^ 30 + ((287 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep07CoefficientIdentity02 :
    row18_reducedY22_combinationStep07Coefficient02 =
      row18_reducedY22_combinationStep06Coefficient02 +
        row18_reducedY22_combinationStep07Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep07Coefficient02 row18_reducedY22_combinationStep06Coefficient02 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 (((4978 / 6241) : ℂ) + ((1363 / 6241) : ℂ) * ζ ^ 1 - ((2345 / 12482) : ℂ) * ζ ^ 2 + ((2043 / 12482) : ℂ) * ζ ^ 3 - ((2434 / 6241) : ℂ) * ζ ^ 4 + ((1310 / 6241) : ℂ) * ζ ^ 5 + ((10323 / 12482) : ℂ) * ζ ^ 6 + ((3050 / 6241) : ℂ) * ζ ^ 7 - ((2498 / 6241) : ℂ) * ζ ^ 8 - ((1739 / 12482) : ℂ) * ζ ^ 9 + ((5095 / 12482) : ℂ) * ζ ^ 10 - ((4917 / 12482) : ℂ) * ζ ^ 11 + ((4607 / 6241) : ℂ) * ζ ^ 12 - ((1753 / 6241) : ℂ) * ζ ^ 13 - ((2961 / 6241) : ℂ) * ζ ^ 14 + ((8021 / 12482) : ℂ) * ζ ^ 15 - ((347 / 6241) : ℂ) * ζ ^ 16 + ((1852 / 6241) : ℂ) * ζ ^ 17 + ((505 / 6241) : ℂ) * ζ ^ 18 - ((728 / 6241) : ℂ) * ζ ^ 19 + ((1667 / 6241) : ℂ) * ζ ^ 20 - ((6627 / 12482) : ℂ) * ζ ^ 21 - ((4319 / 12482) : ℂ) * ζ ^ 22 + ((92 / 6241) : ℂ) * ζ ^ 23 + ((4045 / 12482) : ℂ) * ζ ^ 24 + ((7860 / 6241) : ℂ) * ζ ^ 25 + ((13 / 6241) : ℂ) * ζ ^ 26 - ((3509 / 6241) : ℂ) * ζ ^ 27 - ((573 / 6241) : ℂ) * ζ ^ 28 + ((888 / 6241) : ℂ) * ζ ^ 29 - ((90 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep07Coefficient03 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep07CoefficientIdentity03 :
    row18_reducedY22_combinationStep07Coefficient03 =
      row18_reducedY22_combinationStep06Coefficient03 +
        row18_reducedY22_combinationStep07Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep07Coefficient03 row18_reducedY22_combinationStep06Coefficient03 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 (-((4466 / 6241) : ℂ) - ((3988 / 6241) : ℂ) * ζ ^ 1 - ((6751 / 12482) : ℂ) * ζ ^ 2 - ((1189 / 12482) : ℂ) * ζ ^ 3 + ((4723 / 6241) : ℂ) * ζ ^ 4 + ((1569 / 12482) : ℂ) * ζ ^ 5 - ((125 / 6241) : ℂ) * ζ ^ 6 - ((1633 / 6241) : ℂ) * ζ ^ 7 - ((4183 / 6241) : ℂ) * ζ ^ 8 + ((5487 / 6241) : ℂ) * ζ ^ 9 + ((1469 / 6241) : ℂ) * ζ ^ 10 + ((2829 / 6241) : ℂ) * ζ ^ 11 + ((1961 / 12482) : ℂ) * ζ ^ 12 - ((293 / 6241) : ℂ) * ζ ^ 13 + ((139 / 6241) : ℂ) * ζ ^ 14 + ((2645 / 12482) : ℂ) * ζ ^ 15 - ((191 / 6241) : ℂ) * ζ ^ 16 + ((3653 / 6241) : ℂ) * ζ ^ 17 + ((2886 / 6241) : ℂ) * ζ ^ 18 + ((3632 / 6241) : ℂ) * ζ ^ 19 - ((3885 / 6241) : ℂ) * ζ ^ 20 - ((2547 / 6241) : ℂ) * ζ ^ 21 + ((2357 / 12482) : ℂ) * ζ ^ 22 + ((3984 / 6241) : ℂ) * ζ ^ 23 + ((697 / 6241) : ℂ) * ζ ^ 24 - ((627 / 6241) : ℂ) * ζ ^ 25 - ((2849 / 6241) : ℂ) * ζ ^ 26 - ((718 / 6241) : ℂ) * ζ ^ 27 + ((916 / 6241) : ℂ) * ζ ^ 28 + ((8 / 79) : ℂ) * ζ ^ 29 - ((84 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep07Coefficient04 : ℂ :=
  (-((57 / 79) : ℂ) - ((4 / 395) : ℂ) * ζ ^ 1 - ((1391 / 790) : ℂ) * ζ ^ 2 + ((186 / 395) : ℂ) * ζ ^ 3 - ((582 / 395) : ℂ) * ζ ^ 5 - ((1392 / 395) : ℂ) * ζ ^ 6 - ((181 / 158) : ℂ) * ζ ^ 8 - ((642 / 395) : ℂ) * ζ ^ 9 - ((828 / 395) : ℂ) * ζ ^ 11 - ((181 / 158) : ℂ) * ζ ^ 12 + ((4 / 395) : ℂ) * ζ ^ 13 - ((764 / 395) : ℂ) * ζ ^ 15 + ((4 / 395) : ℂ) * ζ ^ 17 + ((1393 / 790) : ℂ) * ζ ^ 18 - ((182 / 395) : ℂ) * ζ ^ 21 + ((1391 / 790) : ℂ) * ζ ^ 22 + ((578 / 395) : ℂ) * ζ ^ 25 + ((182 / 395) : ℂ) * ζ ^ 27 + ((181 / 158) : ℂ) * ζ ^ 28 - ((4 / 395) : ℂ) * ζ ^ 29 - ((696 / 395) : ℂ) * ζ ^ 30 + ((828 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep07CoefficientIdentity04 :
    row18_reducedY22_combinationStep07Coefficient04 =
      row18_reducedY22_combinationStep06Coefficient04 +
        row18_reducedY22_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep07Coefficient04 row18_reducedY22_combinationStep06Coefficient04 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep07Coefficient05 : ℂ :=
  (-((6 / 79) : ℂ) + ((20 / 79) : ℂ) * ζ ^ 1 - ((229 / 158) : ℂ) * ζ ^ 2 - ((193 / 79) : ℂ) * ζ ^ 5 - ((217 / 158) : ℂ) * ζ ^ 6 - ((217 / 158) : ℂ) * ζ ^ 8 - ((193 / 79) : ℂ) * ζ ^ 9 - ((311 / 158) : ℂ) * ζ ^ 11 - ((42 / 79) : ℂ) * ζ ^ 12 - ((20 / 79) : ℂ) * ζ ^ 13 - ((125 / 79) : ℂ) * ζ ^ 15 - ((20 / 79) : ℂ) * ζ ^ 17 + ((49 / 79) : ℂ) * ζ ^ 18 + ((173 / 158) : ℂ) * ζ ^ 21 + ((229 / 158) : ℂ) * ζ ^ 22 + ((119 / 158) : ℂ) * ζ ^ 24 + ((213 / 79) : ℂ) * ζ ^ 25 + ((125 / 79) : ℂ) * ζ ^ 27 + ((217 / 158) : ℂ) * ζ ^ 28 + ((20 / 79) : ℂ) * ζ ^ 29 - ((133 / 158) : ℂ) * ζ ^ 30 + ((311 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY22_combinationStep07CoefficientIdentity05 :
    row18_reducedY22_combinationStep07Coefficient05 =
      row18_reducedY22_combinationStep06Coefficient05 +
        row18_reducedY22_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep07Coefficient05 row18_reducedY22_combinationStep06Coefficient05 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep07Coefficient06 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep07CoefficientIdentity06 :
    row18_reducedY22_combinationStep07Coefficient06 =
      row18_reducedY22_combinationStep06Coefficient06 +
        row18_reducedY22_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep07Coefficient06 row18_reducedY22_combinationStep06Coefficient06 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep07Coefficient07 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep07CoefficientIdentity07 :
    row18_reducedY22_combinationStep07Coefficient07 =
      row18_reducedY22_combinationStep06Coefficient07 +
        row18_reducedY22_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep07Coefficient07 row18_reducedY22_combinationStep06Coefficient07 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep07Coefficient08 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep07CoefficientIdentity08 :
    row18_reducedY22_combinationStep07Coefficient08 =
      row18_reducedY22_combinationStep06Coefficient08 +
        row18_reducedY22_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep07Coefficient08 row18_reducedY22_combinationStep06Coefficient08 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep07Coefficient09 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep07CoefficientIdentity09 :
    row18_reducedY22_combinationStep07Coefficient09 =
      row18_reducedY22_combinationStep06Coefficient09 +
        row18_reducedY22_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep07Coefficient09 row18_reducedY22_combinationStep06Coefficient09 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep07Coefficient10 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep07CoefficientIdentity10 :
    row18_reducedY22_combinationStep07Coefficient10 =
      row18_reducedY22_combinationStep06Coefficient10 +
        row18_reducedY22_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep07Coefficient10 row18_reducedY22_combinationStep06Coefficient10 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep07Coefficient11 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep07CoefficientIdentity11 :
    row18_reducedY22_combinationStep07Coefficient11 =
      row18_reducedY22_combinationStep06Coefficient11 +
        row18_reducedY22_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep07Coefficient11 row18_reducedY22_combinationStep06Coefficient11 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep07Coefficient12 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep07CoefficientIdentity12 :
    row18_reducedY22_combinationStep07Coefficient12 =
      row18_reducedY22_combinationStep06Coefficient12 +
        row18_reducedY22_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep07Coefficient12 row18_reducedY22_combinationStep06Coefficient12 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep07Coefficient13 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep07CoefficientIdentity13 :
    row18_reducedY22_combinationStep07Coefficient13 =
      row18_reducedY22_combinationStep06Coefficient13 +
        row18_reducedY22_combinationStep07Multiplier *
          (((5 / 316) : ℂ) - ((3 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((33 / 158) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 + ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 + ((3 / 316) : ℂ) * ζ ^ 9 + ((33 / 316) : ℂ) * ζ ^ 11 + ((3 / 79) : ℂ) * ζ ^ 12 + ((3 / 316) : ℂ) * ζ ^ 13 + ((35 / 158) : ℂ) * ζ ^ 15 + ((3 / 316) : ℂ) * ζ ^ 17 + ((19 / 316) : ℂ) * ζ ^ 18 + ((45 / 158) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((1 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 - ((3 / 316) : ℂ) * ζ ^ 29 + ((13 / 79) : ℂ) * ζ ^ 30 - ((33 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep07Coefficient13 row18_reducedY22_combinationStep06Coefficient13 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 (((3058 / 6241) : ℂ) + ((392 / 6241) : ℂ) * ζ ^ 1 - ((2841 / 12482) : ℂ) * ζ ^ 2 - ((103 / 6241) : ℂ) * ζ ^ 3 + ((3836 / 6241) : ℂ) * ζ ^ 4 - ((4895 / 12482) : ℂ) * ζ ^ 5 - ((2491 / 12482) : ℂ) * ζ ^ 6 - ((12839 / 12482) : ℂ) * ζ ^ 7 + ((2017 / 12482) : ℂ) * ζ ^ 8 + ((10211 / 12482) : ℂ) * ζ ^ 9 + ((2538 / 6241) : ℂ) * ζ ^ 10 - ((1486 / 6241) : ℂ) * ζ ^ 11 - ((24711 / 12482) : ℂ) * ζ ^ 12 - ((6425 / 12482) : ℂ) * ζ ^ 13 - ((1453 / 6241) : ℂ) * ζ ^ 14 + ((5079 / 12482) : ℂ) * ζ ^ 15 + ((2641 / 12482) : ℂ) * ζ ^ 16 - ((707 / 12482) : ℂ) * ζ ^ 17 - ((12423 / 12482) : ℂ) * ζ ^ 18 - ((1465 / 6241) : ℂ) * ζ ^ 19 - ((10497 / 12482) : ℂ) * ζ ^ 20 - ((3557 / 6241) : ℂ) * ζ ^ 21 - ((2515 / 12482) : ℂ) * ζ ^ 22 + ((7701 / 6241) : ℂ) * ζ ^ 23 - ((6705 / 12482) : ℂ) * ζ ^ 24 - ((2191 / 6241) : ℂ) * ζ ^ 25 - ((6207 / 6241) : ℂ) * ζ ^ 26 - ((2633 / 6241) : ℂ) * ζ ^ 27 + ((1037 / 6241) : ℂ) * ζ ^ 28 + ((1632 / 6241) : ℂ) * ζ ^ 29 - ((198 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep07Coefficient14 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep07CoefficientIdentity14 :
    row18_reducedY22_combinationStep07Coefficient14 =
      row18_reducedY22_combinationStep06Coefficient14 +
        row18_reducedY22_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep07Coefficient14 row18_reducedY22_combinationStep06Coefficient14 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep07Coefficient15 : ℂ :=
  (-(1 : ℂ))

private theorem row18_reducedY22_combinationStep07CoefficientIdentity15 :
    row18_reducedY22_combinationStep07Coefficient15 =
      row18_reducedY22_combinationStep06Coefficient15 +
        row18_reducedY22_combinationStep07Multiplier *
          (-((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((35 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep07Coefficient15 row18_reducedY22_combinationStep06Coefficient15 row18_reducedY22_combinationStep07Multiplier
  close_cyclotomic_row18 (((4466 / 6241) : ℂ) + ((3988 / 6241) : ℂ) * ζ ^ 1 + ((6751 / 12482) : ℂ) * ζ ^ 2 + ((1189 / 12482) : ℂ) * ζ ^ 3 - ((4723 / 6241) : ℂ) * ζ ^ 4 - ((1569 / 12482) : ℂ) * ζ ^ 5 + ((125 / 6241) : ℂ) * ζ ^ 6 + ((1633 / 6241) : ℂ) * ζ ^ 7 + ((4183 / 6241) : ℂ) * ζ ^ 8 - ((5487 / 6241) : ℂ) * ζ ^ 9 - ((1469 / 6241) : ℂ) * ζ ^ 10 - ((2829 / 6241) : ℂ) * ζ ^ 11 - ((1961 / 12482) : ℂ) * ζ ^ 12 + ((293 / 6241) : ℂ) * ζ ^ 13 - ((139 / 6241) : ℂ) * ζ ^ 14 - ((2645 / 12482) : ℂ) * ζ ^ 15 + ((191 / 6241) : ℂ) * ζ ^ 16 - ((3653 / 6241) : ℂ) * ζ ^ 17 - ((2886 / 6241) : ℂ) * ζ ^ 18 - ((3632 / 6241) : ℂ) * ζ ^ 19 + ((3885 / 6241) : ℂ) * ζ ^ 20 + ((2547 / 6241) : ℂ) * ζ ^ 21 - ((2357 / 12482) : ℂ) * ζ ^ 22 - ((3984 / 6241) : ℂ) * ζ ^ 23 - ((697 / 6241) : ℂ) * ζ ^ 24 + ((627 / 6241) : ℂ) * ζ ^ 25 + ((2849 / 6241) : ℂ) * ζ ^ 26 + ((718 / 6241) : ℂ) * ζ ^ 27 - ((916 / 6241) : ℂ) * ζ ^ 28 - ((8 / 79) : ℂ) * ζ ^ 29 + ((84 / 6241) : ℂ) * ζ ^ 30)

private theorem row18_reducedY22_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY22_combinationStep07Coefficient00) * Y 0 0
      + (row18_reducedY22_combinationStep07Coefficient01) * Y 0 1
      + (row18_reducedY22_combinationStep07Coefficient02) * Y 1 0
      + (row18_reducedY22_combinationStep07Coefficient03) * Y 1 1
      + (row18_reducedY22_combinationStep07Coefficient04) * Y 2 2
      + (row18_reducedY22_combinationStep07Coefficient05) * Y 2 3
      + (row18_reducedY22_combinationStep07Coefficient06) * Y 3 2
      + (row18_reducedY22_combinationStep07Coefficient07) * Y 3 3
      + (row18_reducedY22_combinationStep07Coefficient08) * Y 4 4
      + (row18_reducedY22_combinationStep07Coefficient09) * Y 4 5
      + (row18_reducedY22_combinationStep07Coefficient10) * Y 5 4
      + (row18_reducedY22_combinationStep07Coefficient11) * Y 5 5
      + (row18_reducedY22_combinationStep07Coefficient12) * Y 6 6
      + (row18_reducedY22_combinationStep07Coefficient13) * Y 6 7
      + (row18_reducedY22_combinationStep07Coefficient14) * Y 7 6
      + (row18_reducedY22_combinationStep07Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY22_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation17
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY22_combinationStep07CoefficientIdentity00,
      row18_reducedY22_combinationStep07CoefficientIdentity01,
      row18_reducedY22_combinationStep07CoefficientIdentity02,
      row18_reducedY22_combinationStep07CoefficientIdentity03,
      row18_reducedY22_combinationStep07CoefficientIdentity04,
      row18_reducedY22_combinationStep07CoefficientIdentity05,
      row18_reducedY22_combinationStep07CoefficientIdentity06,
      row18_reducedY22_combinationStep07CoefficientIdentity07,
      row18_reducedY22_combinationStep07CoefficientIdentity08,
      row18_reducedY22_combinationStep07CoefficientIdentity09,
      row18_reducedY22_combinationStep07CoefficientIdentity10,
      row18_reducedY22_combinationStep07CoefficientIdentity11,
      row18_reducedY22_combinationStep07CoefficientIdentity12,
      row18_reducedY22_combinationStep07CoefficientIdentity13,
      row18_reducedY22_combinationStep07CoefficientIdentity14,
      row18_reducedY22_combinationStep07CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY22_combinationStep07Multiplier * equation

private def row18_reducedY22_combinationStep08Multiplier : ℂ :=
  (-((196 / 79) : ℂ) - ((1172 / 395) : ℂ) * ζ ^ 1 + ((376 / 79) : ℂ) * ζ ^ 2 + ((1568 / 395) : ℂ) * ζ ^ 3 + ((114 / 395) : ℂ) * ζ ^ 5 + ((320 / 79) : ℂ) * ζ ^ 6 + ((440 / 79) : ℂ) * ζ ^ 8 + ((2284 / 395) : ℂ) * ζ ^ 9 + ((716 / 395) : ℂ) * ζ ^ 11 + ((440 / 79) : ℂ) * ζ ^ 12 + ((1172 / 395) : ℂ) * ζ ^ 13 - ((282 / 395) : ℂ) * ζ ^ 15 + ((1172 / 395) : ℂ) * ζ ^ 17 + ((56 / 79) : ℂ) * ζ ^ 18 - ((396 / 395) : ℂ) * ζ ^ 21 - ((376 / 79) : ℂ) * ζ ^ 22 - ((1286 / 395) : ℂ) * ζ ^ 25 + ((396 / 395) : ℂ) * ζ ^ 27 - ((440 / 79) : ℂ) * ζ ^ 28 - ((1172 / 395) : ℂ) * ζ ^ 29 + ((160 / 79) : ℂ) * ζ ^ 30 - ((716 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY22_combinationStep08Coefficient00 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep08CoefficientIdentity00 :
    row18_reducedY22_combinationStep08Coefficient00 =
      row18_reducedY22_combinationStep07Coefficient00 +
        row18_reducedY22_combinationStep08Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep08Coefficient00 row18_reducedY22_combinationStep07Coefficient00 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 (((10156 / 6241) : ℂ) - ((101 / 6241) : ℂ) * ζ ^ 1 + ((33853 / 12482) : ℂ) * ζ ^ 2 + ((1998 / 6241) : ℂ) * ζ ^ 3 - ((94749 / 31205) : ℂ) * ζ ^ 4 + ((4077 / 6241) : ℂ) * ζ ^ 5 + ((9212 / 6241) : ℂ) * ζ ^ 6 - ((43073 / 62410) : ℂ) * ζ ^ 7 + ((84843 / 31205) : ℂ) * ζ ^ 8 + ((25261 / 31205) : ℂ) * ζ ^ 9 - ((24041 / 6241) : ℂ) * ζ ^ 10 + ((32119 / 62410) : ℂ) * ζ ^ 11 + ((5027 / 62410) : ℂ) * ζ ^ 12 - ((94377 / 62410) : ℂ) * ζ ^ 13 + ((92141 / 31205) : ℂ) * ζ ^ 14 + ((21547 / 62410) : ℂ) * ζ ^ 15 - ((12127 / 6241) : ℂ) * ζ ^ 16 + ((69291 / 62410) : ℂ) * ζ ^ 17 - ((48732 / 31205) : ℂ) * ζ ^ 18 - ((30837 / 31205) : ℂ) * ζ ^ 19 + ((48091 / 31205) : ℂ) * ζ ^ 20 - ((44169 / 62410) : ℂ) * ζ ^ 21 - ((8199 / 12482) : ℂ) * ζ ^ 22 + ((15086 / 31205) : ℂ) * ζ ^ 23 - ((18594 / 31205) : ℂ) * ζ ^ 24 - ((8253 / 31205) : ℂ) * ζ ^ 25 + ((17279 / 31205) : ℂ) * ζ ^ 26 + ((3923 / 31205) : ℂ) * ζ ^ 27 + ((2871 / 31205) : ℂ) * ζ ^ 28 + ((64 / 31205) : ℂ) * ζ ^ 29 + ((2506 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep08Coefficient01 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep08CoefficientIdentity01 :
    row18_reducedY22_combinationStep08Coefficient01 =
      row18_reducedY22_combinationStep07Coefficient01 +
        row18_reducedY22_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep08Coefficient01 row18_reducedY22_combinationStep07Coefficient01 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep08Coefficient02 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep08CoefficientIdentity02 :
    row18_reducedY22_combinationStep08Coefficient02 =
      row18_reducedY22_combinationStep07Coefficient02 +
        row18_reducedY22_combinationStep08Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep08Coefficient02 row18_reducedY22_combinationStep07Coefficient02 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 (((23846 / 31205) : ℂ) + ((6074 / 31205) : ℂ) * ζ ^ 1 - ((27525 / 12482) : ℂ) * ζ ^ 2 + ((14527 / 62410) : ℂ) * ζ ^ 3 - ((5543 / 31205) : ℂ) * ζ ^ 4 - ((20054 / 6241) : ℂ) * ζ ^ 5 - ((26649 / 62410) : ℂ) * ζ ^ 6 - ((55072 / 31205) : ℂ) * ζ ^ 7 - ((187161 / 62410) : ℂ) * ζ ^ 8 - ((12989 / 62410) : ℂ) * ζ ^ 9 + ((7629 / 12482) : ℂ) * ζ ^ 10 - ((128229 / 62410) : ℂ) * ζ ^ 11 + ((3405 / 12482) : ℂ) * ζ ^ 12 + ((8514 / 31205) : ℂ) * ζ ^ 13 - ((169229 / 62410) : ℂ) * ζ ^ 14 + ((29891 / 62410) : ℂ) * ζ ^ 15 - ((2762 / 31205) : ℂ) * ζ ^ 16 - ((1880 / 6241) : ℂ) * ζ ^ 17 + ((65472 / 31205) : ℂ) * ζ ^ 18 + ((30481 / 31205) : ℂ) * ζ ^ 19 + ((4409 / 31205) : ℂ) * ζ ^ 20 + ((13319 / 12482) : ℂ) * ζ ^ 21 - ((36651 / 62410) : ℂ) * ζ ^ 22 - ((693 / 6241) : ℂ) * ζ ^ 23 + ((56603 / 31205) : ℂ) * ζ ^ 24 + ((25393 / 31205) : ℂ) * ζ ^ 25 + ((17711 / 31205) : ℂ) * ζ ^ 26 + ((12605 / 6241) : ℂ) * ζ ^ 27 + ((21993 / 31205) : ℂ) * ζ ^ 28 - ((8208 / 31205) : ℂ) * ζ ^ 29 + ((15036 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep08Coefficient03 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep08CoefficientIdentity03 :
    row18_reducedY22_combinationStep08Coefficient03 =
      row18_reducedY22_combinationStep07Coefficient03 +
        row18_reducedY22_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep08Coefficient03 row18_reducedY22_combinationStep07Coefficient03 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep08Coefficient04 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY22_combinationStep08CoefficientIdentity04 :
    row18_reducedY22_combinationStep08Coefficient04 =
      row18_reducedY22_combinationStep07Coefficient04 +
        row18_reducedY22_combinationStep08Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep08Coefficient04 row18_reducedY22_combinationStep07Coefficient04 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 (-((10156 / 6241) : ℂ) + ((101 / 6241) : ℂ) * ζ ^ 1 - ((33853 / 12482) : ℂ) * ζ ^ 2 - ((1998 / 6241) : ℂ) * ζ ^ 3 + ((94749 / 31205) : ℂ) * ζ ^ 4 - ((4077 / 6241) : ℂ) * ζ ^ 5 - ((9212 / 6241) : ℂ) * ζ ^ 6 + ((43073 / 62410) : ℂ) * ζ ^ 7 - ((84843 / 31205) : ℂ) * ζ ^ 8 - ((25261 / 31205) : ℂ) * ζ ^ 9 + ((24041 / 6241) : ℂ) * ζ ^ 10 - ((32119 / 62410) : ℂ) * ζ ^ 11 - ((5027 / 62410) : ℂ) * ζ ^ 12 + ((94377 / 62410) : ℂ) * ζ ^ 13 - ((92141 / 31205) : ℂ) * ζ ^ 14 - ((21547 / 62410) : ℂ) * ζ ^ 15 + ((12127 / 6241) : ℂ) * ζ ^ 16 - ((69291 / 62410) : ℂ) * ζ ^ 17 + ((48732 / 31205) : ℂ) * ζ ^ 18 + ((30837 / 31205) : ℂ) * ζ ^ 19 - ((48091 / 31205) : ℂ) * ζ ^ 20 + ((44169 / 62410) : ℂ) * ζ ^ 21 + ((8199 / 12482) : ℂ) * ζ ^ 22 - ((15086 / 31205) : ℂ) * ζ ^ 23 + ((18594 / 31205) : ℂ) * ζ ^ 24 + ((8253 / 31205) : ℂ) * ζ ^ 25 - ((17279 / 31205) : ℂ) * ζ ^ 26 - ((3923 / 31205) : ℂ) * ζ ^ 27 - ((2871 / 31205) : ℂ) * ζ ^ 28 - ((64 / 31205) : ℂ) * ζ ^ 29 - ((2506 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep08Coefficient05 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep08CoefficientIdentity05 :
    row18_reducedY22_combinationStep08Coefficient05 =
      row18_reducedY22_combinationStep07Coefficient05 +
        row18_reducedY22_combinationStep08Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY22_combinationStep08Coefficient05 row18_reducedY22_combinationStep07Coefficient05 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 (-((3855 / 6241) : ℂ) - ((7907 / 31205) : ℂ) * ζ ^ 1 - ((10637 / 62410) : ℂ) * ζ ^ 2 + ((4245 / 6241) : ℂ) * ζ ^ 3 + ((7989 / 31205) : ℂ) * ζ ^ 4 - ((135859 / 62410) : ℂ) * ζ ^ 5 + ((11002 / 31205) : ℂ) * ζ ^ 6 - ((3835 / 12482) : ℂ) * ζ ^ 7 - ((14873 / 12482) : ℂ) * ζ ^ 8 + ((30863 / 62410) : ℂ) * ζ ^ 9 - ((60774 / 31205) : ℂ) * ζ ^ 10 - ((128482 / 31205) : ℂ) * ζ ^ 11 - ((90301 / 62410) : ℂ) * ζ ^ 12 + ((116133 / 62410) : ℂ) * ζ ^ 13 + ((40683 / 62410) : ℂ) * ζ ^ 14 + ((46639 / 62410) : ℂ) * ζ ^ 15 - ((8767 / 12482) : ℂ) * ζ ^ 16 - ((162791 / 62410) : ℂ) * ζ ^ 17 - ((3311 / 6241) : ℂ) * ζ ^ 18 + ((74278 / 31205) : ℂ) * ζ ^ 19 + ((17679 / 62410) : ℂ) * ζ ^ 20 + ((37511 / 31205) : ℂ) * ζ ^ 21 + ((8353 / 31205) : ℂ) * ζ ^ 22 - ((48728 / 31205) : ℂ) * ζ ^ 23 - ((5279 / 31205) : ℂ) * ζ ^ 24 - ((8966 / 31205) : ℂ) * ζ ^ 25 + ((15749 / 31205) : ℂ) * ζ ^ 26 + ((19452 / 6241) : ℂ) * ζ ^ 27 + ((45162 / 31205) : ℂ) * ζ ^ 28 - ((26334 / 31205) : ℂ) * ζ ^ 29 + ((6444 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY22_combinationStep08Coefficient06 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep08CoefficientIdentity06 :
    row18_reducedY22_combinationStep08Coefficient06 =
      row18_reducedY22_combinationStep07Coefficient06 +
        row18_reducedY22_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep08Coefficient06 row18_reducedY22_combinationStep07Coefficient06 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep08Coefficient07 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep08CoefficientIdentity07 :
    row18_reducedY22_combinationStep08Coefficient07 =
      row18_reducedY22_combinationStep07Coefficient07 +
        row18_reducedY22_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep08Coefficient07 row18_reducedY22_combinationStep07Coefficient07 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep08Coefficient08 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep08CoefficientIdentity08 :
    row18_reducedY22_combinationStep08Coefficient08 =
      row18_reducedY22_combinationStep07Coefficient08 +
        row18_reducedY22_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep08Coefficient08 row18_reducedY22_combinationStep07Coefficient08 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep08Coefficient09 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep08CoefficientIdentity09 :
    row18_reducedY22_combinationStep08Coefficient09 =
      row18_reducedY22_combinationStep07Coefficient09 +
        row18_reducedY22_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep08Coefficient09 row18_reducedY22_combinationStep07Coefficient09 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep08Coefficient10 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep08CoefficientIdentity10 :
    row18_reducedY22_combinationStep08Coefficient10 =
      row18_reducedY22_combinationStep07Coefficient10 +
        row18_reducedY22_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep08Coefficient10 row18_reducedY22_combinationStep07Coefficient10 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep08Coefficient11 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep08CoefficientIdentity11 :
    row18_reducedY22_combinationStep08Coefficient11 =
      row18_reducedY22_combinationStep07Coefficient11 +
        row18_reducedY22_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep08Coefficient11 row18_reducedY22_combinationStep07Coefficient11 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep08Coefficient12 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep08CoefficientIdentity12 :
    row18_reducedY22_combinationStep08Coefficient12 =
      row18_reducedY22_combinationStep07Coefficient12 +
        row18_reducedY22_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep08Coefficient12 row18_reducedY22_combinationStep07Coefficient12 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep08Coefficient13 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep08CoefficientIdentity13 :
    row18_reducedY22_combinationStep08Coefficient13 =
      row18_reducedY22_combinationStep07Coefficient13 +
        row18_reducedY22_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep08Coefficient13 row18_reducedY22_combinationStep07Coefficient13 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep08Coefficient14 : ℂ :=
  0

private theorem row18_reducedY22_combinationStep08CoefficientIdentity14 :
    row18_reducedY22_combinationStep08Coefficient14 =
      row18_reducedY22_combinationStep07Coefficient14 +
        row18_reducedY22_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep08Coefficient14 row18_reducedY22_combinationStep07Coefficient14 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY22_combinationStep08Coefficient15 : ℂ :=
  (-(1 : ℂ))

private theorem row18_reducedY22_combinationStep08CoefficientIdentity15 :
    row18_reducedY22_combinationStep08Coefficient15 =
      row18_reducedY22_combinationStep07Coefficient15 +
        row18_reducedY22_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY22_combinationStep08Coefficient15 row18_reducedY22_combinationStep07Coefficient15 row18_reducedY22_combinationStep08Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY22_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY22_combinationStep08Coefficient00) * Y 0 0
      + (row18_reducedY22_combinationStep08Coefficient01) * Y 0 1
      + (row18_reducedY22_combinationStep08Coefficient02) * Y 1 0
      + (row18_reducedY22_combinationStep08Coefficient03) * Y 1 1
      + (row18_reducedY22_combinationStep08Coefficient04) * Y 2 2
      + (row18_reducedY22_combinationStep08Coefficient05) * Y 2 3
      + (row18_reducedY22_combinationStep08Coefficient06) * Y 3 2
      + (row18_reducedY22_combinationStep08Coefficient07) * Y 3 3
      + (row18_reducedY22_combinationStep08Coefficient08) * Y 4 4
      + (row18_reducedY22_combinationStep08Coefficient09) * Y 4 5
      + (row18_reducedY22_combinationStep08Coefficient10) * Y 5 4
      + (row18_reducedY22_combinationStep08Coefficient11) * Y 5 5
      + (row18_reducedY22_combinationStep08Coefficient12) * Y 6 6
      + (row18_reducedY22_combinationStep08Coefficient13) * Y 6 7
      + (row18_reducedY22_combinationStep08Coefficient14) * Y 7 6
      + (row18_reducedY22_combinationStep08Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY22_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY22_combinationStep08CoefficientIdentity00,
      row18_reducedY22_combinationStep08CoefficientIdentity01,
      row18_reducedY22_combinationStep08CoefficientIdentity02,
      row18_reducedY22_combinationStep08CoefficientIdentity03,
      row18_reducedY22_combinationStep08CoefficientIdentity04,
      row18_reducedY22_combinationStep08CoefficientIdentity05,
      row18_reducedY22_combinationStep08CoefficientIdentity06,
      row18_reducedY22_combinationStep08CoefficientIdentity07,
      row18_reducedY22_combinationStep08CoefficientIdentity08,
      row18_reducedY22_combinationStep08CoefficientIdentity09,
      row18_reducedY22_combinationStep08CoefficientIdentity10,
      row18_reducedY22_combinationStep08CoefficientIdentity11,
      row18_reducedY22_combinationStep08CoefficientIdentity12,
      row18_reducedY22_combinationStep08CoefficientIdentity13,
      row18_reducedY22_combinationStep08CoefficientIdentity14,
      row18_reducedY22_combinationStep08CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY22_combinationStep08Multiplier * equation

theorem row18_reducedY22
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 2 2 = Y 7 7 := by
  have reduced :=
    row18_reducedY22_combinationStep08 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY22_combinationStep08Coefficient00,
      row18_reducedY22_combinationStep08Coefficient01,
      row18_reducedY22_combinationStep08Coefficient02,
      row18_reducedY22_combinationStep08Coefficient03,
      row18_reducedY22_combinationStep08Coefficient04,
      row18_reducedY22_combinationStep08Coefficient05,
      row18_reducedY22_combinationStep08Coefficient06,
      row18_reducedY22_combinationStep08Coefficient07,
      row18_reducedY22_combinationStep08Coefficient08,
      row18_reducedY22_combinationStep08Coefficient09,
      row18_reducedY22_combinationStep08Coefficient10,
      row18_reducedY22_combinationStep08Coefficient11,
      row18_reducedY22_combinationStep08Coefficient12,
      row18_reducedY22_combinationStep08Coefficient13,
      row18_reducedY22_combinationStep08Coefficient14,
      row18_reducedY22_combinationStep08Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
