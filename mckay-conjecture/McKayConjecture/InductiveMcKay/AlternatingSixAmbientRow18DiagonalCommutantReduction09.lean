/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction08

/-!
# Ambient row 18 commutant reduction 09

This generated module checks the reduced relation `reducedY45` for
matrix coordinate (4, 5).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY45_combinationStep00Multiplier : ℂ :=
  (-((72476 / 1185) : ℂ) + ((13822 / 237) : ℂ) * ζ ^ 1 - ((55832 / 1185) : ℂ) * ζ ^ 2 - ((60146 / 1185) : ℂ) * ζ ^ 3 - ((33826 / 395) : ℂ) * ζ ^ 6 - ((15682 / 1185) : ℂ) * ζ ^ 8 - ((7554 / 79) : ℂ) * ζ ^ 9 - ((34832 / 1185) : ℂ) * ζ ^ 11 - ((45646 / 1185) : ℂ) * ζ ^ 12 - ((13822 / 237) : ℂ) * ζ ^ 13 - ((60146 / 1185) : ℂ) * ζ ^ 15 - ((13822 / 237) : ℂ) * ζ ^ 17 - ((5548 / 395) : ℂ) * ζ ^ 18 - ((13822 / 237) : ℂ) * ζ ^ 21 + ((55832 / 1185) : ℂ) * ζ ^ 22 - ((55832 / 1185) : ℂ) * ζ ^ 24 + ((13822 / 237) : ℂ) * ζ ^ 25 - ((34832 / 1185) : ℂ) * ζ ^ 27 + ((15682 / 1185) : ℂ) * ζ ^ 28 + ((13822 / 237) : ℂ) * ζ ^ 29 - ((23838 / 395) : ℂ) * ζ ^ 30 + ((34832 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY45_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep00CoefficientIdentity00 :
    row18_reducedY45_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep00Coefficient00 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep00Coefficient01 : ℂ :=
  (((25 / 158) : ℂ) + ((22 / 79) : ℂ) * ζ ^ 1 + ((211 / 79) : ℂ) * ζ ^ 2 - ((67 / 474) : ℂ) * ζ ^ 3 + ((218 / 79) : ℂ) * ζ ^ 5 + ((1480 / 237) : ℂ) * ζ ^ 6 + ((1381 / 474) : ℂ) * ζ ^ 8 + ((290 / 79) : ℂ) * ζ ^ 9 + ((1807 / 474) : ℂ) * ζ ^ 11 + ((1381 / 474) : ℂ) * ζ ^ 12 - ((22 / 79) : ℂ) * ζ ^ 13 + ((1243 / 474) : ℂ) * ζ ^ 15 - ((22 / 79) : ℂ) * ζ ^ 17 - ((847 / 237) : ℂ) * ζ ^ 18 - ((65 / 474) : ℂ) * ζ ^ 21 - ((211 / 79) : ℂ) * ζ ^ 22 - ((196 / 79) : ℂ) * ζ ^ 25 + ((65 / 474) : ℂ) * ζ ^ 27 - ((1381 / 474) : ℂ) * ζ ^ 28 + ((22 / 79) : ℂ) * ζ ^ 29 + ((740 / 237) : ℂ) * ζ ^ 30 - ((1807 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep00CoefficientIdentity01 :
    row18_reducedY45_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep00Coefficient01 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 (-((1024539 / 62410) : ℂ) + ((420723 / 31205) : ℂ) * ζ ^ 1 - ((4128491 / 187230) : ℂ) * ζ ^ 2 - ((1230491 / 187230) : ℂ) * ζ ^ 3 + ((787328 / 93615) : ℂ) * ζ ^ 4 - ((2084 / 237) : ℂ) * ζ ^ 5 - ((244489 / 18723) : ℂ) * ζ ^ 6 + ((148534 / 18723) : ℂ) * ζ ^ 7 - ((94838 / 93615) : ℂ) * ζ ^ 8 - ((1331959 / 187230) : ℂ) * ζ ^ 9 + ((57503 / 93615) : ℂ) * ζ ^ 10 - ((758504 / 93615) : ℂ) * ζ ^ 11 + ((3559409 / 187230) : ℂ) * ζ ^ 12 - ((326515 / 18723) : ℂ) * ζ ^ 13 + ((91339 / 31205) : ℂ) * ζ ^ 14 + ((666326 / 93615) : ℂ) * ζ ^ 15 - ((81235 / 18723) : ℂ) * ζ ^ 16 - ((455 / 6241) : ℂ) * ζ ^ 17 + ((297139 / 31205) : ℂ) * ζ ^ 18 - ((1076119 / 187230) : ℂ) * ζ ^ 19 + ((117668 / 31205) : ℂ) * ζ ^ 20 + ((182696 / 93615) : ℂ) * ζ ^ 21 + ((768227 / 93615) : ℂ) * ζ ^ 22 - ((1211951 / 187230) : ℂ) * ζ ^ 23 - ((39529 / 37446) : ℂ) * ζ ^ 24 + ((798361 / 187230) : ℂ) * ζ ^ 25 + ((22897 / 31205) : ℂ) * ζ ^ 26 + ((129104 / 31205) : ℂ) * ζ ^ 27 - ((631687 / 37446) : ℂ) * ζ ^ 28 + ((483618 / 31205) : ℂ) * ζ ^ 29 - ((592144 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep00Coefficient02 : ℂ :=
  (-((152 / 237) : ℂ) - ((635 / 158) : ℂ) * ζ ^ 1 + ((635 / 158) : ℂ) * ζ ^ 3 - ((479 / 158) : ℂ) * ζ ^ 5 + ((977 / 237) : ℂ) * ζ ^ 6 + ((76 / 237) : ℂ) * ζ ^ 8 + ((1063 / 237) : ℂ) * ζ ^ 9 - ((78 / 79) : ℂ) * ζ ^ 11 + ((956 / 237) : ℂ) * ζ ^ 12 + ((635 / 158) : ℂ) * ζ ^ 13 + ((33 / 79) : ℂ) * ζ ^ 15 + ((635 / 158) : ℂ) * ζ ^ 17 + ((17 / 79) : ℂ) * ζ ^ 18 + ((701 / 158) : ℂ) * ζ ^ 21 + ((268 / 79) : ℂ) * ζ ^ 24 - ((78 / 79) : ℂ) * ζ ^ 25 + ((1063 / 237) : ℂ) * ζ ^ 27 - ((76 / 237) : ℂ) * ζ ^ 28 - ((635 / 158) : ℂ) * ζ ^ 29 + ((977 / 237) : ℂ) * ζ ^ 30 + ((78 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep00CoefficientIdentity02 :
    row18_reducedY45_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep00Coefficient02 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 (-((1425718 / 93615) : ℂ) + ((13143 / 790) : ℂ) * ζ ^ 1 - ((3071989 / 187230) : ℂ) * ζ ^ 2 - ((19453 / 2370) : ℂ) * ζ ^ 3 + ((227341 / 62410) : ℂ) * ζ ^ 4 - ((18353 / 1185) : ℂ) * ζ ^ 5 - ((102487 / 12482) : ℂ) * ζ ^ 6 + ((1061 / 158) : ℂ) * ζ ^ 7 - ((1206709 / 187230) : ℂ) * ζ ^ 8 - ((5177 / 790) : ℂ) * ζ ^ 9 - ((53333 / 31205) : ℂ) * ζ ^ 10 - ((5582 / 1185) : ℂ) * ζ ^ 11 - ((119069 / 187230) : ℂ) * ζ ^ 12 - ((11081 / 2370) : ℂ) * ζ ^ 13 - ((404309 / 93615) : ℂ) * ζ ^ 14 + ((3113 / 474) : ℂ) * ζ ^ 15 - ((1572043 / 187230) : ℂ) * ζ ^ 16 + ((1789 / 474) : ℂ) * ζ ^ 17 - ((101551 / 31205) : ℂ) * ζ ^ 18 + ((957 / 395) : ℂ) * ζ ^ 19 - ((195221 / 187230) : ℂ) * ζ ^ 20 - ((422 / 1185) : ℂ) * ζ ^ 21 + ((1335133 / 187230) : ℂ) * ζ ^ 22 - ((5561 / 1185) : ℂ) * ζ ^ 23 - ((195221 / 187230) : ℂ) * ζ ^ 24 + ((4383 / 395) : ℂ) * ζ ^ 25 - ((1159949 / 187230) : ℂ) * ζ ^ 26 - ((1147 / 474) : ℂ) * ζ ^ 27 + ((336761 / 93615) : ℂ) * ζ ^ 28 + ((279 / 790) : ℂ) * ζ ^ 29 - ((8708 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep00CoefficientIdentity03 :
    row18_reducedY45_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep00Coefficient03 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep00CoefficientIdentity04 :
    row18_reducedY45_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep00Coefficient04 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep00CoefficientIdentity05 :
    row18_reducedY45_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep00Coefficient05 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep00CoefficientIdentity06 :
    row18_reducedY45_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep00Coefficient06 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep00CoefficientIdentity07 :
    row18_reducedY45_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep00Coefficient07 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep00CoefficientIdentity08 :
    row18_reducedY45_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep00Coefficient08 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep00CoefficientIdentity09 :
    row18_reducedY45_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep00Coefficient09 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep00CoefficientIdentity10 :
    row18_reducedY45_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep00Coefficient10 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep00CoefficientIdentity11 :
    row18_reducedY45_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep00Coefficient11 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep00CoefficientIdentity12 :
    row18_reducedY45_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep00Coefficient12 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep00CoefficientIdentity13 :
    row18_reducedY45_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep00Coefficient13 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep00CoefficientIdentity14 :
    row18_reducedY45_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep00Coefficient14 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep00CoefficientIdentity15 :
    row18_reducedY45_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY45_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep00Coefficient15 row18_reducedY45_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY45_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY45_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY45_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY45_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY45_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY45_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY45_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY45_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY45_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY45_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY45_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY45_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY45_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY45_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY45_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY45_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY45_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY45_combinationStep00CoefficientIdentity00,
      row18_reducedY45_combinationStep00CoefficientIdentity01,
      row18_reducedY45_combinationStep00CoefficientIdentity02,
      row18_reducedY45_combinationStep00CoefficientIdentity03,
      row18_reducedY45_combinationStep00CoefficientIdentity04,
      row18_reducedY45_combinationStep00CoefficientIdentity05,
      row18_reducedY45_combinationStep00CoefficientIdentity06,
      row18_reducedY45_combinationStep00CoefficientIdentity07,
      row18_reducedY45_combinationStep00CoefficientIdentity08,
      row18_reducedY45_combinationStep00CoefficientIdentity09,
      row18_reducedY45_combinationStep00CoefficientIdentity10,
      row18_reducedY45_combinationStep00CoefficientIdentity11,
      row18_reducedY45_combinationStep00CoefficientIdentity12,
      row18_reducedY45_combinationStep00CoefficientIdentity13,
      row18_reducedY45_combinationStep00CoefficientIdentity14,
      row18_reducedY45_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY45_combinationStep00Multiplier * equation

private def row18_reducedY45_combinationStep01Multiplier : ℂ :=
  (-((864 / 395) : ℂ) + ((2174 / 395) : ℂ) * ζ ^ 1 + ((976 / 237) : ℂ) * ζ ^ 2 - ((424 / 395) : ℂ) * ζ ^ 3 + ((8456 / 1185) : ℂ) * ζ ^ 5 + ((2062 / 395) : ℂ) * ζ ^ 8 - ((648 / 395) : ℂ) * ζ ^ 9 + ((1072 / 395) : ℂ) * ζ ^ 11 - ((334 / 395) : ℂ) * ζ ^ 12 - ((2174 / 395) : ℂ) * ζ ^ 13 - ((662 / 1185) : ℂ) * ζ ^ 15 - ((2174 / 395) : ℂ) * ζ ^ 17 - ((976 / 237) : ℂ) * ζ ^ 18 - ((2598 / 395) : ℂ) * ζ ^ 21 - ((976 / 237) : ℂ) * ζ ^ 22 - ((1728 / 395) : ℂ) * ζ ^ 24 - ((1934 / 1185) : ℂ) * ζ ^ 25 - ((2598 / 395) : ℂ) * ζ ^ 27 - ((2062 / 395) : ℂ) * ζ ^ 28 + ((2174 / 395) : ℂ) * ζ ^ 29 - ((496 / 237) : ℂ) * ζ ^ 30 - ((1072 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY45_combinationStep01Coefficient00 : ℂ :=
  (-((461 / 474) : ℂ) - ((341 / 237) : ℂ) * ζ ^ 1 + ((51 / 79) : ℂ) * ζ ^ 2 - ((175 / 474) : ℂ) * ζ ^ 3 - ((69 / 79) : ℂ) * ζ ^ 5 - ((116 / 237) : ℂ) * ζ ^ 6 + ((109 / 158) : ℂ) * ζ ^ 8 + ((475 / 474) : ℂ) * ζ ^ 9 + ((211 / 474) : ℂ) * ζ ^ 11 + ((269 / 237) : ℂ) * ζ ^ 12 + ((341 / 237) : ℂ) * ζ ^ 13 + ((175 / 474) : ℂ) * ζ ^ 15 + ((341 / 237) : ℂ) * ζ ^ 17 + ((155 / 474) : ℂ) * ζ ^ 18 - ((134 / 237) : ℂ) * ζ ^ 21 - ((51 / 79) : ℂ) * ζ ^ 22 - ((51 / 79) : ℂ) * ζ ^ 24 - ((134 / 237) : ℂ) * ζ ^ 25 - ((211 / 474) : ℂ) * ζ ^ 27 - ((109 / 158) : ℂ) * ζ ^ 28 - ((341 / 237) : ℂ) * ζ ^ 29 - ((7 / 158) : ℂ) * ζ ^ 30 - ((211 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep01CoefficientIdentity00 :
    row18_reducedY45_combinationStep01Coefficient00 =
      row18_reducedY45_combinationStep00Coefficient00 +
        row18_reducedY45_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep01Coefficient00 row18_reducedY45_combinationStep00Coefficient00 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 (((288367 / 187230) : ℂ) + ((9418 / 93615) : ℂ) * ζ ^ 1 - ((319279 / 187230) : ℂ) * ζ ^ 2 - ((52421 / 187230) : ℂ) * ζ ^ 3 - ((721 / 474) : ℂ) * ζ ^ 4 - ((257 / 395) : ℂ) * ζ ^ 5 + ((4493 / 2370) : ℂ) * ζ ^ 6 - ((63601 / 93615) : ℂ) * ζ ^ 7 - ((3414 / 6241) : ℂ) * ζ ^ 8 + ((83701 / 187230) : ℂ) * ζ ^ 9 - ((57319 / 187230) : ℂ) * ζ ^ 10 + ((44659 / 62410) : ℂ) * ζ ^ 11 + ((4934 / 18723) : ℂ) * ζ ^ 12 + ((54817 / 62410) : ℂ) * ζ ^ 13 + ((222961 / 187230) : ℂ) * ζ ^ 14 - ((132851 / 187230) : ℂ) * ζ ^ 15 + ((7552 / 18723) : ℂ) * ζ ^ 16 + ((10897 / 62410) : ℂ) * ζ ^ 17 + ((12779 / 37446) : ℂ) * ζ ^ 18 + ((9763 / 31205) : ℂ) * ζ ^ 19 - ((9719 / 93615) : ℂ) * ζ ^ 20 + ((114061 / 187230) : ℂ) * ζ ^ 21 + ((30644 / 93615) : ℂ) * ζ ^ 22 + ((8937 / 12482) : ℂ) * ζ ^ 23 + ((53493 / 62410) : ℂ) * ζ ^ 24 - ((12221 / 12482) : ℂ) * ζ ^ 25 - ((60479 / 187230) : ℂ) * ζ ^ 26 + ((15586 / 18723) : ℂ) * ζ ^ 27 + ((12113 / 62410) : ℂ) * ζ ^ 28 - ((10336 / 31205) : ℂ) * ζ ^ 29 - ((804 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep01Coefficient01 : ℂ :=
  (((190 / 79) : ℂ) - ((103 / 79) : ℂ) * ζ ^ 1 + ((837 / 158) : ℂ) * ζ ^ 2 + ((94 / 237) : ℂ) * ζ ^ 3 + ((695 / 158) : ℂ) * ζ ^ 5 + ((2114 / 237) : ℂ) * ζ ^ 6 + ((735 / 158) : ℂ) * ζ ^ 8 + ((1622 / 237) : ℂ) * ζ ^ 9 + ((1528 / 237) : ℂ) * ζ ^ 11 + ((735 / 158) : ℂ) * ζ ^ 12 + ((103 / 79) : ℂ) * ζ ^ 13 + ((2515 / 474) : ℂ) * ζ ^ 15 + ((103 / 79) : ℂ) * ζ ^ 17 - ((1717 / 474) : ℂ) * ζ ^ 18 + ((215 / 237) : ℂ) * ζ ^ 21 - ((837 / 158) : ℂ) * ζ ^ 22 - ((901 / 158) : ℂ) * ζ ^ 25 - ((215 / 237) : ℂ) * ζ ^ 27 - ((735 / 158) : ℂ) * ζ ^ 28 - ((103 / 79) : ℂ) * ζ ^ 29 + ((1057 / 237) : ℂ) * ζ ^ 30 - ((1528 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep01CoefficientIdentity01 :
    row18_reducedY45_combinationStep01Coefficient01 =
      row18_reducedY45_combinationStep00Coefficient01 +
        row18_reducedY45_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep01Coefficient01 row18_reducedY45_combinationStep00Coefficient01 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 (-((126401 / 62410) : ℂ) + ((93 / 79) : ℂ) * ζ ^ 1 - ((85033 / 37446) : ℂ) * ζ ^ 2 - ((736 / 237) : ℂ) * ζ ^ 3 - ((25886 / 18723) : ℂ) * ζ ^ 4 - ((9983 / 2370) : ℂ) * ζ ^ 5 + ((969 / 62410) : ℂ) * ζ ^ 6 - ((202 / 1185) : ℂ) * ζ ^ 7 - ((261208 / 93615) : ℂ) * ζ ^ 8 + ((267 / 790) : ℂ) * ζ ^ 9 + ((27773 / 187230) : ℂ) * ζ ^ 10 - ((383 / 237) : ℂ) * ζ ^ 11 - ((352919 / 187230) : ℂ) * ζ ^ 12 - ((649 / 2370) : ℂ) * ζ ^ 13 + ((196849 / 187230) : ℂ) * ζ ^ 14 - ((1186 / 1185) : ℂ) * ζ ^ 15 - ((3088 / 31205) : ℂ) * ζ ^ 16 - ((872 / 1185) : ℂ) * ζ ^ 17 - ((720623 / 187230) : ℂ) * ζ ^ 18 + ((4451 / 1185) : ℂ) * ζ ^ 19 + ((151049 / 93615) : ℂ) * ζ ^ 20 - ((463 / 237) : ℂ) * ζ ^ 21 + ((159269 / 187230) : ℂ) * ζ ^ 22 + ((643 / 474) : ℂ) * ζ ^ 23 - ((77503 / 187230) : ℂ) * ζ ^ 24 + ((157 / 395) : ℂ) * ζ ^ 25 - ((18327 / 31205) : ℂ) * ζ ^ 26 + ((242 / 1185) : ℂ) * ζ ^ 27 + ((16154 / 31205) : ℂ) * ζ ^ 28 - ((464 / 1185) : ℂ) * ζ ^ 29 - ((7504 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep01Coefficient02 : ℂ :=
  (-((152 / 237) : ℂ) - ((635 / 158) : ℂ) * ζ ^ 1 + ((635 / 158) : ℂ) * ζ ^ 3 - ((479 / 158) : ℂ) * ζ ^ 5 + ((977 / 237) : ℂ) * ζ ^ 6 + ((76 / 237) : ℂ) * ζ ^ 8 + ((1063 / 237) : ℂ) * ζ ^ 9 - ((78 / 79) : ℂ) * ζ ^ 11 + ((956 / 237) : ℂ) * ζ ^ 12 + ((635 / 158) : ℂ) * ζ ^ 13 + ((33 / 79) : ℂ) * ζ ^ 15 + ((635 / 158) : ℂ) * ζ ^ 17 + ((17 / 79) : ℂ) * ζ ^ 18 + ((701 / 158) : ℂ) * ζ ^ 21 + ((268 / 79) : ℂ) * ζ ^ 24 - ((78 / 79) : ℂ) * ζ ^ 25 + ((1063 / 237) : ℂ) * ζ ^ 27 - ((76 / 237) : ℂ) * ζ ^ 28 - ((635 / 158) : ℂ) * ζ ^ 29 + ((977 / 237) : ℂ) * ζ ^ 30 + ((78 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep01CoefficientIdentity02 :
    row18_reducedY45_combinationStep01Coefficient02 =
      row18_reducedY45_combinationStep00Coefficient02 +
        row18_reducedY45_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep01Coefficient02 row18_reducedY45_combinationStep00Coefficient02 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep01Coefficient03 : ℂ :=
  (((461 / 474) : ℂ) + ((341 / 237) : ℂ) * ζ ^ 1 - ((51 / 79) : ℂ) * ζ ^ 2 + ((175 / 474) : ℂ) * ζ ^ 3 + ((69 / 79) : ℂ) * ζ ^ 5 + ((116 / 237) : ℂ) * ζ ^ 6 - ((109 / 158) : ℂ) * ζ ^ 8 - ((475 / 474) : ℂ) * ζ ^ 9 - ((211 / 474) : ℂ) * ζ ^ 11 - ((269 / 237) : ℂ) * ζ ^ 12 - ((341 / 237) : ℂ) * ζ ^ 13 - ((175 / 474) : ℂ) * ζ ^ 15 - ((341 / 237) : ℂ) * ζ ^ 17 - ((155 / 474) : ℂ) * ζ ^ 18 + ((134 / 237) : ℂ) * ζ ^ 21 + ((51 / 79) : ℂ) * ζ ^ 22 + ((51 / 79) : ℂ) * ζ ^ 24 + ((134 / 237) : ℂ) * ζ ^ 25 + ((211 / 474) : ℂ) * ζ ^ 27 + ((109 / 158) : ℂ) * ζ ^ 28 + ((341 / 237) : ℂ) * ζ ^ 29 + ((7 / 158) : ℂ) * ζ ^ 30 + ((211 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep01CoefficientIdentity03 :
    row18_reducedY45_combinationStep01Coefficient03 =
      row18_reducedY45_combinationStep00Coefficient03 +
        row18_reducedY45_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep01Coefficient03 row18_reducedY45_combinationStep00Coefficient03 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 (-((288367 / 187230) : ℂ) - ((9418 / 93615) : ℂ) * ζ ^ 1 + ((319279 / 187230) : ℂ) * ζ ^ 2 + ((52421 / 187230) : ℂ) * ζ ^ 3 + ((721 / 474) : ℂ) * ζ ^ 4 + ((257 / 395) : ℂ) * ζ ^ 5 - ((4493 / 2370) : ℂ) * ζ ^ 6 + ((63601 / 93615) : ℂ) * ζ ^ 7 + ((3414 / 6241) : ℂ) * ζ ^ 8 - ((83701 / 187230) : ℂ) * ζ ^ 9 + ((57319 / 187230) : ℂ) * ζ ^ 10 - ((44659 / 62410) : ℂ) * ζ ^ 11 - ((4934 / 18723) : ℂ) * ζ ^ 12 - ((54817 / 62410) : ℂ) * ζ ^ 13 - ((222961 / 187230) : ℂ) * ζ ^ 14 + ((132851 / 187230) : ℂ) * ζ ^ 15 - ((7552 / 18723) : ℂ) * ζ ^ 16 - ((10897 / 62410) : ℂ) * ζ ^ 17 - ((12779 / 37446) : ℂ) * ζ ^ 18 - ((9763 / 31205) : ℂ) * ζ ^ 19 + ((9719 / 93615) : ℂ) * ζ ^ 20 - ((114061 / 187230) : ℂ) * ζ ^ 21 - ((30644 / 93615) : ℂ) * ζ ^ 22 - ((8937 / 12482) : ℂ) * ζ ^ 23 - ((53493 / 62410) : ℂ) * ζ ^ 24 + ((12221 / 12482) : ℂ) * ζ ^ 25 + ((60479 / 187230) : ℂ) * ζ ^ 26 - ((15586 / 18723) : ℂ) * ζ ^ 27 - ((12113 / 62410) : ℂ) * ζ ^ 28 + ((10336 / 31205) : ℂ) * ζ ^ 29 + ((804 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep01CoefficientIdentity04 :
    row18_reducedY45_combinationStep01Coefficient04 =
      row18_reducedY45_combinationStep00Coefficient04 +
        row18_reducedY45_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep01Coefficient04 row18_reducedY45_combinationStep00Coefficient04 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep01CoefficientIdentity05 :
    row18_reducedY45_combinationStep01Coefficient05 =
      row18_reducedY45_combinationStep00Coefficient05 +
        row18_reducedY45_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep01Coefficient05 row18_reducedY45_combinationStep00Coefficient05 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep01CoefficientIdentity06 :
    row18_reducedY45_combinationStep01Coefficient06 =
      row18_reducedY45_combinationStep00Coefficient06 +
        row18_reducedY45_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep01Coefficient06 row18_reducedY45_combinationStep00Coefficient06 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep01CoefficientIdentity07 :
    row18_reducedY45_combinationStep01Coefficient07 =
      row18_reducedY45_combinationStep00Coefficient07 +
        row18_reducedY45_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep01Coefficient07 row18_reducedY45_combinationStep00Coefficient07 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep01CoefficientIdentity08 :
    row18_reducedY45_combinationStep01Coefficient08 =
      row18_reducedY45_combinationStep00Coefficient08 +
        row18_reducedY45_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep01Coefficient08 row18_reducedY45_combinationStep00Coefficient08 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep01CoefficientIdentity09 :
    row18_reducedY45_combinationStep01Coefficient09 =
      row18_reducedY45_combinationStep00Coefficient09 +
        row18_reducedY45_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep01Coefficient09 row18_reducedY45_combinationStep00Coefficient09 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep01CoefficientIdentity10 :
    row18_reducedY45_combinationStep01Coefficient10 =
      row18_reducedY45_combinationStep00Coefficient10 +
        row18_reducedY45_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep01Coefficient10 row18_reducedY45_combinationStep00Coefficient10 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep01CoefficientIdentity11 :
    row18_reducedY45_combinationStep01Coefficient11 =
      row18_reducedY45_combinationStep00Coefficient11 +
        row18_reducedY45_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep01Coefficient11 row18_reducedY45_combinationStep00Coefficient11 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep01CoefficientIdentity12 :
    row18_reducedY45_combinationStep01Coefficient12 =
      row18_reducedY45_combinationStep00Coefficient12 +
        row18_reducedY45_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep01Coefficient12 row18_reducedY45_combinationStep00Coefficient12 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep01CoefficientIdentity13 :
    row18_reducedY45_combinationStep01Coefficient13 =
      row18_reducedY45_combinationStep00Coefficient13 +
        row18_reducedY45_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep01Coefficient13 row18_reducedY45_combinationStep00Coefficient13 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep01CoefficientIdentity14 :
    row18_reducedY45_combinationStep01Coefficient14 =
      row18_reducedY45_combinationStep00Coefficient14 +
        row18_reducedY45_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep01Coefficient14 row18_reducedY45_combinationStep00Coefficient14 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep01CoefficientIdentity15 :
    row18_reducedY45_combinationStep01Coefficient15 =
      row18_reducedY45_combinationStep00Coefficient15 +
        row18_reducedY45_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep01Coefficient15 row18_reducedY45_combinationStep00Coefficient15 row18_reducedY45_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY45_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY45_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY45_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY45_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY45_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY45_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY45_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY45_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY45_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY45_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY45_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY45_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY45_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY45_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY45_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY45_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY45_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY45_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY45_combinationStep01CoefficientIdentity00,
      row18_reducedY45_combinationStep01CoefficientIdentity01,
      row18_reducedY45_combinationStep01CoefficientIdentity02,
      row18_reducedY45_combinationStep01CoefficientIdentity03,
      row18_reducedY45_combinationStep01CoefficientIdentity04,
      row18_reducedY45_combinationStep01CoefficientIdentity05,
      row18_reducedY45_combinationStep01CoefficientIdentity06,
      row18_reducedY45_combinationStep01CoefficientIdentity07,
      row18_reducedY45_combinationStep01CoefficientIdentity08,
      row18_reducedY45_combinationStep01CoefficientIdentity09,
      row18_reducedY45_combinationStep01CoefficientIdentity10,
      row18_reducedY45_combinationStep01CoefficientIdentity11,
      row18_reducedY45_combinationStep01CoefficientIdentity12,
      row18_reducedY45_combinationStep01CoefficientIdentity13,
      row18_reducedY45_combinationStep01CoefficientIdentity14,
      row18_reducedY45_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY45_combinationStep01Multiplier * equation

private def row18_reducedY45_combinationStep02Multiplier : ℂ :=
  (((6304 / 1185) : ℂ) - ((704 / 395) : ℂ) * ζ ^ 1 - ((12178 / 1185) : ℂ) * ζ ^ 2 - ((404 / 237) : ℂ) * ζ ^ 3 - ((14656 / 1185) : ℂ) * ζ ^ 5 - ((1894 / 395) : ℂ) * ζ ^ 6 - ((17272 / 1185) : ℂ) * ζ ^ 8 - ((5216 / 1185) : ℂ) * ζ ^ 9 - ((776 / 79) : ℂ) * ζ ^ 11 - ((6496 / 1185) : ℂ) * ζ ^ 12 + ((704 / 395) : ℂ) * ζ ^ 13 + ((404 / 237) : ℂ) * ζ ^ 15 + ((704 / 395) : ℂ) * ζ ^ 17 + ((1958 / 395) : ℂ) * ζ ^ 18 + ((12544 / 1185) : ℂ) * ζ ^ 21 + ((12178 / 1185) : ℂ) * ζ ^ 22 + ((12178 / 1185) : ℂ) * ζ ^ 24 + ((12544 / 1185) : ℂ) * ζ ^ 25 + ((776 / 79) : ℂ) * ζ ^ 27 + ((17272 / 1185) : ℂ) * ζ ^ 28 - ((704 / 395) : ℂ) * ζ ^ 29 + ((1698 / 395) : ℂ) * ζ ^ 30 + ((776 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY45_combinationStep02Coefficient00 : ℂ :=
  (-((21 / 10) : ℂ) + ((3527 / 2370) : ℂ) * ζ ^ 1 + ((1759 / 395) : ℂ) * ζ ^ 2 - ((667 / 474) : ℂ) * ζ ^ 3 + ((6953 / 1185) : ℂ) * ζ ^ 5 + ((32 / 15) : ℂ) * ζ ^ 6 + ((14761 / 2370) : ℂ) * ζ ^ 8 + ((571 / 395) : ℂ) * ζ ^ 9 + ((1214 / 237) : ℂ) * ζ ^ 11 + ((2749 / 1185) : ℂ) * ζ ^ 12 - ((3527 / 2370) : ℂ) * ζ ^ 13 + ((667 / 474) : ℂ) * ζ ^ 15 - ((3527 / 2370) : ℂ) * ζ ^ 17 - ((1859 / 790) : ℂ) * ζ ^ 18 - ((10379 / 2370) : ℂ) * ζ ^ 21 - ((1759 / 395) : ℂ) * ζ ^ 22 - ((1759 / 395) : ℂ) * ζ ^ 24 - ((10379 / 2370) : ℂ) * ζ ^ 25 - ((1214 / 237) : ℂ) * ζ ^ 27 - ((14761 / 2370) : ℂ) * ζ ^ 28 + ((3527 / 2370) : ℂ) * ζ ^ 29 - ((4207 / 2370) : ℂ) * ζ ^ 30 - ((1214 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep02CoefficientIdentity00 :
    row18_reducedY45_combinationStep02Coefficient00 =
      row18_reducedY45_combinationStep01Coefficient00 +
        row18_reducedY45_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep02Coefficient00 row18_reducedY45_combinationStep01Coefficient00 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 (((86632 / 93615) : ℂ) - ((166893 / 62410) : ℂ) * ζ ^ 1 - ((459682 / 93615) : ℂ) * ζ ^ 2 + ((15703 / 12482) : ℂ) * ζ ^ 3 + ((331079 / 187230) : ℂ) * ζ ^ 4 - ((131941 / 37446) : ℂ) * ζ ^ 5 + ((149482 / 93615) : ℂ) * ζ ^ 6 + ((505567 / 187230) : ℂ) * ζ ^ 7 - ((118869 / 31205) : ℂ) * ζ ^ 8 + ((46483 / 18723) : ℂ) * ζ ^ 9 + ((345197 / 187230) : ℂ) * ζ ^ 10 - ((824969 / 187230) : ℂ) * ζ ^ 11 + ((5459 / 1185) : ℂ) * ζ ^ 12 - ((8328 / 31205) : ℂ) * ζ ^ 13 - ((287153 / 62410) : ℂ) * ζ ^ 14 + ((806111 / 187230) : ℂ) * ζ ^ 15 - ((389143 / 187230) : ℂ) * ζ ^ 16 - ((457141 / 187230) : ℂ) * ζ ^ 17 + ((69448 / 18723) : ℂ) * ζ ^ 18 - ((42421 / 93615) : ℂ) * ζ ^ 19 + ((28714 / 31205) : ℂ) * ζ ^ 20 + ((92846 / 31205) : ℂ) * ζ ^ 21 + ((35765 / 37446) : ℂ) * ζ ^ 22 + ((517 / 12482) : ℂ) * ζ ^ 23 + ((326 / 31205) : ℂ) * ζ ^ 24 + ((129409 / 187230) : ℂ) * ζ ^ 25 - ((163277 / 187230) : ℂ) * ζ ^ 26 - ((37883 / 187230) : ℂ) * ζ ^ 27 + ((1414 / 31205) : ℂ) * ζ ^ 28 - ((9577 / 31205) : ℂ) * ζ ^ 29 + ((2716 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep02Coefficient01 : ℂ :=
  (-((665 / 158) : ℂ) + ((1750 / 237) : ℂ) * ζ ^ 1 - ((5525 / 474) : ℂ) * ζ ^ 2 - ((2605 / 474) : ℂ) * ζ ^ 3 - ((1234 / 237) : ℂ) * ζ ^ 5 - ((1005 / 79) : ℂ) * ζ ^ 6 - ((3997 / 474) : ℂ) * ζ ^ 8 - ((2267 / 158) : ℂ) * ζ ^ 9 - ((2098 / 237) : ℂ) * ζ ^ 11 - ((3997 / 474) : ℂ) * ζ ^ 12 - ((1750 / 237) : ℂ) * ζ ^ 13 - ((1121 / 158) : ℂ) * ζ ^ 15 - ((1750 / 237) : ℂ) * ζ ^ 17 + ((505 / 474) : ℂ) * ζ ^ 18 - ((895 / 474) : ℂ) * ζ ^ 21 + ((5525 / 474) : ℂ) * ζ ^ 22 + ((2984 / 237) : ℂ) * ζ ^ 25 + ((895 / 474) : ℂ) * ζ ^ 27 + ((3997 / 474) : ℂ) * ζ ^ 28 + ((1750 / 237) : ℂ) * ζ ^ 29 - ((1005 / 158) : ℂ) * ζ ^ 30 + ((2098 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep02CoefficientIdentity01 :
    row18_reducedY45_combinationStep02Coefficient01 =
      row18_reducedY45_combinationStep01Coefficient01 +
        row18_reducedY45_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep02Coefficient01 row18_reducedY45_combinationStep01Coefficient01 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 (((485271 / 62410) : ℂ) - ((327899 / 31205) : ℂ) * ζ ^ 1 + ((2872207 / 187230) : ℂ) * ζ ^ 2 + ((270593 / 31205) : ℂ) * ζ ^ 3 - ((145222 / 18723) : ℂ) * ζ ^ 4 + ((2824873 / 187230) : ℂ) * ζ ^ 5 + ((191591 / 18723) : ℂ) * ζ ^ 6 - ((506414 / 93615) : ℂ) * ζ ^ 7 + ((2455081 / 187230) : ℂ) * ζ ^ 8 + ((947326 / 93615) : ℂ) * ζ ^ 9 - ((381946 / 93615) : ℂ) * ζ ^ 10 + ((241792 / 18723) : ℂ) * ζ ^ 11 + ((213989 / 31205) : ℂ) * ζ ^ 12 - ((260807 / 187230) : ℂ) * ζ ^ 13 + ((2582083 / 187230) : ℂ) * ζ ^ 14 + ((263612 / 93615) : ℂ) * ζ ^ 15 - ((9467 / 12482) : ℂ) * ζ ^ 16 + ((902887 / 62410) : ℂ) * ζ ^ 17 + ((135223 / 62410) : ℂ) * ζ ^ 18 - ((62077 / 37446) : ℂ) * ζ ^ 19 + ((472987 / 37446) : ℂ) * ζ ^ 20 + ((701927 / 187230) : ℂ) * ζ ^ 21 - ((655991 / 187230) : ℂ) * ζ ^ 22 + ((670382 / 93615) : ℂ) * ζ ^ 23 + ((311443 / 93615) : ℂ) * ζ ^ 24 - ((829163 / 187230) : ℂ) * ζ ^ 25 + ((26711 / 6241) : ℂ) * ζ ^ 26 + ((292709 / 187230) : ℂ) * ζ ^ 27 - ((12363 / 6241) : ℂ) * ζ ^ 28 + ((115797 / 62410) : ℂ) * ζ ^ 29 + ((2522 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep02Coefficient02 : ℂ :=
  (-((152 / 237) : ℂ) - ((635 / 158) : ℂ) * ζ ^ 1 + ((635 / 158) : ℂ) * ζ ^ 3 - ((479 / 158) : ℂ) * ζ ^ 5 + ((977 / 237) : ℂ) * ζ ^ 6 + ((76 / 237) : ℂ) * ζ ^ 8 + ((1063 / 237) : ℂ) * ζ ^ 9 - ((78 / 79) : ℂ) * ζ ^ 11 + ((956 / 237) : ℂ) * ζ ^ 12 + ((635 / 158) : ℂ) * ζ ^ 13 + ((33 / 79) : ℂ) * ζ ^ 15 + ((635 / 158) : ℂ) * ζ ^ 17 + ((17 / 79) : ℂ) * ζ ^ 18 + ((701 / 158) : ℂ) * ζ ^ 21 + ((268 / 79) : ℂ) * ζ ^ 24 - ((78 / 79) : ℂ) * ζ ^ 25 + ((1063 / 237) : ℂ) * ζ ^ 27 - ((76 / 237) : ℂ) * ζ ^ 28 - ((635 / 158) : ℂ) * ζ ^ 29 + ((977 / 237) : ℂ) * ζ ^ 30 + ((78 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep02CoefficientIdentity02 :
    row18_reducedY45_combinationStep02Coefficient02 =
      row18_reducedY45_combinationStep01Coefficient02 +
        row18_reducedY45_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep02Coefficient02 row18_reducedY45_combinationStep01Coefficient02 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep02Coefficient03 : ℂ :=
  (((461 / 474) : ℂ) + ((341 / 237) : ℂ) * ζ ^ 1 - ((51 / 79) : ℂ) * ζ ^ 2 + ((175 / 474) : ℂ) * ζ ^ 3 + ((69 / 79) : ℂ) * ζ ^ 5 + ((116 / 237) : ℂ) * ζ ^ 6 - ((109 / 158) : ℂ) * ζ ^ 8 - ((475 / 474) : ℂ) * ζ ^ 9 - ((211 / 474) : ℂ) * ζ ^ 11 - ((269 / 237) : ℂ) * ζ ^ 12 - ((341 / 237) : ℂ) * ζ ^ 13 - ((175 / 474) : ℂ) * ζ ^ 15 - ((341 / 237) : ℂ) * ζ ^ 17 - ((155 / 474) : ℂ) * ζ ^ 18 + ((134 / 237) : ℂ) * ζ ^ 21 + ((51 / 79) : ℂ) * ζ ^ 22 + ((51 / 79) : ℂ) * ζ ^ 24 + ((134 / 237) : ℂ) * ζ ^ 25 + ((211 / 474) : ℂ) * ζ ^ 27 + ((109 / 158) : ℂ) * ζ ^ 28 + ((341 / 237) : ℂ) * ζ ^ 29 + ((7 / 158) : ℂ) * ζ ^ 30 + ((211 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep02CoefficientIdentity03 :
    row18_reducedY45_combinationStep02Coefficient03 =
      row18_reducedY45_combinationStep01Coefficient03 +
        row18_reducedY45_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep02Coefficient03 row18_reducedY45_combinationStep01Coefficient03 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep02Coefficient04 : ℂ :=
  (((1336 / 1185) : ℂ) - ((6937 / 2370) : ℂ) * ζ ^ 1 - ((1504 / 395) : ℂ) * ζ ^ 2 + ((82 / 79) : ℂ) * ζ ^ 3 - ((7988 / 1185) : ℂ) * ζ ^ 5 - ((1036 / 395) : ℂ) * ζ ^ 6 - ((6563 / 1185) : ℂ) * ζ ^ 8 - ((1051 / 2370) : ℂ) * ζ ^ 9 - ((739 / 158) : ℂ) * ζ ^ 11 - ((468 / 395) : ℂ) * ζ ^ 12 + ((6937 / 2370) : ℂ) * ζ ^ 13 - ((82 / 79) : ℂ) * ζ ^ 15 + ((6937 / 2370) : ℂ) * ζ ^ 17 + ((3176 / 1185) : ℂ) * ζ ^ 18 + ((3013 / 790) : ℂ) * ζ ^ 21 + ((1504 / 395) : ℂ) * ζ ^ 22 + ((1504 / 395) : ℂ) * ζ ^ 24 + ((3013 / 790) : ℂ) * ζ ^ 25 + ((739 / 158) : ℂ) * ζ ^ 27 + ((6563 / 1185) : ℂ) * ζ ^ 28 - ((6937 / 2370) : ℂ) * ζ ^ 29 + ((2051 / 1185) : ℂ) * ζ ^ 30 + ((739 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep02CoefficientIdentity04 :
    row18_reducedY45_combinationStep02Coefficient04 =
      row18_reducedY45_combinationStep01Coefficient04 +
        row18_reducedY45_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep02Coefficient04 row18_reducedY45_combinationStep01Coefficient04 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 (-((86632 / 93615) : ℂ) + ((166893 / 62410) : ℂ) * ζ ^ 1 + ((459682 / 93615) : ℂ) * ζ ^ 2 - ((15703 / 12482) : ℂ) * ζ ^ 3 - ((331079 / 187230) : ℂ) * ζ ^ 4 + ((131941 / 37446) : ℂ) * ζ ^ 5 - ((149482 / 93615) : ℂ) * ζ ^ 6 - ((505567 / 187230) : ℂ) * ζ ^ 7 + ((118869 / 31205) : ℂ) * ζ ^ 8 - ((46483 / 18723) : ℂ) * ζ ^ 9 - ((345197 / 187230) : ℂ) * ζ ^ 10 + ((824969 / 187230) : ℂ) * ζ ^ 11 - ((5459 / 1185) : ℂ) * ζ ^ 12 + ((8328 / 31205) : ℂ) * ζ ^ 13 + ((287153 / 62410) : ℂ) * ζ ^ 14 - ((806111 / 187230) : ℂ) * ζ ^ 15 + ((389143 / 187230) : ℂ) * ζ ^ 16 + ((457141 / 187230) : ℂ) * ζ ^ 17 - ((69448 / 18723) : ℂ) * ζ ^ 18 + ((42421 / 93615) : ℂ) * ζ ^ 19 - ((28714 / 31205) : ℂ) * ζ ^ 20 - ((92846 / 31205) : ℂ) * ζ ^ 21 - ((35765 / 37446) : ℂ) * ζ ^ 22 - ((517 / 12482) : ℂ) * ζ ^ 23 - ((326 / 31205) : ℂ) * ζ ^ 24 - ((129409 / 187230) : ℂ) * ζ ^ 25 + ((163277 / 187230) : ℂ) * ζ ^ 26 + ((37883 / 187230) : ℂ) * ζ ^ 27 - ((1414 / 31205) : ℂ) * ζ ^ 28 + ((9577 / 31205) : ℂ) * ζ ^ 29 - ((2716 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep02CoefficientIdentity05 :
    row18_reducedY45_combinationStep02Coefficient05 =
      row18_reducedY45_combinationStep01Coefficient05 +
        row18_reducedY45_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep02Coefficient05 row18_reducedY45_combinationStep01Coefficient05 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep02Coefficient06 : ℂ :=
  (((1763 / 790) : ℂ) * ζ ^ 1 + ((49 / 395) : ℂ) * ζ ^ 2 + ((1763 / 790) : ℂ) * ζ ^ 3 - ((1883 / 2370) : ℂ) * ζ ^ 5 - ((529 / 395) : ℂ) * ζ ^ 6 + ((43 / 158) : ℂ) * ζ ^ 8 + ((17 / 395) : ℂ) * ζ ^ 9 - ((3586 / 1185) : ℂ) * ζ ^ 11 - ((697 / 237) : ℂ) * ζ ^ 12 - ((1763 / 790) : ℂ) * ζ ^ 13 - ((1273 / 1185) : ℂ) * ζ ^ 15 - ((1763 / 790) : ℂ) * ζ ^ 17 - ((49 / 790) : ℂ) * ζ ^ 18 - ((2743 / 2370) : ℂ) * ζ ^ 21 - ((49 / 395) : ℂ) * ζ ^ 22 + ((697 / 237) : ℂ) * ζ ^ 24 + ((3586 / 1185) : ℂ) * ζ ^ 25 - ((17 / 395) : ℂ) * ζ ^ 27 - ((43 / 158) : ℂ) * ζ ^ 28 + ((1763 / 790) : ℂ) * ζ ^ 29 + ((578 / 395) : ℂ) * ζ ^ 30 + ((3586 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep02CoefficientIdentity06 :
    row18_reducedY45_combinationStep02Coefficient06 =
      row18_reducedY45_combinationStep01Coefficient06 +
        row18_reducedY45_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep02Coefficient06 row18_reducedY45_combinationStep01Coefficient06 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 (-((59888 / 93615) : ℂ) - ((336727 / 187230) : ℂ) * ζ ^ 1 + ((26626 / 31205) : ℂ) * ζ ^ 2 - ((185672 / 93615) : ℂ) * ζ ^ 3 + ((49427 / 62410) : ℂ) * ζ ^ 4 + ((314461 / 93615) : ℂ) * ζ ^ 5 - ((13862 / 93615) : ℂ) * ζ ^ 6 + ((450923 / 187230) : ℂ) * ζ ^ 7 + ((75461 / 37446) : ℂ) * ζ ^ 8 - ((80254 / 31205) : ℂ) * ζ ^ 9 - ((119713 / 62410) : ℂ) * ζ ^ 10 - ((14063 / 12482) : ℂ) * ζ ^ 11 - ((6181 / 187230) : ℂ) * ζ ^ 12 + ((62197 / 62410) : ℂ) * ζ ^ 13 + ((108049 / 187230) : ℂ) * ζ ^ 14 - ((5915 / 18723) : ℂ) * ζ ^ 15 - ((56443 / 31205) : ℂ) * ζ ^ 16 - ((30862 / 31205) : ℂ) * ζ ^ 17 - ((81691 / 187230) : ℂ) * ζ ^ 18 + ((30076 / 93615) : ℂ) * ζ ^ 19 + ((148201 / 93615) : ℂ) * ζ ^ 20 - ((54907 / 93615) : ℂ) * ζ ^ 21 + ((40768 / 93615) : ℂ) * ζ ^ 22 + ((39993 / 62410) : ℂ) * ζ ^ 23 - ((43036 / 18723) : ℂ) * ζ ^ 24 + ((49081 / 93615) : ℂ) * ζ ^ 25 + ((54409 / 62410) : ℂ) * ζ ^ 26 - ((77139 / 62410) : ℂ) * ζ ^ 27 + ((30346 / 31205) : ℂ) * ζ ^ 28 + ((21171 / 12482) : ℂ) * ζ ^ 29 + ((2910 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep02CoefficientIdentity07 :
    row18_reducedY45_combinationStep02Coefficient07 =
      row18_reducedY45_combinationStep01Coefficient07 +
        row18_reducedY45_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep02Coefficient07 row18_reducedY45_combinationStep01Coefficient07 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep02CoefficientIdentity08 :
    row18_reducedY45_combinationStep02Coefficient08 =
      row18_reducedY45_combinationStep01Coefficient08 +
        row18_reducedY45_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep02Coefficient08 row18_reducedY45_combinationStep01Coefficient08 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep02CoefficientIdentity09 :
    row18_reducedY45_combinationStep02Coefficient09 =
      row18_reducedY45_combinationStep01Coefficient09 +
        row18_reducedY45_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep02Coefficient09 row18_reducedY45_combinationStep01Coefficient09 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep02CoefficientIdentity10 :
    row18_reducedY45_combinationStep02Coefficient10 =
      row18_reducedY45_combinationStep01Coefficient10 +
        row18_reducedY45_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep02Coefficient10 row18_reducedY45_combinationStep01Coefficient10 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep02CoefficientIdentity11 :
    row18_reducedY45_combinationStep02Coefficient11 =
      row18_reducedY45_combinationStep01Coefficient11 +
        row18_reducedY45_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep02Coefficient11 row18_reducedY45_combinationStep01Coefficient11 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep02CoefficientIdentity12 :
    row18_reducedY45_combinationStep02Coefficient12 =
      row18_reducedY45_combinationStep01Coefficient12 +
        row18_reducedY45_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep02Coefficient12 row18_reducedY45_combinationStep01Coefficient12 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep02CoefficientIdentity13 :
    row18_reducedY45_combinationStep02Coefficient13 =
      row18_reducedY45_combinationStep01Coefficient13 +
        row18_reducedY45_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep02Coefficient13 row18_reducedY45_combinationStep01Coefficient13 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep02CoefficientIdentity14 :
    row18_reducedY45_combinationStep02Coefficient14 =
      row18_reducedY45_combinationStep01Coefficient14 +
        row18_reducedY45_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep02Coefficient14 row18_reducedY45_combinationStep01Coefficient14 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep02CoefficientIdentity15 :
    row18_reducedY45_combinationStep02Coefficient15 =
      row18_reducedY45_combinationStep01Coefficient15 +
        row18_reducedY45_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep02Coefficient15 row18_reducedY45_combinationStep01Coefficient15 row18_reducedY45_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY45_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY45_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY45_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY45_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY45_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY45_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY45_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY45_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY45_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY45_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY45_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY45_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY45_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY45_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY45_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY45_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY45_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY45_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY45_combinationStep02CoefficientIdentity00,
      row18_reducedY45_combinationStep02CoefficientIdentity01,
      row18_reducedY45_combinationStep02CoefficientIdentity02,
      row18_reducedY45_combinationStep02CoefficientIdentity03,
      row18_reducedY45_combinationStep02CoefficientIdentity04,
      row18_reducedY45_combinationStep02CoefficientIdentity05,
      row18_reducedY45_combinationStep02CoefficientIdentity06,
      row18_reducedY45_combinationStep02CoefficientIdentity07,
      row18_reducedY45_combinationStep02CoefficientIdentity08,
      row18_reducedY45_combinationStep02CoefficientIdentity09,
      row18_reducedY45_combinationStep02CoefficientIdentity10,
      row18_reducedY45_combinationStep02CoefficientIdentity11,
      row18_reducedY45_combinationStep02CoefficientIdentity12,
      row18_reducedY45_combinationStep02CoefficientIdentity13,
      row18_reducedY45_combinationStep02CoefficientIdentity14,
      row18_reducedY45_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY45_combinationStep02Multiplier * equation

private def row18_reducedY45_combinationStep03Multiplier : ℂ :=
  (((1426 / 237) : ℂ) - ((344 / 79) : ℂ) * ζ ^ 1 - ((444 / 79) : ℂ) * ζ ^ 2 + ((1466 / 237) : ℂ) * ζ ^ 3 - ((756 / 79) : ℂ) * ζ ^ 5 - ((672 / 79) : ℂ) * ζ ^ 8 + ((422 / 237) : ℂ) * ζ ^ 9 - ((1888 / 237) : ℂ) * ζ ^ 11 - ((836 / 237) : ℂ) * ζ ^ 12 + ((344 / 79) : ℂ) * ζ ^ 13 - ((230 / 237) : ℂ) * ζ ^ 15 + ((344 / 79) : ℂ) * ζ ^ 17 + ((444 / 79) : ℂ) * ζ ^ 18 + ((2498 / 237) : ℂ) * ζ ^ 21 + ((444 / 79) : ℂ) * ζ ^ 22 + ((2852 / 237) : ℂ) * ζ ^ 24 + ((412 / 79) : ℂ) * ζ ^ 25 + ((2498 / 237) : ℂ) * ζ ^ 27 + ((672 / 79) : ℂ) * ζ ^ 28 - ((344 / 79) : ℂ) * ζ ^ 29 + ((394 / 79) : ℂ) * ζ ^ 30 + ((1888 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY45_combinationStep03Coefficient00 : ℂ :=
  (-((1721 / 1185) : ℂ) + ((2986 / 1185) : ℂ) * ζ ^ 1 + ((12389 / 2370) : ℂ) * ζ ^ 2 - ((413 / 158) : ℂ) * ζ ^ 3 + ((2961 / 395) : ℂ) * ζ ^ 5 + ((7591 / 2370) : ℂ) * ζ ^ 6 + ((7963 / 1185) : ℂ) * ζ ^ 8 + ((2911 / 2370) : ℂ) * ζ ^ 9 + ((3017 / 474) : ℂ) * ζ ^ 11 + ((2399 / 1185) : ℂ) * ζ ^ 12 - ((2986 / 1185) : ℂ) * ζ ^ 13 + ((413 / 158) : ℂ) * ζ ^ 15 - ((2986 / 1185) : ℂ) * ζ ^ 17 - ((8947 / 2370) : ℂ) * ζ ^ 18 - ((5897 / 1185) : ℂ) * ζ ^ 21 - ((12389 / 2370) : ℂ) * ζ ^ 22 - ((12389 / 2370) : ℂ) * ζ ^ 24 - ((5897 / 1185) : ℂ) * ζ ^ 25 - ((3017 / 474) : ℂ) * ζ ^ 27 - ((7963 / 1185) : ℂ) * ζ ^ 28 + ((2986 / 1185) : ℂ) * ζ ^ 29 - ((1179 / 790) : ℂ) * ζ ^ 30 - ((3017 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep03CoefficientIdentity00 :
    row18_reducedY45_combinationStep03Coefficient00 =
      row18_reducedY45_combinationStep02Coefficient00 +
        row18_reducedY45_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep03Coefficient00 row18_reducedY45_combinationStep02Coefficient00 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 (((947 / 12482) : ℂ) - ((33754 / 18723) : ℂ) * ζ ^ 1 - ((6625 / 6241) : ℂ) * ζ ^ 2 + ((29456 / 18723) : ℂ) * ζ ^ 3 - ((3656 / 18723) : ℂ) * ζ ^ 4 - ((4175 / 12482) : ℂ) * ζ ^ 5 + ((21089 / 37446) : ℂ) * ζ ^ 6 - ((44465 / 18723) : ℂ) * ζ ^ 7 - ((43447 / 18723) : ℂ) * ζ ^ 8 + ((18629 / 18723) : ℂ) * ζ ^ 9 + ((7953 / 6241) : ℂ) * ζ ^ 10 + ((8938 / 18723) : ℂ) * ζ ^ 11 + ((19603 / 18723) : ℂ) * ζ ^ 12 + ((1420 / 18723) : ℂ) * ζ ^ 13 - ((26165 / 37446) : ℂ) * ζ ^ 14 + ((5449 / 37446) : ℂ) * ζ ^ 15 + ((9809 / 37446) : ℂ) * ζ ^ 16 + ((13399 / 37446) : ℂ) * ζ ^ 17 + ((30383 / 37446) : ℂ) * ζ ^ 18 - ((973 / 12482) : ℂ) * ζ ^ 19 - ((1765 / 18723) : ℂ) * ζ ^ 20 + ((9614 / 18723) : ℂ) * ζ ^ 21 - ((7886 / 6241) : ℂ) * ζ ^ 22 - ((17203 / 37446) : ℂ) * ζ ^ 23 + ((46853 / 37446) : ℂ) * ζ ^ 24 - ((6743 / 6241) : ℂ) * ζ ^ 25 + ((463 / 6241) : ℂ) * ζ ^ 26 + ((57661 / 37446) : ℂ) * ζ ^ 27 - ((16450 / 18723) : ℂ) * ζ ^ 28 - ((18059 / 12482) : ℂ) * ζ ^ 29 - ((2360 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep03Coefficient01 : ℂ :=
  (-((40 / 79) : ℂ) + ((71 / 237) : ℂ) * ζ ^ 1 - ((98 / 237) : ℂ) * ζ ^ 2 - ((17 / 79) : ℂ) * ζ ^ 3 - ((29 / 237) : ℂ) * ζ ^ 5 + ((4 / 237) : ℂ) * ζ ^ 6 + ((34 / 237) : ℂ) * ζ ^ 8 - ((16 / 79) : ℂ) * ζ ^ 9 + ((1 / 79) : ℂ) * ζ ^ 11 + ((34 / 237) : ℂ) * ζ ^ 12 - ((71 / 237) : ℂ) * ζ ^ 13 - ((49 / 237) : ℂ) * ζ ^ 15 - ((71 / 237) : ℂ) * ζ ^ 17 - ((34 / 79) : ℂ) * ζ ^ 18 - ((20 / 237) : ℂ) * ζ ^ 21 + ((98 / 237) : ℂ) * ζ ^ 22 + ((100 / 237) : ℂ) * ζ ^ 25 + ((20 / 237) : ℂ) * ζ ^ 27 - ((34 / 237) : ℂ) * ζ ^ 28 + ((71 / 237) : ℂ) * ζ ^ 29 + ((2 / 237) : ℂ) * ζ ^ 30 - ((1 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep03CoefficientIdentity01 :
    row18_reducedY45_combinationStep03Coefficient01 =
      row18_reducedY45_combinationStep02Coefficient01 +
        row18_reducedY45_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep03Coefficient01 row18_reducedY45_combinationStep02Coefficient01 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 (-((115829 / 37446) : ℂ) + ((289411 / 37446) : ℂ) * ζ ^ 1 - ((60913 / 6241) : ℂ) * ζ ^ 2 - ((57338 / 6241) : ℂ) * ζ ^ 3 + ((49054 / 18723) : ℂ) * ζ ^ 4 - ((142858 / 18723) : ℂ) * ζ ^ 5 - ((283171 / 37446) : ℂ) * ζ ^ 6 + ((18299 / 6241) : ℂ) * ζ ^ 7 - ((100301 / 12482) : ℂ) * ζ ^ 8 - ((106813 / 18723) : ℂ) * ζ ^ 9 - ((6157 / 18723) : ℂ) * ζ ^ 10 - ((153865 / 12482) : ℂ) * ζ ^ 11 - ((165155 / 37446) : ℂ) * ζ ^ 12 + ((4724 / 18723) : ℂ) * ζ ^ 13 - ((184109 / 18723) : ℂ) * ζ ^ 14 - ((4732 / 18723) : ℂ) * ζ ^ 15 - ((3937 / 18723) : ℂ) * ζ ^ 16 - ((426643 / 37446) : ℂ) * ζ ^ 17 - ((77917 / 37446) : ℂ) * ζ ^ 18 + ((22237 / 18723) : ℂ) * ζ ^ 19 - ((3715 / 474) : ℂ) * ζ ^ 20 - ((35252 / 18723) : ℂ) * ζ ^ 21 + ((12858 / 6241) : ℂ) * ζ ^ 22 - ((14999 / 6241) : ℂ) * ζ ^ 23 + ((77489 / 37446) : ℂ) * ζ ^ 24 - ((6193 / 6241) : ℂ) * ζ ^ 25 - ((58042 / 18723) : ℂ) * ζ ^ 26 + ((20285 / 12482) : ℂ) * ζ ^ 27 + ((8924 / 6241) : ℂ) * ζ ^ 28 + ((6534 / 6241) : ℂ) * ζ ^ 29 + ((13216 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep03Coefficient02 : ℂ :=
  (-((152 / 237) : ℂ) - ((635 / 158) : ℂ) * ζ ^ 1 + ((635 / 158) : ℂ) * ζ ^ 3 - ((479 / 158) : ℂ) * ζ ^ 5 + ((977 / 237) : ℂ) * ζ ^ 6 + ((76 / 237) : ℂ) * ζ ^ 8 + ((1063 / 237) : ℂ) * ζ ^ 9 - ((78 / 79) : ℂ) * ζ ^ 11 + ((956 / 237) : ℂ) * ζ ^ 12 + ((635 / 158) : ℂ) * ζ ^ 13 + ((33 / 79) : ℂ) * ζ ^ 15 + ((635 / 158) : ℂ) * ζ ^ 17 + ((17 / 79) : ℂ) * ζ ^ 18 + ((701 / 158) : ℂ) * ζ ^ 21 + ((268 / 79) : ℂ) * ζ ^ 24 - ((78 / 79) : ℂ) * ζ ^ 25 + ((1063 / 237) : ℂ) * ζ ^ 27 - ((76 / 237) : ℂ) * ζ ^ 28 - ((635 / 158) : ℂ) * ζ ^ 29 + ((977 / 237) : ℂ) * ζ ^ 30 + ((78 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep03CoefficientIdentity02 :
    row18_reducedY45_combinationStep03Coefficient02 =
      row18_reducedY45_combinationStep02Coefficient02 +
        row18_reducedY45_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep03Coefficient02 row18_reducedY45_combinationStep02Coefficient02 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep03Coefficient03 : ℂ :=
  (((461 / 474) : ℂ) + ((341 / 237) : ℂ) * ζ ^ 1 - ((51 / 79) : ℂ) * ζ ^ 2 + ((175 / 474) : ℂ) * ζ ^ 3 + ((69 / 79) : ℂ) * ζ ^ 5 + ((116 / 237) : ℂ) * ζ ^ 6 - ((109 / 158) : ℂ) * ζ ^ 8 - ((475 / 474) : ℂ) * ζ ^ 9 - ((211 / 474) : ℂ) * ζ ^ 11 - ((269 / 237) : ℂ) * ζ ^ 12 - ((341 / 237) : ℂ) * ζ ^ 13 - ((175 / 474) : ℂ) * ζ ^ 15 - ((341 / 237) : ℂ) * ζ ^ 17 - ((155 / 474) : ℂ) * ζ ^ 18 + ((134 / 237) : ℂ) * ζ ^ 21 + ((51 / 79) : ℂ) * ζ ^ 22 + ((51 / 79) : ℂ) * ζ ^ 24 + ((134 / 237) : ℂ) * ζ ^ 25 + ((211 / 474) : ℂ) * ζ ^ 27 + ((109 / 158) : ℂ) * ζ ^ 28 + ((341 / 237) : ℂ) * ζ ^ 29 + ((7 / 158) : ℂ) * ζ ^ 30 + ((211 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep03CoefficientIdentity03 :
    row18_reducedY45_combinationStep03Coefficient03 =
      row18_reducedY45_combinationStep02Coefficient03 +
        row18_reducedY45_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep03Coefficient03 row18_reducedY45_combinationStep02Coefficient03 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep03Coefficient04 : ℂ :=
  (((1336 / 1185) : ℂ) - ((6937 / 2370) : ℂ) * ζ ^ 1 - ((1504 / 395) : ℂ) * ζ ^ 2 + ((82 / 79) : ℂ) * ζ ^ 3 - ((7988 / 1185) : ℂ) * ζ ^ 5 - ((1036 / 395) : ℂ) * ζ ^ 6 - ((6563 / 1185) : ℂ) * ζ ^ 8 - ((1051 / 2370) : ℂ) * ζ ^ 9 - ((739 / 158) : ℂ) * ζ ^ 11 - ((468 / 395) : ℂ) * ζ ^ 12 + ((6937 / 2370) : ℂ) * ζ ^ 13 - ((82 / 79) : ℂ) * ζ ^ 15 + ((6937 / 2370) : ℂ) * ζ ^ 17 + ((3176 / 1185) : ℂ) * ζ ^ 18 + ((3013 / 790) : ℂ) * ζ ^ 21 + ((1504 / 395) : ℂ) * ζ ^ 22 + ((1504 / 395) : ℂ) * ζ ^ 24 + ((3013 / 790) : ℂ) * ζ ^ 25 + ((739 / 158) : ℂ) * ζ ^ 27 + ((6563 / 1185) : ℂ) * ζ ^ 28 - ((6937 / 2370) : ℂ) * ζ ^ 29 + ((2051 / 1185) : ℂ) * ζ ^ 30 + ((739 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep03CoefficientIdentity04 :
    row18_reducedY45_combinationStep03Coefficient04 =
      row18_reducedY45_combinationStep02Coefficient04 +
        row18_reducedY45_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep03Coefficient04 row18_reducedY45_combinationStep02Coefficient04 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep03Coefficient05 : ℂ :=
  (((1015 / 474) : ℂ) - ((436 / 237) : ℂ) * ζ ^ 1 - ((692 / 237) : ℂ) * ζ ^ 2 + ((1207 / 474) : ℂ) * ζ ^ 3 - ((615 / 158) : ℂ) * ζ ^ 5 - ((847 / 237) : ℂ) * ζ ^ 8 + ((305 / 474) : ℂ) * ζ ^ 9 - ((252 / 79) : ℂ) * ζ ^ 11 - ((56 / 79) : ℂ) * ζ ^ 12 + ((436 / 237) : ℂ) * ζ ^ 13 - ((39 / 79) : ℂ) * ζ ^ 15 + ((436 / 237) : ℂ) * ζ ^ 17 + ((692 / 237) : ℂ) * ζ ^ 18 + ((693 / 158) : ℂ) * ζ ^ 21 + ((692 / 237) : ℂ) * ζ ^ 22 + ((1015 / 237) : ℂ) * ζ ^ 24 + ((973 / 474) : ℂ) * ζ ^ 25 + ((693 / 158) : ℂ) * ζ ^ 27 + ((847 / 237) : ℂ) * ζ ^ 28 - ((436 / 237) : ℂ) * ζ ^ 29 + ((557 / 474) : ℂ) * ζ ^ 30 + ((252 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep03CoefficientIdentity05 :
    row18_reducedY45_combinationStep03Coefficient05 =
      row18_reducedY45_combinationStep02Coefficient05 +
        row18_reducedY45_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep03Coefficient05 row18_reducedY45_combinationStep02Coefficient05 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 (-((71629 / 37446) : ℂ) + ((54853 / 37446) : ℂ) * ζ ^ 1 + ((55875 / 12482) : ℂ) * ζ ^ 2 - ((124517 / 37446) : ℂ) * ζ ^ 3 + ((3994 / 18723) : ℂ) * ζ ^ 4 + ((77239 / 18723) : ℂ) * ζ ^ 5 - ((143605 / 37446) : ℂ) * ζ ^ 6 - ((1039 / 37446) : ℂ) * ζ ^ 7 + ((13945 / 6241) : ℂ) * ζ ^ 8 - ((114881 / 37446) : ℂ) * ζ ^ 9 + ((25588 / 18723) : ℂ) * ζ ^ 10 + ((69157 / 37446) : ℂ) * ζ ^ 11 - ((24532 / 6241) : ℂ) * ζ ^ 12 + ((68513 / 37446) : ℂ) * ζ ^ 13 + ((31586 / 18723) : ℂ) * ζ ^ 14 - ((45095 / 12482) : ℂ) * ζ ^ 15 + ((25601 / 12482) : ℂ) * ζ ^ 16 + ((36937 / 37446) : ℂ) * ζ ^ 17 - ((34629 / 12482) : ℂ) * ζ ^ 18 + ((47029 / 37446) : ℂ) * ζ ^ 19 - ((4228 / 6241) : ℂ) * ζ ^ 20 - ((30061 / 12482) : ℂ) * ζ ^ 21 - ((1781 / 6241) : ℂ) * ζ ^ 22 - ((683 / 18723) : ℂ) * ζ ^ 23 - ((15019 / 37446) : ℂ) * ζ ^ 24 - ((23677 / 37446) : ℂ) * ζ ^ 25 + ((8649 / 12482) : ℂ) * ζ ^ 26 + ((4171 / 37446) : ℂ) * ζ ^ 27 + ((3148 / 18723) : ℂ) * ζ ^ 28 + ((3415 / 18723) : ℂ) * ζ ^ 29 - ((6608 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep03Coefficient06 : ℂ :=
  (((1763 / 790) : ℂ) * ζ ^ 1 + ((49 / 395) : ℂ) * ζ ^ 2 + ((1763 / 790) : ℂ) * ζ ^ 3 - ((1883 / 2370) : ℂ) * ζ ^ 5 - ((529 / 395) : ℂ) * ζ ^ 6 + ((43 / 158) : ℂ) * ζ ^ 8 + ((17 / 395) : ℂ) * ζ ^ 9 - ((3586 / 1185) : ℂ) * ζ ^ 11 - ((697 / 237) : ℂ) * ζ ^ 12 - ((1763 / 790) : ℂ) * ζ ^ 13 - ((1273 / 1185) : ℂ) * ζ ^ 15 - ((1763 / 790) : ℂ) * ζ ^ 17 - ((49 / 790) : ℂ) * ζ ^ 18 - ((2743 / 2370) : ℂ) * ζ ^ 21 - ((49 / 395) : ℂ) * ζ ^ 22 + ((697 / 237) : ℂ) * ζ ^ 24 + ((3586 / 1185) : ℂ) * ζ ^ 25 - ((17 / 395) : ℂ) * ζ ^ 27 - ((43 / 158) : ℂ) * ζ ^ 28 + ((1763 / 790) : ℂ) * ζ ^ 29 + ((578 / 395) : ℂ) * ζ ^ 30 + ((3586 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep03CoefficientIdentity06 :
    row18_reducedY45_combinationStep03Coefficient06 =
      row18_reducedY45_combinationStep02Coefficient06 +
        row18_reducedY45_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep03Coefficient06 row18_reducedY45_combinationStep02Coefficient06 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep03Coefficient07 : ℂ :=
  (-((307 / 474) : ℂ) - ((163 / 158) : ℂ) * ζ ^ 1 - ((367 / 474) : ℂ) * ζ ^ 2 + ((286 / 237) : ℂ) * ζ ^ 3 - ((386 / 237) : ℂ) * ζ ^ 5 - ((169 / 158) : ℂ) * ζ ^ 6 - ((233 / 474) : ℂ) * ζ ^ 8 + ((103 / 474) : ℂ) * ζ ^ 9 - ((589 / 474) : ℂ) * ζ ^ 11 + ((70 / 237) : ℂ) * ζ ^ 12 + ((163 / 158) : ℂ) * ζ ^ 13 - ((286 / 237) : ℂ) * ζ ^ 15 + ((163 / 158) : ℂ) * ζ ^ 17 + ((337 / 237) : ℂ) * ζ ^ 18 + ((283 / 474) : ℂ) * ζ ^ 21 + ((367 / 474) : ℂ) * ζ ^ 22 + ((367 / 474) : ℂ) * ζ ^ 24 + ((283 / 474) : ℂ) * ζ ^ 25 + ((589 / 474) : ℂ) * ζ ^ 27 + ((233 / 474) : ℂ) * ζ ^ 28 - ((163 / 158) : ℂ) * ζ ^ 29 - ((67 / 237) : ℂ) * ζ ^ 30 + ((589 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep03CoefficientIdentity07 :
    row18_reducedY45_combinationStep03Coefficient07 =
      row18_reducedY45_combinationStep02Coefficient07 +
        row18_reducedY45_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep03Coefficient07 row18_reducedY45_combinationStep02Coefficient07 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 (-((947 / 12482) : ℂ) + ((33754 / 18723) : ℂ) * ζ ^ 1 + ((6625 / 6241) : ℂ) * ζ ^ 2 - ((29456 / 18723) : ℂ) * ζ ^ 3 + ((3656 / 18723) : ℂ) * ζ ^ 4 + ((4175 / 12482) : ℂ) * ζ ^ 5 - ((21089 / 37446) : ℂ) * ζ ^ 6 + ((44465 / 18723) : ℂ) * ζ ^ 7 + ((43447 / 18723) : ℂ) * ζ ^ 8 - ((18629 / 18723) : ℂ) * ζ ^ 9 - ((7953 / 6241) : ℂ) * ζ ^ 10 - ((8938 / 18723) : ℂ) * ζ ^ 11 - ((19603 / 18723) : ℂ) * ζ ^ 12 - ((1420 / 18723) : ℂ) * ζ ^ 13 + ((26165 / 37446) : ℂ) * ζ ^ 14 - ((5449 / 37446) : ℂ) * ζ ^ 15 - ((9809 / 37446) : ℂ) * ζ ^ 16 - ((13399 / 37446) : ℂ) * ζ ^ 17 - ((30383 / 37446) : ℂ) * ζ ^ 18 + ((973 / 12482) : ℂ) * ζ ^ 19 + ((1765 / 18723) : ℂ) * ζ ^ 20 - ((9614 / 18723) : ℂ) * ζ ^ 21 + ((7886 / 6241) : ℂ) * ζ ^ 22 + ((17203 / 37446) : ℂ) * ζ ^ 23 - ((46853 / 37446) : ℂ) * ζ ^ 24 + ((6743 / 6241) : ℂ) * ζ ^ 25 - ((463 / 6241) : ℂ) * ζ ^ 26 - ((57661 / 37446) : ℂ) * ζ ^ 27 + ((16450 / 18723) : ℂ) * ζ ^ 28 + ((18059 / 12482) : ℂ) * ζ ^ 29 + ((2360 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep03CoefficientIdentity08 :
    row18_reducedY45_combinationStep03Coefficient08 =
      row18_reducedY45_combinationStep02Coefficient08 +
        row18_reducedY45_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep03Coefficient08 row18_reducedY45_combinationStep02Coefficient08 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep03CoefficientIdentity09 :
    row18_reducedY45_combinationStep03Coefficient09 =
      row18_reducedY45_combinationStep02Coefficient09 +
        row18_reducedY45_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep03Coefficient09 row18_reducedY45_combinationStep02Coefficient09 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep03CoefficientIdentity10 :
    row18_reducedY45_combinationStep03Coefficient10 =
      row18_reducedY45_combinationStep02Coefficient10 +
        row18_reducedY45_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep03Coefficient10 row18_reducedY45_combinationStep02Coefficient10 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep03CoefficientIdentity11 :
    row18_reducedY45_combinationStep03Coefficient11 =
      row18_reducedY45_combinationStep02Coefficient11 +
        row18_reducedY45_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep03Coefficient11 row18_reducedY45_combinationStep02Coefficient11 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep03CoefficientIdentity12 :
    row18_reducedY45_combinationStep03Coefficient12 =
      row18_reducedY45_combinationStep02Coefficient12 +
        row18_reducedY45_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep03Coefficient12 row18_reducedY45_combinationStep02Coefficient12 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep03CoefficientIdentity13 :
    row18_reducedY45_combinationStep03Coefficient13 =
      row18_reducedY45_combinationStep02Coefficient13 +
        row18_reducedY45_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep03Coefficient13 row18_reducedY45_combinationStep02Coefficient13 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep03CoefficientIdentity14 :
    row18_reducedY45_combinationStep03Coefficient14 =
      row18_reducedY45_combinationStep02Coefficient14 +
        row18_reducedY45_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep03Coefficient14 row18_reducedY45_combinationStep02Coefficient14 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep03CoefficientIdentity15 :
    row18_reducedY45_combinationStep03Coefficient15 =
      row18_reducedY45_combinationStep02Coefficient15 +
        row18_reducedY45_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep03Coefficient15 row18_reducedY45_combinationStep02Coefficient15 row18_reducedY45_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY45_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY45_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY45_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY45_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY45_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY45_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY45_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY45_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY45_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY45_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY45_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY45_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY45_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY45_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY45_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY45_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY45_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY45_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY45_combinationStep03CoefficientIdentity00,
      row18_reducedY45_combinationStep03CoefficientIdentity01,
      row18_reducedY45_combinationStep03CoefficientIdentity02,
      row18_reducedY45_combinationStep03CoefficientIdentity03,
      row18_reducedY45_combinationStep03CoefficientIdentity04,
      row18_reducedY45_combinationStep03CoefficientIdentity05,
      row18_reducedY45_combinationStep03CoefficientIdentity06,
      row18_reducedY45_combinationStep03CoefficientIdentity07,
      row18_reducedY45_combinationStep03CoefficientIdentity08,
      row18_reducedY45_combinationStep03CoefficientIdentity09,
      row18_reducedY45_combinationStep03CoefficientIdentity10,
      row18_reducedY45_combinationStep03CoefficientIdentity11,
      row18_reducedY45_combinationStep03CoefficientIdentity12,
      row18_reducedY45_combinationStep03CoefficientIdentity13,
      row18_reducedY45_combinationStep03CoefficientIdentity14,
      row18_reducedY45_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY45_combinationStep03Multiplier * equation

private def row18_reducedY45_combinationStep04Multiplier : ℂ :=
  (-((58 / 237) : ℂ) + ((128 / 237) : ℂ) * ζ ^ 1 + ((118 / 79) : ℂ) * ζ ^ 2 + ((106 / 237) : ℂ) * ζ ^ 3 - ((20 / 237) : ℂ) * ζ ^ 5 + ((2 / 237) : ℂ) * ζ ^ 8 - ((154 / 237) : ℂ) * ζ ^ 9 + ((16 / 79) : ℂ) * ζ ^ 11 + ((38 / 79) : ℂ) * ζ ^ 12 - ((128 / 237) : ℂ) * ζ ^ 13 + ((14 / 79) : ℂ) * ζ ^ 15 - ((128 / 237) : ℂ) * ζ ^ 17 - ((118 / 79) : ℂ) * ζ ^ 18 - ((22 / 237) : ℂ) * ζ ^ 21 - ((118 / 79) : ℂ) * ζ ^ 22 - ((116 / 237) : ℂ) * ζ ^ 24 + ((148 / 237) : ℂ) * ζ ^ 25 - ((22 / 237) : ℂ) * ζ ^ 27 - ((2 / 237) : ℂ) * ζ ^ 28 + ((128 / 237) : ℂ) * ζ ^ 29 + ((54 / 79) : ℂ) * ζ ^ 30 - ((16 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY45_combinationStep04Coefficient00 : ℂ :=
  (-((8 / 5) : ℂ) + ((13 / 5) : ℂ) * ζ ^ 1 + ((57 / 10) : ℂ) * ζ ^ 2 - ((5 / 2) : ℂ) * ζ ^ 3 + ((39 / 5) : ℂ) * ζ ^ 5 + ((33 / 10) : ℂ) * ζ ^ 6 + ((34 / 5) : ℂ) * ζ ^ 8 + ((13 / 10) : ℂ) * ζ ^ 9 + ((13 / 2) : ℂ) * ζ ^ 11 + ((12 / 5) : ℂ) * ζ ^ 12 - ((13 / 5) : ℂ) * ζ ^ 13 + ((5 / 2) : ℂ) * ζ ^ 15 - ((13 / 5) : ℂ) * ζ ^ 17 - ((41 / 10) : ℂ) * ζ ^ 18 - ((26 / 5) : ℂ) * ζ ^ 21 - ((57 / 10) : ℂ) * ζ ^ 22 - ((57 / 10) : ℂ) * ζ ^ 24 - ((26 / 5) : ℂ) * ζ ^ 25 - ((13 / 2) : ℂ) * ζ ^ 27 - ((34 / 5) : ℂ) * ζ ^ 28 + ((13 / 5) : ℂ) * ζ ^ 29 - ((11 / 10) : ℂ) * ζ ^ 30 - ((13 / 2) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep04CoefficientIdentity00 :
    row18_reducedY45_combinationStep04Coefficient00 =
      row18_reducedY45_combinationStep03Coefficient00 +
        row18_reducedY45_combinationStep04Multiplier *
          (((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep04Coefficient00 row18_reducedY45_combinationStep03Coefficient00 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 (((1576 / 18723) : ℂ) + ((2623 / 37446) : ℂ) * ζ ^ 1 - ((2500 / 18723) : ℂ) * ζ ^ 2 - ((247 / 12482) : ℂ) * ζ ^ 3 + ((47 / 474) : ℂ) * ζ ^ 4 - ((37 / 158) : ℂ) * ζ ^ 5 + ((31 / 474) : ℂ) * ζ ^ 6 + ((1105 / 37446) : ℂ) * ζ ^ 7 - ((3157 / 37446) : ℂ) * ζ ^ 8 - ((5711 / 37446) : ℂ) * ζ ^ 9 - ((7475 / 37446) : ℂ) * ζ ^ 10 + ((3403 / 37446) : ℂ) * ζ ^ 11 - ((805 / 18723) : ℂ) * ζ ^ 12 + ((2269 / 37446) : ℂ) * ζ ^ 13 + ((529 / 18723) : ℂ) * ζ ^ 14 + ((575 / 37446) : ℂ) * ζ ^ 15 + ((4490 / 18723) : ℂ) * ζ ^ 16 - ((811 / 37446) : ℂ) * ζ ^ 17 - ((4555 / 18723) : ℂ) * ζ ^ 18 + ((1552 / 18723) : ℂ) * ζ ^ 19 - ((2225 / 18723) : ℂ) * ζ ^ 20 + ((747 / 6241) : ℂ) * ζ ^ 21 - ((1000 / 18723) : ℂ) * ζ ^ 22 - ((1133 / 37446) : ℂ) * ζ ^ 23 + ((1459 / 37446) : ℂ) * ζ ^ 24 + ((568 / 18723) : ℂ) * ζ ^ 25 + ((4691 / 37446) : ℂ) * ζ ^ 26 - ((710 / 6241) : ℂ) * ζ ^ 27 - ((305 / 12482) : ℂ) * ζ ^ 28 + ((621 / 12482) : ℂ) * ζ ^ 29 - ((60 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep04Coefficient01 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep04CoefficientIdentity01 :
    row18_reducedY45_combinationStep04Coefficient01 =
      row18_reducedY45_combinationStep03Coefficient01 +
        row18_reducedY45_combinationStep04Multiplier *
          (((16 / 79) : ℂ) + ((35 / 316) : ℂ) * ζ ^ 1 - ((61 / 316) : ℂ) * ζ ^ 2 + ((87 / 316) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 - ((6 / 79) : ℂ) * ζ ^ 8 - ((31 / 316) : ℂ) * ζ ^ 9 - ((14 / 79) : ℂ) * ζ ^ 11 - ((26 / 79) : ℂ) * ζ ^ 12 - ((35 / 316) : ℂ) * ζ ^ 13 - ((49 / 316) : ℂ) * ζ ^ 15 - ((35 / 316) : ℂ) * ζ ^ 17 + ((61 / 316) : ℂ) * ζ ^ 18 + ((13 / 79) : ℂ) * ζ ^ 21 + ((61 / 316) : ℂ) * ζ ^ 22 + ((32 / 79) : ℂ) * ζ ^ 24 + ((19 / 158) : ℂ) * ζ ^ 25 + ((13 / 79) : ℂ) * ζ ^ 27 + ((6 / 79) : ℂ) * ζ ^ 28 + ((35 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((14 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep04Coefficient01 row18_reducedY45_combinationStep03Coefficient01 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 (-((10408 / 18723) : ℂ) + ((181 / 474) : ℂ) * ζ ^ 1 - ((49 / 12482) : ℂ) * ζ ^ 2 - ((31 / 237) : ℂ) * ζ ^ 3 + ((2907 / 6241) : ℂ) * ζ ^ 4 - ((46 / 237) : ℂ) * ζ ^ 5 + ((808 / 6241) : ℂ) * ζ ^ 6 + ((21 / 158) : ℂ) * ζ ^ 7 - ((4113 / 12482) : ℂ) * ζ ^ 8 - ((37 / 237) : ℂ) * ζ ^ 9 - ((2301 / 6241) : ℂ) * ζ ^ 10 - ((7 / 79) : ℂ) * ζ ^ 11 - ((2509 / 12482) : ℂ) * ζ ^ 12 - ((21 / 79) : ℂ) * ζ ^ 13 - ((13045 / 37446) : ℂ) * ζ ^ 14 - ((119 / 474) : ℂ) * ζ ^ 15 - ((5207 / 37446) : ℂ) * ζ ^ 16 - ((29 / 237) : ℂ) * ζ ^ 17 - ((2298 / 6241) : ℂ) * ζ ^ 18 + ((9 / 79) : ℂ) * ζ ^ 19 + ((3094 / 18723) : ℂ) * ζ ^ 20 - ((17 / 158) : ℂ) * ζ ^ 21 + ((2315 / 6241) : ℂ) * ζ ^ 22 - ((1 / 6) : ℂ) * ζ ^ 23 + ((7295 / 37446) : ℂ) * ζ ^ 24 + ((7 / 474) : ℂ) * ζ ^ 25 + ((1856 / 18723) : ℂ) * ζ ^ 26 - ((11 / 474) : ℂ) * ζ ^ 27 - ((572 / 18723) : ℂ) * ζ ^ 28 + ((12 / 79) : ℂ) * ζ ^ 29 - ((224 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep04Coefficient02 : ℂ :=
  (-((152 / 237) : ℂ) - ((635 / 158) : ℂ) * ζ ^ 1 + ((635 / 158) : ℂ) * ζ ^ 3 - ((479 / 158) : ℂ) * ζ ^ 5 + ((977 / 237) : ℂ) * ζ ^ 6 + ((76 / 237) : ℂ) * ζ ^ 8 + ((1063 / 237) : ℂ) * ζ ^ 9 - ((78 / 79) : ℂ) * ζ ^ 11 + ((956 / 237) : ℂ) * ζ ^ 12 + ((635 / 158) : ℂ) * ζ ^ 13 + ((33 / 79) : ℂ) * ζ ^ 15 + ((635 / 158) : ℂ) * ζ ^ 17 + ((17 / 79) : ℂ) * ζ ^ 18 + ((701 / 158) : ℂ) * ζ ^ 21 + ((268 / 79) : ℂ) * ζ ^ 24 - ((78 / 79) : ℂ) * ζ ^ 25 + ((1063 / 237) : ℂ) * ζ ^ 27 - ((76 / 237) : ℂ) * ζ ^ 28 - ((635 / 158) : ℂ) * ζ ^ 29 + ((977 / 237) : ℂ) * ζ ^ 30 + ((78 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep04CoefficientIdentity02 :
    row18_reducedY45_combinationStep04Coefficient02 =
      row18_reducedY45_combinationStep03Coefficient02 +
        row18_reducedY45_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep04Coefficient02 row18_reducedY45_combinationStep03Coefficient02 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep04Coefficient03 : ℂ :=
  (((461 / 474) : ℂ) + ((341 / 237) : ℂ) * ζ ^ 1 - ((51 / 79) : ℂ) * ζ ^ 2 + ((175 / 474) : ℂ) * ζ ^ 3 + ((69 / 79) : ℂ) * ζ ^ 5 + ((116 / 237) : ℂ) * ζ ^ 6 - ((109 / 158) : ℂ) * ζ ^ 8 - ((475 / 474) : ℂ) * ζ ^ 9 - ((211 / 474) : ℂ) * ζ ^ 11 - ((269 / 237) : ℂ) * ζ ^ 12 - ((341 / 237) : ℂ) * ζ ^ 13 - ((175 / 474) : ℂ) * ζ ^ 15 - ((341 / 237) : ℂ) * ζ ^ 17 - ((155 / 474) : ℂ) * ζ ^ 18 + ((134 / 237) : ℂ) * ζ ^ 21 + ((51 / 79) : ℂ) * ζ ^ 22 + ((51 / 79) : ℂ) * ζ ^ 24 + ((134 / 237) : ℂ) * ζ ^ 25 + ((211 / 474) : ℂ) * ζ ^ 27 + ((109 / 158) : ℂ) * ζ ^ 28 + ((341 / 237) : ℂ) * ζ ^ 29 + ((7 / 158) : ℂ) * ζ ^ 30 + ((211 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep04CoefficientIdentity03 :
    row18_reducedY45_combinationStep04Coefficient03 =
      row18_reducedY45_combinationStep03Coefficient03 +
        row18_reducedY45_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep04Coefficient03 row18_reducedY45_combinationStep03Coefficient03 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep04Coefficient04 : ℂ :=
  (((1336 / 1185) : ℂ) - ((6937 / 2370) : ℂ) * ζ ^ 1 - ((1504 / 395) : ℂ) * ζ ^ 2 + ((82 / 79) : ℂ) * ζ ^ 3 - ((7988 / 1185) : ℂ) * ζ ^ 5 - ((1036 / 395) : ℂ) * ζ ^ 6 - ((6563 / 1185) : ℂ) * ζ ^ 8 - ((1051 / 2370) : ℂ) * ζ ^ 9 - ((739 / 158) : ℂ) * ζ ^ 11 - ((468 / 395) : ℂ) * ζ ^ 12 + ((6937 / 2370) : ℂ) * ζ ^ 13 - ((82 / 79) : ℂ) * ζ ^ 15 + ((6937 / 2370) : ℂ) * ζ ^ 17 + ((3176 / 1185) : ℂ) * ζ ^ 18 + ((3013 / 790) : ℂ) * ζ ^ 21 + ((1504 / 395) : ℂ) * ζ ^ 22 + ((1504 / 395) : ℂ) * ζ ^ 24 + ((3013 / 790) : ℂ) * ζ ^ 25 + ((739 / 158) : ℂ) * ζ ^ 27 + ((6563 / 1185) : ℂ) * ζ ^ 28 - ((6937 / 2370) : ℂ) * ζ ^ 29 + ((2051 / 1185) : ℂ) * ζ ^ 30 + ((739 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep04CoefficientIdentity04 :
    row18_reducedY45_combinationStep04Coefficient04 =
      row18_reducedY45_combinationStep03Coefficient04 +
        row18_reducedY45_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep04Coefficient04 row18_reducedY45_combinationStep03Coefficient04 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep04Coefficient05 : ℂ :=
  (((1015 / 474) : ℂ) - ((436 / 237) : ℂ) * ζ ^ 1 - ((692 / 237) : ℂ) * ζ ^ 2 + ((1207 / 474) : ℂ) * ζ ^ 3 - ((615 / 158) : ℂ) * ζ ^ 5 - ((847 / 237) : ℂ) * ζ ^ 8 + ((305 / 474) : ℂ) * ζ ^ 9 - ((252 / 79) : ℂ) * ζ ^ 11 - ((56 / 79) : ℂ) * ζ ^ 12 + ((436 / 237) : ℂ) * ζ ^ 13 - ((39 / 79) : ℂ) * ζ ^ 15 + ((436 / 237) : ℂ) * ζ ^ 17 + ((692 / 237) : ℂ) * ζ ^ 18 + ((693 / 158) : ℂ) * ζ ^ 21 + ((692 / 237) : ℂ) * ζ ^ 22 + ((1015 / 237) : ℂ) * ζ ^ 24 + ((973 / 474) : ℂ) * ζ ^ 25 + ((693 / 158) : ℂ) * ζ ^ 27 + ((847 / 237) : ℂ) * ζ ^ 28 - ((436 / 237) : ℂ) * ζ ^ 29 + ((557 / 474) : ℂ) * ζ ^ 30 + ((252 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep04CoefficientIdentity05 :
    row18_reducedY45_combinationStep04Coefficient05 =
      row18_reducedY45_combinationStep03Coefficient05 +
        row18_reducedY45_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep04Coefficient05 row18_reducedY45_combinationStep03Coefficient05 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep04Coefficient06 : ℂ :=
  (((1763 / 790) : ℂ) * ζ ^ 1 + ((49 / 395) : ℂ) * ζ ^ 2 + ((1763 / 790) : ℂ) * ζ ^ 3 - ((1883 / 2370) : ℂ) * ζ ^ 5 - ((529 / 395) : ℂ) * ζ ^ 6 + ((43 / 158) : ℂ) * ζ ^ 8 + ((17 / 395) : ℂ) * ζ ^ 9 - ((3586 / 1185) : ℂ) * ζ ^ 11 - ((697 / 237) : ℂ) * ζ ^ 12 - ((1763 / 790) : ℂ) * ζ ^ 13 - ((1273 / 1185) : ℂ) * ζ ^ 15 - ((1763 / 790) : ℂ) * ζ ^ 17 - ((49 / 790) : ℂ) * ζ ^ 18 - ((2743 / 2370) : ℂ) * ζ ^ 21 - ((49 / 395) : ℂ) * ζ ^ 22 + ((697 / 237) : ℂ) * ζ ^ 24 + ((3586 / 1185) : ℂ) * ζ ^ 25 - ((17 / 395) : ℂ) * ζ ^ 27 - ((43 / 158) : ℂ) * ζ ^ 28 + ((1763 / 790) : ℂ) * ζ ^ 29 + ((578 / 395) : ℂ) * ζ ^ 30 + ((3586 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep04CoefficientIdentity06 :
    row18_reducedY45_combinationStep04Coefficient06 =
      row18_reducedY45_combinationStep03Coefficient06 +
        row18_reducedY45_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep04Coefficient06 row18_reducedY45_combinationStep03Coefficient06 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep04Coefficient07 : ℂ :=
  (-((307 / 474) : ℂ) - ((163 / 158) : ℂ) * ζ ^ 1 - ((367 / 474) : ℂ) * ζ ^ 2 + ((286 / 237) : ℂ) * ζ ^ 3 - ((386 / 237) : ℂ) * ζ ^ 5 - ((169 / 158) : ℂ) * ζ ^ 6 - ((233 / 474) : ℂ) * ζ ^ 8 + ((103 / 474) : ℂ) * ζ ^ 9 - ((589 / 474) : ℂ) * ζ ^ 11 + ((70 / 237) : ℂ) * ζ ^ 12 + ((163 / 158) : ℂ) * ζ ^ 13 - ((286 / 237) : ℂ) * ζ ^ 15 + ((163 / 158) : ℂ) * ζ ^ 17 + ((337 / 237) : ℂ) * ζ ^ 18 + ((283 / 474) : ℂ) * ζ ^ 21 + ((367 / 474) : ℂ) * ζ ^ 22 + ((367 / 474) : ℂ) * ζ ^ 24 + ((283 / 474) : ℂ) * ζ ^ 25 + ((589 / 474) : ℂ) * ζ ^ 27 + ((233 / 474) : ℂ) * ζ ^ 28 - ((163 / 158) : ℂ) * ζ ^ 29 - ((67 / 237) : ℂ) * ζ ^ 30 + ((589 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep04CoefficientIdentity07 :
    row18_reducedY45_combinationStep04Coefficient07 =
      row18_reducedY45_combinationStep03Coefficient07 +
        row18_reducedY45_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep04Coefficient07 row18_reducedY45_combinationStep03Coefficient07 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep04Coefficient08 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep04CoefficientIdentity08 :
    row18_reducedY45_combinationStep04Coefficient08 =
      row18_reducedY45_combinationStep03Coefficient08 +
        row18_reducedY45_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep04Coefficient08 row18_reducedY45_combinationStep03Coefficient08 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep04Coefficient09 : ℂ :=
  (((105 / 158) : ℂ) - ((26 / 237) : ℂ) * ζ ^ 1 + ((20 / 237) : ℂ) * ζ ^ 2 - ((67 / 237) : ℂ) * ζ ^ 3 - ((149 / 474) : ℂ) * ζ ^ 5 - ((25 / 237) : ℂ) * ζ ^ 6 + ((64 / 237) : ℂ) * ζ ^ 8 + ((2 / 237) : ℂ) * ζ ^ 9 + ((23 / 79) : ℂ) * ζ ^ 11 + ((64 / 237) : ℂ) * ζ ^ 12 + ((26 / 237) : ℂ) * ζ ^ 13 + ((37 / 474) : ℂ) * ζ ^ 15 + ((26 / 237) : ℂ) * ζ ^ 17 + ((15 / 79) : ℂ) * ζ ^ 18 + ((31 / 79) : ℂ) * ζ ^ 21 - ((20 / 237) : ℂ) * ζ ^ 22 + ((97 / 474) : ℂ) * ζ ^ 25 - ((31 / 79) : ℂ) * ζ ^ 27 - ((64 / 237) : ℂ) * ζ ^ 28 - ((26 / 237) : ℂ) * ζ ^ 29 - ((25 / 474) : ℂ) * ζ ^ 30 - ((23 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep04CoefficientIdentity09 :
    row18_reducedY45_combinationStep04Coefficient09 =
      row18_reducedY45_combinationStep03Coefficient09 +
        row18_reducedY45_combinationStep04Multiplier *
          (((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((57 / 158) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((57 / 158) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((57 / 158) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep04Coefficient09 row18_reducedY45_combinationStep03Coefficient09 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 (-((25349 / 37446) : ℂ) + ((23 / 158) : ℂ) * ζ ^ 1 + ((379 / 6241) : ℂ) * ζ ^ 2 + ((9 / 158) : ℂ) * ζ ^ 3 + ((786 / 6241) : ℂ) * ζ ^ 4 - ((1 / 474) : ℂ) * ζ ^ 5 + ((518 / 6241) : ℂ) * ζ ^ 6 + ((5 / 79) : ℂ) * ζ ^ 7 - ((13651 / 37446) : ℂ) * ζ ^ 8 - ((14 / 237) : ℂ) * ζ ^ 9 - ((953 / 12482) : ℂ) * ζ ^ 10 - ((4 / 79) : ℂ) * ζ ^ 11 - ((10411 / 18723) : ℂ) * ζ ^ 12 - ((11 / 79) : ℂ) * ζ ^ 13 - ((3418 / 18723) : ℂ) * ζ ^ 14 + ((131 / 474) : ℂ) * ζ ^ 15 - ((1045 / 37446) : ℂ) * ζ ^ 16 - ((7 / 237) : ℂ) * ζ ^ 17 - ((1763 / 18723) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 19 + ((9289 / 37446) : ℂ) * ζ ^ 20 - ((14 / 237) : ℂ) * ζ ^ 21 + ((249 / 12482) : ℂ) * ζ ^ 22 - ((20 / 237) : ℂ) * ζ ^ 23 + ((2515 / 37446) : ℂ) * ζ ^ 24 + ((1 / 237) : ℂ) * ζ ^ 25 - ((56 / 6241) : ℂ) * ζ ^ 26 - ((23 / 474) : ℂ) * ζ ^ 27 + ((94 / 18723) : ℂ) * ζ ^ 28 + ((3 / 79) : ℂ) * ζ ^ 29 - ((56 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep04Coefficient10 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep04CoefficientIdentity10 :
    row18_reducedY45_combinationStep04Coefficient10 =
      row18_reducedY45_combinationStep03Coefficient10 +
        row18_reducedY45_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep04Coefficient10 row18_reducedY45_combinationStep03Coefficient10 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep04Coefficient11 : ℂ :=
  (((35 / 237) : ℂ) - ((19 / 237) : ℂ) * ζ ^ 1 - ((112 / 237) : ℂ) * ζ ^ 2 - ((9 / 79) : ℂ) * ζ ^ 3 - ((24 / 79) : ℂ) * ζ ^ 5 - ((23 / 237) : ℂ) * ζ ^ 6 - ((19 / 237) : ℂ) * ζ ^ 8 - ((17 / 237) : ℂ) * ζ ^ 9 - ((32 / 237) : ℂ) * ζ ^ 11 - ((89 / 237) : ℂ) * ζ ^ 12 + ((19 / 237) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 + ((19 / 237) : ℂ) * ζ ^ 17 + ((77 / 237) : ℂ) * ζ ^ 18 + ((53 / 237) : ℂ) * ζ ^ 21 + ((112 / 237) : ℂ) * ζ ^ 22 + ((112 / 237) : ℂ) * ζ ^ 24 + ((53 / 237) : ℂ) * ζ ^ 25 + ((32 / 237) : ℂ) * ζ ^ 27 + ((19 / 237) : ℂ) * ζ ^ 28 - ((19 / 237) : ℂ) * ζ ^ 29 - ((31 / 79) : ℂ) * ζ ^ 30 + ((32 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep04CoefficientIdentity11 :
    row18_reducedY45_combinationStep04Coefficient11 =
      row18_reducedY45_combinationStep03Coefficient11 +
        row18_reducedY45_combinationStep04Multiplier *
          (-((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep04Coefficient11 row18_reducedY45_combinationStep03Coefficient11 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 (-((1576 / 18723) : ℂ) - ((2623 / 37446) : ℂ) * ζ ^ 1 + ((2500 / 18723) : ℂ) * ζ ^ 2 + ((247 / 12482) : ℂ) * ζ ^ 3 - ((47 / 474) : ℂ) * ζ ^ 4 + ((37 / 158) : ℂ) * ζ ^ 5 - ((31 / 474) : ℂ) * ζ ^ 6 - ((1105 / 37446) : ℂ) * ζ ^ 7 + ((3157 / 37446) : ℂ) * ζ ^ 8 + ((5711 / 37446) : ℂ) * ζ ^ 9 + ((7475 / 37446) : ℂ) * ζ ^ 10 - ((3403 / 37446) : ℂ) * ζ ^ 11 + ((805 / 18723) : ℂ) * ζ ^ 12 - ((2269 / 37446) : ℂ) * ζ ^ 13 - ((529 / 18723) : ℂ) * ζ ^ 14 - ((575 / 37446) : ℂ) * ζ ^ 15 - ((4490 / 18723) : ℂ) * ζ ^ 16 + ((811 / 37446) : ℂ) * ζ ^ 17 + ((4555 / 18723) : ℂ) * ζ ^ 18 - ((1552 / 18723) : ℂ) * ζ ^ 19 + ((2225 / 18723) : ℂ) * ζ ^ 20 - ((747 / 6241) : ℂ) * ζ ^ 21 + ((1000 / 18723) : ℂ) * ζ ^ 22 + ((1133 / 37446) : ℂ) * ζ ^ 23 - ((1459 / 37446) : ℂ) * ζ ^ 24 - ((568 / 18723) : ℂ) * ζ ^ 25 - ((4691 / 37446) : ℂ) * ζ ^ 26 + ((710 / 6241) : ℂ) * ζ ^ 27 + ((305 / 12482) : ℂ) * ζ ^ 28 - ((621 / 12482) : ℂ) * ζ ^ 29 + ((60 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep04Coefficient12 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep04CoefficientIdentity12 :
    row18_reducedY45_combinationStep04Coefficient12 =
      row18_reducedY45_combinationStep03Coefficient12 +
        row18_reducedY45_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep04Coefficient12 row18_reducedY45_combinationStep03Coefficient12 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep04Coefficient13 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep04CoefficientIdentity13 :
    row18_reducedY45_combinationStep04Coefficient13 =
      row18_reducedY45_combinationStep03Coefficient13 +
        row18_reducedY45_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep04Coefficient13 row18_reducedY45_combinationStep03Coefficient13 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep04Coefficient14 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep04CoefficientIdentity14 :
    row18_reducedY45_combinationStep04Coefficient14 =
      row18_reducedY45_combinationStep03Coefficient14 +
        row18_reducedY45_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep04Coefficient14 row18_reducedY45_combinationStep03Coefficient14 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep04Coefficient15 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep04CoefficientIdentity15 :
    row18_reducedY45_combinationStep04Coefficient15 =
      row18_reducedY45_combinationStep03Coefficient15 +
        row18_reducedY45_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep04Coefficient15 row18_reducedY45_combinationStep03Coefficient15 row18_reducedY45_combinationStep04Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY45_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY45_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY45_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY45_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY45_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY45_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY45_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY45_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY45_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY45_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY45_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY45_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY45_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY45_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY45_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY45_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY45_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY45_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation05
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY45_combinationStep04CoefficientIdentity00,
      row18_reducedY45_combinationStep04CoefficientIdentity01,
      row18_reducedY45_combinationStep04CoefficientIdentity02,
      row18_reducedY45_combinationStep04CoefficientIdentity03,
      row18_reducedY45_combinationStep04CoefficientIdentity04,
      row18_reducedY45_combinationStep04CoefficientIdentity05,
      row18_reducedY45_combinationStep04CoefficientIdentity06,
      row18_reducedY45_combinationStep04CoefficientIdentity07,
      row18_reducedY45_combinationStep04CoefficientIdentity08,
      row18_reducedY45_combinationStep04CoefficientIdentity09,
      row18_reducedY45_combinationStep04CoefficientIdentity10,
      row18_reducedY45_combinationStep04CoefficientIdentity11,
      row18_reducedY45_combinationStep04CoefficientIdentity12,
      row18_reducedY45_combinationStep04CoefficientIdentity13,
      row18_reducedY45_combinationStep04CoefficientIdentity14,
      row18_reducedY45_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY45_combinationStep04Multiplier * equation

private def row18_reducedY45_combinationStep05Multiplier : ℂ :=
  (-((472 / 395) : ℂ) + ((4066 / 1185) : ℂ) * ζ ^ 1 - ((4066 / 1185) : ℂ) * ζ ^ 3 + ((556 / 395) : ℂ) * ζ ^ 5 + ((464 / 237) : ℂ) * ζ ^ 6 + ((236 / 395) : ℂ) * ζ ^ 8 - ((204 / 395) : ℂ) * ζ ^ 9 + ((2398 / 1185) : ℂ) * ζ ^ 11 + ((108 / 395) : ℂ) * ζ ^ 12 - ((4066 / 1185) : ℂ) * ζ ^ 13 + ((1714 / 1185) : ℂ) * ζ ^ 15 - ((4066 / 1185) : ℂ) * ζ ^ 17 - ((360 / 79) : ℂ) * ζ ^ 18 - ((784 / 395) : ℂ) * ζ ^ 21 - ((364 / 395) : ℂ) * ζ ^ 24 + ((2398 / 1185) : ℂ) * ζ ^ 25 - ((204 / 395) : ℂ) * ζ ^ 27 - ((236 / 395) : ℂ) * ζ ^ 28 + ((4066 / 1185) : ℂ) * ζ ^ 29 + ((464 / 237) : ℂ) * ζ ^ 30 - ((2398 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY45_combinationStep05Coefficient00 : ℂ :=
  (-((8 / 5) : ℂ) + ((13 / 5) : ℂ) * ζ ^ 1 + ((57 / 10) : ℂ) * ζ ^ 2 - ((5 / 2) : ℂ) * ζ ^ 3 + ((39 / 5) : ℂ) * ζ ^ 5 + ((33 / 10) : ℂ) * ζ ^ 6 + ((34 / 5) : ℂ) * ζ ^ 8 + ((13 / 10) : ℂ) * ζ ^ 9 + ((13 / 2) : ℂ) * ζ ^ 11 + ((12 / 5) : ℂ) * ζ ^ 12 - ((13 / 5) : ℂ) * ζ ^ 13 + ((5 / 2) : ℂ) * ζ ^ 15 - ((13 / 5) : ℂ) * ζ ^ 17 - ((41 / 10) : ℂ) * ζ ^ 18 - ((26 / 5) : ℂ) * ζ ^ 21 - ((57 / 10) : ℂ) * ζ ^ 22 - ((57 / 10) : ℂ) * ζ ^ 24 - ((26 / 5) : ℂ) * ζ ^ 25 - ((13 / 2) : ℂ) * ζ ^ 27 - ((34 / 5) : ℂ) * ζ ^ 28 + ((13 / 5) : ℂ) * ζ ^ 29 - ((11 / 10) : ℂ) * ζ ^ 30 - ((13 / 2) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep05CoefficientIdentity00 :
    row18_reducedY45_combinationStep05Coefficient00 =
      row18_reducedY45_combinationStep04Coefficient00 +
        row18_reducedY45_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep05Coefficient00 row18_reducedY45_combinationStep04Coefficient00 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep05Coefficient01 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep05CoefficientIdentity01 :
    row18_reducedY45_combinationStep05Coefficient01 =
      row18_reducedY45_combinationStep04Coefficient01 +
        row18_reducedY45_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep05Coefficient01 row18_reducedY45_combinationStep04Coefficient01 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep05Coefficient02 : ℂ :=
  (((103 / 79) : ℂ) - ((10897 / 2370) : ℂ) * ζ ^ 1 + ((10897 / 2370) : ℂ) * ζ ^ 3 - ((6851 / 2370) : ℂ) * ζ ^ 5 + ((866 / 237) : ℂ) * ζ ^ 6 - ((103 / 158) : ℂ) * ζ ^ 8 + ((4747 / 1185) : ℂ) * ζ ^ 9 - ((2023 / 1185) : ℂ) * ζ ^ 11 + ((649 / 237) : ℂ) * ζ ^ 12 + ((10897 / 2370) : ℂ) * ζ ^ 13 + ((1261 / 1185) : ℂ) * ζ ^ 15 + ((10897 / 2370) : ℂ) * ζ ^ 17 + ((695 / 474) : ℂ) * ζ ^ 18 + ((4473 / 790) : ℂ) * ζ ^ 21 + ((958 / 237) : ℂ) * ζ ^ 24 - ((2023 / 1185) : ℂ) * ζ ^ 25 + ((4747 / 1185) : ℂ) * ζ ^ 27 + ((103 / 158) : ℂ) * ζ ^ 28 - ((10897 / 2370) : ℂ) * ζ ^ 29 + ((866 / 237) : ℂ) * ζ ^ 30 + ((2023 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep05CoefficientIdentity02 :
    row18_reducedY45_combinationStep05Coefficient02 =
      row18_reducedY45_combinationStep04Coefficient02 +
        row18_reducedY45_combinationStep05Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep05Coefficient02 row18_reducedY45_combinationStep04Coefficient02 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 (-((177847 / 93615) : ℂ) + ((38102 / 93615) : ℂ) * ζ ^ 1 + ((82543 / 187230) : ℂ) * ζ ^ 2 - ((86071 / 62410) : ℂ) * ζ ^ 3 + ((337397 / 187230) : ℂ) * ζ ^ 4 + ((24553 / 62410) : ℂ) * ζ ^ 5 - ((9818 / 93615) : ℂ) * ζ ^ 6 + ((45009 / 62410) : ℂ) * ζ ^ 7 - ((48527 / 37446) : ℂ) * ζ ^ 8 + ((85339 / 93615) : ℂ) * ζ ^ 9 - ((27031 / 93615) : ℂ) * ζ ^ 10 - ((48947 / 93615) : ℂ) * ζ ^ 11 + ((37069 / 93615) : ℂ) * ζ ^ 12 - ((29532 / 31205) : ℂ) * ζ ^ 13 + ((134047 / 187230) : ℂ) * ζ ^ 14 - ((57043 / 62410) : ℂ) * ζ ^ 15 - ((75917 / 93615) : ℂ) * ζ ^ 16 + ((67276 / 93615) : ℂ) * ζ ^ 17 - ((72433 / 93615) : ℂ) * ζ ^ 18 + ((86302 / 93615) : ℂ) * ζ ^ 19 + ((51842 / 93615) : ℂ) * ζ ^ 20 - ((70009 / 187230) : ℂ) * ζ ^ 21 + ((18919 / 37446) : ℂ) * ζ ^ 22 - ((3161 / 187230) : ℂ) * ζ ^ 23 + ((9778 / 93615) : ℂ) * ζ ^ 24 - ((90497 / 187230) : ℂ) * ζ ^ 25 - ((7829 / 93615) : ℂ) * ζ ^ 26 + ((5747 / 62410) : ℂ) * ζ ^ 27 - ((3287 / 187230) : ℂ) * ζ ^ 28 + ((5904 / 31205) : ℂ) * ζ ^ 29 - ((8393 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep05Coefficient03 : ℂ :=
  (((1 / 2) : ℂ) + ((527 / 474) : ℂ) * ζ ^ 1 + ((197 / 158) : ℂ) * ζ ^ 2 - ((259 / 237) : ℂ) * ζ ^ 3 + ((458 / 237) : ℂ) * ζ ^ 5 + ((7 / 6) : ℂ) * ζ ^ 6 + ((271 / 474) : ℂ) * ζ ^ 8 - ((23 / 158) : ℂ) * ζ ^ 9 + ((653 / 474) : ℂ) * ζ ^ 11 + ((19 / 237) : ℂ) * ζ ^ 12 - ((527 / 474) : ℂ) * ζ ^ 13 + ((259 / 237) : ℂ) * ζ ^ 15 - ((527 / 474) : ℂ) * ζ ^ 17 - ((138 / 79) : ℂ) * ζ ^ 18 - ((389 / 474) : ℂ) * ζ ^ 21 - ((197 / 158) : ℂ) * ζ ^ 22 - ((197 / 158) : ℂ) * ζ ^ 24 - ((389 / 474) : ℂ) * ζ ^ 25 - ((653 / 474) : ℂ) * ζ ^ 27 - ((271 / 474) : ℂ) * ζ ^ 28 + ((527 / 474) : ℂ) * ζ ^ 29 + ((160 / 237) : ℂ) * ζ ^ 30 - ((653 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep05CoefficientIdentity03 :
    row18_reducedY45_combinationStep05Coefficient03 =
      row18_reducedY45_combinationStep04Coefficient03 +
        row18_reducedY45_combinationStep05Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep05Coefficient03 row18_reducedY45_combinationStep04Coefficient03 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 (((19814 / 93615) : ℂ) + ((130841 / 93615) : ℂ) * ζ ^ 1 - ((266746 / 93615) : ℂ) * ζ ^ 2 + ((44449 / 62410) : ℂ) * ζ ^ 3 + ((37207 / 37446) : ℂ) * ζ ^ 4 - ((120181 / 62410) : ℂ) * ζ ^ 5 + ((13496 / 18723) : ℂ) * ζ ^ 6 - ((65867 / 187230) : ℂ) * ζ ^ 7 - ((68833 / 93615) : ℂ) * ζ ^ 8 - ((198199 / 187230) : ℂ) * ζ ^ 9 - ((1283 / 62410) : ℂ) * ζ ^ 10 - ((8667 / 31205) : ℂ) * ζ ^ 11 - ((80227 / 62410) : ℂ) * ζ ^ 12 + ((25643 / 93615) : ℂ) * ζ ^ 13 - ((9094 / 18723) : ℂ) * ζ ^ 14 + ((9293 / 18723) : ℂ) * ζ ^ 15 - ((9127 / 187230) : ℂ) * ζ ^ 16 - ((50917 / 31205) : ℂ) * ζ ^ 17 + ((174941 / 93615) : ℂ) * ζ ^ 18 + ((55504 / 93615) : ℂ) * ζ ^ 19 - ((31187 / 37446) : ℂ) * ζ ^ 20 + ((80782 / 93615) : ℂ) * ζ ^ 21 + ((34539 / 62410) : ℂ) * ζ ^ 22 - ((24791 / 187230) : ℂ) * ζ ^ 23 - ((32147 / 37446) : ℂ) * ζ ^ 24 + ((115543 / 93615) : ℂ) * ζ ^ 25 - ((49712 / 93615) : ℂ) * ζ ^ 26 - ((43471 / 93615) : ℂ) * ζ ^ 27 + ((95492 / 93615) : ℂ) * ζ ^ 28 - ((24833 / 93615) : ℂ) * ζ ^ 29 - ((15587 / 187230) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep05Coefficient04 : ℂ :=
  (((8 / 5) : ℂ) - ((13 / 5) : ℂ) * ζ ^ 1 - ((57 / 10) : ℂ) * ζ ^ 2 + ((5 / 2) : ℂ) * ζ ^ 3 - ((39 / 5) : ℂ) * ζ ^ 5 - ((33 / 10) : ℂ) * ζ ^ 6 - ((34 / 5) : ℂ) * ζ ^ 8 - ((13 / 10) : ℂ) * ζ ^ 9 - ((13 / 2) : ℂ) * ζ ^ 11 - ((12 / 5) : ℂ) * ζ ^ 12 + ((13 / 5) : ℂ) * ζ ^ 13 - ((5 / 2) : ℂ) * ζ ^ 15 + ((13 / 5) : ℂ) * ζ ^ 17 + ((41 / 10) : ℂ) * ζ ^ 18 + ((26 / 5) : ℂ) * ζ ^ 21 + ((57 / 10) : ℂ) * ζ ^ 22 + ((57 / 10) : ℂ) * ζ ^ 24 + ((26 / 5) : ℂ) * ζ ^ 25 + ((13 / 2) : ℂ) * ζ ^ 27 + ((34 / 5) : ℂ) * ζ ^ 28 - ((13 / 5) : ℂ) * ζ ^ 29 + ((11 / 10) : ℂ) * ζ ^ 30 + ((13 / 2) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep05CoefficientIdentity04 :
    row18_reducedY45_combinationStep05Coefficient04 =
      row18_reducedY45_combinationStep04Coefficient04 +
        row18_reducedY45_combinationStep05Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep05Coefficient04 row18_reducedY45_combinationStep04Coefficient04 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 (-((19814 / 93615) : ℂ) - ((130841 / 93615) : ℂ) * ζ ^ 1 + ((266746 / 93615) : ℂ) * ζ ^ 2 - ((44449 / 62410) : ℂ) * ζ ^ 3 - ((37207 / 37446) : ℂ) * ζ ^ 4 + ((120181 / 62410) : ℂ) * ζ ^ 5 - ((13496 / 18723) : ℂ) * ζ ^ 6 + ((65867 / 187230) : ℂ) * ζ ^ 7 + ((68833 / 93615) : ℂ) * ζ ^ 8 + ((198199 / 187230) : ℂ) * ζ ^ 9 + ((1283 / 62410) : ℂ) * ζ ^ 10 + ((8667 / 31205) : ℂ) * ζ ^ 11 + ((80227 / 62410) : ℂ) * ζ ^ 12 - ((25643 / 93615) : ℂ) * ζ ^ 13 + ((9094 / 18723) : ℂ) * ζ ^ 14 - ((9293 / 18723) : ℂ) * ζ ^ 15 + ((9127 / 187230) : ℂ) * ζ ^ 16 + ((50917 / 31205) : ℂ) * ζ ^ 17 - ((174941 / 93615) : ℂ) * ζ ^ 18 - ((55504 / 93615) : ℂ) * ζ ^ 19 + ((31187 / 37446) : ℂ) * ζ ^ 20 - ((80782 / 93615) : ℂ) * ζ ^ 21 - ((34539 / 62410) : ℂ) * ζ ^ 22 + ((24791 / 187230) : ℂ) * ζ ^ 23 + ((32147 / 37446) : ℂ) * ζ ^ 24 - ((115543 / 93615) : ℂ) * ζ ^ 25 + ((49712 / 93615) : ℂ) * ζ ^ 26 + ((43471 / 93615) : ℂ) * ζ ^ 27 - ((95492 / 93615) : ℂ) * ζ ^ 28 + ((24833 / 93615) : ℂ) * ζ ^ 29 + ((15587 / 187230) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep05Coefficient05 : ℂ :=
  (((1015 / 474) : ℂ) - ((436 / 237) : ℂ) * ζ ^ 1 - ((692 / 237) : ℂ) * ζ ^ 2 + ((1207 / 474) : ℂ) * ζ ^ 3 - ((615 / 158) : ℂ) * ζ ^ 5 - ((847 / 237) : ℂ) * ζ ^ 8 + ((305 / 474) : ℂ) * ζ ^ 9 - ((252 / 79) : ℂ) * ζ ^ 11 - ((56 / 79) : ℂ) * ζ ^ 12 + ((436 / 237) : ℂ) * ζ ^ 13 - ((39 / 79) : ℂ) * ζ ^ 15 + ((436 / 237) : ℂ) * ζ ^ 17 + ((692 / 237) : ℂ) * ζ ^ 18 + ((693 / 158) : ℂ) * ζ ^ 21 + ((692 / 237) : ℂ) * ζ ^ 22 + ((1015 / 237) : ℂ) * ζ ^ 24 + ((973 / 474) : ℂ) * ζ ^ 25 + ((693 / 158) : ℂ) * ζ ^ 27 + ((847 / 237) : ℂ) * ζ ^ 28 - ((436 / 237) : ℂ) * ζ ^ 29 + ((557 / 474) : ℂ) * ζ ^ 30 + ((252 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep05CoefficientIdentity05 :
    row18_reducedY45_combinationStep05Coefficient05 =
      row18_reducedY45_combinationStep04Coefficient05 +
        row18_reducedY45_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep05Coefficient05 row18_reducedY45_combinationStep04Coefficient05 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep05Coefficient06 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep05CoefficientIdentity06 :
    row18_reducedY45_combinationStep05Coefficient06 =
      row18_reducedY45_combinationStep04Coefficient06 +
        row18_reducedY45_combinationStep05Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep05Coefficient06 row18_reducedY45_combinationStep04Coefficient06 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 (((3776 / 31205) : ℂ) + ((393131 / 187230) : ℂ) * ζ ^ 1 + ((4279 / 62410) : ℂ) * ζ ^ 2 + ((20909 / 31205) : ℂ) * ζ ^ 3 + ((124883 / 93615) : ℂ) * ζ ^ 4 - ((13085 / 12482) : ℂ) * ζ ^ 5 - ((117336 / 31205) : ℂ) * ζ ^ 6 - ((10528 / 6241) : ℂ) * ζ ^ 7 - ((128023 / 187230) : ℂ) * ζ ^ 8 + ((382003 / 187230) : ℂ) * ζ ^ 9 + ((24901 / 12482) : ℂ) * ζ ^ 10 - ((187082 / 93615) : ℂ) * ζ ^ 11 - ((263467 / 187230) : ℂ) * ζ ^ 12 - ((81476 / 31205) : ℂ) * ζ ^ 13 - ((161317 / 187230) : ℂ) * ζ ^ 14 + ((128141 / 62410) : ℂ) * ζ ^ 15 + ((8588 / 31205) : ℂ) * ζ ^ 16 + ((92009 / 93615) : ℂ) * ζ ^ 17 + ((74797 / 93615) : ℂ) * ζ ^ 18 + ((55069 / 37446) : ℂ) * ζ ^ 19 - ((34 / 1185) : ℂ) * ζ ^ 20 - ((156271 / 62410) : ℂ) * ζ ^ 21 + ((43969 / 37446) : ℂ) * ζ ^ 22 + ((26276 / 31205) : ℂ) * ζ ^ 23 + ((37967 / 31205) : ℂ) * ζ ^ 24 + ((5409 / 6241) : ℂ) * ζ ^ 25 - ((20465 / 12482) : ℂ) * ζ ^ 26 - ((15102 / 31205) : ℂ) * ζ ^ 27 - ((16421 / 187230) : ℂ) * ζ ^ 28 - ((1852 / 93615) : ℂ) * ζ ^ 29 + ((16786 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep05Coefficient07 : ℂ :=
  (-((307 / 474) : ℂ) - ((163 / 158) : ℂ) * ζ ^ 1 - ((367 / 474) : ℂ) * ζ ^ 2 + ((286 / 237) : ℂ) * ζ ^ 3 - ((386 / 237) : ℂ) * ζ ^ 5 - ((169 / 158) : ℂ) * ζ ^ 6 - ((233 / 474) : ℂ) * ζ ^ 8 + ((103 / 474) : ℂ) * ζ ^ 9 - ((589 / 474) : ℂ) * ζ ^ 11 + ((70 / 237) : ℂ) * ζ ^ 12 + ((163 / 158) : ℂ) * ζ ^ 13 - ((286 / 237) : ℂ) * ζ ^ 15 + ((163 / 158) : ℂ) * ζ ^ 17 + ((337 / 237) : ℂ) * ζ ^ 18 + ((283 / 474) : ℂ) * ζ ^ 21 + ((367 / 474) : ℂ) * ζ ^ 22 + ((367 / 474) : ℂ) * ζ ^ 24 + ((283 / 474) : ℂ) * ζ ^ 25 + ((589 / 474) : ℂ) * ζ ^ 27 + ((233 / 474) : ℂ) * ζ ^ 28 - ((163 / 158) : ℂ) * ζ ^ 29 - ((67 / 237) : ℂ) * ζ ^ 30 + ((589 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep05CoefficientIdentity07 :
    row18_reducedY45_combinationStep05Coefficient07 =
      row18_reducedY45_combinationStep04Coefficient07 +
        row18_reducedY45_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep05Coefficient07 row18_reducedY45_combinationStep04Coefficient07 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep05Coefficient08 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep05CoefficientIdentity08 :
    row18_reducedY45_combinationStep05Coefficient08 =
      row18_reducedY45_combinationStep04Coefficient08 +
        row18_reducedY45_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep05Coefficient08 row18_reducedY45_combinationStep04Coefficient08 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep05Coefficient09 : ℂ :=
  (((105 / 158) : ℂ) - ((26 / 237) : ℂ) * ζ ^ 1 + ((20 / 237) : ℂ) * ζ ^ 2 - ((67 / 237) : ℂ) * ζ ^ 3 - ((149 / 474) : ℂ) * ζ ^ 5 - ((25 / 237) : ℂ) * ζ ^ 6 + ((64 / 237) : ℂ) * ζ ^ 8 + ((2 / 237) : ℂ) * ζ ^ 9 + ((23 / 79) : ℂ) * ζ ^ 11 + ((64 / 237) : ℂ) * ζ ^ 12 + ((26 / 237) : ℂ) * ζ ^ 13 + ((37 / 474) : ℂ) * ζ ^ 15 + ((26 / 237) : ℂ) * ζ ^ 17 + ((15 / 79) : ℂ) * ζ ^ 18 + ((31 / 79) : ℂ) * ζ ^ 21 - ((20 / 237) : ℂ) * ζ ^ 22 + ((97 / 474) : ℂ) * ζ ^ 25 - ((31 / 79) : ℂ) * ζ ^ 27 - ((64 / 237) : ℂ) * ζ ^ 28 - ((26 / 237) : ℂ) * ζ ^ 29 - ((25 / 474) : ℂ) * ζ ^ 30 - ((23 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep05CoefficientIdentity09 :
    row18_reducedY45_combinationStep05Coefficient09 =
      row18_reducedY45_combinationStep04Coefficient09 +
        row18_reducedY45_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep05Coefficient09 row18_reducedY45_combinationStep04Coefficient09 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep05Coefficient10 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep05CoefficientIdentity10 :
    row18_reducedY45_combinationStep05Coefficient10 =
      row18_reducedY45_combinationStep04Coefficient10 +
        row18_reducedY45_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep05Coefficient10 row18_reducedY45_combinationStep04Coefficient10 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep05Coefficient11 : ℂ :=
  (((35 / 237) : ℂ) - ((19 / 237) : ℂ) * ζ ^ 1 - ((112 / 237) : ℂ) * ζ ^ 2 - ((9 / 79) : ℂ) * ζ ^ 3 - ((24 / 79) : ℂ) * ζ ^ 5 - ((23 / 237) : ℂ) * ζ ^ 6 - ((19 / 237) : ℂ) * ζ ^ 8 - ((17 / 237) : ℂ) * ζ ^ 9 - ((32 / 237) : ℂ) * ζ ^ 11 - ((89 / 237) : ℂ) * ζ ^ 12 + ((19 / 237) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 + ((19 / 237) : ℂ) * ζ ^ 17 + ((77 / 237) : ℂ) * ζ ^ 18 + ((53 / 237) : ℂ) * ζ ^ 21 + ((112 / 237) : ℂ) * ζ ^ 22 + ((112 / 237) : ℂ) * ζ ^ 24 + ((53 / 237) : ℂ) * ζ ^ 25 + ((32 / 237) : ℂ) * ζ ^ 27 + ((19 / 237) : ℂ) * ζ ^ 28 - ((19 / 237) : ℂ) * ζ ^ 29 - ((31 / 79) : ℂ) * ζ ^ 30 + ((32 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep05CoefficientIdentity11 :
    row18_reducedY45_combinationStep05Coefficient11 =
      row18_reducedY45_combinationStep04Coefficient11 +
        row18_reducedY45_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep05Coefficient11 row18_reducedY45_combinationStep04Coefficient11 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep05Coefficient12 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep05CoefficientIdentity12 :
    row18_reducedY45_combinationStep05Coefficient12 =
      row18_reducedY45_combinationStep04Coefficient12 +
        row18_reducedY45_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep05Coefficient12 row18_reducedY45_combinationStep04Coefficient12 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep05Coefficient13 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep05CoefficientIdentity13 :
    row18_reducedY45_combinationStep05Coefficient13 =
      row18_reducedY45_combinationStep04Coefficient13 +
        row18_reducedY45_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep05Coefficient13 row18_reducedY45_combinationStep04Coefficient13 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep05Coefficient14 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep05CoefficientIdentity14 :
    row18_reducedY45_combinationStep05Coefficient14 =
      row18_reducedY45_combinationStep04Coefficient14 +
        row18_reducedY45_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep05Coefficient14 row18_reducedY45_combinationStep04Coefficient14 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep05Coefficient15 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep05CoefficientIdentity15 :
    row18_reducedY45_combinationStep05Coefficient15 =
      row18_reducedY45_combinationStep04Coefficient15 +
        row18_reducedY45_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep05Coefficient15 row18_reducedY45_combinationStep04Coefficient15 row18_reducedY45_combinationStep05Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY45_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY45_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY45_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY45_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY45_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY45_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY45_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY45_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY45_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY45_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY45_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY45_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY45_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY45_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY45_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY45_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY45_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY45_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY45_combinationStep05CoefficientIdentity00,
      row18_reducedY45_combinationStep05CoefficientIdentity01,
      row18_reducedY45_combinationStep05CoefficientIdentity02,
      row18_reducedY45_combinationStep05CoefficientIdentity03,
      row18_reducedY45_combinationStep05CoefficientIdentity04,
      row18_reducedY45_combinationStep05CoefficientIdentity05,
      row18_reducedY45_combinationStep05CoefficientIdentity06,
      row18_reducedY45_combinationStep05CoefficientIdentity07,
      row18_reducedY45_combinationStep05CoefficientIdentity08,
      row18_reducedY45_combinationStep05CoefficientIdentity09,
      row18_reducedY45_combinationStep05CoefficientIdentity10,
      row18_reducedY45_combinationStep05CoefficientIdentity11,
      row18_reducedY45_combinationStep05CoefficientIdentity12,
      row18_reducedY45_combinationStep05CoefficientIdentity13,
      row18_reducedY45_combinationStep05CoefficientIdentity14,
      row18_reducedY45_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY45_combinationStep05Multiplier * equation

private def row18_reducedY45_combinationStep06Multiplier : ℂ :=
  (-((22 / 237) : ℂ) + ((58 / 79) : ℂ) * ζ ^ 1 + ((14 / 237) : ℂ) * ζ ^ 2 - ((22 / 79) : ℂ) * ζ ^ 3 - ((62 / 79) : ℂ) * ζ ^ 6 + ((26 / 237) : ℂ) * ζ ^ 8 - ((164 / 237) : ℂ) * ζ ^ 9 - ((176 / 237) : ℂ) * ζ ^ 11 - ((200 / 237) : ℂ) * ζ ^ 12 - ((58 / 79) : ℂ) * ζ ^ 13 - ((22 / 79) : ℂ) * ζ ^ 15 - ((58 / 79) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 - ((58 / 79) : ℂ) * ζ ^ 21 - ((14 / 237) : ℂ) * ζ ^ 22 + ((14 / 237) : ℂ) * ζ ^ 24 + ((58 / 79) : ℂ) * ζ ^ 25 - ((176 / 237) : ℂ) * ζ ^ 27 - ((26 / 237) : ℂ) * ζ ^ 28 + ((58 / 79) : ℂ) * ζ ^ 29 + ((40 / 237) : ℂ) * ζ ^ 30 + ((176 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY45_combinationStep06Coefficient00 : ℂ :=
  (-((8 / 5) : ℂ) + ((13 / 5) : ℂ) * ζ ^ 1 + ((57 / 10) : ℂ) * ζ ^ 2 - ((5 / 2) : ℂ) * ζ ^ 3 + ((39 / 5) : ℂ) * ζ ^ 5 + ((33 / 10) : ℂ) * ζ ^ 6 + ((34 / 5) : ℂ) * ζ ^ 8 + ((13 / 10) : ℂ) * ζ ^ 9 + ((13 / 2) : ℂ) * ζ ^ 11 + ((12 / 5) : ℂ) * ζ ^ 12 - ((13 / 5) : ℂ) * ζ ^ 13 + ((5 / 2) : ℂ) * ζ ^ 15 - ((13 / 5) : ℂ) * ζ ^ 17 - ((41 / 10) : ℂ) * ζ ^ 18 - ((26 / 5) : ℂ) * ζ ^ 21 - ((57 / 10) : ℂ) * ζ ^ 22 - ((57 / 10) : ℂ) * ζ ^ 24 - ((26 / 5) : ℂ) * ζ ^ 25 - ((13 / 2) : ℂ) * ζ ^ 27 - ((34 / 5) : ℂ) * ζ ^ 28 + ((13 / 5) : ℂ) * ζ ^ 29 - ((11 / 10) : ℂ) * ζ ^ 30 - ((13 / 2) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep06CoefficientIdentity00 :
    row18_reducedY45_combinationStep06Coefficient00 =
      row18_reducedY45_combinationStep05Coefficient00 +
        row18_reducedY45_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep06Coefficient00 row18_reducedY45_combinationStep05Coefficient00 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep06Coefficient01 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep06CoefficientIdentity01 :
    row18_reducedY45_combinationStep06Coefficient01 =
      row18_reducedY45_combinationStep05Coefficient01 +
        row18_reducedY45_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep06Coefficient01 row18_reducedY45_combinationStep05Coefficient01 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep06Coefficient02 : ℂ :=
  (((170 / 79) : ℂ) - ((1592 / 395) : ℂ) * ζ ^ 1 + ((1592 / 395) : ℂ) * ζ ^ 3 - ((2983 / 1185) : ℂ) * ζ ^ 5 + ((964 / 237) : ℂ) * ζ ^ 6 - ((85 / 79) : ℂ) * ζ ^ 8 + ((1439 / 395) : ℂ) * ζ ^ 9 - ((1793 / 1185) : ℂ) * ζ ^ 11 + ((174 / 79) : ℂ) * ζ ^ 12 + ((1592 / 395) : ℂ) * ζ ^ 13 + ((2056 / 1185) : ℂ) * ζ ^ 15 + ((1592 / 395) : ℂ) * ζ ^ 17 + ((227 / 237) : ℂ) * ζ ^ 18 + ((6832 / 1185) : ℂ) * ζ ^ 21 + ((344 / 79) : ℂ) * ζ ^ 24 - ((1793 / 1185) : ℂ) * ζ ^ 25 + ((1439 / 395) : ℂ) * ζ ^ 27 + ((85 / 79) : ℂ) * ζ ^ 28 - ((1592 / 395) : ℂ) * ζ ^ 29 + ((964 / 237) : ℂ) * ζ ^ 30 + ((1793 / 1185) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep06CoefficientIdentity02 :
    row18_reducedY45_combinationStep06Coefficient02 =
      row18_reducedY45_combinationStep05Coefficient02 +
        row18_reducedY45_combinationStep06Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep06Coefficient02 row18_reducedY45_combinationStep05Coefficient02 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 (-((16088 / 18723) : ℂ) - ((2967 / 6241) : ℂ) * ζ ^ 1 - ((493 / 18723) : ℂ) * ζ ^ 2 + ((21127 / 37446) : ℂ) * ζ ^ 3 + ((5099 / 6241) : ℂ) * ζ ^ 4 + ((548 / 6241) : ℂ) * ζ ^ 5 - ((8807 / 18723) : ℂ) * ζ ^ 6 - ((8480 / 18723) : ℂ) * ζ ^ 7 - ((14357 / 37446) : ℂ) * ζ ^ 8 + ((1958 / 18723) : ℂ) * ζ ^ 9 + ((5551 / 18723) : ℂ) * ζ ^ 10 + ((3164 / 18723) : ℂ) * ζ ^ 11 + ((2221 / 37446) : ℂ) * ζ ^ 12 - ((739 / 18723) : ℂ) * ζ ^ 13 - ((1073 / 12482) : ℂ) * ζ ^ 14 - ((919 / 6241) : ℂ) * ζ ^ 15 - ((2285 / 18723) : ℂ) * ζ ^ 16 + ((599 / 6241) : ℂ) * ζ ^ 17 + ((1312 / 6241) : ℂ) * ζ ^ 18 + ((2103 / 6241) : ℂ) * ζ ^ 19 + ((1321 / 18723) : ℂ) * ζ ^ 20 - ((3015 / 12482) : ℂ) * ζ ^ 21 - ((2777 / 12482) : ℂ) * ζ ^ 22 - ((9911 / 37446) : ℂ) * ζ ^ 23 + ((1321 / 18723) : ℂ) * ζ ^ 24 + ((7175 / 18723) : ℂ) * ζ ^ 25 + ((4633 / 37446) : ℂ) * ζ ^ 26 + ((317 / 12482) : ℂ) * ζ ^ 27 - ((3409 / 37446) : ℂ) * ζ ^ 28 - ((754 / 6241) : ℂ) * ζ ^ 29 - ((220 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep06Coefficient03 : ℂ :=
  (-((35 / 237) : ℂ) + ((19 / 237) : ℂ) * ζ ^ 1 + ((112 / 237) : ℂ) * ζ ^ 2 + ((9 / 79) : ℂ) * ζ ^ 3 + ((24 / 79) : ℂ) * ζ ^ 5 + ((23 / 237) : ℂ) * ζ ^ 6 + ((19 / 237) : ℂ) * ζ ^ 8 + ((17 / 237) : ℂ) * ζ ^ 9 + ((32 / 237) : ℂ) * ζ ^ 11 + ((89 / 237) : ℂ) * ζ ^ 12 - ((19 / 237) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 - ((19 / 237) : ℂ) * ζ ^ 17 - ((77 / 237) : ℂ) * ζ ^ 18 - ((53 / 237) : ℂ) * ζ ^ 21 - ((112 / 237) : ℂ) * ζ ^ 22 - ((112 / 237) : ℂ) * ζ ^ 24 - ((53 / 237) : ℂ) * ζ ^ 25 - ((32 / 237) : ℂ) * ζ ^ 27 - ((19 / 237) : ℂ) * ζ ^ 28 + ((19 / 237) : ℂ) * ζ ^ 29 + ((31 / 79) : ℂ) * ζ ^ 30 - ((32 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep06CoefficientIdentity03 :
    row18_reducedY45_combinationStep06Coefficient03 =
      row18_reducedY45_combinationStep05Coefficient03 +
        row18_reducedY45_combinationStep06Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep06Coefficient03 row18_reducedY45_combinationStep05Coefficient03 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 (((7967 / 12482) : ℂ) + ((6798 / 6241) : ℂ) * ζ ^ 1 + ((32537 / 37446) : ℂ) * ζ ^ 2 - ((32035 / 37446) : ℂ) * ζ ^ 3 - ((15719 / 18723) : ℂ) * ζ ^ 4 + ((6833 / 18723) : ℂ) * ζ ^ 5 + ((15607 / 37446) : ℂ) * ζ ^ 6 + ((4570 / 6241) : ℂ) * ζ ^ 7 + ((16651 / 18723) : ℂ) * ζ ^ 8 - ((9362 / 18723) : ℂ) * ζ ^ 9 - ((9293 / 37446) : ℂ) * ζ ^ 10 - ((1533 / 12482) : ℂ) * ζ ^ 11 - ((13846 / 18723) : ℂ) * ζ ^ 12 - ((589 / 6241) : ℂ) * ζ ^ 13 + ((8714 / 18723) : ℂ) * ζ ^ 14 + ((863 / 12482) : ℂ) * ζ ^ 15 + ((10603 / 18723) : ℂ) * ζ ^ 16 + ((3844 / 18723) : ℂ) * ζ ^ 17 - ((21166 / 18723) : ℂ) * ζ ^ 18 - ((14281 / 18723) : ℂ) * ζ ^ 19 - ((40 / 6241) : ℂ) * ζ ^ 20 + ((1397 / 37446) : ℂ) * ζ ^ 21 + ((335 / 474) : ℂ) * ζ ^ 22 + ((1931 / 18723) : ℂ) * ζ ^ 23 - ((12967 / 18723) : ℂ) * ζ ^ 24 - ((2387 / 12482) : ℂ) * ζ ^ 25 - ((11833 / 37446) : ℂ) * ζ ^ 26 + ((1960 / 18723) : ℂ) * ζ ^ 27 + ((1322 / 6241) : ℂ) * ζ ^ 28 + ((1336 / 18723) : ℂ) * ζ ^ 29 + ((1232 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep06Coefficient04 : ℂ :=
  (((8 / 5) : ℂ) - ((13 / 5) : ℂ) * ζ ^ 1 - ((57 / 10) : ℂ) * ζ ^ 2 + ((5 / 2) : ℂ) * ζ ^ 3 - ((39 / 5) : ℂ) * ζ ^ 5 - ((33 / 10) : ℂ) * ζ ^ 6 - ((34 / 5) : ℂ) * ζ ^ 8 - ((13 / 10) : ℂ) * ζ ^ 9 - ((13 / 2) : ℂ) * ζ ^ 11 - ((12 / 5) : ℂ) * ζ ^ 12 + ((13 / 5) : ℂ) * ζ ^ 13 - ((5 / 2) : ℂ) * ζ ^ 15 + ((13 / 5) : ℂ) * ζ ^ 17 + ((41 / 10) : ℂ) * ζ ^ 18 + ((26 / 5) : ℂ) * ζ ^ 21 + ((57 / 10) : ℂ) * ζ ^ 22 + ((57 / 10) : ℂ) * ζ ^ 24 + ((26 / 5) : ℂ) * ζ ^ 25 + ((13 / 2) : ℂ) * ζ ^ 27 + ((34 / 5) : ℂ) * ζ ^ 28 - ((13 / 5) : ℂ) * ζ ^ 29 + ((11 / 10) : ℂ) * ζ ^ 30 + ((13 / 2) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep06CoefficientIdentity04 :
    row18_reducedY45_combinationStep06Coefficient04 =
      row18_reducedY45_combinationStep05Coefficient04 +
        row18_reducedY45_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep06Coefficient04 row18_reducedY45_combinationStep05Coefficient04 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep06Coefficient05 : ℂ :=
  (((219 / 79) : ℂ) - ((195 / 79) : ℂ) * ζ ^ 1 - ((573 / 158) : ℂ) * ζ ^ 2 + ((509 / 158) : ℂ) * ζ ^ 3 - ((813 / 158) : ℂ) * ζ ^ 5 - ((737 / 158) : ℂ) * ζ ^ 8 + ((131 / 158) : ℂ) * ζ ^ 9 - ((320 / 79) : ℂ) * ζ ^ 11 - ((139 / 158) : ℂ) * ζ ^ 12 + ((195 / 79) : ℂ) * ζ ^ 13 - ((43 / 79) : ℂ) * ζ ^ 15 + ((195 / 79) : ℂ) * ζ ^ 17 + ((573 / 158) : ℂ) * ζ ^ 18 + ((899 / 158) : ℂ) * ζ ^ 21 + ((573 / 158) : ℂ) * ζ ^ 22 + ((438 / 79) : ℂ) * ζ ^ 24 + ((423 / 158) : ℂ) * ζ ^ 25 + ((899 / 158) : ℂ) * ζ ^ 27 + ((737 / 158) : ℂ) * ζ ^ 28 - ((195 / 79) : ℂ) * ζ ^ 29 + ((132 / 79) : ℂ) * ζ ^ 30 + ((320 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep06CoefficientIdentity05 :
    row18_reducedY45_combinationStep06Coefficient05 =
      row18_reducedY45_combinationStep05Coefficient05 +
        row18_reducedY45_combinationStep06Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep06Coefficient05 row18_reducedY45_combinationStep05Coefficient05 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 (-((11431 / 18723) : ℂ) + ((8302 / 18723) : ℂ) * ζ ^ 1 + ((16738 / 18723) : ℂ) * ζ ^ 2 - ((7635 / 12482) : ℂ) * ζ ^ 3 + ((8866 / 18723) : ℂ) * ζ ^ 4 + ((4917 / 6241) : ℂ) * ζ ^ 5 - ((8974 / 18723) : ℂ) * ζ ^ 6 + ((8809 / 37446) : ℂ) * ζ ^ 7 + ((9421 / 18723) : ℂ) * ζ ^ 8 - ((8489 / 18723) : ℂ) * ζ ^ 9 + ((2006 / 18723) : ℂ) * ζ ^ 10 + ((3113 / 6241) : ℂ) * ζ ^ 11 - ((7609 / 12482) : ℂ) * ζ ^ 12 + ((6277 / 18723) : ℂ) * ζ ^ 13 + ((2363 / 37446) : ℂ) * ζ ^ 14 - ((21311 / 37446) : ℂ) * ζ ^ 15 + ((15059 / 37446) : ℂ) * ζ ^ 16 + ((7025 / 37446) : ℂ) * ζ ^ 17 - ((10495 / 18723) : ℂ) * ζ ^ 18 + ((1717 / 6241) : ℂ) * ζ ^ 19 - ((142 / 18723) : ℂ) * ζ ^ 20 - ((8687 / 18723) : ℂ) * ζ ^ 21 - ((1390 / 18723) : ℂ) * ζ ^ 22 + ((700 / 18723) : ℂ) * ζ ^ 23 - ((6781 / 18723) : ℂ) * ζ ^ 24 + ((571 / 12482) : ℂ) * ζ ^ 25 + ((2707 / 12482) : ℂ) * ζ ^ 26 - ((3231 / 12482) : ℂ) * ζ ^ 27 + ((5269 / 37446) : ℂ) * ζ ^ 28 - ((2506 / 18723) : ℂ) * ζ ^ 29 - ((572 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep06Coefficient06 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep06CoefficientIdentity06 :
    row18_reducedY45_combinationStep06Coefficient06 =
      row18_reducedY45_combinationStep05Coefficient06 +
        row18_reducedY45_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep06Coefficient06 row18_reducedY45_combinationStep05Coefficient06 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep06Coefficient07 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep06CoefficientIdentity07 :
    row18_reducedY45_combinationStep06Coefficient07 =
      row18_reducedY45_combinationStep05Coefficient07 +
        row18_reducedY45_combinationStep06Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep06Coefficient07 row18_reducedY45_combinationStep05Coefficient07 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 (-((7967 / 12482) : ℂ) - ((6798 / 6241) : ℂ) * ζ ^ 1 - ((32537 / 37446) : ℂ) * ζ ^ 2 + ((32035 / 37446) : ℂ) * ζ ^ 3 + ((15719 / 18723) : ℂ) * ζ ^ 4 - ((6833 / 18723) : ℂ) * ζ ^ 5 - ((15607 / 37446) : ℂ) * ζ ^ 6 - ((4570 / 6241) : ℂ) * ζ ^ 7 - ((16651 / 18723) : ℂ) * ζ ^ 8 + ((9362 / 18723) : ℂ) * ζ ^ 9 + ((9293 / 37446) : ℂ) * ζ ^ 10 + ((1533 / 12482) : ℂ) * ζ ^ 11 + ((13846 / 18723) : ℂ) * ζ ^ 12 + ((589 / 6241) : ℂ) * ζ ^ 13 - ((8714 / 18723) : ℂ) * ζ ^ 14 - ((863 / 12482) : ℂ) * ζ ^ 15 - ((10603 / 18723) : ℂ) * ζ ^ 16 - ((3844 / 18723) : ℂ) * ζ ^ 17 + ((21166 / 18723) : ℂ) * ζ ^ 18 + ((14281 / 18723) : ℂ) * ζ ^ 19 + ((40 / 6241) : ℂ) * ζ ^ 20 - ((1397 / 37446) : ℂ) * ζ ^ 21 - ((335 / 474) : ℂ) * ζ ^ 22 - ((1931 / 18723) : ℂ) * ζ ^ 23 + ((12967 / 18723) : ℂ) * ζ ^ 24 + ((2387 / 12482) : ℂ) * ζ ^ 25 + ((11833 / 37446) : ℂ) * ζ ^ 26 - ((1960 / 18723) : ℂ) * ζ ^ 27 - ((1322 / 6241) : ℂ) * ζ ^ 28 - ((1336 / 18723) : ℂ) * ζ ^ 29 - ((1232 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep06Coefficient08 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep06CoefficientIdentity08 :
    row18_reducedY45_combinationStep06Coefficient08 =
      row18_reducedY45_combinationStep05Coefficient08 +
        row18_reducedY45_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep06Coefficient08 row18_reducedY45_combinationStep05Coefficient08 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep06Coefficient09 : ℂ :=
  (((105 / 158) : ℂ) - ((26 / 237) : ℂ) * ζ ^ 1 + ((20 / 237) : ℂ) * ζ ^ 2 - ((67 / 237) : ℂ) * ζ ^ 3 - ((149 / 474) : ℂ) * ζ ^ 5 - ((25 / 237) : ℂ) * ζ ^ 6 + ((64 / 237) : ℂ) * ζ ^ 8 + ((2 / 237) : ℂ) * ζ ^ 9 + ((23 / 79) : ℂ) * ζ ^ 11 + ((64 / 237) : ℂ) * ζ ^ 12 + ((26 / 237) : ℂ) * ζ ^ 13 + ((37 / 474) : ℂ) * ζ ^ 15 + ((26 / 237) : ℂ) * ζ ^ 17 + ((15 / 79) : ℂ) * ζ ^ 18 + ((31 / 79) : ℂ) * ζ ^ 21 - ((20 / 237) : ℂ) * ζ ^ 22 + ((97 / 474) : ℂ) * ζ ^ 25 - ((31 / 79) : ℂ) * ζ ^ 27 - ((64 / 237) : ℂ) * ζ ^ 28 - ((26 / 237) : ℂ) * ζ ^ 29 - ((25 / 474) : ℂ) * ζ ^ 30 - ((23 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep06CoefficientIdentity09 :
    row18_reducedY45_combinationStep06Coefficient09 =
      row18_reducedY45_combinationStep05Coefficient09 +
        row18_reducedY45_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep06Coefficient09 row18_reducedY45_combinationStep05Coefficient09 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep06Coefficient10 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep06CoefficientIdentity10 :
    row18_reducedY45_combinationStep06Coefficient10 =
      row18_reducedY45_combinationStep05Coefficient10 +
        row18_reducedY45_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep06Coefficient10 row18_reducedY45_combinationStep05Coefficient10 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep06Coefficient11 : ℂ :=
  (((35 / 237) : ℂ) - ((19 / 237) : ℂ) * ζ ^ 1 - ((112 / 237) : ℂ) * ζ ^ 2 - ((9 / 79) : ℂ) * ζ ^ 3 - ((24 / 79) : ℂ) * ζ ^ 5 - ((23 / 237) : ℂ) * ζ ^ 6 - ((19 / 237) : ℂ) * ζ ^ 8 - ((17 / 237) : ℂ) * ζ ^ 9 - ((32 / 237) : ℂ) * ζ ^ 11 - ((89 / 237) : ℂ) * ζ ^ 12 + ((19 / 237) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 + ((19 / 237) : ℂ) * ζ ^ 17 + ((77 / 237) : ℂ) * ζ ^ 18 + ((53 / 237) : ℂ) * ζ ^ 21 + ((112 / 237) : ℂ) * ζ ^ 22 + ((112 / 237) : ℂ) * ζ ^ 24 + ((53 / 237) : ℂ) * ζ ^ 25 + ((32 / 237) : ℂ) * ζ ^ 27 + ((19 / 237) : ℂ) * ζ ^ 28 - ((19 / 237) : ℂ) * ζ ^ 29 - ((31 / 79) : ℂ) * ζ ^ 30 + ((32 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep06CoefficientIdentity11 :
    row18_reducedY45_combinationStep06Coefficient11 =
      row18_reducedY45_combinationStep05Coefficient11 +
        row18_reducedY45_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep06Coefficient11 row18_reducedY45_combinationStep05Coefficient11 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep06Coefficient12 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep06CoefficientIdentity12 :
    row18_reducedY45_combinationStep06Coefficient12 =
      row18_reducedY45_combinationStep05Coefficient12 +
        row18_reducedY45_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep06Coefficient12 row18_reducedY45_combinationStep05Coefficient12 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep06Coefficient13 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep06CoefficientIdentity13 :
    row18_reducedY45_combinationStep06Coefficient13 =
      row18_reducedY45_combinationStep05Coefficient13 +
        row18_reducedY45_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep06Coefficient13 row18_reducedY45_combinationStep05Coefficient13 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep06Coefficient14 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep06CoefficientIdentity14 :
    row18_reducedY45_combinationStep06Coefficient14 =
      row18_reducedY45_combinationStep05Coefficient14 +
        row18_reducedY45_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep06Coefficient14 row18_reducedY45_combinationStep05Coefficient14 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep06Coefficient15 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep06CoefficientIdentity15 :
    row18_reducedY45_combinationStep06Coefficient15 =
      row18_reducedY45_combinationStep05Coefficient15 +
        row18_reducedY45_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep06Coefficient15 row18_reducedY45_combinationStep05Coefficient15 row18_reducedY45_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY45_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY45_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY45_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY45_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY45_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY45_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY45_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY45_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY45_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY45_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY45_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY45_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY45_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY45_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY45_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY45_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY45_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY45_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY45_combinationStep06CoefficientIdentity00,
      row18_reducedY45_combinationStep06CoefficientIdentity01,
      row18_reducedY45_combinationStep06CoefficientIdentity02,
      row18_reducedY45_combinationStep06CoefficientIdentity03,
      row18_reducedY45_combinationStep06CoefficientIdentity04,
      row18_reducedY45_combinationStep06CoefficientIdentity05,
      row18_reducedY45_combinationStep06CoefficientIdentity06,
      row18_reducedY45_combinationStep06CoefficientIdentity07,
      row18_reducedY45_combinationStep06CoefficientIdentity08,
      row18_reducedY45_combinationStep06CoefficientIdentity09,
      row18_reducedY45_combinationStep06CoefficientIdentity10,
      row18_reducedY45_combinationStep06CoefficientIdentity11,
      row18_reducedY45_combinationStep06CoefficientIdentity12,
      row18_reducedY45_combinationStep06CoefficientIdentity13,
      row18_reducedY45_combinationStep06CoefficientIdentity14,
      row18_reducedY45_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY45_combinationStep06Multiplier * equation

private def row18_reducedY45_combinationStep07Multiplier : ℂ :=
  (((238 / 237) : ℂ) - ((22 / 237) : ℂ) * ζ ^ 1 - ((94 / 237) : ℂ) * ζ ^ 2 - ((8 / 237) : ℂ) * ζ ^ 3 - ((286 / 237) : ℂ) * ζ ^ 6 + ((2 / 79) : ℂ) * ζ ^ 8 + ((62 / 79) : ℂ) * ζ ^ 9 + ((242 / 237) : ℂ) * ζ ^ 11 - ((64 / 79) : ℂ) * ζ ^ 12 + ((22 / 237) : ℂ) * ζ ^ 13 - ((8 / 237) : ℂ) * ζ ^ 15 + ((22 / 237) : ℂ) * ζ ^ 17 + ((332 / 237) : ℂ) * ζ ^ 18 + ((22 / 237) : ℂ) * ζ ^ 21 + ((94 / 237) : ℂ) * ζ ^ 22 - ((94 / 237) : ℂ) * ζ ^ 24 - ((22 / 237) : ℂ) * ζ ^ 25 + ((242 / 237) : ℂ) * ζ ^ 27 - ((2 / 79) : ℂ) * ζ ^ 28 - ((22 / 237) : ℂ) * ζ ^ 29 - ((88 / 237) : ℂ) * ζ ^ 30 - ((242 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY45_combinationStep07Coefficient00 : ℂ :=
  (-((8 / 5) : ℂ) + ((13 / 5) : ℂ) * ζ ^ 1 + ((57 / 10) : ℂ) * ζ ^ 2 - ((5 / 2) : ℂ) * ζ ^ 3 + ((39 / 5) : ℂ) * ζ ^ 5 + ((33 / 10) : ℂ) * ζ ^ 6 + ((34 / 5) : ℂ) * ζ ^ 8 + ((13 / 10) : ℂ) * ζ ^ 9 + ((13 / 2) : ℂ) * ζ ^ 11 + ((12 / 5) : ℂ) * ζ ^ 12 - ((13 / 5) : ℂ) * ζ ^ 13 + ((5 / 2) : ℂ) * ζ ^ 15 - ((13 / 5) : ℂ) * ζ ^ 17 - ((41 / 10) : ℂ) * ζ ^ 18 - ((26 / 5) : ℂ) * ζ ^ 21 - ((57 / 10) : ℂ) * ζ ^ 22 - ((57 / 10) : ℂ) * ζ ^ 24 - ((26 / 5) : ℂ) * ζ ^ 25 - ((13 / 2) : ℂ) * ζ ^ 27 - ((34 / 5) : ℂ) * ζ ^ 28 + ((13 / 5) : ℂ) * ζ ^ 29 - ((11 / 10) : ℂ) * ζ ^ 30 - ((13 / 2) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep07CoefficientIdentity00 :
    row18_reducedY45_combinationStep07Coefficient00 =
      row18_reducedY45_combinationStep06Coefficient00 +
        row18_reducedY45_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep07Coefficient00 row18_reducedY45_combinationStep06Coefficient00 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep07Coefficient01 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep07CoefficientIdentity01 :
    row18_reducedY45_combinationStep07Coefficient01 =
      row18_reducedY45_combinationStep06Coefficient01 +
        row18_reducedY45_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep07Coefficient01 row18_reducedY45_combinationStep06Coefficient01 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep07Coefficient02 : ℂ :=
  (((254 / 79) : ℂ) - ((1617 / 395) : ℂ) * ζ ^ 1 + ((1617 / 395) : ℂ) * ζ ^ 3 - ((1036 / 395) : ℂ) * ζ ^ 5 + ((306 / 79) : ℂ) * ζ ^ 6 - ((127 / 79) : ℂ) * ζ ^ 8 + ((1639 / 395) : ℂ) * ζ ^ 9 - ((581 / 395) : ℂ) * ζ ^ 11 + ((128 / 79) : ℂ) * ζ ^ 12 + ((1617 / 395) : ℂ) * ζ ^ 13 + ((577 / 395) : ℂ) * ζ ^ 15 + ((1617 / 395) : ℂ) * ζ ^ 17 + ((105 / 79) : ℂ) * ζ ^ 18 + ((2194 / 395) : ℂ) * ζ ^ 21 + ((382 / 79) : ℂ) * ζ ^ 24 - ((581 / 395) : ℂ) * ζ ^ 25 + ((1639 / 395) : ℂ) * ζ ^ 27 + ((127 / 79) : ℂ) * ζ ^ 28 - ((1617 / 395) : ℂ) * ζ ^ 29 + ((306 / 79) : ℂ) * ζ ^ 30 + ((581 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep07CoefficientIdentity02 :
    row18_reducedY45_combinationStep07Coefficient02 =
      row18_reducedY45_combinationStep06Coefficient02 +
        row18_reducedY45_combinationStep07Multiplier *
          (((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep07Coefficient02 row18_reducedY45_combinationStep06Coefficient02 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 (-((15029 / 18723) : ℂ) - ((1 / 474) : ℂ) * ζ ^ 1 + ((335 / 37446) : ℂ) * ζ ^ 2 + ((5 / 474) : ℂ) * ζ ^ 3 + ((4708 / 6241) : ℂ) * ζ ^ 4 + ((35 / 474) : ℂ) * ζ ^ 5 - ((1790 / 18723) : ℂ) * ζ ^ 6 + ((17 / 474) : ℂ) * ζ ^ 7 - ((10366 / 18723) : ℂ) * ζ ^ 8 - ((103 / 474) : ℂ) * ζ ^ 9 + ((2263 / 18723) : ℂ) * ζ ^ 10 + ((11 / 79) : ℂ) * ζ ^ 11 + ((412 / 18723) : ℂ) * ζ ^ 12 + ((61 / 158) : ℂ) * ζ ^ 13 + ((2530 / 18723) : ℂ) * ζ ^ 14 - ((17 / 158) : ℂ) * ζ ^ 15 - ((939 / 12482) : ℂ) * ζ ^ 16 - ((63 / 158) : ℂ) * ζ ^ 17 + ((2876 / 18723) : ℂ) * ζ ^ 18 - ((40 / 237) : ℂ) * ζ ^ 19 - ((2779 / 37446) : ℂ) * ζ ^ 20 + ((65 / 237) : ℂ) * ζ ^ 21 - ((4741 / 37446) : ℂ) * ζ ^ 22 + ((127 / 474) : ℂ) * ζ ^ 23 - ((2779 / 37446) : ℂ) * ζ ^ 24 - ((37 / 237) : ℂ) * ζ ^ 25 + ((995 / 12482) : ℂ) * ζ ^ 26 - ((83 / 474) : ℂ) * ζ ^ 27 + ((1298 / 18723) : ℂ) * ζ ^ 28 + ((11 / 158) : ℂ) * ζ ^ 29 - ((605 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep07Coefficient03 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep07CoefficientIdentity03 :
    row18_reducedY45_combinationStep07Coefficient03 =
      row18_reducedY45_combinationStep06Coefficient03 +
        row18_reducedY45_combinationStep07Multiplier *
          (((16 / 79) : ℂ) + ((35 / 316) : ℂ) * ζ ^ 1 - ((61 / 316) : ℂ) * ζ ^ 2 + ((87 / 316) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 - ((6 / 79) : ℂ) * ζ ^ 8 - ((31 / 316) : ℂ) * ζ ^ 9 - ((14 / 79) : ℂ) * ζ ^ 11 - ((26 / 79) : ℂ) * ζ ^ 12 - ((35 / 316) : ℂ) * ζ ^ 13 - ((49 / 316) : ℂ) * ζ ^ 15 - ((35 / 316) : ℂ) * ζ ^ 17 + ((61 / 316) : ℂ) * ζ ^ 18 + ((13 / 79) : ℂ) * ζ ^ 21 + ((61 / 316) : ℂ) * ζ ^ 22 + ((32 / 79) : ℂ) * ζ ^ 24 + ((19 / 158) : ℂ) * ζ ^ 25 + ((13 / 79) : ℂ) * ζ ^ 27 + ((6 / 79) : ℂ) * ζ ^ 28 + ((35 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((14 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep07Coefficient03 row18_reducedY45_combinationStep06Coefficient03 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 (((1043 / 18723) : ℂ) + ((6463 / 37446) : ℂ) * ζ ^ 1 + ((1174 / 6241) : ℂ) * ζ ^ 2 + ((4463 / 12482) : ℂ) * ζ ^ 3 - ((2 / 237) : ℂ) * ζ ^ 4 + ((3 / 158) : ℂ) * ζ ^ 5 - ((163 / 474) : ℂ) * ζ ^ 6 - ((18253 / 37446) : ℂ) * ζ ^ 7 + ((9389 / 37446) : ℂ) * ζ ^ 8 - ((3917 / 18723) : ℂ) * ζ ^ 9 + ((2903 / 6241) : ℂ) * ζ ^ 10 + ((20959 / 37446) : ℂ) * ζ ^ 11 + ((435 / 12482) : ℂ) * ζ ^ 12 + ((430 / 18723) : ℂ) * ζ ^ 13 + ((7522 / 18723) : ℂ) * ζ ^ 14 - ((10226 / 18723) : ℂ) * ζ ^ 15 + ((763 / 18723) : ℂ) * ζ ^ 16 + ((8369 / 37446) : ℂ) * ζ ^ 17 - ((431 / 6241) : ℂ) * ζ ^ 18 + ((3939 / 6241) : ℂ) * ζ ^ 19 - ((4609 / 18723) : ℂ) * ζ ^ 20 + ((3629 / 37446) : ℂ) * ζ ^ 21 - ((1925 / 18723) : ℂ) * ζ ^ 22 - ((2072 / 6241) : ℂ) * ζ ^ 23 + ((186 / 6241) : ℂ) * ζ ^ 24 - ((11809 / 37446) : ℂ) * ζ ^ 25 + ((5963 / 37446) : ℂ) * ζ ^ 26 - ((2042 / 18723) : ℂ) * ζ ^ 27 - ((913 / 12482) : ℂ) * ζ ^ 28 + ((1672 / 18723) : ℂ) * ζ ^ 29 - ((3388 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep07Coefficient04 : ℂ :=
  (((8 / 5) : ℂ) - ((13 / 5) : ℂ) * ζ ^ 1 - ((57 / 10) : ℂ) * ζ ^ 2 + ((5 / 2) : ℂ) * ζ ^ 3 - ((39 / 5) : ℂ) * ζ ^ 5 - ((33 / 10) : ℂ) * ζ ^ 6 - ((34 / 5) : ℂ) * ζ ^ 8 - ((13 / 10) : ℂ) * ζ ^ 9 - ((13 / 2) : ℂ) * ζ ^ 11 - ((12 / 5) : ℂ) * ζ ^ 12 + ((13 / 5) : ℂ) * ζ ^ 13 - ((5 / 2) : ℂ) * ζ ^ 15 + ((13 / 5) : ℂ) * ζ ^ 17 + ((41 / 10) : ℂ) * ζ ^ 18 + ((26 / 5) : ℂ) * ζ ^ 21 + ((57 / 10) : ℂ) * ζ ^ 22 + ((57 / 10) : ℂ) * ζ ^ 24 + ((26 / 5) : ℂ) * ζ ^ 25 + ((13 / 2) : ℂ) * ζ ^ 27 + ((34 / 5) : ℂ) * ζ ^ 28 - ((13 / 5) : ℂ) * ζ ^ 29 + ((11 / 10) : ℂ) * ζ ^ 30 + ((13 / 2) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep07CoefficientIdentity04 :
    row18_reducedY45_combinationStep07Coefficient04 =
      row18_reducedY45_combinationStep06Coefficient04 +
        row18_reducedY45_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep07Coefficient04 row18_reducedY45_combinationStep06Coefficient04 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep07Coefficient05 : ℂ :=
  (((219 / 79) : ℂ) - ((195 / 79) : ℂ) * ζ ^ 1 - ((573 / 158) : ℂ) * ζ ^ 2 + ((509 / 158) : ℂ) * ζ ^ 3 - ((813 / 158) : ℂ) * ζ ^ 5 - ((737 / 158) : ℂ) * ζ ^ 8 + ((131 / 158) : ℂ) * ζ ^ 9 - ((320 / 79) : ℂ) * ζ ^ 11 - ((139 / 158) : ℂ) * ζ ^ 12 + ((195 / 79) : ℂ) * ζ ^ 13 - ((43 / 79) : ℂ) * ζ ^ 15 + ((195 / 79) : ℂ) * ζ ^ 17 + ((573 / 158) : ℂ) * ζ ^ 18 + ((899 / 158) : ℂ) * ζ ^ 21 + ((573 / 158) : ℂ) * ζ ^ 22 + ((438 / 79) : ℂ) * ζ ^ 24 + ((423 / 158) : ℂ) * ζ ^ 25 + ((899 / 158) : ℂ) * ζ ^ 27 + ((737 / 158) : ℂ) * ζ ^ 28 - ((195 / 79) : ℂ) * ζ ^ 29 + ((132 / 79) : ℂ) * ζ ^ 30 + ((320 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY45_combinationStep07CoefficientIdentity05 :
    row18_reducedY45_combinationStep07Coefficient05 =
      row18_reducedY45_combinationStep06Coefficient05 +
        row18_reducedY45_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep07Coefficient05 row18_reducedY45_combinationStep06Coefficient05 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep07Coefficient06 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep07CoefficientIdentity06 :
    row18_reducedY45_combinationStep07Coefficient06 =
      row18_reducedY45_combinationStep06Coefficient06 +
        row18_reducedY45_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep07Coefficient06 row18_reducedY45_combinationStep06Coefficient06 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep07Coefficient07 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep07CoefficientIdentity07 :
    row18_reducedY45_combinationStep07Coefficient07 =
      row18_reducedY45_combinationStep06Coefficient07 +
        row18_reducedY45_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep07Coefficient07 row18_reducedY45_combinationStep06Coefficient07 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep07Coefficient08 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep07CoefficientIdentity08 :
    row18_reducedY45_combinationStep07Coefficient08 =
      row18_reducedY45_combinationStep06Coefficient08 +
        row18_reducedY45_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep07Coefficient08 row18_reducedY45_combinationStep06Coefficient08 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep07Coefficient09 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY45_combinationStep07CoefficientIdentity09 :
    row18_reducedY45_combinationStep07Coefficient09 =
      row18_reducedY45_combinationStep06Coefficient09 +
        row18_reducedY45_combinationStep07Multiplier *
          (((5 / 79) : ℂ) + ((43 / 316) : ℂ) * ζ ^ 1 + ((9 / 158) : ℂ) * ζ ^ 2 + ((63 / 316) : ℂ) * ζ ^ 5 - ((1 / 158) : ℂ) * ζ ^ 6 - ((1 / 158) : ℂ) * ζ ^ 8 + ((63 / 316) : ℂ) * ζ ^ 9 - ((57 / 158) : ℂ) * ζ ^ 11 - ((31 / 316) : ℂ) * ζ ^ 12 - ((43 / 316) : ℂ) * ζ ^ 13 + ((3 / 79) : ℂ) * ζ ^ 15 - ((43 / 316) : ℂ) * ζ ^ 17 + ((3 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 - ((9 / 158) : ℂ) * ζ ^ 22 - ((1 / 316) : ℂ) * ζ ^ 24 - ((5 / 79) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((1 / 158) : ℂ) * ζ ^ 28 + ((43 / 316) : ℂ) * ζ ^ 29 + ((29 / 316) : ℂ) * ζ ^ 30 + ((57 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep07Coefficient09 row18_reducedY45_combinationStep06Coefficient09 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 (-((10181 / 37446) : ℂ) + ((263 / 12482) : ℂ) * ζ ^ 1 + ((3889 / 37446) : ℂ) * ζ ^ 2 - ((4295 / 12482) : ℂ) * ζ ^ 3 + ((9163 / 37446) : ℂ) * ζ ^ 4 - ((65 / 474) : ℂ) * ζ ^ 5 - ((5815 / 18723) : ℂ) * ζ ^ 6 + ((3797 / 37446) : ℂ) * ζ ^ 7 - ((1961 / 37446) : ℂ) * ζ ^ 8 + ((4989 / 12482) : ℂ) * ζ ^ 9 + ((2514 / 6241) : ℂ) * ζ ^ 10 - ((14329 / 37446) : ℂ) * ζ ^ 11 + ((1387 / 18723) : ℂ) * ζ ^ 12 - ((11029 / 37446) : ℂ) * ζ ^ 13 - ((3925 / 37446) : ℂ) * ζ ^ 14 - ((379 / 12482) : ℂ) * ζ ^ 15 + ((1231 / 12482) : ℂ) * ζ ^ 16 + ((5091 / 12482) : ℂ) * ζ ^ 17 + ((9523 / 18723) : ℂ) * ζ ^ 18 + ((3458 / 18723) : ℂ) * ζ ^ 19 - ((6785 / 37446) : ℂ) * ζ ^ 20 - ((6847 / 37446) : ℂ) * ζ ^ 21 - ((5236 / 6241) : ℂ) * ζ ^ 22 - ((1603 / 37446) : ℂ) * ζ ^ 23 + ((7114 / 18723) : ℂ) * ζ ^ 24 + ((4137 / 12482) : ℂ) * ζ ^ 25 + ((4732 / 6241) : ℂ) * ζ ^ 26 - ((2795 / 37446) : ℂ) * ζ ^ 27 - ((7733 / 37446) : ℂ) * ζ ^ 28 - ((8525 / 37446) : ℂ) * ζ ^ 29 - ((2299 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep07Coefficient10 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep07CoefficientIdentity10 :
    row18_reducedY45_combinationStep07Coefficient10 =
      row18_reducedY45_combinationStep06Coefficient10 +
        row18_reducedY45_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep07Coefficient10 row18_reducedY45_combinationStep06Coefficient10 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep07Coefficient11 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep07CoefficientIdentity11 :
    row18_reducedY45_combinationStep07Coefficient11 =
      row18_reducedY45_combinationStep06Coefficient11 +
        row18_reducedY45_combinationStep07Multiplier *
          (-((16 / 79) : ℂ) - ((35 / 316) : ℂ) * ζ ^ 1 + ((61 / 316) : ℂ) * ζ ^ 2 - ((87 / 316) : ℂ) * ζ ^ 3 + ((3 / 316) : ℂ) * ζ ^ 5 + ((6 / 79) : ℂ) * ζ ^ 8 + ((31 / 316) : ℂ) * ζ ^ 9 + ((14 / 79) : ℂ) * ζ ^ 11 + ((26 / 79) : ℂ) * ζ ^ 12 + ((35 / 316) : ℂ) * ζ ^ 13 + ((49 / 316) : ℂ) * ζ ^ 15 + ((35 / 316) : ℂ) * ζ ^ 17 - ((61 / 316) : ℂ) * ζ ^ 18 - ((13 / 79) : ℂ) * ζ ^ 21 - ((61 / 316) : ℂ) * ζ ^ 22 - ((32 / 79) : ℂ) * ζ ^ 24 - ((19 / 158) : ℂ) * ζ ^ 25 - ((13 / 79) : ℂ) * ζ ^ 27 - ((6 / 79) : ℂ) * ζ ^ 28 - ((35 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((14 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep07Coefficient11 row18_reducedY45_combinationStep06Coefficient11 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 (-((1043 / 18723) : ℂ) - ((6463 / 37446) : ℂ) * ζ ^ 1 - ((1174 / 6241) : ℂ) * ζ ^ 2 - ((4463 / 12482) : ℂ) * ζ ^ 3 + ((2 / 237) : ℂ) * ζ ^ 4 - ((3 / 158) : ℂ) * ζ ^ 5 + ((163 / 474) : ℂ) * ζ ^ 6 + ((18253 / 37446) : ℂ) * ζ ^ 7 - ((9389 / 37446) : ℂ) * ζ ^ 8 + ((3917 / 18723) : ℂ) * ζ ^ 9 - ((2903 / 6241) : ℂ) * ζ ^ 10 - ((20959 / 37446) : ℂ) * ζ ^ 11 - ((435 / 12482) : ℂ) * ζ ^ 12 - ((430 / 18723) : ℂ) * ζ ^ 13 - ((7522 / 18723) : ℂ) * ζ ^ 14 + ((10226 / 18723) : ℂ) * ζ ^ 15 - ((763 / 18723) : ℂ) * ζ ^ 16 - ((8369 / 37446) : ℂ) * ζ ^ 17 + ((431 / 6241) : ℂ) * ζ ^ 18 - ((3939 / 6241) : ℂ) * ζ ^ 19 + ((4609 / 18723) : ℂ) * ζ ^ 20 - ((3629 / 37446) : ℂ) * ζ ^ 21 + ((1925 / 18723) : ℂ) * ζ ^ 22 + ((2072 / 6241) : ℂ) * ζ ^ 23 - ((186 / 6241) : ℂ) * ζ ^ 24 + ((11809 / 37446) : ℂ) * ζ ^ 25 - ((5963 / 37446) : ℂ) * ζ ^ 26 + ((2042 / 18723) : ℂ) * ζ ^ 27 + ((913 / 12482) : ℂ) * ζ ^ 28 - ((1672 / 18723) : ℂ) * ζ ^ 29 + ((3388 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep07Coefficient12 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep07CoefficientIdentity12 :
    row18_reducedY45_combinationStep07Coefficient12 =
      row18_reducedY45_combinationStep06Coefficient12 +
        row18_reducedY45_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep07Coefficient12 row18_reducedY45_combinationStep06Coefficient12 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep07Coefficient13 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep07CoefficientIdentity13 :
    row18_reducedY45_combinationStep07Coefficient13 =
      row18_reducedY45_combinationStep06Coefficient13 +
        row18_reducedY45_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep07Coefficient13 row18_reducedY45_combinationStep06Coefficient13 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep07Coefficient14 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep07CoefficientIdentity14 :
    row18_reducedY45_combinationStep07Coefficient14 =
      row18_reducedY45_combinationStep06Coefficient14 +
        row18_reducedY45_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep07Coefficient14 row18_reducedY45_combinationStep06Coefficient14 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep07Coefficient15 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep07CoefficientIdentity15 :
    row18_reducedY45_combinationStep07Coefficient15 =
      row18_reducedY45_combinationStep06Coefficient15 +
        row18_reducedY45_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep07Coefficient15 row18_reducedY45_combinationStep06Coefficient15 row18_reducedY45_combinationStep07Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY45_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY45_combinationStep07Coefficient00) * Y 0 0
      + (row18_reducedY45_combinationStep07Coefficient01) * Y 0 1
      + (row18_reducedY45_combinationStep07Coefficient02) * Y 1 0
      + (row18_reducedY45_combinationStep07Coefficient03) * Y 1 1
      + (row18_reducedY45_combinationStep07Coefficient04) * Y 2 2
      + (row18_reducedY45_combinationStep07Coefficient05) * Y 2 3
      + (row18_reducedY45_combinationStep07Coefficient06) * Y 3 2
      + (row18_reducedY45_combinationStep07Coefficient07) * Y 3 3
      + (row18_reducedY45_combinationStep07Coefficient08) * Y 4 4
      + (row18_reducedY45_combinationStep07Coefficient09) * Y 4 5
      + (row18_reducedY45_combinationStep07Coefficient10) * Y 5 4
      + (row18_reducedY45_combinationStep07Coefficient11) * Y 5 5
      + (row18_reducedY45_combinationStep07Coefficient12) * Y 6 6
      + (row18_reducedY45_combinationStep07Coefficient13) * Y 6 7
      + (row18_reducedY45_combinationStep07Coefficient14) * Y 7 6
      + (row18_reducedY45_combinationStep07Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY45_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation15
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY45_combinationStep07CoefficientIdentity00,
      row18_reducedY45_combinationStep07CoefficientIdentity01,
      row18_reducedY45_combinationStep07CoefficientIdentity02,
      row18_reducedY45_combinationStep07CoefficientIdentity03,
      row18_reducedY45_combinationStep07CoefficientIdentity04,
      row18_reducedY45_combinationStep07CoefficientIdentity05,
      row18_reducedY45_combinationStep07CoefficientIdentity06,
      row18_reducedY45_combinationStep07CoefficientIdentity07,
      row18_reducedY45_combinationStep07CoefficientIdentity08,
      row18_reducedY45_combinationStep07CoefficientIdentity09,
      row18_reducedY45_combinationStep07CoefficientIdentity10,
      row18_reducedY45_combinationStep07CoefficientIdentity11,
      row18_reducedY45_combinationStep07CoefficientIdentity12,
      row18_reducedY45_combinationStep07CoefficientIdentity13,
      row18_reducedY45_combinationStep07CoefficientIdentity14,
      row18_reducedY45_combinationStep07CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY45_combinationStep07Multiplier * equation

private def row18_reducedY45_combinationStep08Multiplier : ℂ :=
  (-((1734 / 395) : ℂ) + ((242 / 79) : ℂ) * ζ ^ 1 + ((4348 / 395) : ℂ) * ζ ^ 2 - ((22 / 79) : ℂ) * ζ ^ 3 + ((1100 / 79) : ℂ) * ζ ^ 5 + ((2092 / 395) : ℂ) * ζ ^ 6 + ((5582 / 395) : ℂ) * ζ ^ 8 + ((308 / 79) : ℂ) * ζ ^ 9 + ((840 / 79) : ℂ) * ζ ^ 11 + ((2256 / 395) : ℂ) * ζ ^ 12 - ((242 / 79) : ℂ) * ζ ^ 13 + ((22 / 79) : ℂ) * ζ ^ 15 - ((242 / 79) : ℂ) * ζ ^ 17 - ((2614 / 395) : ℂ) * ζ ^ 18 - ((858 / 79) : ℂ) * ζ ^ 21 - ((4348 / 395) : ℂ) * ζ ^ 22 - ((4348 / 395) : ℂ) * ζ ^ 24 - ((858 / 79) : ℂ) * ζ ^ 25 - ((840 / 79) : ℂ) * ζ ^ 27 - ((5582 / 395) : ℂ) * ζ ^ 28 + ((242 / 79) : ℂ) * ζ ^ 29 - ((1234 / 395) : ℂ) * ζ ^ 30 - ((840 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY45_combinationStep08Coefficient00 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity00 :
    row18_reducedY45_combinationStep08Coefficient00 =
      row18_reducedY45_combinationStep07Coefficient00 +
        row18_reducedY45_combinationStep08Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep08Coefficient00 row18_reducedY45_combinationStep07Coefficient00 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 (-((11026 / 6241) : ℂ) + ((179063 / 62410) : ℂ) * ζ ^ 1 + ((89773 / 12482) : ℂ) * ζ ^ 2 - ((231157 / 62410) : ℂ) * ζ ^ 3 - ((7453 / 6241) : ℂ) * ζ ^ 4 + ((2337 / 395) : ℂ) * ζ ^ 5 - ((250961 / 62410) : ℂ) * ζ ^ 6 - ((98679 / 62410) : ℂ) * ζ ^ 7 + ((403177 / 62410) : ℂ) * ζ ^ 8 - ((170653 / 31205) : ℂ) * ζ ^ 9 - ((145469 / 62410) : ℂ) * ζ ^ 10 + ((179986 / 31205) : ℂ) * ζ ^ 11 - ((369359 / 62410) : ℂ) * ζ ^ 12 - ((20321 / 62410) : ℂ) * ζ ^ 13 + ((159766 / 31205) : ℂ) * ζ ^ 14 - ((176872 / 31205) : ℂ) * ζ ^ 15 + ((50889 / 62410) : ℂ) * ζ ^ 16 + ((172447 / 62410) : ℂ) * ζ ^ 17 - ((347293 / 62410) : ℂ) * ζ ^ 18 + ((77999 / 62410) : ℂ) * ζ ^ 19 + ((6568 / 31205) : ℂ) * ζ ^ 20 - ((151448 / 31205) : ℂ) * ζ ^ 21 + ((26734 / 31205) : ℂ) * ζ ^ 22 + ((25172 / 31205) : ℂ) * ζ ^ 23 - ((116217 / 62410) : ℂ) * ζ ^ 24 + ((25321 / 31205) : ℂ) * ζ ^ 25 + ((20803 / 31205) : ℂ) * ζ ^ 26 - ((37319 / 62410) : ℂ) * ζ ^ 27 + ((12251 / 31205) : ℂ) * ζ ^ 28 + ((21119 / 31205) : ℂ) * ζ ^ 29 + ((2940 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep08Coefficient01 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity01 :
    row18_reducedY45_combinationStep08Coefficient01 =
      row18_reducedY45_combinationStep07Coefficient01 +
        row18_reducedY45_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep08Coefficient01 row18_reducedY45_combinationStep07Coefficient01 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep08Coefficient02 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity02 :
    row18_reducedY45_combinationStep08Coefficient02 =
      row18_reducedY45_combinationStep07Coefficient02 +
        row18_reducedY45_combinationStep08Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep08Coefficient02 row18_reducedY45_combinationStep07Coefficient02 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 (((116803 / 31205) : ℂ) - ((3097 / 790) : ℂ) * ζ ^ 1 - ((57872 / 31205) : ℂ) * ζ ^ 2 + ((1668 / 395) : ℂ) * ζ ^ 3 - ((133116 / 31205) : ℂ) * ζ ^ 4 - ((1224 / 395) : ℂ) * ζ ^ 5 + ((157303 / 62410) : ℂ) * ζ ^ 6 - ((453 / 79) : ℂ) * ζ ^ 7 - ((169997 / 62410) : ℂ) * ζ ^ 8 + ((2957 / 790) : ℂ) * ζ ^ 9 - ((151291 / 62410) : ℂ) * ζ ^ 10 - ((482 / 395) : ℂ) * ζ ^ 11 + ((410769 / 62410) : ℂ) * ζ ^ 12 - ((364 / 395) : ℂ) * ζ ^ 13 - ((2279 / 62410) : ℂ) * ζ ^ 14 + ((4513 / 790) : ℂ) * ζ ^ 15 - ((17723 / 31205) : ℂ) * ζ ^ 16 + ((1296 / 395) : ℂ) * ζ ^ 17 + ((351699 / 62410) : ℂ) * ζ ^ 18 + ((463 / 395) : ℂ) * ζ ^ 19 + ((296333 / 62410) : ℂ) * ζ ^ 20 + ((3951 / 790) : ℂ) * ζ ^ 21 + ((53463 / 62410) : ℂ) * ζ ^ 22 + ((390 / 79) : ℂ) * ζ ^ 23 + ((296333 / 62410) : ℂ) * ζ ^ 24 + ((463 / 395) : ℂ) * ζ ^ 25 + ((161588 / 31205) : ℂ) * ζ ^ 26 + ((4473 / 790) : ℂ) * ζ ^ 27 + ((30348 / 31205) : ℂ) * ζ ^ 28 + ((966 / 395) : ℂ) * ζ ^ 29 + ((17640 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep08Coefficient03 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity03 :
    row18_reducedY45_combinationStep08Coefficient03 =
      row18_reducedY45_combinationStep07Coefficient03 +
        row18_reducedY45_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep08Coefficient03 row18_reducedY45_combinationStep07Coefficient03 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep08Coefficient04 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity04 :
    row18_reducedY45_combinationStep08Coefficient04 =
      row18_reducedY45_combinationStep07Coefficient04 +
        row18_reducedY45_combinationStep08Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep08Coefficient04 row18_reducedY45_combinationStep07Coefficient04 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 (((11026 / 6241) : ℂ) - ((179063 / 62410) : ℂ) * ζ ^ 1 - ((89773 / 12482) : ℂ) * ζ ^ 2 + ((231157 / 62410) : ℂ) * ζ ^ 3 + ((7453 / 6241) : ℂ) * ζ ^ 4 - ((2337 / 395) : ℂ) * ζ ^ 5 + ((250961 / 62410) : ℂ) * ζ ^ 6 + ((98679 / 62410) : ℂ) * ζ ^ 7 - ((403177 / 62410) : ℂ) * ζ ^ 8 + ((170653 / 31205) : ℂ) * ζ ^ 9 + ((145469 / 62410) : ℂ) * ζ ^ 10 - ((179986 / 31205) : ℂ) * ζ ^ 11 + ((369359 / 62410) : ℂ) * ζ ^ 12 + ((20321 / 62410) : ℂ) * ζ ^ 13 - ((159766 / 31205) : ℂ) * ζ ^ 14 + ((176872 / 31205) : ℂ) * ζ ^ 15 - ((50889 / 62410) : ℂ) * ζ ^ 16 - ((172447 / 62410) : ℂ) * ζ ^ 17 + ((347293 / 62410) : ℂ) * ζ ^ 18 - ((77999 / 62410) : ℂ) * ζ ^ 19 - ((6568 / 31205) : ℂ) * ζ ^ 20 + ((151448 / 31205) : ℂ) * ζ ^ 21 - ((26734 / 31205) : ℂ) * ζ ^ 22 - ((25172 / 31205) : ℂ) * ζ ^ 23 + ((116217 / 62410) : ℂ) * ζ ^ 24 - ((25321 / 31205) : ℂ) * ζ ^ 25 - ((20803 / 31205) : ℂ) * ζ ^ 26 + ((37319 / 62410) : ℂ) * ζ ^ 27 - ((12251 / 31205) : ℂ) * ζ ^ 28 - ((21119 / 31205) : ℂ) * ζ ^ 29 - ((2940 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep08Coefficient05 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity05 :
    row18_reducedY45_combinationStep08Coefficient05 =
      row18_reducedY45_combinationStep07Coefficient05 +
        row18_reducedY45_combinationStep08Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY45_combinationStep08Coefficient05 row18_reducedY45_combinationStep07Coefficient05 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 (((113187 / 62410) : ℂ) - ((96699 / 62410) : ℂ) * ζ ^ 1 - ((39708 / 31205) : ℂ) * ζ ^ 2 + ((152683 / 62410) : ℂ) * ζ ^ 3 - ((131763 / 62410) : ℂ) * ζ ^ 4 - ((69 / 158) : ℂ) * ζ ^ 5 + ((82438 / 31205) : ℂ) * ζ ^ 6 - ((260843 / 62410) : ℂ) * ζ ^ 7 - ((77693 / 62410) : ℂ) * ζ ^ 8 + ((22964 / 31205) : ℂ) * ζ ^ 9 - ((400267 / 62410) : ℂ) * ζ ^ 10 - ((246017 / 62410) : ℂ) * ζ ^ 11 + ((224567 / 62410) : ℂ) * ζ ^ 12 + ((5484 / 6241) : ℂ) * ζ ^ 13 - ((57043 / 62410) : ℂ) * ζ ^ 14 + ((272299 / 62410) : ℂ) * ζ ^ 15 + ((33402 / 31205) : ℂ) * ζ ^ 16 - ((15366 / 31205) : ℂ) * ζ ^ 17 + ((266399 / 62410) : ℂ) * ζ ^ 18 + ((67437 / 62410) : ℂ) * ζ ^ 19 - ((20646 / 31205) : ℂ) * ζ ^ 20 + ((152667 / 31205) : ℂ) * ζ ^ 21 - ((3033 / 12482) : ℂ) * ζ ^ 22 + ((19839 / 62410) : ℂ) * ζ ^ 23 + ((213559 / 62410) : ℂ) * ζ ^ 24 + ((38813 / 62410) : ℂ) * ζ ^ 25 + ((135099 / 31205) : ℂ) * ζ ^ 26 + ((158508 / 31205) : ℂ) * ζ ^ 27 - ((18891 / 31205) : ℂ) * ζ ^ 28 + ((22446 / 6241) : ℂ) * ζ ^ 29 + ((37800 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY45_combinationStep08Coefficient06 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity06 :
    row18_reducedY45_combinationStep08Coefficient06 =
      row18_reducedY45_combinationStep07Coefficient06 +
        row18_reducedY45_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep08Coefficient06 row18_reducedY45_combinationStep07Coefficient06 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep08Coefficient07 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity07 :
    row18_reducedY45_combinationStep08Coefficient07 =
      row18_reducedY45_combinationStep07Coefficient07 +
        row18_reducedY45_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep08Coefficient07 row18_reducedY45_combinationStep07Coefficient07 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep08Coefficient08 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity08 :
    row18_reducedY45_combinationStep08Coefficient08 =
      row18_reducedY45_combinationStep07Coefficient08 +
        row18_reducedY45_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep08Coefficient08 row18_reducedY45_combinationStep07Coefficient08 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep08Coefficient09 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY45_combinationStep08CoefficientIdentity09 :
    row18_reducedY45_combinationStep08Coefficient09 =
      row18_reducedY45_combinationStep07Coefficient09 +
        row18_reducedY45_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep08Coefficient09 row18_reducedY45_combinationStep07Coefficient09 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep08Coefficient10 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity10 :
    row18_reducedY45_combinationStep08Coefficient10 =
      row18_reducedY45_combinationStep07Coefficient10 +
        row18_reducedY45_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep08Coefficient10 row18_reducedY45_combinationStep07Coefficient10 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep08Coefficient11 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity11 :
    row18_reducedY45_combinationStep08Coefficient11 =
      row18_reducedY45_combinationStep07Coefficient11 +
        row18_reducedY45_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep08Coefficient11 row18_reducedY45_combinationStep07Coefficient11 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep08Coefficient12 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity12 :
    row18_reducedY45_combinationStep08Coefficient12 =
      row18_reducedY45_combinationStep07Coefficient12 +
        row18_reducedY45_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep08Coefficient12 row18_reducedY45_combinationStep07Coefficient12 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep08Coefficient13 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity13 :
    row18_reducedY45_combinationStep08Coefficient13 =
      row18_reducedY45_combinationStep07Coefficient13 +
        row18_reducedY45_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep08Coefficient13 row18_reducedY45_combinationStep07Coefficient13 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep08Coefficient14 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity14 :
    row18_reducedY45_combinationStep08Coefficient14 =
      row18_reducedY45_combinationStep07Coefficient14 +
        row18_reducedY45_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep08Coefficient14 row18_reducedY45_combinationStep07Coefficient14 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY45_combinationStep08Coefficient15 : ℂ :=
  0

private theorem row18_reducedY45_combinationStep08CoefficientIdentity15 :
    row18_reducedY45_combinationStep08Coefficient15 =
      row18_reducedY45_combinationStep07Coefficient15 +
        row18_reducedY45_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY45_combinationStep08Coefficient15 row18_reducedY45_combinationStep07Coefficient15 row18_reducedY45_combinationStep08Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY45_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY45_combinationStep08Coefficient00) * Y 0 0
      + (row18_reducedY45_combinationStep08Coefficient01) * Y 0 1
      + (row18_reducedY45_combinationStep08Coefficient02) * Y 1 0
      + (row18_reducedY45_combinationStep08Coefficient03) * Y 1 1
      + (row18_reducedY45_combinationStep08Coefficient04) * Y 2 2
      + (row18_reducedY45_combinationStep08Coefficient05) * Y 2 3
      + (row18_reducedY45_combinationStep08Coefficient06) * Y 3 2
      + (row18_reducedY45_combinationStep08Coefficient07) * Y 3 3
      + (row18_reducedY45_combinationStep08Coefficient08) * Y 4 4
      + (row18_reducedY45_combinationStep08Coefficient09) * Y 4 5
      + (row18_reducedY45_combinationStep08Coefficient10) * Y 5 4
      + (row18_reducedY45_combinationStep08Coefficient11) * Y 5 5
      + (row18_reducedY45_combinationStep08Coefficient12) * Y 6 6
      + (row18_reducedY45_combinationStep08Coefficient13) * Y 6 7
      + (row18_reducedY45_combinationStep08Coefficient14) * Y 7 6
      + (row18_reducedY45_combinationStep08Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY45_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY45_combinationStep08CoefficientIdentity00,
      row18_reducedY45_combinationStep08CoefficientIdentity01,
      row18_reducedY45_combinationStep08CoefficientIdentity02,
      row18_reducedY45_combinationStep08CoefficientIdentity03,
      row18_reducedY45_combinationStep08CoefficientIdentity04,
      row18_reducedY45_combinationStep08CoefficientIdentity05,
      row18_reducedY45_combinationStep08CoefficientIdentity06,
      row18_reducedY45_combinationStep08CoefficientIdentity07,
      row18_reducedY45_combinationStep08CoefficientIdentity08,
      row18_reducedY45_combinationStep08CoefficientIdentity09,
      row18_reducedY45_combinationStep08CoefficientIdentity10,
      row18_reducedY45_combinationStep08CoefficientIdentity11,
      row18_reducedY45_combinationStep08CoefficientIdentity12,
      row18_reducedY45_combinationStep08CoefficientIdentity13,
      row18_reducedY45_combinationStep08CoefficientIdentity14,
      row18_reducedY45_combinationStep08CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY45_combinationStep08Multiplier * equation

theorem row18_reducedY45
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 4 5 = 0 := by
  have reduced :=
    row18_reducedY45_combinationStep08 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY45_combinationStep08Coefficient00,
      row18_reducedY45_combinationStep08Coefficient01,
      row18_reducedY45_combinationStep08Coefficient02,
      row18_reducedY45_combinationStep08Coefficient03,
      row18_reducedY45_combinationStep08Coefficient04,
      row18_reducedY45_combinationStep08Coefficient05,
      row18_reducedY45_combinationStep08Coefficient06,
      row18_reducedY45_combinationStep08Coefficient07,
      row18_reducedY45_combinationStep08Coefficient08,
      row18_reducedY45_combinationStep08Coefficient09,
      row18_reducedY45_combinationStep08Coefficient10,
      row18_reducedY45_combinationStep08Coefficient11,
      row18_reducedY45_combinationStep08Coefficient12,
      row18_reducedY45_combinationStep08Coefficient13,
      row18_reducedY45_combinationStep08Coefficient14,
      row18_reducedY45_combinationStep08Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
