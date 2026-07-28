/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction01

/-!
# Ambient row 18 commutant reduction 02

This generated module checks the reduced relation `reducedY10` for
matrix coordinate (1, 0).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY10_combinationStep00Multiplier : ℂ :=
  (-((5632 / 1185) : ℂ) - ((788 / 395) : ℂ) * ζ ^ 1 - ((552 / 395) : ℂ) * ζ ^ 2 + ((36 / 395) : ℂ) * ζ ^ 5 + ((3976 / 1185) : ℂ) * ζ ^ 6 + ((3976 / 1185) : ℂ) * ζ ^ 8 + ((36 / 395) : ℂ) * ζ ^ 9 + ((1726 / 237) : ℂ) * ζ ^ 11 + ((11068 / 1185) : ℂ) * ζ ^ 12 + ((788 / 395) : ℂ) * ζ ^ 13 - ((664 / 237) : ℂ) * ζ ^ 15 + ((788 / 395) : ℂ) * ζ ^ 17 + ((66 / 395) : ℂ) * ζ ^ 18 + ((376 / 395) : ℂ) * ζ ^ 21 + ((552 / 395) : ℂ) * ζ ^ 22 - ((4174 / 1185) : ℂ) * ζ ^ 24 - ((824 / 395) : ℂ) * ζ ^ 25 + ((664 / 237) : ℂ) * ζ ^ 27 - ((3976 / 1185) : ℂ) * ζ ^ 28 - ((788 / 395) : ℂ) * ζ ^ 29 - ((2364 / 395) : ℂ) * ζ ^ 30 - ((1726 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY10_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep00CoefficientIdentity00 :
    row18_reducedY10_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep00Coefficient00 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep00Coefficient01 : ℂ :=
  (((63107 / 37446) : ℂ) + ((27084 / 6241) : ℂ) * ζ ^ 1 - ((18109 / 37446) : ℂ) * ζ ^ 2 - ((77141 / 37446) : ℂ) * ζ ^ 3 + ((96847 / 37446) : ℂ) * ζ ^ 5 + ((161191 / 37446) : ℂ) * ζ ^ 6 - ((54076 / 18723) : ℂ) * ζ ^ 8 - ((64225 / 18723) : ℂ) * ζ ^ 9 + ((96847 / 37446) : ℂ) * ζ ^ 11 - ((27038 / 18723) : ℂ) * ζ ^ 12 - ((27084 / 6241) : ℂ) * ζ ^ 13 + ((20931 / 12482) : ℂ) * ζ ^ 15 - ((27084 / 6241) : ℂ) * ζ ^ 17 - ((161191 / 37446) : ℂ) * ζ ^ 18 - ((9853 / 18723) : ℂ) * ζ ^ 21 + ((18109 / 37446) : ℂ) * ζ ^ 22 + ((15015 / 12482) : ℂ) * ζ ^ 24 + ((65657 / 37446) : ℂ) * ζ ^ 25 + ((65657 / 37446) : ℂ) * ζ ^ 27 + ((54076 / 18723) : ℂ) * ζ ^ 28 + ((27084 / 6241) : ℂ) * ζ ^ 29 - ((96847 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep00CoefficientIdentity01 :
    row18_reducedY10_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep00Coefficient01 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 (-((552079 / 187230) : ℂ) - ((156192 / 31205) : ℂ) * ζ ^ 1 - ((113549 / 187230) : ℂ) * ζ ^ 2 + ((65249 / 37446) : ℂ) * ζ ^ 3 + ((515647 / 187230) : ℂ) * ζ ^ 4 + ((668653 / 187230) : ℂ) * ζ ^ 5 - ((161819 / 93615) : ℂ) * ζ ^ 6 - ((196597 / 187230) : ℂ) * ζ ^ 7 + ((141779 / 62410) : ℂ) * ζ ^ 8 + ((16967 / 12482) : ℂ) * ζ ^ 9 + ((264658 / 93615) : ℂ) * ζ ^ 10 - ((20345 / 18723) : ℂ) * ζ ^ 11 - ((174569 / 187230) : ℂ) * ζ ^ 12 - ((143209 / 187230) : ℂ) * ζ ^ 13 - ((489757 / 187230) : ℂ) * ζ ^ 14 - ((114763 / 93615) : ℂ) * ζ ^ 15 - ((61018 / 31205) : ℂ) * ζ ^ 16 + ((2285 / 6241) : ℂ) * ζ ^ 17 + ((493879 / 187230) : ℂ) * ζ ^ 18 + ((67879 / 37446) : ℂ) * ζ ^ 19 + ((114598 / 93615) : ℂ) * ζ ^ 20 - ((147959 / 93615) : ℂ) * ζ ^ 21 - ((217621 / 187230) : ℂ) * ζ ^ 22 - ((125173 / 187230) : ℂ) * ζ ^ 23 - ((198959 / 187230) : ℂ) * ζ ^ 24 + ((41507 / 62410) : ℂ) * ζ ^ 25 - ((47419 / 31205) : ℂ) * ζ ^ 26 - ((16874 / 31205) : ℂ) * ζ ^ 27 - ((18067 / 62410) : ℂ) * ζ ^ 28 + ((41541 / 62410) : ℂ) * ζ ^ 29 + ((29342 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep00Coefficient02 : ℂ :=
  (-((89758 / 18723) : ℂ) - ((14273 / 18723) : ℂ) * ζ ^ 1 + ((16202 / 18723) : ℂ) * ζ ^ 2 + ((123611 / 37446) : ℂ) * ζ ^ 3 - ((51043 / 37446) : ℂ) * ζ ^ 5 - ((1313 / 6241) : ℂ) * ζ ^ 6 + ((30135 / 12482) : ℂ) * ζ ^ 8 + ((11507 / 6241) : ℂ) * ζ ^ 9 - ((54569 / 37446) : ℂ) * ζ ^ 11 + ((30135 / 12482) : ℂ) * ζ ^ 12 + ((14273 / 18723) : ℂ) * ζ ^ 13 - ((73054 / 18723) : ℂ) * ζ ^ 15 + ((14273 / 18723) : ℂ) * ζ ^ 17 + ((20141 / 18723) : ℂ) * ζ ^ 18 - ((95065 / 37446) : ℂ) * ζ ^ 21 - ((16202 / 18723) : ℂ) * ζ ^ 22 + ((7499 / 12482) : ℂ) * ζ ^ 25 + ((95065 / 37446) : ℂ) * ζ ^ 27 - ((30135 / 12482) : ℂ) * ζ ^ 28 - ((14273 / 18723) : ℂ) * ζ ^ 29 - ((1313 / 12482) : ℂ) * ζ ^ 30 + ((54569 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep00CoefficientIdentity02 :
    row18_reducedY10_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep00Coefficient02 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 (((333334 / 93615) : ℂ) + ((1533 / 31205) : ℂ) * ζ ^ 1 - ((170513 / 93615) : ℂ) * ζ ^ 2 - ((601423 / 187230) : ℂ) * ζ ^ 3 - ((333226 / 93615) : ℂ) * ζ ^ 4 + ((270317 / 187230) : ℂ) * ζ ^ 5 + ((256579 / 93615) : ℂ) * ζ ^ 6 + ((205367 / 62410) : ℂ) * ζ ^ 7 + ((606407 / 187230) : ℂ) * ζ ^ 8 - ((352481 / 187230) : ℂ) * ζ ^ 9 - ((51148 / 31205) : ℂ) * ζ ^ 10 - ((7838 / 93615) : ℂ) * ζ ^ 11 + ((2351 / 2370) : ℂ) * ζ ^ 12 + ((116521 / 37446) : ℂ) * ζ ^ 13 - ((527 / 31205) : ℂ) * ζ ^ 14 - ((30425 / 37446) : ℂ) * ζ ^ 15 - ((327551 / 187230) : ℂ) * ζ ^ 16 - ((141073 / 62410) : ℂ) * ζ ^ 17 - ((36071 / 93615) : ℂ) * ζ ^ 18 - ((27977 / 62410) : ℂ) * ζ ^ 19 + ((83167 / 93615) : ℂ) * ζ ^ 20 + ((165691 / 93615) : ℂ) * ζ ^ 21 + ((87199 / 62410) : ℂ) * ζ ^ 22 + ((95444 / 93615) : ℂ) * ζ ^ 23 - ((21235 / 18723) : ℂ) * ζ ^ 24 - ((365651 / 187230) : ℂ) * ζ ^ 25 - ((55391 / 31205) : ℂ) * ζ ^ 26 - ((247579 / 187230) : ℂ) * ζ ^ 27 + ((57377 / 187230) : ℂ) * ζ ^ 28 + ((11313 / 12482) : ℂ) * ζ ^ 29 + ((4315 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep00CoefficientIdentity03 :
    row18_reducedY10_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep00Coefficient03 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep00CoefficientIdentity04 :
    row18_reducedY10_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep00Coefficient04 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep00CoefficientIdentity05 :
    row18_reducedY10_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep00Coefficient05 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep00CoefficientIdentity06 :
    row18_reducedY10_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep00Coefficient06 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep00CoefficientIdentity07 :
    row18_reducedY10_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep00Coefficient07 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep00CoefficientIdentity08 :
    row18_reducedY10_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep00Coefficient08 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep00CoefficientIdentity09 :
    row18_reducedY10_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep00Coefficient09 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep00CoefficientIdentity10 :
    row18_reducedY10_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep00Coefficient10 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep00CoefficientIdentity11 :
    row18_reducedY10_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep00Coefficient11 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep00CoefficientIdentity12 :
    row18_reducedY10_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep00Coefficient12 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep00CoefficientIdentity13 :
    row18_reducedY10_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep00Coefficient13 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep00CoefficientIdentity14 :
    row18_reducedY10_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep00Coefficient14 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep00CoefficientIdentity15 :
    row18_reducedY10_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY10_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep00Coefficient15 row18_reducedY10_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY10_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY10_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY10_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY10_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY10_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY10_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY10_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY10_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY10_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY10_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY10_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY10_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY10_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY10_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY10_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY10_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY10_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY10_combinationStep00CoefficientIdentity00,
      row18_reducedY10_combinationStep00CoefficientIdentity01,
      row18_reducedY10_combinationStep00CoefficientIdentity02,
      row18_reducedY10_combinationStep00CoefficientIdentity03,
      row18_reducedY10_combinationStep00CoefficientIdentity04,
      row18_reducedY10_combinationStep00CoefficientIdentity05,
      row18_reducedY10_combinationStep00CoefficientIdentity06,
      row18_reducedY10_combinationStep00CoefficientIdentity07,
      row18_reducedY10_combinationStep00CoefficientIdentity08,
      row18_reducedY10_combinationStep00CoefficientIdentity09,
      row18_reducedY10_combinationStep00CoefficientIdentity10,
      row18_reducedY10_combinationStep00CoefficientIdentity11,
      row18_reducedY10_combinationStep00CoefficientIdentity12,
      row18_reducedY10_combinationStep00CoefficientIdentity13,
      row18_reducedY10_combinationStep00CoefficientIdentity14,
      row18_reducedY10_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY10_combinationStep00Multiplier * equation

private def row18_reducedY10_combinationStep01Multiplier : ℂ :=
  (((446 / 79) : ℂ) + ((6694 / 1185) : ℂ) * ζ ^ 1 + ((1858 / 1185) : ℂ) * ζ ^ 2 + ((1604 / 1185) : ℂ) * ζ ^ 3 + ((584 / 395) : ℂ) * ζ ^ 5 + ((134 / 395) : ℂ) * ζ ^ 6 - ((1018 / 1185) : ℂ) * ζ ^ 9 - ((584 / 395) : ℂ) * ζ ^ 11 - ((1646 / 237) : ℂ) * ζ ^ 12 - ((6694 / 1185) : ℂ) * ζ ^ 13 + ((1308 / 395) : ℂ) * ζ ^ 15 - ((6694 / 1185) : ℂ) * ζ ^ 17 - ((3314 / 1185) : ℂ) * ζ ^ 18 - ((148 / 1185) : ℂ) * ζ ^ 21 - ((1858 / 1185) : ℂ) * ζ ^ 22 + ((446 / 79) : ℂ) * ζ ^ 24 + ((4942 / 1185) : ℂ) * ζ ^ 25 - ((4942 / 1185) : ℂ) * ζ ^ 27 + ((6694 / 1185) : ℂ) * ζ ^ 29 + ((3716 / 1185) : ℂ) * ζ ^ 30 + ((584 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY10_combinationStep01Coefficient00 : ℂ :=
  (-((58367 / 18723) : ℂ) - ((16918 / 6241) : ℂ) * ζ ^ 1 + ((18311 / 18723) : ℂ) * ζ ^ 2 + ((30575 / 18723) : ℂ) * ζ ^ 3 - ((16918 / 6241) : ℂ) * ζ ^ 5 - ((13352 / 6241) : ℂ) * ζ ^ 6 + ((13352 / 6241) : ℂ) * ζ ^ 8 + ((16918 / 6241) : ℂ) * ζ ^ 9 - ((30575 / 37446) : ℂ) * ζ ^ 11 + ((98393 / 37446) : ℂ) * ζ ^ 12 + ((16918 / 6241) : ℂ) * ζ ^ 13 - ((30623 / 18723) : ℂ) * ζ ^ 15 + ((16918 / 6241) : ℂ) * ζ ^ 17 + ((19835 / 12482) : ℂ) * ζ ^ 18 - ((6197 / 6241) : ℂ) * ζ ^ 21 - ((18311 / 18723) : ℂ) * ζ ^ 22 - ((6869 / 12482) : ℂ) * ζ ^ 24 - ((16 / 6241) : ℂ) * ζ ^ 27 - ((13352 / 6241) : ℂ) * ζ ^ 28 - ((16918 / 6241) : ℂ) * ζ ^ 29 + ((18281 / 37446) : ℂ) * ζ ^ 30 + ((30575 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep01CoefficientIdentity00 :
    row18_reducedY10_combinationStep01Coefficient00 =
      row18_reducedY10_combinationStep00Coefficient00 +
        row18_reducedY10_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep01Coefficient00 row18_reducedY10_combinationStep00Coefficient00 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 (((30938 / 18723) : ℂ) + ((189601 / 187230) : ℂ) * ζ ^ 1 - ((138843 / 62410) : ℂ) * ζ ^ 2 - ((417109 / 187230) : ℂ) * ζ ^ 3 - ((135532 / 93615) : ℂ) * ζ ^ 4 + ((48227 / 37446) : ℂ) * ζ ^ 5 + ((1628 / 395) : ℂ) * ζ ^ 6 + ((23193 / 12482) : ℂ) * ζ ^ 7 + ((7852 / 18723) : ℂ) * ζ ^ 8 - ((129619 / 93615) : ℂ) * ζ ^ 9 - ((230354 / 93615) : ℂ) * ζ ^ 10 - ((9605 / 37446) : ℂ) * ζ ^ 11 + ((79682 / 93615) : ℂ) * ζ ^ 12 + ((458999 / 187230) : ℂ) * ζ ^ 13 + ((336509 / 187230) : ℂ) * ζ ^ 14 - ((12904 / 31205) : ℂ) * ζ ^ 15 - ((24878 / 31205) : ℂ) * ζ ^ 16 - ((44426 / 31205) : ℂ) * ζ ^ 17 - ((42203 / 62410) : ℂ) * ζ ^ 18 - ((9518 / 93615) : ℂ) * ζ ^ 19 - ((39616 / 93615) : ℂ) * ζ ^ 20 + ((58111 / 187230) : ℂ) * ζ ^ 21 + ((104384 / 93615) : ℂ) * ζ ^ 22 + ((100453 / 93615) : ℂ) * ζ ^ 23 - ((40694 / 93615) : ℂ) * ζ ^ 24 - ((175138 / 93615) : ℂ) * ζ ^ 25 - ((36699 / 31205) : ℂ) * ζ ^ 26 + ((12779 / 187230) : ℂ) * ζ ^ 27 + ((29661 / 62410) : ℂ) * ζ ^ 28 + ((8587 / 31205) : ℂ) * ζ ^ 29 + ((438 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep01Coefficient01 : ℂ :=
  (((51989 / 18723) : ℂ) + ((35023 / 12482) : ℂ) * ζ ^ 1 - ((49366 / 18723) : ℂ) * ζ ^ 2 - ((51917 / 12482) : ℂ) * ζ ^ 3 + ((83431 / 37446) : ℂ) * ζ ^ 5 + ((113887 / 37446) : ℂ) * ζ ^ 6 - ((45385 / 18723) : ℂ) * ζ ^ 8 - ((93145 / 37446) : ℂ) * ζ ^ 9 + ((83431 / 37446) : ℂ) * ζ ^ 11 - ((45385 / 37446) : ℂ) * ζ ^ 12 - ((35023 / 12482) : ℂ) * ζ ^ 13 + ((71507 / 37446) : ℂ) * ζ ^ 15 - ((35023 / 12482) : ℂ) * ζ ^ 17 - ((113887 / 37446) : ℂ) * ζ ^ 18 + ((36160 / 18723) : ℂ) * ζ ^ 21 + ((49366 / 18723) : ℂ) * ζ ^ 22 - ((6604 / 18723) : ℂ) * ζ ^ 24 + ((10819 / 18723) : ℂ) * ζ ^ 25 + ((10819 / 18723) : ℂ) * ζ ^ 27 + ((45385 / 18723) : ℂ) * ζ ^ 28 + ((35023 / 12482) : ℂ) * ζ ^ 29 - ((83431 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep01CoefficientIdentity01 :
    row18_reducedY10_combinationStep01Coefficient01 =
      row18_reducedY10_combinationStep00Coefficient01 +
        row18_reducedY10_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep01Coefficient01 row18_reducedY10_combinationStep00Coefficient01 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 (-((62279 / 37446) : ℂ) + ((106481 / 187230) : ℂ) * ζ ^ 1 - ((129431 / 93615) : ℂ) * ζ ^ 2 - ((77146 / 31205) : ℂ) * ζ ^ 3 - ((1423 / 2370) : ℂ) * ζ ^ 4 - ((71966 / 93615) : ℂ) * ζ ^ 5 + ((268357 / 93615) : ℂ) * ζ ^ 6 + ((173732 / 93615) : ℂ) * ζ ^ 7 - ((524 / 31205) : ℂ) * ζ ^ 8 + ((117773 / 62410) : ℂ) * ζ ^ 9 - ((136339 / 187230) : ℂ) * ζ ^ 10 - ((14806 / 18723) : ℂ) * ζ ^ 11 + ((251 / 187230) : ℂ) * ζ ^ 12 + ((42047 / 187230) : ℂ) * ζ ^ 13 + ((87680 / 18723) : ℂ) * ζ ^ 14 + ((289712 / 93615) : ℂ) * ζ ^ 15 - ((68723 / 62410) : ℂ) * ζ ^ 16 - ((311126 / 93615) : ℂ) * ζ ^ 17 - ((36157 / 18723) : ℂ) * ζ ^ 18 + ((236932 / 93615) : ℂ) * ζ ^ 19 + ((2798 / 1185) : ℂ) * ζ ^ 20 + ((7382 / 18723) : ℂ) * ζ ^ 21 + ((73223 / 187230) : ℂ) * ζ ^ 22 - ((6934 / 93615) : ℂ) * ζ ^ 23 - ((225437 / 187230) : ℂ) * ζ ^ 24 - ((9033 / 6241) : ℂ) * ζ ^ 25 - ((118037 / 93615) : ℂ) * ζ ^ 26 + ((2894 / 18723) : ℂ) * ζ ^ 27 + ((59518 / 93615) : ℂ) * ζ ^ 28 + ((36524 / 93615) : ℂ) * ζ ^ 29 + ((4088 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep01Coefficient02 : ℂ :=
  (-((89758 / 18723) : ℂ) - ((14273 / 18723) : ℂ) * ζ ^ 1 + ((16202 / 18723) : ℂ) * ζ ^ 2 + ((123611 / 37446) : ℂ) * ζ ^ 3 - ((51043 / 37446) : ℂ) * ζ ^ 5 - ((1313 / 6241) : ℂ) * ζ ^ 6 + ((30135 / 12482) : ℂ) * ζ ^ 8 + ((11507 / 6241) : ℂ) * ζ ^ 9 - ((54569 / 37446) : ℂ) * ζ ^ 11 + ((30135 / 12482) : ℂ) * ζ ^ 12 + ((14273 / 18723) : ℂ) * ζ ^ 13 - ((73054 / 18723) : ℂ) * ζ ^ 15 + ((14273 / 18723) : ℂ) * ζ ^ 17 + ((20141 / 18723) : ℂ) * ζ ^ 18 - ((95065 / 37446) : ℂ) * ζ ^ 21 - ((16202 / 18723) : ℂ) * ζ ^ 22 + ((7499 / 12482) : ℂ) * ζ ^ 25 + ((95065 / 37446) : ℂ) * ζ ^ 27 - ((30135 / 12482) : ℂ) * ζ ^ 28 - ((14273 / 18723) : ℂ) * ζ ^ 29 - ((1313 / 12482) : ℂ) * ζ ^ 30 + ((54569 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep01CoefficientIdentity02 :
    row18_reducedY10_combinationStep01Coefficient02 =
      row18_reducedY10_combinationStep00Coefficient02 +
        row18_reducedY10_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep01Coefficient02 row18_reducedY10_combinationStep00Coefficient02 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep01Coefficient03 : ℂ :=
  (((58367 / 18723) : ℂ) + ((16918 / 6241) : ℂ) * ζ ^ 1 - ((18311 / 18723) : ℂ) * ζ ^ 2 - ((30575 / 18723) : ℂ) * ζ ^ 3 + ((16918 / 6241) : ℂ) * ζ ^ 5 + ((13352 / 6241) : ℂ) * ζ ^ 6 - ((13352 / 6241) : ℂ) * ζ ^ 8 - ((16918 / 6241) : ℂ) * ζ ^ 9 + ((30575 / 37446) : ℂ) * ζ ^ 11 - ((98393 / 37446) : ℂ) * ζ ^ 12 - ((16918 / 6241) : ℂ) * ζ ^ 13 + ((30623 / 18723) : ℂ) * ζ ^ 15 - ((16918 / 6241) : ℂ) * ζ ^ 17 - ((19835 / 12482) : ℂ) * ζ ^ 18 + ((6197 / 6241) : ℂ) * ζ ^ 21 + ((18311 / 18723) : ℂ) * ζ ^ 22 + ((6869 / 12482) : ℂ) * ζ ^ 24 + ((16 / 6241) : ℂ) * ζ ^ 27 + ((13352 / 6241) : ℂ) * ζ ^ 28 + ((16918 / 6241) : ℂ) * ζ ^ 29 - ((18281 / 37446) : ℂ) * ζ ^ 30 - ((30575 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep01CoefficientIdentity03 :
    row18_reducedY10_combinationStep01Coefficient03 =
      row18_reducedY10_combinationStep00Coefficient03 +
        row18_reducedY10_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep01Coefficient03 row18_reducedY10_combinationStep00Coefficient03 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 (-((30938 / 18723) : ℂ) - ((189601 / 187230) : ℂ) * ζ ^ 1 + ((138843 / 62410) : ℂ) * ζ ^ 2 + ((417109 / 187230) : ℂ) * ζ ^ 3 + ((135532 / 93615) : ℂ) * ζ ^ 4 - ((48227 / 37446) : ℂ) * ζ ^ 5 - ((1628 / 395) : ℂ) * ζ ^ 6 - ((23193 / 12482) : ℂ) * ζ ^ 7 - ((7852 / 18723) : ℂ) * ζ ^ 8 + ((129619 / 93615) : ℂ) * ζ ^ 9 + ((230354 / 93615) : ℂ) * ζ ^ 10 + ((9605 / 37446) : ℂ) * ζ ^ 11 - ((79682 / 93615) : ℂ) * ζ ^ 12 - ((458999 / 187230) : ℂ) * ζ ^ 13 - ((336509 / 187230) : ℂ) * ζ ^ 14 + ((12904 / 31205) : ℂ) * ζ ^ 15 + ((24878 / 31205) : ℂ) * ζ ^ 16 + ((44426 / 31205) : ℂ) * ζ ^ 17 + ((42203 / 62410) : ℂ) * ζ ^ 18 + ((9518 / 93615) : ℂ) * ζ ^ 19 + ((39616 / 93615) : ℂ) * ζ ^ 20 - ((58111 / 187230) : ℂ) * ζ ^ 21 - ((104384 / 93615) : ℂ) * ζ ^ 22 - ((100453 / 93615) : ℂ) * ζ ^ 23 + ((40694 / 93615) : ℂ) * ζ ^ 24 + ((175138 / 93615) : ℂ) * ζ ^ 25 + ((36699 / 31205) : ℂ) * ζ ^ 26 - ((12779 / 187230) : ℂ) * ζ ^ 27 - ((29661 / 62410) : ℂ) * ζ ^ 28 - ((8587 / 31205) : ℂ) * ζ ^ 29 - ((438 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep01CoefficientIdentity04 :
    row18_reducedY10_combinationStep01Coefficient04 =
      row18_reducedY10_combinationStep00Coefficient04 +
        row18_reducedY10_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep01Coefficient04 row18_reducedY10_combinationStep00Coefficient04 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep01CoefficientIdentity05 :
    row18_reducedY10_combinationStep01Coefficient05 =
      row18_reducedY10_combinationStep00Coefficient05 +
        row18_reducedY10_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep01Coefficient05 row18_reducedY10_combinationStep00Coefficient05 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep01CoefficientIdentity06 :
    row18_reducedY10_combinationStep01Coefficient06 =
      row18_reducedY10_combinationStep00Coefficient06 +
        row18_reducedY10_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep01Coefficient06 row18_reducedY10_combinationStep00Coefficient06 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep01CoefficientIdentity07 :
    row18_reducedY10_combinationStep01Coefficient07 =
      row18_reducedY10_combinationStep00Coefficient07 +
        row18_reducedY10_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep01Coefficient07 row18_reducedY10_combinationStep00Coefficient07 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep01CoefficientIdentity08 :
    row18_reducedY10_combinationStep01Coefficient08 =
      row18_reducedY10_combinationStep00Coefficient08 +
        row18_reducedY10_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep01Coefficient08 row18_reducedY10_combinationStep00Coefficient08 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep01CoefficientIdentity09 :
    row18_reducedY10_combinationStep01Coefficient09 =
      row18_reducedY10_combinationStep00Coefficient09 +
        row18_reducedY10_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep01Coefficient09 row18_reducedY10_combinationStep00Coefficient09 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep01CoefficientIdentity10 :
    row18_reducedY10_combinationStep01Coefficient10 =
      row18_reducedY10_combinationStep00Coefficient10 +
        row18_reducedY10_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep01Coefficient10 row18_reducedY10_combinationStep00Coefficient10 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep01CoefficientIdentity11 :
    row18_reducedY10_combinationStep01Coefficient11 =
      row18_reducedY10_combinationStep00Coefficient11 +
        row18_reducedY10_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep01Coefficient11 row18_reducedY10_combinationStep00Coefficient11 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep01CoefficientIdentity12 :
    row18_reducedY10_combinationStep01Coefficient12 =
      row18_reducedY10_combinationStep00Coefficient12 +
        row18_reducedY10_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep01Coefficient12 row18_reducedY10_combinationStep00Coefficient12 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep01CoefficientIdentity13 :
    row18_reducedY10_combinationStep01Coefficient13 =
      row18_reducedY10_combinationStep00Coefficient13 +
        row18_reducedY10_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep01Coefficient13 row18_reducedY10_combinationStep00Coefficient13 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep01CoefficientIdentity14 :
    row18_reducedY10_combinationStep01Coefficient14 =
      row18_reducedY10_combinationStep00Coefficient14 +
        row18_reducedY10_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep01Coefficient14 row18_reducedY10_combinationStep00Coefficient14 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep01CoefficientIdentity15 :
    row18_reducedY10_combinationStep01Coefficient15 =
      row18_reducedY10_combinationStep00Coefficient15 +
        row18_reducedY10_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep01Coefficient15 row18_reducedY10_combinationStep00Coefficient15 row18_reducedY10_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY10_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY10_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY10_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY10_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY10_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY10_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY10_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY10_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY10_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY10_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY10_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY10_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY10_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY10_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY10_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY10_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY10_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY10_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY10_combinationStep01CoefficientIdentity00,
      row18_reducedY10_combinationStep01CoefficientIdentity01,
      row18_reducedY10_combinationStep01CoefficientIdentity02,
      row18_reducedY10_combinationStep01CoefficientIdentity03,
      row18_reducedY10_combinationStep01CoefficientIdentity04,
      row18_reducedY10_combinationStep01CoefficientIdentity05,
      row18_reducedY10_combinationStep01CoefficientIdentity06,
      row18_reducedY10_combinationStep01CoefficientIdentity07,
      row18_reducedY10_combinationStep01CoefficientIdentity08,
      row18_reducedY10_combinationStep01CoefficientIdentity09,
      row18_reducedY10_combinationStep01CoefficientIdentity10,
      row18_reducedY10_combinationStep01CoefficientIdentity11,
      row18_reducedY10_combinationStep01CoefficientIdentity12,
      row18_reducedY10_combinationStep01CoefficientIdentity13,
      row18_reducedY10_combinationStep01CoefficientIdentity14,
      row18_reducedY10_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY10_combinationStep01Multiplier * equation

private def row18_reducedY10_combinationStep02Multiplier : ℂ :=
  (((717068 / 93615) : ℂ) + ((81784 / 18723) : ℂ) * ζ ^ 1 - ((98444 / 93615) : ℂ) * ζ ^ 2 - ((1243496 / 93615) : ℂ) * ζ ^ 3 + ((81784 / 18723) : ℂ) * ζ ^ 5 + ((206208 / 31205) : ℂ) * ζ ^ 6 - ((206208 / 31205) : ℂ) * ζ ^ 8 - ((81784 / 18723) : ℂ) * ζ ^ 9 + ((621748 / 93615) : ℂ) * ζ ^ 11 - ((72794 / 31205) : ℂ) * ζ ^ 12 - ((81784 / 18723) : ℂ) * ζ ^ 13 + ((966754 / 93615) : ℂ) * ζ ^ 15 - ((81784 / 18723) : ℂ) * ζ ^ 17 - ((946108 / 93615) : ℂ) * ζ ^ 18 + ((26764 / 18723) : ℂ) * ζ ^ 21 + ((98444 / 93615) : ℂ) * ζ ^ 22 - ((327484 / 93615) : ℂ) * ζ ^ 24 - ((276742 / 93615) : ℂ) * ζ ^ 27 + ((206208 / 31205) : ℂ) * ζ ^ 28 + ((81784 / 18723) : ℂ) * ζ ^ 29 + ((133414 / 31205) : ℂ) * ζ ^ 30 - ((621748 / 93615) : ℂ) * ζ ^ 31)

private def row18_reducedY10_combinationStep02Coefficient00 : ℂ :=
  (-((59182 / 93615) : ℂ) - ((36665 / 37446) : ℂ) * ζ ^ 1 - ((41614 / 93615) : ℂ) * ζ ^ 2 + ((228173 / 93615) : ℂ) * ζ ^ 3 - ((36665 / 37446) : ℂ) * ζ ^ 5 - ((100796 / 93615) : ℂ) * ζ ^ 6 + ((100796 / 93615) : ℂ) * ζ ^ 8 + ((36665 / 37446) : ℂ) * ζ ^ 9 - ((228173 / 187230) : ℂ) * ζ ^ 11 + ((23623 / 93615) : ℂ) * ζ ^ 12 + ((36665 / 37446) : ℂ) * ζ ^ 13 - ((124933 / 62410) : ℂ) * ζ ^ 15 + ((36665 / 37446) : ℂ) * ζ ^ 17 + ((166982 / 93615) : ℂ) * ζ ^ 18 + ((14095 / 37446) : ℂ) * ζ ^ 21 + ((41614 / 93615) : ℂ) * ζ ^ 22 + ((22062 / 31205) : ℂ) * ζ ^ 24 + ((81547 / 187230) : ℂ) * ζ ^ 27 - ((100796 / 93615) : ℂ) * ζ ^ 28 - ((36665 / 37446) : ℂ) * ζ ^ 29 - ((77173 / 93615) : ℂ) * ζ ^ 30 + ((228173 / 187230) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep02CoefficientIdentity00 :
    row18_reducedY10_combinationStep02Coefficient00 =
      row18_reducedY10_combinationStep01Coefficient00 +
        row18_reducedY10_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep02Coefficient00 row18_reducedY10_combinationStep01Coefficient00 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 (-((6843597 / 2465195) : ℂ) - ((8040877 / 4930390) : ℂ) * ζ ^ 1 - ((3297482 / 7395585) : ℂ) * ζ ^ 2 - ((3606597 / 2465195) : ℂ) * ζ ^ 3 + ((19407572 / 7395585) : ℂ) * ζ ^ 4 + ((20997058 / 7395585) : ℂ) * ζ ^ 5 - ((13593758 / 7395585) : ℂ) * ζ ^ 6 + ((1027706 / 7395585) : ℂ) * ζ ^ 7 - ((9665261 / 7395585) : ℂ) * ζ ^ 8 + ((6038209 / 14791170) : ℂ) * ζ ^ 9 + ((21584473 / 7395585) : ℂ) * ζ ^ 10 - ((10843261 / 7395585) : ℂ) * ζ ^ 11 + ((24971969 / 14791170) : ℂ) * ζ ^ 12 - ((2130894 / 2465195) : ℂ) * ζ ^ 13 - ((15222221 / 14791170) : ℂ) * ζ ^ 14 - ((33007 / 37446) : ℂ) * ζ ^ 15 - ((6934773 / 2465195) : ℂ) * ζ ^ 16 + ((3387788 / 7395585) : ℂ) * ζ ^ 17 + ((4604 / 7395585) : ℂ) * ζ ^ 18 + ((4561803 / 4930390) : ℂ) * ζ ^ 19 + ((19018903 / 7395585) : ℂ) * ζ ^ 20 - ((11543147 / 14791170) : ℂ) * ζ ^ 21 + ((3047556 / 2465195) : ℂ) * ζ ^ 22 - ((260941 / 2465195) : ℂ) * ζ ^ 23 - ((15257131 / 14791170) : ℂ) * ζ ^ 24 - ((6713837 / 14791170) : ℂ) * ζ ^ 25 - ((3776829 / 4930390) : ℂ) * ζ ^ 26 + ((4713643 / 4930390) : ℂ) * ζ ^ 27 - ((375911 / 1479117) : ℂ) * ζ ^ 28 + ((3887839 / 7395585) : ℂ) * ζ ^ 29 - ((2176118 / 7395585) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep02Coefficient01 : ℂ :=
  (((23776 / 6241) : ℂ) + ((41549 / 18723) : ℂ) * ζ ^ 1 - ((20608 / 18723) : ℂ) * ζ ^ 2 - ((191995 / 37446) : ℂ) * ζ ^ 3 + ((129709 / 37446) : ℂ) * ζ ^ 5 + ((21568 / 6241) : ℂ) * ζ ^ 6 - ((40996 / 18723) : ℂ) * ζ ^ 8 - ((88441 / 37446) : ℂ) * ζ ^ 9 + ((129709 / 37446) : ℂ) * ζ ^ 11 - ((20498 / 18723) : ℂ) * ζ ^ 12 - ((41549 / 18723) : ℂ) * ζ ^ 13 + ((67526 / 18723) : ℂ) * ζ ^ 15 - ((41549 / 18723) : ℂ) * ζ ^ 17 - ((21568 / 6241) : ℂ) * ζ ^ 18 + ((10381 / 6241) : ℂ) * ζ ^ 21 + ((20608 / 18723) : ℂ) * ζ ^ 22 - ((30332 / 18723) : ℂ) * ζ ^ 24 - ((15537 / 12482) : ℂ) * ζ ^ 25 - ((15537 / 12482) : ℂ) * ζ ^ 27 + ((40996 / 18723) : ℂ) * ζ ^ 28 + ((41549 / 18723) : ℂ) * ζ ^ 29 - ((129709 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep02CoefficientIdentity01 :
    row18_reducedY10_combinationStep02Coefficient01 =
      row18_reducedY10_combinationStep01Coefficient01 +
        row18_reducedY10_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep02Coefficient01 row18_reducedY10_combinationStep01Coefficient01 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 (((4730518 / 7395585) : ℂ) - ((512607 / 986078) : ℂ) * ζ ^ 1 - ((20133716 / 7395585) : ℂ) * ζ ^ 2 - ((6619169 / 7395585) : ℂ) * ζ ^ 3 + ((24130253 / 7395585) : ℂ) * ζ ^ 4 - ((11277953 / 4930390) : ℂ) * ζ ^ 5 + ((32521169 / 14791170) : ℂ) * ζ ^ 6 + ((4459354 / 7395585) : ℂ) * ζ ^ 7 - ((21963482 / 7395585) : ℂ) * ζ ^ 8 + ((18232837 / 14791170) : ℂ) * ζ ^ 9 - ((14086561 / 14791170) : ℂ) * ζ ^ 10 + ((86566 / 93615) : ℂ) * ζ ^ 11 - ((4600854 / 2465195) : ℂ) * ζ ^ 12 - ((2575 / 493039) : ℂ) * ζ ^ 13 + ((1907819 / 2465195) : ℂ) * ζ ^ 14 - ((4357012 / 7395585) : ℂ) * ζ ^ 15 - ((22561133 / 14791170) : ℂ) * ζ ^ 16 - ((4754183 / 4930390) : ℂ) * ζ ^ 17 + ((14476483 / 7395585) : ℂ) * ζ ^ 18 + ((6179893 / 2465195) : ℂ) * ζ ^ 19 - ((4638181 / 2465195) : ℂ) * ζ ^ 20 + ((8743129 / 2958234) : ℂ) * ζ ^ 21 - ((82337 / 1479117) : ℂ) * ζ ^ 22 - ((7081511 / 4930390) : ℂ) * ζ ^ 23 - ((2365253 / 14791170) : ℂ) * ζ ^ 24 - ((676361 / 4930390) : ℂ) * ζ ^ 25 + ((14688733 / 14791170) : ℂ) * ζ ^ 26 - ((8732187 / 4930390) : ℂ) * ζ ^ 27 + ((6648134 / 2465195) : ℂ) * ζ ^ 28 - ((4728541 / 4930390) : ℂ) * ζ ^ 29 - ((2020681 / 7395585) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep02Coefficient02 : ℂ :=
  (-((89758 / 18723) : ℂ) - ((14273 / 18723) : ℂ) * ζ ^ 1 + ((16202 / 18723) : ℂ) * ζ ^ 2 + ((123611 / 37446) : ℂ) * ζ ^ 3 - ((51043 / 37446) : ℂ) * ζ ^ 5 - ((1313 / 6241) : ℂ) * ζ ^ 6 + ((30135 / 12482) : ℂ) * ζ ^ 8 + ((11507 / 6241) : ℂ) * ζ ^ 9 - ((54569 / 37446) : ℂ) * ζ ^ 11 + ((30135 / 12482) : ℂ) * ζ ^ 12 + ((14273 / 18723) : ℂ) * ζ ^ 13 - ((73054 / 18723) : ℂ) * ζ ^ 15 + ((14273 / 18723) : ℂ) * ζ ^ 17 + ((20141 / 18723) : ℂ) * ζ ^ 18 - ((95065 / 37446) : ℂ) * ζ ^ 21 - ((16202 / 18723) : ℂ) * ζ ^ 22 + ((7499 / 12482) : ℂ) * ζ ^ 25 + ((95065 / 37446) : ℂ) * ζ ^ 27 - ((30135 / 12482) : ℂ) * ζ ^ 28 - ((14273 / 18723) : ℂ) * ζ ^ 29 - ((1313 / 12482) : ℂ) * ζ ^ 30 + ((54569 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep02CoefficientIdentity02 :
    row18_reducedY10_combinationStep02Coefficient02 =
      row18_reducedY10_combinationStep01Coefficient02 +
        row18_reducedY10_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep02Coefficient02 row18_reducedY10_combinationStep01Coefficient02 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep02Coefficient03 : ℂ :=
  (((58367 / 18723) : ℂ) + ((16918 / 6241) : ℂ) * ζ ^ 1 - ((18311 / 18723) : ℂ) * ζ ^ 2 - ((30575 / 18723) : ℂ) * ζ ^ 3 + ((16918 / 6241) : ℂ) * ζ ^ 5 + ((13352 / 6241) : ℂ) * ζ ^ 6 - ((13352 / 6241) : ℂ) * ζ ^ 8 - ((16918 / 6241) : ℂ) * ζ ^ 9 + ((30575 / 37446) : ℂ) * ζ ^ 11 - ((98393 / 37446) : ℂ) * ζ ^ 12 - ((16918 / 6241) : ℂ) * ζ ^ 13 + ((30623 / 18723) : ℂ) * ζ ^ 15 - ((16918 / 6241) : ℂ) * ζ ^ 17 - ((19835 / 12482) : ℂ) * ζ ^ 18 + ((6197 / 6241) : ℂ) * ζ ^ 21 + ((18311 / 18723) : ℂ) * ζ ^ 22 + ((6869 / 12482) : ℂ) * ζ ^ 24 + ((16 / 6241) : ℂ) * ζ ^ 27 + ((13352 / 6241) : ℂ) * ζ ^ 28 + ((16918 / 6241) : ℂ) * ζ ^ 29 - ((18281 / 37446) : ℂ) * ζ ^ 30 - ((30575 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep02CoefficientIdentity03 :
    row18_reducedY10_combinationStep02Coefficient03 =
      row18_reducedY10_combinationStep01Coefficient03 +
        row18_reducedY10_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep02Coefficient03 row18_reducedY10_combinationStep01Coefficient03 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep02Coefficient04 : ℂ :=
  (-((77551 / 31205) : ℂ) - ((64843 / 37446) : ℂ) * ζ ^ 1 + ((133169 / 93615) : ℂ) * ζ ^ 2 - ((75298 / 93615) : ℂ) * ζ ^ 3 - ((64843 / 37446) : ℂ) * ζ ^ 5 - ((99484 / 93615) : ℂ) * ζ ^ 6 + ((99484 / 93615) : ℂ) * ζ ^ 8 + ((64843 / 37446) : ℂ) * ζ ^ 9 + ((37649 / 93615) : ℂ) * ζ ^ 11 + ((444719 / 187230) : ℂ) * ζ ^ 12 + ((64843 / 37446) : ℂ) * ζ ^ 13 + ((68569 / 187230) : ℂ) * ζ ^ 15 + ((64843 / 37446) : ℂ) * ζ ^ 17 - ((36439 / 187230) : ℂ) * ζ ^ 18 - ((51277 / 37446) : ℂ) * ζ ^ 21 - ((133169 / 93615) : ℂ) * ζ ^ 22 - ((78469 / 62410) : ℂ) * ζ ^ 24 - ((82027 / 187230) : ℂ) * ζ ^ 27 - ((99484 / 93615) : ℂ) * ζ ^ 28 - ((64843 / 37446) : ℂ) * ζ ^ 29 + ((81917 / 62410) : ℂ) * ζ ^ 30 - ((37649 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep02CoefficientIdentity04 :
    row18_reducedY10_combinationStep02Coefficient04 =
      row18_reducedY10_combinationStep01Coefficient04 +
        row18_reducedY10_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep02Coefficient04 row18_reducedY10_combinationStep01Coefficient04 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 (((6843597 / 2465195) : ℂ) + ((8040877 / 4930390) : ℂ) * ζ ^ 1 + ((3297482 / 7395585) : ℂ) * ζ ^ 2 + ((3606597 / 2465195) : ℂ) * ζ ^ 3 - ((19407572 / 7395585) : ℂ) * ζ ^ 4 - ((20997058 / 7395585) : ℂ) * ζ ^ 5 + ((13593758 / 7395585) : ℂ) * ζ ^ 6 - ((1027706 / 7395585) : ℂ) * ζ ^ 7 + ((9665261 / 7395585) : ℂ) * ζ ^ 8 - ((6038209 / 14791170) : ℂ) * ζ ^ 9 - ((21584473 / 7395585) : ℂ) * ζ ^ 10 + ((10843261 / 7395585) : ℂ) * ζ ^ 11 - ((24971969 / 14791170) : ℂ) * ζ ^ 12 + ((2130894 / 2465195) : ℂ) * ζ ^ 13 + ((15222221 / 14791170) : ℂ) * ζ ^ 14 + ((33007 / 37446) : ℂ) * ζ ^ 15 + ((6934773 / 2465195) : ℂ) * ζ ^ 16 - ((3387788 / 7395585) : ℂ) * ζ ^ 17 - ((4604 / 7395585) : ℂ) * ζ ^ 18 - ((4561803 / 4930390) : ℂ) * ζ ^ 19 - ((19018903 / 7395585) : ℂ) * ζ ^ 20 + ((11543147 / 14791170) : ℂ) * ζ ^ 21 - ((3047556 / 2465195) : ℂ) * ζ ^ 22 + ((260941 / 2465195) : ℂ) * ζ ^ 23 + ((15257131 / 14791170) : ℂ) * ζ ^ 24 + ((6713837 / 14791170) : ℂ) * ζ ^ 25 + ((3776829 / 4930390) : ℂ) * ζ ^ 26 - ((4713643 / 4930390) : ℂ) * ζ ^ 27 + ((375911 / 1479117) : ℂ) * ζ ^ 28 - ((3887839 / 7395585) : ℂ) * ζ ^ 29 + ((2176118 / 7395585) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep02CoefficientIdentity05 :
    row18_reducedY10_combinationStep02Coefficient05 =
      row18_reducedY10_combinationStep01Coefficient05 +
        row18_reducedY10_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep02Coefficient05 row18_reducedY10_combinationStep01Coefficient05 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep02Coefficient06 : ℂ :=
  (((324118 / 93615) : ℂ) + ((749534 / 93615) : ℂ) * ζ ^ 1 + ((68041 / 12482) : ℂ) * ζ ^ 2 + ((81407 / 31205) : ℂ) * ζ ^ 3 + ((308629 / 187230) : ℂ) * ζ ^ 5 + ((400327 / 187230) : ℂ) * ζ ^ 8 + ((205592 / 93615) : ℂ) * ζ ^ 9 - ((449813 / 93615) : ℂ) * ζ ^ 11 - ((1696799 / 187230) : ℂ) * ζ ^ 12 - ((749534 / 93615) : ℂ) * ζ ^ 13 + ((233999 / 62410) : ℂ) * ζ ^ 15 - ((749534 / 93615) : ℂ) * ζ ^ 17 - ((68041 / 12482) : ℂ) * ζ ^ 18 - ((505313 / 93615) : ℂ) * ζ ^ 21 - ((68041 / 12482) : ℂ) * ζ ^ 22 + ((648236 / 93615) : ℂ) * ζ ^ 24 + ((396813 / 62410) : ℂ) * ζ ^ 25 - ((505313 / 93615) : ℂ) * ζ ^ 27 - ((400327 / 187230) : ℂ) * ζ ^ 28 + ((749534 / 93615) : ℂ) * ζ ^ 29 + ((161467 / 18723) : ℂ) * ζ ^ 30 + ((449813 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep02CoefficientIdentity06 :
    row18_reducedY10_combinationStep02Coefficient06 =
      row18_reducedY10_combinationStep01Coefficient06 +
        row18_reducedY10_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep02Coefficient06 row18_reducedY10_combinationStep01Coefficient06 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 (-((32417468 / 7395585) : ℂ) - ((12153491 / 1479117) : ℂ) * ζ ^ 1 - ((80044043 / 14791170) : ℂ) * ζ ^ 2 - ((4622312 / 7395585) : ℂ) * ζ ^ 3 + ((31100347 / 7395585) : ℂ) * ζ ^ 4 + ((95041639 / 14791170) : ℂ) * ζ ^ 5 + ((43836059 / 14791170) : ℂ) * ζ ^ 6 + ((406498 / 1479117) : ℂ) * ζ ^ 7 - ((19247003 / 4930390) : ℂ) * ζ ^ 8 - ((3535589 / 986078) : ℂ) * ζ ^ 9 - ((5764213 / 2958234) : ℂ) * ζ ^ 10 - ((1564798 / 7395585) : ℂ) * ζ ^ 11 + ((28090076 / 7395585) : ℂ) * ζ ^ 12 + ((28146814 / 7395585) : ℂ) * ζ ^ 13 + ((2840707 / 4930390) : ℂ) * ζ ^ 14 - ((7944629 / 4930390) : ℂ) * ζ ^ 15 - ((21921359 / 4930390) : ℂ) * ζ ^ 16 - ((12853894 / 7395585) : ℂ) * ζ ^ 17 + ((6161474 / 7395585) : ℂ) * ζ ^ 18 + ((11928299 / 4930390) : ℂ) * ζ ^ 19 + ((16618787 / 4930390) : ℂ) * ζ ^ 20 + ((454606 / 2465195) : ℂ) * ζ ^ 21 - ((3045979 / 2465195) : ℂ) * ζ ^ 22 - ((28307633 / 14791170) : ℂ) * ζ ^ 23 - ((35787839 / 14791170) : ℂ) * ζ ^ 24 - ((576557 / 1479117) : ℂ) * ζ ^ 25 + ((6474236 / 7395585) : ℂ) * ζ ^ 26 + ((35396899 / 14791170) : ℂ) * ζ ^ 27 + ((4315673 / 7395585) : ℂ) * ζ ^ 28 - ((3973379 / 4930390) : ℂ) * ζ ^ 29 - ((155437 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep02CoefficientIdentity07 :
    row18_reducedY10_combinationStep02Coefficient07 =
      row18_reducedY10_combinationStep01Coefficient07 +
        row18_reducedY10_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep02Coefficient07 row18_reducedY10_combinationStep01Coefficient07 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep02CoefficientIdentity08 :
    row18_reducedY10_combinationStep02Coefficient08 =
      row18_reducedY10_combinationStep01Coefficient08 +
        row18_reducedY10_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep02Coefficient08 row18_reducedY10_combinationStep01Coefficient08 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep02CoefficientIdentity09 :
    row18_reducedY10_combinationStep02Coefficient09 =
      row18_reducedY10_combinationStep01Coefficient09 +
        row18_reducedY10_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep02Coefficient09 row18_reducedY10_combinationStep01Coefficient09 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep02CoefficientIdentity10 :
    row18_reducedY10_combinationStep02Coefficient10 =
      row18_reducedY10_combinationStep01Coefficient10 +
        row18_reducedY10_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep02Coefficient10 row18_reducedY10_combinationStep01Coefficient10 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep02CoefficientIdentity11 :
    row18_reducedY10_combinationStep02Coefficient11 =
      row18_reducedY10_combinationStep01Coefficient11 +
        row18_reducedY10_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep02Coefficient11 row18_reducedY10_combinationStep01Coefficient11 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep02CoefficientIdentity12 :
    row18_reducedY10_combinationStep02Coefficient12 =
      row18_reducedY10_combinationStep01Coefficient12 +
        row18_reducedY10_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep02Coefficient12 row18_reducedY10_combinationStep01Coefficient12 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep02CoefficientIdentity13 :
    row18_reducedY10_combinationStep02Coefficient13 =
      row18_reducedY10_combinationStep01Coefficient13 +
        row18_reducedY10_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep02Coefficient13 row18_reducedY10_combinationStep01Coefficient13 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep02CoefficientIdentity14 :
    row18_reducedY10_combinationStep02Coefficient14 =
      row18_reducedY10_combinationStep01Coefficient14 +
        row18_reducedY10_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep02Coefficient14 row18_reducedY10_combinationStep01Coefficient14 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep02CoefficientIdentity15 :
    row18_reducedY10_combinationStep02Coefficient15 =
      row18_reducedY10_combinationStep01Coefficient15 +
        row18_reducedY10_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep02Coefficient15 row18_reducedY10_combinationStep01Coefficient15 row18_reducedY10_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY10_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY10_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY10_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY10_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY10_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY10_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY10_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY10_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY10_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY10_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY10_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY10_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY10_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY10_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY10_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY10_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY10_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY10_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY10_combinationStep02CoefficientIdentity00,
      row18_reducedY10_combinationStep02CoefficientIdentity01,
      row18_reducedY10_combinationStep02CoefficientIdentity02,
      row18_reducedY10_combinationStep02CoefficientIdentity03,
      row18_reducedY10_combinationStep02CoefficientIdentity04,
      row18_reducedY10_combinationStep02CoefficientIdentity05,
      row18_reducedY10_combinationStep02CoefficientIdentity06,
      row18_reducedY10_combinationStep02CoefficientIdentity07,
      row18_reducedY10_combinationStep02CoefficientIdentity08,
      row18_reducedY10_combinationStep02CoefficientIdentity09,
      row18_reducedY10_combinationStep02CoefficientIdentity10,
      row18_reducedY10_combinationStep02CoefficientIdentity11,
      row18_reducedY10_combinationStep02CoefficientIdentity12,
      row18_reducedY10_combinationStep02CoefficientIdentity13,
      row18_reducedY10_combinationStep02CoefficientIdentity14,
      row18_reducedY10_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY10_combinationStep02Multiplier * equation

private def row18_reducedY10_combinationStep03Multiplier : ℂ :=
  (((35944 / 18723) : ℂ) + ((22856 / 6241) : ℂ) * ζ ^ 1 + ((18238 / 18723) : ℂ) * ζ ^ 2 - ((5694 / 6241) : ℂ) * ζ ^ 3 + ((9272 / 18723) : ℂ) * ζ ^ 5 - ((9584 / 18723) : ℂ) * ζ ^ 6 - ((4446 / 6241) : ℂ) * ζ ^ 9 - ((9272 / 18723) : ℂ) * ζ ^ 11 - ((59516 / 18723) : ℂ) * ζ ^ 12 - ((22856 / 6241) : ℂ) * ζ ^ 13 + ((45958 / 18723) : ℂ) * ζ ^ 15 - ((22856 / 6241) : ℂ) * ζ ^ 17 - ((46060 / 18723) : ℂ) * ζ ^ 18 - ((26354 / 18723) : ℂ) * ζ ^ 21 - ((18238 / 18723) : ℂ) * ζ ^ 22 + ((35944 / 18723) : ℂ) * ζ ^ 24 + ((59296 / 18723) : ℂ) * ζ ^ 25 - ((59296 / 18723) : ℂ) * ζ ^ 27 + ((22856 / 6241) : ℂ) * ζ ^ 29 + ((36476 / 18723) : ℂ) * ζ ^ 30 + ((9272 / 18723) : ℂ) * ζ ^ 31)

private def row18_reducedY10_combinationStep03Coefficient00 : ℂ :=
  (((1883 / 790) : ℂ) + ((185 / 158) : ℂ) * ζ ^ 1 - ((452 / 395) : ℂ) * ζ ^ 2 - ((221 / 395) : ℂ) * ζ ^ 3 + ((185 / 158) : ℂ) * ζ ^ 5 + ((979 / 790) : ℂ) * ζ ^ 6 - ((979 / 790) : ℂ) * ζ ^ 8 - ((185 / 158) : ℂ) * ζ ^ 9 + ((221 / 790) : ℂ) * ζ ^ 11 - ((1197 / 790) : ℂ) * ζ ^ 12 - ((185 / 158) : ℂ) * ζ ^ 13 + ((543 / 790) : ℂ) * ζ ^ 15 - ((185 / 158) : ℂ) * ζ ^ 17 - ((244 / 395) : ℂ) * ζ ^ 18 + ((217 / 158) : ℂ) * ζ ^ 21 + ((452 / 395) : ℂ) * ζ ^ 22 + ((491 / 790) : ℂ) * ζ ^ 24 + ((101 / 790) : ℂ) * ζ ^ 27 + ((979 / 790) : ℂ) * ζ ^ 28 + ((185 / 158) : ℂ) * ζ ^ 29 - ((109 / 395) : ℂ) * ζ ^ 30 - ((221 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep03CoefficientIdentity00 :
    row18_reducedY10_combinationStep03Coefficient00 =
      row18_reducedY10_combinationStep02Coefficient00 +
        row18_reducedY10_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep03Coefficient00 row18_reducedY10_combinationStep02Coefficient00 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 (-((2746099 / 986078) : ℂ) - ((2645567 / 1479117) : ℂ) * ζ ^ 1 + ((1084319 / 1479117) : ℂ) * ζ ^ 2 + ((2789357 / 986078) : ℂ) * ζ ^ 3 + ((7626823 / 2958234) : ℂ) * ζ ^ 4 - ((1205795 / 2958234) : ℂ) * ζ ^ 5 - ((8446087 / 2958234) : ℂ) * ζ ^ 6 - ((2363041 / 986078) : ℂ) * ζ ^ 7 - ((281664 / 493039) : ℂ) * ζ ^ 8 + ((3604873 / 2958234) : ℂ) * ζ ^ 9 + ((1704969 / 986078) : ℂ) * ζ ^ 10 + ((2572033 / 2958234) : ℂ) * ζ ^ 11 - ((124648 / 493039) : ℂ) * ζ ^ 12 - ((1308611 / 1479117) : ℂ) * ζ ^ 13 - ((2296033 / 2958234) : ℂ) * ζ ^ 14 - ((641138 / 1479117) : ℂ) * ζ ^ 15 - ((101903 / 1479117) : ℂ) * ζ ^ 16 + ((1715935 / 2958234) : ℂ) * ζ ^ 17 + ((462672 / 493039) : ℂ) * ζ ^ 18 + ((857759 / 986078) : ℂ) * ζ ^ 19 + ((180287 / 986078) : ℂ) * ζ ^ 20 - ((745673 / 986078) : ℂ) * ζ ^ 21 - ((1576012 / 1479117) : ℂ) * ζ ^ 22 - ((1009406 / 1479117) : ℂ) * ζ ^ 23 + ((922324 / 1479117) : ℂ) * ζ ^ 24 + ((702588 / 493039) : ℂ) * ζ ^ 25 + ((607075 / 1479117) : ℂ) * ζ ^ 26 - ((804601 / 1479117) : ℂ) * ζ ^ 27 - ((724976 / 1479117) : ℂ) * ζ ^ 28 - ((82683 / 493039) : ℂ) * ζ ^ 29 - ((11590 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep03Coefficient01 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep03CoefficientIdentity01 :
    row18_reducedY10_combinationStep03Coefficient01 =
      row18_reducedY10_combinationStep02Coefficient01 +
        row18_reducedY10_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep03Coefficient01 row18_reducedY10_combinationStep02Coefficient01 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 (((5922464 / 1479117) : ℂ) + ((4343117 / 1479117) : ℂ) * ζ ^ 1 + ((277960 / 493039) : ℂ) * ζ ^ 2 - ((5598331 / 1479117) : ℂ) * ζ ^ 3 - ((2268817 / 493039) : ℂ) * ζ ^ 4 + ((1495613 / 2958234) : ℂ) * ζ ^ 5 + ((12683869 / 2958234) : ℂ) * ζ ^ 6 + ((6253972 / 1479117) : ℂ) * ζ ^ 7 + ((835312 / 493039) : ℂ) * ζ ^ 8 - ((3425612 / 1479117) : ℂ) * ζ ^ 9 - ((4559641 / 1479117) : ℂ) * ζ ^ 10 - ((3315811 / 2958234) : ℂ) * ζ ^ 11 + ((50038 / 1479117) : ℂ) * ζ ^ 12 + ((395087 / 493039) : ℂ) * ζ ^ 13 + ((409563 / 493039) : ℂ) * ζ ^ 14 + ((129136 / 493039) : ℂ) * ζ ^ 15 + ((1609273 / 1479117) : ℂ) * ζ ^ 16 - ((32953 / 1479117) : ℂ) * ζ ^ 17 - ((11804149 / 2958234) : ℂ) * ζ ^ 18 - ((3727961 / 986078) : ℂ) * ζ ^ 19 + ((418871 / 1479117) : ℂ) * ζ ^ 20 + ((2997112 / 1479117) : ℂ) * ζ ^ 21 + ((2631908 / 1479117) : ℂ) * ζ ^ 22 - ((755038 / 1479117) : ℂ) * ζ ^ 23 - ((1217640 / 493039) : ℂ) * ζ ^ 24 - ((560994 / 493039) : ℂ) * ζ ^ 25 + ((3746 / 18723) : ℂ) * ζ ^ 26 + ((319669 / 493039) : ℂ) * ζ ^ 27 + ((276986 / 493039) : ℂ) * ζ ^ 28 + ((310964 / 1479117) : ℂ) * ζ ^ 29 + ((64904 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep03Coefficient02 : ℂ :=
  (-((89758 / 18723) : ℂ) - ((14273 / 18723) : ℂ) * ζ ^ 1 + ((16202 / 18723) : ℂ) * ζ ^ 2 + ((123611 / 37446) : ℂ) * ζ ^ 3 - ((51043 / 37446) : ℂ) * ζ ^ 5 - ((1313 / 6241) : ℂ) * ζ ^ 6 + ((30135 / 12482) : ℂ) * ζ ^ 8 + ((11507 / 6241) : ℂ) * ζ ^ 9 - ((54569 / 37446) : ℂ) * ζ ^ 11 + ((30135 / 12482) : ℂ) * ζ ^ 12 + ((14273 / 18723) : ℂ) * ζ ^ 13 - ((73054 / 18723) : ℂ) * ζ ^ 15 + ((14273 / 18723) : ℂ) * ζ ^ 17 + ((20141 / 18723) : ℂ) * ζ ^ 18 - ((95065 / 37446) : ℂ) * ζ ^ 21 - ((16202 / 18723) : ℂ) * ζ ^ 22 + ((7499 / 12482) : ℂ) * ζ ^ 25 + ((95065 / 37446) : ℂ) * ζ ^ 27 - ((30135 / 12482) : ℂ) * ζ ^ 28 - ((14273 / 18723) : ℂ) * ζ ^ 29 - ((1313 / 12482) : ℂ) * ζ ^ 30 + ((54569 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep03CoefficientIdentity02 :
    row18_reducedY10_combinationStep03Coefficient02 =
      row18_reducedY10_combinationStep02Coefficient02 +
        row18_reducedY10_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep03Coefficient02 row18_reducedY10_combinationStep02Coefficient02 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep03Coefficient03 : ℂ :=
  (((58367 / 18723) : ℂ) + ((16918 / 6241) : ℂ) * ζ ^ 1 - ((18311 / 18723) : ℂ) * ζ ^ 2 - ((30575 / 18723) : ℂ) * ζ ^ 3 + ((16918 / 6241) : ℂ) * ζ ^ 5 + ((13352 / 6241) : ℂ) * ζ ^ 6 - ((13352 / 6241) : ℂ) * ζ ^ 8 - ((16918 / 6241) : ℂ) * ζ ^ 9 + ((30575 / 37446) : ℂ) * ζ ^ 11 - ((98393 / 37446) : ℂ) * ζ ^ 12 - ((16918 / 6241) : ℂ) * ζ ^ 13 + ((30623 / 18723) : ℂ) * ζ ^ 15 - ((16918 / 6241) : ℂ) * ζ ^ 17 - ((19835 / 12482) : ℂ) * ζ ^ 18 + ((6197 / 6241) : ℂ) * ζ ^ 21 + ((18311 / 18723) : ℂ) * ζ ^ 22 + ((6869 / 12482) : ℂ) * ζ ^ 24 + ((16 / 6241) : ℂ) * ζ ^ 27 + ((13352 / 6241) : ℂ) * ζ ^ 28 + ((16918 / 6241) : ℂ) * ζ ^ 29 - ((18281 / 37446) : ℂ) * ζ ^ 30 - ((30575 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep03CoefficientIdentity03 :
    row18_reducedY10_combinationStep03Coefficient03 =
      row18_reducedY10_combinationStep02Coefficient03 +
        row18_reducedY10_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep03Coefficient03 row18_reducedY10_combinationStep02Coefficient03 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep03Coefficient04 : ℂ :=
  (-((77551 / 31205) : ℂ) - ((64843 / 37446) : ℂ) * ζ ^ 1 + ((133169 / 93615) : ℂ) * ζ ^ 2 - ((75298 / 93615) : ℂ) * ζ ^ 3 - ((64843 / 37446) : ℂ) * ζ ^ 5 - ((99484 / 93615) : ℂ) * ζ ^ 6 + ((99484 / 93615) : ℂ) * ζ ^ 8 + ((64843 / 37446) : ℂ) * ζ ^ 9 + ((37649 / 93615) : ℂ) * ζ ^ 11 + ((444719 / 187230) : ℂ) * ζ ^ 12 + ((64843 / 37446) : ℂ) * ζ ^ 13 + ((68569 / 187230) : ℂ) * ζ ^ 15 + ((64843 / 37446) : ℂ) * ζ ^ 17 - ((36439 / 187230) : ℂ) * ζ ^ 18 - ((51277 / 37446) : ℂ) * ζ ^ 21 - ((133169 / 93615) : ℂ) * ζ ^ 22 - ((78469 / 62410) : ℂ) * ζ ^ 24 - ((82027 / 187230) : ℂ) * ζ ^ 27 - ((99484 / 93615) : ℂ) * ζ ^ 28 - ((64843 / 37446) : ℂ) * ζ ^ 29 + ((81917 / 62410) : ℂ) * ζ ^ 30 - ((37649 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep03CoefficientIdentity04 :
    row18_reducedY10_combinationStep03Coefficient04 =
      row18_reducedY10_combinationStep02Coefficient04 +
        row18_reducedY10_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep03Coefficient04 row18_reducedY10_combinationStep02Coefficient04 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep03Coefficient05 : ℂ :=
  (-((17701 / 37446) : ℂ) - ((1636 / 6241) : ℂ) * ζ ^ 1 - ((4807 / 18723) : ℂ) * ζ ^ 2 + ((2419 / 12482) : ℂ) * ζ ^ 3 + ((4209 / 12482) : ℂ) * ζ ^ 5 - ((1208 / 18723) : ℂ) * ζ ^ 6 - ((3878 / 18723) : ℂ) * ζ ^ 9 - ((4209 / 12482) : ℂ) * ζ ^ 11 - ((112 / 18723) : ℂ) * ζ ^ 12 + ((1636 / 6241) : ℂ) * ζ ^ 13 - ((30199 / 37446) : ℂ) * ζ ^ 15 + ((1636 / 6241) : ℂ) * ζ ^ 17 + ((2802 / 6241) : ℂ) * ζ ^ 18 - ((895 / 6241) : ℂ) * ζ ^ 21 + ((4807 / 18723) : ℂ) * ζ ^ 22 - ((17701 / 37446) : ℂ) * ζ ^ 24 - ((7481 / 12482) : ℂ) * ζ ^ 25 + ((7481 / 12482) : ℂ) * ζ ^ 27 - ((1636 / 6241) : ℂ) * ζ ^ 29 - ((9614 / 18723) : ℂ) * ζ ^ 30 + ((4209 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep03CoefficientIdentity05 :
    row18_reducedY10_combinationStep03Coefficient05 =
      row18_reducedY10_combinationStep02Coefficient05 +
        row18_reducedY10_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep03Coefficient05 row18_reducedY10_combinationStep02Coefficient05 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 (((1614043 / 2958234) : ℂ) + ((494590 / 1479117) : ℂ) * ζ ^ 1 + ((1009715 / 1479117) : ℂ) * ζ ^ 2 + ((1051046 / 1479117) : ℂ) * ζ ^ 3 - ((813545 / 2958234) : ℂ) * ζ ^ 4 - ((1166918 / 1479117) : ℂ) * ζ ^ 5 - ((346742 / 1479117) : ℂ) * ζ ^ 6 - ((384971 / 2958234) : ℂ) * ζ ^ 7 - ((51269 / 1479117) : ℂ) * ζ ^ 8 + ((809264 / 1479117) : ℂ) * ζ ^ 9 + ((473585 / 1479117) : ℂ) * ζ ^ 10 + ((738641 / 1479117) : ℂ) * ζ ^ 11 + ((345545 / 986078) : ℂ) * ζ ^ 12 - ((1459892 / 1479117) : ℂ) * ζ ^ 13 - ((517874 / 1479117) : ℂ) * ζ ^ 14 + ((1135091 / 2958234) : ℂ) * ζ ^ 15 + ((559619 / 2958234) : ℂ) * ζ ^ 16 + ((1060642 / 1479117) : ℂ) * ζ ^ 17 + ((1434 / 6241) : ℂ) * ζ ^ 18 - ((1148959 / 2958234) : ℂ) * ζ ^ 19 + ((58100 / 1479117) : ℂ) * ζ ^ 20 - ((48020 / 1479117) : ℂ) * ζ ^ 21 - ((681293 / 1479117) : ℂ) * ζ ^ 22 - ((312041 / 493039) : ℂ) * ζ ^ 23 - ((217276 / 1479117) : ℂ) * ζ ^ 24 + ((334817 / 1479117) : ℂ) * ζ ^ 25 + ((340457 / 1479117) : ℂ) * ζ ^ 26 + ((85031 / 493039) : ℂ) * ζ ^ 27 - ((119582 / 1479117) : ℂ) * ζ ^ 28 - ((90578 / 1479117) : ℂ) * ζ ^ 29 - ((32452 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep03Coefficient06 : ℂ :=
  (((324118 / 93615) : ℂ) + ((749534 / 93615) : ℂ) * ζ ^ 1 + ((68041 / 12482) : ℂ) * ζ ^ 2 + ((81407 / 31205) : ℂ) * ζ ^ 3 + ((308629 / 187230) : ℂ) * ζ ^ 5 + ((400327 / 187230) : ℂ) * ζ ^ 8 + ((205592 / 93615) : ℂ) * ζ ^ 9 - ((449813 / 93615) : ℂ) * ζ ^ 11 - ((1696799 / 187230) : ℂ) * ζ ^ 12 - ((749534 / 93615) : ℂ) * ζ ^ 13 + ((233999 / 62410) : ℂ) * ζ ^ 15 - ((749534 / 93615) : ℂ) * ζ ^ 17 - ((68041 / 12482) : ℂ) * ζ ^ 18 - ((505313 / 93615) : ℂ) * ζ ^ 21 - ((68041 / 12482) : ℂ) * ζ ^ 22 + ((648236 / 93615) : ℂ) * ζ ^ 24 + ((396813 / 62410) : ℂ) * ζ ^ 25 - ((505313 / 93615) : ℂ) * ζ ^ 27 - ((400327 / 187230) : ℂ) * ζ ^ 28 + ((749534 / 93615) : ℂ) * ζ ^ 29 + ((161467 / 18723) : ℂ) * ζ ^ 30 + ((449813 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep03CoefficientIdentity06 :
    row18_reducedY10_combinationStep03Coefficient06 =
      row18_reducedY10_combinationStep02Coefficient06 +
        row18_reducedY10_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep03Coefficient06 row18_reducedY10_combinationStep02Coefficient06 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep03Coefficient07 : ℂ :=
  (-((112927 / 37446) : ℂ) - ((40255 / 18723) : ℂ) * ζ ^ 1 + ((13102 / 18723) : ℂ) * ζ ^ 2 + ((56110 / 18723) : ℂ) * ζ ^ 3 - ((40255 / 18723) : ℂ) * ζ ^ 5 - ((86723 / 37446) : ℂ) * ζ ^ 6 + ((86723 / 37446) : ℂ) * ζ ^ 8 + ((40255 / 18723) : ℂ) * ζ ^ 9 - ((28055 / 18723) : ℂ) * ζ ^ 11 + ((66187 / 37446) : ℂ) * ζ ^ 12 + ((40255 / 18723) : ℂ) * ζ ^ 13 - ((16783 / 6241) : ℂ) * ζ ^ 15 + ((40255 / 18723) : ℂ) * ζ ^ 17 + ((44962 / 18723) : ℂ) * ζ ^ 18 - ((18667 / 18723) : ℂ) * ζ ^ 21 - ((13102 / 18723) : ℂ) * ζ ^ 22 + ((1067 / 12482) : ℂ) * ζ ^ 24 + ((5761 / 18723) : ℂ) * ζ ^ 27 - ((86723 / 37446) : ℂ) * ζ ^ 28 - ((40255 / 18723) : ℂ) * ζ ^ 29 - ((10268 / 18723) : ℂ) * ζ ^ 30 + ((28055 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep03CoefficientIdentity07 :
    row18_reducedY10_combinationStep03Coefficient07 =
      row18_reducedY10_combinationStep02Coefficient07 +
        row18_reducedY10_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep03Coefficient07 row18_reducedY10_combinationStep02Coefficient07 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 (((2746099 / 986078) : ℂ) + ((2645567 / 1479117) : ℂ) * ζ ^ 1 - ((1084319 / 1479117) : ℂ) * ζ ^ 2 - ((2789357 / 986078) : ℂ) * ζ ^ 3 - ((7626823 / 2958234) : ℂ) * ζ ^ 4 + ((1205795 / 2958234) : ℂ) * ζ ^ 5 + ((8446087 / 2958234) : ℂ) * ζ ^ 6 + ((2363041 / 986078) : ℂ) * ζ ^ 7 + ((281664 / 493039) : ℂ) * ζ ^ 8 - ((3604873 / 2958234) : ℂ) * ζ ^ 9 - ((1704969 / 986078) : ℂ) * ζ ^ 10 - ((2572033 / 2958234) : ℂ) * ζ ^ 11 + ((124648 / 493039) : ℂ) * ζ ^ 12 + ((1308611 / 1479117) : ℂ) * ζ ^ 13 + ((2296033 / 2958234) : ℂ) * ζ ^ 14 + ((641138 / 1479117) : ℂ) * ζ ^ 15 + ((101903 / 1479117) : ℂ) * ζ ^ 16 - ((1715935 / 2958234) : ℂ) * ζ ^ 17 - ((462672 / 493039) : ℂ) * ζ ^ 18 - ((857759 / 986078) : ℂ) * ζ ^ 19 - ((180287 / 986078) : ℂ) * ζ ^ 20 + ((745673 / 986078) : ℂ) * ζ ^ 21 + ((1576012 / 1479117) : ℂ) * ζ ^ 22 + ((1009406 / 1479117) : ℂ) * ζ ^ 23 - ((922324 / 1479117) : ℂ) * ζ ^ 24 - ((702588 / 493039) : ℂ) * ζ ^ 25 - ((607075 / 1479117) : ℂ) * ζ ^ 26 + ((804601 / 1479117) : ℂ) * ζ ^ 27 + ((724976 / 1479117) : ℂ) * ζ ^ 28 + ((82683 / 493039) : ℂ) * ζ ^ 29 + ((11590 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep03CoefficientIdentity08 :
    row18_reducedY10_combinationStep03Coefficient08 =
      row18_reducedY10_combinationStep02Coefficient08 +
        row18_reducedY10_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep03Coefficient08 row18_reducedY10_combinationStep02Coefficient08 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep03CoefficientIdentity09 :
    row18_reducedY10_combinationStep03Coefficient09 =
      row18_reducedY10_combinationStep02Coefficient09 +
        row18_reducedY10_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep03Coefficient09 row18_reducedY10_combinationStep02Coefficient09 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep03CoefficientIdentity10 :
    row18_reducedY10_combinationStep03Coefficient10 =
      row18_reducedY10_combinationStep02Coefficient10 +
        row18_reducedY10_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep03Coefficient10 row18_reducedY10_combinationStep02Coefficient10 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep03CoefficientIdentity11 :
    row18_reducedY10_combinationStep03Coefficient11 =
      row18_reducedY10_combinationStep02Coefficient11 +
        row18_reducedY10_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep03Coefficient11 row18_reducedY10_combinationStep02Coefficient11 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep03CoefficientIdentity12 :
    row18_reducedY10_combinationStep03Coefficient12 =
      row18_reducedY10_combinationStep02Coefficient12 +
        row18_reducedY10_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep03Coefficient12 row18_reducedY10_combinationStep02Coefficient12 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep03CoefficientIdentity13 :
    row18_reducedY10_combinationStep03Coefficient13 =
      row18_reducedY10_combinationStep02Coefficient13 +
        row18_reducedY10_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep03Coefficient13 row18_reducedY10_combinationStep02Coefficient13 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep03CoefficientIdentity14 :
    row18_reducedY10_combinationStep03Coefficient14 =
      row18_reducedY10_combinationStep02Coefficient14 +
        row18_reducedY10_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep03Coefficient14 row18_reducedY10_combinationStep02Coefficient14 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep03CoefficientIdentity15 :
    row18_reducedY10_combinationStep03Coefficient15 =
      row18_reducedY10_combinationStep02Coefficient15 +
        row18_reducedY10_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep03Coefficient15 row18_reducedY10_combinationStep02Coefficient15 row18_reducedY10_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY10_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY10_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY10_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY10_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY10_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY10_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY10_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY10_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY10_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY10_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY10_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY10_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY10_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY10_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY10_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY10_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY10_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY10_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY10_combinationStep03CoefficientIdentity00,
      row18_reducedY10_combinationStep03CoefficientIdentity01,
      row18_reducedY10_combinationStep03CoefficientIdentity02,
      row18_reducedY10_combinationStep03CoefficientIdentity03,
      row18_reducedY10_combinationStep03CoefficientIdentity04,
      row18_reducedY10_combinationStep03CoefficientIdentity05,
      row18_reducedY10_combinationStep03CoefficientIdentity06,
      row18_reducedY10_combinationStep03CoefficientIdentity07,
      row18_reducedY10_combinationStep03CoefficientIdentity08,
      row18_reducedY10_combinationStep03CoefficientIdentity09,
      row18_reducedY10_combinationStep03CoefficientIdentity10,
      row18_reducedY10_combinationStep03CoefficientIdentity11,
      row18_reducedY10_combinationStep03CoefficientIdentity12,
      row18_reducedY10_combinationStep03CoefficientIdentity13,
      row18_reducedY10_combinationStep03CoefficientIdentity14,
      row18_reducedY10_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY10_combinationStep03Multiplier * equation

private def row18_reducedY10_combinationStep04Multiplier : ℂ :=
  (((75290 / 18723) : ℂ) + ((206666 / 31205) : ℂ) * ζ ^ 1 - ((67508 / 31205) : ℂ) * ζ ^ 2 - ((691982 / 93615) : ℂ) * ζ ^ 3 + ((386944 / 93615) : ℂ) * ζ ^ 5 + ((533684 / 93615) : ℂ) * ζ ^ 6 - ((40042 / 18723) : ℂ) * ζ ^ 8 - ((265246 / 93615) : ℂ) * ζ ^ 9 + ((426736 / 93615) : ℂ) * ζ ^ 11 - ((40042 / 18723) : ℂ) * ζ ^ 12 - ((206666 / 31205) : ℂ) * ζ ^ 13 + ((152976 / 31205) : ℂ) * ζ ^ 15 - ((206666 / 31205) : ℂ) * ζ ^ 17 - ((736208 / 93615) : ℂ) * ζ ^ 18 + ((71984 / 93615) : ℂ) * ζ ^ 21 + ((67508 / 31205) : ℂ) * ζ ^ 22 + ((233054 / 93615) : ℂ) * ζ ^ 25 - ((71984 / 93615) : ℂ) * ζ ^ 27 + ((40042 / 18723) : ℂ) * ζ ^ 28 + ((206666 / 31205) : ℂ) * ζ ^ 29 + ((266842 / 93615) : ℂ) * ζ ^ 30 - ((426736 / 93615) : ℂ) * ζ ^ 31)

private def row18_reducedY10_combinationStep04Coefficient00 : ℂ :=
  (((1883 / 790) : ℂ) + ((185 / 158) : ℂ) * ζ ^ 1 - ((452 / 395) : ℂ) * ζ ^ 2 - ((221 / 395) : ℂ) * ζ ^ 3 + ((185 / 158) : ℂ) * ζ ^ 5 + ((979 / 790) : ℂ) * ζ ^ 6 - ((979 / 790) : ℂ) * ζ ^ 8 - ((185 / 158) : ℂ) * ζ ^ 9 + ((221 / 790) : ℂ) * ζ ^ 11 - ((1197 / 790) : ℂ) * ζ ^ 12 - ((185 / 158) : ℂ) * ζ ^ 13 + ((543 / 790) : ℂ) * ζ ^ 15 - ((185 / 158) : ℂ) * ζ ^ 17 - ((244 / 395) : ℂ) * ζ ^ 18 + ((217 / 158) : ℂ) * ζ ^ 21 + ((452 / 395) : ℂ) * ζ ^ 22 + ((491 / 790) : ℂ) * ζ ^ 24 + ((101 / 790) : ℂ) * ζ ^ 27 + ((979 / 790) : ℂ) * ζ ^ 28 + ((185 / 158) : ℂ) * ζ ^ 29 - ((109 / 395) : ℂ) * ζ ^ 30 - ((221 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep04CoefficientIdentity00 :
    row18_reducedY10_combinationStep04Coefficient00 =
      row18_reducedY10_combinationStep03Coefficient00 +
        row18_reducedY10_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep04Coefficient00 row18_reducedY10_combinationStep03Coefficient00 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep04Coefficient01 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep04CoefficientIdentity01 :
    row18_reducedY10_combinationStep04Coefficient01 =
      row18_reducedY10_combinationStep03Coefficient01 +
        row18_reducedY10_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep04Coefficient01 row18_reducedY10_combinationStep03Coefficient01 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep04Coefficient02 : ℂ :=
  (-((13503 / 6241) : ℂ) - ((122888 / 93615) : ℂ) * ζ ^ 1 + ((30239 / 37446) : ℂ) * ζ ^ 2 + ((76904 / 31205) : ℂ) * ζ ^ 3 - ((207983 / 187230) : ℂ) * ζ ^ 5 - ((5230 / 6241) : ℂ) * ζ ^ 6 + ((11657 / 12482) : ℂ) * ζ ^ 8 + ((78821 / 93615) : ℂ) * ζ ^ 9 - ((151891 / 93615) : ℂ) * ζ ^ 11 + ((11657 / 12482) : ℂ) * ζ ^ 12 + ((122888 / 93615) : ℂ) * ζ ^ 13 - ((423631 / 187230) : ℂ) * ζ ^ 15 + ((122888 / 93615) : ℂ) * ζ ^ 17 + ((61619 / 37446) : ℂ) * ζ ^ 18 - ((107824 / 93615) : ℂ) * ζ ^ 21 - ((30239 / 37446) : ℂ) * ζ ^ 22 - ((37793 / 187230) : ℂ) * ζ ^ 25 + ((107824 / 93615) : ℂ) * ζ ^ 27 - ((11657 / 12482) : ℂ) * ζ ^ 28 - ((122888 / 93615) : ℂ) * ζ ^ 29 - ((2615 / 6241) : ℂ) * ζ ^ 30 + ((151891 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep04CoefficientIdentity02 :
    row18_reducedY10_combinationStep04Coefficient02 =
      row18_reducedY10_combinationStep03Coefficient02 +
        row18_reducedY10_combinationStep04Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep04Coefficient02 row18_reducedY10_combinationStep03Coefficient02 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 (-((4116541 / 1479117) : ℂ) + ((2163707 / 4930390) : ℂ) * ζ ^ 1 - ((10518817 / 14791170) : ℂ) * ζ ^ 2 - ((5280803 / 7395585) : ℂ) * ζ ^ 3 + ((46586777 / 14791170) : ℂ) * ζ ^ 4 + ((13086323 / 14791170) : ℂ) * ζ ^ 5 + ((3061516 / 7395585) : ℂ) * ζ ^ 6 - ((5472121 / 7395585) : ℂ) * ζ ^ 7 - ((1958775 / 986078) : ℂ) * ζ ^ 8 + ((22418531 / 14791170) : ℂ) * ζ ^ 9 - ((5006543 / 7395585) : ℂ) * ζ ^ 10 - ((2890199 / 14791170) : ℂ) * ζ ^ 11 + ((5628272 / 7395585) : ℂ) * ζ ^ 12 - ((10357409 / 7395585) : ℂ) * ζ ^ 13 + ((15650659 / 14791170) : ℂ) * ζ ^ 14 - ((4083042 / 2465195) : ℂ) * ζ ^ 15 - ((6770471 / 4930390) : ℂ) * ζ ^ 16 + ((12206491 / 14791170) : ℂ) * ζ ^ 17 - ((11426479 / 14791170) : ℂ) * ζ ^ 18 + ((12915583 / 7395585) : ℂ) * ζ ^ 19 + ((597694 / 493039) : ℂ) * ζ ^ 20 - ((169122 / 493039) : ℂ) * ζ ^ 21 + ((4421939 / 4930390) : ℂ) * ζ ^ 22 - ((338857 / 7395585) : ℂ) * ζ ^ 23 - ((2248732 / 7395585) : ℂ) * ζ ^ 24 - ((12720247 / 14791170) : ℂ) * ζ ^ 25 - ((1575973 / 7395585) : ℂ) * ζ ^ 26 + ((5376997 / 14791170) : ℂ) * ζ ^ 27 - ((23633 / 2465195) : ℂ) * ζ ^ 28 + ((11143 / 31205) : ℂ) * ζ ^ 29 - ((1493576 / 7395585) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep04Coefficient03 : ℂ :=
  (((112927 / 37446) : ℂ) + ((40255 / 18723) : ℂ) * ζ ^ 1 - ((13102 / 18723) : ℂ) * ζ ^ 2 - ((56110 / 18723) : ℂ) * ζ ^ 3 + ((40255 / 18723) : ℂ) * ζ ^ 5 + ((86723 / 37446) : ℂ) * ζ ^ 6 - ((86723 / 37446) : ℂ) * ζ ^ 8 - ((40255 / 18723) : ℂ) * ζ ^ 9 + ((28055 / 18723) : ℂ) * ζ ^ 11 - ((66187 / 37446) : ℂ) * ζ ^ 12 - ((40255 / 18723) : ℂ) * ζ ^ 13 + ((16783 / 6241) : ℂ) * ζ ^ 15 - ((40255 / 18723) : ℂ) * ζ ^ 17 - ((44962 / 18723) : ℂ) * ζ ^ 18 + ((18667 / 18723) : ℂ) * ζ ^ 21 + ((13102 / 18723) : ℂ) * ζ ^ 22 - ((1067 / 12482) : ℂ) * ζ ^ 24 - ((5761 / 18723) : ℂ) * ζ ^ 27 + ((86723 / 37446) : ℂ) * ζ ^ 28 + ((40255 / 18723) : ℂ) * ζ ^ 29 + ((10268 / 18723) : ℂ) * ζ ^ 30 - ((28055 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep04CoefficientIdentity03 :
    row18_reducedY10_combinationStep04Coefficient03 =
      row18_reducedY10_combinationStep03Coefficient03 +
        row18_reducedY10_combinationStep04Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep04Coefficient03 row18_reducedY10_combinationStep03Coefficient03 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 (((483043 / 493039) : ℂ) + ((2280836 / 2465195) : ℂ) * ζ ^ 1 - ((17879039 / 7395585) : ℂ) * ζ ^ 2 + ((2098397 / 2465195) : ℂ) * ζ ^ 3 + ((22066561 / 14791170) : ℂ) * ζ ^ 4 - ((2297849 / 2465195) : ℂ) * ζ ^ 5 + ((1444958 / 1479117) : ℂ) * ζ ^ 6 - ((371756 / 7395585) : ℂ) * ζ ^ 7 - ((6050681 / 7395585) : ℂ) * ζ ^ 8 - ((7793127 / 4930390) : ℂ) * ζ ^ 9 + ((13725661 / 14791170) : ℂ) * ζ ^ 10 + ((9925591 / 14791170) : ℂ) * ζ ^ 11 - ((31763387 / 14791170) : ℂ) * ζ ^ 12 + ((21103157 / 14791170) : ℂ) * ζ ^ 13 + ((87893 / 93615) : ℂ) * ζ ^ 14 + ((1027831 / 2465195) : ℂ) * ζ ^ 15 - ((7075619 / 14791170) : ℂ) * ζ ^ 16 - ((808489 / 986078) : ℂ) * ζ ^ 17 + ((20670688 / 7395585) : ℂ) * ζ ^ 18 + ((21441731 / 14791170) : ℂ) * ζ ^ 19 - ((3158813 / 7395585) : ℂ) * ζ ^ 20 + ((24633509 / 14791170) : ℂ) * ζ ^ 21 + ((15622831 / 14791170) : ℂ) * ζ ^ 22 - ((5581346 / 7395585) : ℂ) * ζ ^ 23 - ((2418108 / 2465195) : ℂ) * ζ ^ 24 + ((12291098 / 7395585) : ℂ) * ζ ^ 25 - ((3312821 / 4930390) : ℂ) * ζ ^ 26 - ((4971089 / 7395585) : ℂ) * ζ ^ 27 + ((29371001 / 14791170) : ℂ) * ζ ^ 28 - ((9787399 / 14791170) : ℂ) * ζ ^ 29 - ((1386892 / 7395585) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep04Coefficient04 : ℂ :=
  (-((1883 / 790) : ℂ) - ((185 / 158) : ℂ) * ζ ^ 1 + ((452 / 395) : ℂ) * ζ ^ 2 + ((221 / 395) : ℂ) * ζ ^ 3 - ((185 / 158) : ℂ) * ζ ^ 5 - ((979 / 790) : ℂ) * ζ ^ 6 + ((979 / 790) : ℂ) * ζ ^ 8 + ((185 / 158) : ℂ) * ζ ^ 9 - ((221 / 790) : ℂ) * ζ ^ 11 + ((1197 / 790) : ℂ) * ζ ^ 12 + ((185 / 158) : ℂ) * ζ ^ 13 - ((543 / 790) : ℂ) * ζ ^ 15 + ((185 / 158) : ℂ) * ζ ^ 17 + ((244 / 395) : ℂ) * ζ ^ 18 - ((217 / 158) : ℂ) * ζ ^ 21 - ((452 / 395) : ℂ) * ζ ^ 22 - ((491 / 790) : ℂ) * ζ ^ 24 - ((101 / 790) : ℂ) * ζ ^ 27 - ((979 / 790) : ℂ) * ζ ^ 28 - ((185 / 158) : ℂ) * ζ ^ 29 + ((109 / 395) : ℂ) * ζ ^ 30 + ((221 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep04CoefficientIdentity04 :
    row18_reducedY10_combinationStep04Coefficient04 =
      row18_reducedY10_combinationStep03Coefficient04 +
        row18_reducedY10_combinationStep04Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep04Coefficient04 row18_reducedY10_combinationStep03Coefficient04 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 (-((483043 / 493039) : ℂ) - ((2280836 / 2465195) : ℂ) * ζ ^ 1 + ((17879039 / 7395585) : ℂ) * ζ ^ 2 - ((2098397 / 2465195) : ℂ) * ζ ^ 3 - ((22066561 / 14791170) : ℂ) * ζ ^ 4 + ((2297849 / 2465195) : ℂ) * ζ ^ 5 - ((1444958 / 1479117) : ℂ) * ζ ^ 6 + ((371756 / 7395585) : ℂ) * ζ ^ 7 + ((6050681 / 7395585) : ℂ) * ζ ^ 8 + ((7793127 / 4930390) : ℂ) * ζ ^ 9 - ((13725661 / 14791170) : ℂ) * ζ ^ 10 - ((9925591 / 14791170) : ℂ) * ζ ^ 11 + ((31763387 / 14791170) : ℂ) * ζ ^ 12 - ((21103157 / 14791170) : ℂ) * ζ ^ 13 - ((87893 / 93615) : ℂ) * ζ ^ 14 - ((1027831 / 2465195) : ℂ) * ζ ^ 15 + ((7075619 / 14791170) : ℂ) * ζ ^ 16 + ((808489 / 986078) : ℂ) * ζ ^ 17 - ((20670688 / 7395585) : ℂ) * ζ ^ 18 - ((21441731 / 14791170) : ℂ) * ζ ^ 19 + ((3158813 / 7395585) : ℂ) * ζ ^ 20 - ((24633509 / 14791170) : ℂ) * ζ ^ 21 - ((15622831 / 14791170) : ℂ) * ζ ^ 22 + ((5581346 / 7395585) : ℂ) * ζ ^ 23 + ((2418108 / 2465195) : ℂ) * ζ ^ 24 - ((12291098 / 7395585) : ℂ) * ζ ^ 25 + ((3312821 / 4930390) : ℂ) * ζ ^ 26 + ((4971089 / 7395585) : ℂ) * ζ ^ 27 - ((29371001 / 14791170) : ℂ) * ζ ^ 28 + ((9787399 / 14791170) : ℂ) * ζ ^ 29 + ((1386892 / 7395585) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep04Coefficient05 : ℂ :=
  (-((17701 / 37446) : ℂ) - ((1636 / 6241) : ℂ) * ζ ^ 1 - ((4807 / 18723) : ℂ) * ζ ^ 2 + ((2419 / 12482) : ℂ) * ζ ^ 3 + ((4209 / 12482) : ℂ) * ζ ^ 5 - ((1208 / 18723) : ℂ) * ζ ^ 6 - ((3878 / 18723) : ℂ) * ζ ^ 9 - ((4209 / 12482) : ℂ) * ζ ^ 11 - ((112 / 18723) : ℂ) * ζ ^ 12 + ((1636 / 6241) : ℂ) * ζ ^ 13 - ((30199 / 37446) : ℂ) * ζ ^ 15 + ((1636 / 6241) : ℂ) * ζ ^ 17 + ((2802 / 6241) : ℂ) * ζ ^ 18 - ((895 / 6241) : ℂ) * ζ ^ 21 + ((4807 / 18723) : ℂ) * ζ ^ 22 - ((17701 / 37446) : ℂ) * ζ ^ 24 - ((7481 / 12482) : ℂ) * ζ ^ 25 + ((7481 / 12482) : ℂ) * ζ ^ 27 - ((1636 / 6241) : ℂ) * ζ ^ 29 - ((9614 / 18723) : ℂ) * ζ ^ 30 + ((4209 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep04CoefficientIdentity05 :
    row18_reducedY10_combinationStep04Coefficient05 =
      row18_reducedY10_combinationStep03Coefficient05 +
        row18_reducedY10_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep04Coefficient05 row18_reducedY10_combinationStep03Coefficient05 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep04Coefficient06 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep04CoefficientIdentity06 :
    row18_reducedY10_combinationStep04Coefficient06 =
      row18_reducedY10_combinationStep03Coefficient06 +
        row18_reducedY10_combinationStep04Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep04Coefficient06 row18_reducedY10_combinationStep03Coefficient06 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 (((22593722 / 7395585) : ℂ) + ((97777579 / 14791170) : ℂ) * ζ ^ 1 + ((38153501 / 14791170) : ℂ) * ζ ^ 2 + ((3955673 / 2465195) : ℂ) * ζ ^ 3 + ((6746002 / 7395585) : ℂ) * ζ ^ 4 - ((18092519 / 4930390) : ℂ) * ζ ^ 5 - ((19123593 / 2465195) : ℂ) * ζ ^ 6 - ((28923842 / 7395585) : ℂ) * ζ ^ 7 + ((32640893 / 14791170) : ℂ) * ζ ^ 8 + ((101214211 / 14791170) : ℂ) * ζ ^ 9 + ((84491419 / 14791170) : ℂ) * ζ ^ 10 - ((11198701 / 7395585) : ℂ) * ζ ^ 11 - ((2862481 / 493039) : ℂ) * ζ ^ 12 - ((16980582 / 2465195) : ℂ) * ζ ^ 13 + ((255635 / 2958234) : ℂ) * ζ ^ 14 + ((14834029 / 2958234) : ℂ) * ζ ^ 15 + ((30014474 / 7395585) : ℂ) * ζ ^ 16 + ((5332319 / 1479117) : ℂ) * ζ ^ 17 + ((16003331 / 14791170) : ℂ) * ζ ^ 18 + ((2854675 / 2958234) : ℂ) * ζ ^ 19 - ((11505609 / 4930390) : ℂ) * ζ ^ 20 - ((29846164 / 7395585) : ℂ) * ζ ^ 21 + ((47937403 / 14791170) : ℂ) * ζ ^ 22 + ((7577106 / 2465195) : ℂ) * ζ ^ 23 + ((15049703 / 7395585) : ℂ) * ζ ^ 24 + ((6693 / 12482) : ℂ) * ζ ^ 25 - ((11046271 / 2958234) : ℂ) * ζ ^ 26 - ((15287497 / 14791170) : ℂ) * ζ ^ 27 + ((9330 / 493039) : ℂ) * ζ ^ 28 + ((692522 / 7395585) : ℂ) * ζ ^ 29 + ((2987152 / 7395585) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep04Coefficient07 : ℂ :=
  (-((112927 / 37446) : ℂ) - ((40255 / 18723) : ℂ) * ζ ^ 1 + ((13102 / 18723) : ℂ) * ζ ^ 2 + ((56110 / 18723) : ℂ) * ζ ^ 3 - ((40255 / 18723) : ℂ) * ζ ^ 5 - ((86723 / 37446) : ℂ) * ζ ^ 6 + ((86723 / 37446) : ℂ) * ζ ^ 8 + ((40255 / 18723) : ℂ) * ζ ^ 9 - ((28055 / 18723) : ℂ) * ζ ^ 11 + ((66187 / 37446) : ℂ) * ζ ^ 12 + ((40255 / 18723) : ℂ) * ζ ^ 13 - ((16783 / 6241) : ℂ) * ζ ^ 15 + ((40255 / 18723) : ℂ) * ζ ^ 17 + ((44962 / 18723) : ℂ) * ζ ^ 18 - ((18667 / 18723) : ℂ) * ζ ^ 21 - ((13102 / 18723) : ℂ) * ζ ^ 22 + ((1067 / 12482) : ℂ) * ζ ^ 24 + ((5761 / 18723) : ℂ) * ζ ^ 27 - ((86723 / 37446) : ℂ) * ζ ^ 28 - ((40255 / 18723) : ℂ) * ζ ^ 29 - ((10268 / 18723) : ℂ) * ζ ^ 30 + ((28055 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep04CoefficientIdentity07 :
    row18_reducedY10_combinationStep04Coefficient07 =
      row18_reducedY10_combinationStep03Coefficient07 +
        row18_reducedY10_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep04Coefficient07 row18_reducedY10_combinationStep03Coefficient07 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep04Coefficient08 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep04CoefficientIdentity08 :
    row18_reducedY10_combinationStep04Coefficient08 =
      row18_reducedY10_combinationStep03Coefficient08 +
        row18_reducedY10_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep04Coefficient08 row18_reducedY10_combinationStep03Coefficient08 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep04Coefficient09 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep04CoefficientIdentity09 :
    row18_reducedY10_combinationStep04Coefficient09 =
      row18_reducedY10_combinationStep03Coefficient09 +
        row18_reducedY10_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep04Coefficient09 row18_reducedY10_combinationStep03Coefficient09 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep04Coefficient10 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep04CoefficientIdentity10 :
    row18_reducedY10_combinationStep04Coefficient10 =
      row18_reducedY10_combinationStep03Coefficient10 +
        row18_reducedY10_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep04Coefficient10 row18_reducedY10_combinationStep03Coefficient10 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep04Coefficient11 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep04CoefficientIdentity11 :
    row18_reducedY10_combinationStep04Coefficient11 =
      row18_reducedY10_combinationStep03Coefficient11 +
        row18_reducedY10_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep04Coefficient11 row18_reducedY10_combinationStep03Coefficient11 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep04Coefficient12 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep04CoefficientIdentity12 :
    row18_reducedY10_combinationStep04Coefficient12 =
      row18_reducedY10_combinationStep03Coefficient12 +
        row18_reducedY10_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep04Coefficient12 row18_reducedY10_combinationStep03Coefficient12 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep04Coefficient13 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep04CoefficientIdentity13 :
    row18_reducedY10_combinationStep04Coefficient13 =
      row18_reducedY10_combinationStep03Coefficient13 +
        row18_reducedY10_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep04Coefficient13 row18_reducedY10_combinationStep03Coefficient13 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep04Coefficient14 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep04CoefficientIdentity14 :
    row18_reducedY10_combinationStep04Coefficient14 =
      row18_reducedY10_combinationStep03Coefficient14 +
        row18_reducedY10_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep04Coefficient14 row18_reducedY10_combinationStep03Coefficient14 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep04Coefficient15 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep04CoefficientIdentity15 :
    row18_reducedY10_combinationStep04Coefficient15 =
      row18_reducedY10_combinationStep03Coefficient15 +
        row18_reducedY10_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep04Coefficient15 row18_reducedY10_combinationStep03Coefficient15 row18_reducedY10_combinationStep04Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY10_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY10_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY10_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY10_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY10_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY10_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY10_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY10_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY10_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY10_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY10_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY10_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY10_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY10_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY10_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY10_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY10_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY10_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY10_combinationStep04CoefficientIdentity00,
      row18_reducedY10_combinationStep04CoefficientIdentity01,
      row18_reducedY10_combinationStep04CoefficientIdentity02,
      row18_reducedY10_combinationStep04CoefficientIdentity03,
      row18_reducedY10_combinationStep04CoefficientIdentity04,
      row18_reducedY10_combinationStep04CoefficientIdentity05,
      row18_reducedY10_combinationStep04CoefficientIdentity06,
      row18_reducedY10_combinationStep04CoefficientIdentity07,
      row18_reducedY10_combinationStep04CoefficientIdentity08,
      row18_reducedY10_combinationStep04CoefficientIdentity09,
      row18_reducedY10_combinationStep04CoefficientIdentity10,
      row18_reducedY10_combinationStep04CoefficientIdentity11,
      row18_reducedY10_combinationStep04CoefficientIdentity12,
      row18_reducedY10_combinationStep04CoefficientIdentity13,
      row18_reducedY10_combinationStep04CoefficientIdentity14,
      row18_reducedY10_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY10_combinationStep04Multiplier * equation

private def row18_reducedY10_combinationStep05Multiplier : ℂ :=
  (((4940 / 18723) : ℂ) + ((25166 / 18723) : ℂ) * ζ ^ 1 + ((21352 / 18723) : ℂ) * ζ ^ 2 + ((31286 / 18723) : ℂ) * ζ ^ 5 + ((16412 / 18723) : ℂ) * ζ ^ 6 + ((16412 / 18723) : ℂ) * ζ ^ 8 + ((31286 / 18723) : ℂ) * ζ ^ 9 - ((45470 / 18723) : ℂ) * ζ ^ 11 - ((13586 / 6241) : ℂ) * ζ ^ 12 - ((25166 / 18723) : ℂ) * ζ ^ 13 + ((3436 / 6241) : ℂ) * ζ ^ 15 - ((25166 / 18723) : ℂ) * ζ ^ 17 - ((14348 / 18723) : ℂ) * ζ ^ 18 - ((28226 / 18723) : ℂ) * ζ ^ 21 - ((21352 / 18723) : ℂ) * ζ ^ 22 - ((688 / 6241) : ℂ) * ζ ^ 24 - ((2040 / 6241) : ℂ) * ζ ^ 25 - ((3436 / 6241) : ℂ) * ζ ^ 27 - ((16412 / 18723) : ℂ) * ζ ^ 28 + ((25166 / 18723) : ℂ) * ζ ^ 29 + ((57170 / 18723) : ℂ) * ζ ^ 30 + ((45470 / 18723) : ℂ) * ζ ^ 31)

private def row18_reducedY10_combinationStep05Coefficient00 : ℂ :=
  (((1883 / 790) : ℂ) + ((185 / 158) : ℂ) * ζ ^ 1 - ((452 / 395) : ℂ) * ζ ^ 2 - ((221 / 395) : ℂ) * ζ ^ 3 + ((185 / 158) : ℂ) * ζ ^ 5 + ((979 / 790) : ℂ) * ζ ^ 6 - ((979 / 790) : ℂ) * ζ ^ 8 - ((185 / 158) : ℂ) * ζ ^ 9 + ((221 / 790) : ℂ) * ζ ^ 11 - ((1197 / 790) : ℂ) * ζ ^ 12 - ((185 / 158) : ℂ) * ζ ^ 13 + ((543 / 790) : ℂ) * ζ ^ 15 - ((185 / 158) : ℂ) * ζ ^ 17 - ((244 / 395) : ℂ) * ζ ^ 18 + ((217 / 158) : ℂ) * ζ ^ 21 + ((452 / 395) : ℂ) * ζ ^ 22 + ((491 / 790) : ℂ) * ζ ^ 24 + ((101 / 790) : ℂ) * ζ ^ 27 + ((979 / 790) : ℂ) * ζ ^ 28 + ((185 / 158) : ℂ) * ζ ^ 29 - ((109 / 395) : ℂ) * ζ ^ 30 - ((221 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep05CoefficientIdentity00 :
    row18_reducedY10_combinationStep05Coefficient00 =
      row18_reducedY10_combinationStep04Coefficient00 +
        row18_reducedY10_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep05Coefficient00 row18_reducedY10_combinationStep04Coefficient00 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep05Coefficient01 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep05CoefficientIdentity01 :
    row18_reducedY10_combinationStep05Coefficient01 =
      row18_reducedY10_combinationStep04Coefficient01 +
        row18_reducedY10_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep05Coefficient01 row18_reducedY10_combinationStep04Coefficient01 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep05Coefficient02 : ℂ :=
  (((25 / 79) : ℂ) - ((29 / 395) : ℂ) * ζ ^ 1 - ((25 / 158) : ℂ) * ζ ^ 2 - ((113 / 790) : ℂ) * ζ ^ 3 - ((309 / 790) : ℂ) * ζ ^ 5 - ((14 / 79) : ℂ) * ζ ^ 6 - ((1 / 158) : ℂ) * ζ ^ 8 - ((269 / 790) : ℂ) * ζ ^ 9 - ((78 / 395) : ℂ) * ζ ^ 11 - ((1 / 158) : ℂ) * ζ ^ 12 + ((29 / 395) : ℂ) * ζ ^ 13 - ((69 / 395) : ℂ) * ζ ^ 15 + ((29 / 395) : ℂ) * ζ ^ 17 + ((3 / 158) : ℂ) * ζ ^ 18 + ((171 / 790) : ℂ) * ζ ^ 21 + ((25 / 158) : ℂ) * ζ ^ 22 + ((251 / 790) : ℂ) * ζ ^ 25 - ((171 / 790) : ℂ) * ζ ^ 27 + ((1 / 158) : ℂ) * ζ ^ 28 - ((29 / 395) : ℂ) * ζ ^ 29 - ((7 / 79) : ℂ) * ζ ^ 30 + ((78 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep05CoefficientIdentity02 :
    row18_reducedY10_combinationStep05Coefficient02 =
      row18_reducedY10_combinationStep04Coefficient02 +
        row18_reducedY10_combinationStep05Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep05Coefficient02 row18_reducedY10_combinationStep04Coefficient02 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 (-((3621356 / 1479117) : ℂ) - ((1610015 / 1479117) : ℂ) * ζ ^ 1 + ((3126235 / 2958234) : ℂ) * ζ ^ 2 + ((1275664 / 493039) : ℂ) * ζ ^ 3 + ((3529078 / 1479117) : ℂ) * ζ ^ 4 + ((714595 / 1479117) : ℂ) * ζ ^ 5 - ((2444281 / 1479117) : ℂ) * ζ ^ 6 - ((7160767 / 2958234) : ℂ) * ζ ^ 7 - ((2016404 / 1479117) : ℂ) * ζ ^ 8 + ((704893 / 1479117) : ℂ) * ζ ^ 9 + ((3088613 / 2958234) : ℂ) * ζ ^ 10 + ((864248 / 1479117) : ℂ) * ζ ^ 11 - ((379096 / 1479117) : ℂ) * ζ ^ 12 - ((934166 / 1479117) : ℂ) * ζ ^ 13 - ((587363 / 2958234) : ℂ) * ζ ^ 14 + ((108737 / 1479117) : ℂ) * ζ ^ 15 + ((257125 / 2958234) : ℂ) * ζ ^ 16 + ((597820 / 1479117) : ℂ) * ζ ^ 17 + ((673169 / 986078) : ℂ) * ζ ^ 18 + ((926216 / 1479117) : ℂ) * ζ ^ 19 - ((803107 / 2958234) : ℂ) * ζ ^ 20 - ((3057275 / 2958234) : ℂ) * ζ ^ 21 - ((418887 / 493039) : ℂ) * ζ ^ 22 - ((145867 / 493039) : ℂ) * ζ ^ 23 + ((689159 / 1479117) : ℂ) * ζ ^ 24 + ((1015099 / 986078) : ℂ) * ζ ^ 25 + ((1338092 / 1479117) : ℂ) * ζ ^ 26 + ((244433 / 1479117) : ℂ) * ζ ^ 27 - ((928190 / 1479117) : ℂ) * ζ ^ 28 - ((506685 / 986078) : ℂ) * ζ ^ 29 - ((113675 / 986078) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep05Coefficient03 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep05CoefficientIdentity03 :
    row18_reducedY10_combinationStep05Coefficient03 =
      row18_reducedY10_combinationStep04Coefficient03 +
        row18_reducedY10_combinationStep05Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep05Coefficient03 row18_reducedY10_combinationStep04Coefficient03 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 (((3000091 / 986078) : ℂ) + ((3451868 / 1479117) : ℂ) * ζ ^ 1 - ((643223 / 2958234) : ℂ) * ζ ^ 2 - ((6572171 / 2958234) : ℂ) * ζ ^ 3 - ((4189220 / 1479117) : ℂ) * ζ ^ 4 - ((311431 / 1479117) : ℂ) * ζ ^ 5 + ((9881717 / 2958234) : ℂ) * ζ ^ 6 + ((5208484 / 1479117) : ℂ) * ζ ^ 7 + ((889229 / 1479117) : ℂ) * ζ ^ 8 - ((882103 / 493039) : ℂ) * ζ ^ 9 - ((5041255 / 2958234) : ℂ) * ζ ^ 10 - ((3156845 / 2958234) : ℂ) * ζ ^ 11 - ((273376 / 493039) : ℂ) * ζ ^ 12 + ((67788 / 493039) : ℂ) * ζ ^ 13 + ((4199599 / 2958234) : ℂ) * ζ ^ 14 + ((2370539 / 1479117) : ℂ) * ζ ^ 15 + ((606620 / 1479117) : ℂ) * ζ ^ 16 - ((1121870 / 1479117) : ℂ) * ζ ^ 17 - ((5403001 / 2958234) : ℂ) * ζ ^ 18 - ((2029385 / 986078) : ℂ) * ζ ^ 19 - ((2442811 / 2958234) : ℂ) * ζ ^ 20 + ((2976623 / 2958234) : ℂ) * ζ ^ 21 + ((2384530 / 1479117) : ℂ) * ζ ^ 22 - ((377957 / 1479117) : ℂ) * ζ ^ 23 - ((2715223 / 1479117) : ℂ) * ζ ^ 24 - ((936142 / 493039) : ℂ) * ζ ^ 25 - ((988025 / 986078) : ℂ) * ζ ^ 26 + ((1974389 / 2958234) : ℂ) * ζ ^ 27 + ((2334259 / 2958234) : ℂ) * ζ ^ 28 + ((673010 / 1479117) : ℂ) * ζ ^ 29 + ((318290 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep05Coefficient04 : ℂ :=
  (-((1883 / 790) : ℂ) - ((185 / 158) : ℂ) * ζ ^ 1 + ((452 / 395) : ℂ) * ζ ^ 2 + ((221 / 395) : ℂ) * ζ ^ 3 - ((185 / 158) : ℂ) * ζ ^ 5 - ((979 / 790) : ℂ) * ζ ^ 6 + ((979 / 790) : ℂ) * ζ ^ 8 + ((185 / 158) : ℂ) * ζ ^ 9 - ((221 / 790) : ℂ) * ζ ^ 11 + ((1197 / 790) : ℂ) * ζ ^ 12 + ((185 / 158) : ℂ) * ζ ^ 13 - ((543 / 790) : ℂ) * ζ ^ 15 + ((185 / 158) : ℂ) * ζ ^ 17 + ((244 / 395) : ℂ) * ζ ^ 18 - ((217 / 158) : ℂ) * ζ ^ 21 - ((452 / 395) : ℂ) * ζ ^ 22 - ((491 / 790) : ℂ) * ζ ^ 24 - ((101 / 790) : ℂ) * ζ ^ 27 - ((979 / 790) : ℂ) * ζ ^ 28 - ((185 / 158) : ℂ) * ζ ^ 29 + ((109 / 395) : ℂ) * ζ ^ 30 + ((221 / 790) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep05CoefficientIdentity04 :
    row18_reducedY10_combinationStep05Coefficient04 =
      row18_reducedY10_combinationStep04Coefficient04 +
        row18_reducedY10_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep05Coefficient04 row18_reducedY10_combinationStep04Coefficient04 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep05Coefficient05 : ℂ :=
  (-((18 / 79) : ℂ) - ((65 / 158) : ℂ) * ζ ^ 1 - ((40 / 79) : ℂ) * ζ ^ 2 - ((8 / 79) : ℂ) * ζ ^ 3 - ((31 / 79) : ℂ) * ζ ^ 5 - ((55 / 79) : ℂ) * ζ ^ 6 - ((85 / 158) : ℂ) * ζ ^ 9 + ((31 / 79) : ℂ) * ζ ^ 11 + ((31 / 79) : ℂ) * ζ ^ 12 + ((65 / 158) : ℂ) * ζ ^ 13 - ((44 / 79) : ℂ) * ζ ^ 15 + ((65 / 158) : ℂ) * ζ ^ 17 + ((25 / 79) : ℂ) * ζ ^ 18 + ((23 / 79) : ℂ) * ζ ^ 21 + ((40 / 79) : ℂ) * ζ ^ 22 - ((18 / 79) : ℂ) * ζ ^ 24 - ((3 / 158) : ℂ) * ζ ^ 25 + ((3 / 158) : ℂ) * ζ ^ 27 - ((65 / 158) : ℂ) * ζ ^ 29 - ((80 / 79) : ℂ) * ζ ^ 30 - ((31 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY10_combinationStep05CoefficientIdentity05 :
    row18_reducedY10_combinationStep05Coefficient05 =
      row18_reducedY10_combinationStep04Coefficient05 +
        row18_reducedY10_combinationStep05Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep05Coefficient05 row18_reducedY10_combinationStep04Coefficient05 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 (-((894781 / 2958234) : ℂ) - ((108373 / 1479117) : ℂ) * ζ ^ 1 + ((1049015 / 2958234) : ℂ) * ζ ^ 2 + ((267144 / 493039) : ℂ) * ζ ^ 3 + ((471539 / 2958234) : ℂ) * ζ ^ 4 + ((614056 / 1479117) : ℂ) * ζ ^ 5 + ((2459987 / 2958234) : ℂ) * ζ ^ 6 - ((373385 / 986078) : ℂ) * ζ ^ 7 - ((2158393 / 2958234) : ℂ) * ζ ^ 8 - ((36535 / 1479117) : ℂ) * ζ ^ 9 - ((55679 / 1479117) : ℂ) * ζ ^ 10 - ((610813 / 1479117) : ℂ) * ζ ^ 11 - ((1265161 / 2958234) : ℂ) * ζ ^ 12 + ((451957 / 1479117) : ℂ) * ζ ^ 13 + ((8668 / 493039) : ℂ) * ζ ^ 14 - ((203398 / 1479117) : ℂ) * ζ ^ 15 + ((744613 / 2958234) : ℂ) * ζ ^ 16 + ((505283 / 986078) : ℂ) * ζ ^ 17 + ((115 / 12482) : ℂ) * ζ ^ 18 - ((804363 / 986078) : ℂ) * ζ ^ 19 - ((954680 / 1479117) : ℂ) * ζ ^ 20 - ((972961 / 2958234) : ℂ) * ζ ^ 21 - ((3028481 / 2958234) : ℂ) * ζ ^ 22 - ((1071370 / 1479117) : ℂ) * ζ ^ 23 - ((42106 / 1479117) : ℂ) * ζ ^ 24 - ((30053 / 2958234) : ℂ) * ζ ^ 25 - ((89379 / 493039) : ℂ) * ζ ^ 26 + ((83591 / 2958234) : ℂ) * ζ ^ 27 + ((37551 / 493039) : ℂ) * ζ ^ 28 - ((1599295 / 2958234) : ℂ) * ζ ^ 29 - ((295555 / 2958234) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep05Coefficient06 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep05CoefficientIdentity06 :
    row18_reducedY10_combinationStep05Coefficient06 =
      row18_reducedY10_combinationStep04Coefficient06 +
        row18_reducedY10_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep05Coefficient06 row18_reducedY10_combinationStep04Coefficient06 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep05Coefficient07 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep05CoefficientIdentity07 :
    row18_reducedY10_combinationStep05Coefficient07 =
      row18_reducedY10_combinationStep04Coefficient07 +
        row18_reducedY10_combinationStep05Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep05Coefficient07 row18_reducedY10_combinationStep04Coefficient07 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 (-((3000091 / 986078) : ℂ) - ((3451868 / 1479117) : ℂ) * ζ ^ 1 + ((643223 / 2958234) : ℂ) * ζ ^ 2 + ((6572171 / 2958234) : ℂ) * ζ ^ 3 + ((4189220 / 1479117) : ℂ) * ζ ^ 4 + ((311431 / 1479117) : ℂ) * ζ ^ 5 - ((9881717 / 2958234) : ℂ) * ζ ^ 6 - ((5208484 / 1479117) : ℂ) * ζ ^ 7 - ((889229 / 1479117) : ℂ) * ζ ^ 8 + ((882103 / 493039) : ℂ) * ζ ^ 9 + ((5041255 / 2958234) : ℂ) * ζ ^ 10 + ((3156845 / 2958234) : ℂ) * ζ ^ 11 + ((273376 / 493039) : ℂ) * ζ ^ 12 - ((67788 / 493039) : ℂ) * ζ ^ 13 - ((4199599 / 2958234) : ℂ) * ζ ^ 14 - ((2370539 / 1479117) : ℂ) * ζ ^ 15 - ((606620 / 1479117) : ℂ) * ζ ^ 16 + ((1121870 / 1479117) : ℂ) * ζ ^ 17 + ((5403001 / 2958234) : ℂ) * ζ ^ 18 + ((2029385 / 986078) : ℂ) * ζ ^ 19 + ((2442811 / 2958234) : ℂ) * ζ ^ 20 - ((2976623 / 2958234) : ℂ) * ζ ^ 21 - ((2384530 / 1479117) : ℂ) * ζ ^ 22 + ((377957 / 1479117) : ℂ) * ζ ^ 23 + ((2715223 / 1479117) : ℂ) * ζ ^ 24 + ((936142 / 493039) : ℂ) * ζ ^ 25 + ((988025 / 986078) : ℂ) * ζ ^ 26 - ((1974389 / 2958234) : ℂ) * ζ ^ 27 - ((2334259 / 2958234) : ℂ) * ζ ^ 28 - ((673010 / 1479117) : ℂ) * ζ ^ 29 - ((318290 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep05Coefficient08 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep05CoefficientIdentity08 :
    row18_reducedY10_combinationStep05Coefficient08 =
      row18_reducedY10_combinationStep04Coefficient08 +
        row18_reducedY10_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep05Coefficient08 row18_reducedY10_combinationStep04Coefficient08 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep05Coefficient09 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep05CoefficientIdentity09 :
    row18_reducedY10_combinationStep05Coefficient09 =
      row18_reducedY10_combinationStep04Coefficient09 +
        row18_reducedY10_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep05Coefficient09 row18_reducedY10_combinationStep04Coefficient09 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep05Coefficient10 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep05CoefficientIdentity10 :
    row18_reducedY10_combinationStep05Coefficient10 =
      row18_reducedY10_combinationStep04Coefficient10 +
        row18_reducedY10_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep05Coefficient10 row18_reducedY10_combinationStep04Coefficient10 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep05Coefficient11 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep05CoefficientIdentity11 :
    row18_reducedY10_combinationStep05Coefficient11 =
      row18_reducedY10_combinationStep04Coefficient11 +
        row18_reducedY10_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep05Coefficient11 row18_reducedY10_combinationStep04Coefficient11 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep05Coefficient12 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep05CoefficientIdentity12 :
    row18_reducedY10_combinationStep05Coefficient12 =
      row18_reducedY10_combinationStep04Coefficient12 +
        row18_reducedY10_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep05Coefficient12 row18_reducedY10_combinationStep04Coefficient12 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep05Coefficient13 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep05CoefficientIdentity13 :
    row18_reducedY10_combinationStep05Coefficient13 =
      row18_reducedY10_combinationStep04Coefficient13 +
        row18_reducedY10_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep05Coefficient13 row18_reducedY10_combinationStep04Coefficient13 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep05Coefficient14 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep05CoefficientIdentity14 :
    row18_reducedY10_combinationStep05Coefficient14 =
      row18_reducedY10_combinationStep04Coefficient14 +
        row18_reducedY10_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep05Coefficient14 row18_reducedY10_combinationStep04Coefficient14 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep05Coefficient15 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep05CoefficientIdentity15 :
    row18_reducedY10_combinationStep05Coefficient15 =
      row18_reducedY10_combinationStep04Coefficient15 +
        row18_reducedY10_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep05Coefficient15 row18_reducedY10_combinationStep04Coefficient15 row18_reducedY10_combinationStep05Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY10_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY10_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY10_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY10_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY10_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY10_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY10_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY10_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY10_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY10_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY10_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY10_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY10_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY10_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY10_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY10_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY10_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY10_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY10_combinationStep05CoefficientIdentity00,
      row18_reducedY10_combinationStep05CoefficientIdentity01,
      row18_reducedY10_combinationStep05CoefficientIdentity02,
      row18_reducedY10_combinationStep05CoefficientIdentity03,
      row18_reducedY10_combinationStep05CoefficientIdentity04,
      row18_reducedY10_combinationStep05CoefficientIdentity05,
      row18_reducedY10_combinationStep05CoefficientIdentity06,
      row18_reducedY10_combinationStep05CoefficientIdentity07,
      row18_reducedY10_combinationStep05CoefficientIdentity08,
      row18_reducedY10_combinationStep05CoefficientIdentity09,
      row18_reducedY10_combinationStep05CoefficientIdentity10,
      row18_reducedY10_combinationStep05CoefficientIdentity11,
      row18_reducedY10_combinationStep05CoefficientIdentity12,
      row18_reducedY10_combinationStep05CoefficientIdentity13,
      row18_reducedY10_combinationStep05CoefficientIdentity14,
      row18_reducedY10_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY10_combinationStep05Multiplier * equation

private def row18_reducedY10_combinationStep06Multiplier : ℂ :=
  (-((18 / 5) : ℂ) - (2 : ℂ) * ζ ^ 1 + ((4 / 5) : ℂ) * ζ ^ 2 + (8 : ℂ) * ζ ^ 3 - (2 : ℂ) * ζ ^ 5 - ((14 / 5) : ℂ) * ζ ^ 6 + ((14 / 5) : ℂ) * ζ ^ 8 + (2 : ℂ) * ζ ^ 9 - (4 : ℂ) * ζ ^ 11 + ((2 / 5) : ℂ) * ζ ^ 12 + (2 : ℂ) * ζ ^ 13 - (6 : ℂ) * ζ ^ 15 + (2 : ℂ) * ζ ^ 17 + ((28 / 5) : ℂ) * ζ ^ 18 - ((4 / 5) : ℂ) * ζ ^ 22 + ((14 / 5) : ℂ) * ζ ^ 24 + (2 : ℂ) * ζ ^ 27 - ((14 / 5) : ℂ) * ζ ^ 28 - (2 : ℂ) * ζ ^ 29 - ((12 / 5) : ℂ) * ζ ^ 30 + (4 : ℂ) * ζ ^ 31)

private def row18_reducedY10_combinationStep06Coefficient00 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity00 :
    row18_reducedY10_combinationStep06Coefficient00 =
      row18_reducedY10_combinationStep05Coefficient00 +
        row18_reducedY10_combinationStep06Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep06Coefficient00 row18_reducedY10_combinationStep05Coefficient00 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 (((355 / 158) : ℂ) + ((482 / 395) : ℂ) * ζ ^ 1 - ((6 / 79) : ℂ) * ζ ^ 2 + ((21 / 79) : ℂ) * ζ ^ 3 - ((216 / 79) : ℂ) * ζ ^ 4 - ((1531 / 790) : ℂ) * ζ ^ 5 + ((714 / 395) : ℂ) * ζ ^ 6 + ((196 / 395) : ℂ) * ζ ^ 7 + ((758 / 395) : ℂ) * ζ ^ 8 + ((7 / 395) : ℂ) * ζ ^ 9 - ((2063 / 790) : ℂ) * ζ ^ 10 - ((1153 / 790) : ℂ) * ζ ^ 11 - ((46 / 395) : ℂ) * ζ ^ 12 + ((993 / 790) : ℂ) * ζ ^ 13 + ((917 / 395) : ℂ) * ζ ^ 14 + ((533 / 790) : ℂ) * ζ ^ 15 + ((81 / 395) : ℂ) * ζ ^ 16 - ((501 / 395) : ℂ) * ζ ^ 17 - ((691 / 790) : ℂ) * ζ ^ 18 - ((6 / 395) : ℂ) * ζ ^ 19 + ((44 / 395) : ℂ) * ζ ^ 20 + ((349 / 395) : ℂ) * ζ ^ 21 - ((87 / 395) : ℂ) * ζ ^ 22 - ((547 / 790) : ℂ) * ζ ^ 23 - ((53 / 395) : ℂ) * ζ ^ 24 - ((3 / 79) : ℂ) * ζ ^ 25 - ((93 / 790) : ℂ) * ζ ^ 26 + ((297 / 395) : ℂ) * ζ ^ 27 + ((28 / 395) : ℂ) * ζ ^ 28 - ((38 / 395) : ℂ) * ζ ^ 29 - ((14 / 79) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep06Coefficient01 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity01 :
    row18_reducedY10_combinationStep06Coefficient01 =
      row18_reducedY10_combinationStep05Coefficient01 +
        row18_reducedY10_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep06Coefficient01 row18_reducedY10_combinationStep05Coefficient01 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep06Coefficient02 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY10_combinationStep06CoefficientIdentity02 :
    row18_reducedY10_combinationStep06Coefficient02 =
      row18_reducedY10_combinationStep05Coefficient02 +
        row18_reducedY10_combinationStep06Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep06Coefficient02 row18_reducedY10_combinationStep05Coefficient02 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 (-((99 / 395) : ℂ) + ((483 / 790) : ℂ) * ζ ^ 1 - ((21 / 158) : ℂ) * ζ ^ 2 - ((133 / 790) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 4 - ((72 / 395) : ℂ) * ζ ^ 5 - (2 : ℂ) * ζ ^ 6 + ((17 / 158) : ℂ) * ζ ^ 7 - ((1211 / 790) : ℂ) * ζ ^ 8 + ((341 / 790) : ℂ) * ζ ^ 9 + ((349 / 158) : ℂ) * ζ ^ 10 + ((27 / 158) : ℂ) * ζ ^ 11 + ((362 / 395) : ℂ) * ζ ^ 12 - ((419 / 395) : ℂ) * ζ ^ 13 - ((23 / 158) : ℂ) * ζ ^ 14 - ((534 / 395) : ℂ) * ζ ^ 15 - ((129 / 790) : ℂ) * ζ ^ 16 + ((131 / 395) : ℂ) * ζ ^ 17 + ((51 / 79) : ℂ) * ζ ^ 18 + ((367 / 790) : ℂ) * ζ ^ 19 - ((449 / 790) : ℂ) * ζ ^ 20 - ((1031 / 790) : ℂ) * ζ ^ 21 - ((120 / 79) : ℂ) * ζ ^ 22 - ((931 / 790) : ℂ) * ζ ^ 23 + ((41 / 79) : ℂ) * ζ ^ 24 + ((404 / 395) : ℂ) * ζ ^ 25 + ((93 / 158) : ℂ) * ζ ^ 26 + ((236 / 395) : ℂ) * ζ ^ 27 + ((159 / 395) : ℂ) * ζ ^ 28 + ((12 / 395) : ℂ) * ζ ^ 29 - ((84 / 79) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep06Coefficient03 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity03 :
    row18_reducedY10_combinationStep06Coefficient03 =
      row18_reducedY10_combinationStep05Coefficient03 +
        row18_reducedY10_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep06Coefficient03 row18_reducedY10_combinationStep05Coefficient03 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep06Coefficient04 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity04 :
    row18_reducedY10_combinationStep06Coefficient04 =
      row18_reducedY10_combinationStep05Coefficient04 +
        row18_reducedY10_combinationStep06Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep06Coefficient04 row18_reducedY10_combinationStep05Coefficient04 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 (-((355 / 158) : ℂ) - ((482 / 395) : ℂ) * ζ ^ 1 + ((6 / 79) : ℂ) * ζ ^ 2 - ((21 / 79) : ℂ) * ζ ^ 3 + ((216 / 79) : ℂ) * ζ ^ 4 + ((1531 / 790) : ℂ) * ζ ^ 5 - ((714 / 395) : ℂ) * ζ ^ 6 - ((196 / 395) : ℂ) * ζ ^ 7 - ((758 / 395) : ℂ) * ζ ^ 8 - ((7 / 395) : ℂ) * ζ ^ 9 + ((2063 / 790) : ℂ) * ζ ^ 10 + ((1153 / 790) : ℂ) * ζ ^ 11 + ((46 / 395) : ℂ) * ζ ^ 12 - ((993 / 790) : ℂ) * ζ ^ 13 - ((917 / 395) : ℂ) * ζ ^ 14 - ((533 / 790) : ℂ) * ζ ^ 15 - ((81 / 395) : ℂ) * ζ ^ 16 + ((501 / 395) : ℂ) * ζ ^ 17 + ((691 / 790) : ℂ) * ζ ^ 18 + ((6 / 395) : ℂ) * ζ ^ 19 - ((44 / 395) : ℂ) * ζ ^ 20 - ((349 / 395) : ℂ) * ζ ^ 21 + ((87 / 395) : ℂ) * ζ ^ 22 + ((547 / 790) : ℂ) * ζ ^ 23 + ((53 / 395) : ℂ) * ζ ^ 24 + ((3 / 79) : ℂ) * ζ ^ 25 + ((93 / 790) : ℂ) * ζ ^ 26 - ((297 / 395) : ℂ) * ζ ^ 27 - ((28 / 395) : ℂ) * ζ ^ 28 + ((38 / 395) : ℂ) * ζ ^ 29 + ((14 / 79) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep06Coefficient05 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity05 :
    row18_reducedY10_combinationStep06Coefficient05 =
      row18_reducedY10_combinationStep05Coefficient05 +
        row18_reducedY10_combinationStep06Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY10_combinationStep06Coefficient05 row18_reducedY10_combinationStep05Coefficient05 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 (-((801 / 790) : ℂ) - ((254 / 395) : ℂ) * ζ ^ 1 - ((91 / 790) : ℂ) * ζ ^ 2 + ((1309 / 790) : ℂ) * ζ ^ 3 + ((423 / 790) : ℂ) * ζ ^ 4 - ((51 / 158) : ℂ) * ζ ^ 5 - ((11 / 79) : ℂ) * ζ ^ 6 - ((382 / 395) : ℂ) * ζ ^ 7 + ((509 / 790) : ℂ) * ζ ^ 8 - ((1049 / 790) : ℂ) * ζ ^ 9 - ((119 / 790) : ℂ) * ζ ^ 10 - ((2411 / 790) : ℂ) * ζ ^ 11 - ((1049 / 790) : ℂ) * ζ ^ 12 + ((387 / 158) : ℂ) * ζ ^ 13 + ((3391 / 790) : ℂ) * ζ ^ 14 + ((657 / 790) : ℂ) * ζ ^ 15 - ((49 / 79) : ℂ) * ζ ^ 16 - ((2699 / 790) : ℂ) * ζ ^ 17 - ((567 / 790) : ℂ) * ζ ^ 18 + ((678 / 395) : ℂ) * ζ ^ 19 + ((601 / 395) : ℂ) * ζ ^ 20 + ((363 / 790) : ℂ) * ζ ^ 21 - ((1517 / 790) : ℂ) * ζ ^ 22 - ((1443 / 790) : ℂ) * ζ ^ 23 - ((271 / 158) : ℂ) * ζ ^ 24 - ((282 / 395) : ℂ) * ζ ^ 25 + ((5 / 79) : ℂ) * ζ ^ 26 + ((1209 / 395) : ℂ) * ζ ^ 27 + ((522 / 395) : ℂ) * ζ ^ 28 + ((54 / 79) : ℂ) * ζ ^ 29 - ((180 / 79) : ℂ) * ζ ^ 30)

private def row18_reducedY10_combinationStep06Coefficient06 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity06 :
    row18_reducedY10_combinationStep06Coefficient06 =
      row18_reducedY10_combinationStep05Coefficient06 +
        row18_reducedY10_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep06Coefficient06 row18_reducedY10_combinationStep05Coefficient06 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep06Coefficient07 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity07 :
    row18_reducedY10_combinationStep06Coefficient07 =
      row18_reducedY10_combinationStep05Coefficient07 +
        row18_reducedY10_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep06Coefficient07 row18_reducedY10_combinationStep05Coefficient07 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep06Coefficient08 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity08 :
    row18_reducedY10_combinationStep06Coefficient08 =
      row18_reducedY10_combinationStep05Coefficient08 +
        row18_reducedY10_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep06Coefficient08 row18_reducedY10_combinationStep05Coefficient08 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep06Coefficient09 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity09 :
    row18_reducedY10_combinationStep06Coefficient09 =
      row18_reducedY10_combinationStep05Coefficient09 +
        row18_reducedY10_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep06Coefficient09 row18_reducedY10_combinationStep05Coefficient09 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep06Coefficient10 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity10 :
    row18_reducedY10_combinationStep06Coefficient10 =
      row18_reducedY10_combinationStep05Coefficient10 +
        row18_reducedY10_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep06Coefficient10 row18_reducedY10_combinationStep05Coefficient10 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep06Coefficient11 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity11 :
    row18_reducedY10_combinationStep06Coefficient11 =
      row18_reducedY10_combinationStep05Coefficient11 +
        row18_reducedY10_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep06Coefficient11 row18_reducedY10_combinationStep05Coefficient11 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep06Coefficient12 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity12 :
    row18_reducedY10_combinationStep06Coefficient12 =
      row18_reducedY10_combinationStep05Coefficient12 +
        row18_reducedY10_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep06Coefficient12 row18_reducedY10_combinationStep05Coefficient12 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep06Coefficient13 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity13 :
    row18_reducedY10_combinationStep06Coefficient13 =
      row18_reducedY10_combinationStep05Coefficient13 +
        row18_reducedY10_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep06Coefficient13 row18_reducedY10_combinationStep05Coefficient13 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep06Coefficient14 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity14 :
    row18_reducedY10_combinationStep06Coefficient14 =
      row18_reducedY10_combinationStep05Coefficient14 +
        row18_reducedY10_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep06Coefficient14 row18_reducedY10_combinationStep05Coefficient14 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY10_combinationStep06Coefficient15 : ℂ :=
  0

private theorem row18_reducedY10_combinationStep06CoefficientIdentity15 :
    row18_reducedY10_combinationStep06Coefficient15 =
      row18_reducedY10_combinationStep05Coefficient15 +
        row18_reducedY10_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY10_combinationStep06Coefficient15 row18_reducedY10_combinationStep05Coefficient15 row18_reducedY10_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY10_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY10_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY10_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY10_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY10_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY10_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY10_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY10_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY10_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY10_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY10_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY10_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY10_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY10_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY10_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY10_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY10_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY10_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY10_combinationStep06CoefficientIdentity00,
      row18_reducedY10_combinationStep06CoefficientIdentity01,
      row18_reducedY10_combinationStep06CoefficientIdentity02,
      row18_reducedY10_combinationStep06CoefficientIdentity03,
      row18_reducedY10_combinationStep06CoefficientIdentity04,
      row18_reducedY10_combinationStep06CoefficientIdentity05,
      row18_reducedY10_combinationStep06CoefficientIdentity06,
      row18_reducedY10_combinationStep06CoefficientIdentity07,
      row18_reducedY10_combinationStep06CoefficientIdentity08,
      row18_reducedY10_combinationStep06CoefficientIdentity09,
      row18_reducedY10_combinationStep06CoefficientIdentity10,
      row18_reducedY10_combinationStep06CoefficientIdentity11,
      row18_reducedY10_combinationStep06CoefficientIdentity12,
      row18_reducedY10_combinationStep06CoefficientIdentity13,
      row18_reducedY10_combinationStep06CoefficientIdentity14,
      row18_reducedY10_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY10_combinationStep06Multiplier * equation

theorem row18_reducedY10
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 1 0 = 0 := by
  have reduced :=
    row18_reducedY10_combinationStep06 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY10_combinationStep06Coefficient00,
      row18_reducedY10_combinationStep06Coefficient01,
      row18_reducedY10_combinationStep06Coefficient02,
      row18_reducedY10_combinationStep06Coefficient03,
      row18_reducedY10_combinationStep06Coefficient04,
      row18_reducedY10_combinationStep06Coefficient05,
      row18_reducedY10_combinationStep06Coefficient06,
      row18_reducedY10_combinationStep06Coefficient07,
      row18_reducedY10_combinationStep06Coefficient08,
      row18_reducedY10_combinationStep06Coefficient09,
      row18_reducedY10_combinationStep06Coefficient10,
      row18_reducedY10_combinationStep06Coefficient11,
      row18_reducedY10_combinationStep06Coefficient12,
      row18_reducedY10_combinationStep06Coefficient13,
      row18_reducedY10_combinationStep06Coefficient14,
      row18_reducedY10_combinationStep06Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
