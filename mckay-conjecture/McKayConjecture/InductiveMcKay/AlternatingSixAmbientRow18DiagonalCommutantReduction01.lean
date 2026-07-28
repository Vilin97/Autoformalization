/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction00

/-!
# Ambient row 18 commutant reduction 01

This generated module checks the reduced relation `reducedY01` for
matrix coordinate (0, 1).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY01_combinationStep00Multiplier : ℂ :=
  (-((2846 / 1185) : ℂ) - ((244 / 237) : ℂ) * ζ ^ 1 - ((10082 / 1185) : ℂ) * ζ ^ 2 - ((6146 / 1185) : ℂ) * ζ ^ 3 - ((13648 / 1185) : ℂ) * ζ ^ 6 - ((6332 / 1185) : ℂ) * ζ ^ 8 - ((1844 / 237) : ℂ) * ζ ^ 9 - ((214 / 395) : ℂ) * ζ ^ 11 - ((3566 / 1185) : ℂ) * ζ ^ 12 + ((244 / 237) : ℂ) * ζ ^ 13 - ((6146 / 1185) : ℂ) * ζ ^ 15 + ((244 / 237) : ℂ) * ζ ^ 17 + ((2412 / 395) : ℂ) * ζ ^ 18 + ((244 / 237) : ℂ) * ζ ^ 21 + ((10082 / 1185) : ℂ) * ζ ^ 22 - ((10082 / 1185) : ℂ) * ζ ^ 24 - ((244 / 237) : ℂ) * ζ ^ 25 - ((214 / 395) : ℂ) * ζ ^ 27 + ((6332 / 1185) : ℂ) * ζ ^ 28 - ((244 / 237) : ℂ) * ζ ^ 29 - ((16414 / 1185) : ℂ) * ζ ^ 30 + ((214 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY01_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep00CoefficientIdentity00 :
    row18_reducedY01_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep00Coefficient00 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep00Coefficient01 : ℂ :=
  (((108481 / 18723) : ℂ) + ((14273 / 18723) : ℂ) * ζ ^ 1 - ((16202 / 18723) : ℂ) * ζ ^ 2 - ((123611 / 37446) : ℂ) * ζ ^ 3 + ((51043 / 37446) : ℂ) * ζ ^ 5 + ((1313 / 6241) : ℂ) * ζ ^ 6 - ((30135 / 12482) : ℂ) * ζ ^ 8 - ((11507 / 6241) : ℂ) * ζ ^ 9 + ((54569 / 37446) : ℂ) * ζ ^ 11 - ((30135 / 12482) : ℂ) * ζ ^ 12 - ((14273 / 18723) : ℂ) * ζ ^ 13 + ((73054 / 18723) : ℂ) * ζ ^ 15 - ((14273 / 18723) : ℂ) * ζ ^ 17 - ((20141 / 18723) : ℂ) * ζ ^ 18 + ((95065 / 37446) : ℂ) * ζ ^ 21 + ((16202 / 18723) : ℂ) * ζ ^ 22 - ((7499 / 12482) : ℂ) * ζ ^ 25 - ((95065 / 37446) : ℂ) * ζ ^ 27 + ((30135 / 12482) : ℂ) * ζ ^ 28 + ((14273 / 18723) : ℂ) * ζ ^ 29 + ((1313 / 12482) : ℂ) * ζ ^ 30 - ((54569 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep00CoefficientIdentity01 :
    row18_reducedY01_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep00Coefficient01 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 (-((602171 / 93615) : ℂ) - ((206777 / 187230) : ℂ) * ζ ^ 1 - ((54921 / 31205) : ℂ) * ζ ^ 2 + ((143857 / 93615) : ℂ) * ζ ^ 3 + ((954881 / 187230) : ℂ) * ζ ^ 4 - ((15385 / 37446) : ℂ) * ζ ^ 5 - ((18041 / 18723) : ℂ) * ζ ^ 6 + ((10669 / 37446) : ℂ) * ζ ^ 7 - ((580021 / 187230) : ℂ) * ζ ^ 8 + ((130223 / 93615) : ℂ) * ζ ^ 9 + ((123503 / 93615) : ℂ) * ζ ^ 10 + ((360037 / 187230) : ℂ) * ζ ^ 11 + ((2941 / 2370) : ℂ) * ζ ^ 12 - ((71017 / 37446) : ℂ) * ζ ^ 13 + ((230129 / 187230) : ℂ) * ζ ^ 14 - ((194843 / 187230) : ℂ) * ζ ^ 15 - ((25163 / 12482) : ℂ) * ζ ^ 16 - ((27157 / 37446) : ℂ) * ζ ^ 17 + ((199127 / 93615) : ℂ) * ζ ^ 18 + ((162277 / 62410) : ℂ) * ζ ^ 19 + ((55103 / 187230) : ℂ) * ζ ^ 20 - ((249143 / 187230) : ℂ) * ζ ^ 21 - ((211813 / 93615) : ℂ) * ζ ^ 22 - ((50801 / 31205) : ℂ) * ζ ^ 23 + ((83155 / 37446) : ℂ) * ζ ^ 24 + ((8736 / 31205) : ℂ) * ζ ^ 25 - ((114514 / 93615) : ℂ) * ζ ^ 26 - ((292781 / 187230) : ℂ) * ζ ^ 27 - ((17722 / 18723) : ℂ) * ζ ^ 28 + ((566743 / 187230) : ℂ) * ζ ^ 29 - ((3638 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep00Coefficient02 : ℂ :=
  (-((7088 / 6241) : ℂ) - ((154105 / 37446) : ℂ) * ζ ^ 1 + ((154105 / 37446) : ℂ) * ζ ^ 3 - ((36669 / 12482) : ℂ) * ζ ^ 5 - ((68648 / 18723) : ℂ) * ζ ^ 6 + ((3544 / 6241) : ℂ) * ζ ^ 8 + ((11976 / 6241) : ℂ) * ζ ^ 9 - ((22049 / 18723) : ℂ) * ζ ^ 11 + ((4111 / 6241) : ℂ) * ζ ^ 12 + ((154105 / 37446) : ℂ) * ζ ^ 13 - ((44030 / 18723) : ℂ) * ζ ^ 15 + ((154105 / 37446) : ℂ) * ζ ^ 17 + ((28469 / 6241) : ℂ) * ζ ^ 18 + ((22015 / 12482) : ℂ) * ζ ^ 21 - ((2977 / 6241) : ℂ) * ζ ^ 24 - ((22049 / 18723) : ℂ) * ζ ^ 25 + ((11976 / 6241) : ℂ) * ζ ^ 27 - ((3544 / 6241) : ℂ) * ζ ^ 28 - ((154105 / 37446) : ℂ) * ζ ^ 29 - ((68648 / 18723) : ℂ) * ζ ^ 30 + ((22049 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep00CoefficientIdentity02 :
    row18_reducedY01_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep00Coefficient02 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 (((47977 / 93615) : ℂ) + ((117001 / 31205) : ℂ) * ζ ^ 1 - ((78279 / 31205) : ℂ) * ζ ^ 2 - ((537316 / 93615) : ℂ) * ζ ^ 3 - ((292657 / 187230) : ℂ) * ζ ^ 4 - ((135469 / 187230) : ℂ) * ζ ^ 5 + ((130937 / 37446) : ℂ) * ζ ^ 6 + ((97921 / 18723) : ℂ) * ζ ^ 7 - ((91313 / 62410) : ℂ) * ζ ^ 8 - ((185252 / 93615) : ℂ) * ζ ^ 9 - ((234809 / 93615) : ℂ) * ζ ^ 10 - ((163328 / 93615) : ℂ) * ζ ^ 11 + ((382741 / 187230) : ℂ) * ζ ^ 12 + ((137413 / 93615) : ℂ) * ζ ^ 13 + ((207086 / 93615) : ℂ) * ζ ^ 14 + ((12850 / 18723) : ℂ) * ζ ^ 15 - ((193159 / 93615) : ℂ) * ζ ^ 16 + ((527 / 6241) : ℂ) * ζ ^ 17 - ((106508 / 93615) : ℂ) * ζ ^ 18 - ((26191 / 93615) : ℂ) * ζ ^ 19 - ((20893 / 93615) : ℂ) * ζ ^ 20 + ((28037 / 93615) : ℂ) * ζ ^ 21 + ((207994 / 93615) : ℂ) * ζ ^ 22 + ((47449 / 62410) : ℂ) * ζ ^ 23 - ((20893 / 93615) : ℂ) * ζ ^ 24 - ((37488 / 31205) : ℂ) * ζ ^ 25 - ((96599 / 31205) : ℂ) * ζ ^ 26 - ((11813 / 18723) : ℂ) * ζ ^ 27 + ((39152 / 31205) : ℂ) * ζ ^ 28 + ((19073 / 31205) : ℂ) * ζ ^ 29 - ((321 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep00CoefficientIdentity03 :
    row18_reducedY01_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep00Coefficient03 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep00CoefficientIdentity04 :
    row18_reducedY01_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep00Coefficient04 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep00CoefficientIdentity05 :
    row18_reducedY01_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep00Coefficient05 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep00CoefficientIdentity06 :
    row18_reducedY01_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep00Coefficient06 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep00CoefficientIdentity07 :
    row18_reducedY01_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep00Coefficient07 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep00CoefficientIdentity08 :
    row18_reducedY01_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep00Coefficient08 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep00CoefficientIdentity09 :
    row18_reducedY01_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep00Coefficient09 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep00CoefficientIdentity10 :
    row18_reducedY01_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep00Coefficient10 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep00CoefficientIdentity11 :
    row18_reducedY01_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep00Coefficient11 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep00CoefficientIdentity12 :
    row18_reducedY01_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep00Coefficient12 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep00CoefficientIdentity13 :
    row18_reducedY01_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep00Coefficient13 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep00CoefficientIdentity14 :
    row18_reducedY01_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep00Coefficient14 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep00CoefficientIdentity15 :
    row18_reducedY01_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY01_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep00Coefficient15 row18_reducedY01_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY01_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY01_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY01_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY01_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY01_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY01_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY01_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY01_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY01_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY01_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY01_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY01_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY01_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY01_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY01_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY01_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY01_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY01_combinationStep00CoefficientIdentity00,
      row18_reducedY01_combinationStep00CoefficientIdentity01,
      row18_reducedY01_combinationStep00CoefficientIdentity02,
      row18_reducedY01_combinationStep00CoefficientIdentity03,
      row18_reducedY01_combinationStep00CoefficientIdentity04,
      row18_reducedY01_combinationStep00CoefficientIdentity05,
      row18_reducedY01_combinationStep00CoefficientIdentity06,
      row18_reducedY01_combinationStep00CoefficientIdentity07,
      row18_reducedY01_combinationStep00CoefficientIdentity08,
      row18_reducedY01_combinationStep00CoefficientIdentity09,
      row18_reducedY01_combinationStep00CoefficientIdentity10,
      row18_reducedY01_combinationStep00CoefficientIdentity11,
      row18_reducedY01_combinationStep00CoefficientIdentity12,
      row18_reducedY01_combinationStep00CoefficientIdentity13,
      row18_reducedY01_combinationStep00CoefficientIdentity14,
      row18_reducedY01_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY01_combinationStep00Multiplier * equation

private def row18_reducedY01_combinationStep01Multiplier : ℂ :=
  (((358 / 1185) : ℂ) + ((2942 / 1185) : ℂ) * ζ ^ 1 + ((1058 / 237) : ℂ) * ζ ^ 2 - ((614 / 395) : ℂ) * ζ ^ 3 + ((92 / 395) : ℂ) * ζ ^ 5 + ((2216 / 1185) : ℂ) * ζ ^ 8 + ((3326 / 1185) : ℂ) * ζ ^ 9 - ((1484 / 1185) : ℂ) * ζ ^ 11 - ((2932 / 1185) : ℂ) * ζ ^ 12 - ((2942 / 1185) : ℂ) * ζ ^ 13 + ((4508 / 1185) : ℂ) * ζ ^ 15 - ((2942 / 1185) : ℂ) * ζ ^ 17 - ((1058 / 237) : ℂ) * ζ ^ 18 - ((4784 / 1185) : ℂ) * ζ ^ 21 - ((1058 / 237) : ℂ) * ζ ^ 22 + ((716 / 1185) : ℂ) * ζ ^ 24 + ((2666 / 1185) : ℂ) * ζ ^ 25 - ((4784 / 1185) : ℂ) * ζ ^ 27 - ((2216 / 1185) : ℂ) * ζ ^ 28 + ((2942 / 1185) : ℂ) * ζ ^ 29 + ((1550 / 237) : ℂ) * ζ ^ 30 + ((1484 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY01_combinationStep01Coefficient00 : ℂ :=
  (-((100129 / 37446) : ℂ) - ((9087 / 6241) : ℂ) * ζ ^ 1 - ((4003 / 18723) : ℂ) * ζ ^ 2 + ((130387 / 37446) : ℂ) * ζ ^ 3 - ((15619 / 18723) : ℂ) * ζ ^ 5 - ((8984 / 6241) : ℂ) * ζ ^ 6 + ((63127 / 37446) : ℂ) * ζ ^ 8 + ((38903 / 37446) : ℂ) * ζ ^ 9 - ((17183 / 12482) : ℂ) * ζ ^ 11 + ((22949 / 18723) : ℂ) * ζ ^ 12 + ((9087 / 6241) : ℂ) * ζ ^ 13 - ((130387 / 37446) : ℂ) * ζ ^ 15 + ((9087 / 6241) : ℂ) * ζ ^ 17 + ((36045 / 12482) : ℂ) * ζ ^ 18 - ((11642 / 18723) : ℂ) * ζ ^ 21 + ((4003 / 18723) : ℂ) * ζ ^ 22 + ((4003 / 18723) : ℂ) * ζ ^ 24 - ((11642 / 18723) : ℂ) * ζ ^ 25 + ((17183 / 12482) : ℂ) * ζ ^ 27 - ((63127 / 37446) : ℂ) * ζ ^ 28 - ((9087 / 6241) : ℂ) * ζ ^ 29 - ((23711 / 12482) : ℂ) * ζ ^ 30 + ((17183 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep01CoefficientIdentity00 :
    row18_reducedY01_combinationStep01Coefficient00 =
      row18_reducedY01_combinationStep00Coefficient00 +
        row18_reducedY01_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep01Coefficient00 row18_reducedY01_combinationStep00Coefficient00 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 (((161989 / 62410) : ℂ) + ((49887 / 62410) : ℂ) * ζ ^ 1 - ((202069 / 187230) : ℂ) * ζ ^ 2 - ((328258 / 93615) : ℂ) * ζ ^ 3 - ((52862 / 18723) : ℂ) * ζ ^ 4 + ((90007 / 187230) : ℂ) * ζ ^ 5 + ((74287 / 31205) : ℂ) * ζ ^ 6 + ((211881 / 62410) : ℂ) * ζ ^ 7 + ((7151 / 12482) : ℂ) * ζ ^ 8 - ((161092 / 93615) : ℂ) * ζ ^ 9 - ((117407 / 93615) : ℂ) * ζ ^ 10 - ((105829 / 93615) : ℂ) * ζ ^ 11 + ((23288 / 18723) : ℂ) * ζ ^ 12 + ((184523 / 93615) : ℂ) * ζ ^ 13 + ((58567 / 62410) : ℂ) * ζ ^ 14 + ((18142 / 93615) : ℂ) * ζ ^ 15 - ((25129 / 18723) : ℂ) * ζ ^ 16 - ((48712 / 93615) : ℂ) * ζ ^ 17 - ((3547 / 12482) : ℂ) * ζ ^ 18 - ((27341 / 93615) : ℂ) * ζ ^ 19 + ((45556 / 93615) : ℂ) * ζ ^ 20 + ((140171 / 187230) : ℂ) * ζ ^ 21 + ((110449 / 93615) : ℂ) * ζ ^ 22 + ((20083 / 18723) : ℂ) * ζ ^ 23 - ((15038 / 93615) : ℂ) * ζ ^ 24 - ((18413 / 12482) : ℂ) * ζ ^ 25 - ((57259 / 31205) : ℂ) * ζ ^ 26 - ((2418 / 6241) : ℂ) * ζ ^ 27 + ((58522 / 93615) : ℂ) * ζ ^ 28 + ((26053 / 62410) : ℂ) * ζ ^ 29 + ((371 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep01Coefficient01 : ℂ :=
  (((111376 / 18723) : ℂ) + ((37472 / 18723) : ℂ) * ζ ^ 1 - ((223 / 37446) : ℂ) * ζ ^ 2 - ((69374 / 18723) : ℂ) * ζ ^ 3 + ((104113 / 37446) : ℂ) * ζ ^ 5 + ((16146 / 6241) : ℂ) * ζ ^ 6 - ((98879 / 37446) : ℂ) * ζ ^ 8 - ((35710 / 18723) : ℂ) * ζ ^ 9 + ((33664 / 18723) : ℂ) * ζ ^ 11 - ((98879 / 37446) : ℂ) * ζ ^ 12 - ((37472 / 18723) : ℂ) * ζ ^ 13 + ((167917 / 37446) : ℂ) * ζ ^ 15 - ((37472 / 18723) : ℂ) * ζ ^ 17 - ((97099 / 37446) : ℂ) * ζ ^ 18 + ((10634 / 6241) : ℂ) * ζ ^ 21 + ((223 / 37446) : ℂ) * ζ ^ 22 - ((9723 / 12482) : ℂ) * ζ ^ 25 - ((10634 / 6241) : ℂ) * ζ ^ 27 + ((98879 / 37446) : ℂ) * ζ ^ 28 + ((37472 / 18723) : ℂ) * ζ ^ 29 + ((8073 / 6241) : ℂ) * ζ ^ 30 - ((33664 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep01CoefficientIdentity01 :
    row18_reducedY01_combinationStep01Coefficient01 =
      row18_reducedY01_combinationStep00Coefficient01 +
        row18_reducedY01_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep01Coefficient01 row18_reducedY01_combinationStep00Coefficient01 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 (-((17339 / 93615) : ℂ) - ((28300 / 18723) : ℂ) * ζ ^ 1 - ((10260 / 6241) : ℂ) * ζ ^ 2 - ((179 / 158) : ℂ) * ζ ^ 3 - ((16570 / 6241) : ℂ) * ζ ^ 4 - ((12266 / 93615) : ℂ) * ζ ^ 5 - ((15253 / 187230) : ℂ) * ζ ^ 6 + ((289579 / 187230) : ℂ) * ζ ^ 7 + ((230407 / 93615) : ℂ) * ζ ^ 8 - ((5081 / 187230) : ℂ) * ζ ^ 9 - ((8936 / 93615) : ℂ) * ζ ^ 10 - ((43408 / 18723) : ℂ) * ζ ^ 11 - ((320677 / 93615) : ℂ) * ζ ^ 12 + ((207439 / 187230) : ℂ) * ζ ^ 13 + ((158002 / 93615) : ℂ) * ζ ^ 14 + ((204691 / 93615) : ℂ) * ζ ^ 15 + ((76676 / 93615) : ℂ) * ζ ^ 16 - ((241583 / 93615) : ℂ) * ζ ^ 17 - ((80051 / 62410) : ℂ) * ζ ^ 18 + ((39308 / 31205) : ℂ) * ζ ^ 19 + ((251311 / 62410) : ℂ) * ζ ^ 20 + ((25379 / 12482) : ℂ) * ζ ^ 21 + ((1157 / 93615) : ℂ) * ζ ^ 22 - ((6067 / 18723) : ℂ) * ζ ^ 23 - ((45701 / 62410) : ℂ) * ζ ^ 24 - ((382367 / 187230) : ℂ) * ζ ^ 25 - ((116266 / 93615) : ℂ) * ζ ^ 26 - ((14979 / 31205) : ℂ) * ζ ^ 27 + ((19644 / 31205) : ℂ) * ζ ^ 28 + ((63154 / 93615) : ℂ) * ζ ^ 29 + ((10388 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep01Coefficient02 : ℂ :=
  (-((7088 / 6241) : ℂ) - ((154105 / 37446) : ℂ) * ζ ^ 1 + ((154105 / 37446) : ℂ) * ζ ^ 3 - ((36669 / 12482) : ℂ) * ζ ^ 5 - ((68648 / 18723) : ℂ) * ζ ^ 6 + ((3544 / 6241) : ℂ) * ζ ^ 8 + ((11976 / 6241) : ℂ) * ζ ^ 9 - ((22049 / 18723) : ℂ) * ζ ^ 11 + ((4111 / 6241) : ℂ) * ζ ^ 12 + ((154105 / 37446) : ℂ) * ζ ^ 13 - ((44030 / 18723) : ℂ) * ζ ^ 15 + ((154105 / 37446) : ℂ) * ζ ^ 17 + ((28469 / 6241) : ℂ) * ζ ^ 18 + ((22015 / 12482) : ℂ) * ζ ^ 21 - ((2977 / 6241) : ℂ) * ζ ^ 24 - ((22049 / 18723) : ℂ) * ζ ^ 25 + ((11976 / 6241) : ℂ) * ζ ^ 27 - ((3544 / 6241) : ℂ) * ζ ^ 28 - ((154105 / 37446) : ℂ) * ζ ^ 29 - ((68648 / 18723) : ℂ) * ζ ^ 30 + ((22049 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep01CoefficientIdentity02 :
    row18_reducedY01_combinationStep01Coefficient02 =
      row18_reducedY01_combinationStep00Coefficient02 +
        row18_reducedY01_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep01Coefficient02 row18_reducedY01_combinationStep00Coefficient02 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep01Coefficient03 : ℂ :=
  (((100129 / 37446) : ℂ) + ((9087 / 6241) : ℂ) * ζ ^ 1 + ((4003 / 18723) : ℂ) * ζ ^ 2 - ((130387 / 37446) : ℂ) * ζ ^ 3 + ((15619 / 18723) : ℂ) * ζ ^ 5 + ((8984 / 6241) : ℂ) * ζ ^ 6 - ((63127 / 37446) : ℂ) * ζ ^ 8 - ((38903 / 37446) : ℂ) * ζ ^ 9 + ((17183 / 12482) : ℂ) * ζ ^ 11 - ((22949 / 18723) : ℂ) * ζ ^ 12 - ((9087 / 6241) : ℂ) * ζ ^ 13 + ((130387 / 37446) : ℂ) * ζ ^ 15 - ((9087 / 6241) : ℂ) * ζ ^ 17 - ((36045 / 12482) : ℂ) * ζ ^ 18 + ((11642 / 18723) : ℂ) * ζ ^ 21 - ((4003 / 18723) : ℂ) * ζ ^ 22 - ((4003 / 18723) : ℂ) * ζ ^ 24 + ((11642 / 18723) : ℂ) * ζ ^ 25 - ((17183 / 12482) : ℂ) * ζ ^ 27 + ((63127 / 37446) : ℂ) * ζ ^ 28 + ((9087 / 6241) : ℂ) * ζ ^ 29 + ((23711 / 12482) : ℂ) * ζ ^ 30 - ((17183 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep01CoefficientIdentity03 :
    row18_reducedY01_combinationStep01Coefficient03 =
      row18_reducedY01_combinationStep00Coefficient03 +
        row18_reducedY01_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep01Coefficient03 row18_reducedY01_combinationStep00Coefficient03 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 (-((161989 / 62410) : ℂ) - ((49887 / 62410) : ℂ) * ζ ^ 1 + ((202069 / 187230) : ℂ) * ζ ^ 2 + ((328258 / 93615) : ℂ) * ζ ^ 3 + ((52862 / 18723) : ℂ) * ζ ^ 4 - ((90007 / 187230) : ℂ) * ζ ^ 5 - ((74287 / 31205) : ℂ) * ζ ^ 6 - ((211881 / 62410) : ℂ) * ζ ^ 7 - ((7151 / 12482) : ℂ) * ζ ^ 8 + ((161092 / 93615) : ℂ) * ζ ^ 9 + ((117407 / 93615) : ℂ) * ζ ^ 10 + ((105829 / 93615) : ℂ) * ζ ^ 11 - ((23288 / 18723) : ℂ) * ζ ^ 12 - ((184523 / 93615) : ℂ) * ζ ^ 13 - ((58567 / 62410) : ℂ) * ζ ^ 14 - ((18142 / 93615) : ℂ) * ζ ^ 15 + ((25129 / 18723) : ℂ) * ζ ^ 16 + ((48712 / 93615) : ℂ) * ζ ^ 17 + ((3547 / 12482) : ℂ) * ζ ^ 18 + ((27341 / 93615) : ℂ) * ζ ^ 19 - ((45556 / 93615) : ℂ) * ζ ^ 20 - ((140171 / 187230) : ℂ) * ζ ^ 21 - ((110449 / 93615) : ℂ) * ζ ^ 22 - ((20083 / 18723) : ℂ) * ζ ^ 23 + ((15038 / 93615) : ℂ) * ζ ^ 24 + ((18413 / 12482) : ℂ) * ζ ^ 25 + ((57259 / 31205) : ℂ) * ζ ^ 26 + ((2418 / 6241) : ℂ) * ζ ^ 27 - ((58522 / 93615) : ℂ) * ζ ^ 28 - ((26053 / 62410) : ℂ) * ζ ^ 29 - ((371 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep01CoefficientIdentity04 :
    row18_reducedY01_combinationStep01Coefficient04 =
      row18_reducedY01_combinationStep00Coefficient04 +
        row18_reducedY01_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep01Coefficient04 row18_reducedY01_combinationStep00Coefficient04 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep01CoefficientIdentity05 :
    row18_reducedY01_combinationStep01Coefficient05 =
      row18_reducedY01_combinationStep00Coefficient05 +
        row18_reducedY01_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep01Coefficient05 row18_reducedY01_combinationStep00Coefficient05 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep01CoefficientIdentity06 :
    row18_reducedY01_combinationStep01Coefficient06 =
      row18_reducedY01_combinationStep00Coefficient06 +
        row18_reducedY01_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep01Coefficient06 row18_reducedY01_combinationStep00Coefficient06 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep01CoefficientIdentity07 :
    row18_reducedY01_combinationStep01Coefficient07 =
      row18_reducedY01_combinationStep00Coefficient07 +
        row18_reducedY01_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep01Coefficient07 row18_reducedY01_combinationStep00Coefficient07 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep01CoefficientIdentity08 :
    row18_reducedY01_combinationStep01Coefficient08 =
      row18_reducedY01_combinationStep00Coefficient08 +
        row18_reducedY01_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep01Coefficient08 row18_reducedY01_combinationStep00Coefficient08 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep01CoefficientIdentity09 :
    row18_reducedY01_combinationStep01Coefficient09 =
      row18_reducedY01_combinationStep00Coefficient09 +
        row18_reducedY01_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep01Coefficient09 row18_reducedY01_combinationStep00Coefficient09 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep01CoefficientIdentity10 :
    row18_reducedY01_combinationStep01Coefficient10 =
      row18_reducedY01_combinationStep00Coefficient10 +
        row18_reducedY01_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep01Coefficient10 row18_reducedY01_combinationStep00Coefficient10 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep01CoefficientIdentity11 :
    row18_reducedY01_combinationStep01Coefficient11 =
      row18_reducedY01_combinationStep00Coefficient11 +
        row18_reducedY01_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep01Coefficient11 row18_reducedY01_combinationStep00Coefficient11 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep01CoefficientIdentity12 :
    row18_reducedY01_combinationStep01Coefficient12 =
      row18_reducedY01_combinationStep00Coefficient12 +
        row18_reducedY01_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep01Coefficient12 row18_reducedY01_combinationStep00Coefficient12 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep01CoefficientIdentity13 :
    row18_reducedY01_combinationStep01Coefficient13 =
      row18_reducedY01_combinationStep00Coefficient13 +
        row18_reducedY01_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep01Coefficient13 row18_reducedY01_combinationStep00Coefficient13 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep01CoefficientIdentity14 :
    row18_reducedY01_combinationStep01Coefficient14 =
      row18_reducedY01_combinationStep00Coefficient14 +
        row18_reducedY01_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep01Coefficient14 row18_reducedY01_combinationStep00Coefficient14 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep01CoefficientIdentity15 :
    row18_reducedY01_combinationStep01Coefficient15 =
      row18_reducedY01_combinationStep00Coefficient15 +
        row18_reducedY01_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep01Coefficient15 row18_reducedY01_combinationStep00Coefficient15 row18_reducedY01_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY01_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY01_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY01_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY01_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY01_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY01_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY01_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY01_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY01_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY01_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY01_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY01_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY01_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY01_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY01_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY01_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY01_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY01_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY01_combinationStep01CoefficientIdentity00,
      row18_reducedY01_combinationStep01CoefficientIdentity01,
      row18_reducedY01_combinationStep01CoefficientIdentity02,
      row18_reducedY01_combinationStep01CoefficientIdentity03,
      row18_reducedY01_combinationStep01CoefficientIdentity04,
      row18_reducedY01_combinationStep01CoefficientIdentity05,
      row18_reducedY01_combinationStep01CoefficientIdentity06,
      row18_reducedY01_combinationStep01CoefficientIdentity07,
      row18_reducedY01_combinationStep01CoefficientIdentity08,
      row18_reducedY01_combinationStep01CoefficientIdentity09,
      row18_reducedY01_combinationStep01CoefficientIdentity10,
      row18_reducedY01_combinationStep01CoefficientIdentity11,
      row18_reducedY01_combinationStep01CoefficientIdentity12,
      row18_reducedY01_combinationStep01CoefficientIdentity13,
      row18_reducedY01_combinationStep01CoefficientIdentity14,
      row18_reducedY01_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY01_combinationStep01Multiplier * equation

private def row18_reducedY01_combinationStep02Multiplier : ℂ :=
  (((301572 / 31205) : ℂ) + ((307504 / 31205) : ℂ) * ζ ^ 1 - ((104594 / 31205) : ℂ) * ζ ^ 2 - ((114664 / 18723) : ℂ) * ζ ^ 3 + ((629216 / 93615) : ℂ) * ζ ^ 5 + ((478342 / 93615) : ℂ) * ζ ^ 6 - ((173976 / 31205) : ℂ) * ζ ^ 8 - ((607904 / 93615) : ℂ) * ζ ^ 9 + ((10500 / 6241) : ℂ) * ζ ^ 11 - ((792124 / 93615) : ℂ) * ζ ^ 12 - ((307504 / 31205) : ℂ) * ζ ^ 13 + ((114664 / 18723) : ℂ) * ζ ^ 15 - ((307504 / 31205) : ℂ) * ζ ^ 17 - ((196978 / 31205) : ℂ) * ζ ^ 18 + ((293296 / 93615) : ℂ) * ζ ^ 21 + ((104594 / 31205) : ℂ) * ζ ^ 22 + ((104594 / 31205) : ℂ) * ζ ^ 24 + ((293296 / 93615) : ℂ) * ζ ^ 25 - ((10500 / 6241) : ℂ) * ζ ^ 27 + ((173976 / 31205) : ℂ) * ζ ^ 28 + ((307504 / 31205) : ℂ) * ζ ^ 29 + ((69382 / 31205) : ℂ) * ζ ^ 30 - ((10500 / 6241) : ℂ) * ζ ^ 31)

private def row18_reducedY01_combinationStep02Coefficient00 : ℂ :=
  (-((325463 / 187230) : ℂ) - ((277337 / 187230) : ℂ) * ζ ^ 1 + ((81248 / 93615) : ℂ) * ζ ^ 2 + ((16091 / 37446) : ℂ) * ζ ^ 3 - ((48383 / 93615) : ℂ) * ζ ^ 5 - ((19756 / 31205) : ℂ) * ζ ^ 6 + ((194719 / 187230) : ℂ) * ζ ^ 8 + ((38159 / 31205) : ℂ) * ζ ^ 9 + ((3113 / 18723) : ℂ) * ζ ^ 11 + ((140516 / 93615) : ℂ) * ζ ^ 12 + ((277337 / 187230) : ℂ) * ζ ^ 13 - ((16091 / 37446) : ℂ) * ζ ^ 15 + ((277337 / 187230) : ℂ) * ζ ^ 17 + ((162967 / 187230) : ℂ) * ζ ^ 18 - ((180571 / 187230) : ℂ) * ζ ^ 21 - ((81248 / 93615) : ℂ) * ζ ^ 22 - ((81248 / 93615) : ℂ) * ζ ^ 24 - ((180571 / 187230) : ℂ) * ζ ^ 25 - ((3113 / 18723) : ℂ) * ζ ^ 27 - ((194719 / 187230) : ℂ) * ζ ^ 28 - ((277337 / 187230) : ℂ) * ζ ^ 29 - ((10741 / 62410) : ℂ) * ζ ^ 30 - ((3113 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep02CoefficientIdentity00 :
    row18_reducedY01_combinationStep02Coefficient00 =
      row18_reducedY01_combinationStep01Coefficient00 +
        row18_reducedY01_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep02Coefficient00 row18_reducedY01_combinationStep01Coefficient00 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 (-((3211279 / 2465195) : ℂ) - ((185701 / 14791170) : ℂ) * ζ ^ 1 - ((23746738 / 7395585) : ℂ) * ζ ^ 2 + ((1711799 / 2958234) : ℂ) * ζ ^ 3 + ((30372661 / 14791170) : ℂ) * ζ ^ 4 + ((1434685 / 2958234) : ℂ) * ζ ^ 5 + ((6171868 / 7395585) : ℂ) * ζ ^ 6 - ((44449057 / 14791170) : ℂ) * ζ ^ 7 - ((5544733 / 7395585) : ℂ) * ζ ^ 8 + ((1124984 / 1479117) : ℂ) * ζ ^ 9 - ((10509077 / 14791170) : ℂ) * ζ ^ 10 + ((5633933 / 4930390) : ℂ) * ζ ^ 11 - ((4383 / 31205) : ℂ) * ζ ^ 12 + ((6004879 / 7395585) : ℂ) * ζ ^ 13 + ((1311473 / 4930390) : ℂ) * ζ ^ 14 - ((34441351 / 14791170) : ℂ) * ζ ^ 15 - ((3742719 / 4930390) : ℂ) * ζ ^ 16 - ((6340203 / 4930390) : ℂ) * ζ ^ 17 - ((2674 / 493039) : ℂ) * ζ ^ 18 + ((5054367 / 2465195) : ℂ) * ζ ^ 19 + ((5852383 / 7395585) : ℂ) * ζ ^ 20 + ((6651097 / 7395585) : ℂ) * ζ ^ 21 + ((3136943 / 2958234) : ℂ) * ζ ^ 22 + ((1789325 / 2958234) : ℂ) * ζ ^ 23 - ((4119628 / 7395585) : ℂ) * ζ ^ 24 - ((4459143 / 4930390) : ℂ) * ζ ^ 25 - ((1255971 / 4930390) : ℂ) * ζ ^ 26 + ((58151 / 4930390) : ℂ) * ζ ^ 27 + ((654361 / 2465195) : ℂ) * ζ ^ 28 + ((452837 / 2465195) : ℂ) * ζ ^ 29 - ((36750 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep02Coefficient01 : ℂ :=
  (((181973 / 37446) : ℂ) + ((67963 / 18723) : ℂ) * ζ ^ 1 - ((63929 / 37446) : ℂ) * ζ ^ 2 - ((59251 / 12482) : ℂ) * ζ ^ 3 + ((14442 / 6241) : ℂ) * ζ ^ 5 + ((30683 / 18723) : ℂ) * ζ ^ 6 - ((42063 / 12482) : ℂ) * ζ ^ 8 - ((44701 / 12482) : ℂ) * ζ ^ 9 + ((7275 / 6241) : ℂ) * ζ ^ 11 - ((42063 / 12482) : ℂ) * ζ ^ 12 - ((67963 / 18723) : ℂ) * ζ ^ 13 + ((128479 / 37446) : ℂ) * ζ ^ 15 - ((67963 / 18723) : ℂ) * ζ ^ 17 - ((41765 / 12482) : ℂ) * ζ ^ 18 + ((41827 / 37446) : ℂ) * ζ ^ 21 + ((63929 / 37446) : ℂ) * ζ ^ 22 + ((24637 / 18723) : ℂ) * ζ ^ 25 - ((41827 / 37446) : ℂ) * ζ ^ 27 + ((42063 / 12482) : ℂ) * ζ ^ 28 + ((67963 / 18723) : ℂ) * ζ ^ 29 + ((30683 / 37446) : ℂ) * ζ ^ 30 - ((7275 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep02CoefficientIdentity01 :
    row18_reducedY01_combinationStep02Coefficient01 =
      row18_reducedY01_combinationStep01Coefficient01 +
        row18_reducedY01_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep02Coefficient01 row18_reducedY01_combinationStep01Coefficient01 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 (((15773469 / 4930390) : ℂ) - ((15355828 / 7395585) : ℂ) * ζ ^ 1 - ((20797147 / 14791170) : ℂ) * ζ ^ 2 + ((12437891 / 7395585) : ℂ) * ζ ^ 3 - ((1237367 / 1479117) : ℂ) * ζ ^ 4 + ((14207167 / 14791170) : ℂ) * ζ ^ 5 + ((1320872 / 1479117) : ℂ) * ζ ^ 6 + ((1156643 / 2465195) : ℂ) * ζ ^ 7 - ((7668371 / 14791170) : ℂ) * ζ ^ 8 - ((953351 / 7395585) : ℂ) * ζ ^ 9 + ((17490551 / 7395585) : ℂ) * ζ ^ 10 + ((567905 / 1479117) : ℂ) * ζ ^ 11 + ((643883 / 7395585) : ℂ) * ζ ^ 12 + ((8297559 / 4930390) : ℂ) * ζ ^ 13 + ((42177247 / 14791170) : ℂ) * ζ ^ 14 + ((3688051 / 2465195) : ℂ) * ζ ^ 15 - ((1719797 / 986078) : ℂ) * ζ ^ 16 + ((25392739 / 14791170) : ℂ) * ζ ^ 17 + ((18012447 / 4930390) : ℂ) * ζ ^ 18 + ((1188539 / 986078) : ℂ) * ζ ^ 19 + ((5079377 / 2958234) : ℂ) * ζ ^ 20 + ((14154981 / 4930390) : ℂ) * ζ ^ 21 + ((25388731 / 14791170) : ℂ) * ζ ^ 22 - ((2796519 / 2465195) : ℂ) * ζ ^ 23 + ((7167697 / 7395585) : ℂ) * ζ ^ 24 + ((4425221 / 4930390) : ℂ) * ζ ^ 25 - ((587567 / 493039) : ℂ) * ζ ^ 26 + ((4437217 / 4930390) : ℂ) * ζ ^ 27 + ((610334 / 493039) : ℂ) * ζ ^ 28 - ((966517 / 4930390) : ℂ) * ζ ^ 29 - ((34125 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep02Coefficient02 : ℂ :=
  (-((7088 / 6241) : ℂ) - ((154105 / 37446) : ℂ) * ζ ^ 1 + ((154105 / 37446) : ℂ) * ζ ^ 3 - ((36669 / 12482) : ℂ) * ζ ^ 5 - ((68648 / 18723) : ℂ) * ζ ^ 6 + ((3544 / 6241) : ℂ) * ζ ^ 8 + ((11976 / 6241) : ℂ) * ζ ^ 9 - ((22049 / 18723) : ℂ) * ζ ^ 11 + ((4111 / 6241) : ℂ) * ζ ^ 12 + ((154105 / 37446) : ℂ) * ζ ^ 13 - ((44030 / 18723) : ℂ) * ζ ^ 15 + ((154105 / 37446) : ℂ) * ζ ^ 17 + ((28469 / 6241) : ℂ) * ζ ^ 18 + ((22015 / 12482) : ℂ) * ζ ^ 21 - ((2977 / 6241) : ℂ) * ζ ^ 24 - ((22049 / 18723) : ℂ) * ζ ^ 25 + ((11976 / 6241) : ℂ) * ζ ^ 27 - ((3544 / 6241) : ℂ) * ζ ^ 28 - ((154105 / 37446) : ℂ) * ζ ^ 29 - ((68648 / 18723) : ℂ) * ζ ^ 30 + ((22049 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep02CoefficientIdentity02 :
    row18_reducedY01_combinationStep02Coefficient02 =
      row18_reducedY01_combinationStep01Coefficient02 +
        row18_reducedY01_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep02Coefficient02 row18_reducedY01_combinationStep01Coefficient02 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep02Coefficient03 : ℂ :=
  (((100129 / 37446) : ℂ) + ((9087 / 6241) : ℂ) * ζ ^ 1 + ((4003 / 18723) : ℂ) * ζ ^ 2 - ((130387 / 37446) : ℂ) * ζ ^ 3 + ((15619 / 18723) : ℂ) * ζ ^ 5 + ((8984 / 6241) : ℂ) * ζ ^ 6 - ((63127 / 37446) : ℂ) * ζ ^ 8 - ((38903 / 37446) : ℂ) * ζ ^ 9 + ((17183 / 12482) : ℂ) * ζ ^ 11 - ((22949 / 18723) : ℂ) * ζ ^ 12 - ((9087 / 6241) : ℂ) * ζ ^ 13 + ((130387 / 37446) : ℂ) * ζ ^ 15 - ((9087 / 6241) : ℂ) * ζ ^ 17 - ((36045 / 12482) : ℂ) * ζ ^ 18 + ((11642 / 18723) : ℂ) * ζ ^ 21 - ((4003 / 18723) : ℂ) * ζ ^ 22 - ((4003 / 18723) : ℂ) * ζ ^ 24 + ((11642 / 18723) : ℂ) * ζ ^ 25 - ((17183 / 12482) : ℂ) * ζ ^ 27 + ((63127 / 37446) : ℂ) * ζ ^ 28 + ((9087 / 6241) : ℂ) * ζ ^ 29 + ((23711 / 12482) : ℂ) * ζ ^ 30 - ((17183 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep02CoefficientIdentity03 :
    row18_reducedY01_combinationStep02Coefficient03 =
      row18_reducedY01_combinationStep01Coefficient03 +
        row18_reducedY01_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep02Coefficient03 row18_reducedY01_combinationStep01Coefficient03 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep02Coefficient04 : ℂ :=
  (-((29197 / 31205) : ℂ) + ((4727 / 187230) : ℂ) * ζ ^ 1 - ((101263 / 93615) : ℂ) * ζ ^ 2 + ((57148 / 18723) : ℂ) * ζ ^ 3 - ((9904 / 31205) : ℂ) * ζ ^ 5 - ((25164 / 31205) : ℂ) * ζ ^ 6 + ((60458 / 93615) : ℂ) * ζ ^ 8 - ((34439 / 187230) : ℂ) * ζ ^ 9 - ((57775 / 37446) : ℂ) * ζ ^ 11 - ((25771 / 93615) : ℂ) * ζ ^ 12 - ((4727 / 187230) : ℂ) * ζ ^ 13 - ((57148 / 18723) : ℂ) * ζ ^ 15 - ((4727 / 187230) : ℂ) * ζ ^ 17 + ((188854 / 93615) : ℂ) * ζ ^ 18 + ((64151 / 187230) : ℂ) * ζ ^ 21 + ((101263 / 93615) : ℂ) * ζ ^ 22 + ((101263 / 93615) : ℂ) * ζ ^ 24 + ((64151 / 187230) : ℂ) * ζ ^ 25 + ((57775 / 37446) : ℂ) * ζ ^ 27 - ((60458 / 93615) : ℂ) * ζ ^ 28 + ((4727 / 187230) : ℂ) * ζ ^ 29 - ((53907 / 31205) : ℂ) * ζ ^ 30 + ((57775 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep02CoefficientIdentity04 :
    row18_reducedY01_combinationStep02Coefficient04 =
      row18_reducedY01_combinationStep01Coefficient04 +
        row18_reducedY01_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep02Coefficient04 row18_reducedY01_combinationStep01Coefficient04 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 (((3211279 / 2465195) : ℂ) + ((185701 / 14791170) : ℂ) * ζ ^ 1 + ((23746738 / 7395585) : ℂ) * ζ ^ 2 - ((1711799 / 2958234) : ℂ) * ζ ^ 3 - ((30372661 / 14791170) : ℂ) * ζ ^ 4 - ((1434685 / 2958234) : ℂ) * ζ ^ 5 - ((6171868 / 7395585) : ℂ) * ζ ^ 6 + ((44449057 / 14791170) : ℂ) * ζ ^ 7 + ((5544733 / 7395585) : ℂ) * ζ ^ 8 - ((1124984 / 1479117) : ℂ) * ζ ^ 9 + ((10509077 / 14791170) : ℂ) * ζ ^ 10 - ((5633933 / 4930390) : ℂ) * ζ ^ 11 + ((4383 / 31205) : ℂ) * ζ ^ 12 - ((6004879 / 7395585) : ℂ) * ζ ^ 13 - ((1311473 / 4930390) : ℂ) * ζ ^ 14 + ((34441351 / 14791170) : ℂ) * ζ ^ 15 + ((3742719 / 4930390) : ℂ) * ζ ^ 16 + ((6340203 / 4930390) : ℂ) * ζ ^ 17 + ((2674 / 493039) : ℂ) * ζ ^ 18 - ((5054367 / 2465195) : ℂ) * ζ ^ 19 - ((5852383 / 7395585) : ℂ) * ζ ^ 20 - ((6651097 / 7395585) : ℂ) * ζ ^ 21 - ((3136943 / 2958234) : ℂ) * ζ ^ 22 - ((1789325 / 2958234) : ℂ) * ζ ^ 23 + ((4119628 / 7395585) : ℂ) * ζ ^ 24 + ((4459143 / 4930390) : ℂ) * ζ ^ 25 + ((1255971 / 4930390) : ℂ) * ζ ^ 26 - ((58151 / 4930390) : ℂ) * ζ ^ 27 - ((654361 / 2465195) : ℂ) * ζ ^ 28 - ((452837 / 2465195) : ℂ) * ζ ^ 29 + ((36750 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep02CoefficientIdentity05 :
    row18_reducedY01_combinationStep02Coefficient05 =
      row18_reducedY01_combinationStep01Coefficient05 +
        row18_reducedY01_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep02Coefficient05 row18_reducedY01_combinationStep01Coefficient05 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep02Coefficient06 : ℂ :=
  (((648761 / 187230) : ℂ) * ζ ^ 1 + ((584093 / 93615) : ℂ) * ζ ^ 2 + ((648761 / 187230) : ℂ) * ζ ^ 3 - ((100269 / 62410) : ℂ) * ζ ^ 5 - ((183143 / 93615) : ℂ) * ζ ^ 6 + ((116635 / 37446) : ℂ) * ζ ^ 8 + ((403739 / 93615) : ℂ) * ζ ^ 9 - ((474784 / 93615) : ℂ) * ζ ^ 11 - ((30963 / 6241) : ℂ) * ζ ^ 12 - ((648761 / 187230) : ℂ) * ζ ^ 13 + ((203353 / 93615) : ℂ) * ζ ^ 15 - ((648761 / 187230) : ℂ) * ζ ^ 17 - ((584093 / 187230) : ℂ) * ζ ^ 18 - ((1055467 / 187230) : ℂ) * ζ ^ 21 - ((584093 / 93615) : ℂ) * ζ ^ 22 + ((30963 / 6241) : ℂ) * ζ ^ 24 + ((474784 / 93615) : ℂ) * ζ ^ 25 - ((403739 / 93615) : ℂ) * ζ ^ 27 - ((116635 / 37446) : ℂ) * ζ ^ 28 + ((648761 / 187230) : ℂ) * ζ ^ 29 + ((767236 / 93615) : ℂ) * ζ ^ 30 + ((474784 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep02CoefficientIdentity06 :
    row18_reducedY01_combinationStep02Coefficient06 =
      row18_reducedY01_combinationStep01Coefficient06 +
        row18_reducedY01_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep02Coefficient06 row18_reducedY01_combinationStep01Coefficient06 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 (-((2864934 / 2465195) : ℂ) - ((62899193 / 14791170) : ℂ) * ζ ^ 1 - ((42652223 / 7395585) : ℂ) * ζ ^ 2 - ((6102641 / 2465195) : ℂ) * ζ ^ 3 + ((26258969 / 14791170) : ℂ) * ζ ^ 4 + ((37047859 / 7395585) : ℂ) * ζ ^ 5 + ((43491217 / 7395585) : ℂ) * ζ ^ 6 + ((6860559 / 4930390) : ℂ) * ζ ^ 7 - ((5094007 / 2958234) : ℂ) * ζ ^ 8 - ((8171686 / 2465195) : ℂ) * ζ ^ 9 - ((19524757 / 4930390) : ℂ) * ζ ^ 10 + ((189641 / 2958234) : ℂ) * ζ ^ 11 + ((40907671 / 14791170) : ℂ) * ζ ^ 12 + ((17773803 / 4930390) : ℂ) * ζ ^ 13 + ((24843181 / 14791170) : ℂ) * ζ ^ 14 - ((3510449 / 1479117) : ℂ) * ζ ^ 15 - ((7416857 / 2465195) : ℂ) * ζ ^ 16 - ((19749764 / 7395585) : ℂ) * ζ ^ 17 - ((11657119 / 14791170) : ℂ) * ζ ^ 18 + ((5170488 / 2465195) : ℂ) * ζ ^ 19 + ((4933748 / 2465195) : ℂ) * ζ ^ 20 + ((10068472 / 7395585) : ℂ) * ζ ^ 21 + ((953212 / 7395585) : ℂ) * ζ ^ 22 - ((6570163 / 4930390) : ℂ) * ζ ^ 23 - ((1101803 / 493039) : ℂ) * ζ ^ 24 - ((4490627 / 2465195) : ℂ) * ζ ^ 25 + ((4521181 / 4930390) : ℂ) * ζ ^ 26 + ((10684649 / 4930390) : ℂ) * ζ ^ 27 + ((1815099 / 2465195) : ℂ) * ζ ^ 28 - ((147927 / 986078) : ℂ) * ζ ^ 29 - ((39375 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep02CoefficientIdentity07 :
    row18_reducedY01_combinationStep02Coefficient07 =
      row18_reducedY01_combinationStep01Coefficient07 +
        row18_reducedY01_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep02Coefficient07 row18_reducedY01_combinationStep01Coefficient07 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep02CoefficientIdentity08 :
    row18_reducedY01_combinationStep02Coefficient08 =
      row18_reducedY01_combinationStep01Coefficient08 +
        row18_reducedY01_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep02Coefficient08 row18_reducedY01_combinationStep01Coefficient08 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep02CoefficientIdentity09 :
    row18_reducedY01_combinationStep02Coefficient09 =
      row18_reducedY01_combinationStep01Coefficient09 +
        row18_reducedY01_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep02Coefficient09 row18_reducedY01_combinationStep01Coefficient09 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep02CoefficientIdentity10 :
    row18_reducedY01_combinationStep02Coefficient10 =
      row18_reducedY01_combinationStep01Coefficient10 +
        row18_reducedY01_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep02Coefficient10 row18_reducedY01_combinationStep01Coefficient10 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep02CoefficientIdentity11 :
    row18_reducedY01_combinationStep02Coefficient11 =
      row18_reducedY01_combinationStep01Coefficient11 +
        row18_reducedY01_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep02Coefficient11 row18_reducedY01_combinationStep01Coefficient11 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep02CoefficientIdentity12 :
    row18_reducedY01_combinationStep02Coefficient12 =
      row18_reducedY01_combinationStep01Coefficient12 +
        row18_reducedY01_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep02Coefficient12 row18_reducedY01_combinationStep01Coefficient12 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep02CoefficientIdentity13 :
    row18_reducedY01_combinationStep02Coefficient13 =
      row18_reducedY01_combinationStep01Coefficient13 +
        row18_reducedY01_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep02Coefficient13 row18_reducedY01_combinationStep01Coefficient13 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep02CoefficientIdentity14 :
    row18_reducedY01_combinationStep02Coefficient14 =
      row18_reducedY01_combinationStep01Coefficient14 +
        row18_reducedY01_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep02Coefficient14 row18_reducedY01_combinationStep01Coefficient14 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep02CoefficientIdentity15 :
    row18_reducedY01_combinationStep02Coefficient15 =
      row18_reducedY01_combinationStep01Coefficient15 +
        row18_reducedY01_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep02Coefficient15 row18_reducedY01_combinationStep01Coefficient15 row18_reducedY01_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY01_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY01_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY01_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY01_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY01_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY01_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY01_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY01_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY01_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY01_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY01_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY01_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY01_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY01_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY01_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY01_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY01_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY01_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY01_combinationStep02CoefficientIdentity00,
      row18_reducedY01_combinationStep02CoefficientIdentity01,
      row18_reducedY01_combinationStep02CoefficientIdentity02,
      row18_reducedY01_combinationStep02CoefficientIdentity03,
      row18_reducedY01_combinationStep02CoefficientIdentity04,
      row18_reducedY01_combinationStep02CoefficientIdentity05,
      row18_reducedY01_combinationStep02CoefficientIdentity06,
      row18_reducedY01_combinationStep02CoefficientIdentity07,
      row18_reducedY01_combinationStep02CoefficientIdentity08,
      row18_reducedY01_combinationStep02CoefficientIdentity09,
      row18_reducedY01_combinationStep02CoefficientIdentity10,
      row18_reducedY01_combinationStep02CoefficientIdentity11,
      row18_reducedY01_combinationStep02CoefficientIdentity12,
      row18_reducedY01_combinationStep02CoefficientIdentity13,
      row18_reducedY01_combinationStep02CoefficientIdentity14,
      row18_reducedY01_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY01_combinationStep02Multiplier * equation

private def row18_reducedY01_combinationStep03Multiplier : ℂ :=
  (((6270 / 6241) : ℂ) + ((24140 / 18723) : ℂ) * ζ ^ 1 + ((29884 / 18723) : ℂ) * ζ ^ 2 + ((6030 / 6241) : ℂ) * ζ ^ 3 - ((14980 / 18723) : ℂ) * ζ ^ 5 + ((7028 / 18723) : ℂ) * ζ ^ 8 + ((24958 / 18723) : ℂ) * ζ ^ 9 - ((43048 / 18723) : ℂ) * ζ ^ 11 - ((44648 / 18723) : ℂ) * ζ ^ 12 - ((24140 / 18723) : ℂ) * ζ ^ 13 + ((7010 / 6241) : ℂ) * ζ ^ 15 - ((24140 / 18723) : ℂ) * ζ ^ 17 - ((29884 / 18723) : ℂ) * ζ ^ 18 - ((6050 / 18723) : ℂ) * ζ ^ 21 - ((29884 / 18723) : ℂ) * ζ ^ 22 + ((12540 / 6241) : ℂ) * ζ ^ 24 + ((13040 / 6241) : ℂ) * ζ ^ 25 - ((6050 / 18723) : ℂ) * ζ ^ 27 - ((7028 / 18723) : ℂ) * ζ ^ 28 + ((24140 / 18723) : ℂ) * ζ ^ 29 + ((67934 / 18723) : ℂ) * ζ ^ 30 + ((43048 / 18723) : ℂ) * ζ ^ 31)

private def row18_reducedY01_combinationStep03Coefficient00 : ℂ :=
  (((488 / 395) : ℂ) + ((347 / 395) : ℂ) * ζ ^ 1 + ((653 / 790) : ℂ) * ζ ^ 2 - ((399 / 158) : ℂ) * ζ ^ 3 + ((421 / 395) : ℂ) * ζ ^ 5 + ((977 / 790) : ℂ) * ζ ^ 6 - ((134 / 395) : ℂ) * ζ ^ 8 - ((273 / 790) : ℂ) * ζ ^ 9 + ((203 / 158) : ℂ) * ζ ^ 11 - ((162 / 395) : ℂ) * ζ ^ 12 - ((347 / 395) : ℂ) * ζ ^ 13 + ((399 / 158) : ℂ) * ζ ^ 15 - ((347 / 395) : ℂ) * ζ ^ 17 - ((1629 / 790) : ℂ) * ζ ^ 18 - ((74 / 395) : ℂ) * ζ ^ 21 - ((653 / 790) : ℂ) * ζ ^ 22 - ((653 / 790) : ℂ) * ζ ^ 24 - ((74 / 395) : ℂ) * ζ ^ 25 - ((203 / 158) : ℂ) * ζ ^ 27 + ((134 / 395) : ℂ) * ζ ^ 28 + ((347 / 395) : ℂ) * ζ ^ 29 + ((921 / 790) : ℂ) * ζ ^ 30 - ((203 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep03CoefficientIdentity00 :
    row18_reducedY01_combinationStep03Coefficient00 =
      row18_reducedY01_combinationStep02Coefficient00 +
        row18_reducedY01_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep03Coefficient00 row18_reducedY01_combinationStep02Coefficient00 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 (-((8439655 / 2958234) : ℂ) - ((3322141 / 1479117) : ℂ) * ζ ^ 1 + ((318277 / 1479117) : ℂ) * ζ ^ 2 + ((4399090 / 1479117) : ℂ) * ζ ^ 3 + ((4098376 / 1479117) : ℂ) * ζ ^ 4 + ((1418693 / 2958234) : ℂ) * ζ ^ 5 - ((1989279 / 986078) : ℂ) * ζ ^ 6 - ((4235095 / 1479117) : ℂ) * ζ ^ 7 - ((1925107 / 1479117) : ℂ) * ζ ^ 8 + ((1227478 / 1479117) : ℂ) * ζ ^ 9 + ((1974403 / 1479117) : ℂ) * ζ ^ 10 + ((1246964 / 1479117) : ℂ) * ζ ^ 11 - ((27716 / 493039) : ℂ) * ζ ^ 12 - ((728929 / 1479117) : ℂ) * ζ ^ 13 - ((1499443 / 2958234) : ℂ) * ζ ^ 14 - ((1033991 / 2958234) : ℂ) * ζ ^ 15 - ((415393 / 2958234) : ℂ) * ζ ^ 16 + ((232695 / 986078) : ℂ) * ζ ^ 17 + ((822963 / 986078) : ℂ) * ζ ^ 18 + ((2855839 / 2958234) : ℂ) * ζ ^ 19 + ((90252 / 493039) : ℂ) * ζ ^ 20 - ((939923 / 1479117) : ℂ) * ζ ^ 21 - ((615453 / 493039) : ℂ) * ζ ^ 22 - ((1958717 / 2958234) : ℂ) * ζ ^ 23 + ((1531115 / 2958234) : ℂ) * ζ ^ 24 + ((492529 / 493039) : ℂ) * ζ ^ 25 + ((1353455 / 1479117) : ℂ) * ζ ^ 26 + ((100565 / 986078) : ℂ) * ζ ^ 27 - ((1045639 / 1479117) : ℂ) * ζ ^ 28 - ((514219 / 986078) : ℂ) * ζ ^ 29 - ((53810 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep03Coefficient01 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY01_combinationStep03CoefficientIdentity01 :
    row18_reducedY01_combinationStep03Coefficient01 =
      row18_reducedY01_combinationStep02Coefficient01 +
        row18_reducedY01_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep03Coefficient01 row18_reducedY01_combinationStep02Coefficient01 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 (((11718593 / 2958234) : ℂ) + ((147601 / 37446) : ℂ) * ζ ^ 1 - ((1241456 / 1479117) : ℂ) * ζ ^ 2 - ((5913554 / 1479117) : ℂ) * ζ ^ 3 - ((1651010 / 493039) : ℂ) * ζ ^ 4 - ((655965 / 493039) : ℂ) * ζ ^ 5 + ((7390291 / 2958234) : ℂ) * ζ ^ 6 + ((6087707 / 1479117) : ℂ) * ζ ^ 7 + ((466619 / 986078) : ℂ) * ζ ^ 8 - ((2608018 / 1479117) : ℂ) * ζ ^ 9 - ((966896 / 493039) : ℂ) * ζ ^ 10 - ((2210003 / 986078) : ℂ) * ζ ^ 11 - ((2429609 / 2958234) : ℂ) * ζ ^ 12 + ((20788 / 493039) : ℂ) * ζ ^ 13 - ((53366 / 493039) : ℂ) * ζ ^ 14 + ((704381 / 493039) : ℂ) * ζ ^ 15 + ((1874021 / 1479117) : ℂ) * ζ ^ 16 - ((1178307 / 986078) : ℂ) * ζ ^ 17 - ((2618623 / 986078) : ℂ) * ζ ^ 18 - ((4509166 / 1479117) : ℂ) * ζ ^ 19 - ((6337985 / 2958234) : ℂ) * ζ ^ 20 + ((790880 / 493039) : ℂ) * ζ ^ 21 + ((3105529 / 1479117) : ℂ) * ζ ^ 22 - ((161685 / 493039) : ℂ) * ζ ^ 23 - ((4546813 / 2958234) : ℂ) * ζ ^ 24 - ((1024548 / 493039) : ℂ) * ζ ^ 25 - ((1280165 / 1479117) : ℂ) * ζ ^ 26 + ((2385695 / 2958234) : ℂ) * ζ ^ 27 + ((1190018 / 1479117) : ℂ) * ζ ^ 28 + ((733826 / 1479117) : ℂ) * ζ ^ 29 + ((301336 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep03Coefficient02 : ℂ :=
  (-((7088 / 6241) : ℂ) - ((154105 / 37446) : ℂ) * ζ ^ 1 + ((154105 / 37446) : ℂ) * ζ ^ 3 - ((36669 / 12482) : ℂ) * ζ ^ 5 - ((68648 / 18723) : ℂ) * ζ ^ 6 + ((3544 / 6241) : ℂ) * ζ ^ 8 + ((11976 / 6241) : ℂ) * ζ ^ 9 - ((22049 / 18723) : ℂ) * ζ ^ 11 + ((4111 / 6241) : ℂ) * ζ ^ 12 + ((154105 / 37446) : ℂ) * ζ ^ 13 - ((44030 / 18723) : ℂ) * ζ ^ 15 + ((154105 / 37446) : ℂ) * ζ ^ 17 + ((28469 / 6241) : ℂ) * ζ ^ 18 + ((22015 / 12482) : ℂ) * ζ ^ 21 - ((2977 / 6241) : ℂ) * ζ ^ 24 - ((22049 / 18723) : ℂ) * ζ ^ 25 + ((11976 / 6241) : ℂ) * ζ ^ 27 - ((3544 / 6241) : ℂ) * ζ ^ 28 - ((154105 / 37446) : ℂ) * ζ ^ 29 - ((68648 / 18723) : ℂ) * ζ ^ 30 + ((22049 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep03CoefficientIdentity02 :
    row18_reducedY01_combinationStep03Coefficient02 =
      row18_reducedY01_combinationStep02Coefficient02 +
        row18_reducedY01_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep03Coefficient02 row18_reducedY01_combinationStep02Coefficient02 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep03Coefficient03 : ℂ :=
  (((100129 / 37446) : ℂ) + ((9087 / 6241) : ℂ) * ζ ^ 1 + ((4003 / 18723) : ℂ) * ζ ^ 2 - ((130387 / 37446) : ℂ) * ζ ^ 3 + ((15619 / 18723) : ℂ) * ζ ^ 5 + ((8984 / 6241) : ℂ) * ζ ^ 6 - ((63127 / 37446) : ℂ) * ζ ^ 8 - ((38903 / 37446) : ℂ) * ζ ^ 9 + ((17183 / 12482) : ℂ) * ζ ^ 11 - ((22949 / 18723) : ℂ) * ζ ^ 12 - ((9087 / 6241) : ℂ) * ζ ^ 13 + ((130387 / 37446) : ℂ) * ζ ^ 15 - ((9087 / 6241) : ℂ) * ζ ^ 17 - ((36045 / 12482) : ℂ) * ζ ^ 18 + ((11642 / 18723) : ℂ) * ζ ^ 21 - ((4003 / 18723) : ℂ) * ζ ^ 22 - ((4003 / 18723) : ℂ) * ζ ^ 24 + ((11642 / 18723) : ℂ) * ζ ^ 25 - ((17183 / 12482) : ℂ) * ζ ^ 27 + ((63127 / 37446) : ℂ) * ζ ^ 28 + ((9087 / 6241) : ℂ) * ζ ^ 29 + ((23711 / 12482) : ℂ) * ζ ^ 30 - ((17183 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep03CoefficientIdentity03 :
    row18_reducedY01_combinationStep03Coefficient03 =
      row18_reducedY01_combinationStep02Coefficient03 +
        row18_reducedY01_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep03Coefficient03 row18_reducedY01_combinationStep02Coefficient03 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep03Coefficient04 : ℂ :=
  (-((29197 / 31205) : ℂ) + ((4727 / 187230) : ℂ) * ζ ^ 1 - ((101263 / 93615) : ℂ) * ζ ^ 2 + ((57148 / 18723) : ℂ) * ζ ^ 3 - ((9904 / 31205) : ℂ) * ζ ^ 5 - ((25164 / 31205) : ℂ) * ζ ^ 6 + ((60458 / 93615) : ℂ) * ζ ^ 8 - ((34439 / 187230) : ℂ) * ζ ^ 9 - ((57775 / 37446) : ℂ) * ζ ^ 11 - ((25771 / 93615) : ℂ) * ζ ^ 12 - ((4727 / 187230) : ℂ) * ζ ^ 13 - ((57148 / 18723) : ℂ) * ζ ^ 15 - ((4727 / 187230) : ℂ) * ζ ^ 17 + ((188854 / 93615) : ℂ) * ζ ^ 18 + ((64151 / 187230) : ℂ) * ζ ^ 21 + ((101263 / 93615) : ℂ) * ζ ^ 22 + ((101263 / 93615) : ℂ) * ζ ^ 24 + ((64151 / 187230) : ℂ) * ζ ^ 25 + ((57775 / 37446) : ℂ) * ζ ^ 27 - ((60458 / 93615) : ℂ) * ζ ^ 28 + ((4727 / 187230) : ℂ) * ζ ^ 29 - ((53907 / 31205) : ℂ) * ζ ^ 30 + ((57775 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep03CoefficientIdentity04 :
    row18_reducedY01_combinationStep03Coefficient04 =
      row18_reducedY01_combinationStep02Coefficient04 +
        row18_reducedY01_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep03Coefficient04 row18_reducedY01_combinationStep02Coefficient04 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep03Coefficient05 : ℂ :=
  (((619 / 12482) : ℂ) - ((8222 / 18723) : ℂ) * ζ ^ 1 - ((6107 / 18723) : ℂ) * ζ ^ 2 + ((1157 / 12482) : ℂ) * ζ ^ 3 - ((6033 / 12482) : ℂ) * ζ ^ 5 - ((10001 / 18723) : ℂ) * ζ ^ 8 - ((5165 / 37446) : ℂ) * ζ ^ 9 + ((847 / 18723) : ℂ) * ζ ^ 11 + ((8144 / 18723) : ℂ) * ζ ^ 12 + ((8222 / 18723) : ℂ) * ζ ^ 13 - ((908 / 18723) : ℂ) * ζ ^ 15 + ((8222 / 18723) : ℂ) * ζ ^ 17 + ((6107 / 18723) : ℂ) * ζ ^ 18 + ((19915 / 37446) : ℂ) * ζ ^ 21 + ((6107 / 18723) : ℂ) * ζ ^ 22 + ((619 / 6241) : ℂ) * ζ ^ 24 + ((1655 / 37446) : ℂ) * ζ ^ 25 + ((19915 / 37446) : ℂ) * ζ ^ 27 + ((10001 / 18723) : ℂ) * ζ ^ 28 - ((8222 / 18723) : ℂ) * ζ ^ 29 - ((9431 / 37446) : ℂ) * ζ ^ 30 - ((847 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep03CoefficientIdentity05 :
    row18_reducedY01_combinationStep03Coefficient05 =
      row18_reducedY01_combinationStep02Coefficient05 +
        row18_reducedY01_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep03Coefficient05 row18_reducedY01_combinationStep02Coefficient05 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 (-((11281 / 986078) : ℂ) + ((1340461 / 2958234) : ℂ) * ζ ^ 1 + ((1810865 / 2958234) : ℂ) * ζ ^ 2 + ((2857 / 12482) : ℂ) * ζ ^ 3 + ((196713 / 493039) : ℂ) * ζ ^ 4 + ((458558 / 1479117) : ℂ) * ζ ^ 5 - ((405425 / 986078) : ℂ) * ζ ^ 6 - ((643621 / 2958234) : ℂ) * ζ ^ 7 + ((129642 / 493039) : ℂ) * ζ ^ 8 - ((139379 / 986078) : ℂ) * ζ ^ 9 + ((142876 / 493039) : ℂ) * ζ ^ 10 + ((1059913 / 2958234) : ℂ) * ζ ^ 11 - ((1103092 / 1479117) : ℂ) * ζ ^ 12 - ((1050185 / 2958234) : ℂ) * ζ ^ 13 - ((128669 / 493039) : ℂ) * ζ ^ 14 - ((182129 / 986078) : ℂ) * ζ ^ 15 + ((3110023 / 2958234) : ℂ) * ζ ^ 16 + ((2093849 / 2958234) : ℂ) * ζ ^ 17 + ((378469 / 2958234) : ℂ) * ζ ^ 18 + ((312885 / 986078) : ℂ) * ζ ^ 19 - ((167562 / 493039) : ℂ) * ζ ^ 20 - ((379843 / 986078) : ℂ) * ζ ^ 21 - ((650350 / 1479117) : ℂ) * ζ ^ 22 - ((275267 / 493039) : ℂ) * ζ ^ 23 - ((1303913 / 2958234) : ℂ) * ζ ^ 24 + ((102287 / 2958234) : ℂ) * ζ ^ 25 + ((354575 / 986078) : ℂ) * ζ ^ 26 + ((622019 / 2958234) : ℂ) * ζ ^ 27 + ((68864 / 1479117) : ℂ) * ζ ^ 28 - ((21859 / 493039) : ℂ) * ζ ^ 29 - ((150668 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep03Coefficient06 : ℂ :=
  (((648761 / 187230) : ℂ) * ζ ^ 1 + ((584093 / 93615) : ℂ) * ζ ^ 2 + ((648761 / 187230) : ℂ) * ζ ^ 3 - ((100269 / 62410) : ℂ) * ζ ^ 5 - ((183143 / 93615) : ℂ) * ζ ^ 6 + ((116635 / 37446) : ℂ) * ζ ^ 8 + ((403739 / 93615) : ℂ) * ζ ^ 9 - ((474784 / 93615) : ℂ) * ζ ^ 11 - ((30963 / 6241) : ℂ) * ζ ^ 12 - ((648761 / 187230) : ℂ) * ζ ^ 13 + ((203353 / 93615) : ℂ) * ζ ^ 15 - ((648761 / 187230) : ℂ) * ζ ^ 17 - ((584093 / 187230) : ℂ) * ζ ^ 18 - ((1055467 / 187230) : ℂ) * ζ ^ 21 - ((584093 / 93615) : ℂ) * ζ ^ 22 + ((30963 / 6241) : ℂ) * ζ ^ 24 + ((474784 / 93615) : ℂ) * ζ ^ 25 - ((403739 / 93615) : ℂ) * ζ ^ 27 - ((116635 / 37446) : ℂ) * ζ ^ 28 + ((648761 / 187230) : ℂ) * ζ ^ 29 + ((767236 / 93615) : ℂ) * ζ ^ 30 + ((474784 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep03CoefficientIdentity06 :
    row18_reducedY01_combinationStep03Coefficient06 =
      row18_reducedY01_combinationStep02Coefficient06 +
        row18_reducedY01_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep03Coefficient06 row18_reducedY01_combinationStep02Coefficient06 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep03Coefficient07 : ℂ :=
  (-((111355 / 37446) : ℂ) - ((88363 / 37446) : ℂ) * ζ ^ 1 + ((1547 / 37446) : ℂ) * ζ ^ 2 + ((55327 / 18723) : ℂ) * ζ ^ 3 - ((29632 / 18723) : ℂ) * ζ ^ 5 - ((23339 / 12482) : ℂ) * ζ ^ 6 + ((51647 / 37446) : ℂ) * ζ ^ 8 + ((19577 / 12482) : ℂ) * ζ ^ 9 - ((41885 / 37446) : ℂ) * ζ ^ 11 + ((35782 / 18723) : ℂ) * ζ ^ 12 + ((88363 / 37446) : ℂ) * ζ ^ 13 - ((55327 / 18723) : ℂ) * ζ ^ 15 + ((88363 / 37446) : ℂ) * ζ ^ 17 + ((54904 / 18723) : ℂ) * ζ ^ 18 - ((29099 / 37446) : ℂ) * ζ ^ 21 - ((1547 / 37446) : ℂ) * ζ ^ 22 - ((1547 / 37446) : ℂ) * ζ ^ 24 - ((29099 / 37446) : ℂ) * ζ ^ 25 + ((41885 / 37446) : ℂ) * ζ ^ 27 - ((51647 / 37446) : ℂ) * ζ ^ 28 - ((88363 / 37446) : ℂ) * ζ ^ 29 - ((8350 / 6241) : ℂ) * ζ ^ 30 + ((41885 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep03CoefficientIdentity07 :
    row18_reducedY01_combinationStep03Coefficient07 =
      row18_reducedY01_combinationStep02Coefficient07 +
        row18_reducedY01_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep03Coefficient07 row18_reducedY01_combinationStep02Coefficient07 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 (((8439655 / 2958234) : ℂ) + ((3322141 / 1479117) : ℂ) * ζ ^ 1 - ((318277 / 1479117) : ℂ) * ζ ^ 2 - ((4399090 / 1479117) : ℂ) * ζ ^ 3 - ((4098376 / 1479117) : ℂ) * ζ ^ 4 - ((1418693 / 2958234) : ℂ) * ζ ^ 5 + ((1989279 / 986078) : ℂ) * ζ ^ 6 + ((4235095 / 1479117) : ℂ) * ζ ^ 7 + ((1925107 / 1479117) : ℂ) * ζ ^ 8 - ((1227478 / 1479117) : ℂ) * ζ ^ 9 - ((1974403 / 1479117) : ℂ) * ζ ^ 10 - ((1246964 / 1479117) : ℂ) * ζ ^ 11 + ((27716 / 493039) : ℂ) * ζ ^ 12 + ((728929 / 1479117) : ℂ) * ζ ^ 13 + ((1499443 / 2958234) : ℂ) * ζ ^ 14 + ((1033991 / 2958234) : ℂ) * ζ ^ 15 + ((415393 / 2958234) : ℂ) * ζ ^ 16 - ((232695 / 986078) : ℂ) * ζ ^ 17 - ((822963 / 986078) : ℂ) * ζ ^ 18 - ((2855839 / 2958234) : ℂ) * ζ ^ 19 - ((90252 / 493039) : ℂ) * ζ ^ 20 + ((939923 / 1479117) : ℂ) * ζ ^ 21 + ((615453 / 493039) : ℂ) * ζ ^ 22 + ((1958717 / 2958234) : ℂ) * ζ ^ 23 - ((1531115 / 2958234) : ℂ) * ζ ^ 24 - ((492529 / 493039) : ℂ) * ζ ^ 25 - ((1353455 / 1479117) : ℂ) * ζ ^ 26 - ((100565 / 986078) : ℂ) * ζ ^ 27 + ((1045639 / 1479117) : ℂ) * ζ ^ 28 + ((514219 / 986078) : ℂ) * ζ ^ 29 + ((53810 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep03CoefficientIdentity08 :
    row18_reducedY01_combinationStep03Coefficient08 =
      row18_reducedY01_combinationStep02Coefficient08 +
        row18_reducedY01_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep03Coefficient08 row18_reducedY01_combinationStep02Coefficient08 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep03CoefficientIdentity09 :
    row18_reducedY01_combinationStep03Coefficient09 =
      row18_reducedY01_combinationStep02Coefficient09 +
        row18_reducedY01_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep03Coefficient09 row18_reducedY01_combinationStep02Coefficient09 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep03CoefficientIdentity10 :
    row18_reducedY01_combinationStep03Coefficient10 =
      row18_reducedY01_combinationStep02Coefficient10 +
        row18_reducedY01_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep03Coefficient10 row18_reducedY01_combinationStep02Coefficient10 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep03CoefficientIdentity11 :
    row18_reducedY01_combinationStep03Coefficient11 =
      row18_reducedY01_combinationStep02Coefficient11 +
        row18_reducedY01_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep03Coefficient11 row18_reducedY01_combinationStep02Coefficient11 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep03CoefficientIdentity12 :
    row18_reducedY01_combinationStep03Coefficient12 =
      row18_reducedY01_combinationStep02Coefficient12 +
        row18_reducedY01_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep03Coefficient12 row18_reducedY01_combinationStep02Coefficient12 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep03CoefficientIdentity13 :
    row18_reducedY01_combinationStep03Coefficient13 =
      row18_reducedY01_combinationStep02Coefficient13 +
        row18_reducedY01_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep03Coefficient13 row18_reducedY01_combinationStep02Coefficient13 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep03CoefficientIdentity14 :
    row18_reducedY01_combinationStep03Coefficient14 =
      row18_reducedY01_combinationStep02Coefficient14 +
        row18_reducedY01_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep03Coefficient14 row18_reducedY01_combinationStep02Coefficient14 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep03CoefficientIdentity15 :
    row18_reducedY01_combinationStep03Coefficient15 =
      row18_reducedY01_combinationStep02Coefficient15 +
        row18_reducedY01_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep03Coefficient15 row18_reducedY01_combinationStep02Coefficient15 row18_reducedY01_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY01_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY01_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY01_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY01_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY01_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY01_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY01_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY01_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY01_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY01_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY01_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY01_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY01_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY01_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY01_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY01_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY01_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY01_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY01_combinationStep03CoefficientIdentity00,
      row18_reducedY01_combinationStep03CoefficientIdentity01,
      row18_reducedY01_combinationStep03CoefficientIdentity02,
      row18_reducedY01_combinationStep03CoefficientIdentity03,
      row18_reducedY01_combinationStep03CoefficientIdentity04,
      row18_reducedY01_combinationStep03CoefficientIdentity05,
      row18_reducedY01_combinationStep03CoefficientIdentity06,
      row18_reducedY01_combinationStep03CoefficientIdentity07,
      row18_reducedY01_combinationStep03CoefficientIdentity08,
      row18_reducedY01_combinationStep03CoefficientIdentity09,
      row18_reducedY01_combinationStep03CoefficientIdentity10,
      row18_reducedY01_combinationStep03CoefficientIdentity11,
      row18_reducedY01_combinationStep03CoefficientIdentity12,
      row18_reducedY01_combinationStep03CoefficientIdentity13,
      row18_reducedY01_combinationStep03CoefficientIdentity14,
      row18_reducedY01_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY01_combinationStep03Multiplier * equation

private def row18_reducedY01_combinationStep04Multiplier : ℂ :=
  (((737936 / 93615) : ℂ) + ((379774 / 93615) : ℂ) * ζ ^ 1 - ((379774 / 93615) : ℂ) * ζ ^ 3 + ((355772 / 93615) : ℂ) * ζ ^ 5 + ((32948 / 18723) : ℂ) * ζ ^ 6 - ((368968 / 93615) : ℂ) * ζ ^ 8 - ((278248 / 93615) : ℂ) * ζ ^ 9 + ((24002 / 93615) : ℂ) * ζ ^ 11 - ((676244 / 93615) : ℂ) * ζ ^ 12 - ((379774 / 93615) : ℂ) * ζ ^ 13 + ((632486 / 93615) : ℂ) * ζ ^ 15 - ((379774 / 93615) : ℂ) * ζ ^ 17 - ((75616 / 18723) : ℂ) * ζ ^ 18 + ((252712 / 93615) : ℂ) * ζ ^ 21 + ((20564 / 31205) : ℂ) * ζ ^ 24 + ((24002 / 93615) : ℂ) * ζ ^ 25 - ((278248 / 93615) : ℂ) * ζ ^ 27 + ((368968 / 93615) : ℂ) * ζ ^ 28 + ((379774 / 93615) : ℂ) * ζ ^ 29 + ((32948 / 18723) : ℂ) * ζ ^ 30 - ((24002 / 93615) : ℂ) * ζ ^ 31)

private def row18_reducedY01_combinationStep04Coefficient00 : ℂ :=
  (((488 / 395) : ℂ) + ((347 / 395) : ℂ) * ζ ^ 1 + ((653 / 790) : ℂ) * ζ ^ 2 - ((399 / 158) : ℂ) * ζ ^ 3 + ((421 / 395) : ℂ) * ζ ^ 5 + ((977 / 790) : ℂ) * ζ ^ 6 - ((134 / 395) : ℂ) * ζ ^ 8 - ((273 / 790) : ℂ) * ζ ^ 9 + ((203 / 158) : ℂ) * ζ ^ 11 - ((162 / 395) : ℂ) * ζ ^ 12 - ((347 / 395) : ℂ) * ζ ^ 13 + ((399 / 158) : ℂ) * ζ ^ 15 - ((347 / 395) : ℂ) * ζ ^ 17 - ((1629 / 790) : ℂ) * ζ ^ 18 - ((74 / 395) : ℂ) * ζ ^ 21 - ((653 / 790) : ℂ) * ζ ^ 22 - ((653 / 790) : ℂ) * ζ ^ 24 - ((74 / 395) : ℂ) * ζ ^ 25 - ((203 / 158) : ℂ) * ζ ^ 27 + ((134 / 395) : ℂ) * ζ ^ 28 + ((347 / 395) : ℂ) * ζ ^ 29 + ((921 / 790) : ℂ) * ζ ^ 30 - ((203 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep04CoefficientIdentity00 :
    row18_reducedY01_combinationStep04Coefficient00 =
      row18_reducedY01_combinationStep03Coefficient00 +
        row18_reducedY01_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep04Coefficient00 row18_reducedY01_combinationStep03Coefficient00 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep04Coefficient01 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY01_combinationStep04CoefficientIdentity01 :
    row18_reducedY01_combinationStep04Coefficient01 =
      row18_reducedY01_combinationStep03Coefficient01 +
        row18_reducedY01_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep04Coefficient01 row18_reducedY01_combinationStep03Coefficient01 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep04Coefficient02 : ℂ :=
  (-((30229 / 18723) : ℂ) - ((507323 / 187230) : ℂ) * ζ ^ 1 + ((507323 / 187230) : ℂ) * ζ ^ 3 - ((455489 / 187230) : ℂ) * ζ ^ 5 - ((14052 / 6241) : ℂ) * ζ ^ 6 + ((30229 / 37446) : ℂ) * ζ ^ 8 + ((201943 / 93615) : ℂ) * ζ ^ 9 - ((8639 / 31205) : ℂ) * ζ ^ 11 + ((19129 / 18723) : ℂ) * ζ ^ 12 + ((507323 / 187230) : ℂ) * ζ ^ 13 - ((52432 / 31205) : ℂ) * ζ ^ 15 + ((507323 / 187230) : ℂ) * ζ ^ 17 + ((91405 / 37446) : ℂ) * ζ ^ 18 + ((192731 / 187230) : ℂ) * ζ ^ 21 - ((3700 / 6241) : ℂ) * ζ ^ 24 - ((8639 / 31205) : ℂ) * ζ ^ 25 + ((201943 / 93615) : ℂ) * ζ ^ 27 - ((30229 / 37446) : ℂ) * ζ ^ 28 - ((507323 / 187230) : ℂ) * ζ ^ 29 - ((14052 / 6241) : ℂ) * ζ ^ 30 + ((8639 / 31205) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep04CoefficientIdentity02 :
    row18_reducedY01_combinationStep04Coefficient02 =
      row18_reducedY01_combinationStep03Coefficient02 +
        row18_reducedY01_combinationStep04Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep04Coefficient02 row18_reducedY01_combinationStep03Coefficient02 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 (((1327367 / 7395585) : ℂ) - ((9506477 / 7395585) : ℂ) * ζ ^ 1 - ((9757841 / 4930390) : ℂ) * ζ ^ 2 + ((2556381 / 4930390) : ℂ) * ζ ^ 3 - ((4363717 / 14791170) : ℂ) * ζ ^ 4 + ((18539191 / 14791170) : ℂ) * ζ ^ 5 - ((3240727 / 7395585) : ℂ) * ζ ^ 6 - ((27959767 / 14791170) : ℂ) * ζ ^ 7 + ((860827 / 986078) : ℂ) * ζ ^ 8 - ((6981674 / 7395585) : ℂ) * ζ ^ 9 + ((7486876 / 7395585) : ℂ) * ζ ^ 10 + ((3439762 / 7395585) : ℂ) * ζ ^ 11 - ((908509 / 7395585) : ℂ) * ζ ^ 12 + ((4266862 / 2465195) : ℂ) * ζ ^ 13 - ((7706837 / 14791170) : ℂ) * ζ ^ 14 - ((4153857 / 4930390) : ℂ) * ζ ^ 15 - ((4978028 / 7395585) : ℂ) * ζ ^ 16 - ((12742526 / 7395585) : ℂ) * ζ ^ 17 + ((931066 / 2465195) : ℂ) * ζ ^ 18 + ((2170508 / 7395585) : ℂ) * ζ ^ 19 + ((1791401 / 2465195) : ℂ) * ζ ^ 20 + ((7098829 / 14791170) : ℂ) * ζ ^ 21 + ((1841629 / 2958234) : ℂ) * ζ ^ 22 + ((3035957 / 4930390) : ℂ) * ζ ^ 23 - ((3459638 / 7395585) : ℂ) * ζ ^ 24 - ((2665123 / 14791170) : ℂ) * ζ ^ 25 - ((2840836 / 7395585) : ℂ) * ζ ^ 26 + ((870689 / 14791170) : ℂ) * ζ ^ 27 + ((402829 / 4930390) : ℂ) * ζ ^ 28 + ((672598 / 7395585) : ℂ) * ζ ^ 29 - ((84007 / 7395585) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep04Coefficient03 : ℂ :=
  (((111355 / 37446) : ℂ) + ((88363 / 37446) : ℂ) * ζ ^ 1 - ((1547 / 37446) : ℂ) * ζ ^ 2 - ((55327 / 18723) : ℂ) * ζ ^ 3 + ((29632 / 18723) : ℂ) * ζ ^ 5 + ((23339 / 12482) : ℂ) * ζ ^ 6 - ((51647 / 37446) : ℂ) * ζ ^ 8 - ((19577 / 12482) : ℂ) * ζ ^ 9 + ((41885 / 37446) : ℂ) * ζ ^ 11 - ((35782 / 18723) : ℂ) * ζ ^ 12 - ((88363 / 37446) : ℂ) * ζ ^ 13 + ((55327 / 18723) : ℂ) * ζ ^ 15 - ((88363 / 37446) : ℂ) * ζ ^ 17 - ((54904 / 18723) : ℂ) * ζ ^ 18 + ((29099 / 37446) : ℂ) * ζ ^ 21 + ((1547 / 37446) : ℂ) * ζ ^ 22 + ((1547 / 37446) : ℂ) * ζ ^ 24 + ((29099 / 37446) : ℂ) * ζ ^ 25 - ((41885 / 37446) : ℂ) * ζ ^ 27 + ((51647 / 37446) : ℂ) * ζ ^ 28 + ((88363 / 37446) : ℂ) * ζ ^ 29 + ((8350 / 6241) : ℂ) * ζ ^ 30 - ((41885 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep04CoefficientIdentity03 :
    row18_reducedY01_combinationStep04Coefficient03 =
      row18_reducedY01_combinationStep03Coefficient03 +
        row18_reducedY01_combinationStep04Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep04Coefficient03 row18_reducedY01_combinationStep03Coefficient03 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 (((3504087 / 2465195) : ℂ) - ((5271212 / 2465195) : ℂ) * ζ ^ 1 - ((1507708 / 2465195) : ℂ) * ζ ^ 2 - ((9594587 / 14791170) : ℂ) * ζ ^ 3 + ((3529 / 986078) : ℂ) * ζ ^ 4 - ((240127 / 14791170) : ℂ) * ζ ^ 5 + ((94688 / 1479117) : ℂ) * ζ ^ 6 + ((6335099 / 4930390) : ℂ) * ζ ^ 7 - ((4098279 / 2465195) : ℂ) * ζ ^ 8 + ((18035299 / 14791170) : ℂ) * ζ ^ 9 + ((10238389 / 14791170) : ℂ) * ζ ^ 10 - ((1760194 / 7395585) : ℂ) * ζ ^ 11 + ((6745241 / 14791170) : ℂ) * ζ ^ 12 + ((4030912 / 7395585) : ℂ) * ζ ^ 13 + ((1886485 / 1479117) : ℂ) * ζ ^ 14 + ((710659 / 1479117) : ℂ) * ζ ^ 15 - ((25986713 / 14791170) : ℂ) * ζ ^ 16 + ((2341857 / 2465195) : ℂ) * ζ ^ 17 + ((5393194 / 7395585) : ℂ) * ζ ^ 18 + ((3016897 / 2465195) : ℂ) * ζ ^ 19 + ((648581 / 2958234) : ℂ) * ζ ^ 20 + ((14582588 / 7395585) : ℂ) * ζ ^ 21 + ((10836643 / 14791170) : ℂ) * ζ ^ 22 - ((14469529 / 14791170) : ℂ) * ζ ^ 23 + ((3990761 / 2958234) : ℂ) * ζ ^ 24 - ((1357741 / 2465195) : ℂ) * ζ ^ 25 - ((751003 / 7395585) : ℂ) * ζ ^ 26 + ((785777 / 2465195) : ℂ) * ζ ^ 27 + ((1322766 / 2465195) : ℂ) * ζ ^ 28 + ((211378 / 7395585) : ℂ) * ζ ^ 29 - ((156013 / 14791170) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep04Coefficient04 : ℂ :=
  (-((488 / 395) : ℂ) - ((347 / 395) : ℂ) * ζ ^ 1 - ((653 / 790) : ℂ) * ζ ^ 2 + ((399 / 158) : ℂ) * ζ ^ 3 - ((421 / 395) : ℂ) * ζ ^ 5 - ((977 / 790) : ℂ) * ζ ^ 6 + ((134 / 395) : ℂ) * ζ ^ 8 + ((273 / 790) : ℂ) * ζ ^ 9 - ((203 / 158) : ℂ) * ζ ^ 11 + ((162 / 395) : ℂ) * ζ ^ 12 + ((347 / 395) : ℂ) * ζ ^ 13 - ((399 / 158) : ℂ) * ζ ^ 15 + ((347 / 395) : ℂ) * ζ ^ 17 + ((1629 / 790) : ℂ) * ζ ^ 18 + ((74 / 395) : ℂ) * ζ ^ 21 + ((653 / 790) : ℂ) * ζ ^ 22 + ((653 / 790) : ℂ) * ζ ^ 24 + ((74 / 395) : ℂ) * ζ ^ 25 + ((203 / 158) : ℂ) * ζ ^ 27 - ((134 / 395) : ℂ) * ζ ^ 28 - ((347 / 395) : ℂ) * ζ ^ 29 - ((921 / 790) : ℂ) * ζ ^ 30 + ((203 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep04CoefficientIdentity04 :
    row18_reducedY01_combinationStep04Coefficient04 =
      row18_reducedY01_combinationStep03Coefficient04 +
        row18_reducedY01_combinationStep04Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep04Coefficient04 row18_reducedY01_combinationStep03Coefficient04 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 (-((3504087 / 2465195) : ℂ) + ((5271212 / 2465195) : ℂ) * ζ ^ 1 + ((1507708 / 2465195) : ℂ) * ζ ^ 2 + ((9594587 / 14791170) : ℂ) * ζ ^ 3 - ((3529 / 986078) : ℂ) * ζ ^ 4 + ((240127 / 14791170) : ℂ) * ζ ^ 5 - ((94688 / 1479117) : ℂ) * ζ ^ 6 - ((6335099 / 4930390) : ℂ) * ζ ^ 7 + ((4098279 / 2465195) : ℂ) * ζ ^ 8 - ((18035299 / 14791170) : ℂ) * ζ ^ 9 - ((10238389 / 14791170) : ℂ) * ζ ^ 10 + ((1760194 / 7395585) : ℂ) * ζ ^ 11 - ((6745241 / 14791170) : ℂ) * ζ ^ 12 - ((4030912 / 7395585) : ℂ) * ζ ^ 13 - ((1886485 / 1479117) : ℂ) * ζ ^ 14 - ((710659 / 1479117) : ℂ) * ζ ^ 15 + ((25986713 / 14791170) : ℂ) * ζ ^ 16 - ((2341857 / 2465195) : ℂ) * ζ ^ 17 - ((5393194 / 7395585) : ℂ) * ζ ^ 18 - ((3016897 / 2465195) : ℂ) * ζ ^ 19 - ((648581 / 2958234) : ℂ) * ζ ^ 20 - ((14582588 / 7395585) : ℂ) * ζ ^ 21 - ((10836643 / 14791170) : ℂ) * ζ ^ 22 + ((14469529 / 14791170) : ℂ) * ζ ^ 23 - ((3990761 / 2958234) : ℂ) * ζ ^ 24 + ((1357741 / 2465195) : ℂ) * ζ ^ 25 + ((751003 / 7395585) : ℂ) * ζ ^ 26 - ((785777 / 2465195) : ℂ) * ζ ^ 27 - ((1322766 / 2465195) : ℂ) * ζ ^ 28 - ((211378 / 7395585) : ℂ) * ζ ^ 29 + ((156013 / 14791170) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep04Coefficient05 : ℂ :=
  (((619 / 12482) : ℂ) - ((8222 / 18723) : ℂ) * ζ ^ 1 - ((6107 / 18723) : ℂ) * ζ ^ 2 + ((1157 / 12482) : ℂ) * ζ ^ 3 - ((6033 / 12482) : ℂ) * ζ ^ 5 - ((10001 / 18723) : ℂ) * ζ ^ 8 - ((5165 / 37446) : ℂ) * ζ ^ 9 + ((847 / 18723) : ℂ) * ζ ^ 11 + ((8144 / 18723) : ℂ) * ζ ^ 12 + ((8222 / 18723) : ℂ) * ζ ^ 13 - ((908 / 18723) : ℂ) * ζ ^ 15 + ((8222 / 18723) : ℂ) * ζ ^ 17 + ((6107 / 18723) : ℂ) * ζ ^ 18 + ((19915 / 37446) : ℂ) * ζ ^ 21 + ((6107 / 18723) : ℂ) * ζ ^ 22 + ((619 / 6241) : ℂ) * ζ ^ 24 + ((1655 / 37446) : ℂ) * ζ ^ 25 + ((19915 / 37446) : ℂ) * ζ ^ 27 + ((10001 / 18723) : ℂ) * ζ ^ 28 - ((8222 / 18723) : ℂ) * ζ ^ 29 - ((9431 / 37446) : ℂ) * ζ ^ 30 - ((847 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep04CoefficientIdentity05 :
    row18_reducedY01_combinationStep04Coefficient05 =
      row18_reducedY01_combinationStep03Coefficient05 +
        row18_reducedY01_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep04Coefficient05 row18_reducedY01_combinationStep03Coefficient05 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep04Coefficient06 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep04CoefficientIdentity06 :
    row18_reducedY01_combinationStep04Coefficient06 =
      row18_reducedY01_combinationStep03Coefficient06 +
        row18_reducedY01_combinationStep04Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep04Coefficient06 row18_reducedY01_combinationStep03Coefficient06 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 (-((5903488 / 7395585) : ℂ) + ((24144559 / 14791170) : ℂ) * ζ ^ 1 + ((26486903 / 14791170) : ℂ) * ζ ^ 2 + ((28722938 / 7395585) : ℂ) * ζ ^ 3 + ((6208639 / 2465195) : ℂ) * ζ ^ 4 - ((12293273 / 2958234) : ℂ) * ζ ^ 5 - ((16904844 / 2465195) : ℂ) * ζ ^ 6 - ((2954866 / 493039) : ℂ) * ζ ^ 7 + ((39183113 / 14791170) : ℂ) * ζ ^ 8 + ((110104177 / 14791170) : ℂ) * ζ ^ 9 + ((19895257 / 2958234) : ℂ) * ζ ^ 10 + ((9875242 / 7395585) : ℂ) * ζ ^ 11 - ((26835931 / 4930390) : ℂ) * ζ ^ 12 - ((10421864 / 2465195) : ℂ) * ζ ^ 13 - ((3136761 / 4930390) : ℂ) * ζ ^ 14 + ((30157337 / 14791170) : ℂ) * ζ ^ 15 + ((28618456 / 7395585) : ℂ) * ζ ^ 16 + ((8169166 / 7395585) : ℂ) * ζ ^ 17 + ((8303956 / 2465195) : ℂ) * ζ ^ 18 + ((1135543 / 2958234) : ℂ) * ζ ^ 19 - ((291701 / 93615) : ℂ) * ζ ^ 20 - ((3959989 / 4930390) : ℂ) * ζ ^ 21 - ((652997 / 2958234) : ℂ) * ζ ^ 22 + ((21828892 / 7395585) : ℂ) * ζ ^ 23 + ((6157118 / 2465195) : ℂ) * ζ ^ 24 + ((120022 / 493039) : ℂ) * ζ ^ 25 - ((2857661 / 2958234) : ℂ) * ζ ^ 26 - ((7136959 / 7395585) : ℂ) * ζ ^ 27 - ((6609659 / 14791170) : ℂ) * ζ ^ 28 - ((1009168 / 7395585) : ℂ) * ζ ^ 29 + ((168014 / 7395585) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep04Coefficient07 : ℂ :=
  (-((111355 / 37446) : ℂ) - ((88363 / 37446) : ℂ) * ζ ^ 1 + ((1547 / 37446) : ℂ) * ζ ^ 2 + ((55327 / 18723) : ℂ) * ζ ^ 3 - ((29632 / 18723) : ℂ) * ζ ^ 5 - ((23339 / 12482) : ℂ) * ζ ^ 6 + ((51647 / 37446) : ℂ) * ζ ^ 8 + ((19577 / 12482) : ℂ) * ζ ^ 9 - ((41885 / 37446) : ℂ) * ζ ^ 11 + ((35782 / 18723) : ℂ) * ζ ^ 12 + ((88363 / 37446) : ℂ) * ζ ^ 13 - ((55327 / 18723) : ℂ) * ζ ^ 15 + ((88363 / 37446) : ℂ) * ζ ^ 17 + ((54904 / 18723) : ℂ) * ζ ^ 18 - ((29099 / 37446) : ℂ) * ζ ^ 21 - ((1547 / 37446) : ℂ) * ζ ^ 22 - ((1547 / 37446) : ℂ) * ζ ^ 24 - ((29099 / 37446) : ℂ) * ζ ^ 25 + ((41885 / 37446) : ℂ) * ζ ^ 27 - ((51647 / 37446) : ℂ) * ζ ^ 28 - ((88363 / 37446) : ℂ) * ζ ^ 29 - ((8350 / 6241) : ℂ) * ζ ^ 30 + ((41885 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep04CoefficientIdentity07 :
    row18_reducedY01_combinationStep04Coefficient07 =
      row18_reducedY01_combinationStep03Coefficient07 +
        row18_reducedY01_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep04Coefficient07 row18_reducedY01_combinationStep03Coefficient07 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep04Coefficient08 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep04CoefficientIdentity08 :
    row18_reducedY01_combinationStep04Coefficient08 =
      row18_reducedY01_combinationStep03Coefficient08 +
        row18_reducedY01_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep04Coefficient08 row18_reducedY01_combinationStep03Coefficient08 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep04Coefficient09 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep04CoefficientIdentity09 :
    row18_reducedY01_combinationStep04Coefficient09 =
      row18_reducedY01_combinationStep03Coefficient09 +
        row18_reducedY01_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep04Coefficient09 row18_reducedY01_combinationStep03Coefficient09 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep04Coefficient10 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep04CoefficientIdentity10 :
    row18_reducedY01_combinationStep04Coefficient10 =
      row18_reducedY01_combinationStep03Coefficient10 +
        row18_reducedY01_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep04Coefficient10 row18_reducedY01_combinationStep03Coefficient10 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep04Coefficient11 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep04CoefficientIdentity11 :
    row18_reducedY01_combinationStep04Coefficient11 =
      row18_reducedY01_combinationStep03Coefficient11 +
        row18_reducedY01_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep04Coefficient11 row18_reducedY01_combinationStep03Coefficient11 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep04Coefficient12 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep04CoefficientIdentity12 :
    row18_reducedY01_combinationStep04Coefficient12 =
      row18_reducedY01_combinationStep03Coefficient12 +
        row18_reducedY01_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep04Coefficient12 row18_reducedY01_combinationStep03Coefficient12 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep04Coefficient13 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep04CoefficientIdentity13 :
    row18_reducedY01_combinationStep04Coefficient13 =
      row18_reducedY01_combinationStep03Coefficient13 +
        row18_reducedY01_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep04Coefficient13 row18_reducedY01_combinationStep03Coefficient13 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep04Coefficient14 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep04CoefficientIdentity14 :
    row18_reducedY01_combinationStep04Coefficient14 =
      row18_reducedY01_combinationStep03Coefficient14 +
        row18_reducedY01_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep04Coefficient14 row18_reducedY01_combinationStep03Coefficient14 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep04Coefficient15 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep04CoefficientIdentity15 :
    row18_reducedY01_combinationStep04Coefficient15 =
      row18_reducedY01_combinationStep03Coefficient15 +
        row18_reducedY01_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep04Coefficient15 row18_reducedY01_combinationStep03Coefficient15 row18_reducedY01_combinationStep04Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY01_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY01_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY01_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY01_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY01_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY01_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY01_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY01_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY01_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY01_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY01_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY01_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY01_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY01_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY01_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY01_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY01_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY01_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY01_combinationStep04CoefficientIdentity00,
      row18_reducedY01_combinationStep04CoefficientIdentity01,
      row18_reducedY01_combinationStep04CoefficientIdentity02,
      row18_reducedY01_combinationStep04CoefficientIdentity03,
      row18_reducedY01_combinationStep04CoefficientIdentity04,
      row18_reducedY01_combinationStep04CoefficientIdentity05,
      row18_reducedY01_combinationStep04CoefficientIdentity06,
      row18_reducedY01_combinationStep04CoefficientIdentity07,
      row18_reducedY01_combinationStep04CoefficientIdentity08,
      row18_reducedY01_combinationStep04CoefficientIdentity09,
      row18_reducedY01_combinationStep04CoefficientIdentity10,
      row18_reducedY01_combinationStep04CoefficientIdentity11,
      row18_reducedY01_combinationStep04CoefficientIdentity12,
      row18_reducedY01_combinationStep04CoefficientIdentity13,
      row18_reducedY01_combinationStep04CoefficientIdentity14,
      row18_reducedY01_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY01_combinationStep04Multiplier * equation

private def row18_reducedY01_combinationStep05Multiplier : ℂ :=
  (((27214 / 18723) : ℂ) + ((55570 / 18723) : ℂ) * ζ ^ 1 + ((51254 / 18723) : ℂ) * ζ ^ 2 - ((3622 / 18723) : ℂ) * ζ ^ 3 + ((37322 / 18723) : ℂ) * ζ ^ 6 + ((6706 / 18723) : ℂ) * ζ ^ 8 - ((34328 / 18723) : ℂ) * ζ ^ 9 - ((25880 / 18723) : ℂ) * ζ ^ 11 - ((4644 / 6241) : ℂ) * ζ ^ 12 - ((55570 / 18723) : ℂ) * ζ ^ 13 - ((3622 / 18723) : ℂ) * ζ ^ 15 - ((55570 / 18723) : ℂ) * ζ ^ 17 - ((24040 / 18723) : ℂ) * ζ ^ 18 - ((55570 / 18723) : ℂ) * ζ ^ 21 - ((51254 / 18723) : ℂ) * ζ ^ 22 + ((51254 / 18723) : ℂ) * ζ ^ 24 + ((55570 / 18723) : ℂ) * ζ ^ 25 - ((25880 / 18723) : ℂ) * ζ ^ 27 - ((6706 / 18723) : ℂ) * ζ ^ 28 + ((55570 / 18723) : ℂ) * ζ ^ 29 + ((19320 / 6241) : ℂ) * ζ ^ 30 + ((25880 / 18723) : ℂ) * ζ ^ 31)

private def row18_reducedY01_combinationStep05Coefficient00 : ℂ :=
  (((488 / 395) : ℂ) + ((347 / 395) : ℂ) * ζ ^ 1 + ((653 / 790) : ℂ) * ζ ^ 2 - ((399 / 158) : ℂ) * ζ ^ 3 + ((421 / 395) : ℂ) * ζ ^ 5 + ((977 / 790) : ℂ) * ζ ^ 6 - ((134 / 395) : ℂ) * ζ ^ 8 - ((273 / 790) : ℂ) * ζ ^ 9 + ((203 / 158) : ℂ) * ζ ^ 11 - ((162 / 395) : ℂ) * ζ ^ 12 - ((347 / 395) : ℂ) * ζ ^ 13 + ((399 / 158) : ℂ) * ζ ^ 15 - ((347 / 395) : ℂ) * ζ ^ 17 - ((1629 / 790) : ℂ) * ζ ^ 18 - ((74 / 395) : ℂ) * ζ ^ 21 - ((653 / 790) : ℂ) * ζ ^ 22 - ((653 / 790) : ℂ) * ζ ^ 24 - ((74 / 395) : ℂ) * ζ ^ 25 - ((203 / 158) : ℂ) * ζ ^ 27 + ((134 / 395) : ℂ) * ζ ^ 28 + ((347 / 395) : ℂ) * ζ ^ 29 + ((921 / 790) : ℂ) * ζ ^ 30 - ((203 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep05CoefficientIdentity00 :
    row18_reducedY01_combinationStep05Coefficient00 =
      row18_reducedY01_combinationStep04Coefficient00 +
        row18_reducedY01_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep05Coefficient00 row18_reducedY01_combinationStep04Coefficient00 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep05Coefficient01 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY01_combinationStep05CoefficientIdentity01 :
    row18_reducedY01_combinationStep05Coefficient01 =
      row18_reducedY01_combinationStep04Coefficient01 +
        row18_reducedY01_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep05Coefficient01 row18_reducedY01_combinationStep04Coefficient01 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep05Coefficient02 : ℂ :=
  (((74 / 79) : ℂ) - ((62 / 395) : ℂ) * ζ ^ 1 + ((62 / 395) : ℂ) * ζ ^ 3 - ((156 / 395) : ℂ) * ζ ^ 5 - ((11 / 79) : ℂ) * ζ ^ 6 - ((37 / 79) : ℂ) * ζ ^ 8 + ((259 / 395) : ℂ) * ζ ^ 9 + ((94 / 395) : ℂ) * ζ ^ 11 - ((33 / 79) : ℂ) * ζ ^ 12 + ((62 / 395) : ℂ) * ζ ^ 13 - ((58 / 395) : ℂ) * ζ ^ 15 + ((62 / 395) : ℂ) * ζ ^ 17 + ((76 / 79) : ℂ) * ζ ^ 18 + ((4 / 395) : ℂ) * ζ ^ 21 + ((41 / 79) : ℂ) * ζ ^ 24 + ((94 / 395) : ℂ) * ζ ^ 25 + ((259 / 395) : ℂ) * ζ ^ 27 + ((37 / 79) : ℂ) * ζ ^ 28 - ((62 / 395) : ℂ) * ζ ^ 29 - ((11 / 79) : ℂ) * ζ ^ 30 - ((94 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep05CoefficientIdentity02 :
    row18_reducedY01_combinationStep05Coefficient02 =
      row18_reducedY01_combinationStep04Coefficient02 +
        row18_reducedY01_combinationStep05Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep05Coefficient02 row18_reducedY01_combinationStep04Coefficient02 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 (-((3515060 / 1479117) : ℂ) - ((3336217 / 1479117) : ℂ) * ζ ^ 1 + ((381149 / 1479117) : ℂ) * ζ ^ 2 + ((2376157 / 986078) : ℂ) * ζ ^ 3 + ((3334360 / 1479117) : ℂ) * ζ ^ 4 + ((1509 / 493039) : ℂ) * ζ ^ 5 - ((965970 / 493039) : ℂ) * ζ ^ 6 - ((3213187 / 1479117) : ℂ) * ζ ^ 7 - ((2493937 / 2958234) : ℂ) * ζ ^ 8 + ((74180 / 493039) : ℂ) * ζ ^ 9 + ((368317 / 493039) : ℂ) * ζ ^ 10 + ((1150351 / 1479117) : ℂ) * ζ ^ 11 + ((1553699 / 2958234) : ℂ) * ζ ^ 12 + ((263299 / 1479117) : ℂ) * ζ ^ 13 - ((916001 / 2958234) : ℂ) * ζ ^ 14 - ((1050925 / 1479117) : ℂ) * ζ ^ 15 - ((1056463 / 1479117) : ℂ) * ζ ^ 16 - ((290767 / 1479117) : ℂ) * ζ ^ 17 + ((435280 / 493039) : ℂ) * ζ ^ 18 + ((641596 / 493039) : ℂ) * ζ ^ 19 + ((296368 / 493039) : ℂ) * ζ ^ 20 - ((1897091 / 2958234) : ℂ) * ζ ^ 21 - ((3919685 / 2958234) : ℂ) * ζ ^ 22 - ((1869575 / 2958234) : ℂ) * ζ ^ 23 + ((296368 / 493039) : ℂ) * ζ ^ 24 + ((632424 / 493039) : ℂ) * ζ ^ 25 + ((2091859 / 2958234) : ℂ) * ζ ^ 26 - ((896665 / 2958234) : ℂ) * ζ ^ 27 - ((1976035 / 2958234) : ℂ) * ζ ^ 28 - ((175970 / 493039) : ℂ) * ζ ^ 29 - ((32350 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep05Coefficient03 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep05CoefficientIdentity03 :
    row18_reducedY01_combinationStep05Coefficient03 =
      row18_reducedY01_combinationStep04Coefficient03 +
        row18_reducedY01_combinationStep05Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep05Coefficient03 row18_reducedY01_combinationStep04Coefficient03 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 (((9232469 / 2958234) : ℂ) + ((4322698 / 1479117) : ℂ) * ζ ^ 1 + ((4309039 / 2958234) : ℂ) * ζ ^ 2 - ((1415551 / 986078) : ℂ) * ζ ^ 3 - ((3828359 / 1479117) : ℂ) * ζ ^ 4 - ((2436586 / 1479117) : ℂ) * ζ ^ 5 + ((1560611 / 986078) : ℂ) * ζ ^ 6 + ((3910888 / 1479117) : ℂ) * ζ ^ 7 + ((3061814 / 1479117) : ℂ) * ζ ^ 8 - ((233143 / 1479117) : ℂ) * ζ ^ 9 - ((2550683 / 2958234) : ℂ) * ζ ^ 10 - ((3582209 / 2958234) : ℂ) * ζ ^ 11 - ((643213 / 493039) : ℂ) * ζ ^ 12 - ((23371 / 18723) : ℂ) * ζ ^ 13 + ((231389 / 1479117) : ℂ) * ζ ^ 14 + ((5498377 / 2958234) : ℂ) * ζ ^ 15 + ((1211063 / 493039) : ℂ) * ζ ^ 16 - ((587482 / 1479117) : ℂ) * ζ ^ 17 - ((5573791 / 1479117) : ℂ) * ζ ^ 18 - ((2225224 / 493039) : ℂ) * ζ ^ 19 - ((2040040 / 1479117) : ℂ) * ζ ^ 20 + ((2079279 / 986078) : ℂ) * ζ ^ 21 + ((5255855 / 2958234) : ℂ) * ζ ^ 22 - ((530849 / 1479117) : ℂ) * ζ ^ 23 - ((1077441 / 493039) : ℂ) * ζ ^ 24 - ((1724527 / 986078) : ℂ) * ζ ^ 25 - ((607567 / 2958234) : ℂ) * ζ ^ 26 + ((1190048 / 1479117) : ℂ) * ζ ^ 27 + ((1105540 / 1479117) : ℂ) * ζ ^ 28 + ((187000 / 493039) : ℂ) * ζ ^ 29 + ((181160 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep05Coefficient04 : ℂ :=
  (-((488 / 395) : ℂ) - ((347 / 395) : ℂ) * ζ ^ 1 - ((653 / 790) : ℂ) * ζ ^ 2 + ((399 / 158) : ℂ) * ζ ^ 3 - ((421 / 395) : ℂ) * ζ ^ 5 - ((977 / 790) : ℂ) * ζ ^ 6 + ((134 / 395) : ℂ) * ζ ^ 8 + ((273 / 790) : ℂ) * ζ ^ 9 - ((203 / 158) : ℂ) * ζ ^ 11 + ((162 / 395) : ℂ) * ζ ^ 12 + ((347 / 395) : ℂ) * ζ ^ 13 - ((399 / 158) : ℂ) * ζ ^ 15 + ((347 / 395) : ℂ) * ζ ^ 17 + ((1629 / 790) : ℂ) * ζ ^ 18 + ((74 / 395) : ℂ) * ζ ^ 21 + ((653 / 790) : ℂ) * ζ ^ 22 + ((653 / 790) : ℂ) * ζ ^ 24 + ((74 / 395) : ℂ) * ζ ^ 25 + ((203 / 158) : ℂ) * ζ ^ 27 - ((134 / 395) : ℂ) * ζ ^ 28 - ((347 / 395) : ℂ) * ζ ^ 29 - ((921 / 790) : ℂ) * ζ ^ 30 + ((203 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep05CoefficientIdentity04 :
    row18_reducedY01_combinationStep05Coefficient04 =
      row18_reducedY01_combinationStep04Coefficient04 +
        row18_reducedY01_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep05Coefficient04 row18_reducedY01_combinationStep04Coefficient04 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep05Coefficient05 : ℂ :=
  (-((14 / 79) : ℂ) - ((59 / 79) : ℂ) * ζ ^ 1 - ((77 / 158) : ℂ) * ζ ^ 2 + ((43 / 158) : ℂ) * ζ ^ 3 - ((105 / 158) : ℂ) * ζ ^ 5 - ((29 / 158) : ℂ) * ζ ^ 8 + ((21 / 158) : ℂ) * ζ ^ 9 - ((32 / 79) : ℂ) * ζ ^ 11 + ((85 / 158) : ℂ) * ζ ^ 12 + ((59 / 79) : ℂ) * ζ ^ 13 - ((28 / 79) : ℂ) * ζ ^ 15 + ((59 / 79) : ℂ) * ζ ^ 17 + ((77 / 158) : ℂ) * ζ ^ 18 + ((161 / 158) : ℂ) * ζ ^ 21 + ((77 / 158) : ℂ) * ζ ^ 22 - ((28 / 79) : ℂ) * ζ ^ 24 - ((13 / 158) : ℂ) * ζ ^ 25 + ((161 / 158) : ℂ) * ζ ^ 27 + ((29 / 158) : ℂ) * ζ ^ 28 - ((59 / 79) : ℂ) * ζ ^ 29 - ((29 / 79) : ℂ) * ζ ^ 30 + ((32 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY01_combinationStep05CoefficientIdentity05 :
    row18_reducedY01_combinationStep05Coefficient05 =
      row18_reducedY01_combinationStep04Coefficient05 +
        row18_reducedY01_combinationStep05Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep05Coefficient05 row18_reducedY01_combinationStep04Coefficient05 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 (-((44656 / 493039) : ℂ) + ((74834 / 1479117) : ℂ) * ζ ^ 1 + ((473882 / 1479117) : ℂ) * ζ ^ 2 + ((389509 / 986078) : ℂ) * ζ ^ 3 - ((139842 / 493039) : ℂ) * ζ ^ 4 + ((446509 / 1479117) : ℂ) * ζ ^ 5 - ((443954 / 1479117) : ℂ) * ζ ^ 6 + ((428723 / 2958234) : ℂ) * ζ ^ 7 - ((281490 / 493039) : ℂ) * ζ ^ 8 + ((73632 / 493039) : ℂ) * ζ ^ 9 - ((482014 / 1479117) : ℂ) * ζ ^ 10 + ((653528 / 1479117) : ℂ) * ζ ^ 11 + ((109823 / 986078) : ℂ) * ζ ^ 12 + ((61259 / 493039) : ℂ) * ζ ^ 13 - ((2085935 / 2958234) : ℂ) * ζ ^ 14 - ((901591 / 2958234) : ℂ) * ζ ^ 15 - ((350761 / 986078) : ℂ) * ζ ^ 16 + ((39055 / 2958234) : ℂ) * ζ ^ 17 - ((1340008 / 1479117) : ℂ) * ζ ^ 18 - ((329160 / 493039) : ℂ) * ζ ^ 19 - ((774935 / 1479117) : ℂ) * ζ ^ 20 - ((322654 / 493039) : ℂ) * ζ ^ 21 - ((1441250 / 1479117) : ℂ) * ζ ^ 22 - ((1167218 / 1479117) : ℂ) * ζ ^ 23 - ((99271 / 493039) : ℂ) * ζ ^ 24 - ((909815 / 2958234) : ℂ) * ζ ^ 25 + ((515267 / 2958234) : ℂ) * ζ ^ 26 - ((2821 / 2958234) : ℂ) * ζ ^ 27 - ((826225 / 2958234) : ℂ) * ζ ^ 28 - ((179250 / 493039) : ℂ) * ζ ^ 29 - ((84110 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep05Coefficient06 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep05CoefficientIdentity06 :
    row18_reducedY01_combinationStep05Coefficient06 =
      row18_reducedY01_combinationStep04Coefficient06 +
        row18_reducedY01_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep05Coefficient06 row18_reducedY01_combinationStep04Coefficient06 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep05Coefficient07 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep05CoefficientIdentity07 :
    row18_reducedY01_combinationStep05Coefficient07 =
      row18_reducedY01_combinationStep04Coefficient07 +
        row18_reducedY01_combinationStep05Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep05Coefficient07 row18_reducedY01_combinationStep04Coefficient07 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 (-((9232469 / 2958234) : ℂ) - ((4322698 / 1479117) : ℂ) * ζ ^ 1 - ((4309039 / 2958234) : ℂ) * ζ ^ 2 + ((1415551 / 986078) : ℂ) * ζ ^ 3 + ((3828359 / 1479117) : ℂ) * ζ ^ 4 + ((2436586 / 1479117) : ℂ) * ζ ^ 5 - ((1560611 / 986078) : ℂ) * ζ ^ 6 - ((3910888 / 1479117) : ℂ) * ζ ^ 7 - ((3061814 / 1479117) : ℂ) * ζ ^ 8 + ((233143 / 1479117) : ℂ) * ζ ^ 9 + ((2550683 / 2958234) : ℂ) * ζ ^ 10 + ((3582209 / 2958234) : ℂ) * ζ ^ 11 + ((643213 / 493039) : ℂ) * ζ ^ 12 + ((23371 / 18723) : ℂ) * ζ ^ 13 - ((231389 / 1479117) : ℂ) * ζ ^ 14 - ((5498377 / 2958234) : ℂ) * ζ ^ 15 - ((1211063 / 493039) : ℂ) * ζ ^ 16 + ((587482 / 1479117) : ℂ) * ζ ^ 17 + ((5573791 / 1479117) : ℂ) * ζ ^ 18 + ((2225224 / 493039) : ℂ) * ζ ^ 19 + ((2040040 / 1479117) : ℂ) * ζ ^ 20 - ((2079279 / 986078) : ℂ) * ζ ^ 21 - ((5255855 / 2958234) : ℂ) * ζ ^ 22 + ((530849 / 1479117) : ℂ) * ζ ^ 23 + ((1077441 / 493039) : ℂ) * ζ ^ 24 + ((1724527 / 986078) : ℂ) * ζ ^ 25 + ((607567 / 2958234) : ℂ) * ζ ^ 26 - ((1190048 / 1479117) : ℂ) * ζ ^ 27 - ((1105540 / 1479117) : ℂ) * ζ ^ 28 - ((187000 / 493039) : ℂ) * ζ ^ 29 - ((181160 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep05Coefficient08 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep05CoefficientIdentity08 :
    row18_reducedY01_combinationStep05Coefficient08 =
      row18_reducedY01_combinationStep04Coefficient08 +
        row18_reducedY01_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep05Coefficient08 row18_reducedY01_combinationStep04Coefficient08 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep05Coefficient09 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep05CoefficientIdentity09 :
    row18_reducedY01_combinationStep05Coefficient09 =
      row18_reducedY01_combinationStep04Coefficient09 +
        row18_reducedY01_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep05Coefficient09 row18_reducedY01_combinationStep04Coefficient09 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep05Coefficient10 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep05CoefficientIdentity10 :
    row18_reducedY01_combinationStep05Coefficient10 =
      row18_reducedY01_combinationStep04Coefficient10 +
        row18_reducedY01_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep05Coefficient10 row18_reducedY01_combinationStep04Coefficient10 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep05Coefficient11 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep05CoefficientIdentity11 :
    row18_reducedY01_combinationStep05Coefficient11 =
      row18_reducedY01_combinationStep04Coefficient11 +
        row18_reducedY01_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep05Coefficient11 row18_reducedY01_combinationStep04Coefficient11 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep05Coefficient12 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep05CoefficientIdentity12 :
    row18_reducedY01_combinationStep05Coefficient12 =
      row18_reducedY01_combinationStep04Coefficient12 +
        row18_reducedY01_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep05Coefficient12 row18_reducedY01_combinationStep04Coefficient12 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep05Coefficient13 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep05CoefficientIdentity13 :
    row18_reducedY01_combinationStep05Coefficient13 =
      row18_reducedY01_combinationStep04Coefficient13 +
        row18_reducedY01_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep05Coefficient13 row18_reducedY01_combinationStep04Coefficient13 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep05Coefficient14 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep05CoefficientIdentity14 :
    row18_reducedY01_combinationStep05Coefficient14 =
      row18_reducedY01_combinationStep04Coefficient14 +
        row18_reducedY01_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep05Coefficient14 row18_reducedY01_combinationStep04Coefficient14 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep05Coefficient15 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep05CoefficientIdentity15 :
    row18_reducedY01_combinationStep05Coefficient15 =
      row18_reducedY01_combinationStep04Coefficient15 +
        row18_reducedY01_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep05Coefficient15 row18_reducedY01_combinationStep04Coefficient15 row18_reducedY01_combinationStep05Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY01_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY01_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY01_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY01_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY01_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY01_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY01_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY01_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY01_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY01_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY01_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY01_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY01_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY01_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY01_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY01_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY01_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY01_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY01_combinationStep05CoefficientIdentity00,
      row18_reducedY01_combinationStep05CoefficientIdentity01,
      row18_reducedY01_combinationStep05CoefficientIdentity02,
      row18_reducedY01_combinationStep05CoefficientIdentity03,
      row18_reducedY01_combinationStep05CoefficientIdentity04,
      row18_reducedY01_combinationStep05CoefficientIdentity05,
      row18_reducedY01_combinationStep05CoefficientIdentity06,
      row18_reducedY01_combinationStep05CoefficientIdentity07,
      row18_reducedY01_combinationStep05CoefficientIdentity08,
      row18_reducedY01_combinationStep05CoefficientIdentity09,
      row18_reducedY01_combinationStep05CoefficientIdentity10,
      row18_reducedY01_combinationStep05CoefficientIdentity11,
      row18_reducedY01_combinationStep05CoefficientIdentity12,
      row18_reducedY01_combinationStep05CoefficientIdentity13,
      row18_reducedY01_combinationStep05CoefficientIdentity14,
      row18_reducedY01_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY01_combinationStep05Multiplier * equation

private def row18_reducedY01_combinationStep06Multiplier : ℂ :=
  (-((26 / 5) : ℂ) - (6 : ℂ) * ζ ^ 1 + ((12 / 5) : ℂ) * ζ ^ 2 + (2 : ℂ) * ζ ^ 3 - (4 : ℂ) * ζ ^ 5 - ((12 / 5) : ℂ) * ζ ^ 6 + ((18 / 5) : ℂ) * ζ ^ 8 + (4 : ℂ) * ζ ^ 9 + ((24 / 5) : ℂ) * ζ ^ 12 + (6 : ℂ) * ζ ^ 13 - (2 : ℂ) * ζ ^ 15 + (6 : ℂ) * ζ ^ 17 + ((14 / 5) : ℂ) * ζ ^ 18 - (2 : ℂ) * ζ ^ 21 - ((12 / 5) : ℂ) * ζ ^ 22 - ((12 / 5) : ℂ) * ζ ^ 24 - (2 : ℂ) * ζ ^ 25 - ((18 / 5) : ℂ) * ζ ^ 28 - (6 : ℂ) * ζ ^ 29 - ((6 / 5) : ℂ) * ζ ^ 30)

private def row18_reducedY01_combinationStep06Coefficient00 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity00 :
    row18_reducedY01_combinationStep06Coefficient00 =
      row18_reducedY01_combinationStep05Coefficient00 +
        row18_reducedY01_combinationStep06Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep06Coefficient00 row18_reducedY01_combinationStep05Coefficient00 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 (((82 / 79) : ℂ) + ((657 / 790) : ℂ) * ζ ^ 1 + ((399 / 158) : ℂ) * ζ ^ 2 - ((713 / 790) : ℂ) * ζ ^ 3 - ((137 / 79) : ℂ) * ζ ^ 4 + ((12 / 395) : ℂ) * ζ ^ 5 - ((119 / 790) : ℂ) * ζ ^ 6 + ((1929 / 790) : ℂ) * ζ ^ 7 + ((1843 / 790) : ℂ) * ζ ^ 8 - ((37 / 395) : ℂ) * ζ ^ 9 - ((861 / 790) : ℂ) * ζ ^ 10 - ((776 / 395) : ℂ) * ζ ^ 11 - ((9 / 10) : ℂ) * ζ ^ 12 + ((631 / 790) : ℂ) * ζ ^ 13 + ((429 / 395) : ℂ) * ζ ^ 14 + ((607 / 395) : ℂ) * ζ ^ 15 + ((71 / 790) : ℂ) * ζ ^ 16 - ((617 / 790) : ℂ) * ζ ^ 17 - ((857 / 790) : ℂ) * ζ ^ 18 - ((909 / 790) : ℂ) * ζ ^ 19 + ((42 / 395) : ℂ) * ζ ^ 20 + ((118 / 395) : ℂ) * ζ ^ 21 - ((169 / 395) : ℂ) * ζ ^ 22 - ((92 / 395) : ℂ) * ζ ^ 23 - ((323 / 790) : ℂ) * ζ ^ 24 - ((216 / 395) : ℂ) * ζ ^ 25 + ((102 / 395) : ℂ) * ζ ^ 26 + ((399 / 790) : ℂ) * ζ ^ 27 + ((129 / 395) : ℂ) * ζ ^ 28 + ((21 / 395) : ℂ) * ζ ^ 29)

private def row18_reducedY01_combinationStep06Coefficient01 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY01_combinationStep06CoefficientIdentity01 :
    row18_reducedY01_combinationStep06Coefficient01 =
      row18_reducedY01_combinationStep05Coefficient01 +
        row18_reducedY01_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep06Coefficient01 row18_reducedY01_combinationStep05Coefficient01 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep06Coefficient02 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity02 :
    row18_reducedY01_combinationStep06Coefficient02 =
      row18_reducedY01_combinationStep05Coefficient02 +
        row18_reducedY01_combinationStep06Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep06Coefficient02 row18_reducedY01_combinationStep05Coefficient02 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 (((617 / 395) : ℂ) + ((953 / 790) : ℂ) * ζ ^ 1 + ((107 / 395) : ℂ) * ζ ^ 2 + ((398 / 395) : ℂ) * ζ ^ 3 + ((46 / 395) : ℂ) * ζ ^ 4 - ((394 / 395) : ℂ) * ζ ^ 5 + ((87 / 790) : ℂ) * ζ ^ 6 - ((147 / 79) : ℂ) * ζ ^ 7 - ((703 / 790) : ℂ) * ζ ^ 8 + ((247 / 790) : ℂ) * ζ ^ 9 + ((231 / 790) : ℂ) * ζ ^ 10 + ((68 / 395) : ℂ) * ζ ^ 11 - ((909 / 790) : ℂ) * ζ ^ 12 - ((444 / 395) : ℂ) * ζ ^ 13 - ((1451 / 790) : ℂ) * ζ ^ 14 - ((1157 / 790) : ℂ) * ζ ^ 15 - ((297 / 395) : ℂ) * ζ ^ 16 + ((251 / 395) : ℂ) * ζ ^ 17 + ((1281 / 790) : ℂ) * ζ ^ 18 + ((618 / 395) : ℂ) * ζ ^ 19 + ((807 / 790) : ℂ) * ζ ^ 20 - ((119 / 790) : ℂ) * ζ ^ 21 - ((813 / 790) : ℂ) * ζ ^ 22 - ((12 / 79) : ℂ) * ζ ^ 23 + ((807 / 790) : ℂ) * ζ ^ 24 + ((618 / 395) : ℂ) * ζ ^ 25 + ((597 / 395) : ℂ) * ζ ^ 26 + ((1593 / 790) : ℂ) * ζ ^ 27 + ((702 / 395) : ℂ) * ζ ^ 28 + ((126 / 395) : ℂ) * ζ ^ 29)

private def row18_reducedY01_combinationStep06Coefficient03 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity03 :
    row18_reducedY01_combinationStep06Coefficient03 =
      row18_reducedY01_combinationStep05Coefficient03 +
        row18_reducedY01_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep06Coefficient03 row18_reducedY01_combinationStep05Coefficient03 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep06Coefficient04 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity04 :
    row18_reducedY01_combinationStep06Coefficient04 =
      row18_reducedY01_combinationStep05Coefficient04 +
        row18_reducedY01_combinationStep06Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep06Coefficient04 row18_reducedY01_combinationStep05Coefficient04 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 (-((82 / 79) : ℂ) - ((657 / 790) : ℂ) * ζ ^ 1 - ((399 / 158) : ℂ) * ζ ^ 2 + ((713 / 790) : ℂ) * ζ ^ 3 + ((137 / 79) : ℂ) * ζ ^ 4 - ((12 / 395) : ℂ) * ζ ^ 5 + ((119 / 790) : ℂ) * ζ ^ 6 - ((1929 / 790) : ℂ) * ζ ^ 7 - ((1843 / 790) : ℂ) * ζ ^ 8 + ((37 / 395) : ℂ) * ζ ^ 9 + ((861 / 790) : ℂ) * ζ ^ 10 + ((776 / 395) : ℂ) * ζ ^ 11 + ((9 / 10) : ℂ) * ζ ^ 12 - ((631 / 790) : ℂ) * ζ ^ 13 - ((429 / 395) : ℂ) * ζ ^ 14 - ((607 / 395) : ℂ) * ζ ^ 15 - ((71 / 790) : ℂ) * ζ ^ 16 + ((617 / 790) : ℂ) * ζ ^ 17 + ((857 / 790) : ℂ) * ζ ^ 18 + ((909 / 790) : ℂ) * ζ ^ 19 - ((42 / 395) : ℂ) * ζ ^ 20 - ((118 / 395) : ℂ) * ζ ^ 21 + ((169 / 395) : ℂ) * ζ ^ 22 + ((92 / 395) : ℂ) * ζ ^ 23 + ((323 / 790) : ℂ) * ζ ^ 24 + ((216 / 395) : ℂ) * ζ ^ 25 - ((102 / 395) : ℂ) * ζ ^ 26 - ((399 / 790) : ℂ) * ζ ^ 27 - ((129 / 395) : ℂ) * ζ ^ 28 - ((21 / 395) : ℂ) * ζ ^ 29)

private def row18_reducedY01_combinationStep06Coefficient05 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity05 :
    row18_reducedY01_combinationStep06Coefficient05 =
      row18_reducedY01_combinationStep05Coefficient05 +
        row18_reducedY01_combinationStep06Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY01_combinationStep06Coefficient05 row18_reducedY01_combinationStep05Coefficient05 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 (-((1037 / 790) : ℂ) - ((1391 / 790) : ℂ) * ζ ^ 1 + ((208 / 395) : ℂ) * ζ ^ 2 + ((587 / 790) : ℂ) * ζ ^ 3 + ((893 / 790) : ℂ) * ζ ^ 4 + ((47 / 158) : ℂ) * ζ ^ 5 + ((242 / 395) : ℂ) * ζ ^ 6 + ((733 / 790) : ℂ) * ζ ^ 7 + ((143 / 790) : ℂ) * ζ ^ 8 + ((641 / 395) : ℂ) * ζ ^ 9 - ((1013 / 790) : ℂ) * ζ ^ 10 - ((3093 / 790) : ℂ) * ζ ^ 11 - ((1887 / 790) : ℂ) * ζ ^ 12 + ((65 / 79) : ℂ) * ζ ^ 13 + ((1303 / 790) : ℂ) * ζ ^ 14 + ((1071 / 790) : ℂ) * ζ ^ 15 - ((927 / 395) : ℂ) * ζ ^ 16 - ((824 / 395) : ℂ) * ζ ^ 17 - ((289 / 790) : ℂ) * ζ ^ 18 + ((1053 / 790) : ℂ) * ζ ^ 19 + ((736 / 395) : ℂ) * ζ ^ 20 + ((198 / 395) : ℂ) * ζ ^ 21 - ((63 / 158) : ℂ) * ζ ^ 22 - ((339 / 790) : ℂ) * ζ ^ 23 - ((1389 / 790) : ℂ) * ζ ^ 24 - ((1293 / 790) : ℂ) * ζ ^ 25 + ((261 / 395) : ℂ) * ζ ^ 26 + ((1242 / 395) : ℂ) * ζ ^ 27 + ((1431 / 395) : ℂ) * ζ ^ 28 + ((54 / 79) : ℂ) * ζ ^ 29)

private def row18_reducedY01_combinationStep06Coefficient06 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity06 :
    row18_reducedY01_combinationStep06Coefficient06 =
      row18_reducedY01_combinationStep05Coefficient06 +
        row18_reducedY01_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep06Coefficient06 row18_reducedY01_combinationStep05Coefficient06 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep06Coefficient07 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity07 :
    row18_reducedY01_combinationStep06Coefficient07 =
      row18_reducedY01_combinationStep05Coefficient07 +
        row18_reducedY01_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep06Coefficient07 row18_reducedY01_combinationStep05Coefficient07 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep06Coefficient08 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity08 :
    row18_reducedY01_combinationStep06Coefficient08 =
      row18_reducedY01_combinationStep05Coefficient08 +
        row18_reducedY01_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep06Coefficient08 row18_reducedY01_combinationStep05Coefficient08 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep06Coefficient09 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity09 :
    row18_reducedY01_combinationStep06Coefficient09 =
      row18_reducedY01_combinationStep05Coefficient09 +
        row18_reducedY01_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep06Coefficient09 row18_reducedY01_combinationStep05Coefficient09 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep06Coefficient10 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity10 :
    row18_reducedY01_combinationStep06Coefficient10 =
      row18_reducedY01_combinationStep05Coefficient10 +
        row18_reducedY01_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep06Coefficient10 row18_reducedY01_combinationStep05Coefficient10 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep06Coefficient11 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity11 :
    row18_reducedY01_combinationStep06Coefficient11 =
      row18_reducedY01_combinationStep05Coefficient11 +
        row18_reducedY01_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep06Coefficient11 row18_reducedY01_combinationStep05Coefficient11 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep06Coefficient12 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity12 :
    row18_reducedY01_combinationStep06Coefficient12 =
      row18_reducedY01_combinationStep05Coefficient12 +
        row18_reducedY01_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep06Coefficient12 row18_reducedY01_combinationStep05Coefficient12 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep06Coefficient13 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity13 :
    row18_reducedY01_combinationStep06Coefficient13 =
      row18_reducedY01_combinationStep05Coefficient13 +
        row18_reducedY01_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep06Coefficient13 row18_reducedY01_combinationStep05Coefficient13 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep06Coefficient14 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity14 :
    row18_reducedY01_combinationStep06Coefficient14 =
      row18_reducedY01_combinationStep05Coefficient14 +
        row18_reducedY01_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep06Coefficient14 row18_reducedY01_combinationStep05Coefficient14 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY01_combinationStep06Coefficient15 : ℂ :=
  0

private theorem row18_reducedY01_combinationStep06CoefficientIdentity15 :
    row18_reducedY01_combinationStep06Coefficient15 =
      row18_reducedY01_combinationStep05Coefficient15 +
        row18_reducedY01_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY01_combinationStep06Coefficient15 row18_reducedY01_combinationStep05Coefficient15 row18_reducedY01_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY01_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY01_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY01_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY01_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY01_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY01_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY01_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY01_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY01_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY01_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY01_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY01_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY01_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY01_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY01_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY01_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY01_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY01_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY01_combinationStep06CoefficientIdentity00,
      row18_reducedY01_combinationStep06CoefficientIdentity01,
      row18_reducedY01_combinationStep06CoefficientIdentity02,
      row18_reducedY01_combinationStep06CoefficientIdentity03,
      row18_reducedY01_combinationStep06CoefficientIdentity04,
      row18_reducedY01_combinationStep06CoefficientIdentity05,
      row18_reducedY01_combinationStep06CoefficientIdentity06,
      row18_reducedY01_combinationStep06CoefficientIdentity07,
      row18_reducedY01_combinationStep06CoefficientIdentity08,
      row18_reducedY01_combinationStep06CoefficientIdentity09,
      row18_reducedY01_combinationStep06CoefficientIdentity10,
      row18_reducedY01_combinationStep06CoefficientIdentity11,
      row18_reducedY01_combinationStep06CoefficientIdentity12,
      row18_reducedY01_combinationStep06CoefficientIdentity13,
      row18_reducedY01_combinationStep06CoefficientIdentity14,
      row18_reducedY01_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY01_combinationStep06Multiplier * equation

theorem row18_reducedY01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 0 1 = 0 := by
  have reduced :=
    row18_reducedY01_combinationStep06 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY01_combinationStep06Coefficient00,
      row18_reducedY01_combinationStep06Coefficient01,
      row18_reducedY01_combinationStep06Coefficient02,
      row18_reducedY01_combinationStep06Coefficient03,
      row18_reducedY01_combinationStep06Coefficient04,
      row18_reducedY01_combinationStep06Coefficient05,
      row18_reducedY01_combinationStep06Coefficient06,
      row18_reducedY01_combinationStep06Coefficient07,
      row18_reducedY01_combinationStep06Coefficient08,
      row18_reducedY01_combinationStep06Coefficient09,
      row18_reducedY01_combinationStep06Coefficient10,
      row18_reducedY01_combinationStep06Coefficient11,
      row18_reducedY01_combinationStep06Coefficient12,
      row18_reducedY01_combinationStep06Coefficient13,
      row18_reducedY01_combinationStep06Coefficient14,
      row18_reducedY01_combinationStep06Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
