/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction06

/-!
# Ambient row 18 commutant reduction 07

This generated module checks the reduced relation `reducedY33` for
matrix coordinate (3, 3).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY33_combinationStep00Multiplier : ℂ :=
  (-((26628 / 395) : ℂ) + ((75044 / 1185) : ℂ) * ζ ^ 1 + ((21200 / 237) : ℂ) * ζ ^ 2 - ((26788 / 395) : ℂ) * ζ ^ 3 + ((136352 / 1185) : ℂ) * ζ ^ 5 + ((131432 / 1185) : ℂ) * ζ ^ 8 - ((19628 / 1185) : ℂ) * ζ ^ 9 + ((99992 / 1185) : ℂ) * ζ ^ 11 + ((28336 / 1185) : ℂ) * ζ ^ 12 - ((75044 / 1185) : ℂ) * ζ ^ 13 + ((6352 / 395) : ℂ) * ζ ^ 15 - ((75044 / 1185) : ℂ) * ζ ^ 17 - ((21200 / 237) : ℂ) * ζ ^ 18 - ((155408 / 1185) : ℂ) * ζ ^ 21 - ((21200 / 237) : ℂ) * ζ ^ 22 - ((53256 / 395) : ℂ) * ζ ^ 24 - ((20436 / 395) : ℂ) * ζ ^ 25 - ((155408 / 1185) : ℂ) * ζ ^ 27 - ((131432 / 1185) : ℂ) * ζ ^ 28 + ((75044 / 1185) : ℂ) * ζ ^ 29 - ((11240 / 237) : ℂ) * ζ ^ 30 - ((99992 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY33_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep00CoefficientIdentity00 :
    row18_reducedY33_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep00Coefficient00 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep00Coefficient01 : ℂ :=
  (((1 / 237) : ℂ) - ((998 / 237) : ℂ) * ζ ^ 1 + ((90 / 79) : ℂ) * ζ ^ 2 + ((832 / 79) : ℂ) * ζ ^ 3 - ((998 / 237) : ℂ) * ζ ^ 5 + ((271 / 237) : ℂ) * ζ ^ 6 - ((271 / 237) : ℂ) * ζ ^ 8 + ((998 / 237) : ℂ) * ζ ^ 9 - ((416 / 79) : ℂ) * ζ ^ 11 + ((155 / 79) : ℂ) * ζ ^ 12 + ((998 / 237) : ℂ) * ζ ^ 13 - ((622 / 237) : ℂ) * ζ ^ 15 + ((998 / 237) : ℂ) * ζ ^ 17 + ((953 / 237) : ℂ) * ζ ^ 18 - ((80 / 237) : ℂ) * ζ ^ 21 - ((90 / 79) : ℂ) * ζ ^ 22 + ((408 / 79) : ℂ) * ζ ^ 24 + ((1874 / 237) : ℂ) * ζ ^ 27 + ((271 / 237) : ℂ) * ζ ^ 28 - ((998 / 237) : ℂ) * ζ ^ 29 + ((736 / 237) : ℂ) * ζ ^ 30 + ((416 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep00CoefficientIdentity01 :
    row18_reducedY33_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep00Coefficient01 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 (-((1677959 / 93615) : ℂ) + ((358079 / 18723) : ℂ) * ζ ^ 1 + ((93965 / 6241) : ℂ) * ζ ^ 2 - ((321916 / 18723) : ℂ) * ζ ^ 3 + ((532628 / 18723) : ℂ) * ζ ^ 4 + ((693676 / 31205) : ℂ) * ζ ^ 5 - ((1817963 / 93615) : ℂ) * ζ ^ 6 + ((371512 / 93615) : ℂ) * ζ ^ 7 + ((483214 / 31205) : ℂ) * ζ ^ 8 - ((346893 / 31205) : ℂ) * ζ ^ 9 - ((22837 / 1185) : ℂ) * ζ ^ 10 - ((1900036 / 93615) : ℂ) * ζ ^ 11 + ((1629392 / 93615) : ℂ) * ζ ^ 12 - ((215702 / 18723) : ℂ) * ζ ^ 13 - ((1152329 / 31205) : ℂ) * ζ ^ 14 - ((103081 / 93615) : ℂ) * ζ ^ 15 + ((134134 / 93615) : ℂ) * ζ ^ 16 - ((233344 / 31205) : ℂ) * ζ ^ 17 + ((145847 / 93615) : ℂ) * ζ ^ 18 - ((809066 / 93615) : ℂ) * ζ ^ 19 - ((1647976 / 93615) : ℂ) * ζ ^ 20 + ((27707 / 31205) : ℂ) * ζ ^ 21 + ((921746 / 93615) : ℂ) * ζ ^ 22 - ((341416 / 31205) : ℂ) * ζ ^ 23 - ((151156 / 6241) : ℂ) * ζ ^ 24 + ((38612 / 18723) : ℂ) * ζ ^ 25 + ((1561603 / 93615) : ℂ) * ζ ^ 26 + ((1614521 / 93615) : ℂ) * ζ ^ 27 - ((376016 / 18723) : ℂ) * ζ ^ 28 + ((280454 / 93615) : ℂ) * ζ ^ 29 + ((1699864 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep00Coefficient02 : ℂ :=
  (((1055 / 237) : ℂ) + ((232 / 237) : ℂ) * ζ ^ 1 - ((134 / 79) : ℂ) * ζ ^ 2 + ((123 / 79) : ℂ) * ζ ^ 3 - ((2048 / 237) : ℂ) * ζ ^ 5 + ((194 / 79) : ℂ) * ζ ^ 6 - ((422 / 79) : ℂ) * ζ ^ 8 - ((1256 / 237) : ℂ) * ζ ^ 9 - ((2512 / 237) : ℂ) * ζ ^ 11 - ((328 / 79) : ℂ) * ζ ^ 12 - ((232 / 237) : ℂ) * ζ ^ 13 - ((123 / 79) : ℂ) * ζ ^ 15 - ((232 / 237) : ℂ) * ζ ^ 17 - ((653 / 237) : ℂ) * ζ ^ 18 + ((760 / 79) : ℂ) * ζ ^ 21 + ((134 / 79) : ℂ) * ζ ^ 22 + ((134 / 79) : ℂ) * ζ ^ 24 + ((760 / 79) : ℂ) * ζ ^ 25 + ((2512 / 237) : ℂ) * ζ ^ 27 + ((422 / 79) : ℂ) * ζ ^ 28 + ((232 / 237) : ℂ) * ζ ^ 29 + ((288 / 79) : ℂ) * ζ ^ 30 + ((2512 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep00CoefficientIdentity02 :
    row18_reducedY33_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep00Coefficient02 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 (-((2054347 / 93615) : ℂ) + ((395713 / 31205) : ℂ) * ζ ^ 1 + ((632223 / 31205) : ℂ) * ζ ^ 2 - ((110513 / 31205) : ℂ) * ζ ^ 3 + ((448780 / 18723) : ℂ) * ζ ^ 4 + ((365981 / 31205) : ℂ) * ζ ^ 5 - ((1420912 / 93615) : ℂ) * ζ ^ 6 + ((565634 / 31205) : ℂ) * ζ ^ 7 + ((328429 / 18723) : ℂ) * ζ ^ 8 - ((464611 / 93615) : ℂ) * ζ ^ 9 - ((530521 / 93615) : ℂ) * ζ ^ 10 - ((270302 / 93615) : ℂ) * ζ ^ 11 - ((3780 / 6241) : ℂ) * ζ ^ 12 - ((706736 / 93615) : ℂ) * ζ ^ 13 - ((1491631 / 93615) : ℂ) * ζ ^ 14 + ((210196 / 93615) : ℂ) * ζ ^ 15 - ((184730 / 18723) : ℂ) * ζ ^ 16 - ((436852 / 31205) : ℂ) * ζ ^ 17 - ((68555 / 6241) : ℂ) * ζ ^ 18 - ((509558 / 93615) : ℂ) * ζ ^ 19 - ((30544 / 31205) : ℂ) * ζ ^ 20 - ((665866 / 93615) : ℂ) * ζ ^ 21 - ((14751 / 31205) : ℂ) * ζ ^ 22 - ((232252 / 18723) : ℂ) * ζ ^ 23 - ((2096029 / 93615) : ℂ) * ζ ^ 24 + ((44655 / 6241) : ℂ) * ζ ^ 25 + ((106849 / 93615) : ℂ) * ζ ^ 26 - ((114747 / 6241) : ℂ) * ζ ^ 27 - ((227039 / 93615) : ℂ) * ζ ^ 28 + ((295232 / 31205) : ℂ) * ζ ^ 29 + ((24998 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep00CoefficientIdentity03 :
    row18_reducedY33_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep00Coefficient03 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep00CoefficientIdentity04 :
    row18_reducedY33_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep00Coefficient04 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep00CoefficientIdentity05 :
    row18_reducedY33_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep00Coefficient05 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep00CoefficientIdentity06 :
    row18_reducedY33_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep00Coefficient06 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep00CoefficientIdentity07 :
    row18_reducedY33_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep00Coefficient07 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep00CoefficientIdentity08 :
    row18_reducedY33_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep00Coefficient08 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep00CoefficientIdentity09 :
    row18_reducedY33_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep00Coefficient09 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep00CoefficientIdentity10 :
    row18_reducedY33_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep00Coefficient10 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep00CoefficientIdentity11 :
    row18_reducedY33_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep00Coefficient11 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep00CoefficientIdentity12 :
    row18_reducedY33_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep00Coefficient12 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep00CoefficientIdentity13 :
    row18_reducedY33_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep00Coefficient13 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep00CoefficientIdentity14 :
    row18_reducedY33_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep00Coefficient14 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep00CoefficientIdentity15 :
    row18_reducedY33_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY33_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep00Coefficient15 row18_reducedY33_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY33_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY33_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY33_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY33_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY33_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY33_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY33_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY33_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY33_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY33_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY33_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY33_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY33_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY33_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY33_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY33_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY33_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY33_combinationStep00CoefficientIdentity00,
      row18_reducedY33_combinationStep00CoefficientIdentity01,
      row18_reducedY33_combinationStep00CoefficientIdentity02,
      row18_reducedY33_combinationStep00CoefficientIdentity03,
      row18_reducedY33_combinationStep00CoefficientIdentity04,
      row18_reducedY33_combinationStep00CoefficientIdentity05,
      row18_reducedY33_combinationStep00CoefficientIdentity06,
      row18_reducedY33_combinationStep00CoefficientIdentity07,
      row18_reducedY33_combinationStep00CoefficientIdentity08,
      row18_reducedY33_combinationStep00CoefficientIdentity09,
      row18_reducedY33_combinationStep00CoefficientIdentity10,
      row18_reducedY33_combinationStep00CoefficientIdentity11,
      row18_reducedY33_combinationStep00CoefficientIdentity12,
      row18_reducedY33_combinationStep00CoefficientIdentity13,
      row18_reducedY33_combinationStep00CoefficientIdentity14,
      row18_reducedY33_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY33_combinationStep00Multiplier * equation

private def row18_reducedY33_combinationStep01Multiplier : ℂ :=
  (-((4132 / 1185) : ℂ) - ((1196 / 237) : ℂ) * ζ ^ 1 + ((5704 / 1185) : ℂ) * ζ ^ 2 + ((908 / 237) : ℂ) * ζ ^ 5 + ((9836 / 1185) : ℂ) * ζ ^ 6 + ((9836 / 1185) : ℂ) * ζ ^ 8 + ((908 / 237) : ℂ) * ζ ^ 9 + ((3524 / 237) : ℂ) * ζ ^ 11 + ((5316 / 395) : ℂ) * ζ ^ 12 + ((1196 / 237) : ℂ) * ζ ^ 13 + ((1076 / 237) : ℂ) * ζ ^ 15 + ((1196 / 237) : ℂ) * ζ ^ 17 + ((2408 / 1185) : ℂ) * ζ ^ 18 + ((48 / 79) : ℂ) * ζ ^ 21 - ((5704 / 1185) : ℂ) * ζ ^ 22 - ((12244 / 1185) : ℂ) * ζ ^ 24 - ((2104 / 237) : ℂ) * ζ ^ 25 - ((1076 / 237) : ℂ) * ζ ^ 27 - ((9836 / 1185) : ℂ) * ζ ^ 28 - ((1196 / 237) : ℂ) * ζ ^ 29 - ((6112 / 1185) : ℂ) * ζ ^ 30 - ((3524 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY33_combinationStep01Coefficient00 : ℂ :=
  (((847 / 237) : ℂ) + ((161 / 79) : ℂ) * ζ ^ 1 - ((48 / 79) : ℂ) * ζ ^ 2 - ((967 / 237) : ℂ) * ζ ^ 3 + ((457 / 237) : ℂ) * ζ ^ 5 + ((496 / 237) : ℂ) * ζ ^ 6 - ((344 / 237) : ℂ) * ζ ^ 8 - ((368 / 237) : ℂ) * ζ ^ 9 + ((599 / 237) : ℂ) * ζ ^ 11 - ((344 / 237) : ℂ) * ζ ^ 12 - ((161 / 79) : ℂ) * ζ ^ 13 + ((941 / 237) : ℂ) * ζ ^ 15 - ((161 / 79) : ℂ) * ζ ^ 17 - ((640 / 237) : ℂ) * ζ ^ 18 + ((484 / 237) : ℂ) * ζ ^ 21 + ((48 / 79) : ℂ) * ζ ^ 22 + ((26 / 237) : ℂ) * ζ ^ 25 - ((484 / 237) : ℂ) * ζ ^ 27 + ((344 / 237) : ℂ) * ζ ^ 28 + ((161 / 79) : ℂ) * ζ ^ 29 + ((248 / 237) : ℂ) * ζ ^ 30 - ((599 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep01CoefficientIdentity00 :
    row18_reducedY33_combinationStep01Coefficient00 =
      row18_reducedY33_combinationStep00Coefficient00 +
        row18_reducedY33_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep01Coefficient00 row18_reducedY33_combinationStep00Coefficient00 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 (-((249859 / 93615) : ℂ) - ((54766 / 93615) : ℂ) * ζ ^ 1 - ((1099 / 18723) : ℂ) * ζ ^ 2 + ((77893 / 18723) : ℂ) * ζ ^ 3 + ((11033 / 6241) : ℂ) * ζ ^ 4 - ((36919 / 18723) : ℂ) * ζ ^ 5 - ((79091 / 18723) : ℂ) * ζ ^ 6 - ((147859 / 31205) : ℂ) * ζ ^ 7 - ((122106 / 31205) : ℂ) * ζ ^ 8 + ((32099 / 31205) : ℂ) * ζ ^ 9 + ((18230 / 6241) : ℂ) * ζ ^ 10 - ((8426 / 31205) : ℂ) * ζ ^ 11 - ((133003 / 93615) : ℂ) * ζ ^ 12 - ((284438 / 93615) : ℂ) * ζ ^ 13 - ((21583 / 18723) : ℂ) * ζ ^ 14 + ((140843 / 93615) : ℂ) * ζ ^ 15 + ((164128 / 93615) : ℂ) * ζ ^ 16 + ((280303 / 93615) : ℂ) * ζ ^ 17 + ((12968 / 18723) : ℂ) * ζ ^ 18 + ((84029 / 93615) : ℂ) * ζ ^ 19 - ((31897 / 93615) : ℂ) * ζ ^ 20 - ((139762 / 93615) : ℂ) * ζ ^ 21 - ((23024 / 18723) : ℂ) * ζ ^ 22 - ((7936 / 18723) : ℂ) * ζ ^ 23 + ((14276 / 6241) : ℂ) * ζ ^ 24 + ((83874 / 31205) : ℂ) * ζ ^ 25 + ((31645 / 18723) : ℂ) * ζ ^ 26 + ((211319 / 93615) : ℂ) * ζ ^ 27 - ((6416 / 93615) : ℂ) * ζ ^ 28 - ((9457 / 6241) : ℂ) * ζ ^ 29 - ((4405 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep01Coefficient01 : ℂ :=
  (((108 / 79) : ℂ) - ((2197 / 237) : ℂ) * ζ ^ 1 - ((128 / 237) : ℂ) * ζ ^ 2 + ((2738 / 237) : ℂ) * ζ ^ 3 - ((2197 / 237) : ℂ) * ζ ^ 5 + ((196 / 237) : ℂ) * ζ ^ 6 - ((196 / 237) : ℂ) * ζ ^ 8 + ((2197 / 237) : ℂ) * ζ ^ 9 - ((1369 / 237) : ℂ) * ζ ^ 11 + ((342 / 79) : ℂ) * ζ ^ 12 + ((2197 / 237) : ℂ) * ζ ^ 13 - ((170 / 79) : ℂ) * ζ ^ 15 + ((2197 / 237) : ℂ) * ζ ^ 17 + ((2099 / 237) : ℂ) * ζ ^ 18 + ((640 / 79) : ℂ) * ζ ^ 21 + ((128 / 237) : ℂ) * ζ ^ 22 + ((765 / 79) : ℂ) * ζ ^ 24 + ((2228 / 237) : ℂ) * ζ ^ 27 + ((196 / 237) : ℂ) * ζ ^ 28 - ((2197 / 237) : ℂ) * ζ ^ 29 + ((1222 / 237) : ℂ) * ζ ^ 30 + ((1369 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep01CoefficientIdentity01 :
    row18_reducedY33_combinationStep01Coefficient01 =
      row18_reducedY33_combinationStep00Coefficient01 +
        row18_reducedY33_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep01Coefficient01 row18_reducedY33_combinationStep00Coefficient01 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 (-((94529 / 93615) : ℂ) + ((544171 / 93615) : ℂ) * ζ ^ 1 + ((316979 / 93615) : ℂ) * ζ ^ 2 + ((66726 / 31205) : ℂ) * ζ ^ 3 - ((10496 / 31205) : ℂ) * ζ ^ 4 - ((50618 / 18723) : ℂ) * ζ ^ 5 - ((149274 / 31205) : ℂ) * ζ ^ 6 - ((389633 / 93615) : ℂ) * ζ ^ 7 - ((584999 / 93615) : ℂ) * ζ ^ 8 - ((619697 / 93615) : ℂ) * ζ ^ 9 - ((81544 / 93615) : ℂ) * ζ ^ 10 + ((63914 / 31205) : ℂ) * ζ ^ 11 - ((10520 / 18723) : ℂ) * ζ ^ 12 - ((214258 / 93615) : ℂ) * ζ ^ 13 - ((399766 / 93615) : ℂ) * ζ ^ 14 - ((23892 / 6241) : ℂ) * ζ ^ 15 - ((72439 / 93615) : ℂ) * ζ ^ 16 + ((166514 / 93615) : ℂ) * ζ ^ 17 - ((215624 / 93615) : ℂ) * ζ ^ 18 - ((274171 / 93615) : ℂ) * ζ ^ 19 + ((52688 / 93615) : ℂ) * ζ ^ 20 - ((234229 / 31205) : ℂ) * ζ ^ 21 - ((68182 / 93615) : ℂ) * ζ ^ 22 + ((77899 / 18723) : ℂ) * ζ ^ 23 + ((62123 / 18723) : ℂ) * ζ ^ 24 + ((269246 / 93615) : ℂ) * ζ ^ 25 + ((20757 / 6241) : ℂ) * ζ ^ 26 - ((18256 / 93615) : ℂ) * ζ ^ 27 + ((6126 / 31205) : ℂ) * ζ ^ 28 - ((148504 / 93615) : ℂ) * ζ ^ 29 - ((24668 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep01Coefficient02 : ℂ :=
  (((1055 / 237) : ℂ) + ((232 / 237) : ℂ) * ζ ^ 1 - ((134 / 79) : ℂ) * ζ ^ 2 + ((123 / 79) : ℂ) * ζ ^ 3 - ((2048 / 237) : ℂ) * ζ ^ 5 + ((194 / 79) : ℂ) * ζ ^ 6 - ((422 / 79) : ℂ) * ζ ^ 8 - ((1256 / 237) : ℂ) * ζ ^ 9 - ((2512 / 237) : ℂ) * ζ ^ 11 - ((328 / 79) : ℂ) * ζ ^ 12 - ((232 / 237) : ℂ) * ζ ^ 13 - ((123 / 79) : ℂ) * ζ ^ 15 - ((232 / 237) : ℂ) * ζ ^ 17 - ((653 / 237) : ℂ) * ζ ^ 18 + ((760 / 79) : ℂ) * ζ ^ 21 + ((134 / 79) : ℂ) * ζ ^ 22 + ((134 / 79) : ℂ) * ζ ^ 24 + ((760 / 79) : ℂ) * ζ ^ 25 + ((2512 / 237) : ℂ) * ζ ^ 27 + ((422 / 79) : ℂ) * ζ ^ 28 + ((232 / 237) : ℂ) * ζ ^ 29 + ((288 / 79) : ℂ) * ζ ^ 30 + ((2512 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep01CoefficientIdentity02 :
    row18_reducedY33_combinationStep01Coefficient02 =
      row18_reducedY33_combinationStep00Coefficient02 +
        row18_reducedY33_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep01Coefficient02 row18_reducedY33_combinationStep00Coefficient02 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep01Coefficient03 : ℂ :=
  (-((847 / 237) : ℂ) - ((161 / 79) : ℂ) * ζ ^ 1 + ((48 / 79) : ℂ) * ζ ^ 2 + ((967 / 237) : ℂ) * ζ ^ 3 - ((457 / 237) : ℂ) * ζ ^ 5 - ((496 / 237) : ℂ) * ζ ^ 6 + ((344 / 237) : ℂ) * ζ ^ 8 + ((368 / 237) : ℂ) * ζ ^ 9 - ((599 / 237) : ℂ) * ζ ^ 11 + ((344 / 237) : ℂ) * ζ ^ 12 + ((161 / 79) : ℂ) * ζ ^ 13 - ((941 / 237) : ℂ) * ζ ^ 15 + ((161 / 79) : ℂ) * ζ ^ 17 + ((640 / 237) : ℂ) * ζ ^ 18 - ((484 / 237) : ℂ) * ζ ^ 21 - ((48 / 79) : ℂ) * ζ ^ 22 - ((26 / 237) : ℂ) * ζ ^ 25 + ((484 / 237) : ℂ) * ζ ^ 27 - ((344 / 237) : ℂ) * ζ ^ 28 - ((161 / 79) : ℂ) * ζ ^ 29 - ((248 / 237) : ℂ) * ζ ^ 30 + ((599 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep01CoefficientIdentity03 :
    row18_reducedY33_combinationStep01Coefficient03 =
      row18_reducedY33_combinationStep00Coefficient03 +
        row18_reducedY33_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep01Coefficient03 row18_reducedY33_combinationStep00Coefficient03 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 (((249859 / 93615) : ℂ) + ((54766 / 93615) : ℂ) * ζ ^ 1 + ((1099 / 18723) : ℂ) * ζ ^ 2 - ((77893 / 18723) : ℂ) * ζ ^ 3 - ((11033 / 6241) : ℂ) * ζ ^ 4 + ((36919 / 18723) : ℂ) * ζ ^ 5 + ((79091 / 18723) : ℂ) * ζ ^ 6 + ((147859 / 31205) : ℂ) * ζ ^ 7 + ((122106 / 31205) : ℂ) * ζ ^ 8 - ((32099 / 31205) : ℂ) * ζ ^ 9 - ((18230 / 6241) : ℂ) * ζ ^ 10 + ((8426 / 31205) : ℂ) * ζ ^ 11 + ((133003 / 93615) : ℂ) * ζ ^ 12 + ((284438 / 93615) : ℂ) * ζ ^ 13 + ((21583 / 18723) : ℂ) * ζ ^ 14 - ((140843 / 93615) : ℂ) * ζ ^ 15 - ((164128 / 93615) : ℂ) * ζ ^ 16 - ((280303 / 93615) : ℂ) * ζ ^ 17 - ((12968 / 18723) : ℂ) * ζ ^ 18 - ((84029 / 93615) : ℂ) * ζ ^ 19 + ((31897 / 93615) : ℂ) * ζ ^ 20 + ((139762 / 93615) : ℂ) * ζ ^ 21 + ((23024 / 18723) : ℂ) * ζ ^ 22 + ((7936 / 18723) : ℂ) * ζ ^ 23 - ((14276 / 6241) : ℂ) * ζ ^ 24 - ((83874 / 31205) : ℂ) * ζ ^ 25 - ((31645 / 18723) : ℂ) * ζ ^ 26 - ((211319 / 93615) : ℂ) * ζ ^ 27 + ((6416 / 93615) : ℂ) * ζ ^ 28 + ((9457 / 6241) : ℂ) * ζ ^ 29 + ((4405 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep01CoefficientIdentity04 :
    row18_reducedY33_combinationStep01Coefficient04 =
      row18_reducedY33_combinationStep00Coefficient04 +
        row18_reducedY33_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep01Coefficient04 row18_reducedY33_combinationStep00Coefficient04 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep01CoefficientIdentity05 :
    row18_reducedY33_combinationStep01Coefficient05 =
      row18_reducedY33_combinationStep00Coefficient05 +
        row18_reducedY33_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep01Coefficient05 row18_reducedY33_combinationStep00Coefficient05 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep01CoefficientIdentity06 :
    row18_reducedY33_combinationStep01Coefficient06 =
      row18_reducedY33_combinationStep00Coefficient06 +
        row18_reducedY33_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep01Coefficient06 row18_reducedY33_combinationStep00Coefficient06 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep01CoefficientIdentity07 :
    row18_reducedY33_combinationStep01Coefficient07 =
      row18_reducedY33_combinationStep00Coefficient07 +
        row18_reducedY33_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep01Coefficient07 row18_reducedY33_combinationStep00Coefficient07 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep01CoefficientIdentity08 :
    row18_reducedY33_combinationStep01Coefficient08 =
      row18_reducedY33_combinationStep00Coefficient08 +
        row18_reducedY33_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep01Coefficient08 row18_reducedY33_combinationStep00Coefficient08 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep01CoefficientIdentity09 :
    row18_reducedY33_combinationStep01Coefficient09 =
      row18_reducedY33_combinationStep00Coefficient09 +
        row18_reducedY33_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep01Coefficient09 row18_reducedY33_combinationStep00Coefficient09 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep01CoefficientIdentity10 :
    row18_reducedY33_combinationStep01Coefficient10 =
      row18_reducedY33_combinationStep00Coefficient10 +
        row18_reducedY33_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep01Coefficient10 row18_reducedY33_combinationStep00Coefficient10 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep01CoefficientIdentity11 :
    row18_reducedY33_combinationStep01Coefficient11 =
      row18_reducedY33_combinationStep00Coefficient11 +
        row18_reducedY33_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep01Coefficient11 row18_reducedY33_combinationStep00Coefficient11 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep01CoefficientIdentity12 :
    row18_reducedY33_combinationStep01Coefficient12 =
      row18_reducedY33_combinationStep00Coefficient12 +
        row18_reducedY33_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep01Coefficient12 row18_reducedY33_combinationStep00Coefficient12 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep01CoefficientIdentity13 :
    row18_reducedY33_combinationStep01Coefficient13 =
      row18_reducedY33_combinationStep00Coefficient13 +
        row18_reducedY33_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep01Coefficient13 row18_reducedY33_combinationStep00Coefficient13 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep01CoefficientIdentity14 :
    row18_reducedY33_combinationStep01Coefficient14 =
      row18_reducedY33_combinationStep00Coefficient14 +
        row18_reducedY33_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep01Coefficient14 row18_reducedY33_combinationStep00Coefficient14 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep01CoefficientIdentity15 :
    row18_reducedY33_combinationStep01Coefficient15 =
      row18_reducedY33_combinationStep00Coefficient15 +
        row18_reducedY33_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep01Coefficient15 row18_reducedY33_combinationStep00Coefficient15 row18_reducedY33_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY33_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY33_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY33_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY33_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY33_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY33_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY33_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY33_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY33_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY33_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY33_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY33_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY33_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY33_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY33_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY33_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY33_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY33_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY33_combinationStep01CoefficientIdentity00,
      row18_reducedY33_combinationStep01CoefficientIdentity01,
      row18_reducedY33_combinationStep01CoefficientIdentity02,
      row18_reducedY33_combinationStep01CoefficientIdentity03,
      row18_reducedY33_combinationStep01CoefficientIdentity04,
      row18_reducedY33_combinationStep01CoefficientIdentity05,
      row18_reducedY33_combinationStep01CoefficientIdentity06,
      row18_reducedY33_combinationStep01CoefficientIdentity07,
      row18_reducedY33_combinationStep01CoefficientIdentity08,
      row18_reducedY33_combinationStep01CoefficientIdentity09,
      row18_reducedY33_combinationStep01CoefficientIdentity10,
      row18_reducedY33_combinationStep01CoefficientIdentity11,
      row18_reducedY33_combinationStep01CoefficientIdentity12,
      row18_reducedY33_combinationStep01CoefficientIdentity13,
      row18_reducedY33_combinationStep01CoefficientIdentity14,
      row18_reducedY33_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY33_combinationStep01Multiplier * equation

private def row18_reducedY33_combinationStep02Multiplier : ℂ :=
  (-((4396 / 237) : ℂ) - ((1792 / 1185) : ℂ) * ζ ^ 1 - ((2788 / 237) : ℂ) * ζ ^ 2 + ((2556 / 395) : ℂ) * ζ ^ 3 - ((16756 / 1185) : ℂ) * ζ ^ 5 - ((6232 / 237) : ℂ) * ζ ^ 6 - ((740 / 237) : ℂ) * ζ ^ 8 - ((4172 / 395) : ℂ) * ζ ^ 9 - ((6728 / 395) : ℂ) * ζ ^ 11 - ((740 / 237) : ℂ) * ζ ^ 12 + ((1792 / 1185) : ℂ) * ζ ^ 13 - ((7544 / 395) : ℂ) * ζ ^ 15 + ((1792 / 1185) : ℂ) * ζ ^ 17 + ((1148 / 79) : ℂ) * ζ ^ 18 - ((5876 / 1185) : ℂ) * ζ ^ 21 + ((2788 / 237) : ℂ) * ζ ^ 22 + ((4988 / 395) : ℂ) * ζ ^ 25 + ((5876 / 1185) : ℂ) * ζ ^ 27 + ((740 / 237) : ℂ) * ζ ^ 28 - ((1792 / 1185) : ℂ) * ζ ^ 29 - ((3116 / 237) : ℂ) * ζ ^ 30 + ((6728 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY33_combinationStep02Coefficient00 : ℂ :=
  (((22684 / 6241) : ℂ) - ((135419 / 93615) : ℂ) * ζ ^ 1 + ((508013 / 93615) : ℂ) * ζ ^ 2 - ((80489 / 93615) : ℂ) * ζ ^ 3 + ((410528 / 93615) : ℂ) * ζ ^ 5 + ((755522 / 93615) : ℂ) * ζ ^ 6 + ((26005 / 6241) : ℂ) * ζ ^ 8 + ((588478 / 93615) : ℂ) * ζ ^ 9 + ((222989 / 31205) : ℂ) * ζ ^ 11 + ((26005 / 6241) : ℂ) * ζ ^ 12 + ((135419 / 93615) : ℂ) * ζ ^ 13 + ((208812 / 31205) : ℂ) * ζ ^ 15 + ((135419 / 93615) : ℂ) * ζ ^ 17 - ((82503 / 31205) : ℂ) * ζ ^ 18 + ((215908 / 93615) : ℂ) * ζ ^ 21 - ((508013 / 93615) : ℂ) * ζ ^ 22 - ((545947 / 93615) : ℂ) * ζ ^ 25 - ((215908 / 93615) : ℂ) * ζ ^ 27 - ((26005 / 6241) : ℂ) * ζ ^ 28 - ((135419 / 93615) : ℂ) * ζ ^ 29 + ((377761 / 93615) : ℂ) * ζ ^ 30 - ((222989 / 31205) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep02CoefficientIdentity00 :
    row18_reducedY33_combinationStep02Coefficient00 =
      row18_reducedY33_combinationStep01Coefficient00 +
        row18_reducedY33_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep02Coefficient00 row18_reducedY33_combinationStep01Coefficient00 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 (((12049 / 18723) : ℂ) + ((54227 / 18723) : ℂ) * ζ ^ 1 - ((60926 / 93615) : ℂ) * ζ ^ 2 - ((67145 / 18723) : ℂ) * ζ ^ 3 + ((256171 / 93615) : ℂ) * ζ ^ 4 - ((34426 / 6241) : ℂ) * ζ ^ 5 - ((263089 / 93615) : ℂ) * ζ ^ 6 + ((686651 / 93615) : ℂ) * ζ ^ 7 - ((234482 / 93615) : ℂ) * ζ ^ 8 - ((216739 / 93615) : ℂ) * ζ ^ 9 + ((270287 / 93615) : ℂ) * ζ ^ 10 - ((326443 / 93615) : ℂ) * ζ ^ 11 - ((241669 / 93615) : ℂ) * ζ ^ 12 + ((179848 / 31205) : ℂ) * ζ ^ 13 - ((534968 / 93615) : ℂ) * ζ ^ 14 + ((79607 / 31205) : ℂ) * ζ ^ 15 + ((612137 / 93615) : ℂ) * ζ ^ 16 - ((420407 / 93615) : ℂ) * ζ ^ 17 + ((214498 / 93615) : ℂ) * ζ ^ 18 + ((91153 / 93615) : ℂ) * ζ ^ 19 - ((150152 / 31205) : ℂ) * ζ ^ 20 + ((287533 / 93615) : ℂ) * ζ ^ 21 - ((85309 / 93615) : ℂ) * ζ ^ 22 - ((16759 / 93615) : ℂ) * ζ ^ 23 + ((14032 / 18723) : ℂ) * ζ ^ 24 + ((28994 / 31205) : ℂ) * ζ ^ 25 + ((44039 / 31205) : ℂ) * ζ ^ 26 - ((199337 / 93615) : ℂ) * ζ ^ 27 + ((111554 / 93615) : ℂ) * ζ ^ 28 - ((135266 / 93615) : ℂ) * ζ ^ 29 + ((23548 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep02Coefficient01 : ℂ :=
  (-((100492 / 6241) : ℂ) + ((43732 / 6241) : ℂ) * ζ ^ 1 + ((23988 / 6241) : ℂ) * ζ ^ 2 - ((90250 / 18723) : ℂ) * ζ ^ 3 + ((43732 / 6241) : ℂ) * ζ ^ 5 - ((76504 / 6241) : ℂ) * ζ ^ 6 + ((76504 / 6241) : ℂ) * ζ ^ 8 - ((43732 / 6241) : ℂ) * ζ ^ 9 + ((45125 / 18723) : ℂ) * ζ ^ 11 + ((27400 / 18723) : ℂ) * ζ ^ 12 - ((43732 / 6241) : ℂ) * ζ ^ 13 - ((153487 / 18723) : ℂ) * ζ ^ 15 - ((43732 / 6241) : ℂ) * ζ ^ 17 - ((52865 / 18723) : ℂ) * ζ ^ 18 - ((348490 / 18723) : ℂ) * ζ ^ 21 - ((23988 / 6241) : ℂ) * ζ ^ 22 - ((282377 / 18723) : ℂ) * ζ ^ 24 - ((243737 / 18723) : ℂ) * ζ ^ 27 - ((76504 / 6241) : ℂ) * ζ ^ 28 + ((43732 / 6241) : ℂ) * ζ ^ 29 - ((202112 / 18723) : ℂ) * ζ ^ 30 - ((45125 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep02CoefficientIdentity01 :
    row18_reducedY33_combinationStep02Coefficient01 =
      row18_reducedY33_combinationStep01Coefficient01 +
        row18_reducedY33_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep02Coefficient01 row18_reducedY33_combinationStep01Coefficient01 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 (((83747 / 6241) : ℂ) - ((362544 / 31205) : ℂ) * ζ ^ 1 - ((44148 / 6241) : ℂ) * ζ ^ 2 + ((1814356 / 93615) : ℂ) * ζ ^ 3 - ((1462163 / 93615) : ℂ) * ζ ^ 4 - ((331486 / 93615) : ℂ) * ζ ^ 5 + ((1365067 / 93615) : ℂ) * ζ ^ 6 - ((309542 / 31205) : ℂ) * ζ ^ 7 - ((11831 / 93615) : ℂ) * ζ ^ 8 + ((246572 / 18723) : ℂ) * ζ ^ 9 - ((517612 / 93615) : ℂ) * ζ ^ 10 - ((92349 / 31205) : ℂ) * ζ ^ 11 + ((1513066 / 93615) : ℂ) * ζ ^ 12 - ((49215 / 6241) : ℂ) * ζ ^ 13 + ((28760 / 18723) : ℂ) * ζ ^ 14 + ((365811 / 31205) : ℂ) * ζ ^ 15 - ((33328 / 6241) : ℂ) * ζ ^ 16 + ((470827 / 93615) : ℂ) * ζ ^ 17 + ((307051 / 31205) : ℂ) * ζ ^ 18 - ((1109782 / 93615) : ℂ) * ζ ^ 19 + ((205011 / 31205) : ℂ) * ζ ^ 20 + ((525629 / 93615) : ℂ) * ζ ^ 21 - ((109565 / 18723) : ℂ) * ζ ^ 22 + ((70658 / 31205) : ℂ) * ζ ^ 23 + ((212466 / 31205) : ℂ) * ζ ^ 24 - ((287252 / 93615) : ℂ) * ζ ^ 25 - ((73971 / 31205) : ℂ) * ζ ^ 26 + ((712496 / 93615) : ℂ) * ζ ^ 27 - ((645064 / 93615) : ℂ) * ζ ^ 28 + ((221849 / 93615) : ℂ) * ζ ^ 29 + ((21866 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep02Coefficient02 : ℂ :=
  (((1055 / 237) : ℂ) + ((232 / 237) : ℂ) * ζ ^ 1 - ((134 / 79) : ℂ) * ζ ^ 2 + ((123 / 79) : ℂ) * ζ ^ 3 - ((2048 / 237) : ℂ) * ζ ^ 5 + ((194 / 79) : ℂ) * ζ ^ 6 - ((422 / 79) : ℂ) * ζ ^ 8 - ((1256 / 237) : ℂ) * ζ ^ 9 - ((2512 / 237) : ℂ) * ζ ^ 11 - ((328 / 79) : ℂ) * ζ ^ 12 - ((232 / 237) : ℂ) * ζ ^ 13 - ((123 / 79) : ℂ) * ζ ^ 15 - ((232 / 237) : ℂ) * ζ ^ 17 - ((653 / 237) : ℂ) * ζ ^ 18 + ((760 / 79) : ℂ) * ζ ^ 21 + ((134 / 79) : ℂ) * ζ ^ 22 + ((134 / 79) : ℂ) * ζ ^ 24 + ((760 / 79) : ℂ) * ζ ^ 25 + ((2512 / 237) : ℂ) * ζ ^ 27 + ((422 / 79) : ℂ) * ζ ^ 28 + ((232 / 237) : ℂ) * ζ ^ 29 + ((288 / 79) : ℂ) * ζ ^ 30 + ((2512 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep02CoefficientIdentity02 :
    row18_reducedY33_combinationStep02Coefficient02 =
      row18_reducedY33_combinationStep01Coefficient02 +
        row18_reducedY33_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep02Coefficient02 row18_reducedY33_combinationStep01Coefficient02 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep02Coefficient03 : ℂ :=
  (-((847 / 237) : ℂ) - ((161 / 79) : ℂ) * ζ ^ 1 + ((48 / 79) : ℂ) * ζ ^ 2 + ((967 / 237) : ℂ) * ζ ^ 3 - ((457 / 237) : ℂ) * ζ ^ 5 - ((496 / 237) : ℂ) * ζ ^ 6 + ((344 / 237) : ℂ) * ζ ^ 8 + ((368 / 237) : ℂ) * ζ ^ 9 - ((599 / 237) : ℂ) * ζ ^ 11 + ((344 / 237) : ℂ) * ζ ^ 12 + ((161 / 79) : ℂ) * ζ ^ 13 - ((941 / 237) : ℂ) * ζ ^ 15 + ((161 / 79) : ℂ) * ζ ^ 17 + ((640 / 237) : ℂ) * ζ ^ 18 - ((484 / 237) : ℂ) * ζ ^ 21 - ((48 / 79) : ℂ) * ζ ^ 22 - ((26 / 237) : ℂ) * ζ ^ 25 + ((484 / 237) : ℂ) * ζ ^ 27 - ((344 / 237) : ℂ) * ζ ^ 28 - ((161 / 79) : ℂ) * ζ ^ 29 - ((248 / 237) : ℂ) * ζ ^ 30 + ((599 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep02CoefficientIdentity03 :
    row18_reducedY33_combinationStep02Coefficient03 =
      row18_reducedY33_combinationStep01Coefficient03 +
        row18_reducedY33_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep02Coefficient03 row18_reducedY33_combinationStep01Coefficient03 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep02Coefficient04 : ℂ :=
  (-((1139 / 18723) : ℂ) + ((326204 / 93615) : ℂ) * ζ ^ 1 - ((564893 / 93615) : ℂ) * ζ ^ 2 - ((100492 / 31205) : ℂ) * ζ ^ 3 - ((76671 / 31205) : ℂ) * ζ ^ 5 - ((186534 / 31205) : ℂ) * ζ ^ 6 - ((105191 / 18723) : ℂ) * ζ ^ 8 - ((733838 / 93615) : ℂ) * ζ ^ 9 - ((432362 / 93615) : ℂ) * ζ ^ 11 - ((105191 / 18723) : ℂ) * ζ ^ 12 - ((326204 / 93615) : ℂ) * ζ ^ 13 - ((254741 / 93615) : ℂ) * ζ ^ 15 - ((326204 / 93615) : ℂ) * ζ ^ 17 - ((5291 / 93615) : ℂ) * ζ ^ 18 - ((24728 / 93615) : ℂ) * ζ ^ 21 + ((564893 / 93615) : ℂ) * ζ ^ 22 + ((556217 / 93615) : ℂ) * ζ ^ 25 + ((24728 / 93615) : ℂ) * ζ ^ 27 + ((105191 / 18723) : ℂ) * ζ ^ 28 + ((326204 / 93615) : ℂ) * ζ ^ 29 - ((93267 / 31205) : ℂ) * ζ ^ 30 + ((432362 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep02CoefficientIdentity04 :
    row18_reducedY33_combinationStep02Coefficient04 =
      row18_reducedY33_combinationStep01Coefficient04 +
        row18_reducedY33_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep02Coefficient04 row18_reducedY33_combinationStep01Coefficient04 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 (-((12049 / 18723) : ℂ) - ((54227 / 18723) : ℂ) * ζ ^ 1 + ((60926 / 93615) : ℂ) * ζ ^ 2 + ((67145 / 18723) : ℂ) * ζ ^ 3 - ((256171 / 93615) : ℂ) * ζ ^ 4 + ((34426 / 6241) : ℂ) * ζ ^ 5 + ((263089 / 93615) : ℂ) * ζ ^ 6 - ((686651 / 93615) : ℂ) * ζ ^ 7 + ((234482 / 93615) : ℂ) * ζ ^ 8 + ((216739 / 93615) : ℂ) * ζ ^ 9 - ((270287 / 93615) : ℂ) * ζ ^ 10 + ((326443 / 93615) : ℂ) * ζ ^ 11 + ((241669 / 93615) : ℂ) * ζ ^ 12 - ((179848 / 31205) : ℂ) * ζ ^ 13 + ((534968 / 93615) : ℂ) * ζ ^ 14 - ((79607 / 31205) : ℂ) * ζ ^ 15 - ((612137 / 93615) : ℂ) * ζ ^ 16 + ((420407 / 93615) : ℂ) * ζ ^ 17 - ((214498 / 93615) : ℂ) * ζ ^ 18 - ((91153 / 93615) : ℂ) * ζ ^ 19 + ((150152 / 31205) : ℂ) * ζ ^ 20 - ((287533 / 93615) : ℂ) * ζ ^ 21 + ((85309 / 93615) : ℂ) * ζ ^ 22 + ((16759 / 93615) : ℂ) * ζ ^ 23 - ((14032 / 18723) : ℂ) * ζ ^ 24 - ((28994 / 31205) : ℂ) * ζ ^ 25 - ((44039 / 31205) : ℂ) * ζ ^ 26 + ((199337 / 93615) : ℂ) * ζ ^ 27 - ((111554 / 93615) : ℂ) * ζ ^ 28 + ((135266 / 93615) : ℂ) * ζ ^ 29 - ((23548 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep02CoefficientIdentity05 :
    row18_reducedY33_combinationStep02Coefficient05 =
      row18_reducedY33_combinationStep01Coefficient05 +
        row18_reducedY33_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep02Coefficient05 row18_reducedY33_combinationStep01Coefficient05 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep02Coefficient06 : ℂ :=
  (-((262666 / 93615) : ℂ) - ((35608 / 6241) : ℂ) * ζ ^ 1 - ((734687 / 93615) : ℂ) * ζ ^ 2 - ((90047 / 18723) : ℂ) * ζ ^ 3 + ((11229 / 31205) : ℂ) * ζ ^ 6 - ((319912 / 93615) : ℂ) * ζ ^ 8 - ((116045 / 18723) : ℂ) * ζ ^ 9 + ((34991 / 6241) : ℂ) * ζ ^ 11 + ((768374 / 93615) : ℂ) * ζ ^ 12 + ((35608 / 6241) : ℂ) * ζ ^ 13 - ((90047 / 18723) : ℂ) * ζ ^ 15 + ((35608 / 6241) : ℂ) * ζ ^ 17 + ((472021 / 93615) : ℂ) * ζ ^ 18 + ((35608 / 6241) : ℂ) * ζ ^ 21 + ((734687 / 93615) : ℂ) * ζ ^ 22 - ((734687 / 93615) : ℂ) * ζ ^ 24 - ((35608 / 6241) : ℂ) * ζ ^ 25 + ((34991 / 6241) : ℂ) * ζ ^ 27 + ((319912 / 93615) : ℂ) * ζ ^ 28 - ((35608 / 6241) : ℂ) * ζ ^ 29 - ((351533 / 31205) : ℂ) * ζ ^ 30 - ((34991 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep02CoefficientIdentity06 :
    row18_reducedY33_combinationStep02Coefficient06 =
      row18_reducedY33_combinationStep01Coefficient06 +
        row18_reducedY33_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep02Coefficient06 row18_reducedY33_combinationStep01Coefficient06 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 (((471476 / 93615) : ℂ) + ((159903 / 31205) : ℂ) * ζ ^ 1 + ((307246 / 31205) : ℂ) * ζ ^ 2 + ((205132 / 93615) : ℂ) * ζ ^ 3 - ((418972 / 93615) : ℂ) * ζ ^ 4 - ((425254 / 93615) : ℂ) * ζ ^ 5 - ((481024 / 93615) : ℂ) * ζ ^ 6 - ((81697 / 31205) : ℂ) * ζ ^ 7 + ((184491 / 31205) : ℂ) * ζ ^ 8 + ((372206 / 93615) : ℂ) * ζ ^ 9 + ((41455 / 18723) : ℂ) * ζ ^ 10 - ((30593 / 93615) : ℂ) * ζ ^ 11 - ((396922 / 93615) : ℂ) * ζ ^ 12 - ((171099 / 31205) : ℂ) * ζ ^ 13 - ((37818 / 31205) : ℂ) * ζ ^ 14 + ((195196 / 93615) : ℂ) * ζ ^ 15 + ((119737 / 31205) : ℂ) * ζ ^ 16 + ((189091 / 93615) : ℂ) * ζ ^ 17 - ((2991 / 31205) : ℂ) * ζ ^ 18 - ((324518 / 93615) : ℂ) * ζ ^ 19 - ((231428 / 93615) : ℂ) * ζ ^ 20 - ((26532 / 31205) : ℂ) * ζ ^ 21 - ((25139 / 31205) : ℂ) * ζ ^ 22 + ((328859 / 93615) : ℂ) * ζ ^ 23 + ((73679 / 31205) : ℂ) * ζ ^ 24 - ((5463 / 31205) : ℂ) * ζ ^ 25 + ((139036 / 93615) : ℂ) * ζ ^ 26 - ((355978 / 93615) : ℂ) * ζ ^ 27 - ((42694 / 31205) : ℂ) * ζ ^ 28 + ((61261 / 31205) : ℂ) * ζ ^ 29 + ((5046 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep02CoefficientIdentity07 :
    row18_reducedY33_combinationStep02Coefficient07 =
      row18_reducedY33_combinationStep01Coefficient07 +
        row18_reducedY33_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep02Coefficient07 row18_reducedY33_combinationStep01Coefficient07 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep02CoefficientIdentity08 :
    row18_reducedY33_combinationStep02Coefficient08 =
      row18_reducedY33_combinationStep01Coefficient08 +
        row18_reducedY33_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep02Coefficient08 row18_reducedY33_combinationStep01Coefficient08 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep02CoefficientIdentity09 :
    row18_reducedY33_combinationStep02Coefficient09 =
      row18_reducedY33_combinationStep01Coefficient09 +
        row18_reducedY33_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep02Coefficient09 row18_reducedY33_combinationStep01Coefficient09 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep02CoefficientIdentity10 :
    row18_reducedY33_combinationStep02Coefficient10 =
      row18_reducedY33_combinationStep01Coefficient10 +
        row18_reducedY33_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep02Coefficient10 row18_reducedY33_combinationStep01Coefficient10 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep02CoefficientIdentity11 :
    row18_reducedY33_combinationStep02Coefficient11 =
      row18_reducedY33_combinationStep01Coefficient11 +
        row18_reducedY33_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep02Coefficient11 row18_reducedY33_combinationStep01Coefficient11 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep02CoefficientIdentity12 :
    row18_reducedY33_combinationStep02Coefficient12 =
      row18_reducedY33_combinationStep01Coefficient12 +
        row18_reducedY33_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep02Coefficient12 row18_reducedY33_combinationStep01Coefficient12 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep02CoefficientIdentity13 :
    row18_reducedY33_combinationStep02Coefficient13 =
      row18_reducedY33_combinationStep01Coefficient13 +
        row18_reducedY33_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep02Coefficient13 row18_reducedY33_combinationStep01Coefficient13 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep02CoefficientIdentity14 :
    row18_reducedY33_combinationStep02Coefficient14 =
      row18_reducedY33_combinationStep01Coefficient14 +
        row18_reducedY33_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep02Coefficient14 row18_reducedY33_combinationStep01Coefficient14 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep02CoefficientIdentity15 :
    row18_reducedY33_combinationStep02Coefficient15 =
      row18_reducedY33_combinationStep01Coefficient15 +
        row18_reducedY33_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep02Coefficient15 row18_reducedY33_combinationStep01Coefficient15 row18_reducedY33_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY33_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY33_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY33_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY33_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY33_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY33_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY33_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY33_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY33_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY33_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY33_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY33_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY33_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY33_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY33_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY33_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY33_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY33_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY33_combinationStep02CoefficientIdentity00,
      row18_reducedY33_combinationStep02CoefficientIdentity01,
      row18_reducedY33_combinationStep02CoefficientIdentity02,
      row18_reducedY33_combinationStep02CoefficientIdentity03,
      row18_reducedY33_combinationStep02CoefficientIdentity04,
      row18_reducedY33_combinationStep02CoefficientIdentity05,
      row18_reducedY33_combinationStep02CoefficientIdentity06,
      row18_reducedY33_combinationStep02CoefficientIdentity07,
      row18_reducedY33_combinationStep02CoefficientIdentity08,
      row18_reducedY33_combinationStep02CoefficientIdentity09,
      row18_reducedY33_combinationStep02CoefficientIdentity10,
      row18_reducedY33_combinationStep02CoefficientIdentity11,
      row18_reducedY33_combinationStep02CoefficientIdentity12,
      row18_reducedY33_combinationStep02CoefficientIdentity13,
      row18_reducedY33_combinationStep02CoefficientIdentity14,
      row18_reducedY33_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY33_combinationStep02Multiplier * equation

private def row18_reducedY33_combinationStep03Multiplier : ℂ :=
  (-((218 / 237) : ℂ) - ((56 / 79) : ℂ) * ζ ^ 1 - ((3278 / 237) : ℂ) * ζ ^ 2 - ((3340 / 237) : ℂ) * ζ ^ 5 - ((1020 / 79) : ℂ) * ζ ^ 6 - ((1020 / 79) : ℂ) * ζ ^ 8 - ((3340 / 237) : ℂ) * ζ ^ 9 - ((2786 / 237) : ℂ) * ζ ^ 11 - ((1210 / 237) : ℂ) * ζ ^ 12 + ((56 / 79) : ℂ) * ζ ^ 13 - ((2584 / 237) : ℂ) * ζ ^ 15 + ((56 / 79) : ℂ) * ζ ^ 17 + ((1912 / 237) : ℂ) * ζ ^ 18 + ((1754 / 237) : ℂ) * ζ ^ 21 + ((3278 / 237) : ℂ) * ζ ^ 22 + ((1148 / 237) : ℂ) * ζ ^ 24 + ((3172 / 237) : ℂ) * ζ ^ 25 + ((2584 / 237) : ℂ) * ζ ^ 27 + ((1020 / 79) : ℂ) * ζ ^ 28 - ((56 / 79) : ℂ) * ζ ^ 29 - ((1850 / 237) : ℂ) * ζ ^ 30 + ((2786 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY33_combinationStep03Coefficient00 : ℂ :=
  (((44 / 79) : ℂ) - ((1732 / 395) : ℂ) * ζ ^ 1 + ((6563 / 790) : ℂ) * ζ ^ 2 + ((2791 / 790) : ℂ) * ζ ^ 3 + ((2123 / 790) : ℂ) * ζ ^ 5 + ((3176 / 395) : ℂ) * ζ ^ 6 + ((1139 / 158) : ℂ) * ζ ^ 8 + ((7013 / 790) : ℂ) * ζ ^ 9 + ((2111 / 395) : ℂ) * ζ ^ 11 + ((1139 / 158) : ℂ) * ζ ^ 12 + ((1732 / 395) : ℂ) * ζ ^ 13 + ((1398 / 395) : ℂ) * ζ ^ 15 + ((1732 / 395) : ℂ) * ζ ^ 17 + ((211 / 790) : ℂ) * ζ ^ 18 + ((673 / 790) : ℂ) * ζ ^ 21 - ((6563 / 790) : ℂ) * ζ ^ 22 - ((5587 / 790) : ℂ) * ζ ^ 25 - ((673 / 790) : ℂ) * ζ ^ 27 - ((1139 / 158) : ℂ) * ζ ^ 28 - ((1732 / 395) : ℂ) * ζ ^ 29 + ((1588 / 395) : ℂ) * ζ ^ 30 - ((2111 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep03CoefficientIdentity00 :
    row18_reducedY33_combinationStep03Coefficient00 =
      row18_reducedY33_combinationStep02Coefficient00 +
        row18_reducedY33_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep03Coefficient00 row18_reducedY33_combinationStep02Coefficient00 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 (((55553 / 18723) : ℂ) + ((108251 / 37446) : ℂ) * ζ ^ 1 - ((85135 / 18723) : ℂ) * ζ ^ 2 - ((70745 / 18723) : ℂ) * ζ ^ 3 - ((42373 / 12482) : ℂ) * ζ ^ 4 - ((34397 / 18723) : ℂ) * ζ ^ 5 + ((65629 / 18723) : ℂ) * ζ ^ 6 + ((23359 / 6241) : ℂ) * ζ ^ 7 - ((70979 / 37446) : ℂ) * ζ ^ 8 - ((20969 / 37446) : ℂ) * ζ ^ 9 - ((22621 / 37446) : ℂ) * ζ ^ 10 - ((28013 / 37446) : ℂ) * ζ ^ 11 + ((23792 / 18723) : ℂ) * ζ ^ 12 + ((14254 / 6241) : ℂ) * ζ ^ 13 + ((17777 / 37446) : ℂ) * ζ ^ 14 + ((3994 / 6241) : ℂ) * ζ ^ 15 + ((18419 / 37446) : ℂ) * ζ ^ 16 - ((1811 / 6241) : ℂ) * ζ ^ 17 - ((40775 / 37446) : ℂ) * ζ ^ 18 - ((9088 / 18723) : ℂ) * ζ ^ 19 - ((8617 / 37446) : ℂ) * ζ ^ 20 + ((36569 / 18723) : ℂ) * ζ ^ 21 + ((33320 / 18723) : ℂ) * ζ ^ 22 - ((16753 / 18723) : ℂ) * ζ ^ 23 + ((1382 / 18723) : ℂ) * ζ ^ 24 - ((7958 / 6241) : ℂ) * ζ ^ 25 - ((104513 / 37446) : ℂ) * ζ ^ 26 + ((12549 / 6241) : ℂ) * ζ ^ 27 + ((27551 / 37446) : ℂ) * ζ ^ 28 - ((17663 / 12482) : ℂ) * ζ ^ 29 - ((6965 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep03Coefficient01 : ℂ :=
  (-((33 / 158) : ℂ) + ((23 / 158) : ℂ) * ζ ^ 1 - ((7 / 158) : ℂ) * ζ ^ 2 - ((14 / 79) : ℂ) * ζ ^ 3 + ((23 / 158) : ℂ) * ζ ^ 5 - ((20 / 79) : ℂ) * ζ ^ 6 + ((20 / 79) : ℂ) * ζ ^ 8 - ((23 / 158) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((45 / 158) : ℂ) * ζ ^ 12 - ((23 / 158) : ℂ) * ζ ^ 13 - ((11 / 158) : ℂ) * ζ ^ 15 - ((23 / 158) : ℂ) * ζ ^ 17 + ((16 / 79) : ℂ) * ζ ^ 18 - ((29 / 79) : ℂ) * ζ ^ 21 + ((7 / 158) : ℂ) * ζ ^ 22 - ((4 / 79) : ℂ) * ζ ^ 24 - ((39 / 158) : ℂ) * ζ ^ 27 - ((20 / 79) : ℂ) * ζ ^ 28 + ((23 / 158) : ℂ) * ζ ^ 29 + ((5 / 158) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep03CoefficientIdentity01 :
    row18_reducedY33_combinationStep03Coefficient01 =
      row18_reducedY33_combinationStep02Coefficient01 +
        row18_reducedY33_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep03Coefficient01 row18_reducedY33_combinationStep02Coefficient01 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 (-((598619 / 37446) : ℂ) + ((41340 / 6241) : ℂ) * ζ ^ 1 + ((36055 / 18723) : ℂ) * ζ ^ 2 - ((45235 / 6241) : ℂ) * ζ ^ 3 + ((60146 / 6241) : ℂ) * ζ ^ 4 + ((35491 / 18723) : ℂ) * ζ ^ 5 - ((337018 / 18723) : ℂ) * ζ ^ 6 - ((37542 / 6241) : ℂ) * ζ ^ 7 - ((29182 / 18723) : ℂ) * ζ ^ 8 - ((60200 / 6241) : ℂ) * ζ ^ 9 + ((99032 / 18723) : ℂ) * ζ ^ 10 - ((182395 / 37446) : ℂ) * ζ ^ 11 - ((152757 / 12482) : ℂ) * ζ ^ 12 + ((19759 / 18723) : ℂ) * ζ ^ 13 - ((167342 / 18723) : ℂ) * ζ ^ 14 - ((223388 / 18723) : ℂ) * ζ ^ 15 + ((32999 / 18723) : ℂ) * ζ ^ 16 - ((48378 / 6241) : ℂ) * ζ ^ 17 - ((217031 / 37446) : ℂ) * ζ ^ 18 + ((269827 / 37446) : ℂ) * ζ ^ 19 - ((181339 / 37446) : ℂ) * ζ ^ 20 - ((411649 / 37446) : ℂ) * ζ ^ 21 + ((21976 / 18723) : ℂ) * ζ ^ 22 - ((6559 / 18723) : ℂ) * ζ ^ 23 + ((5951 / 6241) : ℂ) * ζ ^ 24 + ((38938 / 6241) : ℂ) * ζ ^ 25 - ((84329 / 18723) : ℂ) * ζ ^ 26 + ((1605 / 12482) : ℂ) * ζ ^ 27 + ((18283 / 12482) : ℂ) * ζ ^ 28 + ((3766 / 18723) : ℂ) * ζ ^ 29 + ((19502 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep03Coefficient02 : ℂ :=
  (((1055 / 237) : ℂ) + ((232 / 237) : ℂ) * ζ ^ 1 - ((134 / 79) : ℂ) * ζ ^ 2 + ((123 / 79) : ℂ) * ζ ^ 3 - ((2048 / 237) : ℂ) * ζ ^ 5 + ((194 / 79) : ℂ) * ζ ^ 6 - ((422 / 79) : ℂ) * ζ ^ 8 - ((1256 / 237) : ℂ) * ζ ^ 9 - ((2512 / 237) : ℂ) * ζ ^ 11 - ((328 / 79) : ℂ) * ζ ^ 12 - ((232 / 237) : ℂ) * ζ ^ 13 - ((123 / 79) : ℂ) * ζ ^ 15 - ((232 / 237) : ℂ) * ζ ^ 17 - ((653 / 237) : ℂ) * ζ ^ 18 + ((760 / 79) : ℂ) * ζ ^ 21 + ((134 / 79) : ℂ) * ζ ^ 22 + ((134 / 79) : ℂ) * ζ ^ 24 + ((760 / 79) : ℂ) * ζ ^ 25 + ((2512 / 237) : ℂ) * ζ ^ 27 + ((422 / 79) : ℂ) * ζ ^ 28 + ((232 / 237) : ℂ) * ζ ^ 29 + ((288 / 79) : ℂ) * ζ ^ 30 + ((2512 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep03CoefficientIdentity02 :
    row18_reducedY33_combinationStep03Coefficient02 =
      row18_reducedY33_combinationStep02Coefficient02 +
        row18_reducedY33_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep03Coefficient02 row18_reducedY33_combinationStep02Coefficient02 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep03Coefficient03 : ℂ :=
  (-((847 / 237) : ℂ) - ((161 / 79) : ℂ) * ζ ^ 1 + ((48 / 79) : ℂ) * ζ ^ 2 + ((967 / 237) : ℂ) * ζ ^ 3 - ((457 / 237) : ℂ) * ζ ^ 5 - ((496 / 237) : ℂ) * ζ ^ 6 + ((344 / 237) : ℂ) * ζ ^ 8 + ((368 / 237) : ℂ) * ζ ^ 9 - ((599 / 237) : ℂ) * ζ ^ 11 + ((344 / 237) : ℂ) * ζ ^ 12 + ((161 / 79) : ℂ) * ζ ^ 13 - ((941 / 237) : ℂ) * ζ ^ 15 + ((161 / 79) : ℂ) * ζ ^ 17 + ((640 / 237) : ℂ) * ζ ^ 18 - ((484 / 237) : ℂ) * ζ ^ 21 - ((48 / 79) : ℂ) * ζ ^ 22 - ((26 / 237) : ℂ) * ζ ^ 25 + ((484 / 237) : ℂ) * ζ ^ 27 - ((344 / 237) : ℂ) * ζ ^ 28 - ((161 / 79) : ℂ) * ζ ^ 29 - ((248 / 237) : ℂ) * ζ ^ 30 + ((599 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep03CoefficientIdentity03 :
    row18_reducedY33_combinationStep03Coefficient03 =
      row18_reducedY33_combinationStep02Coefficient03 +
        row18_reducedY33_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep03Coefficient03 row18_reducedY33_combinationStep02Coefficient03 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep03Coefficient04 : ℂ :=
  (-((1139 / 18723) : ℂ) + ((326204 / 93615) : ℂ) * ζ ^ 1 - ((564893 / 93615) : ℂ) * ζ ^ 2 - ((100492 / 31205) : ℂ) * ζ ^ 3 - ((76671 / 31205) : ℂ) * ζ ^ 5 - ((186534 / 31205) : ℂ) * ζ ^ 6 - ((105191 / 18723) : ℂ) * ζ ^ 8 - ((733838 / 93615) : ℂ) * ζ ^ 9 - ((432362 / 93615) : ℂ) * ζ ^ 11 - ((105191 / 18723) : ℂ) * ζ ^ 12 - ((326204 / 93615) : ℂ) * ζ ^ 13 - ((254741 / 93615) : ℂ) * ζ ^ 15 - ((326204 / 93615) : ℂ) * ζ ^ 17 - ((5291 / 93615) : ℂ) * ζ ^ 18 - ((24728 / 93615) : ℂ) * ζ ^ 21 + ((564893 / 93615) : ℂ) * ζ ^ 22 + ((556217 / 93615) : ℂ) * ζ ^ 25 + ((24728 / 93615) : ℂ) * ζ ^ 27 + ((105191 / 18723) : ℂ) * ζ ^ 28 + ((326204 / 93615) : ℂ) * ζ ^ 29 - ((93267 / 31205) : ℂ) * ζ ^ 30 + ((432362 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep03CoefficientIdentity04 :
    row18_reducedY33_combinationStep03Coefficient04 =
      row18_reducedY33_combinationStep02Coefficient04 +
        row18_reducedY33_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep03Coefficient04 row18_reducedY33_combinationStep02Coefficient04 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep03Coefficient05 : ℂ :=
  (-((2223 / 6241) : ℂ) + ((9192 / 6241) : ℂ) * ζ ^ 1 - ((201011 / 37446) : ℂ) * ζ ^ 2 - ((25171 / 6241) : ℂ) * ζ ^ 5 - ((187673 / 37446) : ℂ) * ζ ^ 6 - ((187673 / 37446) : ℂ) * ζ ^ 8 - ((25171 / 6241) : ℂ) * ζ ^ 9 - ((79151 / 12482) : ℂ) * ζ ^ 11 - ((25515 / 6241) : ℂ) * ζ ^ 12 - ((9192 / 6241) : ℂ) * ζ ^ 13 - ((58274 / 18723) : ℂ) * ζ ^ 15 - ((9192 / 6241) : ℂ) * ζ ^ 17 + ((18115 / 6241) : ℂ) * ζ ^ 18 + ((15979 / 12482) : ℂ) * ζ ^ 21 + ((201011 / 37446) : ℂ) * ζ ^ 22 + ((78983 / 37446) : ℂ) * ζ ^ 24 + ((34363 / 6241) : ℂ) * ζ ^ 25 + ((58274 / 18723) : ℂ) * ζ ^ 27 + ((187673 / 37446) : ℂ) * ζ ^ 28 + ((9192 / 6241) : ℂ) * ζ ^ 29 - ((34583 / 37446) : ℂ) * ζ ^ 30 + ((79151 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep03CoefficientIdentity05 :
    row18_reducedY33_combinationStep03Coefficient05 =
      row18_reducedY33_combinationStep02Coefficient05 +
        row18_reducedY33_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep03Coefficient05 row18_reducedY33_combinationStep02Coefficient05 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 (((2005 / 6241) : ℂ) - ((54961 / 37446) : ℂ) * ζ ^ 1 + ((86501 / 18723) : ℂ) * ζ ^ 2 + ((11107 / 37446) : ℂ) * ζ ^ 3 - ((151177 / 37446) : ℂ) * ζ ^ 4 + ((93577 / 18723) : ℂ) * ζ ^ 5 + ((3199 / 12482) : ℂ) * ζ ^ 6 - ((85028 / 18723) : ℂ) * ζ ^ 7 + ((145147 / 37446) : ℂ) * ζ ^ 8 - ((17323 / 18723) : ℂ) * ζ ^ 9 - ((48325 / 18723) : ℂ) * ζ ^ 10 + ((148199 / 37446) : ℂ) * ζ ^ 11 - ((14945 / 37446) : ℂ) * ζ ^ 12 - ((33865 / 18723) : ℂ) * ζ ^ 13 + ((38225 / 6241) : ℂ) * ζ ^ 14 - ((121015 / 37446) : ℂ) * ζ ^ 15 - ((36381 / 12482) : ℂ) * ζ ^ 16 + ((113665 / 37446) : ℂ) * ζ ^ 17 - ((75817 / 18723) : ℂ) * ζ ^ 18 - ((8433 / 6241) : ℂ) * ζ ^ 19 + ((22003 / 12482) : ℂ) * ζ ^ 20 - ((57872 / 18723) : ℂ) * ζ ^ 21 + ((188 / 6241) : ℂ) * ζ ^ 22 + ((5709 / 6241) : ℂ) * ζ ^ 23 + ((5383 / 37446) : ℂ) * ζ ^ 24 - ((7437 / 12482) : ℂ) * ζ ^ 25 - ((11833 / 18723) : ℂ) * ζ ^ 26 + ((18083 / 18723) : ℂ) * ζ ^ 27 - ((9649 / 12482) : ℂ) * ζ ^ 28 + ((5873 / 6241) : ℂ) * ζ ^ 29 - ((9751 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep03Coefficient06 : ℂ :=
  (-((262666 / 93615) : ℂ) - ((35608 / 6241) : ℂ) * ζ ^ 1 - ((734687 / 93615) : ℂ) * ζ ^ 2 - ((90047 / 18723) : ℂ) * ζ ^ 3 + ((11229 / 31205) : ℂ) * ζ ^ 6 - ((319912 / 93615) : ℂ) * ζ ^ 8 - ((116045 / 18723) : ℂ) * ζ ^ 9 + ((34991 / 6241) : ℂ) * ζ ^ 11 + ((768374 / 93615) : ℂ) * ζ ^ 12 + ((35608 / 6241) : ℂ) * ζ ^ 13 - ((90047 / 18723) : ℂ) * ζ ^ 15 + ((35608 / 6241) : ℂ) * ζ ^ 17 + ((472021 / 93615) : ℂ) * ζ ^ 18 + ((35608 / 6241) : ℂ) * ζ ^ 21 + ((734687 / 93615) : ℂ) * ζ ^ 22 - ((734687 / 93615) : ℂ) * ζ ^ 24 - ((35608 / 6241) : ℂ) * ζ ^ 25 + ((34991 / 6241) : ℂ) * ζ ^ 27 + ((319912 / 93615) : ℂ) * ζ ^ 28 - ((35608 / 6241) : ℂ) * ζ ^ 29 - ((351533 / 31205) : ℂ) * ζ ^ 30 - ((34991 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep03CoefficientIdentity06 :
    row18_reducedY33_combinationStep03Coefficient06 =
      row18_reducedY33_combinationStep02Coefficient06 +
        row18_reducedY33_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep03Coefficient06 row18_reducedY33_combinationStep02Coefficient06 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep03Coefficient07 : ℂ :=
  (((19208 / 6241) : ℂ) + ((55013 / 18723) : ℂ) * ζ ^ 1 - ((107881 / 37446) : ℂ) * ζ ^ 2 - ((164489 / 37446) : ℂ) * ζ ^ 3 + ((63581 / 37446) : ℂ) * ζ ^ 5 + ((562 / 18723) : ℂ) * ζ ^ 6 - ((37971 / 12482) : ℂ) * ζ ^ 8 - ((97025 / 37446) : ℂ) * ζ ^ 9 + ((11244 / 6241) : ℂ) * ζ ^ 11 - ((37971 / 12482) : ℂ) * ζ ^ 12 - ((55013 / 18723) : ℂ) * ζ ^ 13 + ((19674 / 6241) : ℂ) * ζ ^ 15 - ((55013 / 18723) : ℂ) * ζ ^ 17 - ((36335 / 12482) : ℂ) * ζ ^ 18 + ((54463 / 37446) : ℂ) * ζ ^ 21 + ((107881 / 37446) : ℂ) * ζ ^ 22 + ((46445 / 37446) : ℂ) * ζ ^ 25 - ((54463 / 37446) : ℂ) * ζ ^ 27 + ((37971 / 12482) : ℂ) * ζ ^ 28 + ((55013 / 18723) : ℂ) * ζ ^ 29 + ((281 / 18723) : ℂ) * ζ ^ 30 - ((11244 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep03CoefficientIdentity07 :
    row18_reducedY33_combinationStep03Coefficient07 =
      row18_reducedY33_combinationStep02Coefficient07 +
        row18_reducedY33_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep03Coefficient07 row18_reducedY33_combinationStep02Coefficient07 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 (-((55553 / 18723) : ℂ) - ((108251 / 37446) : ℂ) * ζ ^ 1 + ((85135 / 18723) : ℂ) * ζ ^ 2 + ((70745 / 18723) : ℂ) * ζ ^ 3 + ((42373 / 12482) : ℂ) * ζ ^ 4 + ((34397 / 18723) : ℂ) * ζ ^ 5 - ((65629 / 18723) : ℂ) * ζ ^ 6 - ((23359 / 6241) : ℂ) * ζ ^ 7 + ((70979 / 37446) : ℂ) * ζ ^ 8 + ((20969 / 37446) : ℂ) * ζ ^ 9 + ((22621 / 37446) : ℂ) * ζ ^ 10 + ((28013 / 37446) : ℂ) * ζ ^ 11 - ((23792 / 18723) : ℂ) * ζ ^ 12 - ((14254 / 6241) : ℂ) * ζ ^ 13 - ((17777 / 37446) : ℂ) * ζ ^ 14 - ((3994 / 6241) : ℂ) * ζ ^ 15 - ((18419 / 37446) : ℂ) * ζ ^ 16 + ((1811 / 6241) : ℂ) * ζ ^ 17 + ((40775 / 37446) : ℂ) * ζ ^ 18 + ((9088 / 18723) : ℂ) * ζ ^ 19 + ((8617 / 37446) : ℂ) * ζ ^ 20 - ((36569 / 18723) : ℂ) * ζ ^ 21 - ((33320 / 18723) : ℂ) * ζ ^ 22 + ((16753 / 18723) : ℂ) * ζ ^ 23 - ((1382 / 18723) : ℂ) * ζ ^ 24 + ((7958 / 6241) : ℂ) * ζ ^ 25 + ((104513 / 37446) : ℂ) * ζ ^ 26 - ((12549 / 6241) : ℂ) * ζ ^ 27 - ((27551 / 37446) : ℂ) * ζ ^ 28 + ((17663 / 12482) : ℂ) * ζ ^ 29 + ((6965 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep03CoefficientIdentity08 :
    row18_reducedY33_combinationStep03Coefficient08 =
      row18_reducedY33_combinationStep02Coefficient08 +
        row18_reducedY33_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep03Coefficient08 row18_reducedY33_combinationStep02Coefficient08 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep03CoefficientIdentity09 :
    row18_reducedY33_combinationStep03Coefficient09 =
      row18_reducedY33_combinationStep02Coefficient09 +
        row18_reducedY33_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep03Coefficient09 row18_reducedY33_combinationStep02Coefficient09 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep03CoefficientIdentity10 :
    row18_reducedY33_combinationStep03Coefficient10 =
      row18_reducedY33_combinationStep02Coefficient10 +
        row18_reducedY33_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep03Coefficient10 row18_reducedY33_combinationStep02Coefficient10 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep03CoefficientIdentity11 :
    row18_reducedY33_combinationStep03Coefficient11 =
      row18_reducedY33_combinationStep02Coefficient11 +
        row18_reducedY33_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep03Coefficient11 row18_reducedY33_combinationStep02Coefficient11 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep03CoefficientIdentity12 :
    row18_reducedY33_combinationStep03Coefficient12 =
      row18_reducedY33_combinationStep02Coefficient12 +
        row18_reducedY33_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep03Coefficient12 row18_reducedY33_combinationStep02Coefficient12 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep03CoefficientIdentity13 :
    row18_reducedY33_combinationStep03Coefficient13 =
      row18_reducedY33_combinationStep02Coefficient13 +
        row18_reducedY33_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep03Coefficient13 row18_reducedY33_combinationStep02Coefficient13 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep03CoefficientIdentity14 :
    row18_reducedY33_combinationStep03Coefficient14 =
      row18_reducedY33_combinationStep02Coefficient14 +
        row18_reducedY33_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep03Coefficient14 row18_reducedY33_combinationStep02Coefficient14 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep03CoefficientIdentity15 :
    row18_reducedY33_combinationStep03Coefficient15 =
      row18_reducedY33_combinationStep02Coefficient15 +
        row18_reducedY33_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep03Coefficient15 row18_reducedY33_combinationStep02Coefficient15 row18_reducedY33_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY33_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY33_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY33_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY33_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY33_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY33_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY33_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY33_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY33_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY33_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY33_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY33_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY33_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY33_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY33_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY33_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY33_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY33_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY33_combinationStep03CoefficientIdentity00,
      row18_reducedY33_combinationStep03CoefficientIdentity01,
      row18_reducedY33_combinationStep03CoefficientIdentity02,
      row18_reducedY33_combinationStep03CoefficientIdentity03,
      row18_reducedY33_combinationStep03CoefficientIdentity04,
      row18_reducedY33_combinationStep03CoefficientIdentity05,
      row18_reducedY33_combinationStep03CoefficientIdentity06,
      row18_reducedY33_combinationStep03CoefficientIdentity07,
      row18_reducedY33_combinationStep03CoefficientIdentity08,
      row18_reducedY33_combinationStep03CoefficientIdentity09,
      row18_reducedY33_combinationStep03CoefficientIdentity10,
      row18_reducedY33_combinationStep03CoefficientIdentity11,
      row18_reducedY33_combinationStep03CoefficientIdentity12,
      row18_reducedY33_combinationStep03CoefficientIdentity13,
      row18_reducedY33_combinationStep03CoefficientIdentity14,
      row18_reducedY33_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY33_combinationStep03Multiplier * equation

private def row18_reducedY33_combinationStep04Multiplier : ℂ :=
  (-((14 / 79) : ℂ) - ((120 / 79) : ℂ) * ζ ^ 1 - ((218 / 79) : ℂ) * ζ ^ 2 + ((52 / 79) : ℂ) * ζ ^ 5 - ((204 / 79) : ℂ) * ζ ^ 6 - ((204 / 79) : ℂ) * ζ ^ 8 + ((52 / 79) : ℂ) * ζ ^ 9 + ((94 / 79) : ℂ) * ζ ^ 11 - ((2 / 79) : ℂ) * ζ ^ 12 + ((120 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 + ((120 / 79) : ℂ) * ζ ^ 17 + ((148 / 79) : ℂ) * ζ ^ 18 + ((34 / 79) : ℂ) * ζ ^ 21 + ((218 / 79) : ℂ) * ζ ^ 22 + ((56 / 79) : ℂ) * ζ ^ 24 - ((172 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((204 / 79) : ℂ) * ζ ^ 28 - ((120 / 79) : ℂ) * ζ ^ 29 - ((202 / 79) : ℂ) * ζ ^ 30 - ((94 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY33_combinationStep04Coefficient00 : ℂ :=
  (((77 / 79) : ℂ) - ((1852 / 395) : ℂ) * ζ ^ 1 + ((3234 / 395) : ℂ) * ζ ^ 2 + ((1588 / 395) : ℂ) * ζ ^ 3 + ((1109 / 395) : ℂ) * ζ ^ 5 + ((3186 / 395) : ℂ) * ζ ^ 6 + ((572 / 79) : ℂ) * ζ ^ 8 + ((3744 / 395) : ℂ) * ζ ^ 9 + ((2156 / 395) : ℂ) * ζ ^ 11 + ((572 / 79) : ℂ) * ζ ^ 12 + ((1852 / 395) : ℂ) * ζ ^ 13 + ((1373 / 395) : ℂ) * ζ ^ 15 + ((1852 / 395) : ℂ) * ζ ^ 17 + ((48 / 395) : ℂ) * ζ ^ 18 + ((264 / 395) : ℂ) * ζ ^ 21 - ((3234 / 395) : ℂ) * ζ ^ 22 - ((2961 / 395) : ℂ) * ζ ^ 25 - ((264 / 395) : ℂ) * ζ ^ 27 - ((572 / 79) : ℂ) * ζ ^ 28 - ((1852 / 395) : ℂ) * ζ ^ 29 + ((1593 / 395) : ℂ) * ζ ^ 30 - ((2156 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep04CoefficientIdentity00 :
    row18_reducedY33_combinationStep04Coefficient00 =
      row18_reducedY33_combinationStep03Coefficient00 +
        row18_reducedY33_combinationStep04Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep04Coefficient00 row18_reducedY33_combinationStep03Coefficient00 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 (-((2474 / 6241) : ℂ) + ((6163 / 12482) : ℂ) * ζ ^ 1 + ((3250 / 6241) : ℂ) * ζ ^ 2 - ((1919 / 6241) : ℂ) * ζ ^ 3 + ((7587 / 12482) : ℂ) * ζ ^ 4 - ((3018 / 6241) : ℂ) * ζ ^ 5 - ((1520 / 6241) : ℂ) * ζ ^ 6 + ((3459 / 6241) : ℂ) * ζ ^ 7 - ((315 / 12482) : ℂ) * ζ ^ 8 - ((1635 / 12482) : ℂ) * ζ ^ 9 + ((2433 / 12482) : ℂ) * ζ ^ 10 + ((203 / 12482) : ℂ) * ζ ^ 11 - ((1748 / 6241) : ℂ) * ζ ^ 12 + ((1205 / 6241) : ℂ) * ζ ^ 13 - ((837 / 12482) : ℂ) * ζ ^ 14 + ((894 / 6241) : ℂ) * ζ ^ 15 + ((247 / 12482) : ℂ) * ζ ^ 16 + ((163 / 6241) : ℂ) * ζ ^ 17 + ((1985 / 12482) : ℂ) * ζ ^ 18 - ((1125 / 6241) : ℂ) * ζ ^ 19 + ((871 / 12482) : ℂ) * ζ ^ 20 + ((706 / 6241) : ℂ) * ζ ^ 21 - ((3236 / 6241) : ℂ) * ζ ^ 22 + ((2 / 79) : ℂ) * ζ ^ 23 - ((710 / 6241) : ℂ) * ζ ^ 24 + ((240 / 6241) : ℂ) * ζ ^ 25 + ((10525 / 12482) : ℂ) * ζ ^ 26 - ((162 / 6241) : ℂ) * ζ ^ 27 - ((3337 / 12482) : ℂ) * ζ ^ 28 - ((741 / 12482) : ℂ) * ζ ^ 29 + ((705 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep04Coefficient01 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep04CoefficientIdentity01 :
    row18_reducedY33_combinationStep04Coefficient01 =
      row18_reducedY33_combinationStep03Coefficient01 +
        row18_reducedY33_combinationStep04Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep04Coefficient01 row18_reducedY33_combinationStep03Coefficient01 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 (-((2719 / 12482) : ℂ) + ((390 / 6241) : ℂ) * ζ ^ 1 - ((1601 / 6241) : ℂ) * ζ ^ 2 - ((2752 / 6241) : ℂ) * ζ ^ 3 - ((518 / 6241) : ℂ) * ζ ^ 4 + ((676 / 6241) : ℂ) * ζ ^ 5 - ((1552 / 6241) : ℂ) * ζ ^ 6 + ((1011 / 6241) : ℂ) * ζ ^ 7 - ((495 / 6241) : ℂ) * ζ ^ 8 - ((1661 / 6241) : ℂ) * ζ ^ 9 + ((1017 / 6241) : ℂ) * ζ ^ 10 - ((893 / 12482) : ℂ) * ζ ^ 11 + ((1643 / 12482) : ℂ) * ζ ^ 12 + ((887 / 6241) : ℂ) * ζ ^ 13 - ((55 / 6241) : ℂ) * ζ ^ 14 - ((204 / 6241) : ℂ) * ζ ^ 15 - ((886 / 6241) : ℂ) * ζ ^ 16 + ((638 / 6241) : ℂ) * ζ ^ 17 + ((2889 / 12482) : ℂ) * ζ ^ 18 + ((2551 / 12482) : ℂ) * ζ ^ 19 + ((5915 / 12482) : ℂ) * ζ ^ 20 - ((4831 / 12482) : ℂ) * ζ ^ 21 - ((1303 / 6241) : ℂ) * ζ ^ 22 + ((594 / 6241) : ℂ) * ζ ^ 23 + ((2049 / 6241) : ℂ) * ζ ^ 24 + ((442 / 6241) : ℂ) * ζ ^ 25 + ((72 / 6241) : ℂ) * ζ ^ 26 - ((3541 / 12482) : ℂ) * ζ ^ 27 - ((889 / 12482) : ℂ) * ζ ^ 28 + ((425 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep04Coefficient02 : ℂ :=
  (((1055 / 237) : ℂ) + ((232 / 237) : ℂ) * ζ ^ 1 - ((134 / 79) : ℂ) * ζ ^ 2 + ((123 / 79) : ℂ) * ζ ^ 3 - ((2048 / 237) : ℂ) * ζ ^ 5 + ((194 / 79) : ℂ) * ζ ^ 6 - ((422 / 79) : ℂ) * ζ ^ 8 - ((1256 / 237) : ℂ) * ζ ^ 9 - ((2512 / 237) : ℂ) * ζ ^ 11 - ((328 / 79) : ℂ) * ζ ^ 12 - ((232 / 237) : ℂ) * ζ ^ 13 - ((123 / 79) : ℂ) * ζ ^ 15 - ((232 / 237) : ℂ) * ζ ^ 17 - ((653 / 237) : ℂ) * ζ ^ 18 + ((760 / 79) : ℂ) * ζ ^ 21 + ((134 / 79) : ℂ) * ζ ^ 22 + ((134 / 79) : ℂ) * ζ ^ 24 + ((760 / 79) : ℂ) * ζ ^ 25 + ((2512 / 237) : ℂ) * ζ ^ 27 + ((422 / 79) : ℂ) * ζ ^ 28 + ((232 / 237) : ℂ) * ζ ^ 29 + ((288 / 79) : ℂ) * ζ ^ 30 + ((2512 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep04CoefficientIdentity02 :
    row18_reducedY33_combinationStep04Coefficient02 =
      row18_reducedY33_combinationStep03Coefficient02 +
        row18_reducedY33_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep04Coefficient02 row18_reducedY33_combinationStep03Coefficient02 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep04Coefficient03 : ℂ :=
  (-((847 / 237) : ℂ) - ((161 / 79) : ℂ) * ζ ^ 1 + ((48 / 79) : ℂ) * ζ ^ 2 + ((967 / 237) : ℂ) * ζ ^ 3 - ((457 / 237) : ℂ) * ζ ^ 5 - ((496 / 237) : ℂ) * ζ ^ 6 + ((344 / 237) : ℂ) * ζ ^ 8 + ((368 / 237) : ℂ) * ζ ^ 9 - ((599 / 237) : ℂ) * ζ ^ 11 + ((344 / 237) : ℂ) * ζ ^ 12 + ((161 / 79) : ℂ) * ζ ^ 13 - ((941 / 237) : ℂ) * ζ ^ 15 + ((161 / 79) : ℂ) * ζ ^ 17 + ((640 / 237) : ℂ) * ζ ^ 18 - ((484 / 237) : ℂ) * ζ ^ 21 - ((48 / 79) : ℂ) * ζ ^ 22 - ((26 / 237) : ℂ) * ζ ^ 25 + ((484 / 237) : ℂ) * ζ ^ 27 - ((344 / 237) : ℂ) * ζ ^ 28 - ((161 / 79) : ℂ) * ζ ^ 29 - ((248 / 237) : ℂ) * ζ ^ 30 + ((599 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep04CoefficientIdentity03 :
    row18_reducedY33_combinationStep04Coefficient03 =
      row18_reducedY33_combinationStep03Coefficient03 +
        row18_reducedY33_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep04Coefficient03 row18_reducedY33_combinationStep03Coefficient03 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep04Coefficient04 : ℂ :=
  (-((1139 / 18723) : ℂ) + ((326204 / 93615) : ℂ) * ζ ^ 1 - ((564893 / 93615) : ℂ) * ζ ^ 2 - ((100492 / 31205) : ℂ) * ζ ^ 3 - ((76671 / 31205) : ℂ) * ζ ^ 5 - ((186534 / 31205) : ℂ) * ζ ^ 6 - ((105191 / 18723) : ℂ) * ζ ^ 8 - ((733838 / 93615) : ℂ) * ζ ^ 9 - ((432362 / 93615) : ℂ) * ζ ^ 11 - ((105191 / 18723) : ℂ) * ζ ^ 12 - ((326204 / 93615) : ℂ) * ζ ^ 13 - ((254741 / 93615) : ℂ) * ζ ^ 15 - ((326204 / 93615) : ℂ) * ζ ^ 17 - ((5291 / 93615) : ℂ) * ζ ^ 18 - ((24728 / 93615) : ℂ) * ζ ^ 21 + ((564893 / 93615) : ℂ) * ζ ^ 22 + ((556217 / 93615) : ℂ) * ζ ^ 25 + ((24728 / 93615) : ℂ) * ζ ^ 27 + ((105191 / 18723) : ℂ) * ζ ^ 28 + ((326204 / 93615) : ℂ) * ζ ^ 29 - ((93267 / 31205) : ℂ) * ζ ^ 30 + ((432362 / 93615) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep04CoefficientIdentity04 :
    row18_reducedY33_combinationStep04Coefficient04 =
      row18_reducedY33_combinationStep03Coefficient04 +
        row18_reducedY33_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep04Coefficient04 row18_reducedY33_combinationStep03Coefficient04 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep04Coefficient05 : ℂ :=
  (-((2223 / 6241) : ℂ) + ((9192 / 6241) : ℂ) * ζ ^ 1 - ((201011 / 37446) : ℂ) * ζ ^ 2 - ((25171 / 6241) : ℂ) * ζ ^ 5 - ((187673 / 37446) : ℂ) * ζ ^ 6 - ((187673 / 37446) : ℂ) * ζ ^ 8 - ((25171 / 6241) : ℂ) * ζ ^ 9 - ((79151 / 12482) : ℂ) * ζ ^ 11 - ((25515 / 6241) : ℂ) * ζ ^ 12 - ((9192 / 6241) : ℂ) * ζ ^ 13 - ((58274 / 18723) : ℂ) * ζ ^ 15 - ((9192 / 6241) : ℂ) * ζ ^ 17 + ((18115 / 6241) : ℂ) * ζ ^ 18 + ((15979 / 12482) : ℂ) * ζ ^ 21 + ((201011 / 37446) : ℂ) * ζ ^ 22 + ((78983 / 37446) : ℂ) * ζ ^ 24 + ((34363 / 6241) : ℂ) * ζ ^ 25 + ((58274 / 18723) : ℂ) * ζ ^ 27 + ((187673 / 37446) : ℂ) * ζ ^ 28 + ((9192 / 6241) : ℂ) * ζ ^ 29 - ((34583 / 37446) : ℂ) * ζ ^ 30 + ((79151 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep04CoefficientIdentity05 :
    row18_reducedY33_combinationStep04Coefficient05 =
      row18_reducedY33_combinationStep03Coefficient05 +
        row18_reducedY33_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep04Coefficient05 row18_reducedY33_combinationStep03Coefficient05 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep04Coefficient06 : ℂ :=
  (-((262666 / 93615) : ℂ) - ((35608 / 6241) : ℂ) * ζ ^ 1 - ((734687 / 93615) : ℂ) * ζ ^ 2 - ((90047 / 18723) : ℂ) * ζ ^ 3 + ((11229 / 31205) : ℂ) * ζ ^ 6 - ((319912 / 93615) : ℂ) * ζ ^ 8 - ((116045 / 18723) : ℂ) * ζ ^ 9 + ((34991 / 6241) : ℂ) * ζ ^ 11 + ((768374 / 93615) : ℂ) * ζ ^ 12 + ((35608 / 6241) : ℂ) * ζ ^ 13 - ((90047 / 18723) : ℂ) * ζ ^ 15 + ((35608 / 6241) : ℂ) * ζ ^ 17 + ((472021 / 93615) : ℂ) * ζ ^ 18 + ((35608 / 6241) : ℂ) * ζ ^ 21 + ((734687 / 93615) : ℂ) * ζ ^ 22 - ((734687 / 93615) : ℂ) * ζ ^ 24 - ((35608 / 6241) : ℂ) * ζ ^ 25 + ((34991 / 6241) : ℂ) * ζ ^ 27 + ((319912 / 93615) : ℂ) * ζ ^ 28 - ((35608 / 6241) : ℂ) * ζ ^ 29 - ((351533 / 31205) : ℂ) * ζ ^ 30 - ((34991 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep04CoefficientIdentity06 :
    row18_reducedY33_combinationStep04Coefficient06 =
      row18_reducedY33_combinationStep03Coefficient06 +
        row18_reducedY33_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep04Coefficient06 row18_reducedY33_combinationStep03Coefficient06 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep04Coefficient07 : ℂ :=
  (((19208 / 6241) : ℂ) + ((55013 / 18723) : ℂ) * ζ ^ 1 - ((107881 / 37446) : ℂ) * ζ ^ 2 - ((164489 / 37446) : ℂ) * ζ ^ 3 + ((63581 / 37446) : ℂ) * ζ ^ 5 + ((562 / 18723) : ℂ) * ζ ^ 6 - ((37971 / 12482) : ℂ) * ζ ^ 8 - ((97025 / 37446) : ℂ) * ζ ^ 9 + ((11244 / 6241) : ℂ) * ζ ^ 11 - ((37971 / 12482) : ℂ) * ζ ^ 12 - ((55013 / 18723) : ℂ) * ζ ^ 13 + ((19674 / 6241) : ℂ) * ζ ^ 15 - ((55013 / 18723) : ℂ) * ζ ^ 17 - ((36335 / 12482) : ℂ) * ζ ^ 18 + ((54463 / 37446) : ℂ) * ζ ^ 21 + ((107881 / 37446) : ℂ) * ζ ^ 22 + ((46445 / 37446) : ℂ) * ζ ^ 25 - ((54463 / 37446) : ℂ) * ζ ^ 27 + ((37971 / 12482) : ℂ) * ζ ^ 28 + ((55013 / 18723) : ℂ) * ζ ^ 29 + ((281 / 18723) : ℂ) * ζ ^ 30 - ((11244 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep04CoefficientIdentity07 :
    row18_reducedY33_combinationStep04Coefficient07 =
      row18_reducedY33_combinationStep03Coefficient07 +
        row18_reducedY33_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep04Coefficient07 row18_reducedY33_combinationStep03Coefficient07 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep04Coefficient08 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep04CoefficientIdentity08 :
    row18_reducedY33_combinationStep04Coefficient08 =
      row18_reducedY33_combinationStep03Coefficient08 +
        row18_reducedY33_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep04Coefficient08 row18_reducedY33_combinationStep03Coefficient08 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep04Coefficient09 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep04CoefficientIdentity09 :
    row18_reducedY33_combinationStep04Coefficient09 =
      row18_reducedY33_combinationStep03Coefficient09 +
        row18_reducedY33_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep04Coefficient09 row18_reducedY33_combinationStep03Coefficient09 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep04Coefficient10 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep04CoefficientIdentity10 :
    row18_reducedY33_combinationStep04Coefficient10 =
      row18_reducedY33_combinationStep03Coefficient10 +
        row18_reducedY33_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep04Coefficient10 row18_reducedY33_combinationStep03Coefficient10 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep04Coefficient11 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep04CoefficientIdentity11 :
    row18_reducedY33_combinationStep04Coefficient11 =
      row18_reducedY33_combinationStep03Coefficient11 +
        row18_reducedY33_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep04Coefficient11 row18_reducedY33_combinationStep03Coefficient11 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep04Coefficient12 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep04CoefficientIdentity12 :
    row18_reducedY33_combinationStep04Coefficient12 =
      row18_reducedY33_combinationStep03Coefficient12 +
        row18_reducedY33_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep04Coefficient12 row18_reducedY33_combinationStep03Coefficient12 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep04Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep04CoefficientIdentity13 :
    row18_reducedY33_combinationStep04Coefficient13 =
      row18_reducedY33_combinationStep03Coefficient13 +
        row18_reducedY33_combinationStep04Multiplier *
          (-((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((73 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((105 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((73 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep04Coefficient13 row18_reducedY33_combinationStep03Coefficient13 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 (-((3276 / 6241) : ℂ) - ((625 / 12482) : ℂ) * ζ ^ 1 + ((689 / 6241) : ℂ) * ζ ^ 2 - ((3167 / 12482) : ℂ) * ζ ^ 3 - ((1285 / 12482) : ℂ) * ζ ^ 4 - ((117 / 6241) : ℂ) * ζ ^ 5 + ((5201 / 12482) : ℂ) * ζ ^ 6 + ((3018 / 6241) : ℂ) * ζ ^ 7 + ((4811 / 12482) : ℂ) * ζ ^ 8 - ((784 / 6241) : ℂ) * ζ ^ 9 - ((8487 / 6241) : ℂ) * ζ ^ 10 - ((4803 / 12482) : ℂ) * ζ ^ 11 + ((6691 / 12482) : ℂ) * ζ ^ 12 + ((178 / 6241) : ℂ) * ζ ^ 13 + ((6775 / 6241) : ℂ) * ζ ^ 14 - ((4021 / 12482) : ℂ) * ζ ^ 15 - ((19101 / 12482) : ℂ) * ζ ^ 16 - ((4973 / 12482) : ℂ) * ζ ^ 17 - ((4376 / 6241) : ℂ) * ζ ^ 18 + ((66 / 6241) : ℂ) * ζ ^ 19 + ((8447 / 12482) : ℂ) * ζ ^ 20 + ((551 / 6241) : ℂ) * ζ ^ 21 - ((119 / 6241) : ℂ) * ζ ^ 22 + ((550 / 6241) : ℂ) * ζ ^ 23 - ((2929 / 12482) : ℂ) * ζ ^ 24 + ((445 / 12482) : ℂ) * ζ ^ 25 + ((1398 / 6241) : ℂ) * ζ ^ 26 + ((1144 / 6241) : ℂ) * ζ ^ 27 + ((2973 / 12482) : ℂ) * ζ ^ 28 + ((1083 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep04Coefficient14 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep04CoefficientIdentity14 :
    row18_reducedY33_combinationStep04Coefficient14 =
      row18_reducedY33_combinationStep03Coefficient14 +
        row18_reducedY33_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep04Coefficient14 row18_reducedY33_combinationStep03Coefficient14 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep04Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep04CoefficientIdentity15 :
    row18_reducedY33_combinationStep04Coefficient15 =
      row18_reducedY33_combinationStep03Coefficient15 +
        row18_reducedY33_combinationStep04Multiplier *
          (((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep04Coefficient15 row18_reducedY33_combinationStep03Coefficient15 row18_reducedY33_combinationStep04Multiplier
  close_cyclotomic_row18 (((2474 / 6241) : ℂ) - ((6163 / 12482) : ℂ) * ζ ^ 1 - ((3250 / 6241) : ℂ) * ζ ^ 2 + ((1919 / 6241) : ℂ) * ζ ^ 3 - ((7587 / 12482) : ℂ) * ζ ^ 4 + ((3018 / 6241) : ℂ) * ζ ^ 5 + ((1520 / 6241) : ℂ) * ζ ^ 6 - ((3459 / 6241) : ℂ) * ζ ^ 7 + ((315 / 12482) : ℂ) * ζ ^ 8 + ((1635 / 12482) : ℂ) * ζ ^ 9 - ((2433 / 12482) : ℂ) * ζ ^ 10 - ((203 / 12482) : ℂ) * ζ ^ 11 + ((1748 / 6241) : ℂ) * ζ ^ 12 - ((1205 / 6241) : ℂ) * ζ ^ 13 + ((837 / 12482) : ℂ) * ζ ^ 14 - ((894 / 6241) : ℂ) * ζ ^ 15 - ((247 / 12482) : ℂ) * ζ ^ 16 - ((163 / 6241) : ℂ) * ζ ^ 17 - ((1985 / 12482) : ℂ) * ζ ^ 18 + ((1125 / 6241) : ℂ) * ζ ^ 19 - ((871 / 12482) : ℂ) * ζ ^ 20 - ((706 / 6241) : ℂ) * ζ ^ 21 + ((3236 / 6241) : ℂ) * ζ ^ 22 - ((2 / 79) : ℂ) * ζ ^ 23 + ((710 / 6241) : ℂ) * ζ ^ 24 - ((240 / 6241) : ℂ) * ζ ^ 25 - ((10525 / 12482) : ℂ) * ζ ^ 26 + ((162 / 6241) : ℂ) * ζ ^ 27 + ((3337 / 12482) : ℂ) * ζ ^ 28 + ((741 / 12482) : ℂ) * ζ ^ 29 - ((705 / 12482) : ℂ) * ζ ^ 30)

private theorem row18_reducedY33_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY33_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY33_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY33_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY33_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY33_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY33_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY33_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY33_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY33_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY33_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY33_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY33_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY33_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY33_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY33_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY33_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY33_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation07
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY33_combinationStep04CoefficientIdentity00,
      row18_reducedY33_combinationStep04CoefficientIdentity01,
      row18_reducedY33_combinationStep04CoefficientIdentity02,
      row18_reducedY33_combinationStep04CoefficientIdentity03,
      row18_reducedY33_combinationStep04CoefficientIdentity04,
      row18_reducedY33_combinationStep04CoefficientIdentity05,
      row18_reducedY33_combinationStep04CoefficientIdentity06,
      row18_reducedY33_combinationStep04CoefficientIdentity07,
      row18_reducedY33_combinationStep04CoefficientIdentity08,
      row18_reducedY33_combinationStep04CoefficientIdentity09,
      row18_reducedY33_combinationStep04CoefficientIdentity10,
      row18_reducedY33_combinationStep04CoefficientIdentity11,
      row18_reducedY33_combinationStep04CoefficientIdentity12,
      row18_reducedY33_combinationStep04CoefficientIdentity13,
      row18_reducedY33_combinationStep04CoefficientIdentity14,
      row18_reducedY33_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY33_combinationStep04Multiplier * equation

private def row18_reducedY33_combinationStep05Multiplier : ℂ :=
  (-((11504 / 1185) : ℂ) - ((116 / 15) : ℂ) * ζ ^ 1 + ((7228 / 1185) : ℂ) * ζ ^ 2 + ((1864 / 237) : ℂ) * ζ ^ 3 - ((128 / 15) : ℂ) * ζ ^ 5 - ((3428 / 1185) : ℂ) * ζ ^ 6 + ((11392 / 1185) : ℂ) * ζ ^ 8 + ((52 / 15) : ℂ) * ζ ^ 9 - ((1220 / 237) : ℂ) * ζ ^ 11 + ((3552 / 395) : ℂ) * ζ ^ 12 + ((116 / 15) : ℂ) * ζ ^ 13 - ((1864 / 237) : ℂ) * ζ ^ 15 + ((116 / 15) : ℂ) * ζ ^ 17 + ((4276 / 1185) : ℂ) * ζ ^ 18 + ((4 / 5) : ℂ) * ζ ^ 21 - ((7228 / 1185) : ℂ) * ζ ^ 22 - ((7228 / 1185) : ℂ) * ζ ^ 24 + ((4 / 5) : ℂ) * ζ ^ 25 + ((1220 / 237) : ℂ) * ζ ^ 27 - ((11392 / 1185) : ℂ) * ζ ^ 28 - ((116 / 15) : ℂ) * ζ ^ 29 - ((1388 / 395) : ℂ) * ζ ^ 30 + ((1220 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY33_combinationStep05Coefficient00 : ℂ :=
  (((77 / 79) : ℂ) - ((1852 / 395) : ℂ) * ζ ^ 1 + ((3234 / 395) : ℂ) * ζ ^ 2 + ((1588 / 395) : ℂ) * ζ ^ 3 + ((1109 / 395) : ℂ) * ζ ^ 5 + ((3186 / 395) : ℂ) * ζ ^ 6 + ((572 / 79) : ℂ) * ζ ^ 8 + ((3744 / 395) : ℂ) * ζ ^ 9 + ((2156 / 395) : ℂ) * ζ ^ 11 + ((572 / 79) : ℂ) * ζ ^ 12 + ((1852 / 395) : ℂ) * ζ ^ 13 + ((1373 / 395) : ℂ) * ζ ^ 15 + ((1852 / 395) : ℂ) * ζ ^ 17 + ((48 / 395) : ℂ) * ζ ^ 18 + ((264 / 395) : ℂ) * ζ ^ 21 - ((3234 / 395) : ℂ) * ζ ^ 22 - ((2961 / 395) : ℂ) * ζ ^ 25 - ((264 / 395) : ℂ) * ζ ^ 27 - ((572 / 79) : ℂ) * ζ ^ 28 - ((1852 / 395) : ℂ) * ζ ^ 29 + ((1593 / 395) : ℂ) * ζ ^ 30 - ((2156 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep05CoefficientIdentity00 :
    row18_reducedY33_combinationStep05Coefficient00 =
      row18_reducedY33_combinationStep04Coefficient00 +
        row18_reducedY33_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep05Coefficient00 row18_reducedY33_combinationStep04Coefficient00 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep05Coefficient01 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep05CoefficientIdentity01 :
    row18_reducedY33_combinationStep05Coefficient01 =
      row18_reducedY33_combinationStep04Coefficient01 +
        row18_reducedY33_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep05Coefficient01 row18_reducedY33_combinationStep04Coefficient01 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep05Coefficient02 : ℂ :=
  (((110676 / 31205) : ℂ) + ((31009 / 93615) : ℂ) * ζ ^ 1 - ((232316 / 93615) : ℂ) * ζ ^ 2 + ((60667 / 18723) : ℂ) * ζ ^ 3 - ((900428 / 93615) : ℂ) * ζ ^ 5 + ((130936 / 93615) : ℂ) * ζ ^ 6 - ((473659 / 93615) : ℂ) * ζ ^ 8 - ((481223 / 93615) : ℂ) * ζ ^ 9 - ((71891 / 6241) : ℂ) * ζ ^ 11 - ((121084 / 31205) : ℂ) * ζ ^ 12 - ((31009 / 93615) : ℂ) * ζ ^ 13 - ((60667 / 18723) : ℂ) * ζ ^ 15 - ((31009 / 93615) : ℂ) * ζ ^ 17 - ((99712 / 93615) : ℂ) * ζ ^ 18 + ((310479 / 31205) : ℂ) * ζ ^ 21 + ((232316 / 93615) : ℂ) * ζ ^ 22 + ((232316 / 93615) : ℂ) * ζ ^ 24 + ((310479 / 31205) : ℂ) * ζ ^ 25 + ((71891 / 6241) : ℂ) * ζ ^ 27 + ((473659 / 93615) : ℂ) * ζ ^ 28 + ((31009 / 93615) : ℂ) * ζ ^ 29 + ((241343 / 93615) : ℂ) * ζ ^ 30 + ((71891 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep05CoefficientIdentity02 :
    row18_reducedY33_combinationStep05Coefficient02 =
      row18_reducedY33_combinationStep04Coefficient02 +
        row18_reducedY33_combinationStep05Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep05Coefficient02 row18_reducedY33_combinationStep04Coefficient02 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 (((119209 / 93615) : ℂ) + ((18829 / 31205) : ℂ) * ζ ^ 1 + ((90367 / 31205) : ℂ) * ζ ^ 2 + ((4664 / 18723) : ℂ) * ζ ^ 3 - ((251756 / 93615) : ℂ) * ζ ^ 4 - ((4965 / 6241) : ℂ) * ζ ^ 5 - ((9890 / 18723) : ℂ) * ζ ^ 6 + ((73704 / 31205) : ℂ) * ζ ^ 7 + ((56204 / 93615) : ℂ) * ζ ^ 8 - ((2891 / 6241) : ℂ) * ζ ^ 9 - ((14188 / 31205) : ℂ) * ζ ^ 10 - ((977 / 93615) : ℂ) * ζ ^ 11 - ((26078 / 31205) : ℂ) * ζ ^ 12 - ((45781 / 93615) : ℂ) * ζ ^ 13 + ((18298 / 31205) : ℂ) * ζ ^ 14 + ((30311 / 18723) : ℂ) * ζ ^ 15 + ((45456 / 31205) : ℂ) * ζ ^ 16 + ((35003 / 93615) : ℂ) * ζ ^ 17 - ((23972 / 93615) : ℂ) * ζ ^ 18 - ((29137 / 18723) : ℂ) * ζ ^ 19 - ((98387 / 93615) : ℂ) * ζ ^ 20 - ((59183 / 93615) : ℂ) * ζ ^ 21 - ((94013 / 93615) : ℂ) * ζ ^ 22 - ((27559 / 31205) : ℂ) * ζ ^ 23 + ((134383 / 93615) : ℂ) * ζ ^ 24 + ((49898 / 93615) : ℂ) * ζ ^ 25 + ((76627 / 93615) : ℂ) * ζ ^ 26 - ((68042 / 93615) : ℂ) * ζ ^ 27 + ((1357 / 93615) : ℂ) * ζ ^ 28 - ((38974 / 93615) : ℂ) * ζ ^ 29 + ((4270 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep05Coefficient03 : ℂ :=
  (-((16601 / 6241) : ℂ) - ((60701 / 18723) : ℂ) * ζ ^ 1 + ((51689 / 18723) : ℂ) * ζ ^ 2 + ((91369 / 18723) : ℂ) * ζ ^ 3 - ((29539 / 18723) : ℂ) * ζ ^ 5 - ((88 / 18723) : ℂ) * ζ ^ 6 + ((19183 / 6241) : ℂ) * ζ ^ 8 + ((59770 / 18723) : ℂ) * ζ ^ 9 - ((10533 / 6241) : ℂ) * ζ ^ 11 + ((19183 / 6241) : ℂ) * ζ ^ 12 + ((60701 / 18723) : ℂ) * ζ ^ 13 - ((20069 / 6241) : ℂ) * ζ ^ 15 + ((60701 / 18723) : ℂ) * ζ ^ 17 + ((17259 / 6241) : ℂ) * ζ ^ 18 - ((30668 / 18723) : ℂ) * ζ ^ 21 - ((51689 / 18723) : ℂ) * ζ ^ 22 - ((31162 / 18723) : ℂ) * ζ ^ 25 + ((30668 / 18723) : ℂ) * ζ ^ 27 - ((19183 / 6241) : ℂ) * ζ ^ 28 - ((60701 / 18723) : ℂ) * ζ ^ 29 - ((44 / 18723) : ℂ) * ζ ^ 30 + ((10533 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep05CoefficientIdentity03 :
    row18_reducedY33_combinationStep05Coefficient03 =
      row18_reducedY33_combinationStep04Coefficient03 +
        row18_reducedY33_combinationStep05Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep05Coefficient03 row18_reducedY33_combinationStep04Coefficient03 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 (-((283994 / 93615) : ℂ) + ((66367 / 31205) : ℂ) * ζ ^ 1 + ((91969 / 93615) : ℂ) * ζ ^ 2 - ((32620 / 18723) : ℂ) * ζ ^ 3 + ((42641 / 93615) : ℂ) * ζ ^ 4 - ((93941 / 93615) : ℂ) * ζ ^ 5 - ((20143 / 18723) : ℂ) * ζ ^ 6 - ((7940 / 6241) : ℂ) * ζ ^ 7 + ((95789 / 93615) : ℂ) * ζ ^ 8 - ((9138 / 6241) : ℂ) * ζ ^ 9 - ((81749 / 93615) : ℂ) * ζ ^ 10 - ((6436 / 6241) : ℂ) * ζ ^ 11 + ((38506 / 93615) : ℂ) * ζ ^ 12 - ((116498 / 93615) : ℂ) * ζ ^ 13 - ((318269 / 93615) : ℂ) * ζ ^ 14 - ((51403 / 93615) : ℂ) * ζ ^ 15 + ((31478 / 18723) : ℂ) * ζ ^ 16 - ((47514 / 31205) : ℂ) * ζ ^ 17 - ((108889 / 31205) : ℂ) * ζ ^ 18 - ((10720 / 18723) : ℂ) * ζ ^ 19 - ((45732 / 31205) : ℂ) * ζ ^ 20 - ((206351 / 93615) : ℂ) * ζ ^ 21 - ((201347 / 93615) : ℂ) * ζ ^ 22 + ((73417 / 31205) : ℂ) * ζ ^ 23 - ((151394 / 93615) : ℂ) * ζ ^ 24 + ((68587 / 93615) : ℂ) * ζ ^ 25 - ((5611 / 18723) : ℂ) * ζ ^ 26 + ((46697 / 93615) : ℂ) * ζ ^ 27 - ((71874 / 31205) : ℂ) * ζ ^ 28 + ((22939 / 31205) : ℂ) * ζ ^ 29 + ((3965 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep05Coefficient04 : ℂ :=
  (-((77 / 79) : ℂ) + ((1852 / 395) : ℂ) * ζ ^ 1 - ((3234 / 395) : ℂ) * ζ ^ 2 - ((1588 / 395) : ℂ) * ζ ^ 3 - ((1109 / 395) : ℂ) * ζ ^ 5 - ((3186 / 395) : ℂ) * ζ ^ 6 - ((572 / 79) : ℂ) * ζ ^ 8 - ((3744 / 395) : ℂ) * ζ ^ 9 - ((2156 / 395) : ℂ) * ζ ^ 11 - ((572 / 79) : ℂ) * ζ ^ 12 - ((1852 / 395) : ℂ) * ζ ^ 13 - ((1373 / 395) : ℂ) * ζ ^ 15 - ((1852 / 395) : ℂ) * ζ ^ 17 - ((48 / 395) : ℂ) * ζ ^ 18 - ((264 / 395) : ℂ) * ζ ^ 21 + ((3234 / 395) : ℂ) * ζ ^ 22 + ((2961 / 395) : ℂ) * ζ ^ 25 + ((264 / 395) : ℂ) * ζ ^ 27 + ((572 / 79) : ℂ) * ζ ^ 28 + ((1852 / 395) : ℂ) * ζ ^ 29 - ((1593 / 395) : ℂ) * ζ ^ 30 + ((2156 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep05CoefficientIdentity04 :
    row18_reducedY33_combinationStep05Coefficient04 =
      row18_reducedY33_combinationStep04Coefficient04 +
        row18_reducedY33_combinationStep05Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep05Coefficient04 row18_reducedY33_combinationStep04Coefficient04 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 (((283994 / 93615) : ℂ) - ((66367 / 31205) : ℂ) * ζ ^ 1 - ((91969 / 93615) : ℂ) * ζ ^ 2 + ((32620 / 18723) : ℂ) * ζ ^ 3 - ((42641 / 93615) : ℂ) * ζ ^ 4 + ((93941 / 93615) : ℂ) * ζ ^ 5 + ((20143 / 18723) : ℂ) * ζ ^ 6 + ((7940 / 6241) : ℂ) * ζ ^ 7 - ((95789 / 93615) : ℂ) * ζ ^ 8 + ((9138 / 6241) : ℂ) * ζ ^ 9 + ((81749 / 93615) : ℂ) * ζ ^ 10 + ((6436 / 6241) : ℂ) * ζ ^ 11 - ((38506 / 93615) : ℂ) * ζ ^ 12 + ((116498 / 93615) : ℂ) * ζ ^ 13 + ((318269 / 93615) : ℂ) * ζ ^ 14 + ((51403 / 93615) : ℂ) * ζ ^ 15 - ((31478 / 18723) : ℂ) * ζ ^ 16 + ((47514 / 31205) : ℂ) * ζ ^ 17 + ((108889 / 31205) : ℂ) * ζ ^ 18 + ((10720 / 18723) : ℂ) * ζ ^ 19 + ((45732 / 31205) : ℂ) * ζ ^ 20 + ((206351 / 93615) : ℂ) * ζ ^ 21 + ((201347 / 93615) : ℂ) * ζ ^ 22 - ((73417 / 31205) : ℂ) * ζ ^ 23 + ((151394 / 93615) : ℂ) * ζ ^ 24 - ((68587 / 93615) : ℂ) * ζ ^ 25 + ((5611 / 18723) : ℂ) * ζ ^ 26 - ((46697 / 93615) : ℂ) * ζ ^ 27 + ((71874 / 31205) : ℂ) * ζ ^ 28 - ((22939 / 31205) : ℂ) * ζ ^ 29 - ((3965 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep05Coefficient05 : ℂ :=
  (-((2223 / 6241) : ℂ) + ((9192 / 6241) : ℂ) * ζ ^ 1 - ((201011 / 37446) : ℂ) * ζ ^ 2 - ((25171 / 6241) : ℂ) * ζ ^ 5 - ((187673 / 37446) : ℂ) * ζ ^ 6 - ((187673 / 37446) : ℂ) * ζ ^ 8 - ((25171 / 6241) : ℂ) * ζ ^ 9 - ((79151 / 12482) : ℂ) * ζ ^ 11 - ((25515 / 6241) : ℂ) * ζ ^ 12 - ((9192 / 6241) : ℂ) * ζ ^ 13 - ((58274 / 18723) : ℂ) * ζ ^ 15 - ((9192 / 6241) : ℂ) * ζ ^ 17 + ((18115 / 6241) : ℂ) * ζ ^ 18 + ((15979 / 12482) : ℂ) * ζ ^ 21 + ((201011 / 37446) : ℂ) * ζ ^ 22 + ((78983 / 37446) : ℂ) * ζ ^ 24 + ((34363 / 6241) : ℂ) * ζ ^ 25 + ((58274 / 18723) : ℂ) * ζ ^ 27 + ((187673 / 37446) : ℂ) * ζ ^ 28 + ((9192 / 6241) : ℂ) * ζ ^ 29 - ((34583 / 37446) : ℂ) * ζ ^ 30 + ((79151 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep05CoefficientIdentity05 :
    row18_reducedY33_combinationStep05Coefficient05 =
      row18_reducedY33_combinationStep04Coefficient05 +
        row18_reducedY33_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep05Coefficient05 row18_reducedY33_combinationStep04Coefficient05 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep05Coefficient06 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep05CoefficientIdentity06 :
    row18_reducedY33_combinationStep05Coefficient06 =
      row18_reducedY33_combinationStep04Coefficient06 +
        row18_reducedY33_combinationStep05Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep05Coefficient06 row18_reducedY33_combinationStep04Coefficient06 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 (-((56878 / 31205) : ℂ) - ((296876 / 93615) : ℂ) * ζ ^ 1 - ((15560 / 6241) : ℂ) * ζ ^ 2 - ((507887 / 93615) : ℂ) * ζ ^ 3 - ((135942 / 31205) : ℂ) * ζ ^ 4 + ((451589 / 93615) : ℂ) * ζ ^ 5 + (9 : ℂ) * ζ ^ 6 + ((756322 / 93615) : ℂ) * ζ ^ 7 - ((333037 / 93615) : ℂ) * ζ ^ 8 - ((67901 / 6241) : ℂ) * ζ ^ 9 - ((815443 / 93615) : ℂ) * ζ ^ 10 - ((91567 / 31205) : ℂ) * ζ ^ 11 + ((553183 / 93615) : ℂ) * ζ ^ 12 + ((715916 / 93615) : ℂ) * ζ ^ 13 + ((40074 / 31205) : ℂ) * ζ ^ 14 - ((327412 / 93615) : ℂ) * ζ ^ 15 - ((164766 / 31205) : ℂ) * ζ ^ 16 - ((228483 / 31205) : ℂ) * ζ ^ 17 - ((36485 / 6241) : ℂ) * ζ ^ 18 - ((10442 / 18723) : ℂ) * ζ ^ 19 + ((230091 / 31205) : ℂ) * ζ ^ 20 + ((128882 / 31205) : ℂ) * ζ ^ 21 - ((208879 / 93615) : ℂ) * ζ ^ 22 - ((44738 / 6241) : ℂ) * ζ ^ 23 - ((306061 / 93615) : ℂ) * ζ ^ 24 + ((7062 / 31205) : ℂ) * ζ ^ 25 + ((415781 / 93615) : ℂ) * ζ ^ 26 + ((35153 / 18723) : ℂ) * ζ ^ 27 + ((2207 / 93615) : ℂ) * ζ ^ 28 - ((2484 / 31205) : ℂ) * ζ ^ 29 - ((8540 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep05Coefficient07 : ℂ :=
  (((19208 / 6241) : ℂ) + ((55013 / 18723) : ℂ) * ζ ^ 1 - ((107881 / 37446) : ℂ) * ζ ^ 2 - ((164489 / 37446) : ℂ) * ζ ^ 3 + ((63581 / 37446) : ℂ) * ζ ^ 5 + ((562 / 18723) : ℂ) * ζ ^ 6 - ((37971 / 12482) : ℂ) * ζ ^ 8 - ((97025 / 37446) : ℂ) * ζ ^ 9 + ((11244 / 6241) : ℂ) * ζ ^ 11 - ((37971 / 12482) : ℂ) * ζ ^ 12 - ((55013 / 18723) : ℂ) * ζ ^ 13 + ((19674 / 6241) : ℂ) * ζ ^ 15 - ((55013 / 18723) : ℂ) * ζ ^ 17 - ((36335 / 12482) : ℂ) * ζ ^ 18 + ((54463 / 37446) : ℂ) * ζ ^ 21 + ((107881 / 37446) : ℂ) * ζ ^ 22 + ((46445 / 37446) : ℂ) * ζ ^ 25 - ((54463 / 37446) : ℂ) * ζ ^ 27 + ((37971 / 12482) : ℂ) * ζ ^ 28 + ((55013 / 18723) : ℂ) * ζ ^ 29 + ((281 / 18723) : ℂ) * ζ ^ 30 - ((11244 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep05CoefficientIdentity07 :
    row18_reducedY33_combinationStep05Coefficient07 =
      row18_reducedY33_combinationStep04Coefficient07 +
        row18_reducedY33_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep05Coefficient07 row18_reducedY33_combinationStep04Coefficient07 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep05Coefficient08 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep05CoefficientIdentity08 :
    row18_reducedY33_combinationStep05Coefficient08 =
      row18_reducedY33_combinationStep04Coefficient08 +
        row18_reducedY33_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep05Coefficient08 row18_reducedY33_combinationStep04Coefficient08 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep05Coefficient09 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep05CoefficientIdentity09 :
    row18_reducedY33_combinationStep05Coefficient09 =
      row18_reducedY33_combinationStep04Coefficient09 +
        row18_reducedY33_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep05Coefficient09 row18_reducedY33_combinationStep04Coefficient09 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep05Coefficient10 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep05CoefficientIdentity10 :
    row18_reducedY33_combinationStep05Coefficient10 =
      row18_reducedY33_combinationStep04Coefficient10 +
        row18_reducedY33_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep05Coefficient10 row18_reducedY33_combinationStep04Coefficient10 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep05Coefficient11 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep05CoefficientIdentity11 :
    row18_reducedY33_combinationStep05Coefficient11 =
      row18_reducedY33_combinationStep04Coefficient11 +
        row18_reducedY33_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep05Coefficient11 row18_reducedY33_combinationStep04Coefficient11 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep05Coefficient12 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep05CoefficientIdentity12 :
    row18_reducedY33_combinationStep05Coefficient12 =
      row18_reducedY33_combinationStep04Coefficient12 +
        row18_reducedY33_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep05Coefficient12 row18_reducedY33_combinationStep04Coefficient12 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep05Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep05CoefficientIdentity13 :
    row18_reducedY33_combinationStep05Coefficient13 =
      row18_reducedY33_combinationStep04Coefficient13 +
        row18_reducedY33_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep05Coefficient13 row18_reducedY33_combinationStep04Coefficient13 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep05Coefficient14 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep05CoefficientIdentity14 :
    row18_reducedY33_combinationStep05Coefficient14 =
      row18_reducedY33_combinationStep04Coefficient14 +
        row18_reducedY33_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep05Coefficient14 row18_reducedY33_combinationStep04Coefficient14 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep05Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep05CoefficientIdentity15 :
    row18_reducedY33_combinationStep05Coefficient15 =
      row18_reducedY33_combinationStep04Coefficient15 +
        row18_reducedY33_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep05Coefficient15 row18_reducedY33_combinationStep04Coefficient15 row18_reducedY33_combinationStep05Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY33_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY33_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY33_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY33_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY33_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY33_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY33_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY33_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY33_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY33_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY33_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY33_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY33_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY33_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY33_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY33_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY33_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY33_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY33_combinationStep05CoefficientIdentity00,
      row18_reducedY33_combinationStep05CoefficientIdentity01,
      row18_reducedY33_combinationStep05CoefficientIdentity02,
      row18_reducedY33_combinationStep05CoefficientIdentity03,
      row18_reducedY33_combinationStep05CoefficientIdentity04,
      row18_reducedY33_combinationStep05CoefficientIdentity05,
      row18_reducedY33_combinationStep05CoefficientIdentity06,
      row18_reducedY33_combinationStep05CoefficientIdentity07,
      row18_reducedY33_combinationStep05CoefficientIdentity08,
      row18_reducedY33_combinationStep05CoefficientIdentity09,
      row18_reducedY33_combinationStep05CoefficientIdentity10,
      row18_reducedY33_combinationStep05CoefficientIdentity11,
      row18_reducedY33_combinationStep05CoefficientIdentity12,
      row18_reducedY33_combinationStep05CoefficientIdentity13,
      row18_reducedY33_combinationStep05CoefficientIdentity14,
      row18_reducedY33_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY33_combinationStep05Multiplier * equation

private def row18_reducedY33_combinationStep06Multiplier : ℂ :=
  (((168 / 79) : ℂ) + ((8 / 237) : ℂ) * ζ ^ 1 - ((620 / 79) : ℂ) * ζ ^ 2 - ((728 / 79) : ℂ) * ζ ^ 3 + ((1846 / 237) : ℂ) * ζ ^ 5 - ((1216 / 237) : ℂ) * ζ ^ 8 + ((364 / 237) : ℂ) * ζ ^ 9 + ((1820 / 237) : ℂ) * ζ ^ 11 + ((208 / 237) : ℂ) * ζ ^ 12 - ((8 / 237) : ℂ) * ζ ^ 13 + ((346 / 237) : ℂ) * ζ ^ 15 - ((8 / 237) : ℂ) * ζ ^ 17 + ((620 / 79) : ℂ) * ζ ^ 18 - ((2192 / 237) : ℂ) * ζ ^ 21 + ((620 / 79) : ℂ) * ζ ^ 22 + ((336 / 79) : ℂ) * ζ ^ 24 - ((1838 / 237) : ℂ) * ζ ^ 25 - ((2192 / 237) : ℂ) * ζ ^ 27 + ((1216 / 237) : ℂ) * ζ ^ 28 + ((8 / 237) : ℂ) * ζ ^ 29 - ((32 / 79) : ℂ) * ζ ^ 30 - ((1820 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY33_combinationStep06Coefficient00 : ℂ :=
  (((77 / 79) : ℂ) - ((1852 / 395) : ℂ) * ζ ^ 1 + ((3234 / 395) : ℂ) * ζ ^ 2 + ((1588 / 395) : ℂ) * ζ ^ 3 + ((1109 / 395) : ℂ) * ζ ^ 5 + ((3186 / 395) : ℂ) * ζ ^ 6 + ((572 / 79) : ℂ) * ζ ^ 8 + ((3744 / 395) : ℂ) * ζ ^ 9 + ((2156 / 395) : ℂ) * ζ ^ 11 + ((572 / 79) : ℂ) * ζ ^ 12 + ((1852 / 395) : ℂ) * ζ ^ 13 + ((1373 / 395) : ℂ) * ζ ^ 15 + ((1852 / 395) : ℂ) * ζ ^ 17 + ((48 / 395) : ℂ) * ζ ^ 18 + ((264 / 395) : ℂ) * ζ ^ 21 - ((3234 / 395) : ℂ) * ζ ^ 22 - ((2961 / 395) : ℂ) * ζ ^ 25 - ((264 / 395) : ℂ) * ζ ^ 27 - ((572 / 79) : ℂ) * ζ ^ 28 - ((1852 / 395) : ℂ) * ζ ^ 29 + ((1593 / 395) : ℂ) * ζ ^ 30 - ((2156 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep06CoefficientIdentity00 :
    row18_reducedY33_combinationStep06Coefficient00 =
      row18_reducedY33_combinationStep05Coefficient00 +
        row18_reducedY33_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep06Coefficient00 row18_reducedY33_combinationStep05Coefficient00 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep06Coefficient01 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep06CoefficientIdentity01 :
    row18_reducedY33_combinationStep06Coefficient01 =
      row18_reducedY33_combinationStep05Coefficient01 +
        row18_reducedY33_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep06Coefficient01 row18_reducedY33_combinationStep05Coefficient01 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep06Coefficient02 : ℂ :=
  (((1134 / 395) : ℂ) - ((523 / 395) : ℂ) * ζ ^ 1 - ((5481 / 790) : ℂ) * ζ ^ 2 + ((509 / 158) : ℂ) * ζ ^ 3 - ((2959 / 395) : ℂ) * ζ ^ 5 - ((2549 / 790) : ℂ) * ζ ^ 6 - ((3402 / 395) : ℂ) * ζ ^ 8 - ((1913 / 790) : ℂ) * ζ ^ 9 - ((1085 / 158) : ℂ) * ζ ^ 11 - ((1466 / 395) : ℂ) * ζ ^ 12 + ((523 / 395) : ℂ) * ζ ^ 13 - ((509 / 158) : ℂ) * ζ ^ 15 + ((523 / 395) : ℂ) * ζ ^ 17 + ((3213 / 790) : ℂ) * ζ ^ 18 + ((2436 / 395) : ℂ) * ζ ^ 21 + ((5481 / 790) : ℂ) * ζ ^ 22 + ((5481 / 790) : ℂ) * ζ ^ 24 + ((2436 / 395) : ℂ) * ζ ^ 25 + ((1085 / 158) : ℂ) * ζ ^ 27 + ((3402 / 395) : ℂ) * ζ ^ 28 - ((523 / 395) : ℂ) * ζ ^ 29 + ((1323 / 790) : ℂ) * ζ ^ 30 + ((1085 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep06CoefficientIdentity02 :
    row18_reducedY33_combinationStep06Coefficient02 =
      row18_reducedY33_combinationStep05Coefficient02 +
        row18_reducedY33_combinationStep06Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep06Coefficient02 row18_reducedY33_combinationStep05Coefficient02 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 (((5814 / 6241) : ℂ) + ((9810 / 6241) : ℂ) * ζ ^ 1 + ((44751 / 12482) : ℂ) * ζ ^ 2 - ((34709 / 37446) : ℂ) * ζ ^ 3 - ((5169 / 6241) : ℂ) * ζ ^ 4 - ((46568 / 18723) : ℂ) * ζ ^ 5 + ((61721 / 37446) : ℂ) * ζ ^ 6 + ((22499 / 18723) : ℂ) * ζ ^ 7 + ((36158 / 18723) : ℂ) * ζ ^ 8 - ((17463 / 12482) : ℂ) * ζ ^ 9 - ((16241 / 37446) : ℂ) * ζ ^ 10 + ((9685 / 37446) : ℂ) * ζ ^ 11 + ((20791 / 18723) : ℂ) * ζ ^ 12 - ((46 / 237) : ℂ) * ζ ^ 13 - ((1012 / 6241) : ℂ) * ζ ^ 14 - ((78127 / 37446) : ℂ) * ζ ^ 15 - ((740 / 6241) : ℂ) * ζ ^ 16 + ((5143 / 6241) : ℂ) * ζ ^ 17 + ((37208 / 18723) : ℂ) * ζ ^ 18 + ((677 / 18723) : ℂ) * ζ ^ 19 - ((32168 / 18723) : ℂ) * ζ ^ 20 - ((24131 / 12482) : ℂ) * ζ ^ 21 + ((13663 / 37446) : ℂ) * ζ ^ 22 + ((17000 / 18723) : ℂ) * ζ ^ 23 + ((61721 / 37446) : ℂ) * ζ ^ 24 - ((30 / 6241) : ℂ) * ζ ^ 25 - ((21464 / 18723) : ℂ) * ζ ^ 26 - ((31189 / 18723) : ℂ) * ζ ^ 27 + ((7037 / 18723) : ℂ) * ζ ^ 28 + ((7400 / 6241) : ℂ) * ζ ^ 29 + ((2275 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep06Coefficient03 : ℂ :=
  (-((46 / 79) : ℂ) - ((24 / 79) : ℂ) * ζ ^ 1 - ((19 / 158) : ℂ) * ζ ^ 2 + ((77 / 158) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((2 / 79) : ℂ) * ζ ^ 6 + ((5 / 158) : ℂ) * ζ ^ 8 + ((95 / 158) : ℂ) * ζ ^ 9 + ((9 / 79) : ℂ) * ζ ^ 11 + ((5 / 158) : ℂ) * ζ ^ 12 + ((24 / 79) : ℂ) * ζ ^ 13 - ((5 / 79) : ℂ) * ζ ^ 15 + ((24 / 79) : ℂ) * ζ ^ 17 - ((23 / 158) : ℂ) * ζ ^ 18 - ((29 / 158) : ℂ) * ζ ^ 21 + ((19 / 158) : ℂ) * ζ ^ 22 - ((67 / 158) : ℂ) * ζ ^ 25 + ((29 / 158) : ℂ) * ζ ^ 27 - ((5 / 158) : ℂ) * ζ ^ 28 - ((24 / 79) : ℂ) * ζ ^ 29 + ((1 / 79) : ℂ) * ζ ^ 30 - ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep06CoefficientIdentity03 :
    row18_reducedY33_combinationStep06Coefficient03 =
      row18_reducedY33_combinationStep05Coefficient03 +
        row18_reducedY33_combinationStep06Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep06Coefficient03 row18_reducedY33_combinationStep05Coefficient03 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 (-((11623 / 6241) : ℂ) - ((47767 / 18723) : ℂ) * ζ ^ 1 + ((115897 / 37446) : ℂ) * ζ ^ 2 + ((57727 / 37446) : ℂ) * ζ ^ 3 - ((65692 / 18723) : ℂ) * ζ ^ 4 - ((4913 / 37446) : ℂ) * ζ ^ 5 + ((127 / 237) : ℂ) * ζ ^ 6 - ((1890 / 6241) : ℂ) * ζ ^ 7 + ((7455 / 6241) : ℂ) * ζ ^ 8 + ((49759 / 18723) : ℂ) * ζ ^ 9 + ((875 / 18723) : ℂ) * ζ ^ 10 - ((22336 / 18723) : ℂ) * ζ ^ 11 - ((87247 / 37446) : ℂ) * ζ ^ 12 - ((1414 / 18723) : ℂ) * ζ ^ 13 + ((42134 / 6241) : ℂ) * ζ ^ 14 + ((100153 / 37446) : ℂ) * ζ ^ 15 + ((14657 / 18723) : ℂ) * ζ ^ 16 - ((18936 / 6241) : ℂ) * ζ ^ 17 - ((17101 / 6241) : ℂ) * ζ ^ 18 + ((28583 / 18723) : ℂ) * ζ ^ 19 + ((54165 / 6241) : ℂ) * ζ ^ 20 + ((58321 / 18723) : ℂ) * ζ ^ 21 - ((27635 / 37446) : ℂ) * ζ ^ 22 - ((81152 / 18723) : ℂ) * ζ ^ 23 + ((4388 / 18723) : ℂ) * ζ ^ 24 + ((6336 / 6241) : ℂ) * ζ ^ 25 + ((65488 / 18723) : ℂ) * ζ ^ 26 + ((1732 / 18723) : ℂ) * ζ ^ 27 - ((26455 / 18723) : ℂ) * ζ ^ 28 - ((3864 / 6241) : ℂ) * ζ ^ 29 - ((12740 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep06Coefficient04 : ℂ :=
  (-((77 / 79) : ℂ) + ((1852 / 395) : ℂ) * ζ ^ 1 - ((3234 / 395) : ℂ) * ζ ^ 2 - ((1588 / 395) : ℂ) * ζ ^ 3 - ((1109 / 395) : ℂ) * ζ ^ 5 - ((3186 / 395) : ℂ) * ζ ^ 6 - ((572 / 79) : ℂ) * ζ ^ 8 - ((3744 / 395) : ℂ) * ζ ^ 9 - ((2156 / 395) : ℂ) * ζ ^ 11 - ((572 / 79) : ℂ) * ζ ^ 12 - ((1852 / 395) : ℂ) * ζ ^ 13 - ((1373 / 395) : ℂ) * ζ ^ 15 - ((1852 / 395) : ℂ) * ζ ^ 17 - ((48 / 395) : ℂ) * ζ ^ 18 - ((264 / 395) : ℂ) * ζ ^ 21 + ((3234 / 395) : ℂ) * ζ ^ 22 + ((2961 / 395) : ℂ) * ζ ^ 25 + ((264 / 395) : ℂ) * ζ ^ 27 + ((572 / 79) : ℂ) * ζ ^ 28 + ((1852 / 395) : ℂ) * ζ ^ 29 - ((1593 / 395) : ℂ) * ζ ^ 30 + ((2156 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep06CoefficientIdentity04 :
    row18_reducedY33_combinationStep06Coefficient04 =
      row18_reducedY33_combinationStep05Coefficient04 +
        row18_reducedY33_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep06Coefficient04 row18_reducedY33_combinationStep05Coefficient04 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep06Coefficient05 : ℂ :=
  (-((26 / 79) : ℂ) + ((193 / 79) : ℂ) * ζ ^ 1 - ((483 / 79) : ℂ) * ζ ^ 2 - ((555 / 79) : ℂ) * ζ ^ 5 - ((457 / 79) : ℂ) * ζ ^ 6 - ((457 / 79) : ℂ) * ζ ^ 8 - ((555 / 79) : ℂ) * ζ ^ 9 - ((677 / 79) : ℂ) * ζ ^ 11 - ((340 / 79) : ℂ) * ζ ^ 12 - ((193 / 79) : ℂ) * ζ ^ 13 - ((357 / 79) : ℂ) * ζ ^ 15 - ((193 / 79) : ℂ) * ζ ^ 17 + ((186 / 79) : ℂ) * ζ ^ 18 + ((181 / 79) : ℂ) * ζ ^ 21 + ((483 / 79) : ℂ) * ζ ^ 22 + ((271 / 79) : ℂ) * ζ ^ 24 + ((748 / 79) : ℂ) * ζ ^ 25 + ((357 / 79) : ℂ) * ζ ^ 27 + ((457 / 79) : ℂ) * ζ ^ 28 + ((193 / 79) : ℂ) * ζ ^ 29 - ((117 / 79) : ℂ) * ζ ^ 30 + ((677 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep06CoefficientIdentity05 :
    row18_reducedY33_combinationStep06Coefficient05 =
      row18_reducedY33_combinationStep05Coefficient05 +
        row18_reducedY33_combinationStep06Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep06Coefficient05 row18_reducedY33_combinationStep05Coefficient05 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 (-((3067 / 6241) : ℂ) - ((2531 / 6241) : ℂ) * ζ ^ 1 + ((90173 / 37446) : ℂ) * ζ ^ 2 - ((1715 / 6241) : ℂ) * ζ ^ 3 - ((33076 / 18723) : ℂ) * ζ ^ 4 + ((39657 / 12482) : ℂ) * ζ ^ 5 + ((26303 / 37446) : ℂ) * ζ ^ 6 - ((25793 / 12482) : ℂ) * ζ ^ 7 + ((112427 / 37446) : ℂ) * ζ ^ 8 - ((7097 / 37446) : ℂ) * ζ ^ 9 + ((107 / 18723) : ℂ) * ζ ^ 10 + ((18680 / 18723) : ℂ) * ζ ^ 11 + ((41603 / 37446) : ℂ) * ζ ^ 12 + ((16067 / 37446) : ℂ) * ζ ^ 13 + ((2101 / 6241) : ℂ) * ζ ^ 14 + ((11199 / 12482) : ℂ) * ζ ^ 15 + ((7823 / 12482) : ℂ) * ζ ^ 16 + ((110495 / 37446) : ℂ) * ζ ^ 17 - ((77317 / 37446) : ℂ) * ζ ^ 18 + ((50047 / 18723) : ℂ) * ζ ^ 19 + ((76943 / 37446) : ℂ) * ζ ^ 20 + ((16297 / 18723) : ℂ) * ζ ^ 21 - ((71801 / 37446) : ℂ) * ζ ^ 22 + ((28868 / 6241) : ℂ) * ζ ^ 23 - ((17953 / 12482) : ℂ) * ζ ^ 24 + ((30586 / 18723) : ℂ) * ζ ^ 25 - ((3175 / 6241) : ℂ) * ζ ^ 26 + ((29390 / 18723) : ℂ) * ζ ^ 27 - ((37405 / 18723) : ℂ) * ζ ^ 28 + ((8294 / 6241) : ℂ) * ζ ^ 29 + ((5915 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep06Coefficient06 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep06CoefficientIdentity06 :
    row18_reducedY33_combinationStep06Coefficient06 =
      row18_reducedY33_combinationStep05Coefficient06 +
        row18_reducedY33_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep06Coefficient06 row18_reducedY33_combinationStep05Coefficient06 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep06Coefficient07 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY33_combinationStep06CoefficientIdentity07 :
    row18_reducedY33_combinationStep06Coefficient07 =
      row18_reducedY33_combinationStep05Coefficient07 +
        row18_reducedY33_combinationStep06Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep06Coefficient07 row18_reducedY33_combinationStep05Coefficient07 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 (((11623 / 6241) : ℂ) + ((47767 / 18723) : ℂ) * ζ ^ 1 - ((115897 / 37446) : ℂ) * ζ ^ 2 - ((57727 / 37446) : ℂ) * ζ ^ 3 + ((65692 / 18723) : ℂ) * ζ ^ 4 + ((4913 / 37446) : ℂ) * ζ ^ 5 - ((127 / 237) : ℂ) * ζ ^ 6 + ((1890 / 6241) : ℂ) * ζ ^ 7 - ((7455 / 6241) : ℂ) * ζ ^ 8 - ((49759 / 18723) : ℂ) * ζ ^ 9 - ((875 / 18723) : ℂ) * ζ ^ 10 + ((22336 / 18723) : ℂ) * ζ ^ 11 + ((87247 / 37446) : ℂ) * ζ ^ 12 + ((1414 / 18723) : ℂ) * ζ ^ 13 - ((42134 / 6241) : ℂ) * ζ ^ 14 - ((100153 / 37446) : ℂ) * ζ ^ 15 - ((14657 / 18723) : ℂ) * ζ ^ 16 + ((18936 / 6241) : ℂ) * ζ ^ 17 + ((17101 / 6241) : ℂ) * ζ ^ 18 - ((28583 / 18723) : ℂ) * ζ ^ 19 - ((54165 / 6241) : ℂ) * ζ ^ 20 - ((58321 / 18723) : ℂ) * ζ ^ 21 + ((27635 / 37446) : ℂ) * ζ ^ 22 + ((81152 / 18723) : ℂ) * ζ ^ 23 - ((4388 / 18723) : ℂ) * ζ ^ 24 - ((6336 / 6241) : ℂ) * ζ ^ 25 - ((65488 / 18723) : ℂ) * ζ ^ 26 - ((1732 / 18723) : ℂ) * ζ ^ 27 + ((26455 / 18723) : ℂ) * ζ ^ 28 + ((3864 / 6241) : ℂ) * ζ ^ 29 + ((12740 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep06Coefficient08 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep06CoefficientIdentity08 :
    row18_reducedY33_combinationStep06Coefficient08 =
      row18_reducedY33_combinationStep05Coefficient08 +
        row18_reducedY33_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep06Coefficient08 row18_reducedY33_combinationStep05Coefficient08 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep06Coefficient09 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep06CoefficientIdentity09 :
    row18_reducedY33_combinationStep06Coefficient09 =
      row18_reducedY33_combinationStep05Coefficient09 +
        row18_reducedY33_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep06Coefficient09 row18_reducedY33_combinationStep05Coefficient09 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep06Coefficient10 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep06CoefficientIdentity10 :
    row18_reducedY33_combinationStep06Coefficient10 =
      row18_reducedY33_combinationStep05Coefficient10 +
        row18_reducedY33_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep06Coefficient10 row18_reducedY33_combinationStep05Coefficient10 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep06Coefficient11 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep06CoefficientIdentity11 :
    row18_reducedY33_combinationStep06Coefficient11 =
      row18_reducedY33_combinationStep05Coefficient11 +
        row18_reducedY33_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep06Coefficient11 row18_reducedY33_combinationStep05Coefficient11 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep06Coefficient12 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep06CoefficientIdentity12 :
    row18_reducedY33_combinationStep06Coefficient12 =
      row18_reducedY33_combinationStep05Coefficient12 +
        row18_reducedY33_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep06Coefficient12 row18_reducedY33_combinationStep05Coefficient12 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep06Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep06CoefficientIdentity13 :
    row18_reducedY33_combinationStep06Coefficient13 =
      row18_reducedY33_combinationStep05Coefficient13 +
        row18_reducedY33_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep06Coefficient13 row18_reducedY33_combinationStep05Coefficient13 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep06Coefficient14 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep06CoefficientIdentity14 :
    row18_reducedY33_combinationStep06Coefficient14 =
      row18_reducedY33_combinationStep05Coefficient14 +
        row18_reducedY33_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep06Coefficient14 row18_reducedY33_combinationStep05Coefficient14 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep06Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep06CoefficientIdentity15 :
    row18_reducedY33_combinationStep06Coefficient15 =
      row18_reducedY33_combinationStep05Coefficient15 +
        row18_reducedY33_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep06Coefficient15 row18_reducedY33_combinationStep05Coefficient15 row18_reducedY33_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY33_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY33_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY33_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY33_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY33_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY33_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY33_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY33_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY33_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY33_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY33_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY33_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY33_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY33_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY33_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY33_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY33_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY33_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY33_combinationStep06CoefficientIdentity00,
      row18_reducedY33_combinationStep06CoefficientIdentity01,
      row18_reducedY33_combinationStep06CoefficientIdentity02,
      row18_reducedY33_combinationStep06CoefficientIdentity03,
      row18_reducedY33_combinationStep06CoefficientIdentity04,
      row18_reducedY33_combinationStep06CoefficientIdentity05,
      row18_reducedY33_combinationStep06CoefficientIdentity06,
      row18_reducedY33_combinationStep06CoefficientIdentity07,
      row18_reducedY33_combinationStep06CoefficientIdentity08,
      row18_reducedY33_combinationStep06CoefficientIdentity09,
      row18_reducedY33_combinationStep06CoefficientIdentity10,
      row18_reducedY33_combinationStep06CoefficientIdentity11,
      row18_reducedY33_combinationStep06CoefficientIdentity12,
      row18_reducedY33_combinationStep06CoefficientIdentity13,
      row18_reducedY33_combinationStep06CoefficientIdentity14,
      row18_reducedY33_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY33_combinationStep06Multiplier * equation

private def row18_reducedY33_combinationStep07Multiplier : ℂ :=
  (-((208 / 79) : ℂ) - ((380 / 79) : ℂ) * ζ ^ 1 + ((60 / 79) : ℂ) * ζ ^ 2 - ((132 / 79) : ℂ) * ζ ^ 3 - ((306 / 79) : ℂ) * ζ ^ 5 + ((236 / 79) : ℂ) * ζ ^ 8 + ((156 / 79) : ℂ) * ζ ^ 9 - ((24 / 79) : ℂ) * ζ ^ 11 + ((180 / 79) : ℂ) * ζ ^ 12 + ((380 / 79) : ℂ) * ζ ^ 13 + ((58 / 79) : ℂ) * ζ ^ 15 + ((380 / 79) : ℂ) * ζ ^ 17 - ((60 / 79) : ℂ) * ζ ^ 18 + ((248 / 79) : ℂ) * ζ ^ 21 - ((60 / 79) : ℂ) * ζ ^ 22 - ((416 / 79) : ℂ) * ζ ^ 24 - ((74 / 79) : ℂ) * ζ ^ 25 + ((248 / 79) : ℂ) * ζ ^ 27 - ((236 / 79) : ℂ) * ζ ^ 28 - ((380 / 79) : ℂ) * ζ ^ 29 - ((160 / 79) : ℂ) * ζ ^ 30 + ((24 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY33_combinationStep07Coefficient00 : ℂ :=
  (((77 / 79) : ℂ) - ((1852 / 395) : ℂ) * ζ ^ 1 + ((3234 / 395) : ℂ) * ζ ^ 2 + ((1588 / 395) : ℂ) * ζ ^ 3 + ((1109 / 395) : ℂ) * ζ ^ 5 + ((3186 / 395) : ℂ) * ζ ^ 6 + ((572 / 79) : ℂ) * ζ ^ 8 + ((3744 / 395) : ℂ) * ζ ^ 9 + ((2156 / 395) : ℂ) * ζ ^ 11 + ((572 / 79) : ℂ) * ζ ^ 12 + ((1852 / 395) : ℂ) * ζ ^ 13 + ((1373 / 395) : ℂ) * ζ ^ 15 + ((1852 / 395) : ℂ) * ζ ^ 17 + ((48 / 395) : ℂ) * ζ ^ 18 + ((264 / 395) : ℂ) * ζ ^ 21 - ((3234 / 395) : ℂ) * ζ ^ 22 - ((2961 / 395) : ℂ) * ζ ^ 25 - ((264 / 395) : ℂ) * ζ ^ 27 - ((572 / 79) : ℂ) * ζ ^ 28 - ((1852 / 395) : ℂ) * ζ ^ 29 + ((1593 / 395) : ℂ) * ζ ^ 30 - ((2156 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep07CoefficientIdentity00 :
    row18_reducedY33_combinationStep07Coefficient00 =
      row18_reducedY33_combinationStep06Coefficient00 +
        row18_reducedY33_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep07Coefficient00 row18_reducedY33_combinationStep06Coefficient00 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep07Coefficient01 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep07CoefficientIdentity01 :
    row18_reducedY33_combinationStep07Coefficient01 =
      row18_reducedY33_combinationStep06Coefficient01 +
        row18_reducedY33_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep07Coefficient01 row18_reducedY33_combinationStep06Coefficient01 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep07Coefficient02 : ℂ :=
  (((944 / 395) : ℂ) - ((338 / 395) : ℂ) * ζ ^ 1 - ((2588 / 395) : ℂ) * ζ ^ 2 + ((284 / 79) : ℂ) * ζ ^ 3 - ((2944 / 395) : ℂ) * ζ ^ 5 - ((1302 / 395) : ℂ) * ζ ^ 6 - ((3342 / 395) : ℂ) * ζ ^ 8 - ((1134 / 395) : ℂ) * ζ ^ 9 - ((588 / 79) : ℂ) * ζ ^ 11 - ((1286 / 395) : ℂ) * ζ ^ 12 + ((338 / 395) : ℂ) * ζ ^ 13 - ((284 / 79) : ℂ) * ζ ^ 15 + ((338 / 395) : ℂ) * ζ ^ 17 + ((1644 / 395) : ℂ) * ζ ^ 18 + ((2606 / 395) : ℂ) * ζ ^ 21 + ((2588 / 395) : ℂ) * ζ ^ 22 + ((2588 / 395) : ℂ) * ζ ^ 24 + ((2606 / 395) : ℂ) * ζ ^ 25 + ((588 / 79) : ℂ) * ζ ^ 27 + ((3342 / 395) : ℂ) * ζ ^ 28 - ((338 / 395) : ℂ) * ζ ^ 29 + ((754 / 395) : ℂ) * ζ ^ 30 + ((588 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep07CoefficientIdentity02 :
    row18_reducedY33_combinationStep07Coefficient02 =
      row18_reducedY33_combinationStep06Coefficient02 +
        row18_reducedY33_combinationStep07Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep07Coefficient02 row18_reducedY33_combinationStep06Coefficient02 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 (((4978 / 6241) : ℂ) + ((1363 / 6241) : ℂ) * ζ ^ 1 - ((2345 / 12482) : ℂ) * ζ ^ 2 + ((2043 / 12482) : ℂ) * ζ ^ 3 - ((2434 / 6241) : ℂ) * ζ ^ 4 + ((1310 / 6241) : ℂ) * ζ ^ 5 + ((10323 / 12482) : ℂ) * ζ ^ 6 + ((3050 / 6241) : ℂ) * ζ ^ 7 - ((2498 / 6241) : ℂ) * ζ ^ 8 - ((1739 / 12482) : ℂ) * ζ ^ 9 + ((5095 / 12482) : ℂ) * ζ ^ 10 - ((4917 / 12482) : ℂ) * ζ ^ 11 + ((4607 / 6241) : ℂ) * ζ ^ 12 - ((1753 / 6241) : ℂ) * ζ ^ 13 - ((2961 / 6241) : ℂ) * ζ ^ 14 + ((8021 / 12482) : ℂ) * ζ ^ 15 - ((347 / 6241) : ℂ) * ζ ^ 16 + ((1852 / 6241) : ℂ) * ζ ^ 17 + ((505 / 6241) : ℂ) * ζ ^ 18 - ((728 / 6241) : ℂ) * ζ ^ 19 + ((1667 / 6241) : ℂ) * ζ ^ 20 - ((6627 / 12482) : ℂ) * ζ ^ 21 - ((4319 / 12482) : ℂ) * ζ ^ 22 + ((92 / 6241) : ℂ) * ζ ^ 23 + ((4045 / 12482) : ℂ) * ζ ^ 24 + ((7860 / 6241) : ℂ) * ζ ^ 25 + ((13 / 6241) : ℂ) * ζ ^ 26 - ((3509 / 6241) : ℂ) * ζ ^ 27 - ((573 / 6241) : ℂ) * ζ ^ 28 + ((888 / 6241) : ℂ) * ζ ^ 29 - ((90 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep07Coefficient03 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep07CoefficientIdentity03 :
    row18_reducedY33_combinationStep07Coefficient03 =
      row18_reducedY33_combinationStep06Coefficient03 +
        row18_reducedY33_combinationStep07Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep07Coefficient03 row18_reducedY33_combinationStep06Coefficient03 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 (-((4466 / 6241) : ℂ) - ((3988 / 6241) : ℂ) * ζ ^ 1 - ((6751 / 12482) : ℂ) * ζ ^ 2 - ((1189 / 12482) : ℂ) * ζ ^ 3 + ((4723 / 6241) : ℂ) * ζ ^ 4 + ((1569 / 12482) : ℂ) * ζ ^ 5 - ((125 / 6241) : ℂ) * ζ ^ 6 - ((1633 / 6241) : ℂ) * ζ ^ 7 - ((4183 / 6241) : ℂ) * ζ ^ 8 + ((5487 / 6241) : ℂ) * ζ ^ 9 + ((1469 / 6241) : ℂ) * ζ ^ 10 + ((2829 / 6241) : ℂ) * ζ ^ 11 + ((1961 / 12482) : ℂ) * ζ ^ 12 - ((293 / 6241) : ℂ) * ζ ^ 13 + ((139 / 6241) : ℂ) * ζ ^ 14 + ((2645 / 12482) : ℂ) * ζ ^ 15 - ((191 / 6241) : ℂ) * ζ ^ 16 + ((3653 / 6241) : ℂ) * ζ ^ 17 + ((2886 / 6241) : ℂ) * ζ ^ 18 + ((3632 / 6241) : ℂ) * ζ ^ 19 - ((3885 / 6241) : ℂ) * ζ ^ 20 - ((2547 / 6241) : ℂ) * ζ ^ 21 + ((2357 / 12482) : ℂ) * ζ ^ 22 + ((3984 / 6241) : ℂ) * ζ ^ 23 + ((697 / 6241) : ℂ) * ζ ^ 24 - ((627 / 6241) : ℂ) * ζ ^ 25 - ((2849 / 6241) : ℂ) * ζ ^ 26 - ((718 / 6241) : ℂ) * ζ ^ 27 + ((916 / 6241) : ℂ) * ζ ^ 28 + ((8 / 79) : ℂ) * ζ ^ 29 - ((84 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep07Coefficient04 : ℂ :=
  (-((77 / 79) : ℂ) + ((1852 / 395) : ℂ) * ζ ^ 1 - ((3234 / 395) : ℂ) * ζ ^ 2 - ((1588 / 395) : ℂ) * ζ ^ 3 - ((1109 / 395) : ℂ) * ζ ^ 5 - ((3186 / 395) : ℂ) * ζ ^ 6 - ((572 / 79) : ℂ) * ζ ^ 8 - ((3744 / 395) : ℂ) * ζ ^ 9 - ((2156 / 395) : ℂ) * ζ ^ 11 - ((572 / 79) : ℂ) * ζ ^ 12 - ((1852 / 395) : ℂ) * ζ ^ 13 - ((1373 / 395) : ℂ) * ζ ^ 15 - ((1852 / 395) : ℂ) * ζ ^ 17 - ((48 / 395) : ℂ) * ζ ^ 18 - ((264 / 395) : ℂ) * ζ ^ 21 + ((3234 / 395) : ℂ) * ζ ^ 22 + ((2961 / 395) : ℂ) * ζ ^ 25 + ((264 / 395) : ℂ) * ζ ^ 27 + ((572 / 79) : ℂ) * ζ ^ 28 + ((1852 / 395) : ℂ) * ζ ^ 29 - ((1593 / 395) : ℂ) * ζ ^ 30 + ((2156 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep07CoefficientIdentity04 :
    row18_reducedY33_combinationStep07Coefficient04 =
      row18_reducedY33_combinationStep06Coefficient04 +
        row18_reducedY33_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep07Coefficient04 row18_reducedY33_combinationStep06Coefficient04 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep07Coefficient05 : ℂ :=
  (-((26 / 79) : ℂ) + ((193 / 79) : ℂ) * ζ ^ 1 - ((483 / 79) : ℂ) * ζ ^ 2 - ((555 / 79) : ℂ) * ζ ^ 5 - ((457 / 79) : ℂ) * ζ ^ 6 - ((457 / 79) : ℂ) * ζ ^ 8 - ((555 / 79) : ℂ) * ζ ^ 9 - ((677 / 79) : ℂ) * ζ ^ 11 - ((340 / 79) : ℂ) * ζ ^ 12 - ((193 / 79) : ℂ) * ζ ^ 13 - ((357 / 79) : ℂ) * ζ ^ 15 - ((193 / 79) : ℂ) * ζ ^ 17 + ((186 / 79) : ℂ) * ζ ^ 18 + ((181 / 79) : ℂ) * ζ ^ 21 + ((483 / 79) : ℂ) * ζ ^ 22 + ((271 / 79) : ℂ) * ζ ^ 24 + ((748 / 79) : ℂ) * ζ ^ 25 + ((357 / 79) : ℂ) * ζ ^ 27 + ((457 / 79) : ℂ) * ζ ^ 28 + ((193 / 79) : ℂ) * ζ ^ 29 - ((117 / 79) : ℂ) * ζ ^ 30 + ((677 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY33_combinationStep07CoefficientIdentity05 :
    row18_reducedY33_combinationStep07Coefficient05 =
      row18_reducedY33_combinationStep06Coefficient05 +
        row18_reducedY33_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep07Coefficient05 row18_reducedY33_combinationStep06Coefficient05 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep07Coefficient06 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep07CoefficientIdentity06 :
    row18_reducedY33_combinationStep07Coefficient06 =
      row18_reducedY33_combinationStep06Coefficient06 +
        row18_reducedY33_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep07Coefficient06 row18_reducedY33_combinationStep06Coefficient06 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep07Coefficient07 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY33_combinationStep07CoefficientIdentity07 :
    row18_reducedY33_combinationStep07Coefficient07 =
      row18_reducedY33_combinationStep06Coefficient07 +
        row18_reducedY33_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep07Coefficient07 row18_reducedY33_combinationStep06Coefficient07 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep07Coefficient08 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep07CoefficientIdentity08 :
    row18_reducedY33_combinationStep07Coefficient08 =
      row18_reducedY33_combinationStep06Coefficient08 +
        row18_reducedY33_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep07Coefficient08 row18_reducedY33_combinationStep06Coefficient08 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep07Coefficient09 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep07CoefficientIdentity09 :
    row18_reducedY33_combinationStep07Coefficient09 =
      row18_reducedY33_combinationStep06Coefficient09 +
        row18_reducedY33_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep07Coefficient09 row18_reducedY33_combinationStep06Coefficient09 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep07Coefficient10 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep07CoefficientIdentity10 :
    row18_reducedY33_combinationStep07Coefficient10 =
      row18_reducedY33_combinationStep06Coefficient10 +
        row18_reducedY33_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep07Coefficient10 row18_reducedY33_combinationStep06Coefficient10 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep07Coefficient11 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep07CoefficientIdentity11 :
    row18_reducedY33_combinationStep07Coefficient11 =
      row18_reducedY33_combinationStep06Coefficient11 +
        row18_reducedY33_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep07Coefficient11 row18_reducedY33_combinationStep06Coefficient11 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep07Coefficient12 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep07CoefficientIdentity12 :
    row18_reducedY33_combinationStep07Coefficient12 =
      row18_reducedY33_combinationStep06Coefficient12 +
        row18_reducedY33_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep07Coefficient12 row18_reducedY33_combinationStep06Coefficient12 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep07Coefficient13 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep07CoefficientIdentity13 :
    row18_reducedY33_combinationStep07Coefficient13 =
      row18_reducedY33_combinationStep06Coefficient13 +
        row18_reducedY33_combinationStep07Multiplier *
          (((5 / 316) : ℂ) - ((3 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((33 / 158) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 + ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 + ((3 / 316) : ℂ) * ζ ^ 9 + ((33 / 316) : ℂ) * ζ ^ 11 + ((3 / 79) : ℂ) * ζ ^ 12 + ((3 / 316) : ℂ) * ζ ^ 13 + ((35 / 158) : ℂ) * ζ ^ 15 + ((3 / 316) : ℂ) * ζ ^ 17 + ((19 / 316) : ℂ) * ζ ^ 18 + ((45 / 158) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((1 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 - ((3 / 316) : ℂ) * ζ ^ 29 + ((13 / 79) : ℂ) * ζ ^ 30 - ((33 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep07Coefficient13 row18_reducedY33_combinationStep06Coefficient13 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 (((3058 / 6241) : ℂ) + ((392 / 6241) : ℂ) * ζ ^ 1 - ((2841 / 12482) : ℂ) * ζ ^ 2 - ((103 / 6241) : ℂ) * ζ ^ 3 + ((3836 / 6241) : ℂ) * ζ ^ 4 - ((4895 / 12482) : ℂ) * ζ ^ 5 - ((2491 / 12482) : ℂ) * ζ ^ 6 - ((12839 / 12482) : ℂ) * ζ ^ 7 + ((2017 / 12482) : ℂ) * ζ ^ 8 + ((10211 / 12482) : ℂ) * ζ ^ 9 + ((2538 / 6241) : ℂ) * ζ ^ 10 - ((1486 / 6241) : ℂ) * ζ ^ 11 - ((24711 / 12482) : ℂ) * ζ ^ 12 - ((6425 / 12482) : ℂ) * ζ ^ 13 - ((1453 / 6241) : ℂ) * ζ ^ 14 + ((5079 / 12482) : ℂ) * ζ ^ 15 + ((2641 / 12482) : ℂ) * ζ ^ 16 - ((707 / 12482) : ℂ) * ζ ^ 17 - ((12423 / 12482) : ℂ) * ζ ^ 18 - ((1465 / 6241) : ℂ) * ζ ^ 19 - ((10497 / 12482) : ℂ) * ζ ^ 20 - ((3557 / 6241) : ℂ) * ζ ^ 21 - ((2515 / 12482) : ℂ) * ζ ^ 22 + ((7701 / 6241) : ℂ) * ζ ^ 23 - ((6705 / 12482) : ℂ) * ζ ^ 24 - ((2191 / 6241) : ℂ) * ζ ^ 25 - ((6207 / 6241) : ℂ) * ζ ^ 26 - ((2633 / 6241) : ℂ) * ζ ^ 27 + ((1037 / 6241) : ℂ) * ζ ^ 28 + ((1632 / 6241) : ℂ) * ζ ^ 29 - ((198 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep07Coefficient14 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep07CoefficientIdentity14 :
    row18_reducedY33_combinationStep07Coefficient14 =
      row18_reducedY33_combinationStep06Coefficient14 +
        row18_reducedY33_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep07Coefficient14 row18_reducedY33_combinationStep06Coefficient14 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep07Coefficient15 : ℂ :=
  (-(1 : ℂ))

private theorem row18_reducedY33_combinationStep07CoefficientIdentity15 :
    row18_reducedY33_combinationStep07Coefficient15 =
      row18_reducedY33_combinationStep06Coefficient15 +
        row18_reducedY33_combinationStep07Multiplier *
          (-((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((35 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep07Coefficient15 row18_reducedY33_combinationStep06Coefficient15 row18_reducedY33_combinationStep07Multiplier
  close_cyclotomic_row18 (((4466 / 6241) : ℂ) + ((3988 / 6241) : ℂ) * ζ ^ 1 + ((6751 / 12482) : ℂ) * ζ ^ 2 + ((1189 / 12482) : ℂ) * ζ ^ 3 - ((4723 / 6241) : ℂ) * ζ ^ 4 - ((1569 / 12482) : ℂ) * ζ ^ 5 + ((125 / 6241) : ℂ) * ζ ^ 6 + ((1633 / 6241) : ℂ) * ζ ^ 7 + ((4183 / 6241) : ℂ) * ζ ^ 8 - ((5487 / 6241) : ℂ) * ζ ^ 9 - ((1469 / 6241) : ℂ) * ζ ^ 10 - ((2829 / 6241) : ℂ) * ζ ^ 11 - ((1961 / 12482) : ℂ) * ζ ^ 12 + ((293 / 6241) : ℂ) * ζ ^ 13 - ((139 / 6241) : ℂ) * ζ ^ 14 - ((2645 / 12482) : ℂ) * ζ ^ 15 + ((191 / 6241) : ℂ) * ζ ^ 16 - ((3653 / 6241) : ℂ) * ζ ^ 17 - ((2886 / 6241) : ℂ) * ζ ^ 18 - ((3632 / 6241) : ℂ) * ζ ^ 19 + ((3885 / 6241) : ℂ) * ζ ^ 20 + ((2547 / 6241) : ℂ) * ζ ^ 21 - ((2357 / 12482) : ℂ) * ζ ^ 22 - ((3984 / 6241) : ℂ) * ζ ^ 23 - ((697 / 6241) : ℂ) * ζ ^ 24 + ((627 / 6241) : ℂ) * ζ ^ 25 + ((2849 / 6241) : ℂ) * ζ ^ 26 + ((718 / 6241) : ℂ) * ζ ^ 27 - ((916 / 6241) : ℂ) * ζ ^ 28 - ((8 / 79) : ℂ) * ζ ^ 29 + ((84 / 6241) : ℂ) * ζ ^ 30)

private theorem row18_reducedY33_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY33_combinationStep07Coefficient00) * Y 0 0
      + (row18_reducedY33_combinationStep07Coefficient01) * Y 0 1
      + (row18_reducedY33_combinationStep07Coefficient02) * Y 1 0
      + (row18_reducedY33_combinationStep07Coefficient03) * Y 1 1
      + (row18_reducedY33_combinationStep07Coefficient04) * Y 2 2
      + (row18_reducedY33_combinationStep07Coefficient05) * Y 2 3
      + (row18_reducedY33_combinationStep07Coefficient06) * Y 3 2
      + (row18_reducedY33_combinationStep07Coefficient07) * Y 3 3
      + (row18_reducedY33_combinationStep07Coefficient08) * Y 4 4
      + (row18_reducedY33_combinationStep07Coefficient09) * Y 4 5
      + (row18_reducedY33_combinationStep07Coefficient10) * Y 5 4
      + (row18_reducedY33_combinationStep07Coefficient11) * Y 5 5
      + (row18_reducedY33_combinationStep07Coefficient12) * Y 6 6
      + (row18_reducedY33_combinationStep07Coefficient13) * Y 6 7
      + (row18_reducedY33_combinationStep07Coefficient14) * Y 7 6
      + (row18_reducedY33_combinationStep07Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY33_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation17
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY33_combinationStep07CoefficientIdentity00,
      row18_reducedY33_combinationStep07CoefficientIdentity01,
      row18_reducedY33_combinationStep07CoefficientIdentity02,
      row18_reducedY33_combinationStep07CoefficientIdentity03,
      row18_reducedY33_combinationStep07CoefficientIdentity04,
      row18_reducedY33_combinationStep07CoefficientIdentity05,
      row18_reducedY33_combinationStep07CoefficientIdentity06,
      row18_reducedY33_combinationStep07CoefficientIdentity07,
      row18_reducedY33_combinationStep07CoefficientIdentity08,
      row18_reducedY33_combinationStep07CoefficientIdentity09,
      row18_reducedY33_combinationStep07CoefficientIdentity10,
      row18_reducedY33_combinationStep07CoefficientIdentity11,
      row18_reducedY33_combinationStep07CoefficientIdentity12,
      row18_reducedY33_combinationStep07CoefficientIdentity13,
      row18_reducedY33_combinationStep07CoefficientIdentity14,
      row18_reducedY33_combinationStep07CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY33_combinationStep07Multiplier * equation

private def row18_reducedY33_combinationStep08Multiplier : ℂ :=
  (((1060 / 79) : ℂ) - ((872 / 395) : ℂ) * ζ ^ 1 + ((5652 / 395) : ℂ) * ζ ^ 2 - ((532 / 395) : ℂ) * ζ ^ 3 + ((4264 / 395) : ℂ) * ζ ^ 5 + ((9288 / 395) : ℂ) * ζ ^ 6 + ((516 / 79) : ℂ) * ζ ^ 8 + ((5404 / 395) : ℂ) * ζ ^ 9 + ((5936 / 395) : ℂ) * ζ ^ 11 + ((516 / 79) : ℂ) * ζ ^ 12 + ((872 / 395) : ℂ) * ζ ^ 13 + ((5668 / 395) : ℂ) * ζ ^ 15 + ((872 / 395) : ℂ) * ζ ^ 17 - ((3636 / 395) : ℂ) * ζ ^ 18 + ((1404 / 395) : ℂ) * ζ ^ 21 - ((5652 / 395) : ℂ) * ζ ^ 22 - ((5136 / 395) : ℂ) * ζ ^ 25 - ((1404 / 395) : ℂ) * ζ ^ 27 - ((516 / 79) : ℂ) * ζ ^ 28 - ((872 / 395) : ℂ) * ζ ^ 29 + ((4644 / 395) : ℂ) * ζ ^ 30 - ((5936 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY33_combinationStep08Coefficient00 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep08CoefficientIdentity00 :
    row18_reducedY33_combinationStep08Coefficient00 =
      row18_reducedY33_combinationStep07Coefficient00 +
        row18_reducedY33_combinationStep08Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep08Coefficient00 row18_reducedY33_combinationStep07Coefficient00 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 (((9263 / 6241) : ℂ) - ((163499 / 31205) : ℂ) * ζ ^ 1 + ((32443 / 6241) : ℂ) * ζ ^ 2 + ((125518 / 31205) : ℂ) * ζ ^ 3 - ((164739 / 31205) : ℂ) * ζ ^ 4 + ((234044 / 31205) : ℂ) * ζ ^ 5 + ((13978 / 6241) : ℂ) * ζ ^ 6 - ((277084 / 31205) : ℂ) * ζ ^ 7 + ((112382 / 31205) : ℂ) * ζ ^ 8 + ((97638 / 31205) : ℂ) * ζ ^ 9 - ((44769 / 6241) : ℂ) * ζ ^ 10 + ((287538 / 31205) : ℂ) * ζ ^ 11 + ((24478 / 31205) : ℂ) * ζ ^ 12 - ((260121 / 31205) : ℂ) * ζ ^ 13 + ((145056 / 31205) : ℂ) * ζ ^ 14 - ((72422 / 31205) : ℂ) * ζ ^ 15 - ((208417 / 31205) : ℂ) * ζ ^ 16 + ((237746 / 31205) : ℂ) * ζ ^ 17 - ((73272 / 31205) : ℂ) * ζ ^ 18 - ((84922 / 31205) : ℂ) * ζ ^ 19 + ((134428 / 31205) : ℂ) * ζ ^ 20 - ((147212 / 31205) : ℂ) * ζ ^ 21 - ((8221 / 6241) : ℂ) * ζ ^ 22 + ((90251 / 31205) : ℂ) * ζ ^ 23 - ((27118 / 31205) : ℂ) * ζ ^ 24 - ((16341 / 31205) : ℂ) * ζ ^ 25 + ((55299 / 31205) : ℂ) * ζ ^ 26 - ((52193 / 31205) : ℂ) * ζ ^ 27 + ((160 / 6241) : ℂ) * ζ ^ 28 + ((1498 / 6241) : ℂ) * ζ ^ 29 + ((20776 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep08Coefficient01 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep08CoefficientIdentity01 :
    row18_reducedY33_combinationStep08Coefficient01 =
      row18_reducedY33_combinationStep07Coefficient01 +
        row18_reducedY33_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep08Coefficient01 row18_reducedY33_combinationStep07Coefficient01 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep08Coefficient02 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep08CoefficientIdentity02 :
    row18_reducedY33_combinationStep08Coefficient02 =
      row18_reducedY33_combinationStep07Coefficient02 +
        row18_reducedY33_combinationStep08Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep08Coefficient02 row18_reducedY33_combinationStep07Coefficient02 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 (((24226 / 31205) : ℂ) - ((70093 / 31205) : ℂ) * ζ ^ 1 - ((235069 / 31205) : ℂ) * ζ ^ 2 - ((68796 / 31205) : ℂ) * ζ ^ 3 + ((3530 / 6241) : ℂ) * ζ ^ 4 - ((81023 / 6241) : ℂ) * ζ ^ 5 + ((70816 / 31205) : ℂ) * ζ ^ 6 - ((85272 / 31205) : ℂ) * ζ ^ 7 - ((251437 / 31205) : ℂ) * ζ ^ 8 + ((16293 / 31205) : ℂ) * ζ ^ 9 - ((87481 / 31205) : ℂ) * ζ ^ 10 - ((201648 / 31205) : ℂ) * ζ ^ 11 - ((11198 / 31205) : ℂ) * ζ ^ 12 + ((130516 / 31205) : ℂ) * ζ ^ 13 - ((235046 / 31205) : ℂ) * ζ ^ 14 + ((174114 / 31205) : ℂ) * ζ ^ 15 + ((6699 / 31205) : ℂ) * ζ ^ 16 - ((103573 / 31205) : ℂ) * ζ ^ 17 + ((123531 / 31205) : ℂ) * ζ ^ 18 - ((1406 / 31205) : ℂ) * ζ ^ 19 - ((20091 / 31205) : ℂ) * ζ ^ 20 + ((223732 / 31205) : ℂ) * ζ ^ 21 + ((12876 / 6241) : ℂ) * ζ ^ 22 + ((56373 / 31205) : ℂ) * ζ ^ 23 + ((1824 / 395) : ℂ) * ζ ^ 24 - ((16367 / 31205) : ℂ) * ζ ^ 25 + ((447 / 31205) : ℂ) * ζ ^ 26 + ((106921 / 31205) : ℂ) * ζ ^ 27 + ((4092 / 6241) : ℂ) * ζ ^ 28 - ((26292 / 31205) : ℂ) * ζ ^ 29 + ((124656 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep08Coefficient03 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep08CoefficientIdentity03 :
    row18_reducedY33_combinationStep08Coefficient03 =
      row18_reducedY33_combinationStep07Coefficient03 +
        row18_reducedY33_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep08Coefficient03 row18_reducedY33_combinationStep07Coefficient03 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep08Coefficient04 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep08CoefficientIdentity04 :
    row18_reducedY33_combinationStep08Coefficient04 =
      row18_reducedY33_combinationStep07Coefficient04 +
        row18_reducedY33_combinationStep08Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep08Coefficient04 row18_reducedY33_combinationStep07Coefficient04 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 (-((9263 / 6241) : ℂ) + ((163499 / 31205) : ℂ) * ζ ^ 1 - ((32443 / 6241) : ℂ) * ζ ^ 2 - ((125518 / 31205) : ℂ) * ζ ^ 3 + ((164739 / 31205) : ℂ) * ζ ^ 4 - ((234044 / 31205) : ℂ) * ζ ^ 5 - ((13978 / 6241) : ℂ) * ζ ^ 6 + ((277084 / 31205) : ℂ) * ζ ^ 7 - ((112382 / 31205) : ℂ) * ζ ^ 8 - ((97638 / 31205) : ℂ) * ζ ^ 9 + ((44769 / 6241) : ℂ) * ζ ^ 10 - ((287538 / 31205) : ℂ) * ζ ^ 11 - ((24478 / 31205) : ℂ) * ζ ^ 12 + ((260121 / 31205) : ℂ) * ζ ^ 13 - ((145056 / 31205) : ℂ) * ζ ^ 14 + ((72422 / 31205) : ℂ) * ζ ^ 15 + ((208417 / 31205) : ℂ) * ζ ^ 16 - ((237746 / 31205) : ℂ) * ζ ^ 17 + ((73272 / 31205) : ℂ) * ζ ^ 18 + ((84922 / 31205) : ℂ) * ζ ^ 19 - ((134428 / 31205) : ℂ) * ζ ^ 20 + ((147212 / 31205) : ℂ) * ζ ^ 21 + ((8221 / 6241) : ℂ) * ζ ^ 22 - ((90251 / 31205) : ℂ) * ζ ^ 23 + ((27118 / 31205) : ℂ) * ζ ^ 24 + ((16341 / 31205) : ℂ) * ζ ^ 25 - ((55299 / 31205) : ℂ) * ζ ^ 26 + ((52193 / 31205) : ℂ) * ζ ^ 27 - ((160 / 6241) : ℂ) * ζ ^ 28 - ((1498 / 6241) : ℂ) * ζ ^ 29 - ((20776 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep08Coefficient05 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep08CoefficientIdentity05 :
    row18_reducedY33_combinationStep08Coefficient05 =
      row18_reducedY33_combinationStep07Coefficient05 +
        row18_reducedY33_combinationStep08Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY33_combinationStep08Coefficient05 row18_reducedY33_combinationStep07Coefficient05 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 (((16231 / 6241) : ℂ) + ((37343 / 31205) : ℂ) * ζ ^ 1 - ((101289 / 31205) : ℂ) * ζ ^ 2 - ((32649 / 31205) : ℂ) * ζ ^ 3 - ((91478 / 31205) : ℂ) * ζ ^ 4 - ((192417 / 31205) : ℂ) * ζ ^ 5 - ((39802 / 31205) : ℂ) * ζ ^ 6 - ((13041 / 31205) : ℂ) * ζ ^ 7 - ((55586 / 6241) : ℂ) * ζ ^ 8 + ((71579 / 31205) : ℂ) * ζ ^ 9 - ((107319 / 31205) : ℂ) * ζ ^ 10 - ((28291 / 31205) : ℂ) * ζ ^ 11 - ((8514 / 31205) : ℂ) * ζ ^ 12 + ((74719 / 31205) : ℂ) * ζ ^ 13 - ((4003 / 395) : ℂ) * ζ ^ 14 - ((6453 / 6241) : ℂ) * ζ ^ 15 + ((81459 / 31205) : ℂ) * ζ ^ 16 + ((1142 / 31205) : ℂ) * ζ ^ 17 + ((2603 / 6241) : ℂ) * ζ ^ 18 + ((60487 / 31205) : ℂ) * ζ ^ 19 - ((177066 / 31205) : ℂ) * ζ ^ 20 + ((77621 / 31205) : ℂ) * ζ ^ 21 + ((141774 / 31205) : ℂ) * ζ ^ 22 - ((16529 / 6241) : ℂ) * ζ ^ 23 + ((43448 / 6241) : ℂ) * ζ ^ 24 + ((43719 / 31205) : ℂ) * ζ ^ 25 + ((51512 / 31205) : ℂ) * ζ ^ 26 - ((8778 / 31205) : ℂ) * ζ ^ 27 + ((3258 / 31205) : ℂ) * ζ ^ 28 - ((128844 / 31205) : ℂ) * ζ ^ 29 + ((53424 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY33_combinationStep08Coefficient06 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep08CoefficientIdentity06 :
    row18_reducedY33_combinationStep08Coefficient06 =
      row18_reducedY33_combinationStep07Coefficient06 +
        row18_reducedY33_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep08Coefficient06 row18_reducedY33_combinationStep07Coefficient06 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep08Coefficient07 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY33_combinationStep08CoefficientIdentity07 :
    row18_reducedY33_combinationStep08Coefficient07 =
      row18_reducedY33_combinationStep07Coefficient07 +
        row18_reducedY33_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep08Coefficient07 row18_reducedY33_combinationStep07Coefficient07 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep08Coefficient08 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep08CoefficientIdentity08 :
    row18_reducedY33_combinationStep08Coefficient08 =
      row18_reducedY33_combinationStep07Coefficient08 +
        row18_reducedY33_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep08Coefficient08 row18_reducedY33_combinationStep07Coefficient08 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep08Coefficient09 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep08CoefficientIdentity09 :
    row18_reducedY33_combinationStep08Coefficient09 =
      row18_reducedY33_combinationStep07Coefficient09 +
        row18_reducedY33_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep08Coefficient09 row18_reducedY33_combinationStep07Coefficient09 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep08Coefficient10 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep08CoefficientIdentity10 :
    row18_reducedY33_combinationStep08Coefficient10 =
      row18_reducedY33_combinationStep07Coefficient10 +
        row18_reducedY33_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep08Coefficient10 row18_reducedY33_combinationStep07Coefficient10 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep08Coefficient11 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep08CoefficientIdentity11 :
    row18_reducedY33_combinationStep08Coefficient11 =
      row18_reducedY33_combinationStep07Coefficient11 +
        row18_reducedY33_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep08Coefficient11 row18_reducedY33_combinationStep07Coefficient11 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep08Coefficient12 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep08CoefficientIdentity12 :
    row18_reducedY33_combinationStep08Coefficient12 =
      row18_reducedY33_combinationStep07Coefficient12 +
        row18_reducedY33_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep08Coefficient12 row18_reducedY33_combinationStep07Coefficient12 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep08Coefficient13 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep08CoefficientIdentity13 :
    row18_reducedY33_combinationStep08Coefficient13 =
      row18_reducedY33_combinationStep07Coefficient13 +
        row18_reducedY33_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep08Coefficient13 row18_reducedY33_combinationStep07Coefficient13 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep08Coefficient14 : ℂ :=
  0

private theorem row18_reducedY33_combinationStep08CoefficientIdentity14 :
    row18_reducedY33_combinationStep08Coefficient14 =
      row18_reducedY33_combinationStep07Coefficient14 +
        row18_reducedY33_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep08Coefficient14 row18_reducedY33_combinationStep07Coefficient14 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY33_combinationStep08Coefficient15 : ℂ :=
  (-(1 : ℂ))

private theorem row18_reducedY33_combinationStep08CoefficientIdentity15 :
    row18_reducedY33_combinationStep08Coefficient15 =
      row18_reducedY33_combinationStep07Coefficient15 +
        row18_reducedY33_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY33_combinationStep08Coefficient15 row18_reducedY33_combinationStep07Coefficient15 row18_reducedY33_combinationStep08Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY33_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY33_combinationStep08Coefficient00) * Y 0 0
      + (row18_reducedY33_combinationStep08Coefficient01) * Y 0 1
      + (row18_reducedY33_combinationStep08Coefficient02) * Y 1 0
      + (row18_reducedY33_combinationStep08Coefficient03) * Y 1 1
      + (row18_reducedY33_combinationStep08Coefficient04) * Y 2 2
      + (row18_reducedY33_combinationStep08Coefficient05) * Y 2 3
      + (row18_reducedY33_combinationStep08Coefficient06) * Y 3 2
      + (row18_reducedY33_combinationStep08Coefficient07) * Y 3 3
      + (row18_reducedY33_combinationStep08Coefficient08) * Y 4 4
      + (row18_reducedY33_combinationStep08Coefficient09) * Y 4 5
      + (row18_reducedY33_combinationStep08Coefficient10) * Y 5 4
      + (row18_reducedY33_combinationStep08Coefficient11) * Y 5 5
      + (row18_reducedY33_combinationStep08Coefficient12) * Y 6 6
      + (row18_reducedY33_combinationStep08Coefficient13) * Y 6 7
      + (row18_reducedY33_combinationStep08Coefficient14) * Y 7 6
      + (row18_reducedY33_combinationStep08Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY33_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY33_combinationStep08CoefficientIdentity00,
      row18_reducedY33_combinationStep08CoefficientIdentity01,
      row18_reducedY33_combinationStep08CoefficientIdentity02,
      row18_reducedY33_combinationStep08CoefficientIdentity03,
      row18_reducedY33_combinationStep08CoefficientIdentity04,
      row18_reducedY33_combinationStep08CoefficientIdentity05,
      row18_reducedY33_combinationStep08CoefficientIdentity06,
      row18_reducedY33_combinationStep08CoefficientIdentity07,
      row18_reducedY33_combinationStep08CoefficientIdentity08,
      row18_reducedY33_combinationStep08CoefficientIdentity09,
      row18_reducedY33_combinationStep08CoefficientIdentity10,
      row18_reducedY33_combinationStep08CoefficientIdentity11,
      row18_reducedY33_combinationStep08CoefficientIdentity12,
      row18_reducedY33_combinationStep08CoefficientIdentity13,
      row18_reducedY33_combinationStep08CoefficientIdentity14,
      row18_reducedY33_combinationStep08CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY33_combinationStep08Multiplier * equation

theorem row18_reducedY33
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 3 3 = Y 7 7 := by
  have reduced :=
    row18_reducedY33_combinationStep08 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY33_combinationStep08Coefficient00,
      row18_reducedY33_combinationStep08Coefficient01,
      row18_reducedY33_combinationStep08Coefficient02,
      row18_reducedY33_combinationStep08Coefficient03,
      row18_reducedY33_combinationStep08Coefficient04,
      row18_reducedY33_combinationStep08Coefficient05,
      row18_reducedY33_combinationStep08Coefficient06,
      row18_reducedY33_combinationStep08Coefficient07,
      row18_reducedY33_combinationStep08Coefficient08,
      row18_reducedY33_combinationStep08Coefficient09,
      row18_reducedY33_combinationStep08Coefficient10,
      row18_reducedY33_combinationStep08Coefficient11,
      row18_reducedY33_combinationStep08Coefficient12,
      row18_reducedY33_combinationStep08Coefficient13,
      row18_reducedY33_combinationStep08Coefficient14,
      row18_reducedY33_combinationStep08Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
