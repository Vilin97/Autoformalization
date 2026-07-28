/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction05

/-!
# Ambient row 18 commutant reduction 06

This generated module checks the reduced relation `reducedY32` for
matrix coordinate (3, 2).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY32_combinationStep00Multiplier : ℂ :=
  (((92986 / 1185) : ℂ) - ((17920 / 237) : ℂ) * ζ ^ 1 - ((26128 / 1185) : ℂ) * ζ ^ 2 + ((6152 / 79) : ℂ) * ζ ^ 3 - ((17920 / 237) : ℂ) * ζ ^ 5 + ((22286 / 395) : ℂ) * ζ ^ 6 - ((22286 / 395) : ℂ) * ζ ^ 8 + ((17920 / 237) : ℂ) * ζ ^ 9 - ((3076 / 79) : ℂ) * ζ ^ 11 + ((9266 / 1185) : ℂ) * ζ ^ 12 + ((17920 / 237) : ℂ) * ζ ^ 13 + ((1672 / 79) : ℂ) * ζ ^ 15 + ((17920 / 237) : ℂ) * ζ ^ 17 + ((22898 / 395) : ℂ) * ζ ^ 18 + ((29314 / 237) : ℂ) * ζ ^ 21 + ((26128 / 1185) : ℂ) * ζ ^ 22 + ((45184 / 395) : ℂ) * ζ ^ 24 + ((7824 / 79) : ℂ) * ζ ^ 27 + ((22286 / 395) : ℂ) * ζ ^ 28 - ((17920 / 237) : ℂ) * ζ ^ 29 + ((76124 / 1185) : ℂ) * ζ ^ 30 + ((3076 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY32_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep00CoefficientIdentity00 :
    row18_reducedY32_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep00Coefficient00 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep00Coefficient01 : ℂ :=
  (((4 / 237) : ℂ) + ((1589 / 474) : ℂ) * ζ ^ 1 - ((1675 / 474) : ℂ) * ζ ^ 2 - ((98 / 79) : ℂ) * ζ ^ 3 + ((50 / 79) : ℂ) * ζ ^ 5 - ((1591 / 237) : ℂ) * ζ ^ 6 - ((1394 / 237) : ℂ) * ζ ^ 9 - ((50 / 79) : ℂ) * ζ ^ 11 - ((423 / 158) : ℂ) * ζ ^ 12 - ((1589 / 474) : ℂ) * ζ ^ 13 - ((1499 / 474) : ℂ) * ζ ^ 15 - ((1589 / 474) : ℂ) * ζ ^ 17 + ((28 / 79) : ℂ) * ζ ^ 18 - ((148 / 79) : ℂ) * ζ ^ 21 + ((1675 / 474) : ℂ) * ζ ^ 22 + ((4 / 237) : ℂ) * ζ ^ 24 + ((1289 / 474) : ℂ) * ζ ^ 25 - ((1289 / 474) : ℂ) * ζ ^ 27 + ((1589 / 474) : ℂ) * ζ ^ 29 - ((1675 / 237) : ℂ) * ζ ^ 30 + ((50 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep00CoefficientIdentity01 :
    row18_reducedY32_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep00Coefficient01 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 (((1951126 / 93615) : ℂ) - ((1986209 / 93615) : ℂ) * ζ ^ 1 + ((402247 / 62410) : ℂ) * ζ ^ 2 + ((1009622 / 93615) : ℂ) * ζ ^ 3 - ((676968 / 31205) : ℂ) * ζ ^ 4 - ((1366097 / 187230) : ℂ) * ζ ^ 5 + ((791053 / 37446) : ℂ) * ζ ^ 6 - ((917783 / 187230) : ℂ) * ζ ^ 7 - ((345502 / 31205) : ℂ) * ζ ^ 8 + ((2389121 / 187230) : ℂ) * ζ ^ 9 + ((739873 / 62410) : ℂ) * ζ ^ 10 + ((441692 / 31205) : ℂ) * ζ ^ 11 - ((430103 / 18723) : ℂ) * ζ ^ 12 + ((3049919 / 187230) : ℂ) * ζ ^ 13 + ((2005091 / 93615) : ℂ) * ζ ^ 14 - ((376877 / 93615) : ℂ) * ζ ^ 15 + ((227642 / 93615) : ℂ) * ζ ^ 16 + ((284692 / 31205) : ℂ) * ζ ^ 17 - ((8491 / 1185) : ℂ) * ζ ^ 18 + ((1661081 / 187230) : ℂ) * ζ ^ 19 + ((76143 / 12482) : ℂ) * ζ ^ 20 - ((98149 / 62410) : ℂ) * ζ ^ 21 - ((1994333 / 187230) : ℂ) * ζ ^ 22 + ((65786 / 6241) : ℂ) * ζ ^ 23 + ((1463128 / 93615) : ℂ) * ζ ^ 24 - ((55611 / 12482) : ℂ) * ζ ^ 25 - ((2152937 / 187230) : ℂ) * ζ ^ 26 - ((369569 / 31205) : ℂ) * ζ ^ 27 + ((2140852 / 93615) : ℂ) * ζ ^ 28 - ((982663 / 93615) : ℂ) * ζ ^ 29 - ((52292 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep00Coefficient02 : ℂ :=
  (-((545 / 237) : ℂ) + ((307 / 79) : ℂ) * ζ ^ 1 + ((761 / 237) : ℂ) * ζ ^ 2 - ((1153 / 474) : ℂ) * ζ ^ 3 + ((2753 / 474) : ℂ) * ζ ^ 5 + ((867 / 158) : ℂ) * ζ ^ 8 - ((183 / 79) : ℂ) * ζ ^ 9 + ((2251 / 474) : ℂ) * ζ ^ 11 - ((421 / 474) : ℂ) * ζ ^ 12 - ((307 / 79) : ℂ) * ζ ^ 13 + ((121 / 237) : ℂ) * ζ ^ 15 - ((307 / 79) : ℂ) * ζ ^ 17 - ((761 / 237) : ℂ) * ζ ^ 18 - ((2995 / 474) : ℂ) * ζ ^ 21 - ((761 / 237) : ℂ) * ζ ^ 22 - ((1090 / 237) : ℂ) * ζ ^ 24 - ((911 / 474) : ℂ) * ζ ^ 25 - ((2995 / 474) : ℂ) * ζ ^ 27 - ((867 / 158) : ℂ) * ζ ^ 28 + ((307 / 79) : ℂ) * ζ ^ 29 - ((2189 / 474) : ℂ) * ζ ^ 30 - ((2251 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep00CoefficientIdentity02 :
    row18_reducedY32_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep00Coefficient02 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 (((2121488 / 93615) : ℂ) - ((3796781 / 187230) : ℂ) * ζ ^ 1 - ((112346 / 31205) : ℂ) * ζ ^ 2 + ((1430051 / 187230) : ℂ) * ζ ^ 3 - ((502022 / 31205) : ℂ) * ζ ^ 4 + ((153007 / 31205) : ℂ) * ζ ^ 5 + ((745639 / 62410) : ℂ) * ζ ^ 6 - ((1505737 / 93615) : ℂ) * ζ ^ 7 - ((254072 / 31205) : ℂ) * ζ ^ 8 + ((1752253 / 187230) : ℂ) * ζ ^ 9 + ((1321001 / 187230) : ℂ) * ζ ^ 10 + ((152146 / 31205) : ℂ) * ζ ^ 11 + ((50173 / 62410) : ℂ) * ζ ^ 12 + ((181806 / 31205) : ℂ) * ζ ^ 13 + ((1781809 / 187230) : ℂ) * ζ ^ 14 - ((375431 / 62410) : ℂ) * ζ ^ 15 + ((1005347 / 93615) : ℂ) * ζ ^ 16 + ((1586113 / 187230) : ℂ) * ζ ^ 17 + ((868058 / 93615) : ℂ) * ζ ^ 18 + ((498071 / 187230) : ℂ) * ζ ^ 19 + ((251029 / 93615) : ℂ) * ζ ^ 20 + ((154993 / 31205) : ℂ) * ζ ^ 21 - ((295581 / 62410) : ℂ) * ζ ^ 22 + ((57774 / 6241) : ℂ) * ζ ^ 23 + ((828561 / 62410) : ℂ) * ζ ^ 24 - ((2117833 / 187230) : ℂ) * ζ ^ 25 + ((216233 / 62410) : ℂ) * ζ ^ 26 + ((2610241 / 187230) : ℂ) * ζ ^ 27 - ((9294 / 31205) : ℂ) * ζ ^ 28 - ((39794 / 6241) : ℂ) * ζ ^ 29 - ((11535 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep00CoefficientIdentity03 :
    row18_reducedY32_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep00Coefficient03 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep00CoefficientIdentity04 :
    row18_reducedY32_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep00Coefficient04 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep00CoefficientIdentity05 :
    row18_reducedY32_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep00Coefficient05 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep00CoefficientIdentity06 :
    row18_reducedY32_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep00Coefficient06 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep00CoefficientIdentity07 :
    row18_reducedY32_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep00Coefficient07 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep00CoefficientIdentity08 :
    row18_reducedY32_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep00Coefficient08 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep00CoefficientIdentity09 :
    row18_reducedY32_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep00Coefficient09 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep00CoefficientIdentity10 :
    row18_reducedY32_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep00Coefficient10 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep00CoefficientIdentity11 :
    row18_reducedY32_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep00Coefficient11 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep00CoefficientIdentity12 :
    row18_reducedY32_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep00Coefficient12 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep00CoefficientIdentity13 :
    row18_reducedY32_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep00Coefficient13 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep00CoefficientIdentity14 :
    row18_reducedY32_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep00Coefficient14 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep00CoefficientIdentity15 :
    row18_reducedY32_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY32_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep00Coefficient15 row18_reducedY32_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY32_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY32_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY32_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY32_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY32_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY32_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY32_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY32_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY32_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY32_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY32_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY32_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY32_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY32_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY32_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY32_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY32_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY32_combinationStep00CoefficientIdentity00,
      row18_reducedY32_combinationStep00CoefficientIdentity01,
      row18_reducedY32_combinationStep00CoefficientIdentity02,
      row18_reducedY32_combinationStep00CoefficientIdentity03,
      row18_reducedY32_combinationStep00CoefficientIdentity04,
      row18_reducedY32_combinationStep00CoefficientIdentity05,
      row18_reducedY32_combinationStep00CoefficientIdentity06,
      row18_reducedY32_combinationStep00CoefficientIdentity07,
      row18_reducedY32_combinationStep00CoefficientIdentity08,
      row18_reducedY32_combinationStep00CoefficientIdentity09,
      row18_reducedY32_combinationStep00CoefficientIdentity10,
      row18_reducedY32_combinationStep00CoefficientIdentity11,
      row18_reducedY32_combinationStep00CoefficientIdentity12,
      row18_reducedY32_combinationStep00CoefficientIdentity13,
      row18_reducedY32_combinationStep00CoefficientIdentity14,
      row18_reducedY32_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY32_combinationStep00Multiplier * equation

private def row18_reducedY32_combinationStep01Multiplier : ℂ :=
  (((1058 / 395) : ℂ) - ((1042 / 395) : ℂ) * ζ ^ 1 - ((886 / 79) : ℂ) * ζ ^ 2 + ((2296 / 1185) : ℂ) * ζ ^ 3 - ((11188 / 1185) : ℂ) * ζ ^ 5 - ((1874 / 237) : ℂ) * ζ ^ 6 - ((8452 / 1185) : ℂ) * ζ ^ 8 - ((1946 / 395) : ℂ) * ζ ^ 9 - ((11188 / 1185) : ℂ) * ζ ^ 11 - ((4226 / 1185) : ℂ) * ζ ^ 12 + ((1042 / 395) : ℂ) * ζ ^ 13 - ((2224 / 1185) : ℂ) * ζ ^ 15 + ((1042 / 395) : ℂ) * ζ ^ 17 + ((1874 / 237) : ℂ) * ζ ^ 18 + ((2964 / 395) : ℂ) * ζ ^ 21 + ((886 / 79) : ℂ) * ζ ^ 22 + ((5278 / 1185) : ℂ) * ζ ^ 24 + ((8062 / 1185) : ℂ) * ζ ^ 25 + ((8062 / 1185) : ℂ) * ζ ^ 27 + ((8452 / 1185) : ℂ) * ζ ^ 28 - ((1042 / 395) : ℂ) * ζ ^ 29 + ((11188 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY32_combinationStep01Coefficient00 : ℂ :=
  (-((81 / 79) : ℂ) + ((86 / 79) : ℂ) * ζ ^ 1 - ((164 / 237) : ℂ) * ζ ^ 2 + ((62 / 237) : ℂ) * ζ ^ 5 + ((1 / 3) : ℂ) * ζ ^ 6 + ((1 / 3) : ℂ) * ζ ^ 8 + ((62 / 237) : ℂ) * ζ ^ 9 - ((85 / 158) : ℂ) * ζ ^ 11 - ((37 / 158) : ℂ) * ζ ^ 12 - ((86 / 79) : ℂ) * ζ ^ 13 - ((87 / 79) : ℂ) * ζ ^ 15 - ((86 / 79) : ℂ) * ζ ^ 17 - ((67 / 474) : ℂ) * ζ ^ 18 - ((160 / 237) : ℂ) * ζ ^ 21 + ((164 / 237) : ℂ) * ζ ^ 22 - ((91 / 474) : ℂ) * ζ ^ 24 + ((196 / 237) : ℂ) * ζ ^ 25 + ((87 / 79) : ℂ) * ζ ^ 27 - ((1 / 3) : ℂ) * ζ ^ 28 + ((86 / 79) : ℂ) * ζ ^ 29 + ((269 / 474) : ℂ) * ζ ^ 30 + ((85 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep01CoefficientIdentity00 :
    row18_reducedY32_combinationStep01Coefficient00 =
      row18_reducedY32_combinationStep00Coefficient00 +
        row18_reducedY32_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep01Coefficient00 row18_reducedY32_combinationStep00Coefficient00 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 (((10306 / 31205) : ℂ) - ((6419 / 12482) : ℂ) * ζ ^ 1 + ((640811 / 187230) : ℂ) * ζ ^ 2 + ((83479 / 187230) : ℂ) * ζ ^ 3 + ((55829 / 93615) : ℂ) * ζ ^ 4 + ((307501 / 187230) : ℂ) * ζ ^ 5 - ((118117 / 93615) : ℂ) * ζ ^ 6 + ((12321 / 12482) : ℂ) * ζ ^ 7 + ((36740 / 18723) : ℂ) * ζ ^ 8 - ((82579 / 93615) : ℂ) * ζ ^ 9 - ((51571 / 93615) : ℂ) * ζ ^ 10 - ((11533 / 187230) : ℂ) * ζ ^ 11 + ((18441 / 31205) : ℂ) * ζ ^ 12 + ((7021 / 12482) : ℂ) * ζ ^ 13 - ((60803 / 62410) : ℂ) * ζ ^ 14 - ((23971 / 93615) : ℂ) * ζ ^ 15 - ((13608 / 31205) : ℂ) * ζ ^ 16 - ((203561 / 93615) : ℂ) * ζ ^ 17 - ((259909 / 187230) : ℂ) * ζ ^ 18 - ((27519 / 31205) : ℂ) * ζ ^ 19 + ((3471 / 6241) : ℂ) * ζ ^ 20 + ((9673 / 187230) : ℂ) * ζ ^ 21 - ((24181 / 93615) : ℂ) * ζ ^ 22 - ((3101 / 18723) : ℂ) * ζ ^ 23 - ((101417 / 93615) : ℂ) * ζ ^ 24 - ((898 / 93615) : ℂ) * ζ ^ 25 + ((4511 / 31205) : ℂ) * ζ ^ 26 - ((64009 / 37446) : ℂ) * ζ ^ 27 - ((96167 / 187230) : ℂ) * ζ ^ 28 + ((25173 / 31205) : ℂ) * ζ ^ 29 + ((2797 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep01Coefficient01 : ℂ :=
  (-((837 / 158) : ℂ) + ((497 / 79) : ℂ) * ζ ^ 1 - ((880 / 237) : ℂ) * ζ ^ 2 - ((976 / 237) : ℂ) * ζ ^ 3 + ((213 / 79) : ℂ) * ζ ^ 5 - ((1921 / 237) : ℂ) * ζ ^ 6 - ((4445 / 474) : ℂ) * ζ ^ 9 - ((213 / 79) : ℂ) * ζ ^ 11 - ((1136 / 237) : ℂ) * ζ ^ 12 - ((497 / 79) : ℂ) * ζ ^ 13 - ((2741 / 474) : ℂ) * ζ ^ 15 - ((497 / 79) : ℂ) * ζ ^ 17 - ((161 / 237) : ℂ) * ζ ^ 18 - ((1615 / 237) : ℂ) * ζ ^ 21 + ((880 / 237) : ℂ) * ζ ^ 22 - ((837 / 158) : ℂ) * ζ ^ 24 + ((284 / 79) : ℂ) * ζ ^ 25 - ((284 / 79) : ℂ) * ζ ^ 27 + ((497 / 79) : ℂ) * ζ ^ 29 - ((1760 / 237) : ℂ) * ζ ^ 30 + ((213 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep01CoefficientIdentity01 :
    row18_reducedY32_combinationStep01Coefficient01 =
      row18_reducedY32_combinationStep00Coefficient01 +
        row18_reducedY32_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep01Coefficient01 row18_reducedY32_combinationStep00Coefficient01 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 (((944221 / 187230) : ℂ) - ((535133 / 187230) : ℂ) * ζ ^ 1 + ((7786 / 93615) : ℂ) * ζ ^ 2 + ((26341 / 6241) : ℂ) * ζ ^ 3 + ((85821 / 62410) : ℂ) * ζ ^ 4 + ((347398 / 93615) : ℂ) * ζ ^ 5 + ((186311 / 93615) : ℂ) * ζ ^ 6 - ((912 / 31205) : ℂ) * ζ ^ 7 + ((190397 / 31205) : ℂ) * ζ ^ 8 + ((642179 / 187230) : ℂ) * ζ ^ 9 - ((55963 / 187230) : ℂ) * ζ ^ 10 + ((80348 / 31205) : ℂ) * ζ ^ 11 + ((56811 / 12482) : ℂ) * ζ ^ 12 + ((215573 / 187230) : ℂ) * ζ ^ 13 - ((172912 / 93615) : ℂ) * ζ ^ 14 + ((93263 / 93615) : ℂ) * ζ ^ 15 + ((641 / 790) : ℂ) * ζ ^ 16 - ((24176 / 31205) : ℂ) * ζ ^ 17 + ((2953 / 1185) : ℂ) * ζ ^ 18 - ((7498 / 6241) : ℂ) * ζ ^ 19 - ((109609 / 31205) : ℂ) * ζ ^ 20 + ((486014 / 93615) : ℂ) * ζ ^ 21 + ((59227 / 187230) : ℂ) * ζ ^ 22 - ((78903 / 31205) : ℂ) * ζ ^ 23 - ((22499 / 37446) : ℂ) * ζ ^ 24 - ((55864 / 93615) : ℂ) * ζ ^ 25 - ((102218 / 93615) : ℂ) * ζ ^ 26 + ((6844 / 93615) : ℂ) * ζ ^ 27 - ((83416 / 93615) : ℂ) * ζ ^ 28 + ((22376 / 31205) : ℂ) * ζ ^ 29 + ((78316 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep01Coefficient02 : ℂ :=
  (-((545 / 237) : ℂ) + ((307 / 79) : ℂ) * ζ ^ 1 + ((761 / 237) : ℂ) * ζ ^ 2 - ((1153 / 474) : ℂ) * ζ ^ 3 + ((2753 / 474) : ℂ) * ζ ^ 5 + ((867 / 158) : ℂ) * ζ ^ 8 - ((183 / 79) : ℂ) * ζ ^ 9 + ((2251 / 474) : ℂ) * ζ ^ 11 - ((421 / 474) : ℂ) * ζ ^ 12 - ((307 / 79) : ℂ) * ζ ^ 13 + ((121 / 237) : ℂ) * ζ ^ 15 - ((307 / 79) : ℂ) * ζ ^ 17 - ((761 / 237) : ℂ) * ζ ^ 18 - ((2995 / 474) : ℂ) * ζ ^ 21 - ((761 / 237) : ℂ) * ζ ^ 22 - ((1090 / 237) : ℂ) * ζ ^ 24 - ((911 / 474) : ℂ) * ζ ^ 25 - ((2995 / 474) : ℂ) * ζ ^ 27 - ((867 / 158) : ℂ) * ζ ^ 28 + ((307 / 79) : ℂ) * ζ ^ 29 - ((2189 / 474) : ℂ) * ζ ^ 30 - ((2251 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep01CoefficientIdentity02 :
    row18_reducedY32_combinationStep01Coefficient02 =
      row18_reducedY32_combinationStep00Coefficient02 +
        row18_reducedY32_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep01Coefficient02 row18_reducedY32_combinationStep00Coefficient02 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep01Coefficient03 : ℂ :=
  (((81 / 79) : ℂ) - ((86 / 79) : ℂ) * ζ ^ 1 + ((164 / 237) : ℂ) * ζ ^ 2 - ((62 / 237) : ℂ) * ζ ^ 5 - ((1 / 3) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ((62 / 237) : ℂ) * ζ ^ 9 + ((85 / 158) : ℂ) * ζ ^ 11 + ((37 / 158) : ℂ) * ζ ^ 12 + ((86 / 79) : ℂ) * ζ ^ 13 + ((87 / 79) : ℂ) * ζ ^ 15 + ((86 / 79) : ℂ) * ζ ^ 17 + ((67 / 474) : ℂ) * ζ ^ 18 + ((160 / 237) : ℂ) * ζ ^ 21 - ((164 / 237) : ℂ) * ζ ^ 22 + ((91 / 474) : ℂ) * ζ ^ 24 - ((196 / 237) : ℂ) * ζ ^ 25 - ((87 / 79) : ℂ) * ζ ^ 27 + ((1 / 3) : ℂ) * ζ ^ 28 - ((86 / 79) : ℂ) * ζ ^ 29 - ((269 / 474) : ℂ) * ζ ^ 30 - ((85 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep01CoefficientIdentity03 :
    row18_reducedY32_combinationStep01Coefficient03 =
      row18_reducedY32_combinationStep00Coefficient03 +
        row18_reducedY32_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep01Coefficient03 row18_reducedY32_combinationStep00Coefficient03 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 (-((10306 / 31205) : ℂ) + ((6419 / 12482) : ℂ) * ζ ^ 1 - ((640811 / 187230) : ℂ) * ζ ^ 2 - ((83479 / 187230) : ℂ) * ζ ^ 3 - ((55829 / 93615) : ℂ) * ζ ^ 4 - ((307501 / 187230) : ℂ) * ζ ^ 5 + ((118117 / 93615) : ℂ) * ζ ^ 6 - ((12321 / 12482) : ℂ) * ζ ^ 7 - ((36740 / 18723) : ℂ) * ζ ^ 8 + ((82579 / 93615) : ℂ) * ζ ^ 9 + ((51571 / 93615) : ℂ) * ζ ^ 10 + ((11533 / 187230) : ℂ) * ζ ^ 11 - ((18441 / 31205) : ℂ) * ζ ^ 12 - ((7021 / 12482) : ℂ) * ζ ^ 13 + ((60803 / 62410) : ℂ) * ζ ^ 14 + ((23971 / 93615) : ℂ) * ζ ^ 15 + ((13608 / 31205) : ℂ) * ζ ^ 16 + ((203561 / 93615) : ℂ) * ζ ^ 17 + ((259909 / 187230) : ℂ) * ζ ^ 18 + ((27519 / 31205) : ℂ) * ζ ^ 19 - ((3471 / 6241) : ℂ) * ζ ^ 20 - ((9673 / 187230) : ℂ) * ζ ^ 21 + ((24181 / 93615) : ℂ) * ζ ^ 22 + ((3101 / 18723) : ℂ) * ζ ^ 23 + ((101417 / 93615) : ℂ) * ζ ^ 24 + ((898 / 93615) : ℂ) * ζ ^ 25 - ((4511 / 31205) : ℂ) * ζ ^ 26 + ((64009 / 37446) : ℂ) * ζ ^ 27 + ((96167 / 187230) : ℂ) * ζ ^ 28 - ((25173 / 31205) : ℂ) * ζ ^ 29 - ((2797 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep01CoefficientIdentity04 :
    row18_reducedY32_combinationStep01Coefficient04 =
      row18_reducedY32_combinationStep00Coefficient04 +
        row18_reducedY32_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep01Coefficient04 row18_reducedY32_combinationStep00Coefficient04 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep01CoefficientIdentity05 :
    row18_reducedY32_combinationStep01Coefficient05 =
      row18_reducedY32_combinationStep00Coefficient05 +
        row18_reducedY32_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep01Coefficient05 row18_reducedY32_combinationStep00Coefficient05 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep01CoefficientIdentity06 :
    row18_reducedY32_combinationStep01Coefficient06 =
      row18_reducedY32_combinationStep00Coefficient06 +
        row18_reducedY32_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep01Coefficient06 row18_reducedY32_combinationStep00Coefficient06 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep01CoefficientIdentity07 :
    row18_reducedY32_combinationStep01Coefficient07 =
      row18_reducedY32_combinationStep00Coefficient07 +
        row18_reducedY32_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep01Coefficient07 row18_reducedY32_combinationStep00Coefficient07 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep01CoefficientIdentity08 :
    row18_reducedY32_combinationStep01Coefficient08 =
      row18_reducedY32_combinationStep00Coefficient08 +
        row18_reducedY32_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep01Coefficient08 row18_reducedY32_combinationStep00Coefficient08 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep01CoefficientIdentity09 :
    row18_reducedY32_combinationStep01Coefficient09 =
      row18_reducedY32_combinationStep00Coefficient09 +
        row18_reducedY32_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep01Coefficient09 row18_reducedY32_combinationStep00Coefficient09 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep01CoefficientIdentity10 :
    row18_reducedY32_combinationStep01Coefficient10 =
      row18_reducedY32_combinationStep00Coefficient10 +
        row18_reducedY32_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep01Coefficient10 row18_reducedY32_combinationStep00Coefficient10 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep01CoefficientIdentity11 :
    row18_reducedY32_combinationStep01Coefficient11 =
      row18_reducedY32_combinationStep00Coefficient11 +
        row18_reducedY32_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep01Coefficient11 row18_reducedY32_combinationStep00Coefficient11 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep01CoefficientIdentity12 :
    row18_reducedY32_combinationStep01Coefficient12 =
      row18_reducedY32_combinationStep00Coefficient12 +
        row18_reducedY32_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep01Coefficient12 row18_reducedY32_combinationStep00Coefficient12 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep01CoefficientIdentity13 :
    row18_reducedY32_combinationStep01Coefficient13 =
      row18_reducedY32_combinationStep00Coefficient13 +
        row18_reducedY32_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep01Coefficient13 row18_reducedY32_combinationStep00Coefficient13 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep01CoefficientIdentity14 :
    row18_reducedY32_combinationStep01Coefficient14 =
      row18_reducedY32_combinationStep00Coefficient14 +
        row18_reducedY32_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep01Coefficient14 row18_reducedY32_combinationStep00Coefficient14 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep01CoefficientIdentity15 :
    row18_reducedY32_combinationStep01Coefficient15 =
      row18_reducedY32_combinationStep00Coefficient15 +
        row18_reducedY32_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep01Coefficient15 row18_reducedY32_combinationStep00Coefficient15 row18_reducedY32_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY32_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY32_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY32_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY32_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY32_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY32_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY32_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY32_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY32_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY32_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY32_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY32_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY32_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY32_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY32_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY32_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY32_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY32_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY32_combinationStep01CoefficientIdentity00,
      row18_reducedY32_combinationStep01CoefficientIdentity01,
      row18_reducedY32_combinationStep01CoefficientIdentity02,
      row18_reducedY32_combinationStep01CoefficientIdentity03,
      row18_reducedY32_combinationStep01CoefficientIdentity04,
      row18_reducedY32_combinationStep01CoefficientIdentity05,
      row18_reducedY32_combinationStep01CoefficientIdentity06,
      row18_reducedY32_combinationStep01CoefficientIdentity07,
      row18_reducedY32_combinationStep01CoefficientIdentity08,
      row18_reducedY32_combinationStep01CoefficientIdentity09,
      row18_reducedY32_combinationStep01CoefficientIdentity10,
      row18_reducedY32_combinationStep01CoefficientIdentity11,
      row18_reducedY32_combinationStep01CoefficientIdentity12,
      row18_reducedY32_combinationStep01CoefficientIdentity13,
      row18_reducedY32_combinationStep01CoefficientIdentity14,
      row18_reducedY32_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY32_combinationStep01Multiplier * equation

private def row18_reducedY32_combinationStep02Multiplier : ℂ :=
  (((2 / 395) : ℂ) - ((86 / 79) : ℂ) * ζ ^ 1 + ((17638 / 1185) : ℂ) * ζ ^ 2 + ((3098 / 237) : ℂ) * ζ ^ 5 + ((17632 / 1185) : ℂ) * ζ ^ 6 + ((17632 / 1185) : ℂ) * ζ ^ 8 + ((3098 / 237) : ℂ) * ζ ^ 9 + ((1428 / 79) : ℂ) * ζ ^ 11 + ((4232 / 395) : ℂ) * ζ ^ 12 + ((86 / 79) : ℂ) * ζ ^ 13 + ((1628 / 237) : ℂ) * ζ ^ 15 + ((86 / 79) : ℂ) * ζ ^ 17 - ((10804 / 1185) : ℂ) * ζ ^ 18 - ((1420 / 237) : ℂ) * ζ ^ 21 - ((17638 / 1185) : ℂ) * ζ ^ 22 - ((2276 / 395) : ℂ) * ζ ^ 24 - ((3356 / 237) : ℂ) * ζ ^ 25 - ((1628 / 237) : ℂ) * ζ ^ 27 - ((17632 / 1185) : ℂ) * ζ ^ 28 - ((86 / 79) : ℂ) * ζ ^ 29 + ((4936 / 1185) : ℂ) * ζ ^ 30 - ((1428 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY32_combinationStep02Coefficient00 : ℂ :=
  (((43199 / 187230) : ℂ) + ((79129 / 187230) : ℂ) * ζ ^ 1 - ((202098 / 31205) : ℂ) * ζ ^ 2 - ((1080373 / 187230) : ℂ) * ζ ^ 5 - ((1255787 / 187230) : ℂ) * ζ ^ 6 - ((1255787 / 187230) : ℂ) * ζ ^ 8 - ((1080373 / 187230) : ℂ) * ζ ^ 9 - ((43723 / 6241) : ℂ) * ζ ^ 11 - ((942331 / 187230) : ℂ) * ζ ^ 12 - ((79129 / 187230) : ℂ) * ζ ^ 13 - ((46407 / 12482) : ℂ) * ζ ^ 15 - ((79129 / 187230) : ℂ) * ζ ^ 17 + ((325682 / 93615) : ℂ) * ζ ^ 18 + ((83437 / 31205) : ℂ) * ζ ^ 21 + ((202098 / 31205) : ℂ) * ζ ^ 22 + ((604423 / 187230) : ℂ) * ζ ^ 24 + ((579751 / 93615) : ℂ) * ζ ^ 25 + ((46407 / 12482) : ℂ) * ζ ^ 27 + ((1255787 / 187230) : ℂ) * ζ ^ 28 + ((79129 / 187230) : ℂ) * ζ ^ 29 - ((156728 / 93615) : ℂ) * ζ ^ 30 + ((43723 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep02CoefficientIdentity00 :
    row18_reducedY32_combinationStep02Coefficient00 =
      row18_reducedY32_combinationStep01Coefficient00 +
        row18_reducedY32_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep02Coefficient00 row18_reducedY32_combinationStep01Coefficient00 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 (-((47041 / 37446) : ℂ) + ((66232 / 93615) : ℂ) * ζ ^ 1 + ((96985 / 18723) : ℂ) * ζ ^ 2 + ((15184 / 18723) : ℂ) * ζ ^ 3 - ((17190 / 6241) : ℂ) * ζ ^ 4 + ((92153 / 18723) : ℂ) * ζ ^ 5 + ((113303 / 62410) : ℂ) * ζ ^ 6 - ((86011 / 18723) : ℂ) * ζ ^ 7 + ((356066 / 93615) : ℂ) * ζ ^ 8 + ((6896 / 6241) : ℂ) * ζ ^ 9 - ((417412 / 93615) : ℂ) * ζ ^ 10 + ((130108 / 31205) : ℂ) * ζ ^ 11 - ((132352 / 93615) : ℂ) * ζ ^ 12 - ((544936 / 93615) : ℂ) * ζ ^ 13 + ((697861 / 93615) : ℂ) * ζ ^ 14 - ((680599 / 187230) : ℂ) * ζ ^ 15 - ((422861 / 187230) : ℂ) * ζ ^ 16 + ((616423 / 93615) : ℂ) * ζ ^ 17 - ((253921 / 62410) : ℂ) * ζ ^ 18 - ((11822 / 31205) : ℂ) * ζ ^ 19 + ((345761 / 187230) : ℂ) * ζ ^ 20 - ((859091 / 187230) : ℂ) * ζ ^ 21 - ((37079 / 62410) : ℂ) * ζ ^ 22 - ((50284 / 93615) : ℂ) * ζ ^ 23 - ((17027 / 187230) : ℂ) * ζ ^ 24 - ((183109 / 187230) : ℂ) * ζ ^ 25 + ((437 / 62410) : ℂ) * ζ ^ 26 + ((48149 / 31205) : ℂ) * ζ ^ 27 - ((83164 / 93615) : ℂ) * ζ ^ 28 + ((102956 / 93615) : ℂ) * ζ ^ 29 - ((4998 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep02Coefficient01 : ℂ :=
  (((175685 / 18723) : ℂ) - ((382423 / 37446) : ℂ) * ζ ^ 1 + ((181705 / 37446) : ℂ) * ζ ^ 2 + ((113299 / 12482) : ℂ) * ζ ^ 3 - ((97361 / 37446) : ℂ) * ζ ^ 5 + ((81488 / 6241) : ℂ) * ζ ^ 6 + ((267052 / 18723) : ℂ) * ζ ^ 9 + ((97361 / 37446) : ℂ) * ζ ^ 11 + ((221273 / 37446) : ℂ) * ζ ^ 12 + ((382423 / 37446) : ℂ) * ζ ^ 13 + ((41507 / 6241) : ℂ) * ζ ^ 15 + ((382423 / 37446) : ℂ) * ζ ^ 17 + ((62759 / 18723) : ℂ) * ζ ^ 18 + ((218629 / 18723) : ℂ) * ζ ^ 21 - ((181705 / 37446) : ℂ) * ζ ^ 22 + ((175685 / 18723) : ℂ) * ζ ^ 24 - ((142531 / 18723) : ℂ) * ζ ^ 25 + ((142531 / 18723) : ℂ) * ζ ^ 27 - ((382423 / 37446) : ℂ) * ζ ^ 29 + ((181705 / 18723) : ℂ) * ζ ^ 30 - ((97361 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep02CoefficientIdentity01 :
    row18_reducedY32_combinationStep02Coefficient01 =
      row18_reducedY32_combinationStep01Coefficient01 +
        row18_reducedY32_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep02Coefficient01 row18_reducedY32_combinationStep01Coefficient01 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 (-((1374244 / 93615) : ℂ) + ((609049 / 37446) : ℂ) * ζ ^ 1 - ((156727 / 31205) : ℂ) * ζ ^ 2 - ((1075289 / 62410) : ℂ) * ζ ^ 3 + ((2811089 / 187230) : ℂ) * ζ ^ 4 - ((215031 / 31205) : ℂ) * ζ ^ 5 - ((100561 / 6241) : ℂ) * ζ ^ 6 + ((1746287 / 187230) : ℂ) * ζ ^ 7 - ((1234423 / 187230) : ℂ) * ζ ^ 8 - ((12959 / 790) : ℂ) * ζ ^ 9 + ((1036817 / 187230) : ℂ) * ζ ^ 10 - ((219133 / 37446) : ℂ) * ζ ^ 11 - ((1030959 / 62410) : ℂ) * ζ ^ 12 + ((587728 / 93615) : ℂ) * ζ ^ 13 - ((1962893 / 187230) : ℂ) * ζ ^ 14 - ((1903393 / 187230) : ℂ) * ζ ^ 15 + ((227845 / 37446) : ℂ) * ζ ^ 16 - ((1223596 / 93615) : ℂ) * ζ ^ 17 - ((526713 / 62410) : ℂ) * ζ ^ 18 + ((146164 / 18723) : ℂ) * ζ ^ 19 - ((787913 / 62410) : ℂ) * ζ ^ 20 - ((250752 / 31205) : ℂ) * ζ ^ 21 + ((1018021 / 187230) : ℂ) * ζ ^ 22 - ((160887 / 31205) : ℂ) * ζ ^ 23 - ((99411 / 12482) : ℂ) * ζ ^ 24 + ((104527 / 18723) : ℂ) * ζ ^ 25 - ((45619 / 37446) : ℂ) * ζ ^ 26 - ((597299 / 93615) : ℂ) * ζ ^ 27 + ((345079 / 62410) : ℂ) * ζ ^ 28 - ((273128 / 93615) : ℂ) * ζ ^ 29 - ((4641 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep02Coefficient02 : ℂ :=
  (-((545 / 237) : ℂ) + ((307 / 79) : ℂ) * ζ ^ 1 + ((761 / 237) : ℂ) * ζ ^ 2 - ((1153 / 474) : ℂ) * ζ ^ 3 + ((2753 / 474) : ℂ) * ζ ^ 5 + ((867 / 158) : ℂ) * ζ ^ 8 - ((183 / 79) : ℂ) * ζ ^ 9 + ((2251 / 474) : ℂ) * ζ ^ 11 - ((421 / 474) : ℂ) * ζ ^ 12 - ((307 / 79) : ℂ) * ζ ^ 13 + ((121 / 237) : ℂ) * ζ ^ 15 - ((307 / 79) : ℂ) * ζ ^ 17 - ((761 / 237) : ℂ) * ζ ^ 18 - ((2995 / 474) : ℂ) * ζ ^ 21 - ((761 / 237) : ℂ) * ζ ^ 22 - ((1090 / 237) : ℂ) * ζ ^ 24 - ((911 / 474) : ℂ) * ζ ^ 25 - ((2995 / 474) : ℂ) * ζ ^ 27 - ((867 / 158) : ℂ) * ζ ^ 28 + ((307 / 79) : ℂ) * ζ ^ 29 - ((2189 / 474) : ℂ) * ζ ^ 30 - ((2251 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep02CoefficientIdentity02 :
    row18_reducedY32_combinationStep02Coefficient02 =
      row18_reducedY32_combinationStep01Coefficient02 +
        row18_reducedY32_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep02Coefficient02 row18_reducedY32_combinationStep01Coefficient02 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep02Coefficient03 : ℂ :=
  (((81 / 79) : ℂ) - ((86 / 79) : ℂ) * ζ ^ 1 + ((164 / 237) : ℂ) * ζ ^ 2 - ((62 / 237) : ℂ) * ζ ^ 5 - ((1 / 3) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ((62 / 237) : ℂ) * ζ ^ 9 + ((85 / 158) : ℂ) * ζ ^ 11 + ((37 / 158) : ℂ) * ζ ^ 12 + ((86 / 79) : ℂ) * ζ ^ 13 + ((87 / 79) : ℂ) * ζ ^ 15 + ((86 / 79) : ℂ) * ζ ^ 17 + ((67 / 474) : ℂ) * ζ ^ 18 + ((160 / 237) : ℂ) * ζ ^ 21 - ((164 / 237) : ℂ) * ζ ^ 22 + ((91 / 474) : ℂ) * ζ ^ 24 - ((196 / 237) : ℂ) * ζ ^ 25 - ((87 / 79) : ℂ) * ζ ^ 27 + ((1 / 3) : ℂ) * ζ ^ 28 - ((86 / 79) : ℂ) * ζ ^ 29 - ((269 / 474) : ℂ) * ζ ^ 30 - ((85 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep02CoefficientIdentity03 :
    row18_reducedY32_combinationStep02Coefficient03 =
      row18_reducedY32_combinationStep01Coefficient03 +
        row18_reducedY32_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep02Coefficient03 row18_reducedY32_combinationStep01Coefficient03 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep02Coefficient04 : ℂ :=
  (-((235169 / 187230) : ℂ) + ((124691 / 187230) : ℂ) * ζ ^ 1 + ((541514 / 93615) : ℂ) * ζ ^ 2 + ((376451 / 62410) : ℂ) * ζ ^ 5 + ((439399 / 62410) : ℂ) * ζ ^ 6 + ((439399 / 62410) : ℂ) * ζ ^ 8 + ((376451 / 62410) : ℂ) * ζ ^ 9 + ((80731 / 12482) : ℂ) * ζ ^ 11 + ((449243 / 93615) : ℂ) * ζ ^ 12 - ((124691 / 187230) : ℂ) * ζ ^ 13 + ((32661 / 12482) : ℂ) * ζ ^ 15 - ((124691 / 187230) : ℂ) * ζ ^ 17 - ((225943 / 62410) : ℂ) * ζ ^ 18 - ((313511 / 93615) : ℂ) * ζ ^ 21 - ((541514 / 93615) : ℂ) * ζ ^ 22 - ((106728 / 31205) : ℂ) * ζ ^ 24 - ((502331 / 93615) : ℂ) * ζ ^ 25 - ((32661 / 12482) : ℂ) * ζ ^ 27 - ((439399 / 62410) : ℂ) * ζ ^ 28 + ((124691 / 187230) : ℂ) * ζ ^ 29 + ((419711 / 187230) : ℂ) * ζ ^ 30 - ((80731 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep02CoefficientIdentity04 :
    row18_reducedY32_combinationStep02Coefficient04 =
      row18_reducedY32_combinationStep01Coefficient04 +
        row18_reducedY32_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep02Coefficient04 row18_reducedY32_combinationStep01Coefficient04 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 (((47041 / 37446) : ℂ) - ((66232 / 93615) : ℂ) * ζ ^ 1 - ((96985 / 18723) : ℂ) * ζ ^ 2 - ((15184 / 18723) : ℂ) * ζ ^ 3 + ((17190 / 6241) : ℂ) * ζ ^ 4 - ((92153 / 18723) : ℂ) * ζ ^ 5 - ((113303 / 62410) : ℂ) * ζ ^ 6 + ((86011 / 18723) : ℂ) * ζ ^ 7 - ((356066 / 93615) : ℂ) * ζ ^ 8 - ((6896 / 6241) : ℂ) * ζ ^ 9 + ((417412 / 93615) : ℂ) * ζ ^ 10 - ((130108 / 31205) : ℂ) * ζ ^ 11 + ((132352 / 93615) : ℂ) * ζ ^ 12 + ((544936 / 93615) : ℂ) * ζ ^ 13 - ((697861 / 93615) : ℂ) * ζ ^ 14 + ((680599 / 187230) : ℂ) * ζ ^ 15 + ((422861 / 187230) : ℂ) * ζ ^ 16 - ((616423 / 93615) : ℂ) * ζ ^ 17 + ((253921 / 62410) : ℂ) * ζ ^ 18 + ((11822 / 31205) : ℂ) * ζ ^ 19 - ((345761 / 187230) : ℂ) * ζ ^ 20 + ((859091 / 187230) : ℂ) * ζ ^ 21 + ((37079 / 62410) : ℂ) * ζ ^ 22 + ((50284 / 93615) : ℂ) * ζ ^ 23 + ((17027 / 187230) : ℂ) * ζ ^ 24 + ((183109 / 187230) : ℂ) * ζ ^ 25 - ((437 / 62410) : ℂ) * ζ ^ 26 - ((48149 / 31205) : ℂ) * ζ ^ 27 + ((83164 / 93615) : ℂ) * ζ ^ 28 - ((102956 / 93615) : ℂ) * ζ ^ 29 + ((4998 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep02CoefficientIdentity05 :
    row18_reducedY32_combinationStep02Coefficient05 =
      row18_reducedY32_combinationStep01Coefficient05 +
        row18_reducedY32_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep02Coefficient05 row18_reducedY32_combinationStep01Coefficient05 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep02Coefficient06 : ℂ :=
  (((45866 / 18723) : ℂ) - ((30516 / 31205) : ℂ) * ζ ^ 1 + ((12945 / 12482) : ℂ) * ζ ^ 2 - ((35483 / 93615) : ℂ) * ζ ^ 3 + ((103007 / 187230) : ℂ) * ζ ^ 5 + ((6396 / 6241) : ℂ) * ζ ^ 6 + ((7421 / 37446) : ℂ) * ζ ^ 8 + ((57031 / 93615) : ℂ) * ζ ^ 9 + ((30838 / 31205) : ℂ) * ζ ^ 11 + ((7421 / 37446) : ℂ) * ζ ^ 12 + ((30516 / 31205) : ℂ) * ζ ^ 13 + ((119023 / 62410) : ℂ) * ζ ^ 15 + ((30516 / 31205) : ℂ) * ζ ^ 17 + ((153 / 12482) : ℂ) * ζ ^ 18 + ((127031 / 93615) : ℂ) * ζ ^ 21 - ((12945 / 12482) : ℂ) * ζ ^ 22 - ((286103 / 187230) : ℂ) * ζ ^ 25 - ((127031 / 93615) : ℂ) * ζ ^ 27 - ((7421 / 37446) : ℂ) * ζ ^ 28 - ((30516 / 31205) : ℂ) * ζ ^ 29 + ((3198 / 6241) : ℂ) * ζ ^ 30 - ((30838 / 31205) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep02CoefficientIdentity06 :
    row18_reducedY32_combinationStep02Coefficient06 =
      row18_reducedY32_combinationStep01Coefficient06 +
        row18_reducedY32_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep02Coefficient06 row18_reducedY32_combinationStep01Coefficient06 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 (-((229387 / 93615) : ℂ) + ((13843 / 12482) : ℂ) * ζ ^ 1 - ((107543 / 37446) : ℂ) * ζ ^ 2 + ((6426 / 6241) : ℂ) * ζ ^ 3 + ((69257 / 37446) : ℂ) * ζ ^ 4 - ((65551 / 31205) : ℂ) * ζ ^ 5 + ((11141 / 18723) : ℂ) * ζ ^ 6 - ((141437 / 187230) : ℂ) * ζ ^ 7 - ((309721 / 62410) : ℂ) * ζ ^ 8 + ((273323 / 187230) : ℂ) * ζ ^ 9 + ((11948 / 6241) : ℂ) * ζ ^ 10 + ((153239 / 187230) : ℂ) * ζ ^ 11 + ((113516 / 93615) : ℂ) * ζ ^ 12 + ((15448 / 93615) : ℂ) * ζ ^ 13 - ((801 / 6241) : ℂ) * ζ ^ 14 + ((226 / 1185) : ℂ) * ζ ^ 15 + ((58679 / 93615) : ℂ) * ζ ^ 16 + ((44278 / 31205) : ℂ) * ζ ^ 17 + ((4637 / 18723) : ℂ) * ζ ^ 18 + ((102097 / 93615) : ℂ) * ζ ^ 19 - ((90556 / 93615) : ℂ) * ζ ^ 20 - ((75107 / 187230) : ℂ) * ζ ^ 21 + ((6949 / 18723) : ℂ) * ζ ^ 22 - ((43244 / 18723) : ℂ) * ζ ^ 23 + ((24227 / 18723) : ℂ) * ζ ^ 24 + ((168127 / 187230) : ℂ) * ζ ^ 25 - ((63383 / 37446) : ℂ) * ζ ^ 26 + ((250387 / 93615) : ℂ) * ζ ^ 27 - ((10147 / 62410) : ℂ) * ζ ^ 28 - ((15902 / 6241) : ℂ) * ζ ^ 29 - ((5355 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep02CoefficientIdentity07 :
    row18_reducedY32_combinationStep02Coefficient07 =
      row18_reducedY32_combinationStep01Coefficient07 +
        row18_reducedY32_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep02Coefficient07 row18_reducedY32_combinationStep01Coefficient07 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep02CoefficientIdentity08 :
    row18_reducedY32_combinationStep02Coefficient08 =
      row18_reducedY32_combinationStep01Coefficient08 +
        row18_reducedY32_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep02Coefficient08 row18_reducedY32_combinationStep01Coefficient08 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep02CoefficientIdentity09 :
    row18_reducedY32_combinationStep02Coefficient09 =
      row18_reducedY32_combinationStep01Coefficient09 +
        row18_reducedY32_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep02Coefficient09 row18_reducedY32_combinationStep01Coefficient09 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep02CoefficientIdentity10 :
    row18_reducedY32_combinationStep02Coefficient10 =
      row18_reducedY32_combinationStep01Coefficient10 +
        row18_reducedY32_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep02Coefficient10 row18_reducedY32_combinationStep01Coefficient10 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep02CoefficientIdentity11 :
    row18_reducedY32_combinationStep02Coefficient11 =
      row18_reducedY32_combinationStep01Coefficient11 +
        row18_reducedY32_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep02Coefficient11 row18_reducedY32_combinationStep01Coefficient11 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep02CoefficientIdentity12 :
    row18_reducedY32_combinationStep02Coefficient12 =
      row18_reducedY32_combinationStep01Coefficient12 +
        row18_reducedY32_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep02Coefficient12 row18_reducedY32_combinationStep01Coefficient12 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep02CoefficientIdentity13 :
    row18_reducedY32_combinationStep02Coefficient13 =
      row18_reducedY32_combinationStep01Coefficient13 +
        row18_reducedY32_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep02Coefficient13 row18_reducedY32_combinationStep01Coefficient13 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep02CoefficientIdentity14 :
    row18_reducedY32_combinationStep02Coefficient14 =
      row18_reducedY32_combinationStep01Coefficient14 +
        row18_reducedY32_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep02Coefficient14 row18_reducedY32_combinationStep01Coefficient14 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep02CoefficientIdentity15 :
    row18_reducedY32_combinationStep02Coefficient15 =
      row18_reducedY32_combinationStep01Coefficient15 +
        row18_reducedY32_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep02Coefficient15 row18_reducedY32_combinationStep01Coefficient15 row18_reducedY32_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY32_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY32_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY32_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY32_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY32_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY32_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY32_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY32_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY32_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY32_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY32_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY32_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY32_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY32_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY32_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY32_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY32_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY32_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY32_combinationStep02CoefficientIdentity00,
      row18_reducedY32_combinationStep02CoefficientIdentity01,
      row18_reducedY32_combinationStep02CoefficientIdentity02,
      row18_reducedY32_combinationStep02CoefficientIdentity03,
      row18_reducedY32_combinationStep02CoefficientIdentity04,
      row18_reducedY32_combinationStep02CoefficientIdentity05,
      row18_reducedY32_combinationStep02CoefficientIdentity06,
      row18_reducedY32_combinationStep02CoefficientIdentity07,
      row18_reducedY32_combinationStep02CoefficientIdentity08,
      row18_reducedY32_combinationStep02CoefficientIdentity09,
      row18_reducedY32_combinationStep02CoefficientIdentity10,
      row18_reducedY32_combinationStep02CoefficientIdentity11,
      row18_reducedY32_combinationStep02CoefficientIdentity12,
      row18_reducedY32_combinationStep02CoefficientIdentity13,
      row18_reducedY32_combinationStep02CoefficientIdentity14,
      row18_reducedY32_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY32_combinationStep02Multiplier * equation

private def row18_reducedY32_combinationStep03Multiplier : ℂ :=
  (-((400 / 237) : ℂ) + ((60 / 79) : ℂ) * ζ ^ 1 + ((2864 / 237) : ℂ) * ζ ^ 2 - ((276 / 79) : ℂ) * ζ ^ 3 + ((2966 / 237) : ℂ) * ζ ^ 5 + ((1844 / 237) : ℂ) * ζ ^ 6 + ((2996 / 237) : ℂ) * ζ ^ 8 + ((1456 / 237) : ℂ) * ζ ^ 9 + ((2966 / 237) : ℂ) * ζ ^ 11 + ((1498 / 237) : ℂ) * ζ ^ 12 - ((60 / 79) : ℂ) * ζ ^ 13 + ((1330 / 237) : ℂ) * ζ ^ 15 - ((60 / 79) : ℂ) * ζ ^ 17 - ((1844 / 237) : ℂ) * ζ ^ 18 - ((2138 / 237) : ℂ) * ζ ^ 21 - ((2864 / 237) : ℂ) * ζ ^ 22 - ((2596 / 237) : ℂ) * ζ ^ 24 - ((2786 / 237) : ℂ) * ζ ^ 25 - ((2786 / 237) : ℂ) * ζ ^ 27 - ((2996 / 237) : ℂ) * ζ ^ 28 + ((60 / 79) : ℂ) * ζ ^ 29 - ((2966 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY32_combinationStep03Coefficient00 : ℂ :=
  (((137 / 790) : ℂ) + ((156 / 395) : ℂ) * ζ ^ 1 - ((6069 / 790) : ℂ) * ζ ^ 2 - ((2722 / 395) : ℂ) * ζ ^ 5 - ((3103 / 395) : ℂ) * ζ ^ 6 - ((3103 / 395) : ℂ) * ζ ^ 8 - ((2722 / 395) : ℂ) * ζ ^ 9 - ((636 / 79) : ℂ) * ζ ^ 11 - ((4413 / 790) : ℂ) * ζ ^ 12 - ((156 / 395) : ℂ) * ζ ^ 13 - ((353 / 79) : ℂ) * ζ ^ 15 - ((156 / 395) : ℂ) * ζ ^ 17 + ((1646 / 395) : ℂ) * ζ ^ 18 + ((1283 / 395) : ℂ) * ζ ^ 21 + ((6069 / 790) : ℂ) * ζ ^ 22 + ((1457 / 395) : ℂ) * ζ ^ 24 + ((2878 / 395) : ℂ) * ζ ^ 25 + ((353 / 79) : ℂ) * ζ ^ 27 + ((3103 / 395) : ℂ) * ζ ^ 28 + ((156 / 395) : ℂ) * ζ ^ 29 - ((1793 / 790) : ℂ) * ζ ^ 30 + ((636 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep03CoefficientIdentity00 :
    row18_reducedY32_combinationStep03Coefficient00 =
      row18_reducedY32_combinationStep02Coefficient00 +
        row18_reducedY32_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep03Coefficient00 row18_reducedY32_combinationStep02Coefficient00 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 (-((909 / 6241) : ℂ) + ((7057 / 37446) : ℂ) * ζ ^ 1 + ((96199 / 37446) : ℂ) * ζ ^ 2 - ((14279 / 18723) : ℂ) * ζ ^ 3 + ((12214 / 18723) : ℂ) * ζ ^ 4 + ((26173 / 18723) : ℂ) * ζ ^ 5 - ((11433 / 12482) : ℂ) * ζ ^ 6 + ((455 / 474) : ℂ) * ζ ^ 7 + ((36847 / 12482) : ℂ) * ζ ^ 8 - ((26899 / 37446) : ℂ) * ζ ^ 9 - ((50735 / 37446) : ℂ) * ζ ^ 10 - ((16849 / 37446) : ℂ) * ζ ^ 11 - ((20350 / 18723) : ℂ) * ζ ^ 12 - ((15236 / 18723) : ℂ) * ζ ^ 13 + ((20609 / 37446) : ℂ) * ζ ^ 14 - ((8053 / 18723) : ℂ) * ζ ^ 15 - ((3415 / 6241) : ℂ) * ζ ^ 16 - ((2443 / 6241) : ℂ) * ζ ^ 17 - ((11899 / 18723) : ℂ) * ζ ^ 18 - ((283 / 18723) : ℂ) * ζ ^ 19 + ((8162 / 18723) : ℂ) * ζ ^ 20 - ((13760 / 18723) : ℂ) * ζ ^ 21 + ((11209 / 37446) : ℂ) * ζ ^ 22 + ((34711 / 37446) : ℂ) * ζ ^ 23 - ((23339 / 18723) : ℂ) * ζ ^ 24 + ((10232 / 18723) : ℂ) * ζ ^ 25 + ((15713 / 12482) : ℂ) * ζ ^ 26 - ((69347 / 37446) : ℂ) * ζ ^ 27 + ((17929 / 37446) : ℂ) * ζ ^ 28 + ((11864 / 6241) : ℂ) * ζ ^ 29 + ((7415 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep03Coefficient01 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep03CoefficientIdentity01 :
    row18_reducedY32_combinationStep03Coefficient01 =
      row18_reducedY32_combinationStep02Coefficient01 +
        row18_reducedY32_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep03Coefficient01 row18_reducedY32_combinationStep02Coefficient01 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 (((57495 / 6241) : ℂ) - ((390943 / 37446) : ℂ) * ζ ^ 1 + ((202859 / 37446) : ℂ) * ζ ^ 2 + ((437083 / 37446) : ℂ) * ζ ^ 3 - ((81065 / 18723) : ℂ) * ζ ^ 4 + ((74744 / 18723) : ℂ) * ζ ^ 5 + ((73467 / 6241) : ℂ) * ζ ^ 6 - ((49 / 79) : ℂ) * ζ ^ 7 + ((65027 / 12482) : ℂ) * ζ ^ 8 + ((66704 / 6241) : ℂ) * ζ ^ 9 - ((19252 / 18723) : ℂ) * ζ ^ 10 + ((412453 / 37446) : ℂ) * ζ ^ 11 + ((388015 / 37446) : ℂ) * ζ ^ 12 - ((8722 / 6241) : ℂ) * ζ ^ 13 + ((63606 / 6241) : ℂ) * ζ ^ 14 + ((84461 / 12482) : ℂ) * ζ ^ 15 - ((23834 / 18723) : ℂ) * ζ ^ 16 + ((471481 / 37446) : ℂ) * ζ ^ 17 + ((82205 / 12482) : ℂ) * ζ ^ 18 - ((18803 / 6241) : ℂ) * ζ ^ 19 + ((45396 / 6241) : ℂ) * ζ ^ 20 + ((79831 / 12482) : ℂ) * ζ ^ 21 - ((32667 / 12482) : ℂ) * ζ ^ 22 + ((12818 / 6241) : ℂ) * ζ ^ 23 - ((5627 / 37446) : ℂ) * ζ ^ 24 - ((13691 / 6241) : ℂ) * ζ ^ 25 + ((85210 / 18723) : ℂ) * ζ ^ 26 - ((28790 / 18723) : ℂ) * ζ ^ 27 - ((27337 / 12482) : ℂ) * ζ ^ 28 - ((5932 / 6241) : ℂ) * ζ ^ 29 - ((20762 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep03Coefficient02 : ℂ :=
  (-((545 / 237) : ℂ) + ((307 / 79) : ℂ) * ζ ^ 1 + ((761 / 237) : ℂ) * ζ ^ 2 - ((1153 / 474) : ℂ) * ζ ^ 3 + ((2753 / 474) : ℂ) * ζ ^ 5 + ((867 / 158) : ℂ) * ζ ^ 8 - ((183 / 79) : ℂ) * ζ ^ 9 + ((2251 / 474) : ℂ) * ζ ^ 11 - ((421 / 474) : ℂ) * ζ ^ 12 - ((307 / 79) : ℂ) * ζ ^ 13 + ((121 / 237) : ℂ) * ζ ^ 15 - ((307 / 79) : ℂ) * ζ ^ 17 - ((761 / 237) : ℂ) * ζ ^ 18 - ((2995 / 474) : ℂ) * ζ ^ 21 - ((761 / 237) : ℂ) * ζ ^ 22 - ((1090 / 237) : ℂ) * ζ ^ 24 - ((911 / 474) : ℂ) * ζ ^ 25 - ((2995 / 474) : ℂ) * ζ ^ 27 - ((867 / 158) : ℂ) * ζ ^ 28 + ((307 / 79) : ℂ) * ζ ^ 29 - ((2189 / 474) : ℂ) * ζ ^ 30 - ((2251 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep03CoefficientIdentity02 :
    row18_reducedY32_combinationStep03Coefficient02 =
      row18_reducedY32_combinationStep02Coefficient02 +
        row18_reducedY32_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep03Coefficient02 row18_reducedY32_combinationStep02Coefficient02 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep03Coefficient03 : ℂ :=
  (((81 / 79) : ℂ) - ((86 / 79) : ℂ) * ζ ^ 1 + ((164 / 237) : ℂ) * ζ ^ 2 - ((62 / 237) : ℂ) * ζ ^ 5 - ((1 / 3) : ℂ) * ζ ^ 6 - ((1 / 3) : ℂ) * ζ ^ 8 - ((62 / 237) : ℂ) * ζ ^ 9 + ((85 / 158) : ℂ) * ζ ^ 11 + ((37 / 158) : ℂ) * ζ ^ 12 + ((86 / 79) : ℂ) * ζ ^ 13 + ((87 / 79) : ℂ) * ζ ^ 15 + ((86 / 79) : ℂ) * ζ ^ 17 + ((67 / 474) : ℂ) * ζ ^ 18 + ((160 / 237) : ℂ) * ζ ^ 21 - ((164 / 237) : ℂ) * ζ ^ 22 + ((91 / 474) : ℂ) * ζ ^ 24 - ((196 / 237) : ℂ) * ζ ^ 25 - ((87 / 79) : ℂ) * ζ ^ 27 + ((1 / 3) : ℂ) * ζ ^ 28 - ((86 / 79) : ℂ) * ζ ^ 29 - ((269 / 474) : ℂ) * ζ ^ 30 - ((85 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep03CoefficientIdentity03 :
    row18_reducedY32_combinationStep03Coefficient03 =
      row18_reducedY32_combinationStep02Coefficient03 +
        row18_reducedY32_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep03Coefficient03 row18_reducedY32_combinationStep02Coefficient03 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep03Coefficient04 : ℂ :=
  (-((235169 / 187230) : ℂ) + ((124691 / 187230) : ℂ) * ζ ^ 1 + ((541514 / 93615) : ℂ) * ζ ^ 2 + ((376451 / 62410) : ℂ) * ζ ^ 5 + ((439399 / 62410) : ℂ) * ζ ^ 6 + ((439399 / 62410) : ℂ) * ζ ^ 8 + ((376451 / 62410) : ℂ) * ζ ^ 9 + ((80731 / 12482) : ℂ) * ζ ^ 11 + ((449243 / 93615) : ℂ) * ζ ^ 12 - ((124691 / 187230) : ℂ) * ζ ^ 13 + ((32661 / 12482) : ℂ) * ζ ^ 15 - ((124691 / 187230) : ℂ) * ζ ^ 17 - ((225943 / 62410) : ℂ) * ζ ^ 18 - ((313511 / 93615) : ℂ) * ζ ^ 21 - ((541514 / 93615) : ℂ) * ζ ^ 22 - ((106728 / 31205) : ℂ) * ζ ^ 24 - ((502331 / 93615) : ℂ) * ζ ^ 25 - ((32661 / 12482) : ℂ) * ζ ^ 27 - ((439399 / 62410) : ℂ) * ζ ^ 28 + ((124691 / 187230) : ℂ) * ζ ^ 29 + ((419711 / 187230) : ℂ) * ζ ^ 30 - ((80731 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep03CoefficientIdentity04 :
    row18_reducedY32_combinationStep03Coefficient04 =
      row18_reducedY32_combinationStep02Coefficient04 +
        row18_reducedY32_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep03Coefficient04 row18_reducedY32_combinationStep02Coefficient04 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep03Coefficient05 : ℂ :=
  (-((6275 / 6241) : ℂ) + ((8668 / 18723) : ℂ) * ζ ^ 1 + ((99310 / 18723) : ℂ) * ζ ^ 2 - ((10079 / 6241) : ℂ) * ζ ^ 3 + ((32983 / 6241) : ℂ) * ζ ^ 5 + ((110611 / 37446) : ℂ) * ζ ^ 6 + ((32523 / 6241) : ℂ) * ζ ^ 8 + ((83725 / 37446) : ℂ) * ζ ^ 9 + ((32983 / 6241) : ℂ) * ζ ^ 11 + ((32523 / 12482) : ℂ) * ζ ^ 12 - ((8668 / 18723) : ℂ) * ζ ^ 13 + ((32279 / 12482) : ℂ) * ζ ^ 15 - ((8668 / 18723) : ℂ) * ζ ^ 17 - ((110611 / 37446) : ℂ) * ζ ^ 18 - ((22904 / 6241) : ℂ) * ζ ^ 21 - ((99310 / 18723) : ℂ) * ζ ^ 22 - ((26248 / 6241) : ℂ) * ζ ^ 24 - ((90281 / 18723) : ℂ) * ζ ^ 25 - ((90281 / 18723) : ℂ) * ζ ^ 27 - ((32523 / 6241) : ℂ) * ζ ^ 28 + ((8668 / 18723) : ℂ) * ζ ^ 29 - ((32983 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep03CoefficientIdentity05 :
    row18_reducedY32_combinationStep03Coefficient05 =
      row18_reducedY32_combinationStep02Coefficient05 +
        row18_reducedY32_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep03Coefficient05 row18_reducedY32_combinationStep02Coefficient05 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 (((5875 / 6241) : ℂ) - ((7028 / 18723) : ℂ) * ζ ^ 1 - ((99713 / 18723) : ℂ) * ζ ^ 2 + ((23902 / 18723) : ℂ) * ζ ^ 3 + ((45422 / 18723) : ℂ) * ζ ^ 4 - ((34650 / 6241) : ℂ) * ζ ^ 5 + ((13284 / 6241) : ℂ) * ζ ^ 6 + ((1243 / 474) : ℂ) * ζ ^ 7 - ((73822 / 18723) : ℂ) * ζ ^ 8 + ((95791 / 37446) : ℂ) * ζ ^ 9 + ((18755 / 37446) : ℂ) * ζ ^ 10 - ((125567 / 37446) : ℂ) * ζ ^ 11 + ((54670 / 18723) : ℂ) * ζ ^ 12 + ((2580 / 6241) : ℂ) * ζ ^ 13 - ((27354 / 6241) : ℂ) * ζ ^ 14 + ((66784 / 18723) : ℂ) * ζ ^ 15 + ((2227 / 18723) : ℂ) * ζ ^ 16 - ((105845 / 37446) : ℂ) * ζ ^ 17 + ((67894 / 18723) : ℂ) * ζ ^ 18 + ((5888 / 18723) : ℂ) * ζ ^ 19 - ((3903 / 6241) : ℂ) * ζ ^ 20 + ((22583 / 6241) : ℂ) * ζ ^ 21 + ((16903 / 37446) : ℂ) * ζ ^ 22 - ((1952 / 18723) : ℂ) * ζ ^ 23 + ((1777 / 6241) : ℂ) * ζ ^ 24 + ((10534 / 18723) : ℂ) * ζ ^ 25 - ((2313 / 12482) : ℂ) * ζ ^ 26 - ((9831 / 12482) : ℂ) * ζ ^ 27 + ((15053 / 37446) : ℂ) * ζ ^ 28 - ((11864 / 18723) : ℂ) * ζ ^ 29 + ((10381 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep03Coefficient06 : ℂ :=
  (((45866 / 18723) : ℂ) - ((30516 / 31205) : ℂ) * ζ ^ 1 + ((12945 / 12482) : ℂ) * ζ ^ 2 - ((35483 / 93615) : ℂ) * ζ ^ 3 + ((103007 / 187230) : ℂ) * ζ ^ 5 + ((6396 / 6241) : ℂ) * ζ ^ 6 + ((7421 / 37446) : ℂ) * ζ ^ 8 + ((57031 / 93615) : ℂ) * ζ ^ 9 + ((30838 / 31205) : ℂ) * ζ ^ 11 + ((7421 / 37446) : ℂ) * ζ ^ 12 + ((30516 / 31205) : ℂ) * ζ ^ 13 + ((119023 / 62410) : ℂ) * ζ ^ 15 + ((30516 / 31205) : ℂ) * ζ ^ 17 + ((153 / 12482) : ℂ) * ζ ^ 18 + ((127031 / 93615) : ℂ) * ζ ^ 21 - ((12945 / 12482) : ℂ) * ζ ^ 22 - ((286103 / 187230) : ℂ) * ζ ^ 25 - ((127031 / 93615) : ℂ) * ζ ^ 27 - ((7421 / 37446) : ℂ) * ζ ^ 28 - ((30516 / 31205) : ℂ) * ζ ^ 29 + ((3198 / 6241) : ℂ) * ζ ^ 30 - ((30838 / 31205) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep03CoefficientIdentity06 :
    row18_reducedY32_combinationStep03Coefficient06 =
      row18_reducedY32_combinationStep02Coefficient06 +
        row18_reducedY32_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep03Coefficient06 row18_reducedY32_combinationStep02Coefficient06 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep03Coefficient07 : ℂ :=
  (((1073 / 18723) : ℂ) + ((1037 / 37446) : ℂ) * ζ ^ 1 + ((15051 / 12482) : ℂ) * ζ ^ 2 + ((41971 / 37446) : ℂ) * ζ ^ 5 + ((43007 / 37446) : ℂ) * ζ ^ 6 + ((43007 / 37446) : ℂ) * ζ ^ 8 + ((41971 / 37446) : ℂ) * ζ ^ 9 + ((6521 / 6241) : ℂ) * ζ ^ 11 + ((10355 / 18723) : ℂ) * ζ ^ 12 - ((1037 / 37446) : ℂ) * ζ ^ 13 + ((9367 / 12482) : ℂ) * ζ ^ 15 - ((1037 / 37446) : ℂ) * ζ ^ 17 - ((12884 / 18723) : ℂ) * ζ ^ 18 - ((3584 / 6241) : ℂ) * ζ ^ 21 - ((15051 / 12482) : ℂ) * ζ ^ 22 - ((17239 / 37446) : ℂ) * ζ ^ 24 - ((20467 / 18723) : ℂ) * ζ ^ 25 - ((9367 / 12482) : ℂ) * ζ ^ 27 - ((43007 / 37446) : ℂ) * ζ ^ 28 + ((1037 / 37446) : ℂ) * ζ ^ 29 + ((22297 / 37446) : ℂ) * ζ ^ 30 - ((6521 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep03CoefficientIdentity07 :
    row18_reducedY32_combinationStep03Coefficient07 =
      row18_reducedY32_combinationStep02Coefficient07 +
        row18_reducedY32_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep03Coefficient07 row18_reducedY32_combinationStep02Coefficient07 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 (((909 / 6241) : ℂ) - ((7057 / 37446) : ℂ) * ζ ^ 1 - ((96199 / 37446) : ℂ) * ζ ^ 2 + ((14279 / 18723) : ℂ) * ζ ^ 3 - ((12214 / 18723) : ℂ) * ζ ^ 4 - ((26173 / 18723) : ℂ) * ζ ^ 5 + ((11433 / 12482) : ℂ) * ζ ^ 6 - ((455 / 474) : ℂ) * ζ ^ 7 - ((36847 / 12482) : ℂ) * ζ ^ 8 + ((26899 / 37446) : ℂ) * ζ ^ 9 + ((50735 / 37446) : ℂ) * ζ ^ 10 + ((16849 / 37446) : ℂ) * ζ ^ 11 + ((20350 / 18723) : ℂ) * ζ ^ 12 + ((15236 / 18723) : ℂ) * ζ ^ 13 - ((20609 / 37446) : ℂ) * ζ ^ 14 + ((8053 / 18723) : ℂ) * ζ ^ 15 + ((3415 / 6241) : ℂ) * ζ ^ 16 + ((2443 / 6241) : ℂ) * ζ ^ 17 + ((11899 / 18723) : ℂ) * ζ ^ 18 + ((283 / 18723) : ℂ) * ζ ^ 19 - ((8162 / 18723) : ℂ) * ζ ^ 20 + ((13760 / 18723) : ℂ) * ζ ^ 21 - ((11209 / 37446) : ℂ) * ζ ^ 22 - ((34711 / 37446) : ℂ) * ζ ^ 23 + ((23339 / 18723) : ℂ) * ζ ^ 24 - ((10232 / 18723) : ℂ) * ζ ^ 25 - ((15713 / 12482) : ℂ) * ζ ^ 26 + ((69347 / 37446) : ℂ) * ζ ^ 27 - ((17929 / 37446) : ℂ) * ζ ^ 28 - ((11864 / 6241) : ℂ) * ζ ^ 29 - ((7415 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep03CoefficientIdentity08 :
    row18_reducedY32_combinationStep03Coefficient08 =
      row18_reducedY32_combinationStep02Coefficient08 +
        row18_reducedY32_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep03Coefficient08 row18_reducedY32_combinationStep02Coefficient08 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep03CoefficientIdentity09 :
    row18_reducedY32_combinationStep03Coefficient09 =
      row18_reducedY32_combinationStep02Coefficient09 +
        row18_reducedY32_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep03Coefficient09 row18_reducedY32_combinationStep02Coefficient09 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep03CoefficientIdentity10 :
    row18_reducedY32_combinationStep03Coefficient10 =
      row18_reducedY32_combinationStep02Coefficient10 +
        row18_reducedY32_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep03Coefficient10 row18_reducedY32_combinationStep02Coefficient10 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep03CoefficientIdentity11 :
    row18_reducedY32_combinationStep03Coefficient11 =
      row18_reducedY32_combinationStep02Coefficient11 +
        row18_reducedY32_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep03Coefficient11 row18_reducedY32_combinationStep02Coefficient11 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep03CoefficientIdentity12 :
    row18_reducedY32_combinationStep03Coefficient12 =
      row18_reducedY32_combinationStep02Coefficient12 +
        row18_reducedY32_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep03Coefficient12 row18_reducedY32_combinationStep02Coefficient12 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep03CoefficientIdentity13 :
    row18_reducedY32_combinationStep03Coefficient13 =
      row18_reducedY32_combinationStep02Coefficient13 +
        row18_reducedY32_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep03Coefficient13 row18_reducedY32_combinationStep02Coefficient13 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep03CoefficientIdentity14 :
    row18_reducedY32_combinationStep03Coefficient14 =
      row18_reducedY32_combinationStep02Coefficient14 +
        row18_reducedY32_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep03Coefficient14 row18_reducedY32_combinationStep02Coefficient14 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep03CoefficientIdentity15 :
    row18_reducedY32_combinationStep03Coefficient15 =
      row18_reducedY32_combinationStep02Coefficient15 +
        row18_reducedY32_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep03Coefficient15 row18_reducedY32_combinationStep02Coefficient15 row18_reducedY32_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY32_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY32_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY32_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY32_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY32_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY32_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY32_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY32_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY32_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY32_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY32_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY32_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY32_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY32_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY32_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY32_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY32_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY32_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY32_combinationStep03CoefficientIdentity00,
      row18_reducedY32_combinationStep03CoefficientIdentity01,
      row18_reducedY32_combinationStep03CoefficientIdentity02,
      row18_reducedY32_combinationStep03CoefficientIdentity03,
      row18_reducedY32_combinationStep03CoefficientIdentity04,
      row18_reducedY32_combinationStep03CoefficientIdentity05,
      row18_reducedY32_combinationStep03CoefficientIdentity06,
      row18_reducedY32_combinationStep03CoefficientIdentity07,
      row18_reducedY32_combinationStep03CoefficientIdentity08,
      row18_reducedY32_combinationStep03CoefficientIdentity09,
      row18_reducedY32_combinationStep03CoefficientIdentity10,
      row18_reducedY32_combinationStep03CoefficientIdentity11,
      row18_reducedY32_combinationStep03CoefficientIdentity12,
      row18_reducedY32_combinationStep03CoefficientIdentity13,
      row18_reducedY32_combinationStep03CoefficientIdentity14,
      row18_reducedY32_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY32_combinationStep03Multiplier * equation

private def row18_reducedY32_combinationStep04Multiplier : ℂ :=
  (((364 / 395) : ℂ) - ((206 / 395) : ℂ) * ζ ^ 1 - ((1000 / 237) : ℂ) * ζ ^ 2 + ((938 / 1185) : ℂ) * ζ ^ 3 - ((58 / 395) : ℂ) * ζ ^ 5 + ((298 / 395) : ℂ) * ζ ^ 8 + ((1486 / 1185) : ℂ) * ζ ^ 9 - ((808 / 395) : ℂ) * ζ ^ 11 - ((1026 / 395) : ℂ) * ζ ^ 12 + ((206 / 395) : ℂ) * ζ ^ 13 - ((1382 / 1185) : ℂ) * ζ ^ 15 + ((206 / 395) : ℂ) * ζ ^ 17 + ((1000 / 237) : ℂ) * ζ ^ 18 + ((1556 / 1185) : ℂ) * ζ ^ 21 + ((1000 / 237) : ℂ) * ζ ^ 22 + ((728 / 395) : ℂ) * ζ ^ 24 - ((148 / 395) : ℂ) * ζ ^ 25 + ((1556 / 1185) : ℂ) * ζ ^ 27 - ((298 / 395) : ℂ) * ζ ^ 28 - ((206 / 395) : ℂ) * ζ ^ 29 - ((340 / 79) : ℂ) * ζ ^ 30 + ((808 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY32_combinationStep04Coefficient00 : ℂ :=
  (((137 / 790) : ℂ) + ((156 / 395) : ℂ) * ζ ^ 1 - ((6069 / 790) : ℂ) * ζ ^ 2 - ((2722 / 395) : ℂ) * ζ ^ 5 - ((3103 / 395) : ℂ) * ζ ^ 6 - ((3103 / 395) : ℂ) * ζ ^ 8 - ((2722 / 395) : ℂ) * ζ ^ 9 - ((636 / 79) : ℂ) * ζ ^ 11 - ((4413 / 790) : ℂ) * ζ ^ 12 - ((156 / 395) : ℂ) * ζ ^ 13 - ((353 / 79) : ℂ) * ζ ^ 15 - ((156 / 395) : ℂ) * ζ ^ 17 + ((1646 / 395) : ℂ) * ζ ^ 18 + ((1283 / 395) : ℂ) * ζ ^ 21 + ((6069 / 790) : ℂ) * ζ ^ 22 + ((1457 / 395) : ℂ) * ζ ^ 24 + ((2878 / 395) : ℂ) * ζ ^ 25 + ((353 / 79) : ℂ) * ζ ^ 27 + ((3103 / 395) : ℂ) * ζ ^ 28 + ((156 / 395) : ℂ) * ζ ^ 29 - ((1793 / 790) : ℂ) * ζ ^ 30 + ((636 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep04CoefficientIdentity00 :
    row18_reducedY32_combinationStep04Coefficient00 =
      row18_reducedY32_combinationStep03Coefficient00 +
        row18_reducedY32_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep04Coefficient00 row18_reducedY32_combinationStep03Coefficient00 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep04Coefficient01 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep04CoefficientIdentity01 :
    row18_reducedY32_combinationStep04Coefficient01 =
      row18_reducedY32_combinationStep03Coefficient01 +
        row18_reducedY32_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep04Coefficient01 row18_reducedY32_combinationStep03Coefficient01 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep04Coefficient02 : ℂ :=
  (-((326617 / 93615) : ℂ) + ((317231 / 93615) : ℂ) * ζ ^ 1 + ((77915 / 18723) : ℂ) * ζ ^ 2 - ((664147 / 187230) : ℂ) * ζ ^ 3 + ((565313 / 93615) : ℂ) * ζ ^ 5 + ((544766 / 93615) : ℂ) * ζ ^ 8 - ((241109 / 187230) : ℂ) * ζ ^ 9 + ((150876 / 31205) : ℂ) * ζ ^ 11 + ((36156 / 31205) : ℂ) * ζ ^ 12 - ((317231 / 93615) : ℂ) * ζ ^ 13 + ((167983 / 187230) : ℂ) * ζ ^ 15 - ((317231 / 93615) : ℂ) * ζ ^ 17 - ((77915 / 18723) : ℂ) * ζ ^ 18 - ((1298609 / 187230) : ℂ) * ζ ^ 21 - ((77915 / 18723) : ℂ) * ζ ^ 22 - ((653234 / 93615) : ℂ) * ζ ^ 24 - ((82694 / 31205) : ℂ) * ζ ^ 25 - ((1298609 / 187230) : ℂ) * ζ ^ 27 - ((544766 / 93615) : ℂ) * ζ ^ 28 + ((317231 / 93615) : ℂ) * ζ ^ 29 - ((54566 / 18723) : ℂ) * ζ ^ 30 - ((150876 / 31205) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep04CoefficientIdentity02 :
    row18_reducedY32_combinationStep04Coefficient02 =
      row18_reducedY32_combinationStep03Coefficient02 +
        row18_reducedY32_combinationStep04Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep04Coefficient02 row18_reducedY32_combinationStep03Coefficient02 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 (((36022 / 31205) : ℂ) + ((51421 / 93615) : ℂ) * ζ ^ 1 - ((65923 / 62410) : ℂ) * ζ ^ 2 + ((67647 / 62410) : ℂ) * ζ ^ 3 + ((303 / 62410) : ℂ) * ζ ^ 4 - ((100114 / 93615) : ℂ) * ζ ^ 5 + ((186149 / 187230) : ℂ) * ζ ^ 6 - ((69079 / 93615) : ℂ) * ζ ^ 7 + ((1441 / 12482) : ℂ) * ζ ^ 8 - ((28747 / 187230) : ℂ) * ζ ^ 9 - ((9937 / 6241) : ℂ) * ζ ^ 10 + ((23177 / 37446) : ℂ) * ζ ^ 11 - ((82142 / 93615) : ℂ) * ζ ^ 12 + ((8499 / 12482) : ℂ) * ζ ^ 13 + ((38029 / 62410) : ℂ) * ζ ^ 14 - ((3721 / 187230) : ℂ) * ζ ^ 15 + ((69827 / 31205) : ℂ) * ζ ^ 16 - ((103357 / 187230) : ℂ) * ζ ^ 17 + ((19141 / 187230) : ℂ) * ζ ^ 18 + ((1835 / 6241) : ℂ) * ζ ^ 19 - ((141506 / 93615) : ℂ) * ζ ^ 20 + ((4300 / 6241) : ℂ) * ζ ^ 21 - ((121753 / 187230) : ℂ) * ζ ^ 22 - ((18917 / 187230) : ℂ) * ζ ^ 23 + ((1816 / 93615) : ℂ) * ζ ^ 24 + ((7696 / 93615) : ℂ) * ζ ^ 25 + ((102683 / 187230) : ℂ) * ζ ^ 26 - ((11964 / 31205) : ℂ) * ζ ^ 27 + ((8301 / 31205) : ℂ) * ζ ^ 28 - ((9182 / 31205) : ℂ) * ζ ^ 29 + ((2828 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep04Coefficient03 : ℂ :=
  (-((1073 / 18723) : ℂ) - ((1037 / 37446) : ℂ) * ζ ^ 1 - ((15051 / 12482) : ℂ) * ζ ^ 2 - ((41971 / 37446) : ℂ) * ζ ^ 5 - ((43007 / 37446) : ℂ) * ζ ^ 6 - ((43007 / 37446) : ℂ) * ζ ^ 8 - ((41971 / 37446) : ℂ) * ζ ^ 9 - ((6521 / 6241) : ℂ) * ζ ^ 11 - ((10355 / 18723) : ℂ) * ζ ^ 12 + ((1037 / 37446) : ℂ) * ζ ^ 13 - ((9367 / 12482) : ℂ) * ζ ^ 15 + ((1037 / 37446) : ℂ) * ζ ^ 17 + ((12884 / 18723) : ℂ) * ζ ^ 18 + ((3584 / 6241) : ℂ) * ζ ^ 21 + ((15051 / 12482) : ℂ) * ζ ^ 22 + ((17239 / 37446) : ℂ) * ζ ^ 24 + ((20467 / 18723) : ℂ) * ζ ^ 25 + ((9367 / 12482) : ℂ) * ζ ^ 27 + ((43007 / 37446) : ℂ) * ζ ^ 28 - ((1037 / 37446) : ℂ) * ζ ^ 29 - ((22297 / 37446) : ℂ) * ζ ^ 30 + ((6521 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep04CoefficientIdentity03 :
    row18_reducedY32_combinationStep04Coefficient03 =
      row18_reducedY32_combinationStep03Coefficient03 +
        row18_reducedY32_combinationStep04Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep04Coefficient03 row18_reducedY32_combinationStep03Coefficient03 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 (((120187 / 93615) : ℂ) - ((133183 / 93615) : ℂ) * ζ ^ 1 + ((107002 / 93615) : ℂ) * ζ ^ 2 + ((1622 / 1185) : ℂ) * ζ ^ 3 - ((103591 / 62410) : ℂ) * ζ ^ 4 + ((104683 / 62410) : ℂ) * ζ ^ 5 + ((9021 / 62410) : ℂ) * ζ ^ 6 - ((22887 / 62410) : ℂ) * ζ ^ 7 + ((107263 / 93615) : ℂ) * ζ ^ 8 - ((5468 / 31205) : ℂ) * ζ ^ 9 + ((17987 / 37446) : ℂ) * ζ ^ 10 + ((36731 / 187230) : ℂ) * ζ ^ 11 + ((110084 / 93615) : ℂ) * ζ ^ 12 + ((80711 / 93615) : ℂ) * ζ ^ 13 + ((8879 / 37446) : ℂ) * ζ ^ 14 + ((152849 / 93615) : ℂ) * ζ ^ 15 - ((18181 / 31205) : ℂ) * ζ ^ 16 + ((104908 / 93615) : ℂ) * ζ ^ 17 + ((59849 / 93615) : ℂ) * ζ ^ 18 - ((220072 / 93615) : ℂ) * ζ ^ 19 + ((139024 / 93615) : ℂ) * ζ ^ 20 - ((64261 / 93615) : ℂ) * ζ ^ 21 - ((26669 / 187230) : ℂ) * ζ ^ 22 - ((5683 / 12482) : ℂ) * ζ ^ 23 + ((138383 / 187230) : ℂ) * ζ ^ 24 + ((1069 / 62410) : ℂ) * ζ ^ 25 - ((192719 / 187230) : ℂ) * ζ ^ 26 + ((96263 / 62410) : ℂ) * ζ ^ 27 - ((81579 / 62410) : ℂ) * ζ ^ 28 + ((5383 / 31205) : ℂ) * ζ ^ 29 + ((2626 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep04Coefficient04 : ℂ :=
  (-((137 / 790) : ℂ) - ((156 / 395) : ℂ) * ζ ^ 1 + ((6069 / 790) : ℂ) * ζ ^ 2 + ((2722 / 395) : ℂ) * ζ ^ 5 + ((3103 / 395) : ℂ) * ζ ^ 6 + ((3103 / 395) : ℂ) * ζ ^ 8 + ((2722 / 395) : ℂ) * ζ ^ 9 + ((636 / 79) : ℂ) * ζ ^ 11 + ((4413 / 790) : ℂ) * ζ ^ 12 + ((156 / 395) : ℂ) * ζ ^ 13 + ((353 / 79) : ℂ) * ζ ^ 15 + ((156 / 395) : ℂ) * ζ ^ 17 - ((1646 / 395) : ℂ) * ζ ^ 18 - ((1283 / 395) : ℂ) * ζ ^ 21 - ((6069 / 790) : ℂ) * ζ ^ 22 - ((1457 / 395) : ℂ) * ζ ^ 24 - ((2878 / 395) : ℂ) * ζ ^ 25 - ((353 / 79) : ℂ) * ζ ^ 27 - ((3103 / 395) : ℂ) * ζ ^ 28 - ((156 / 395) : ℂ) * ζ ^ 29 + ((1793 / 790) : ℂ) * ζ ^ 30 - ((636 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep04CoefficientIdentity04 :
    row18_reducedY32_combinationStep04Coefficient04 =
      row18_reducedY32_combinationStep03Coefficient04 +
        row18_reducedY32_combinationStep04Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep04Coefficient04 row18_reducedY32_combinationStep03Coefficient04 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 (-((120187 / 93615) : ℂ) + ((133183 / 93615) : ℂ) * ζ ^ 1 - ((107002 / 93615) : ℂ) * ζ ^ 2 - ((1622 / 1185) : ℂ) * ζ ^ 3 + ((103591 / 62410) : ℂ) * ζ ^ 4 - ((104683 / 62410) : ℂ) * ζ ^ 5 - ((9021 / 62410) : ℂ) * ζ ^ 6 + ((22887 / 62410) : ℂ) * ζ ^ 7 - ((107263 / 93615) : ℂ) * ζ ^ 8 + ((5468 / 31205) : ℂ) * ζ ^ 9 - ((17987 / 37446) : ℂ) * ζ ^ 10 - ((36731 / 187230) : ℂ) * ζ ^ 11 - ((110084 / 93615) : ℂ) * ζ ^ 12 - ((80711 / 93615) : ℂ) * ζ ^ 13 - ((8879 / 37446) : ℂ) * ζ ^ 14 - ((152849 / 93615) : ℂ) * ζ ^ 15 + ((18181 / 31205) : ℂ) * ζ ^ 16 - ((104908 / 93615) : ℂ) * ζ ^ 17 - ((59849 / 93615) : ℂ) * ζ ^ 18 + ((220072 / 93615) : ℂ) * ζ ^ 19 - ((139024 / 93615) : ℂ) * ζ ^ 20 + ((64261 / 93615) : ℂ) * ζ ^ 21 + ((26669 / 187230) : ℂ) * ζ ^ 22 + ((5683 / 12482) : ℂ) * ζ ^ 23 - ((138383 / 187230) : ℂ) * ζ ^ 24 - ((1069 / 62410) : ℂ) * ζ ^ 25 + ((192719 / 187230) : ℂ) * ζ ^ 26 - ((96263 / 62410) : ℂ) * ζ ^ 27 + ((81579 / 62410) : ℂ) * ζ ^ 28 - ((5383 / 31205) : ℂ) * ζ ^ 29 - ((2626 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep04Coefficient05 : ℂ :=
  (-((6275 / 6241) : ℂ) + ((8668 / 18723) : ℂ) * ζ ^ 1 + ((99310 / 18723) : ℂ) * ζ ^ 2 - ((10079 / 6241) : ℂ) * ζ ^ 3 + ((32983 / 6241) : ℂ) * ζ ^ 5 + ((110611 / 37446) : ℂ) * ζ ^ 6 + ((32523 / 6241) : ℂ) * ζ ^ 8 + ((83725 / 37446) : ℂ) * ζ ^ 9 + ((32983 / 6241) : ℂ) * ζ ^ 11 + ((32523 / 12482) : ℂ) * ζ ^ 12 - ((8668 / 18723) : ℂ) * ζ ^ 13 + ((32279 / 12482) : ℂ) * ζ ^ 15 - ((8668 / 18723) : ℂ) * ζ ^ 17 - ((110611 / 37446) : ℂ) * ζ ^ 18 - ((22904 / 6241) : ℂ) * ζ ^ 21 - ((99310 / 18723) : ℂ) * ζ ^ 22 - ((26248 / 6241) : ℂ) * ζ ^ 24 - ((90281 / 18723) : ℂ) * ζ ^ 25 - ((90281 / 18723) : ℂ) * ζ ^ 27 - ((32523 / 6241) : ℂ) * ζ ^ 28 + ((8668 / 18723) : ℂ) * ζ ^ 29 - ((32983 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep04CoefficientIdentity05 :
    row18_reducedY32_combinationStep04Coefficient05 =
      row18_reducedY32_combinationStep03Coefficient05 +
        row18_reducedY32_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep04Coefficient05 row18_reducedY32_combinationStep03Coefficient05 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep04Coefficient06 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY32_combinationStep04CoefficientIdentity06 :
    row18_reducedY32_combinationStep04Coefficient06 =
      row18_reducedY32_combinationStep03Coefficient06 +
        row18_reducedY32_combinationStep04Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep04Coefficient06 row18_reducedY32_combinationStep03Coefficient06 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 (((126979 / 93615) : ℂ) - ((6811 / 6241) : ℂ) * ζ ^ 1 + ((105217 / 93615) : ℂ) * ζ ^ 2 + ((48203 / 62410) : ℂ) * ζ ^ 3 + ((11336 / 31205) : ℂ) * ζ ^ 4 - ((2884 / 93615) : ℂ) * ζ ^ 5 + ((1760 / 6241) : ℂ) * ζ ^ 6 + ((56677 / 93615) : ℂ) * ζ ^ 7 - ((578 / 1185) : ℂ) * ζ ^ 8 + ((3179 / 62410) : ℂ) * ζ ^ 9 - ((50261 / 62410) : ℂ) * ζ ^ 10 + ((52931 / 31205) : ℂ) * ζ ^ 11 + ((105685 / 37446) : ℂ) * ζ ^ 12 + ((63928 / 93615) : ℂ) * ζ ^ 13 + ((281431 / 187230) : ℂ) * ζ ^ 14 - ((16018 / 31205) : ℂ) * ζ ^ 15 + ((543 / 6241) : ℂ) * ζ ^ 16 + ((83807 / 93615) : ℂ) * ζ ^ 17 - ((77707 / 62410) : ℂ) * ζ ^ 18 - ((25039 / 187230) : ℂ) * ζ ^ 19 - ((128212 / 93615) : ℂ) * ζ ^ 20 + ((212977 / 93615) : ℂ) * ζ ^ 21 + ((1288 / 31205) : ℂ) * ζ ^ 22 - ((71223 / 31205) : ℂ) * ζ ^ 23 - ((4208 / 31205) : ℂ) * ζ ^ 24 - ((124499 / 62410) : ℂ) * ζ ^ 25 + ((233501 / 187230) : ℂ) * ζ ^ 26 + ((25123 / 31205) : ℂ) * ζ ^ 27 + ((128 / 31205) : ℂ) * ζ ^ 28 + ((7052 / 31205) : ℂ) * ζ ^ 29 - ((5656 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep04Coefficient07 : ℂ :=
  (((1073 / 18723) : ℂ) + ((1037 / 37446) : ℂ) * ζ ^ 1 + ((15051 / 12482) : ℂ) * ζ ^ 2 + ((41971 / 37446) : ℂ) * ζ ^ 5 + ((43007 / 37446) : ℂ) * ζ ^ 6 + ((43007 / 37446) : ℂ) * ζ ^ 8 + ((41971 / 37446) : ℂ) * ζ ^ 9 + ((6521 / 6241) : ℂ) * ζ ^ 11 + ((10355 / 18723) : ℂ) * ζ ^ 12 - ((1037 / 37446) : ℂ) * ζ ^ 13 + ((9367 / 12482) : ℂ) * ζ ^ 15 - ((1037 / 37446) : ℂ) * ζ ^ 17 - ((12884 / 18723) : ℂ) * ζ ^ 18 - ((3584 / 6241) : ℂ) * ζ ^ 21 - ((15051 / 12482) : ℂ) * ζ ^ 22 - ((17239 / 37446) : ℂ) * ζ ^ 24 - ((20467 / 18723) : ℂ) * ζ ^ 25 - ((9367 / 12482) : ℂ) * ζ ^ 27 - ((43007 / 37446) : ℂ) * ζ ^ 28 + ((1037 / 37446) : ℂ) * ζ ^ 29 + ((22297 / 37446) : ℂ) * ζ ^ 30 - ((6521 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep04CoefficientIdentity07 :
    row18_reducedY32_combinationStep04Coefficient07 =
      row18_reducedY32_combinationStep03Coefficient07 +
        row18_reducedY32_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep04Coefficient07 row18_reducedY32_combinationStep03Coefficient07 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep04Coefficient08 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep04CoefficientIdentity08 :
    row18_reducedY32_combinationStep04Coefficient08 =
      row18_reducedY32_combinationStep03Coefficient08 +
        row18_reducedY32_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep04Coefficient08 row18_reducedY32_combinationStep03Coefficient08 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep04Coefficient09 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep04CoefficientIdentity09 :
    row18_reducedY32_combinationStep04Coefficient09 =
      row18_reducedY32_combinationStep03Coefficient09 +
        row18_reducedY32_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep04Coefficient09 row18_reducedY32_combinationStep03Coefficient09 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep04Coefficient10 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep04CoefficientIdentity10 :
    row18_reducedY32_combinationStep04Coefficient10 =
      row18_reducedY32_combinationStep03Coefficient10 +
        row18_reducedY32_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep04Coefficient10 row18_reducedY32_combinationStep03Coefficient10 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep04Coefficient11 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep04CoefficientIdentity11 :
    row18_reducedY32_combinationStep04Coefficient11 =
      row18_reducedY32_combinationStep03Coefficient11 +
        row18_reducedY32_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep04Coefficient11 row18_reducedY32_combinationStep03Coefficient11 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep04Coefficient12 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep04CoefficientIdentity12 :
    row18_reducedY32_combinationStep04Coefficient12 =
      row18_reducedY32_combinationStep03Coefficient12 +
        row18_reducedY32_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep04Coefficient12 row18_reducedY32_combinationStep03Coefficient12 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep04Coefficient13 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep04CoefficientIdentity13 :
    row18_reducedY32_combinationStep04Coefficient13 =
      row18_reducedY32_combinationStep03Coefficient13 +
        row18_reducedY32_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep04Coefficient13 row18_reducedY32_combinationStep03Coefficient13 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep04Coefficient14 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep04CoefficientIdentity14 :
    row18_reducedY32_combinationStep04Coefficient14 =
      row18_reducedY32_combinationStep03Coefficient14 +
        row18_reducedY32_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep04Coefficient14 row18_reducedY32_combinationStep03Coefficient14 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep04Coefficient15 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep04CoefficientIdentity15 :
    row18_reducedY32_combinationStep04Coefficient15 =
      row18_reducedY32_combinationStep03Coefficient15 +
        row18_reducedY32_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep04Coefficient15 row18_reducedY32_combinationStep03Coefficient15 row18_reducedY32_combinationStep04Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY32_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY32_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY32_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY32_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY32_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY32_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY32_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY32_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY32_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY32_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY32_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY32_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY32_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY32_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY32_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY32_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY32_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY32_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY32_combinationStep04CoefficientIdentity00,
      row18_reducedY32_combinationStep04CoefficientIdentity01,
      row18_reducedY32_combinationStep04CoefficientIdentity02,
      row18_reducedY32_combinationStep04CoefficientIdentity03,
      row18_reducedY32_combinationStep04CoefficientIdentity04,
      row18_reducedY32_combinationStep04CoefficientIdentity05,
      row18_reducedY32_combinationStep04CoefficientIdentity06,
      row18_reducedY32_combinationStep04CoefficientIdentity07,
      row18_reducedY32_combinationStep04CoefficientIdentity08,
      row18_reducedY32_combinationStep04CoefficientIdentity09,
      row18_reducedY32_combinationStep04CoefficientIdentity10,
      row18_reducedY32_combinationStep04CoefficientIdentity11,
      row18_reducedY32_combinationStep04CoefficientIdentity12,
      row18_reducedY32_combinationStep04CoefficientIdentity13,
      row18_reducedY32_combinationStep04CoefficientIdentity14,
      row18_reducedY32_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY32_combinationStep04Multiplier * equation

private def row18_reducedY32_combinationStep05Multiplier : ℂ :=
  (((194 / 237) : ℂ) - ((16 / 79) : ℂ) * ζ ^ 1 + ((76 / 237) : ℂ) * ζ ^ 2 + ((52 / 237) : ℂ) * ζ ^ 3 - ((16 / 79) : ℂ) * ζ ^ 5 + ((90 / 79) : ℂ) * ζ ^ 6 - ((90 / 79) : ℂ) * ζ ^ 8 + ((16 / 79) : ℂ) * ζ ^ 9 - ((26 / 237) : ℂ) * ζ ^ 11 + ((8 / 237) : ℂ) * ζ ^ 12 + ((16 / 79) : ℂ) * ζ ^ 13 + ((122 / 237) : ℂ) * ζ ^ 15 + ((16 / 79) : ℂ) * ζ ^ 17 + ((4 / 79) : ℂ) * ζ ^ 18 + ((6 / 79) : ℂ) * ζ ^ 21 - ((76 / 237) : ℂ) * ζ ^ 22 + ((94 / 79) : ℂ) * ζ ^ 24 + ((58 / 79) : ℂ) * ζ ^ 27 + ((90 / 79) : ℂ) * ζ ^ 28 - ((16 / 79) : ℂ) * ζ ^ 29 + ((278 / 237) : ℂ) * ζ ^ 30 + ((26 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY32_combinationStep05Coefficient00 : ℂ :=
  (((137 / 790) : ℂ) + ((156 / 395) : ℂ) * ζ ^ 1 - ((6069 / 790) : ℂ) * ζ ^ 2 - ((2722 / 395) : ℂ) * ζ ^ 5 - ((3103 / 395) : ℂ) * ζ ^ 6 - ((3103 / 395) : ℂ) * ζ ^ 8 - ((2722 / 395) : ℂ) * ζ ^ 9 - ((636 / 79) : ℂ) * ζ ^ 11 - ((4413 / 790) : ℂ) * ζ ^ 12 - ((156 / 395) : ℂ) * ζ ^ 13 - ((353 / 79) : ℂ) * ζ ^ 15 - ((156 / 395) : ℂ) * ζ ^ 17 + ((1646 / 395) : ℂ) * ζ ^ 18 + ((1283 / 395) : ℂ) * ζ ^ 21 + ((6069 / 790) : ℂ) * ζ ^ 22 + ((1457 / 395) : ℂ) * ζ ^ 24 + ((2878 / 395) : ℂ) * ζ ^ 25 + ((353 / 79) : ℂ) * ζ ^ 27 + ((3103 / 395) : ℂ) * ζ ^ 28 + ((156 / 395) : ℂ) * ζ ^ 29 - ((1793 / 790) : ℂ) * ζ ^ 30 + ((636 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep05CoefficientIdentity00 :
    row18_reducedY32_combinationStep05Coefficient00 =
      row18_reducedY32_combinationStep04Coefficient00 +
        row18_reducedY32_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep05Coefficient00 row18_reducedY32_combinationStep04Coefficient00 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep05Coefficient01 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep05CoefficientIdentity01 :
    row18_reducedY32_combinationStep05Coefficient01 =
      row18_reducedY32_combinationStep04Coefficient01 +
        row18_reducedY32_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep05Coefficient01 row18_reducedY32_combinationStep04Coefficient01 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep05Coefficient02 : ℂ :=
  (-((1421 / 395) : ℂ) + ((1288 / 395) : ℂ) * ζ ^ 1 + ((623 / 158) : ℂ) * ζ ^ 2 - ((3071 / 790) : ℂ) * ζ ^ 3 + ((4993 / 790) : ℂ) * ζ ^ 5 + ((4601 / 790) : ℂ) * ζ ^ 8 - ((897 / 790) : ℂ) * ζ ^ 9 + ((1984 / 395) : ℂ) * ζ ^ 11 + ((1083 / 790) : ℂ) * ζ ^ 12 - ((1288 / 395) : ℂ) * ζ ^ 13 + ((327 / 395) : ℂ) * ζ ^ 15 - ((1288 / 395) : ℂ) * ζ ^ 17 - ((623 / 158) : ℂ) * ζ ^ 18 - ((5647 / 790) : ℂ) * ζ ^ 21 - ((623 / 158) : ℂ) * ζ ^ 22 - ((2842 / 395) : ℂ) * ζ ^ 24 - ((2417 / 790) : ℂ) * ζ ^ 25 - ((5647 / 790) : ℂ) * ζ ^ 27 - ((4601 / 790) : ℂ) * ζ ^ 28 + ((1288 / 395) : ℂ) * ζ ^ 29 - ((225 / 79) : ℂ) * ζ ^ 30 - ((1984 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep05CoefficientIdentity02 :
    row18_reducedY32_combinationStep05Coefficient02 =
      row18_reducedY32_combinationStep04Coefficient02 +
        row18_reducedY32_combinationStep05Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep05Coefficient02 row18_reducedY32_combinationStep04Coefficient02 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 (((3875 / 18723) : ℂ) + ((2617 / 37446) : ℂ) * ζ ^ 1 + ((5501 / 18723) : ℂ) * ζ ^ 2 + ((1773 / 6241) : ℂ) * ζ ^ 3 - ((3547 / 18723) : ℂ) * ζ ^ 4 - ((7349 / 18723) : ℂ) * ζ ^ 5 - ((481 / 6241) : ℂ) * ζ ^ 6 - ((4491 / 12482) : ℂ) * ζ ^ 7 - ((587 / 37446) : ℂ) * ζ ^ 8 + ((2573 / 37446) : ℂ) * ζ ^ 9 + ((863 / 37446) : ℂ) * ζ ^ 10 + ((894 / 6241) : ℂ) * ζ ^ 11 + ((2206 / 18723) : ℂ) * ζ ^ 12 - ((667 / 18723) : ℂ) * ζ ^ 13 + ((298 / 18723) : ℂ) * ζ ^ 14 - ((1403 / 37446) : ℂ) * ζ ^ 15 + ((1697 / 18723) : ℂ) * ζ ^ 16 - ((1325 / 18723) : ℂ) * ζ ^ 17 + ((389 / 37446) : ℂ) * ζ ^ 18 - ((29 / 12482) : ℂ) * ζ ^ 19 - ((1892 / 18723) : ℂ) * ζ ^ 20 - ((436 / 18723) : ℂ) * ζ ^ 21 - ((10 / 79) : ℂ) * ζ ^ 22 + ((882 / 6241) : ℂ) * ζ ^ 23 + ((2131 / 6241) : ℂ) * ζ ^ 24 - ((851 / 12482) : ℂ) * ζ ^ 25 + ((559 / 18723) : ℂ) * ζ ^ 26 - ((1913 / 37446) : ℂ) * ζ ^ 27 - ((6481 / 37446) : ℂ) * ζ ^ 28 - ((903 / 12482) : ℂ) * ζ ^ 29 - ((65 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep05Coefficient03 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep05CoefficientIdentity03 :
    row18_reducedY32_combinationStep05Coefficient03 =
      row18_reducedY32_combinationStep04Coefficient03 +
        row18_reducedY32_combinationStep05Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep05Coefficient03 row18_reducedY32_combinationStep04Coefficient03 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 (((479 / 18723) : ℂ) + ((1862 / 18723) : ℂ) * ζ ^ 1 - ((5142 / 6241) : ℂ) * ζ ^ 2 - ((8047 / 37446) : ℂ) * ζ ^ 3 + ((1339 / 6241) : ℂ) * ζ ^ 4 - ((12003 / 12482) : ℂ) * ζ ^ 5 - ((4519 / 12482) : ℂ) * ζ ^ 6 + ((7945 / 18723) : ℂ) * ζ ^ 7 - ((16007 / 18723) : ℂ) * ζ ^ 8 - ((12811 / 37446) : ℂ) * ζ ^ 9 - ((1753 / 6241) : ℂ) * ζ ^ 10 - ((27269 / 37446) : ℂ) * ζ ^ 11 + ((8159 / 37446) : ℂ) * ζ ^ 12 - ((276 / 6241) : ℂ) * ζ ^ 13 - ((6831 / 12482) : ℂ) * ζ ^ 14 + ((5245 / 18723) : ℂ) * ζ ^ 15 + ((189 / 6241) : ℂ) * ζ ^ 16 - ((40499 / 37446) : ℂ) * ζ ^ 17 - ((2369 / 6241) : ℂ) * ζ ^ 18 - ((539 / 18723) : ℂ) * ζ ^ 19 - ((22205 / 37446) : ℂ) * ζ ^ 20 + ((5650 / 18723) : ℂ) * ζ ^ 21 - ((1132 / 18723) : ℂ) * ζ ^ 22 - ((14624 / 18723) : ℂ) * ζ ^ 23 + ((5857 / 37446) : ℂ) * ζ ^ 24 - ((4445 / 12482) : ℂ) * ζ ^ 25 + ((645 / 6241) : ℂ) * ζ ^ 26 + ((3761 / 12482) : ℂ) * ζ ^ 27 + ((1135 / 12482) : ℂ) * ζ ^ 28 + ((2102 / 18723) : ℂ) * ζ ^ 29 + ((182 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep05Coefficient04 : ℂ :=
  (-((137 / 790) : ℂ) - ((156 / 395) : ℂ) * ζ ^ 1 + ((6069 / 790) : ℂ) * ζ ^ 2 + ((2722 / 395) : ℂ) * ζ ^ 5 + ((3103 / 395) : ℂ) * ζ ^ 6 + ((3103 / 395) : ℂ) * ζ ^ 8 + ((2722 / 395) : ℂ) * ζ ^ 9 + ((636 / 79) : ℂ) * ζ ^ 11 + ((4413 / 790) : ℂ) * ζ ^ 12 + ((156 / 395) : ℂ) * ζ ^ 13 + ((353 / 79) : ℂ) * ζ ^ 15 + ((156 / 395) : ℂ) * ζ ^ 17 - ((1646 / 395) : ℂ) * ζ ^ 18 - ((1283 / 395) : ℂ) * ζ ^ 21 - ((6069 / 790) : ℂ) * ζ ^ 22 - ((1457 / 395) : ℂ) * ζ ^ 24 - ((2878 / 395) : ℂ) * ζ ^ 25 - ((353 / 79) : ℂ) * ζ ^ 27 - ((3103 / 395) : ℂ) * ζ ^ 28 - ((156 / 395) : ℂ) * ζ ^ 29 + ((1793 / 790) : ℂ) * ζ ^ 30 - ((636 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep05CoefficientIdentity04 :
    row18_reducedY32_combinationStep05Coefficient04 =
      row18_reducedY32_combinationStep04Coefficient04 +
        row18_reducedY32_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep05Coefficient04 row18_reducedY32_combinationStep04Coefficient04 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep05Coefficient05 : ℂ :=
  (-((227 / 158) : ℂ) + ((46 / 79) : ℂ) * ζ ^ 1 + ((524 / 79) : ℂ) * ζ ^ 2 - ((335 / 158) : ℂ) * ζ ^ 3 + ((1071 / 158) : ℂ) * ζ ^ 5 + ((609 / 158) : ℂ) * ζ ^ 6 + ((559 / 79) : ℂ) * ζ ^ 8 + ((491 / 158) : ℂ) * ζ ^ 9 + ((1071 / 158) : ℂ) * ζ ^ 11 + ((559 / 158) : ℂ) * ζ ^ 12 - ((46 / 79) : ℂ) * ζ ^ 13 + ((244 / 79) : ℂ) * ζ ^ 15 - ((46 / 79) : ℂ) * ζ ^ 17 - ((609 / 158) : ℂ) * ζ ^ 18 - ((368 / 79) : ℂ) * ζ ^ 21 - ((524 / 79) : ℂ) * ζ ^ 22 - ((891 / 158) : ℂ) * ζ ^ 24 - ((979 / 158) : ℂ) * ζ ^ 25 - ((979 / 158) : ℂ) * ζ ^ 27 - ((559 / 79) : ℂ) * ζ ^ 28 + ((46 / 79) : ℂ) * ζ ^ 29 - ((1071 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY32_combinationStep05CoefficientIdentity05 :
    row18_reducedY32_combinationStep05Coefficient05 =
      row18_reducedY32_combinationStep04Coefficient05 +
        row18_reducedY32_combinationStep05Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep05Coefficient05 row18_reducedY32_combinationStep04Coefficient05 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 (((1576 / 6241) : ℂ) + ((1811 / 12482) : ℂ) * ζ ^ 1 - ((55291 / 37446) : ℂ) * ζ ^ 2 + ((6017 / 12482) : ℂ) * ζ ^ 3 - ((3482 / 18723) : ℂ) * ζ ^ 4 - ((17561 / 12482) : ℂ) * ζ ^ 5 - ((34 / 18723) : ℂ) * ζ ^ 6 - ((629 / 18723) : ℂ) * ζ ^ 7 - ((7888 / 6241) : ℂ) * ζ ^ 8 - ((2915 / 12482) : ℂ) * ζ ^ 9 + ((6287 / 37446) : ℂ) * ζ ^ 10 - ((6179 / 6241) : ℂ) * ζ ^ 11 + ((3047 / 12482) : ℂ) * ζ ^ 12 - ((1409 / 12482) : ℂ) * ζ ^ 13 - ((15403 / 18723) : ℂ) * ζ ^ 14 + ((8785 / 18723) : ℂ) * ζ ^ 15 - ((5559 / 12482) : ℂ) * ζ ^ 16 - ((32441 / 37446) : ℂ) * ζ ^ 17 + ((2118 / 6241) : ℂ) * ζ ^ 18 - ((18845 / 37446) : ℂ) * ζ ^ 19 - ((29363 / 37446) : ℂ) * ζ ^ 20 + ((901 / 6241) : ℂ) * ζ ^ 21 - ((3613 / 37446) : ℂ) * ζ ^ 22 - ((3598 / 6241) : ℂ) * ζ ^ 23 + ((1573 / 18723) : ℂ) * ζ ^ 24 + ((5023 / 18723) : ℂ) * ζ ^ 25 - ((10619 / 18723) : ℂ) * ζ ^ 26 + ((5171 / 18723) : ℂ) * ζ ^ 27 - ((6089 / 37446) : ℂ) * ζ ^ 28 - ((2509 / 37446) : ℂ) * ζ ^ 29 - ((169 / 37446) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep05Coefficient06 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY32_combinationStep05CoefficientIdentity06 :
    row18_reducedY32_combinationStep05Coefficient06 =
      row18_reducedY32_combinationStep04Coefficient06 +
        row18_reducedY32_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep05Coefficient06 row18_reducedY32_combinationStep04Coefficient06 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep05Coefficient07 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep05CoefficientIdentity07 :
    row18_reducedY32_combinationStep05Coefficient07 =
      row18_reducedY32_combinationStep04Coefficient07 +
        row18_reducedY32_combinationStep05Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep05Coefficient07 row18_reducedY32_combinationStep04Coefficient07 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 (-((479 / 18723) : ℂ) - ((1862 / 18723) : ℂ) * ζ ^ 1 + ((5142 / 6241) : ℂ) * ζ ^ 2 + ((8047 / 37446) : ℂ) * ζ ^ 3 - ((1339 / 6241) : ℂ) * ζ ^ 4 + ((12003 / 12482) : ℂ) * ζ ^ 5 + ((4519 / 12482) : ℂ) * ζ ^ 6 - ((7945 / 18723) : ℂ) * ζ ^ 7 + ((16007 / 18723) : ℂ) * ζ ^ 8 + ((12811 / 37446) : ℂ) * ζ ^ 9 + ((1753 / 6241) : ℂ) * ζ ^ 10 + ((27269 / 37446) : ℂ) * ζ ^ 11 - ((8159 / 37446) : ℂ) * ζ ^ 12 + ((276 / 6241) : ℂ) * ζ ^ 13 + ((6831 / 12482) : ℂ) * ζ ^ 14 - ((5245 / 18723) : ℂ) * ζ ^ 15 - ((189 / 6241) : ℂ) * ζ ^ 16 + ((40499 / 37446) : ℂ) * ζ ^ 17 + ((2369 / 6241) : ℂ) * ζ ^ 18 + ((539 / 18723) : ℂ) * ζ ^ 19 + ((22205 / 37446) : ℂ) * ζ ^ 20 - ((5650 / 18723) : ℂ) * ζ ^ 21 + ((1132 / 18723) : ℂ) * ζ ^ 22 + ((14624 / 18723) : ℂ) * ζ ^ 23 - ((5857 / 37446) : ℂ) * ζ ^ 24 + ((4445 / 12482) : ℂ) * ζ ^ 25 - ((645 / 6241) : ℂ) * ζ ^ 26 - ((3761 / 12482) : ℂ) * ζ ^ 27 - ((1135 / 12482) : ℂ) * ζ ^ 28 - ((2102 / 18723) : ℂ) * ζ ^ 29 - ((182 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep05Coefficient08 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep05CoefficientIdentity08 :
    row18_reducedY32_combinationStep05Coefficient08 =
      row18_reducedY32_combinationStep04Coefficient08 +
        row18_reducedY32_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep05Coefficient08 row18_reducedY32_combinationStep04Coefficient08 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep05Coefficient09 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep05CoefficientIdentity09 :
    row18_reducedY32_combinationStep05Coefficient09 =
      row18_reducedY32_combinationStep04Coefficient09 +
        row18_reducedY32_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep05Coefficient09 row18_reducedY32_combinationStep04Coefficient09 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep05Coefficient10 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep05CoefficientIdentity10 :
    row18_reducedY32_combinationStep05Coefficient10 =
      row18_reducedY32_combinationStep04Coefficient10 +
        row18_reducedY32_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep05Coefficient10 row18_reducedY32_combinationStep04Coefficient10 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep05Coefficient11 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep05CoefficientIdentity11 :
    row18_reducedY32_combinationStep05Coefficient11 =
      row18_reducedY32_combinationStep04Coefficient11 +
        row18_reducedY32_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep05Coefficient11 row18_reducedY32_combinationStep04Coefficient11 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep05Coefficient12 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep05CoefficientIdentity12 :
    row18_reducedY32_combinationStep05Coefficient12 =
      row18_reducedY32_combinationStep04Coefficient12 +
        row18_reducedY32_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep05Coefficient12 row18_reducedY32_combinationStep04Coefficient12 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep05Coefficient13 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep05CoefficientIdentity13 :
    row18_reducedY32_combinationStep05Coefficient13 =
      row18_reducedY32_combinationStep04Coefficient13 +
        row18_reducedY32_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep05Coefficient13 row18_reducedY32_combinationStep04Coefficient13 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep05Coefficient14 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep05CoefficientIdentity14 :
    row18_reducedY32_combinationStep05Coefficient14 =
      row18_reducedY32_combinationStep04Coefficient14 +
        row18_reducedY32_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep05Coefficient14 row18_reducedY32_combinationStep04Coefficient14 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep05Coefficient15 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep05CoefficientIdentity15 :
    row18_reducedY32_combinationStep05Coefficient15 =
      row18_reducedY32_combinationStep04Coefficient15 +
        row18_reducedY32_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep05Coefficient15 row18_reducedY32_combinationStep04Coefficient15 row18_reducedY32_combinationStep05Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY32_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY32_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY32_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY32_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY32_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY32_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY32_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY32_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY32_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY32_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY32_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY32_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY32_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY32_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY32_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY32_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY32_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY32_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY32_combinationStep05CoefficientIdentity00,
      row18_reducedY32_combinationStep05CoefficientIdentity01,
      row18_reducedY32_combinationStep05CoefficientIdentity02,
      row18_reducedY32_combinationStep05CoefficientIdentity03,
      row18_reducedY32_combinationStep05CoefficientIdentity04,
      row18_reducedY32_combinationStep05CoefficientIdentity05,
      row18_reducedY32_combinationStep05CoefficientIdentity06,
      row18_reducedY32_combinationStep05CoefficientIdentity07,
      row18_reducedY32_combinationStep05CoefficientIdentity08,
      row18_reducedY32_combinationStep05CoefficientIdentity09,
      row18_reducedY32_combinationStep05CoefficientIdentity10,
      row18_reducedY32_combinationStep05CoefficientIdentity11,
      row18_reducedY32_combinationStep05CoefficientIdentity12,
      row18_reducedY32_combinationStep05CoefficientIdentity13,
      row18_reducedY32_combinationStep05CoefficientIdentity14,
      row18_reducedY32_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY32_combinationStep05Multiplier * equation

private def row18_reducedY32_combinationStep06Multiplier : ℂ :=
  (((336 / 395) : ℂ) + ((538 / 395) : ℂ) * ζ ^ 1 - ((5912 / 395) : ℂ) * ζ ^ 2 - ((5326 / 395) : ℂ) * ζ ^ 5 - ((6248 / 395) : ℂ) * ζ ^ 6 - ((6248 / 395) : ℂ) * ζ ^ 8 - ((5326 / 395) : ℂ) * ζ ^ 9 - ((1294 / 79) : ℂ) * ζ ^ 11 - ((4284 / 395) : ℂ) * ζ ^ 12 - ((538 / 395) : ℂ) * ζ ^ 13 - ((554 / 79) : ℂ) * ζ ^ 15 - ((538 / 395) : ℂ) * ζ ^ 17 + ((3576 / 395) : ℂ) * ζ ^ 18 + ((2394 / 395) : ℂ) * ζ ^ 21 + ((5912 / 395) : ℂ) * ζ ^ 22 + ((2672 / 395) : ℂ) * ζ ^ 24 + ((5864 / 395) : ℂ) * ζ ^ 25 + ((554 / 79) : ℂ) * ζ ^ 27 + ((6248 / 395) : ℂ) * ζ ^ 28 + ((538 / 395) : ℂ) * ζ ^ 29 - ((1964 / 395) : ℂ) * ζ ^ 30 + ((1294 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY32_combinationStep06Coefficient00 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity00 :
    row18_reducedY32_combinationStep06Coefficient00 =
      row18_reducedY32_combinationStep05Coefficient00 +
        row18_reducedY32_combinationStep06Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep06Coefficient00 row18_reducedY32_combinationStep05Coefficient00 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 (((12839 / 62410) : ℂ) + ((13014 / 31205) : ℂ) * ζ ^ 1 - ((266081 / 31205) : ℂ) * ζ ^ 2 + ((9483 / 62410) : ℂ) * ζ ^ 3 + ((119076 / 31205) : ℂ) * ζ ^ 4 - ((245072 / 31205) : ℂ) * ζ ^ 5 + ((20247 / 62410) : ℂ) * ζ ^ 6 + ((165654 / 31205) : ℂ) * ζ ^ 7 - ((408999 / 62410) : ℂ) * ζ ^ 8 + ((58369 / 62410) : ℂ) * ζ ^ 9 + ((461433 / 62410) : ℂ) * ζ ^ 10 - ((500229 / 62410) : ℂ) * ζ ^ 11 + ((183609 / 62410) : ℂ) * ζ ^ 12 + ((188147 / 31205) : ℂ) * ζ ^ 13 - ((444333 / 62410) : ℂ) * ζ ^ 14 + ((248293 / 62410) : ℂ) * ζ ^ 15 + ((123576 / 31205) : ℂ) * ζ ^ 16 - ((425663 / 62410) : ℂ) * ζ ^ 17 + ((334383 / 62410) : ℂ) * ζ ^ 18 + ((18531 / 12482) : ℂ) * ζ ^ 19 - ((102873 / 31205) : ℂ) * ζ ^ 20 + ((189092 / 31205) : ℂ) * ζ ^ 21 + ((17548 / 31205) : ℂ) * ζ ^ 22 - ((74637 / 31205) : ℂ) * ζ ^ 23 + ((134933 / 62410) : ℂ) * ζ ^ 24 + ((2687 / 62410) : ℂ) * ζ ^ 25 - ((100233 / 62410) : ℂ) * ζ ^ 26 + ((75987 / 62410) : ℂ) * ζ ^ 27 - ((23639 / 62410) : ℂ) * ζ ^ 28 - ((19006 / 31205) : ℂ) * ζ ^ 29 - ((4529 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep06Coefficient01 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity01 :
    row18_reducedY32_combinationStep06Coefficient01 =
      row18_reducedY32_combinationStep05Coefficient01 +
        row18_reducedY32_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep06Coefficient01 row18_reducedY32_combinationStep05Coefficient01 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep06Coefficient02 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity02 :
    row18_reducedY32_combinationStep06Coefficient02 =
      row18_reducedY32_combinationStep05Coefficient02 +
        row18_reducedY32_combinationStep06Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep06Coefficient02 row18_reducedY32_combinationStep05Coefficient02 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 (-((115451 / 31205) : ℂ) + ((18673 / 6241) : ℂ) * ζ ^ 1 + ((34977 / 6241) : ℂ) * ζ ^ 2 - ((70331 / 31205) : ℂ) * ζ ^ 3 + ((172293 / 62410) : ℂ) * ζ ^ 4 + ((587579 / 62410) : ℂ) * ζ ^ 5 - ((134401 / 62410) : ℂ) * ζ ^ 6 + ((384239 / 62410) : ℂ) * ζ ^ 7 + ((443253 / 62410) : ℂ) * ζ ^ 8 - ((113993 / 62410) : ℂ) * ζ ^ 9 + ((161349 / 62410) : ℂ) * ζ ^ 10 + ((35508 / 6241) : ℂ) * ζ ^ 11 - ((21021 / 6241) : ℂ) * ζ ^ 12 - ((9971 / 6241) : ℂ) * ζ ^ 13 + ((364971 / 62410) : ℂ) * ζ ^ 14 - ((423021 / 62410) : ℂ) * ζ ^ 15 + ((2537 / 31205) : ℂ) * ζ ^ 16 - ((13498 / 31205) : ℂ) * ζ ^ 17 - ((217817 / 31205) : ℂ) * ζ ^ 18 - ((98377 / 62410) : ℂ) * ζ ^ 19 - ((34611 / 12482) : ℂ) * ζ ^ 20 - ((434917 / 62410) : ℂ) * ζ ^ 21 - ((31374 / 31205) : ℂ) * ζ ^ 22 - ((213619 / 62410) : ℂ) * ζ ^ 23 - ((75295 / 12482) : ℂ) * ζ ^ 24 - ((48907 / 62410) : ℂ) * ζ ^ 25 - ((43769 / 12482) : ℂ) * ζ ^ 26 - ((85579 / 12482) : ℂ) * ζ ^ 27 - ((20325 / 12482) : ℂ) * ζ ^ 28 - ((36396 / 31205) : ℂ) * ζ ^ 29 - ((27174 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep06Coefficient03 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity03 :
    row18_reducedY32_combinationStep06Coefficient03 =
      row18_reducedY32_combinationStep05Coefficient03 +
        row18_reducedY32_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep06Coefficient03 row18_reducedY32_combinationStep05Coefficient03 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep06Coefficient04 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity04 :
    row18_reducedY32_combinationStep06Coefficient04 =
      row18_reducedY32_combinationStep05Coefficient04 +
        row18_reducedY32_combinationStep06Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep06Coefficient04 row18_reducedY32_combinationStep05Coefficient04 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 (-((12839 / 62410) : ℂ) - ((13014 / 31205) : ℂ) * ζ ^ 1 + ((266081 / 31205) : ℂ) * ζ ^ 2 - ((9483 / 62410) : ℂ) * ζ ^ 3 - ((119076 / 31205) : ℂ) * ζ ^ 4 + ((245072 / 31205) : ℂ) * ζ ^ 5 - ((20247 / 62410) : ℂ) * ζ ^ 6 - ((165654 / 31205) : ℂ) * ζ ^ 7 + ((408999 / 62410) : ℂ) * ζ ^ 8 - ((58369 / 62410) : ℂ) * ζ ^ 9 - ((461433 / 62410) : ℂ) * ζ ^ 10 + ((500229 / 62410) : ℂ) * ζ ^ 11 - ((183609 / 62410) : ℂ) * ζ ^ 12 - ((188147 / 31205) : ℂ) * ζ ^ 13 + ((444333 / 62410) : ℂ) * ζ ^ 14 - ((248293 / 62410) : ℂ) * ζ ^ 15 - ((123576 / 31205) : ℂ) * ζ ^ 16 + ((425663 / 62410) : ℂ) * ζ ^ 17 - ((334383 / 62410) : ℂ) * ζ ^ 18 - ((18531 / 12482) : ℂ) * ζ ^ 19 + ((102873 / 31205) : ℂ) * ζ ^ 20 - ((189092 / 31205) : ℂ) * ζ ^ 21 - ((17548 / 31205) : ℂ) * ζ ^ 22 + ((74637 / 31205) : ℂ) * ζ ^ 23 - ((134933 / 62410) : ℂ) * ζ ^ 24 - ((2687 / 62410) : ℂ) * ζ ^ 25 + ((100233 / 62410) : ℂ) * ζ ^ 26 - ((75987 / 62410) : ℂ) * ζ ^ 27 + ((23639 / 62410) : ℂ) * ζ ^ 28 + ((19006 / 31205) : ℂ) * ζ ^ 29 + ((4529 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep06Coefficient05 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity05 :
    row18_reducedY32_combinationStep06Coefficient05 =
      row18_reducedY32_combinationStep05Coefficient05 +
        row18_reducedY32_combinationStep06Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY32_combinationStep06Coefficient05 row18_reducedY32_combinationStep05Coefficient05 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 (-((78073 / 62410) : ℂ) + ((51877 / 62410) : ℂ) * ζ ^ 1 + ((101821 / 31205) : ℂ) * ζ ^ 2 - ((40769 / 31205) : ℂ) * ζ ^ 3 + ((104677 / 62410) : ℂ) * ζ ^ 4 + ((186077 / 62410) : ℂ) * ζ ^ 5 - ((29193 / 12482) : ℂ) * ζ ^ 6 + ((164403 / 62410) : ℂ) * ζ ^ 7 + ((366957 / 62410) : ℂ) * ζ ^ 8 - ((141973 / 62410) : ℂ) * ζ ^ 9 + ((94347 / 12482) : ℂ) * ζ ^ 10 + ((172994 / 31205) : ℂ) * ζ ^ 11 - ((25733 / 62410) : ℂ) * ζ ^ 12 - ((48093 / 31205) : ℂ) * ζ ^ 13 + ((72353 / 12482) : ℂ) * ζ ^ 14 - ((67066 / 31205) : ℂ) * ζ ^ 15 - ((54828 / 31205) : ℂ) * ζ ^ 16 + ((23616 / 31205) : ℂ) * ζ ^ 17 - ((200901 / 62410) : ℂ) * ζ ^ 18 - ((222243 / 62410) : ℂ) * ζ ^ 19 + ((90819 / 31205) : ℂ) * ζ ^ 20 - ((134453 / 31205) : ℂ) * ζ ^ 21 - ((85042 / 31205) : ℂ) * ζ ^ 22 + ((145307 / 62410) : ℂ) * ζ ^ 23 - ((310611 / 62410) : ℂ) * ζ ^ 24 - ((2864 / 6241) : ℂ) * ζ ^ 25 - ((192109 / 62410) : ℂ) * ζ ^ 26 - ((30684 / 6241) : ℂ) * ζ ^ 27 - ((26811 / 31205) : ℂ) * ζ ^ 28 + ((207 / 6241) : ℂ) * ζ ^ 29 - ((58230 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY32_combinationStep06Coefficient06 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY32_combinationStep06CoefficientIdentity06 :
    row18_reducedY32_combinationStep06Coefficient06 =
      row18_reducedY32_combinationStep05Coefficient06 +
        row18_reducedY32_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep06Coefficient06 row18_reducedY32_combinationStep05Coefficient06 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep06Coefficient07 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity07 :
    row18_reducedY32_combinationStep06Coefficient07 =
      row18_reducedY32_combinationStep05Coefficient07 +
        row18_reducedY32_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep06Coefficient07 row18_reducedY32_combinationStep05Coefficient07 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep06Coefficient08 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity08 :
    row18_reducedY32_combinationStep06Coefficient08 =
      row18_reducedY32_combinationStep05Coefficient08 +
        row18_reducedY32_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep06Coefficient08 row18_reducedY32_combinationStep05Coefficient08 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep06Coefficient09 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity09 :
    row18_reducedY32_combinationStep06Coefficient09 =
      row18_reducedY32_combinationStep05Coefficient09 +
        row18_reducedY32_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep06Coefficient09 row18_reducedY32_combinationStep05Coefficient09 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep06Coefficient10 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity10 :
    row18_reducedY32_combinationStep06Coefficient10 =
      row18_reducedY32_combinationStep05Coefficient10 +
        row18_reducedY32_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep06Coefficient10 row18_reducedY32_combinationStep05Coefficient10 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep06Coefficient11 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity11 :
    row18_reducedY32_combinationStep06Coefficient11 =
      row18_reducedY32_combinationStep05Coefficient11 +
        row18_reducedY32_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep06Coefficient11 row18_reducedY32_combinationStep05Coefficient11 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep06Coefficient12 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity12 :
    row18_reducedY32_combinationStep06Coefficient12 =
      row18_reducedY32_combinationStep05Coefficient12 +
        row18_reducedY32_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep06Coefficient12 row18_reducedY32_combinationStep05Coefficient12 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep06Coefficient13 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity13 :
    row18_reducedY32_combinationStep06Coefficient13 =
      row18_reducedY32_combinationStep05Coefficient13 +
        row18_reducedY32_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep06Coefficient13 row18_reducedY32_combinationStep05Coefficient13 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep06Coefficient14 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity14 :
    row18_reducedY32_combinationStep06Coefficient14 =
      row18_reducedY32_combinationStep05Coefficient14 +
        row18_reducedY32_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep06Coefficient14 row18_reducedY32_combinationStep05Coefficient14 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY32_combinationStep06Coefficient15 : ℂ :=
  0

private theorem row18_reducedY32_combinationStep06CoefficientIdentity15 :
    row18_reducedY32_combinationStep06Coefficient15 =
      row18_reducedY32_combinationStep05Coefficient15 +
        row18_reducedY32_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY32_combinationStep06Coefficient15 row18_reducedY32_combinationStep05Coefficient15 row18_reducedY32_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY32_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY32_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY32_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY32_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY32_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY32_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY32_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY32_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY32_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY32_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY32_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY32_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY32_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY32_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY32_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY32_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY32_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY32_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY32_combinationStep06CoefficientIdentity00,
      row18_reducedY32_combinationStep06CoefficientIdentity01,
      row18_reducedY32_combinationStep06CoefficientIdentity02,
      row18_reducedY32_combinationStep06CoefficientIdentity03,
      row18_reducedY32_combinationStep06CoefficientIdentity04,
      row18_reducedY32_combinationStep06CoefficientIdentity05,
      row18_reducedY32_combinationStep06CoefficientIdentity06,
      row18_reducedY32_combinationStep06CoefficientIdentity07,
      row18_reducedY32_combinationStep06CoefficientIdentity08,
      row18_reducedY32_combinationStep06CoefficientIdentity09,
      row18_reducedY32_combinationStep06CoefficientIdentity10,
      row18_reducedY32_combinationStep06CoefficientIdentity11,
      row18_reducedY32_combinationStep06CoefficientIdentity12,
      row18_reducedY32_combinationStep06CoefficientIdentity13,
      row18_reducedY32_combinationStep06CoefficientIdentity14,
      row18_reducedY32_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY32_combinationStep06Multiplier * equation

theorem row18_reducedY32
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 3 2 = 0 := by
  have reduced :=
    row18_reducedY32_combinationStep06 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY32_combinationStep06Coefficient00,
      row18_reducedY32_combinationStep06Coefficient01,
      row18_reducedY32_combinationStep06Coefficient02,
      row18_reducedY32_combinationStep06Coefficient03,
      row18_reducedY32_combinationStep06Coefficient04,
      row18_reducedY32_combinationStep06Coefficient05,
      row18_reducedY32_combinationStep06Coefficient06,
      row18_reducedY32_combinationStep06Coefficient07,
      row18_reducedY32_combinationStep06Coefficient08,
      row18_reducedY32_combinationStep06Coefficient09,
      row18_reducedY32_combinationStep06Coefficient10,
      row18_reducedY32_combinationStep06Coefficient11,
      row18_reducedY32_combinationStep06Coefficient12,
      row18_reducedY32_combinationStep06Coefficient13,
      row18_reducedY32_combinationStep06Coefficient14,
      row18_reducedY32_combinationStep06Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
