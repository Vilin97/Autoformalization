/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction07

/-!
# Ambient row 18 commutant reduction 08

This generated module checks the reduced relation `reducedY44` for
matrix coordinate (4, 4).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY44_combinationStep00Multiplier : ℂ :=
  (-((16214 / 1185) : ℂ) + ((1194 / 79) : ℂ) * ζ ^ 1 + ((7318 / 237) : ℂ) * ζ ^ 2 - ((3166 / 237) : ℂ) * ζ ^ 3 + ((3656 / 237) : ℂ) * ζ ^ 5 + ((9354 / 395) : ℂ) * ζ ^ 8 + ((206 / 79) : ℂ) * ζ ^ 9 + ((2548 / 237) : ℂ) * ζ ^ 11 + ((4366 / 1185) : ℂ) * ζ ^ 12 - ((1194 / 79) : ℂ) * ζ ^ 13 + ((3092 / 237) : ℂ) * ζ ^ 15 - ((1194 / 79) : ℂ) * ζ ^ 17 - ((7318 / 237) : ℂ) * ζ ^ 18 - ((6748 / 237) : ℂ) * ζ ^ 21 - ((7318 / 237) : ℂ) * ζ ^ 22 - ((32428 / 1185) : ℂ) * ζ ^ 24 - ((74 / 237) : ℂ) * ζ ^ 25 - ((6748 / 237) : ℂ) * ζ ^ 27 - ((9354 / 395) : ℂ) * ζ ^ 28 + ((1194 / 79) : ℂ) * ζ ^ 29 - ((818 / 237) : ℂ) * ζ ^ 30 - ((2548 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY44_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep00CoefficientIdentity00 :
    row18_reducedY44_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep00Coefficient00 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep00Coefficient01 : ℂ :=
  (-((1235 / 237) : ℂ) - ((577 / 158) : ℂ) * ζ ^ 1 + ((2383 / 474) : ℂ) * ζ ^ 2 + ((597 / 79) : ℂ) * ζ ^ 3 - ((577 / 158) : ℂ) * ζ ^ 5 - ((29 / 158) : ℂ) * ζ ^ 6 + ((29 / 158) : ℂ) * ζ ^ 8 + ((577 / 158) : ℂ) * ζ ^ 9 - ((597 / 158) : ℂ) * ζ ^ 11 + ((559 / 158) : ℂ) * ζ ^ 12 + ((577 / 158) : ℂ) * ζ ^ 13 - ((535 / 237) : ℂ) * ζ ^ 15 + ((577 / 158) : ℂ) * ζ ^ 17 + ((233 / 237) : ℂ) * ζ ^ 18 - ((1685 / 237) : ℂ) * ζ ^ 21 - ((2383 / 474) : ℂ) * ζ ^ 22 + ((379 / 474) : ℂ) * ζ ^ 24 + ((1256 / 237) : ℂ) * ζ ^ 27 - ((29 / 158) : ℂ) * ζ ^ 28 - ((577 / 158) : ℂ) * ζ ^ 29 + ((265 / 79) : ℂ) * ζ ^ 30 + ((597 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep00CoefficientIdentity01 :
    row18_reducedY44_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep00Coefficient01 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 (((147331 / 93615) : ℂ) + ((227167 / 31205) : ℂ) * ζ ^ 1 + ((159691 / 93615) : ℂ) * ζ ^ 2 - ((101405 / 12482) : ℂ) * ζ ^ 3 + ((146361 / 62410) : ℂ) * ζ ^ 4 + ((174134 / 93615) : ℂ) * ζ ^ 5 - ((275051 / 93615) : ℂ) * ζ ^ 6 + ((19291 / 18723) : ℂ) * ζ ^ 7 + ((297087 / 62410) : ℂ) * ζ ^ 8 - ((69843 / 62410) : ℂ) * ζ ^ 9 - ((151259 / 31205) : ℂ) * ζ ^ 10 - ((427403 / 93615) : ℂ) * ζ ^ 11 + ((121237 / 31205) : ℂ) * ζ ^ 12 - ((132197 / 93615) : ℂ) * ζ ^ 13 - ((327467 / 31205) : ℂ) * ζ ^ 14 - ((300601 / 187230) : ℂ) * ζ ^ 15 + ((68373 / 31205) : ℂ) * ζ ^ 16 + ((99086 / 93615) : ℂ) * ζ ^ 17 - ((13953 / 12482) : ℂ) * ζ ^ 18 - ((863531 / 187230) : ℂ) * ζ ^ 19 - ((1151779 / 187230) : ℂ) * ζ ^ 20 + ((377987 / 93615) : ℂ) * ζ ^ 21 + ((328082 / 93615) : ℂ) * ζ ^ 22 + ((3763 / 37446) : ℂ) * ζ ^ 23 - ((238933 / 37446) : ℂ) * ζ ^ 24 - ((35219 / 187230) : ℂ) * ζ ^ 25 + ((409039 / 93615) : ℂ) * ζ ^ 26 + ((461344 / 93615) : ℂ) * ζ ^ 27 - ((48099 / 12482) : ℂ) * ζ ^ 28 - ((3293 / 18723) : ℂ) * ζ ^ 29 + ((43316 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep00Coefficient02 : ℂ :=
  (((297 / 79) : ℂ) + ((262 / 237) : ℂ) * ζ ^ 1 + ((360 / 79) : ℂ) * ζ ^ 2 - ((994 / 237) : ℂ) * ζ ^ 3 - ((820 / 237) : ℂ) * ζ ^ 5 + ((3025 / 474) : ℂ) * ζ ^ 6 - ((199 / 237) : ℂ) * ζ ^ 8 - ((224 / 79) : ℂ) * ζ ^ 9 - ((2125 / 474) : ℂ) * ζ ^ 11 - ((865 / 474) : ℂ) * ζ ^ 12 - ((262 / 237) : ℂ) * ζ ^ 13 + ((994 / 237) : ℂ) * ζ ^ 15 - ((262 / 237) : ℂ) * ζ ^ 17 - ((657 / 79) : ℂ) * ζ ^ 18 + ((1082 / 237) : ℂ) * ζ ^ 21 - ((360 / 79) : ℂ) * ζ ^ 22 - ((360 / 79) : ℂ) * ζ ^ 24 + ((1082 / 237) : ℂ) * ζ ^ 25 + ((2125 / 474) : ℂ) * ζ ^ 27 + ((199 / 237) : ℂ) * ζ ^ 28 + ((262 / 237) : ℂ) * ζ ^ 29 + ((1279 / 237) : ℂ) * ζ ^ 30 + ((2125 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep00CoefficientIdentity02 :
    row18_reducedY44_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep00Coefficient02 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 (-((684332 / 93615) : ℂ) + ((5341 / 2370) : ℂ) * ζ ^ 1 + ((162589 / 62410) : ℂ) * ζ ^ 2 + ((873103 / 187230) : ℂ) * ζ ^ 3 + ((1672879 / 187230) : ℂ) * ζ ^ 4 + ((267151 / 187230) : ℂ) * ζ ^ 5 - ((1463039 / 187230) : ℂ) * ζ ^ 6 - ((231919 / 93615) : ℂ) * ζ ^ 7 + ((7419 / 12482) : ℂ) * ζ ^ 8 + ((53942 / 18723) : ℂ) * ζ ^ 9 + ((181513 / 187230) : ℂ) * ζ ^ 10 + ((649259 / 187230) : ℂ) * ζ ^ 11 - ((3521 / 93615) : ℂ) * ζ ^ 12 - ((783541 / 187230) : ℂ) * ζ ^ 13 - ((1066763 / 187230) : ℂ) * ζ ^ 14 - ((25729 / 37446) : ℂ) * ζ ^ 15 - ((204149 / 187230) : ℂ) * ζ ^ 16 - ((398257 / 187230) : ℂ) * ζ ^ 17 - ((339136 / 93615) : ℂ) * ζ ^ 18 - ((8900 / 18723) : ℂ) * ζ ^ 19 + ((70153 / 187230) : ℂ) * ζ ^ 20 - ((64999 / 62410) : ℂ) * ζ ^ 21 - ((203249 / 187230) : ℂ) * ζ ^ 22 - ((78802 / 18723) : ℂ) * ζ ^ 23 - ((858991 / 187230) : ℂ) * ζ ^ 24 + ((97667 / 31205) : ℂ) * ζ ^ 25 + ((432457 / 187230) : ℂ) * ζ ^ 26 - ((29765 / 12482) : ℂ) * ζ ^ 27 - ((16192 / 18723) : ℂ) * ζ ^ 28 + ((13511 / 12482) : ℂ) * ζ ^ 29 + ((3185 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep00CoefficientIdentity03 :
    row18_reducedY44_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep00Coefficient03 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep00CoefficientIdentity04 :
    row18_reducedY44_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep00Coefficient04 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep00CoefficientIdentity05 :
    row18_reducedY44_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep00Coefficient05 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep00CoefficientIdentity06 :
    row18_reducedY44_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep00Coefficient06 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep00CoefficientIdentity07 :
    row18_reducedY44_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep00Coefficient07 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep00CoefficientIdentity08 :
    row18_reducedY44_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep00Coefficient08 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep00CoefficientIdentity09 :
    row18_reducedY44_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep00Coefficient09 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep00CoefficientIdentity10 :
    row18_reducedY44_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep00Coefficient10 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep00CoefficientIdentity11 :
    row18_reducedY44_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep00Coefficient11 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep00CoefficientIdentity12 :
    row18_reducedY44_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep00Coefficient12 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep00CoefficientIdentity13 :
    row18_reducedY44_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep00Coefficient13 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep00CoefficientIdentity14 :
    row18_reducedY44_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep00Coefficient14 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep00CoefficientIdentity15 :
    row18_reducedY44_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY44_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep00Coefficient15 row18_reducedY44_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY44_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY44_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY44_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY44_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY44_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY44_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY44_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY44_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY44_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY44_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY44_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY44_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY44_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY44_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY44_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY44_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY44_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY44_combinationStep00CoefficientIdentity00,
      row18_reducedY44_combinationStep00CoefficientIdentity01,
      row18_reducedY44_combinationStep00CoefficientIdentity02,
      row18_reducedY44_combinationStep00CoefficientIdentity03,
      row18_reducedY44_combinationStep00CoefficientIdentity04,
      row18_reducedY44_combinationStep00CoefficientIdentity05,
      row18_reducedY44_combinationStep00CoefficientIdentity06,
      row18_reducedY44_combinationStep00CoefficientIdentity07,
      row18_reducedY44_combinationStep00CoefficientIdentity08,
      row18_reducedY44_combinationStep00CoefficientIdentity09,
      row18_reducedY44_combinationStep00CoefficientIdentity10,
      row18_reducedY44_combinationStep00CoefficientIdentity11,
      row18_reducedY44_combinationStep00CoefficientIdentity12,
      row18_reducedY44_combinationStep00CoefficientIdentity13,
      row18_reducedY44_combinationStep00CoefficientIdentity14,
      row18_reducedY44_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY44_combinationStep00Multiplier * equation

private def row18_reducedY44_combinationStep01Multiplier : ℂ :=
  (-((3152 / 395) : ℂ) - ((1196 / 395) : ℂ) * ζ ^ 1 - ((6568 / 1185) : ℂ) * ζ ^ 2 - ((4544 / 1185) : ℂ) * ζ ^ 5 + ((2888 / 1185) : ℂ) * ζ ^ 6 + ((2888 / 1185) : ℂ) * ζ ^ 8 - ((4544 / 1185) : ℂ) * ζ ^ 9 + ((816 / 79) : ℂ) * ζ ^ 11 + ((4818 / 395) : ℂ) * ζ ^ 12 + ((1196 / 395) : ℂ) * ζ ^ 13 - ((194 / 79) : ℂ) * ζ ^ 15 + ((1196 / 395) : ℂ) * ζ ^ 17 + ((5474 / 1185) : ℂ) * ζ ^ 18 + ((4066 / 1185) : ℂ) * ζ ^ 21 + ((6568 / 1185) : ℂ) * ζ ^ 22 - ((8362 / 1185) : ℂ) * ζ ^ 24 + ((956 / 1185) : ℂ) * ζ ^ 25 + ((194 / 79) : ℂ) * ζ ^ 27 - ((2888 / 1185) : ℂ) * ζ ^ 28 - ((1196 / 395) : ℂ) * ζ ^ 29 - ((11566 / 1185) : ℂ) * ζ ^ 30 - ((816 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY44_combinationStep01Coefficient00 : ℂ :=
  (((503 / 79) : ℂ) + ((487 / 237) : ℂ) * ζ ^ 1 - ((283 / 237) : ℂ) * ζ ^ 2 - ((1313 / 237) : ℂ) * ζ ^ 3 + ((931 / 474) : ℂ) * ζ ^ 5 + ((85 / 79) : ℂ) * ζ ^ 6 - ((1495 / 474) : ℂ) * ζ ^ 8 - ((477 / 158) : ℂ) * ζ ^ 9 + ((1195 / 474) : ℂ) * ζ ^ 11 - ((1495 / 474) : ℂ) * ζ ^ 12 - ((487 / 237) : ℂ) * ζ ^ 13 + ((861 / 158) : ℂ) * ζ ^ 15 - ((487 / 237) : ℂ) * ζ ^ 17 - ((538 / 237) : ℂ) * ζ ^ 18 + ((826 / 237) : ℂ) * ζ ^ 21 + ((283 / 237) : ℂ) * ζ ^ 22 + ((43 / 474) : ℂ) * ζ ^ 25 - ((826 / 237) : ℂ) * ζ ^ 27 + ((1495 / 474) : ℂ) * ζ ^ 28 + ((487 / 237) : ℂ) * ζ ^ 29 + ((85 / 158) : ℂ) * ζ ^ 30 - ((1195 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep01CoefficientIdentity00 :
    row18_reducedY44_combinationStep01Coefficient00 =
      row18_reducedY44_combinationStep00Coefficient00 +
        row18_reducedY44_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep01Coefficient00 row18_reducedY44_combinationStep00Coefficient00 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 (-((134069 / 31205) : ℂ) - ((88079 / 93615) : ℂ) * ζ ^ 1 + ((112822 / 31205) : ℂ) * ζ ^ 2 + ((513743 / 93615) : ℂ) * ζ ^ 3 + ((436507 / 93615) : ℂ) * ζ ^ 4 - ((28033 / 62410) : ℂ) * ζ ^ 5 - ((152541 / 31205) : ℂ) * ζ ^ 6 - ((474638 / 93615) : ℂ) * ζ ^ 7 - ((151361 / 37446) : ℂ) * ζ ^ 8 + ((65371 / 31205) : ℂ) * ζ ^ 9 + ((281303 / 93615) : ℂ) * ζ ^ 10 - ((59789 / 187230) : ℂ) * ζ ^ 11 - ((140752 / 93615) : ℂ) * ζ ^ 12 - ((824851 / 187230) : ℂ) * ζ ^ 13 - ((101308 / 93615) : ℂ) * ζ ^ 14 + ((137218 / 93615) : ℂ) * ζ ^ 15 + ((491183 / 187230) : ℂ) * ζ ^ 16 + ((89739 / 31205) : ℂ) * ζ ^ 17 + ((66319 / 187230) : ℂ) * ζ ^ 18 + ((20263 / 37446) : ℂ) * ζ ^ 19 - ((55089 / 62410) : ℂ) * ζ ^ 20 - ((280039 / 93615) : ℂ) * ζ ^ 21 - ((231752 / 93615) : ℂ) * ζ ^ 22 - ((35341 / 31205) : ℂ) * ζ ^ 23 + ((28630 / 18723) : ℂ) * ζ ^ 24 + ((506221 / 187230) : ℂ) * ζ ^ 25 + ((271261 / 93615) : ℂ) * ζ ^ 26 + ((378401 / 187230) : ℂ) * ζ ^ 27 - ((34497 / 62410) : ℂ) * ζ ^ 28 - ((16799 / 12482) : ℂ) * ζ ^ 29 - ((3060 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep01Coefficient01 : ℂ :=
  (-((3049 / 474) : ℂ) - ((532 / 79) : ℂ) * ζ ^ 1 + ((965 / 474) : ℂ) * ζ ^ 2 + ((494 / 79) : ℂ) * ζ ^ 3 - ((532 / 79) : ℂ) * ζ ^ 5 - ((1042 / 237) : ℂ) * ζ ^ 6 + ((1042 / 237) : ℂ) * ζ ^ 8 + ((532 / 79) : ℂ) * ζ ^ 9 - ((247 / 79) : ℂ) * ζ ^ 11 + ((1373 / 237) : ℂ) * ζ ^ 12 + ((532 / 79) : ℂ) * ζ ^ 13 - ((342 / 79) : ℂ) * ζ ^ 15 + ((532 / 79) : ℂ) * ζ ^ 17 + ((863 / 158) : ℂ) * ζ ^ 18 - ((383 / 474) : ℂ) * ζ ^ 21 - ((965 / 474) : ℂ) * ζ ^ 22 + ((505 / 474) : ℂ) * ζ ^ 24 + ((152 / 79) : ℂ) * ζ ^ 27 - ((1042 / 237) : ℂ) * ζ ^ 28 - ((532 / 79) : ℂ) * ζ ^ 29 + ((331 / 237) : ℂ) * ζ ^ 30 + ((247 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep01CoefficientIdentity01 :
    row18_reducedY44_combinationStep01Coefficient01 =
      row18_reducedY44_combinationStep00Coefficient01 +
        row18_reducedY44_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep01Coefficient01 row18_reducedY44_combinationStep00Coefficient01 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 (((126667 / 62410) : ℂ) + ((246173 / 62410) : ℂ) * ζ ^ 1 + ((747121 / 93615) : ℂ) * ζ ^ 2 + ((485278 / 93615) : ℂ) * ζ ^ 3 + ((302977 / 187230) : ℂ) * ζ ^ 4 - ((11042 / 93615) : ℂ) * ζ ^ 5 - ((769823 / 187230) : ℂ) * ζ ^ 6 - ((373846 / 93615) : ℂ) * ζ ^ 7 - ((210914 / 31205) : ℂ) * ζ ^ 8 - ((1130887 / 187230) : ℂ) * ζ ^ 9 + ((268133 / 187230) : ℂ) * ζ ^ 10 + ((109985 / 37446) : ℂ) * ζ ^ 11 + ((416051 / 93615) : ℂ) * ζ ^ 12 - ((4775 / 37446) : ℂ) * ζ ^ 13 - ((496264 / 93615) : ℂ) * ζ ^ 14 + ((9511 / 93615) : ℂ) * ζ ^ 15 + ((3493 / 18723) : ℂ) * ζ ^ 16 + ((216517 / 93615) : ℂ) * ζ ^ 17 - ((109349 / 187230) : ℂ) * ζ ^ 18 - ((46304 / 18723) : ℂ) * ζ ^ 19 - ((198215 / 37446) : ℂ) * ζ ^ 20 - ((89727 / 12482) : ℂ) * ζ ^ 21 - ((320891 / 187230) : ℂ) * ζ ^ 22 + ((287479 / 93615) : ℂ) * ζ ^ 23 + ((257684 / 93615) : ℂ) * ζ ^ 24 + ((703519 / 187230) : ℂ) * ζ ^ 25 + ((101778 / 31205) : ℂ) * ζ ^ 26 + ((58589 / 93615) : ℂ) * ζ ^ 27 - ((9064 / 31205) : ℂ) * ζ ^ 28 - ((154402 / 93615) : ℂ) * ζ ^ 29 - ((5712 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep01Coefficient02 : ℂ :=
  (((297 / 79) : ℂ) + ((262 / 237) : ℂ) * ζ ^ 1 + ((360 / 79) : ℂ) * ζ ^ 2 - ((994 / 237) : ℂ) * ζ ^ 3 - ((820 / 237) : ℂ) * ζ ^ 5 + ((3025 / 474) : ℂ) * ζ ^ 6 - ((199 / 237) : ℂ) * ζ ^ 8 - ((224 / 79) : ℂ) * ζ ^ 9 - ((2125 / 474) : ℂ) * ζ ^ 11 - ((865 / 474) : ℂ) * ζ ^ 12 - ((262 / 237) : ℂ) * ζ ^ 13 + ((994 / 237) : ℂ) * ζ ^ 15 - ((262 / 237) : ℂ) * ζ ^ 17 - ((657 / 79) : ℂ) * ζ ^ 18 + ((1082 / 237) : ℂ) * ζ ^ 21 - ((360 / 79) : ℂ) * ζ ^ 22 - ((360 / 79) : ℂ) * ζ ^ 24 + ((1082 / 237) : ℂ) * ζ ^ 25 + ((2125 / 474) : ℂ) * ζ ^ 27 + ((199 / 237) : ℂ) * ζ ^ 28 + ((262 / 237) : ℂ) * ζ ^ 29 + ((1279 / 237) : ℂ) * ζ ^ 30 + ((2125 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep01CoefficientIdentity02 :
    row18_reducedY44_combinationStep01Coefficient02 =
      row18_reducedY44_combinationStep00Coefficient02 +
        row18_reducedY44_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep01Coefficient02 row18_reducedY44_combinationStep00Coefficient02 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep01Coefficient03 : ℂ :=
  (-((503 / 79) : ℂ) - ((487 / 237) : ℂ) * ζ ^ 1 + ((283 / 237) : ℂ) * ζ ^ 2 + ((1313 / 237) : ℂ) * ζ ^ 3 - ((931 / 474) : ℂ) * ζ ^ 5 - ((85 / 79) : ℂ) * ζ ^ 6 + ((1495 / 474) : ℂ) * ζ ^ 8 + ((477 / 158) : ℂ) * ζ ^ 9 - ((1195 / 474) : ℂ) * ζ ^ 11 + ((1495 / 474) : ℂ) * ζ ^ 12 + ((487 / 237) : ℂ) * ζ ^ 13 - ((861 / 158) : ℂ) * ζ ^ 15 + ((487 / 237) : ℂ) * ζ ^ 17 + ((538 / 237) : ℂ) * ζ ^ 18 - ((826 / 237) : ℂ) * ζ ^ 21 - ((283 / 237) : ℂ) * ζ ^ 22 - ((43 / 474) : ℂ) * ζ ^ 25 + ((826 / 237) : ℂ) * ζ ^ 27 - ((1495 / 474) : ℂ) * ζ ^ 28 - ((487 / 237) : ℂ) * ζ ^ 29 - ((85 / 158) : ℂ) * ζ ^ 30 + ((1195 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep01CoefficientIdentity03 :
    row18_reducedY44_combinationStep01Coefficient03 =
      row18_reducedY44_combinationStep00Coefficient03 +
        row18_reducedY44_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep01Coefficient03 row18_reducedY44_combinationStep00Coefficient03 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 (((134069 / 31205) : ℂ) + ((88079 / 93615) : ℂ) * ζ ^ 1 - ((112822 / 31205) : ℂ) * ζ ^ 2 - ((513743 / 93615) : ℂ) * ζ ^ 3 - ((436507 / 93615) : ℂ) * ζ ^ 4 + ((28033 / 62410) : ℂ) * ζ ^ 5 + ((152541 / 31205) : ℂ) * ζ ^ 6 + ((474638 / 93615) : ℂ) * ζ ^ 7 + ((151361 / 37446) : ℂ) * ζ ^ 8 - ((65371 / 31205) : ℂ) * ζ ^ 9 - ((281303 / 93615) : ℂ) * ζ ^ 10 + ((59789 / 187230) : ℂ) * ζ ^ 11 + ((140752 / 93615) : ℂ) * ζ ^ 12 + ((824851 / 187230) : ℂ) * ζ ^ 13 + ((101308 / 93615) : ℂ) * ζ ^ 14 - ((137218 / 93615) : ℂ) * ζ ^ 15 - ((491183 / 187230) : ℂ) * ζ ^ 16 - ((89739 / 31205) : ℂ) * ζ ^ 17 - ((66319 / 187230) : ℂ) * ζ ^ 18 - ((20263 / 37446) : ℂ) * ζ ^ 19 + ((55089 / 62410) : ℂ) * ζ ^ 20 + ((280039 / 93615) : ℂ) * ζ ^ 21 + ((231752 / 93615) : ℂ) * ζ ^ 22 + ((35341 / 31205) : ℂ) * ζ ^ 23 - ((28630 / 18723) : ℂ) * ζ ^ 24 - ((506221 / 187230) : ℂ) * ζ ^ 25 - ((271261 / 93615) : ℂ) * ζ ^ 26 - ((378401 / 187230) : ℂ) * ζ ^ 27 + ((34497 / 62410) : ℂ) * ζ ^ 28 + ((16799 / 12482) : ℂ) * ζ ^ 29 + ((3060 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep01CoefficientIdentity04 :
    row18_reducedY44_combinationStep01Coefficient04 =
      row18_reducedY44_combinationStep00Coefficient04 +
        row18_reducedY44_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep01Coefficient04 row18_reducedY44_combinationStep00Coefficient04 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep01CoefficientIdentity05 :
    row18_reducedY44_combinationStep01Coefficient05 =
      row18_reducedY44_combinationStep00Coefficient05 +
        row18_reducedY44_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep01Coefficient05 row18_reducedY44_combinationStep00Coefficient05 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep01CoefficientIdentity06 :
    row18_reducedY44_combinationStep01Coefficient06 =
      row18_reducedY44_combinationStep00Coefficient06 +
        row18_reducedY44_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep01Coefficient06 row18_reducedY44_combinationStep00Coefficient06 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep01CoefficientIdentity07 :
    row18_reducedY44_combinationStep01Coefficient07 =
      row18_reducedY44_combinationStep00Coefficient07 +
        row18_reducedY44_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep01Coefficient07 row18_reducedY44_combinationStep00Coefficient07 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep01CoefficientIdentity08 :
    row18_reducedY44_combinationStep01Coefficient08 =
      row18_reducedY44_combinationStep00Coefficient08 +
        row18_reducedY44_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep01Coefficient08 row18_reducedY44_combinationStep00Coefficient08 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep01CoefficientIdentity09 :
    row18_reducedY44_combinationStep01Coefficient09 =
      row18_reducedY44_combinationStep00Coefficient09 +
        row18_reducedY44_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep01Coefficient09 row18_reducedY44_combinationStep00Coefficient09 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep01CoefficientIdentity10 :
    row18_reducedY44_combinationStep01Coefficient10 =
      row18_reducedY44_combinationStep00Coefficient10 +
        row18_reducedY44_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep01Coefficient10 row18_reducedY44_combinationStep00Coefficient10 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep01CoefficientIdentity11 :
    row18_reducedY44_combinationStep01Coefficient11 =
      row18_reducedY44_combinationStep00Coefficient11 +
        row18_reducedY44_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep01Coefficient11 row18_reducedY44_combinationStep00Coefficient11 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep01CoefficientIdentity12 :
    row18_reducedY44_combinationStep01Coefficient12 =
      row18_reducedY44_combinationStep00Coefficient12 +
        row18_reducedY44_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep01Coefficient12 row18_reducedY44_combinationStep00Coefficient12 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep01CoefficientIdentity13 :
    row18_reducedY44_combinationStep01Coefficient13 =
      row18_reducedY44_combinationStep00Coefficient13 +
        row18_reducedY44_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep01Coefficient13 row18_reducedY44_combinationStep00Coefficient13 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep01CoefficientIdentity14 :
    row18_reducedY44_combinationStep01Coefficient14 =
      row18_reducedY44_combinationStep00Coefficient14 +
        row18_reducedY44_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep01Coefficient14 row18_reducedY44_combinationStep00Coefficient14 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep01CoefficientIdentity15 :
    row18_reducedY44_combinationStep01Coefficient15 =
      row18_reducedY44_combinationStep00Coefficient15 +
        row18_reducedY44_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep01Coefficient15 row18_reducedY44_combinationStep00Coefficient15 row18_reducedY44_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY44_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY44_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY44_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY44_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY44_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY44_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY44_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY44_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY44_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY44_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY44_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY44_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY44_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY44_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY44_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY44_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY44_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY44_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY44_combinationStep01CoefficientIdentity00,
      row18_reducedY44_combinationStep01CoefficientIdentity01,
      row18_reducedY44_combinationStep01CoefficientIdentity02,
      row18_reducedY44_combinationStep01CoefficientIdentity03,
      row18_reducedY44_combinationStep01CoefficientIdentity04,
      row18_reducedY44_combinationStep01CoefficientIdentity05,
      row18_reducedY44_combinationStep01CoefficientIdentity06,
      row18_reducedY44_combinationStep01CoefficientIdentity07,
      row18_reducedY44_combinationStep01CoefficientIdentity08,
      row18_reducedY44_combinationStep01CoefficientIdentity09,
      row18_reducedY44_combinationStep01CoefficientIdentity10,
      row18_reducedY44_combinationStep01CoefficientIdentity11,
      row18_reducedY44_combinationStep01CoefficientIdentity12,
      row18_reducedY44_combinationStep01CoefficientIdentity13,
      row18_reducedY44_combinationStep01CoefficientIdentity14,
      row18_reducedY44_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY44_combinationStep01Multiplier * equation

private def row18_reducedY44_combinationStep02Multiplier : ℂ :=
  (-((3454 / 237) : ℂ) - ((14918 / 1185) : ℂ) * ζ ^ 1 + ((214 / 237) : ℂ) * ζ ^ 2 + ((5974 / 395) : ℂ) * ζ ^ 3 - ((4218 / 395) : ℂ) * ζ ^ 5 - ((1340 / 79) : ℂ) * ζ ^ 6 + ((1292 / 237) : ℂ) * ζ ^ 8 + ((5366 / 1185) : ℂ) * ζ ^ 9 - ((12556 / 1185) : ℂ) * ζ ^ 11 + ((1292 / 237) : ℂ) * ζ ^ 12 + ((14918 / 1185) : ℂ) * ζ ^ 13 - ((15658 / 1185) : ℂ) * ζ ^ 15 + ((14918 / 1185) : ℂ) * ζ ^ 17 + ((4234 / 237) : ℂ) * ζ ^ 18 - ((3004 / 1185) : ℂ) * ζ ^ 21 - ((214 / 237) : ℂ) * ζ ^ 22 - ((2264 / 1185) : ℂ) * ζ ^ 25 + ((3004 / 1185) : ℂ) * ζ ^ 27 - ((1292 / 237) : ℂ) * ζ ^ 28 - ((14918 / 1185) : ℂ) * ζ ^ 29 - ((670 / 79) : ℂ) * ζ ^ 30 + ((12556 / 1185) : ℂ) * ζ ^ 31)

private def row18_reducedY44_combinationStep02Coefficient00 : ℂ :=
  (((481 / 237) : ℂ) + ((732 / 395) : ℂ) * ζ ^ 1 + ((51 / 395) : ℂ) * ζ ^ 2 - ((4144 / 1185) : ℂ) * ζ ^ 3 + ((4081 / 2370) : ℂ) * ζ ^ 5 + ((904 / 395) : ℂ) * ζ ^ 6 + ((131 / 237) : ℂ) * ζ ^ 8 + ((128 / 1185) : ℂ) * ζ ^ 9 + ((1424 / 395) : ℂ) * ζ ^ 11 + ((131 / 237) : ℂ) * ζ ^ 12 - ((732 / 395) : ℂ) * ζ ^ 13 + ((2659 / 790) : ℂ) * ζ ^ 15 - ((732 / 395) : ℂ) * ζ ^ 17 - ((853 / 395) : ℂ) * ζ ^ 18 + ((1948 / 1185) : ℂ) * ζ ^ 21 - ((51 / 395) : ℂ) * ζ ^ 22 + ((311 / 2370) : ℂ) * ζ ^ 25 - ((1948 / 1185) : ℂ) * ζ ^ 27 - ((131 / 237) : ℂ) * ζ ^ 28 + ((732 / 395) : ℂ) * ζ ^ 29 + ((452 / 395) : ℂ) * ζ ^ 30 - ((1424 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep02CoefficientIdentity00 :
    row18_reducedY44_combinationStep02Coefficient00 =
      row18_reducedY44_combinationStep01Coefficient00 +
        row18_reducedY44_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep02Coefficient00 row18_reducedY44_combinationStep01Coefficient00 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 (((91574 / 18723) : ℂ) + ((6457 / 37446) : ℂ) * ζ ^ 1 + ((198881 / 93615) : ℂ) * ζ ^ 2 + ((13258 / 18723) : ℂ) * ζ ^ 3 - ((438781 / 93615) : ℂ) * ζ ^ 4 - ((101513 / 37446) : ℂ) * ζ ^ 5 - ((68921 / 93615) : ℂ) * ζ ^ 6 + ((87198 / 31205) : ℂ) * ζ ^ 7 + ((165593 / 62410) : ℂ) * ζ ^ 8 - ((538867 / 187230) : ℂ) * ζ ^ 9 + ((40417 / 62410) : ℂ) * ζ ^ 10 - ((50879 / 187230) : ℂ) * ζ ^ 11 - ((361237 / 187230) : ℂ) * ζ ^ 12 + ((556657 / 187230) : ℂ) * ζ ^ 13 - ((383389 / 187230) : ℂ) * ζ ^ 14 + ((329384 / 93615) : ℂ) * ζ ^ 15 + ((789241 / 187230) : ℂ) * ζ ^ 16 - ((301951 / 187230) : ℂ) * ζ ^ 17 + ((42584 / 31205) : ℂ) * ζ ^ 18 - ((87371 / 31205) : ℂ) * ζ ^ 19 - ((108488 / 31205) : ℂ) * ζ ^ 20 + ((80942 / 93615) : ℂ) * ζ ^ 21 - ((188476 / 93615) : ℂ) * ζ ^ 22 - ((26317 / 187230) : ℂ) * ζ ^ 23 + ((10671 / 12482) : ℂ) * ζ ^ 24 + ((153488 / 93615) : ℂ) * ζ ^ 25 + ((80128 / 93615) : ℂ) * ζ ^ 26 - ((200881 / 187230) : ℂ) * ζ ^ 27 + ((22516 / 93615) : ℂ) * ζ ^ 28 - ((1081 / 1185) : ℂ) * ζ ^ 29 + ((43946 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep02Coefficient01 : ℂ :=
  (-((2335 / 237) : ℂ) - ((1477 / 474) : ℂ) * ζ ^ 1 + ((383 / 158) : ℂ) * ζ ^ 2 + ((1216 / 237) : ℂ) * ζ ^ 3 - ((1477 / 474) : ℂ) * ζ ^ 5 - ((3521 / 474) : ℂ) * ζ ^ 6 + ((3521 / 474) : ℂ) * ζ ^ 8 + ((1477 / 474) : ℂ) * ζ ^ 9 - ((608 / 237) : ℂ) * ζ ^ 11 + ((332 / 79) : ℂ) * ζ ^ 12 + ((1477 / 474) : ℂ) * ζ ^ 13 - ((3367 / 474) : ℂ) * ζ ^ 15 + ((1477 / 474) : ℂ) * ζ ^ 17 + ((1064 / 237) : ℂ) * ζ ^ 18 - ((1387 / 237) : ℂ) * ζ ^ 21 - ((383 / 158) : ℂ) * ζ ^ 22 - ((1393 / 474) : ℂ) * ζ ^ 24 - ((935 / 474) : ℂ) * ζ ^ 27 - ((3521 / 474) : ℂ) * ζ ^ 28 - ((1477 / 474) : ℂ) * ζ ^ 29 - ((1529 / 474) : ℂ) * ζ ^ 30 + ((608 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep02CoefficientIdentity01 :
    row18_reducedY44_combinationStep02Coefficient01 =
      row18_reducedY44_combinationStep01Coefficient01 +
        row18_reducedY44_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep02Coefficient01 row18_reducedY44_combinationStep01Coefficient01 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 (((4448 / 18723) : ℂ) - ((1933 / 790) : ℂ) * ζ ^ 1 + ((104107 / 37446) : ℂ) * ζ ^ 2 + ((491333 / 187230) : ℂ) * ζ ^ 3 - ((497642 / 93615) : ℂ) * ζ ^ 4 + ((172667 / 187230) : ℂ) * ζ ^ 5 + ((42448 / 93615) : ℂ) * ζ ^ 6 - ((107101 / 62410) : ℂ) * ζ ^ 7 + ((174581 / 93615) : ℂ) * ζ ^ 8 + ((70082 / 18723) : ℂ) * ζ ^ 9 - ((421831 / 187230) : ℂ) * ζ ^ 10 - ((144653 / 93615) : ℂ) * ζ ^ 11 + ((550699 / 93615) : ℂ) * ζ ^ 12 - ((128171 / 37446) : ℂ) * ζ ^ 13 - ((63833 / 37446) : ℂ) * ζ ^ 14 + ((251839 / 187230) : ℂ) * ζ ^ 15 + ((13417 / 37446) : ℂ) * ζ ^ 16 + ((105657 / 62410) : ℂ) * ζ ^ 17 - ((300238 / 93615) : ℂ) * ζ ^ 18 - ((333167 / 62410) : ℂ) * ζ ^ 19 + ((47579 / 31205) : ℂ) * ζ ^ 20 - ((499343 / 187230) : ℂ) * ζ ^ 21 - ((18184 / 6241) : ℂ) * ζ ^ 22 + ((305237 / 187230) : ℂ) * ζ ^ 23 + ((447949 / 187230) : ℂ) * ζ ^ 24 - ((540031 / 187230) : ℂ) * ζ ^ 25 + ((55781 / 187230) : ℂ) * ζ ^ 26 + ((472033 / 187230) : ℂ) * ζ ^ 27 - ((300649 / 62410) : ℂ) * ζ ^ 28 + ((91229 / 62410) : ℂ) * ζ ^ 29 + ((40807 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep02Coefficient02 : ℂ :=
  (((297 / 79) : ℂ) + ((262 / 237) : ℂ) * ζ ^ 1 + ((360 / 79) : ℂ) * ζ ^ 2 - ((994 / 237) : ℂ) * ζ ^ 3 - ((820 / 237) : ℂ) * ζ ^ 5 + ((3025 / 474) : ℂ) * ζ ^ 6 - ((199 / 237) : ℂ) * ζ ^ 8 - ((224 / 79) : ℂ) * ζ ^ 9 - ((2125 / 474) : ℂ) * ζ ^ 11 - ((865 / 474) : ℂ) * ζ ^ 12 - ((262 / 237) : ℂ) * ζ ^ 13 + ((994 / 237) : ℂ) * ζ ^ 15 - ((262 / 237) : ℂ) * ζ ^ 17 - ((657 / 79) : ℂ) * ζ ^ 18 + ((1082 / 237) : ℂ) * ζ ^ 21 - ((360 / 79) : ℂ) * ζ ^ 22 - ((360 / 79) : ℂ) * ζ ^ 24 + ((1082 / 237) : ℂ) * ζ ^ 25 + ((2125 / 474) : ℂ) * ζ ^ 27 + ((199 / 237) : ℂ) * ζ ^ 28 + ((262 / 237) : ℂ) * ζ ^ 29 + ((1279 / 237) : ℂ) * ζ ^ 30 + ((2125 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep02CoefficientIdentity02 :
    row18_reducedY44_combinationStep02Coefficient02 =
      row18_reducedY44_combinationStep01Coefficient02 +
        row18_reducedY44_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep02Coefficient02 row18_reducedY44_combinationStep01Coefficient02 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep02Coefficient03 : ℂ :=
  (-((503 / 79) : ℂ) - ((487 / 237) : ℂ) * ζ ^ 1 + ((283 / 237) : ℂ) * ζ ^ 2 + ((1313 / 237) : ℂ) * ζ ^ 3 - ((931 / 474) : ℂ) * ζ ^ 5 - ((85 / 79) : ℂ) * ζ ^ 6 + ((1495 / 474) : ℂ) * ζ ^ 8 + ((477 / 158) : ℂ) * ζ ^ 9 - ((1195 / 474) : ℂ) * ζ ^ 11 + ((1495 / 474) : ℂ) * ζ ^ 12 + ((487 / 237) : ℂ) * ζ ^ 13 - ((861 / 158) : ℂ) * ζ ^ 15 + ((487 / 237) : ℂ) * ζ ^ 17 + ((538 / 237) : ℂ) * ζ ^ 18 - ((826 / 237) : ℂ) * ζ ^ 21 - ((283 / 237) : ℂ) * ζ ^ 22 - ((43 / 474) : ℂ) * ζ ^ 25 + ((826 / 237) : ℂ) * ζ ^ 27 - ((1495 / 474) : ℂ) * ζ ^ 28 - ((487 / 237) : ℂ) * ζ ^ 29 - ((85 / 158) : ℂ) * ζ ^ 30 + ((1195 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep02CoefficientIdentity03 :
    row18_reducedY44_combinationStep02Coefficient03 =
      row18_reducedY44_combinationStep01Coefficient03 +
        row18_reducedY44_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep02Coefficient03 row18_reducedY44_combinationStep01Coefficient03 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep02Coefficient04 : ℂ :=
  (((1028 / 237) : ℂ) + ((239 / 1185) : ℂ) * ζ ^ 1 - ((1568 / 1185) : ℂ) * ζ ^ 2 - ((807 / 395) : ℂ) * ζ ^ 3 + ((287 / 1185) : ℂ) * ζ ^ 5 - ((479 / 395) : ℂ) * ζ ^ 6 - ((1757 / 474) : ℂ) * ζ ^ 8 - ((7411 / 2370) : ℂ) * ζ ^ 9 - ((2569 / 2370) : ℂ) * ζ ^ 11 - ((1757 / 474) : ℂ) * ζ ^ 12 - ((239 / 1185) : ℂ) * ζ ^ 13 + ((823 / 395) : ℂ) * ζ ^ 15 - ((239 / 1185) : ℂ) * ζ ^ 17 - ((131 / 1185) : ℂ) * ζ ^ 18 + ((2182 / 1185) : ℂ) * ζ ^ 21 + ((1568 / 1185) : ℂ) * ζ ^ 22 - ((16 / 395) : ℂ) * ζ ^ 25 - ((2182 / 1185) : ℂ) * ζ ^ 27 + ((1757 / 474) : ℂ) * ζ ^ 28 + ((239 / 1185) : ℂ) * ζ ^ 29 - ((479 / 790) : ℂ) * ζ ^ 30 + ((2569 / 2370) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep02CoefficientIdentity04 :
    row18_reducedY44_combinationStep02Coefficient04 =
      row18_reducedY44_combinationStep01Coefficient04 +
        row18_reducedY44_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep02Coefficient04 row18_reducedY44_combinationStep01Coefficient04 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 (-((91574 / 18723) : ℂ) - ((6457 / 37446) : ℂ) * ζ ^ 1 - ((198881 / 93615) : ℂ) * ζ ^ 2 - ((13258 / 18723) : ℂ) * ζ ^ 3 + ((438781 / 93615) : ℂ) * ζ ^ 4 + ((101513 / 37446) : ℂ) * ζ ^ 5 + ((68921 / 93615) : ℂ) * ζ ^ 6 - ((87198 / 31205) : ℂ) * ζ ^ 7 - ((165593 / 62410) : ℂ) * ζ ^ 8 + ((538867 / 187230) : ℂ) * ζ ^ 9 - ((40417 / 62410) : ℂ) * ζ ^ 10 + ((50879 / 187230) : ℂ) * ζ ^ 11 + ((361237 / 187230) : ℂ) * ζ ^ 12 - ((556657 / 187230) : ℂ) * ζ ^ 13 + ((383389 / 187230) : ℂ) * ζ ^ 14 - ((329384 / 93615) : ℂ) * ζ ^ 15 - ((789241 / 187230) : ℂ) * ζ ^ 16 + ((301951 / 187230) : ℂ) * ζ ^ 17 - ((42584 / 31205) : ℂ) * ζ ^ 18 + ((87371 / 31205) : ℂ) * ζ ^ 19 + ((108488 / 31205) : ℂ) * ζ ^ 20 - ((80942 / 93615) : ℂ) * ζ ^ 21 + ((188476 / 93615) : ℂ) * ζ ^ 22 + ((26317 / 187230) : ℂ) * ζ ^ 23 - ((10671 / 12482) : ℂ) * ζ ^ 24 - ((153488 / 93615) : ℂ) * ζ ^ 25 - ((80128 / 93615) : ℂ) * ζ ^ 26 + ((200881 / 187230) : ℂ) * ζ ^ 27 - ((22516 / 93615) : ℂ) * ζ ^ 28 + ((1081 / 1185) : ℂ) * ζ ^ 29 - ((43946 / 93615) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep02CoefficientIdentity05 :
    row18_reducedY44_combinationStep02Coefficient05 =
      row18_reducedY44_combinationStep01Coefficient05 +
        row18_reducedY44_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep02Coefficient05 row18_reducedY44_combinationStep01Coefficient05 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep02Coefficient06 : ℂ :=
  (-((1492 / 395) : ℂ) - ((1311 / 158) : ℂ) * ζ ^ 1 - ((3914 / 395) : ℂ) * ζ ^ 2 - ((1369 / 237) : ℂ) * ζ ^ 3 + ((3022 / 1185) : ℂ) * ζ ^ 6 - ((4642 / 1185) : ℂ) * ζ ^ 8 - ((2959 / 474) : ℂ) * ζ ^ 9 + ((1367 / 158) : ℂ) * ζ ^ 11 + ((14764 / 1185) : ℂ) * ζ ^ 12 + ((1311 / 158) : ℂ) * ζ ^ 13 - ((1369 / 237) : ℂ) * ζ ^ 15 + ((1311 / 158) : ℂ) * ζ ^ 17 + ((2422 / 395) : ℂ) * ζ ^ 18 + ((1311 / 158) : ℂ) * ζ ^ 21 + ((3914 / 395) : ℂ) * ζ ^ 22 - ((3914 / 395) : ℂ) * ζ ^ 24 - ((1311 / 158) : ℂ) * ζ ^ 25 + ((1367 / 158) : ℂ) * ζ ^ 27 + ((4642 / 1185) : ℂ) * ζ ^ 28 - ((1311 / 158) : ℂ) * ζ ^ 29 - ((16384 / 1185) : ℂ) * ζ ^ 30 - ((1367 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep02CoefficientIdentity06 :
    row18_reducedY44_combinationStep02Coefficient06 =
      row18_reducedY44_combinationStep01Coefficient06 +
        row18_reducedY44_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep02Coefficient06 row18_reducedY44_combinationStep01Coefficient06 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 (((517669 / 93615) : ℂ) + ((862361 / 93615) : ℂ) * ζ ^ 1 + ((916462 / 93615) : ℂ) * ζ ^ 2 + ((311378 / 93615) : ℂ) * ζ ^ 3 - ((551873 / 93615) : ℂ) * ζ ^ 4 - ((1570027 / 187230) : ℂ) * ζ ^ 5 - ((500699 / 62410) : ℂ) * ζ ^ 6 - ((143401 / 62410) : ℂ) * ζ ^ 7 + ((1145489 / 187230) : ℂ) * ζ ^ 8 + ((967573 / 187230) : ℂ) * ζ ^ 9 + ((181291 / 37446) : ℂ) * ζ ^ 10 + ((15161 / 187230) : ℂ) * ζ ^ 11 - ((392637 / 62410) : ℂ) * ζ ^ 12 - ((533143 / 93615) : ℂ) * ζ ^ 13 - ((148919 / 62410) : ℂ) * ζ ^ 14 + ((104393 / 31205) : ℂ) * ζ ^ 15 + ((196118 / 31205) : ℂ) * ζ ^ 16 + ((89093 / 31205) : ℂ) * ζ ^ 17 + ((18421 / 31205) : ℂ) * ζ ^ 18 - ((241873 / 62410) : ℂ) * ζ ^ 19 - ((771149 / 187230) : ℂ) * ζ ^ 20 - ((50571 / 62410) : ℂ) * ζ ^ 21 + ((21202 / 93615) : ℂ) * ζ ^ 22 + ((306661 / 93615) : ℂ) * ζ ^ 23 + ((109681 / 31205) : ℂ) * ζ ^ 24 + ((106531 / 62410) : ℂ) * ζ ^ 25 - ((60671 / 93615) : ℂ) * ζ ^ 26 - ((842209 / 187230) : ℂ) * ζ ^ 27 - ((271471 / 187230) : ℂ) * ζ ^ 28 + ((75323 / 62410) : ℂ) * ζ ^ 29 + ((3139 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep02CoefficientIdentity07 :
    row18_reducedY44_combinationStep02Coefficient07 =
      row18_reducedY44_combinationStep01Coefficient07 +
        row18_reducedY44_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep02Coefficient07 row18_reducedY44_combinationStep01Coefficient07 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep02CoefficientIdentity08 :
    row18_reducedY44_combinationStep02Coefficient08 =
      row18_reducedY44_combinationStep01Coefficient08 +
        row18_reducedY44_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep02Coefficient08 row18_reducedY44_combinationStep01Coefficient08 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep02CoefficientIdentity09 :
    row18_reducedY44_combinationStep02Coefficient09 =
      row18_reducedY44_combinationStep01Coefficient09 +
        row18_reducedY44_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep02Coefficient09 row18_reducedY44_combinationStep01Coefficient09 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep02CoefficientIdentity10 :
    row18_reducedY44_combinationStep02Coefficient10 =
      row18_reducedY44_combinationStep01Coefficient10 +
        row18_reducedY44_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep02Coefficient10 row18_reducedY44_combinationStep01Coefficient10 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep02CoefficientIdentity11 :
    row18_reducedY44_combinationStep02Coefficient11 =
      row18_reducedY44_combinationStep01Coefficient11 +
        row18_reducedY44_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep02Coefficient11 row18_reducedY44_combinationStep01Coefficient11 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep02CoefficientIdentity12 :
    row18_reducedY44_combinationStep02Coefficient12 =
      row18_reducedY44_combinationStep01Coefficient12 +
        row18_reducedY44_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep02Coefficient12 row18_reducedY44_combinationStep01Coefficient12 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep02CoefficientIdentity13 :
    row18_reducedY44_combinationStep02Coefficient13 =
      row18_reducedY44_combinationStep01Coefficient13 +
        row18_reducedY44_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep02Coefficient13 row18_reducedY44_combinationStep01Coefficient13 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep02CoefficientIdentity14 :
    row18_reducedY44_combinationStep02Coefficient14 =
      row18_reducedY44_combinationStep01Coefficient14 +
        row18_reducedY44_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep02Coefficient14 row18_reducedY44_combinationStep01Coefficient14 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep02CoefficientIdentity15 :
    row18_reducedY44_combinationStep02Coefficient15 =
      row18_reducedY44_combinationStep01Coefficient15 +
        row18_reducedY44_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep02Coefficient15 row18_reducedY44_combinationStep01Coefficient15 row18_reducedY44_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY44_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY44_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY44_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY44_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY44_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY44_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY44_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY44_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY44_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY44_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY44_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY44_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY44_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY44_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY44_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY44_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY44_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY44_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY44_combinationStep02CoefficientIdentity00,
      row18_reducedY44_combinationStep02CoefficientIdentity01,
      row18_reducedY44_combinationStep02CoefficientIdentity02,
      row18_reducedY44_combinationStep02CoefficientIdentity03,
      row18_reducedY44_combinationStep02CoefficientIdentity04,
      row18_reducedY44_combinationStep02CoefficientIdentity05,
      row18_reducedY44_combinationStep02CoefficientIdentity06,
      row18_reducedY44_combinationStep02CoefficientIdentity07,
      row18_reducedY44_combinationStep02CoefficientIdentity08,
      row18_reducedY44_combinationStep02CoefficientIdentity09,
      row18_reducedY44_combinationStep02CoefficientIdentity10,
      row18_reducedY44_combinationStep02CoefficientIdentity11,
      row18_reducedY44_combinationStep02CoefficientIdentity12,
      row18_reducedY44_combinationStep02CoefficientIdentity13,
      row18_reducedY44_combinationStep02CoefficientIdentity14,
      row18_reducedY44_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY44_combinationStep02Multiplier * equation

private def row18_reducedY44_combinationStep03Multiplier : ℂ :=
  (-((482 / 237) : ℂ) - ((854 / 237) : ℂ) * ζ ^ 1 - ((896 / 237) : ℂ) * ζ ^ 2 - ((1310 / 237) : ℂ) * ζ ^ 5 - ((138 / 79) : ℂ) * ζ ^ 6 - ((138 / 79) : ℂ) * ζ ^ 8 - ((1310 / 237) : ℂ) * ζ ^ 9 - ((226 / 237) : ℂ) * ζ ^ 11 + ((292 / 79) : ℂ) * ζ ^ 12 + ((854 / 237) : ℂ) * ζ ^ 13 - ((1340 / 237) : ℂ) * ζ ^ 15 + ((854 / 237) : ℂ) * ζ ^ 17 + ((740 / 237) : ℂ) * ζ ^ 18 + ((1082 / 237) : ℂ) * ζ ^ 21 + ((896 / 237) : ℂ) * ζ ^ 22 - ((326 / 237) : ℂ) * ζ ^ 24 + ((152 / 79) : ℂ) * ζ ^ 25 + ((1340 / 237) : ℂ) * ζ ^ 27 + ((138 / 79) : ℂ) * ζ ^ 28 - ((854 / 237) : ℂ) * ζ ^ 29 - ((430 / 79) : ℂ) * ζ ^ 30 + ((226 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY44_combinationStep03Coefficient00 : ℂ :=
  (-((459 / 158) : ℂ) - ((1594 / 1185) : ℂ) * ζ ^ 1 + ((2878 / 1185) : ℂ) * ζ ^ 2 + ((4277 / 2370) : ℂ) * ζ ^ 3 - ((1652 / 1185) : ℂ) * ζ ^ 5 + ((787 / 1185) : ℂ) * ζ ^ 6 + ((991 / 237) : ℂ) * ζ ^ 8 + ((5591 / 2370) : ℂ) * ζ ^ 9 + ((219 / 395) : ℂ) * ζ ^ 11 + ((991 / 237) : ℂ) * ζ ^ 12 + ((1594 / 1185) : ℂ) * ζ ^ 13 - ((4393 / 2370) : ℂ) * ζ ^ 15 + ((1594 / 1185) : ℂ) * ζ ^ 17 + ((697 / 395) : ℂ) * ζ ^ 18 - ((363 / 790) : ℂ) * ζ ^ 21 - ((2878 / 1185) : ℂ) * ζ ^ 22 + ((58 / 1185) : ℂ) * ζ ^ 25 + ((363 / 790) : ℂ) * ζ ^ 27 - ((991 / 237) : ℂ) * ζ ^ 28 - ((1594 / 1185) : ℂ) * ζ ^ 29 + ((787 / 2370) : ℂ) * ζ ^ 30 - ((219 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep03CoefficientIdentity00 :
    row18_reducedY44_combinationStep03Coefficient00 =
      row18_reducedY44_combinationStep02Coefficient00 +
        row18_reducedY44_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep03Coefficient00 row18_reducedY44_combinationStep02Coefficient00 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 (((58541 / 12482) : ℂ) + ((35557 / 12482) : ℂ) * ζ ^ 1 - ((50117 / 18723) : ℂ) * ζ ^ 2 - ((31936 / 6241) : ℂ) * ζ ^ 3 - ((170303 / 37446) : ℂ) * ζ ^ 4 - ((2063 / 18723) : ℂ) * ζ ^ 5 + ((51173 / 12482) : ℂ) * ζ ^ 6 + ((28764 / 6241) : ℂ) * ζ ^ 7 + ((38987 / 37446) : ℂ) * ζ ^ 8 - ((51961 / 37446) : ℂ) * ζ ^ 9 - ((28327 / 12482) : ℂ) * ζ ^ 10 - ((26567 / 18723) : ℂ) * ζ ^ 11 + ((5201 / 12482) : ℂ) * ζ ^ 12 + ((11188 / 6241) : ℂ) * ζ ^ 13 + ((15533 / 18723) : ℂ) * ζ ^ 14 + ((20767 / 37446) : ℂ) * ζ ^ 15 + ((815 / 37446) : ℂ) * ζ ^ 16 - ((33851 / 37446) : ℂ) * ζ ^ 17 - ((9259 / 6241) : ℂ) * ζ ^ 18 - ((20938 / 18723) : ℂ) * ζ ^ 19 + ((1667 / 6241) : ℂ) * ζ ^ 20 + ((12365 / 6241) : ℂ) * ζ ^ 21 + ((10411 / 6241) : ℂ) * ζ ^ 22 + ((11321 / 37446) : ℂ) * ζ ^ 23 - ((7 / 6) : ℂ) * ζ ^ 24 - ((36985 / 18723) : ℂ) * ζ ^ 25 - ((24550 / 18723) : ℂ) * ζ ^ 26 + ((32443 / 37446) : ℂ) * ζ ^ 27 + ((17948 / 18723) : ℂ) * ζ ^ 28 + ((1417 / 12482) : ℂ) * ζ ^ 29 - ((565 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep03Coefficient01 : ℂ :=
  (-((61 / 158) : ℂ) - ((80 / 237) : ℂ) * ζ ^ 1 - ((26 / 79) : ℂ) * ζ ^ 2 - ((17 / 79) : ℂ) * ζ ^ 3 - ((80 / 237) : ℂ) * ζ ^ 5 - ((113 / 158) : ℂ) * ζ ^ 6 + ((113 / 158) : ℂ) * ζ ^ 8 + ((80 / 237) : ℂ) * ζ ^ 9 + ((17 / 158) : ℂ) * ζ ^ 11 + ((337 / 474) : ℂ) * ζ ^ 12 + ((80 / 237) : ℂ) * ζ ^ 13 - ((68 / 237) : ℂ) * ζ ^ 15 + ((80 / 237) : ℂ) * ζ ^ 17 + ((100 / 237) : ℂ) * ζ ^ 18 - ((19 / 474) : ℂ) * ζ ^ 21 + ((26 / 79) : ℂ) * ζ ^ 22 - ((139 / 474) : ℂ) * ζ ^ 24 - ((119 / 237) : ℂ) * ζ ^ 27 - ((113 / 158) : ℂ) * ζ ^ 28 - ((80 / 237) : ℂ) * ζ ^ 29 - ((1 / 237) : ℂ) * ζ ^ 30 - ((17 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep03CoefficientIdentity01 :
    row18_reducedY44_combinationStep03Coefficient01 =
      row18_reducedY44_combinationStep02Coefficient01 +
        row18_reducedY44_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep03Coefficient01 row18_reducedY44_combinationStep02Coefficient01 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 (-((362185 / 37446) : ℂ) - ((65722 / 18723) : ℂ) * ζ ^ 1 + ((28511 / 37446) : ℂ) * ζ ^ 2 + ((64792 / 18723) : ℂ) * ζ ^ 3 + ((164156 / 18723) : ℂ) * ζ ^ 4 + ((5773 / 12482) : ℂ) * ζ ^ 5 - ((60949 / 6241) : ℂ) * ζ ^ 6 - ((47147 / 6241) : ℂ) * ζ ^ 7 - ((10179 / 6241) : ℂ) * ζ ^ 8 + ((49723 / 37446) : ℂ) * ζ ^ 9 + ((193867 / 37446) : ℂ) * ζ ^ 10 + ((12313 / 12482) : ℂ) * ζ ^ 11 - ((43934 / 18723) : ℂ) * ζ ^ 12 - ((3212 / 6241) : ℂ) * ζ ^ 13 - ((74950 / 18723) : ℂ) * ζ ^ 14 - ((79511 / 18723) : ℂ) * ζ ^ 15 - ((11348 / 18723) : ℂ) * ζ ^ 16 - ((5231 / 18723) : ℂ) * ζ ^ 17 + ((67108 / 18723) : ℂ) * ζ ^ 18 + ((198547 / 37446) : ℂ) * ζ ^ 19 - ((60505 / 37446) : ℂ) * ζ ^ 20 - ((85598 / 18723) : ℂ) * ζ ^ 21 - ((38906 / 18723) : ℂ) * ζ ^ 22 + ((27374 / 18723) : ℂ) * ζ ^ 23 + ((60319 / 18723) : ℂ) * ζ ^ 24 + ((41511 / 12482) : ℂ) * ζ ^ 25 - ((26657 / 37446) : ℂ) * ζ ^ 26 - ((13287 / 12482) : ℂ) * ζ ^ 27 - ((20995 / 37446) : ℂ) * ζ ^ 28 - ((2558 / 6241) : ℂ) * ζ ^ 29 + ((1582 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep03Coefficient02 : ℂ :=
  (((297 / 79) : ℂ) + ((262 / 237) : ℂ) * ζ ^ 1 + ((360 / 79) : ℂ) * ζ ^ 2 - ((994 / 237) : ℂ) * ζ ^ 3 - ((820 / 237) : ℂ) * ζ ^ 5 + ((3025 / 474) : ℂ) * ζ ^ 6 - ((199 / 237) : ℂ) * ζ ^ 8 - ((224 / 79) : ℂ) * ζ ^ 9 - ((2125 / 474) : ℂ) * ζ ^ 11 - ((865 / 474) : ℂ) * ζ ^ 12 - ((262 / 237) : ℂ) * ζ ^ 13 + ((994 / 237) : ℂ) * ζ ^ 15 - ((262 / 237) : ℂ) * ζ ^ 17 - ((657 / 79) : ℂ) * ζ ^ 18 + ((1082 / 237) : ℂ) * ζ ^ 21 - ((360 / 79) : ℂ) * ζ ^ 22 - ((360 / 79) : ℂ) * ζ ^ 24 + ((1082 / 237) : ℂ) * ζ ^ 25 + ((2125 / 474) : ℂ) * ζ ^ 27 + ((199 / 237) : ℂ) * ζ ^ 28 + ((262 / 237) : ℂ) * ζ ^ 29 + ((1279 / 237) : ℂ) * ζ ^ 30 + ((2125 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep03CoefficientIdentity02 :
    row18_reducedY44_combinationStep03Coefficient02 =
      row18_reducedY44_combinationStep02Coefficient02 +
        row18_reducedY44_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep03Coefficient02 row18_reducedY44_combinationStep02Coefficient02 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep03Coefficient03 : ℂ :=
  (-((503 / 79) : ℂ) - ((487 / 237) : ℂ) * ζ ^ 1 + ((283 / 237) : ℂ) * ζ ^ 2 + ((1313 / 237) : ℂ) * ζ ^ 3 - ((931 / 474) : ℂ) * ζ ^ 5 - ((85 / 79) : ℂ) * ζ ^ 6 + ((1495 / 474) : ℂ) * ζ ^ 8 + ((477 / 158) : ℂ) * ζ ^ 9 - ((1195 / 474) : ℂ) * ζ ^ 11 + ((1495 / 474) : ℂ) * ζ ^ 12 + ((487 / 237) : ℂ) * ζ ^ 13 - ((861 / 158) : ℂ) * ζ ^ 15 + ((487 / 237) : ℂ) * ζ ^ 17 + ((538 / 237) : ℂ) * ζ ^ 18 - ((826 / 237) : ℂ) * ζ ^ 21 - ((283 / 237) : ℂ) * ζ ^ 22 - ((43 / 474) : ℂ) * ζ ^ 25 + ((826 / 237) : ℂ) * ζ ^ 27 - ((1495 / 474) : ℂ) * ζ ^ 28 - ((487 / 237) : ℂ) * ζ ^ 29 - ((85 / 158) : ℂ) * ζ ^ 30 + ((1195 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep03CoefficientIdentity03 :
    row18_reducedY44_combinationStep03Coefficient03 =
      row18_reducedY44_combinationStep02Coefficient03 +
        row18_reducedY44_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep03Coefficient03 row18_reducedY44_combinationStep02Coefficient03 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep03Coefficient04 : ℂ :=
  (((1028 / 237) : ℂ) + ((239 / 1185) : ℂ) * ζ ^ 1 - ((1568 / 1185) : ℂ) * ζ ^ 2 - ((807 / 395) : ℂ) * ζ ^ 3 + ((287 / 1185) : ℂ) * ζ ^ 5 - ((479 / 395) : ℂ) * ζ ^ 6 - ((1757 / 474) : ℂ) * ζ ^ 8 - ((7411 / 2370) : ℂ) * ζ ^ 9 - ((2569 / 2370) : ℂ) * ζ ^ 11 - ((1757 / 474) : ℂ) * ζ ^ 12 - ((239 / 1185) : ℂ) * ζ ^ 13 + ((823 / 395) : ℂ) * ζ ^ 15 - ((239 / 1185) : ℂ) * ζ ^ 17 - ((131 / 1185) : ℂ) * ζ ^ 18 + ((2182 / 1185) : ℂ) * ζ ^ 21 + ((1568 / 1185) : ℂ) * ζ ^ 22 - ((16 / 395) : ℂ) * ζ ^ 25 - ((2182 / 1185) : ℂ) * ζ ^ 27 + ((1757 / 474) : ℂ) * ζ ^ 28 + ((239 / 1185) : ℂ) * ζ ^ 29 - ((479 / 790) : ℂ) * ζ ^ 30 + ((2569 / 2370) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep03CoefficientIdentity04 :
    row18_reducedY44_combinationStep03Coefficient04 =
      row18_reducedY44_combinationStep02Coefficient04 +
        row18_reducedY44_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep03Coefficient04 row18_reducedY44_combinationStep02Coefficient04 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep03Coefficient05 : ℂ :=
  (-((59 / 158) : ℂ) + ((85 / 79) : ℂ) * ζ ^ 1 - ((457 / 474) : ℂ) * ζ ^ 2 - ((71 / 237) : ℂ) * ζ ^ 5 - ((140 / 237) : ℂ) * ζ ^ 6 - ((140 / 237) : ℂ) * ζ ^ 8 - ((71 / 237) : ℂ) * ζ ^ 9 - ((307 / 158) : ℂ) * ζ ^ 11 - ((89 / 79) : ℂ) * ζ ^ 12 - ((85 / 79) : ℂ) * ζ ^ 13 - ((122 / 237) : ℂ) * ζ ^ 15 - ((85 / 79) : ℂ) * ζ ^ 17 + ((1 / 6) : ℂ) * ζ ^ 18 - ((92 / 237) : ℂ) * ζ ^ 21 + ((457 / 474) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 24 + ((326 / 237) : ℂ) * ζ ^ 25 + ((122 / 237) : ℂ) * ζ ^ 27 + ((140 / 237) : ℂ) * ζ ^ 28 + ((85 / 79) : ℂ) * ζ ^ 29 + ((127 / 237) : ℂ) * ζ ^ 30 + ((307 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep03CoefficientIdentity05 :
    row18_reducedY44_combinationStep03Coefficient05 =
      row18_reducedY44_combinationStep02Coefficient05 +
        row18_reducedY44_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep03Coefficient05 row18_reducedY44_combinationStep02Coefficient05 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 (((3697 / 12482) : ℂ) - ((42763 / 37446) : ℂ) * ζ ^ 1 + ((14939 / 37446) : ℂ) * ζ ^ 2 - ((10295 / 12482) : ℂ) * ζ ^ 3 - ((48317 / 37446) : ℂ) * ζ ^ 4 + ((7073 / 6241) : ℂ) * ζ ^ 5 - ((3923 / 37446) : ℂ) * ζ ^ 6 - ((44689 / 37446) : ℂ) * ζ ^ 7 + ((45767 / 37446) : ℂ) * ζ ^ 8 - ((4056 / 6241) : ℂ) * ζ ^ 9 - ((4178 / 18723) : ℂ) * ζ ^ 10 + ((13594 / 18723) : ℂ) * ζ ^ 11 + ((5576 / 18723) : ℂ) * ζ ^ 12 + ((6263 / 6241) : ℂ) * ζ ^ 13 + ((47353 / 37446) : ℂ) * ζ ^ 14 - ((7917 / 6241) : ℂ) * ζ ^ 15 - ((9933 / 6241) : ℂ) * ζ ^ 16 - ((3542 / 6241) : ℂ) * ζ ^ 17 - ((22328 / 18723) : ℂ) * ζ ^ 18 - ((1827 / 6241) : ℂ) * ζ ^ 19 + ((11345 / 18723) : ℂ) * ζ ^ 20 - ((3359 / 37446) : ℂ) * ζ ^ 21 + ((22817 / 37446) : ℂ) * ζ ^ 22 + ((44719 / 37446) : ℂ) * ζ ^ 23 + ((4429 / 37446) : ℂ) * ζ ^ 24 - ((2985 / 12482) : ℂ) * ζ ^ 25 - ((23833 / 37446) : ℂ) * ζ ^ 26 + ((220 / 6241) : ℂ) * ζ ^ 27 - ((5585 / 37446) : ℂ) * ζ ^ 28 + ((5419 / 18723) : ℂ) * ζ ^ 29 - ((791 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep03Coefficient06 : ℂ :=
  (-((1492 / 395) : ℂ) - ((1311 / 158) : ℂ) * ζ ^ 1 - ((3914 / 395) : ℂ) * ζ ^ 2 - ((1369 / 237) : ℂ) * ζ ^ 3 + ((3022 / 1185) : ℂ) * ζ ^ 6 - ((4642 / 1185) : ℂ) * ζ ^ 8 - ((2959 / 474) : ℂ) * ζ ^ 9 + ((1367 / 158) : ℂ) * ζ ^ 11 + ((14764 / 1185) : ℂ) * ζ ^ 12 + ((1311 / 158) : ℂ) * ζ ^ 13 - ((1369 / 237) : ℂ) * ζ ^ 15 + ((1311 / 158) : ℂ) * ζ ^ 17 + ((2422 / 395) : ℂ) * ζ ^ 18 + ((1311 / 158) : ℂ) * ζ ^ 21 + ((3914 / 395) : ℂ) * ζ ^ 22 - ((3914 / 395) : ℂ) * ζ ^ 24 - ((1311 / 158) : ℂ) * ζ ^ 25 + ((1367 / 158) : ℂ) * ζ ^ 27 + ((4642 / 1185) : ℂ) * ζ ^ 28 - ((1311 / 158) : ℂ) * ζ ^ 29 - ((16384 / 1185) : ℂ) * ζ ^ 30 - ((1367 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep03CoefficientIdentity06 :
    row18_reducedY44_combinationStep03Coefficient06 =
      row18_reducedY44_combinationStep02Coefficient06 +
        row18_reducedY44_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep03Coefficient06 row18_reducedY44_combinationStep02Coefficient06 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep03Coefficient07 : ℂ :=
  (((2339 / 474) : ℂ) + ((758 / 237) : ℂ) * ζ ^ 1 - ((545 / 237) : ℂ) * ζ ^ 2 - ((2513 / 474) : ℂ) * ζ ^ 3 + ((1477 / 474) : ℂ) * ζ ^ 5 + ((385 / 237) : ℂ) * ζ ^ 6 - ((860 / 237) : ℂ) * ζ ^ 8 - ((1067 / 474) : ℂ) * ζ ^ 9 + ((241 / 79) : ℂ) * ζ ^ 11 - ((860 / 237) : ℂ) * ζ ^ 12 - ((758 / 237) : ℂ) * ζ ^ 13 + ((1237 / 237) : ℂ) * ζ ^ 15 - ((758 / 237) : ℂ) * ζ ^ 17 - ((310 / 79) : ℂ) * ζ ^ 18 + ((997 / 474) : ℂ) * ζ ^ 21 + ((545 / 237) : ℂ) * ζ ^ 22 + ((13 / 158) : ℂ) * ζ ^ 25 - ((997 / 474) : ℂ) * ζ ^ 27 + ((860 / 237) : ℂ) * ζ ^ 28 + ((758 / 237) : ℂ) * ζ ^ 29 + ((385 / 474) : ℂ) * ζ ^ 30 - ((241 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep03CoefficientIdentity07 :
    row18_reducedY44_combinationStep03Coefficient07 =
      row18_reducedY44_combinationStep02Coefficient07 +
        row18_reducedY44_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep03Coefficient07 row18_reducedY44_combinationStep02Coefficient07 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 (-((58541 / 12482) : ℂ) - ((35557 / 12482) : ℂ) * ζ ^ 1 + ((50117 / 18723) : ℂ) * ζ ^ 2 + ((31936 / 6241) : ℂ) * ζ ^ 3 + ((170303 / 37446) : ℂ) * ζ ^ 4 + ((2063 / 18723) : ℂ) * ζ ^ 5 - ((51173 / 12482) : ℂ) * ζ ^ 6 - ((28764 / 6241) : ℂ) * ζ ^ 7 - ((38987 / 37446) : ℂ) * ζ ^ 8 + ((51961 / 37446) : ℂ) * ζ ^ 9 + ((28327 / 12482) : ℂ) * ζ ^ 10 + ((26567 / 18723) : ℂ) * ζ ^ 11 - ((5201 / 12482) : ℂ) * ζ ^ 12 - ((11188 / 6241) : ℂ) * ζ ^ 13 - ((15533 / 18723) : ℂ) * ζ ^ 14 - ((20767 / 37446) : ℂ) * ζ ^ 15 - ((815 / 37446) : ℂ) * ζ ^ 16 + ((33851 / 37446) : ℂ) * ζ ^ 17 + ((9259 / 6241) : ℂ) * ζ ^ 18 + ((20938 / 18723) : ℂ) * ζ ^ 19 - ((1667 / 6241) : ℂ) * ζ ^ 20 - ((12365 / 6241) : ℂ) * ζ ^ 21 - ((10411 / 6241) : ℂ) * ζ ^ 22 - ((11321 / 37446) : ℂ) * ζ ^ 23 + ((7 / 6) : ℂ) * ζ ^ 24 + ((36985 / 18723) : ℂ) * ζ ^ 25 + ((24550 / 18723) : ℂ) * ζ ^ 26 - ((32443 / 37446) : ℂ) * ζ ^ 27 - ((17948 / 18723) : ℂ) * ζ ^ 28 - ((1417 / 12482) : ℂ) * ζ ^ 29 + ((565 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep03CoefficientIdentity08 :
    row18_reducedY44_combinationStep03Coefficient08 =
      row18_reducedY44_combinationStep02Coefficient08 +
        row18_reducedY44_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep03Coefficient08 row18_reducedY44_combinationStep02Coefficient08 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep03CoefficientIdentity09 :
    row18_reducedY44_combinationStep03Coefficient09 =
      row18_reducedY44_combinationStep02Coefficient09 +
        row18_reducedY44_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep03Coefficient09 row18_reducedY44_combinationStep02Coefficient09 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep03CoefficientIdentity10 :
    row18_reducedY44_combinationStep03Coefficient10 =
      row18_reducedY44_combinationStep02Coefficient10 +
        row18_reducedY44_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep03Coefficient10 row18_reducedY44_combinationStep02Coefficient10 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep03CoefficientIdentity11 :
    row18_reducedY44_combinationStep03Coefficient11 =
      row18_reducedY44_combinationStep02Coefficient11 +
        row18_reducedY44_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep03Coefficient11 row18_reducedY44_combinationStep02Coefficient11 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep03CoefficientIdentity12 :
    row18_reducedY44_combinationStep03Coefficient12 =
      row18_reducedY44_combinationStep02Coefficient12 +
        row18_reducedY44_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep03Coefficient12 row18_reducedY44_combinationStep02Coefficient12 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep03CoefficientIdentity13 :
    row18_reducedY44_combinationStep03Coefficient13 =
      row18_reducedY44_combinationStep02Coefficient13 +
        row18_reducedY44_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep03Coefficient13 row18_reducedY44_combinationStep02Coefficient13 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep03CoefficientIdentity14 :
    row18_reducedY44_combinationStep03Coefficient14 =
      row18_reducedY44_combinationStep02Coefficient14 +
        row18_reducedY44_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep03Coefficient14 row18_reducedY44_combinationStep02Coefficient14 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep03CoefficientIdentity15 :
    row18_reducedY44_combinationStep03Coefficient15 =
      row18_reducedY44_combinationStep02Coefficient15 +
        row18_reducedY44_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep03Coefficient15 row18_reducedY44_combinationStep02Coefficient15 row18_reducedY44_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY44_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY44_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY44_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY44_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY44_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY44_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY44_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY44_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY44_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY44_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY44_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY44_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY44_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY44_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY44_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY44_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY44_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY44_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY44_combinationStep03CoefficientIdentity00,
      row18_reducedY44_combinationStep03CoefficientIdentity01,
      row18_reducedY44_combinationStep03CoefficientIdentity02,
      row18_reducedY44_combinationStep03CoefficientIdentity03,
      row18_reducedY44_combinationStep03CoefficientIdentity04,
      row18_reducedY44_combinationStep03CoefficientIdentity05,
      row18_reducedY44_combinationStep03CoefficientIdentity06,
      row18_reducedY44_combinationStep03CoefficientIdentity07,
      row18_reducedY44_combinationStep03CoefficientIdentity08,
      row18_reducedY44_combinationStep03CoefficientIdentity09,
      row18_reducedY44_combinationStep03CoefficientIdentity10,
      row18_reducedY44_combinationStep03CoefficientIdentity11,
      row18_reducedY44_combinationStep03CoefficientIdentity12,
      row18_reducedY44_combinationStep03CoefficientIdentity13,
      row18_reducedY44_combinationStep03CoefficientIdentity14,
      row18_reducedY44_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY44_combinationStep03Multiplier * equation

private def row18_reducedY44_combinationStep04Multiplier : ℂ :=
  (-((58 / 237) : ℂ) + ((128 / 237) : ℂ) * ζ ^ 1 + ((118 / 79) : ℂ) * ζ ^ 2 + ((106 / 237) : ℂ) * ζ ^ 3 - ((20 / 237) : ℂ) * ζ ^ 5 + ((2 / 237) : ℂ) * ζ ^ 8 - ((154 / 237) : ℂ) * ζ ^ 9 + ((16 / 79) : ℂ) * ζ ^ 11 + ((38 / 79) : ℂ) * ζ ^ 12 - ((128 / 237) : ℂ) * ζ ^ 13 + ((14 / 79) : ℂ) * ζ ^ 15 - ((128 / 237) : ℂ) * ζ ^ 17 - ((118 / 79) : ℂ) * ζ ^ 18 - ((22 / 237) : ℂ) * ζ ^ 21 - ((118 / 79) : ℂ) * ζ ^ 22 - ((116 / 237) : ℂ) * ζ ^ 24 + ((148 / 237) : ℂ) * ζ ^ 25 - ((22 / 237) : ℂ) * ζ ^ 27 - ((2 / 237) : ℂ) * ζ ^ 28 + ((128 / 237) : ℂ) * ζ ^ 29 + ((54 / 79) : ℂ) * ζ ^ 30 - ((16 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY44_combinationStep04Coefficient00 : ℂ :=
  (-((282 / 79) : ℂ) - ((488 / 395) : ℂ) * ζ ^ 1 + ((926 / 395) : ℂ) * ζ ^ 2 + ((1649 / 790) : ℂ) * ζ ^ 3 - ((853 / 790) : ℂ) * ζ ^ 5 + ((304 / 395) : ℂ) * ζ ^ 6 + ((309 / 79) : ℂ) * ζ ^ 8 + ((1857 / 790) : ℂ) * ζ ^ 9 + ((104 / 395) : ℂ) * ζ ^ 11 + ((309 / 79) : ℂ) * ζ ^ 12 + ((488 / 395) : ℂ) * ζ ^ 13 - ((763 / 395) : ℂ) * ζ ^ 15 + ((488 / 395) : ℂ) * ζ ^ 17 + ((622 / 395) : ℂ) * ζ ^ 18 - ((673 / 790) : ℂ) * ζ ^ 21 - ((926 / 395) : ℂ) * ζ ^ 22 - ((123 / 790) : ℂ) * ζ ^ 25 + ((673 / 790) : ℂ) * ζ ^ 27 - ((309 / 79) : ℂ) * ζ ^ 28 - ((488 / 395) : ℂ) * ζ ^ 29 + ((152 / 395) : ℂ) * ζ ^ 30 - ((104 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep04CoefficientIdentity00 :
    row18_reducedY44_combinationStep04Coefficient00 =
      row18_reducedY44_combinationStep03Coefficient00 +
        row18_reducedY44_combinationStep04Multiplier *
          (-((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((57 / 158) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((57 / 158) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((57 / 158) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep04Coefficient00 row18_reducedY44_combinationStep03Coefficient00 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 (((25349 / 37446) : ℂ) - ((23 / 158) : ℂ) * ζ ^ 1 - ((379 / 6241) : ℂ) * ζ ^ 2 - ((9 / 158) : ℂ) * ζ ^ 3 - ((786 / 6241) : ℂ) * ζ ^ 4 + ((1 / 474) : ℂ) * ζ ^ 5 - ((518 / 6241) : ℂ) * ζ ^ 6 - ((5 / 79) : ℂ) * ζ ^ 7 + ((13651 / 37446) : ℂ) * ζ ^ 8 + ((14 / 237) : ℂ) * ζ ^ 9 + ((953 / 12482) : ℂ) * ζ ^ 10 + ((4 / 79) : ℂ) * ζ ^ 11 + ((10411 / 18723) : ℂ) * ζ ^ 12 + ((11 / 79) : ℂ) * ζ ^ 13 + ((3418 / 18723) : ℂ) * ζ ^ 14 - ((131 / 474) : ℂ) * ζ ^ 15 + ((1045 / 37446) : ℂ) * ζ ^ 16 + ((7 / 237) : ℂ) * ζ ^ 17 + ((1763 / 18723) : ℂ) * ζ ^ 18 - ((1 / 3) : ℂ) * ζ ^ 19 - ((9289 / 37446) : ℂ) * ζ ^ 20 + ((14 / 237) : ℂ) * ζ ^ 21 - ((249 / 12482) : ℂ) * ζ ^ 22 + ((20 / 237) : ℂ) * ζ ^ 23 - ((2515 / 37446) : ℂ) * ζ ^ 24 - ((1 / 237) : ℂ) * ζ ^ 25 + ((56 / 6241) : ℂ) * ζ ^ 26 + ((23 / 474) : ℂ) * ζ ^ 27 - ((94 / 18723) : ℂ) * ζ ^ 28 - ((3 / 79) : ℂ) * ζ ^ 29 + ((56 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep04Coefficient01 : ℂ :=
  (-((33 / 158) : ℂ) + ((23 / 158) : ℂ) * ζ ^ 1 - ((7 / 158) : ℂ) * ζ ^ 2 - ((14 / 79) : ℂ) * ζ ^ 3 + ((23 / 158) : ℂ) * ζ ^ 5 - ((20 / 79) : ℂ) * ζ ^ 6 + ((20 / 79) : ℂ) * ζ ^ 8 - ((23 / 158) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((45 / 158) : ℂ) * ζ ^ 12 - ((23 / 158) : ℂ) * ζ ^ 13 - ((11 / 158) : ℂ) * ζ ^ 15 - ((23 / 158) : ℂ) * ζ ^ 17 + ((16 / 79) : ℂ) * ζ ^ 18 - ((29 / 79) : ℂ) * ζ ^ 21 + ((7 / 158) : ℂ) * ζ ^ 22 - ((4 / 79) : ℂ) * ζ ^ 24 - ((39 / 158) : ℂ) * ζ ^ 27 - ((20 / 79) : ℂ) * ζ ^ 28 + ((23 / 158) : ℂ) * ζ ^ 29 + ((5 / 158) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep04CoefficientIdentity01 :
    row18_reducedY44_combinationStep04Coefficient01 =
      row18_reducedY44_combinationStep03Coefficient01 +
        row18_reducedY44_combinationStep04Multiplier *
          (-((5 / 79) : ℂ) - ((43 / 316) : ℂ) * ζ ^ 1 - ((9 / 158) : ℂ) * ζ ^ 2 - ((63 / 316) : ℂ) * ζ ^ 5 + ((1 / 158) : ℂ) * ζ ^ 6 + ((1 / 158) : ℂ) * ζ ^ 8 - ((63 / 316) : ℂ) * ζ ^ 9 + ((57 / 158) : ℂ) * ζ ^ 11 + ((31 / 316) : ℂ) * ζ ^ 12 + ((43 / 316) : ℂ) * ζ ^ 13 - ((3 / 79) : ℂ) * ζ ^ 15 + ((43 / 316) : ℂ) * ζ ^ 17 - ((3 / 316) : ℂ) * ζ ^ 18 + ((53 / 316) : ℂ) * ζ ^ 21 + ((9 / 158) : ℂ) * ζ ^ 22 + ((1 / 316) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((1 / 158) : ℂ) * ζ ^ 28 - ((43 / 316) : ℂ) * ζ ^ 29 - ((29 / 316) : ℂ) * ζ ^ 30 - ((57 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep04Coefficient01 row18_reducedY44_combinationStep03Coefficient01 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 (-((3028 / 18723) : ℂ) - ((9062 / 18723) : ℂ) * ζ ^ 1 - ((16435 / 37446) : ℂ) * ζ ^ 2 - ((11245 / 37446) : ℂ) * ζ ^ 3 + ((197 / 12482) : ℂ) * ζ ^ 4 + ((7 / 237) : ℂ) * ζ ^ 5 - ((2263 / 18723) : ℂ) * ζ ^ 6 + ((67 / 6241) : ℂ) * ζ ^ 7 + ((4549 / 12482) : ℂ) * ζ ^ 8 + ((20543 / 37446) : ℂ) * ζ ^ 9 + ((4771 / 37446) : ℂ) * ζ ^ 10 - ((6578 / 18723) : ℂ) * ζ ^ 11 - ((953 / 12482) : ℂ) * ζ ^ 12 - ((449 / 12482) : ℂ) * ζ ^ 13 + ((142 / 18723) : ℂ) * ζ ^ 14 + ((659 / 6241) : ℂ) * ζ ^ 15 - ((2324 / 18723) : ℂ) * ζ ^ 16 - ((1373 / 12482) : ℂ) * ζ ^ 17 + ((4033 / 37446) : ℂ) * ζ ^ 18 + ((473 / 12482) : ℂ) * ζ ^ 19 + ((3208 / 18723) : ℂ) * ζ ^ 20 + ((6196 / 18723) : ℂ) * ζ ^ 21 + ((2192 / 18723) : ℂ) * ζ ^ 22 + ((11249 / 37446) : ℂ) * ζ ^ 23 + ((470 / 18723) : ℂ) * ζ ^ 24 + ((1624 / 6241) : ℂ) * ζ ^ 25 - ((4655 / 37446) : ℂ) * ζ ^ 26 - ((5177 / 37446) : ℂ) * ζ ^ 27 - ((2871 / 12482) : ℂ) * ζ ^ 28 - ((1423 / 6241) : ℂ) * ζ ^ 29 + ((456 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep04Coefficient02 : ℂ :=
  (((297 / 79) : ℂ) + ((262 / 237) : ℂ) * ζ ^ 1 + ((360 / 79) : ℂ) * ζ ^ 2 - ((994 / 237) : ℂ) * ζ ^ 3 - ((820 / 237) : ℂ) * ζ ^ 5 + ((3025 / 474) : ℂ) * ζ ^ 6 - ((199 / 237) : ℂ) * ζ ^ 8 - ((224 / 79) : ℂ) * ζ ^ 9 - ((2125 / 474) : ℂ) * ζ ^ 11 - ((865 / 474) : ℂ) * ζ ^ 12 - ((262 / 237) : ℂ) * ζ ^ 13 + ((994 / 237) : ℂ) * ζ ^ 15 - ((262 / 237) : ℂ) * ζ ^ 17 - ((657 / 79) : ℂ) * ζ ^ 18 + ((1082 / 237) : ℂ) * ζ ^ 21 - ((360 / 79) : ℂ) * ζ ^ 22 - ((360 / 79) : ℂ) * ζ ^ 24 + ((1082 / 237) : ℂ) * ζ ^ 25 + ((2125 / 474) : ℂ) * ζ ^ 27 + ((199 / 237) : ℂ) * ζ ^ 28 + ((262 / 237) : ℂ) * ζ ^ 29 + ((1279 / 237) : ℂ) * ζ ^ 30 + ((2125 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep04CoefficientIdentity02 :
    row18_reducedY44_combinationStep04Coefficient02 =
      row18_reducedY44_combinationStep03Coefficient02 +
        row18_reducedY44_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep04Coefficient02 row18_reducedY44_combinationStep03Coefficient02 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep04Coefficient03 : ℂ :=
  (-((503 / 79) : ℂ) - ((487 / 237) : ℂ) * ζ ^ 1 + ((283 / 237) : ℂ) * ζ ^ 2 + ((1313 / 237) : ℂ) * ζ ^ 3 - ((931 / 474) : ℂ) * ζ ^ 5 - ((85 / 79) : ℂ) * ζ ^ 6 + ((1495 / 474) : ℂ) * ζ ^ 8 + ((477 / 158) : ℂ) * ζ ^ 9 - ((1195 / 474) : ℂ) * ζ ^ 11 + ((1495 / 474) : ℂ) * ζ ^ 12 + ((487 / 237) : ℂ) * ζ ^ 13 - ((861 / 158) : ℂ) * ζ ^ 15 + ((487 / 237) : ℂ) * ζ ^ 17 + ((538 / 237) : ℂ) * ζ ^ 18 - ((826 / 237) : ℂ) * ζ ^ 21 - ((283 / 237) : ℂ) * ζ ^ 22 - ((43 / 474) : ℂ) * ζ ^ 25 + ((826 / 237) : ℂ) * ζ ^ 27 - ((1495 / 474) : ℂ) * ζ ^ 28 - ((487 / 237) : ℂ) * ζ ^ 29 - ((85 / 158) : ℂ) * ζ ^ 30 + ((1195 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep04CoefficientIdentity03 :
    row18_reducedY44_combinationStep04Coefficient03 =
      row18_reducedY44_combinationStep03Coefficient03 +
        row18_reducedY44_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep04Coefficient03 row18_reducedY44_combinationStep03Coefficient03 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep04Coefficient04 : ℂ :=
  (((1028 / 237) : ℂ) + ((239 / 1185) : ℂ) * ζ ^ 1 - ((1568 / 1185) : ℂ) * ζ ^ 2 - ((807 / 395) : ℂ) * ζ ^ 3 + ((287 / 1185) : ℂ) * ζ ^ 5 - ((479 / 395) : ℂ) * ζ ^ 6 - ((1757 / 474) : ℂ) * ζ ^ 8 - ((7411 / 2370) : ℂ) * ζ ^ 9 - ((2569 / 2370) : ℂ) * ζ ^ 11 - ((1757 / 474) : ℂ) * ζ ^ 12 - ((239 / 1185) : ℂ) * ζ ^ 13 + ((823 / 395) : ℂ) * ζ ^ 15 - ((239 / 1185) : ℂ) * ζ ^ 17 - ((131 / 1185) : ℂ) * ζ ^ 18 + ((2182 / 1185) : ℂ) * ζ ^ 21 + ((1568 / 1185) : ℂ) * ζ ^ 22 - ((16 / 395) : ℂ) * ζ ^ 25 - ((2182 / 1185) : ℂ) * ζ ^ 27 + ((1757 / 474) : ℂ) * ζ ^ 28 + ((239 / 1185) : ℂ) * ζ ^ 29 - ((479 / 790) : ℂ) * ζ ^ 30 + ((2569 / 2370) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep04CoefficientIdentity04 :
    row18_reducedY44_combinationStep04Coefficient04 =
      row18_reducedY44_combinationStep03Coefficient04 +
        row18_reducedY44_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep04Coefficient04 row18_reducedY44_combinationStep03Coefficient04 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep04Coefficient05 : ℂ :=
  (-((59 / 158) : ℂ) + ((85 / 79) : ℂ) * ζ ^ 1 - ((457 / 474) : ℂ) * ζ ^ 2 - ((71 / 237) : ℂ) * ζ ^ 5 - ((140 / 237) : ℂ) * ζ ^ 6 - ((140 / 237) : ℂ) * ζ ^ 8 - ((71 / 237) : ℂ) * ζ ^ 9 - ((307 / 158) : ℂ) * ζ ^ 11 - ((89 / 79) : ℂ) * ζ ^ 12 - ((85 / 79) : ℂ) * ζ ^ 13 - ((122 / 237) : ℂ) * ζ ^ 15 - ((85 / 79) : ℂ) * ζ ^ 17 + ((1 / 6) : ℂ) * ζ ^ 18 - ((92 / 237) : ℂ) * ζ ^ 21 + ((457 / 474) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 24 + ((326 / 237) : ℂ) * ζ ^ 25 + ((122 / 237) : ℂ) * ζ ^ 27 + ((140 / 237) : ℂ) * ζ ^ 28 + ((85 / 79) : ℂ) * ζ ^ 29 + ((127 / 237) : ℂ) * ζ ^ 30 + ((307 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep04CoefficientIdentity05 :
    row18_reducedY44_combinationStep04Coefficient05 =
      row18_reducedY44_combinationStep03Coefficient05 +
        row18_reducedY44_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep04Coefficient05 row18_reducedY44_combinationStep03Coefficient05 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep04Coefficient06 : ℂ :=
  (-((1492 / 395) : ℂ) - ((1311 / 158) : ℂ) * ζ ^ 1 - ((3914 / 395) : ℂ) * ζ ^ 2 - ((1369 / 237) : ℂ) * ζ ^ 3 + ((3022 / 1185) : ℂ) * ζ ^ 6 - ((4642 / 1185) : ℂ) * ζ ^ 8 - ((2959 / 474) : ℂ) * ζ ^ 9 + ((1367 / 158) : ℂ) * ζ ^ 11 + ((14764 / 1185) : ℂ) * ζ ^ 12 + ((1311 / 158) : ℂ) * ζ ^ 13 - ((1369 / 237) : ℂ) * ζ ^ 15 + ((1311 / 158) : ℂ) * ζ ^ 17 + ((2422 / 395) : ℂ) * ζ ^ 18 + ((1311 / 158) : ℂ) * ζ ^ 21 + ((3914 / 395) : ℂ) * ζ ^ 22 - ((3914 / 395) : ℂ) * ζ ^ 24 - ((1311 / 158) : ℂ) * ζ ^ 25 + ((1367 / 158) : ℂ) * ζ ^ 27 + ((4642 / 1185) : ℂ) * ζ ^ 28 - ((1311 / 158) : ℂ) * ζ ^ 29 - ((16384 / 1185) : ℂ) * ζ ^ 30 - ((1367 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep04CoefficientIdentity06 :
    row18_reducedY44_combinationStep04Coefficient06 =
      row18_reducedY44_combinationStep03Coefficient06 +
        row18_reducedY44_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep04Coefficient06 row18_reducedY44_combinationStep03Coefficient06 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep04Coefficient07 : ℂ :=
  (((2339 / 474) : ℂ) + ((758 / 237) : ℂ) * ζ ^ 1 - ((545 / 237) : ℂ) * ζ ^ 2 - ((2513 / 474) : ℂ) * ζ ^ 3 + ((1477 / 474) : ℂ) * ζ ^ 5 + ((385 / 237) : ℂ) * ζ ^ 6 - ((860 / 237) : ℂ) * ζ ^ 8 - ((1067 / 474) : ℂ) * ζ ^ 9 + ((241 / 79) : ℂ) * ζ ^ 11 - ((860 / 237) : ℂ) * ζ ^ 12 - ((758 / 237) : ℂ) * ζ ^ 13 + ((1237 / 237) : ℂ) * ζ ^ 15 - ((758 / 237) : ℂ) * ζ ^ 17 - ((310 / 79) : ℂ) * ζ ^ 18 + ((997 / 474) : ℂ) * ζ ^ 21 + ((545 / 237) : ℂ) * ζ ^ 22 + ((13 / 158) : ℂ) * ζ ^ 25 - ((997 / 474) : ℂ) * ζ ^ 27 + ((860 / 237) : ℂ) * ζ ^ 28 + ((758 / 237) : ℂ) * ζ ^ 29 + ((385 / 474) : ℂ) * ζ ^ 30 - ((241 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep04CoefficientIdentity07 :
    row18_reducedY44_combinationStep04Coefficient07 =
      row18_reducedY44_combinationStep03Coefficient07 +
        row18_reducedY44_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep04Coefficient07 row18_reducedY44_combinationStep03Coefficient07 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep04Coefficient08 : ℂ :=
  (((105 / 158) : ℂ) - ((26 / 237) : ℂ) * ζ ^ 1 + ((20 / 237) : ℂ) * ζ ^ 2 - ((67 / 237) : ℂ) * ζ ^ 3 - ((149 / 474) : ℂ) * ζ ^ 5 - ((25 / 237) : ℂ) * ζ ^ 6 + ((64 / 237) : ℂ) * ζ ^ 8 + ((2 / 237) : ℂ) * ζ ^ 9 + ((23 / 79) : ℂ) * ζ ^ 11 + ((64 / 237) : ℂ) * ζ ^ 12 + ((26 / 237) : ℂ) * ζ ^ 13 + ((37 / 474) : ℂ) * ζ ^ 15 + ((26 / 237) : ℂ) * ζ ^ 17 + ((15 / 79) : ℂ) * ζ ^ 18 + ((31 / 79) : ℂ) * ζ ^ 21 - ((20 / 237) : ℂ) * ζ ^ 22 + ((97 / 474) : ℂ) * ζ ^ 25 - ((31 / 79) : ℂ) * ζ ^ 27 - ((64 / 237) : ℂ) * ζ ^ 28 - ((26 / 237) : ℂ) * ζ ^ 29 - ((25 / 474) : ℂ) * ζ ^ 30 - ((23 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep04CoefficientIdentity08 :
    row18_reducedY44_combinationStep04Coefficient08 =
      row18_reducedY44_combinationStep03Coefficient08 +
        row18_reducedY44_combinationStep04Multiplier *
          (((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((57 / 158) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((57 / 158) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((57 / 158) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep04Coefficient08 row18_reducedY44_combinationStep03Coefficient08 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 (-((25349 / 37446) : ℂ) + ((23 / 158) : ℂ) * ζ ^ 1 + ((379 / 6241) : ℂ) * ζ ^ 2 + ((9 / 158) : ℂ) * ζ ^ 3 + ((786 / 6241) : ℂ) * ζ ^ 4 - ((1 / 474) : ℂ) * ζ ^ 5 + ((518 / 6241) : ℂ) * ζ ^ 6 + ((5 / 79) : ℂ) * ζ ^ 7 - ((13651 / 37446) : ℂ) * ζ ^ 8 - ((14 / 237) : ℂ) * ζ ^ 9 - ((953 / 12482) : ℂ) * ζ ^ 10 - ((4 / 79) : ℂ) * ζ ^ 11 - ((10411 / 18723) : ℂ) * ζ ^ 12 - ((11 / 79) : ℂ) * ζ ^ 13 - ((3418 / 18723) : ℂ) * ζ ^ 14 + ((131 / 474) : ℂ) * ζ ^ 15 - ((1045 / 37446) : ℂ) * ζ ^ 16 - ((7 / 237) : ℂ) * ζ ^ 17 - ((1763 / 18723) : ℂ) * ζ ^ 18 + ((1 / 3) : ℂ) * ζ ^ 19 + ((9289 / 37446) : ℂ) * ζ ^ 20 - ((14 / 237) : ℂ) * ζ ^ 21 + ((249 / 12482) : ℂ) * ζ ^ 22 - ((20 / 237) : ℂ) * ζ ^ 23 + ((2515 / 37446) : ℂ) * ζ ^ 24 + ((1 / 237) : ℂ) * ζ ^ 25 - ((56 / 6241) : ℂ) * ζ ^ 26 - ((23 / 474) : ℂ) * ζ ^ 27 + ((94 / 18723) : ℂ) * ζ ^ 28 + ((3 / 79) : ℂ) * ζ ^ 29 - ((56 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep04Coefficient09 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep04CoefficientIdentity09 :
    row18_reducedY44_combinationStep04Coefficient09 =
      row18_reducedY44_combinationStep03Coefficient09 +
        row18_reducedY44_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep04Coefficient09 row18_reducedY44_combinationStep03Coefficient09 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep04Coefficient10 : ℂ :=
  (((35 / 237) : ℂ) - ((19 / 237) : ℂ) * ζ ^ 1 - ((112 / 237) : ℂ) * ζ ^ 2 - ((9 / 79) : ℂ) * ζ ^ 3 - ((24 / 79) : ℂ) * ζ ^ 5 - ((23 / 237) : ℂ) * ζ ^ 6 - ((19 / 237) : ℂ) * ζ ^ 8 - ((17 / 237) : ℂ) * ζ ^ 9 - ((32 / 237) : ℂ) * ζ ^ 11 - ((89 / 237) : ℂ) * ζ ^ 12 + ((19 / 237) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 + ((19 / 237) : ℂ) * ζ ^ 17 + ((77 / 237) : ℂ) * ζ ^ 18 + ((53 / 237) : ℂ) * ζ ^ 21 + ((112 / 237) : ℂ) * ζ ^ 22 + ((112 / 237) : ℂ) * ζ ^ 24 + ((53 / 237) : ℂ) * ζ ^ 25 + ((32 / 237) : ℂ) * ζ ^ 27 + ((19 / 237) : ℂ) * ζ ^ 28 - ((19 / 237) : ℂ) * ζ ^ 29 - ((31 / 79) : ℂ) * ζ ^ 30 + ((32 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep04CoefficientIdentity10 :
    row18_reducedY44_combinationStep04Coefficient10 =
      row18_reducedY44_combinationStep03Coefficient10 +
        row18_reducedY44_combinationStep04Multiplier *
          (-((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep04Coefficient10 row18_reducedY44_combinationStep03Coefficient10 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 (-((1576 / 18723) : ℂ) - ((2623 / 37446) : ℂ) * ζ ^ 1 + ((2500 / 18723) : ℂ) * ζ ^ 2 + ((247 / 12482) : ℂ) * ζ ^ 3 - ((47 / 474) : ℂ) * ζ ^ 4 + ((37 / 158) : ℂ) * ζ ^ 5 - ((31 / 474) : ℂ) * ζ ^ 6 - ((1105 / 37446) : ℂ) * ζ ^ 7 + ((3157 / 37446) : ℂ) * ζ ^ 8 + ((5711 / 37446) : ℂ) * ζ ^ 9 + ((7475 / 37446) : ℂ) * ζ ^ 10 - ((3403 / 37446) : ℂ) * ζ ^ 11 + ((805 / 18723) : ℂ) * ζ ^ 12 - ((2269 / 37446) : ℂ) * ζ ^ 13 - ((529 / 18723) : ℂ) * ζ ^ 14 - ((575 / 37446) : ℂ) * ζ ^ 15 - ((4490 / 18723) : ℂ) * ζ ^ 16 + ((811 / 37446) : ℂ) * ζ ^ 17 + ((4555 / 18723) : ℂ) * ζ ^ 18 - ((1552 / 18723) : ℂ) * ζ ^ 19 + ((2225 / 18723) : ℂ) * ζ ^ 20 - ((747 / 6241) : ℂ) * ζ ^ 21 + ((1000 / 18723) : ℂ) * ζ ^ 22 + ((1133 / 37446) : ℂ) * ζ ^ 23 - ((1459 / 37446) : ℂ) * ζ ^ 24 - ((568 / 18723) : ℂ) * ζ ^ 25 - ((4691 / 37446) : ℂ) * ζ ^ 26 + ((710 / 6241) : ℂ) * ζ ^ 27 + ((305 / 12482) : ℂ) * ζ ^ 28 - ((621 / 12482) : ℂ) * ζ ^ 29 + ((60 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep04Coefficient11 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep04CoefficientIdentity11 :
    row18_reducedY44_combinationStep04Coefficient11 =
      row18_reducedY44_combinationStep03Coefficient11 +
        row18_reducedY44_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep04Coefficient11 row18_reducedY44_combinationStep03Coefficient11 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep04Coefficient12 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep04CoefficientIdentity12 :
    row18_reducedY44_combinationStep04Coefficient12 =
      row18_reducedY44_combinationStep03Coefficient12 +
        row18_reducedY44_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep04Coefficient12 row18_reducedY44_combinationStep03Coefficient12 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep04Coefficient13 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep04CoefficientIdentity13 :
    row18_reducedY44_combinationStep04Coefficient13 =
      row18_reducedY44_combinationStep03Coefficient13 +
        row18_reducedY44_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep04Coefficient13 row18_reducedY44_combinationStep03Coefficient13 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep04Coefficient14 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep04CoefficientIdentity14 :
    row18_reducedY44_combinationStep04Coefficient14 =
      row18_reducedY44_combinationStep03Coefficient14 +
        row18_reducedY44_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep04Coefficient14 row18_reducedY44_combinationStep03Coefficient14 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep04Coefficient15 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep04CoefficientIdentity15 :
    row18_reducedY44_combinationStep04Coefficient15 =
      row18_reducedY44_combinationStep03Coefficient15 +
        row18_reducedY44_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep04Coefficient15 row18_reducedY44_combinationStep03Coefficient15 row18_reducedY44_combinationStep04Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY44_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY44_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY44_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY44_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY44_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY44_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY44_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY44_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY44_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY44_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY44_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY44_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY44_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY44_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY44_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY44_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY44_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY44_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation04
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY44_combinationStep04CoefficientIdentity00,
      row18_reducedY44_combinationStep04CoefficientIdentity01,
      row18_reducedY44_combinationStep04CoefficientIdentity02,
      row18_reducedY44_combinationStep04CoefficientIdentity03,
      row18_reducedY44_combinationStep04CoefficientIdentity04,
      row18_reducedY44_combinationStep04CoefficientIdentity05,
      row18_reducedY44_combinationStep04CoefficientIdentity06,
      row18_reducedY44_combinationStep04CoefficientIdentity07,
      row18_reducedY44_combinationStep04CoefficientIdentity08,
      row18_reducedY44_combinationStep04CoefficientIdentity09,
      row18_reducedY44_combinationStep04CoefficientIdentity10,
      row18_reducedY44_combinationStep04CoefficientIdentity11,
      row18_reducedY44_combinationStep04CoefficientIdentity12,
      row18_reducedY44_combinationStep04CoefficientIdentity13,
      row18_reducedY44_combinationStep04CoefficientIdentity14,
      row18_reducedY44_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY44_combinationStep04Multiplier * equation

private def row18_reducedY44_combinationStep05Multiplier : ℂ :=
  (-((14 / 79) : ℂ) - ((120 / 79) : ℂ) * ζ ^ 1 - ((218 / 79) : ℂ) * ζ ^ 2 + ((52 / 79) : ℂ) * ζ ^ 5 - ((204 / 79) : ℂ) * ζ ^ 6 - ((204 / 79) : ℂ) * ζ ^ 8 + ((52 / 79) : ℂ) * ζ ^ 9 + ((94 / 79) : ℂ) * ζ ^ 11 - ((2 / 79) : ℂ) * ζ ^ 12 + ((120 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 + ((120 / 79) : ℂ) * ζ ^ 17 + ((148 / 79) : ℂ) * ζ ^ 18 + ((34 / 79) : ℂ) * ζ ^ 21 + ((218 / 79) : ℂ) * ζ ^ 22 + ((56 / 79) : ℂ) * ζ ^ 24 - ((172 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((204 / 79) : ℂ) * ζ ^ 28 - ((120 / 79) : ℂ) * ζ ^ 29 - ((202 / 79) : ℂ) * ζ ^ 30 - ((94 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY44_combinationStep05Coefficient00 : ℂ :=
  (-((249 / 79) : ℂ) - ((608 / 395) : ℂ) * ζ ^ 1 + ((1757 / 790) : ℂ) * ζ ^ 2 + ((1017 / 395) : ℂ) * ζ ^ 3 - ((379 / 395) : ℂ) * ζ ^ 5 + ((314 / 395) : ℂ) * ζ ^ 6 + ((623 / 158) : ℂ) * ζ ^ 8 + ((1166 / 395) : ℂ) * ζ ^ 9 + ((149 / 395) : ℂ) * ζ ^ 11 + ((623 / 158) : ℂ) * ζ ^ 12 + ((608 / 395) : ℂ) * ζ ^ 13 - ((788 / 395) : ℂ) * ζ ^ 15 + ((608 / 395) : ℂ) * ζ ^ 17 + ((1129 / 790) : ℂ) * ζ ^ 18 - ((409 / 395) : ℂ) * ζ ^ 21 - ((1757 / 790) : ℂ) * ζ ^ 22 - ((229 / 395) : ℂ) * ζ ^ 25 + ((409 / 395) : ℂ) * ζ ^ 27 - ((623 / 158) : ℂ) * ζ ^ 28 - ((608 / 395) : ℂ) * ζ ^ 29 + ((157 / 395) : ℂ) * ζ ^ 30 - ((149 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep05CoefficientIdentity00 :
    row18_reducedY44_combinationStep05Coefficient00 =
      row18_reducedY44_combinationStep04Coefficient00 +
        row18_reducedY44_combinationStep05Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep05Coefficient00 row18_reducedY44_combinationStep04Coefficient00 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 (-((2474 / 6241) : ℂ) + ((6163 / 12482) : ℂ) * ζ ^ 1 + ((3250 / 6241) : ℂ) * ζ ^ 2 - ((1919 / 6241) : ℂ) * ζ ^ 3 + ((7587 / 12482) : ℂ) * ζ ^ 4 - ((3018 / 6241) : ℂ) * ζ ^ 5 - ((1520 / 6241) : ℂ) * ζ ^ 6 + ((3459 / 6241) : ℂ) * ζ ^ 7 - ((315 / 12482) : ℂ) * ζ ^ 8 - ((1635 / 12482) : ℂ) * ζ ^ 9 + ((2433 / 12482) : ℂ) * ζ ^ 10 + ((203 / 12482) : ℂ) * ζ ^ 11 - ((1748 / 6241) : ℂ) * ζ ^ 12 + ((1205 / 6241) : ℂ) * ζ ^ 13 - ((837 / 12482) : ℂ) * ζ ^ 14 + ((894 / 6241) : ℂ) * ζ ^ 15 + ((247 / 12482) : ℂ) * ζ ^ 16 + ((163 / 6241) : ℂ) * ζ ^ 17 + ((1985 / 12482) : ℂ) * ζ ^ 18 - ((1125 / 6241) : ℂ) * ζ ^ 19 + ((871 / 12482) : ℂ) * ζ ^ 20 + ((706 / 6241) : ℂ) * ζ ^ 21 - ((3236 / 6241) : ℂ) * ζ ^ 22 + ((2 / 79) : ℂ) * ζ ^ 23 - ((710 / 6241) : ℂ) * ζ ^ 24 + ((240 / 6241) : ℂ) * ζ ^ 25 + ((10525 / 12482) : ℂ) * ζ ^ 26 - ((162 / 6241) : ℂ) * ζ ^ 27 - ((3337 / 12482) : ℂ) * ζ ^ 28 - ((741 / 12482) : ℂ) * ζ ^ 29 + ((705 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep05Coefficient01 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep05CoefficientIdentity01 :
    row18_reducedY44_combinationStep05Coefficient01 =
      row18_reducedY44_combinationStep04Coefficient01 +
        row18_reducedY44_combinationStep05Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep05Coefficient01 row18_reducedY44_combinationStep04Coefficient01 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 (-((2719 / 12482) : ℂ) + ((390 / 6241) : ℂ) * ζ ^ 1 - ((1601 / 6241) : ℂ) * ζ ^ 2 - ((2752 / 6241) : ℂ) * ζ ^ 3 - ((518 / 6241) : ℂ) * ζ ^ 4 + ((676 / 6241) : ℂ) * ζ ^ 5 - ((1552 / 6241) : ℂ) * ζ ^ 6 + ((1011 / 6241) : ℂ) * ζ ^ 7 - ((495 / 6241) : ℂ) * ζ ^ 8 - ((1661 / 6241) : ℂ) * ζ ^ 9 + ((1017 / 6241) : ℂ) * ζ ^ 10 - ((893 / 12482) : ℂ) * ζ ^ 11 + ((1643 / 12482) : ℂ) * ζ ^ 12 + ((887 / 6241) : ℂ) * ζ ^ 13 - ((55 / 6241) : ℂ) * ζ ^ 14 - ((204 / 6241) : ℂ) * ζ ^ 15 - ((886 / 6241) : ℂ) * ζ ^ 16 + ((638 / 6241) : ℂ) * ζ ^ 17 + ((2889 / 12482) : ℂ) * ζ ^ 18 + ((2551 / 12482) : ℂ) * ζ ^ 19 + ((5915 / 12482) : ℂ) * ζ ^ 20 - ((4831 / 12482) : ℂ) * ζ ^ 21 - ((1303 / 6241) : ℂ) * ζ ^ 22 + ((594 / 6241) : ℂ) * ζ ^ 23 + ((2049 / 6241) : ℂ) * ζ ^ 24 + ((442 / 6241) : ℂ) * ζ ^ 25 + ((72 / 6241) : ℂ) * ζ ^ 26 - ((3541 / 12482) : ℂ) * ζ ^ 27 - ((889 / 12482) : ℂ) * ζ ^ 28 + ((425 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep05Coefficient02 : ℂ :=
  (((297 / 79) : ℂ) + ((262 / 237) : ℂ) * ζ ^ 1 + ((360 / 79) : ℂ) * ζ ^ 2 - ((994 / 237) : ℂ) * ζ ^ 3 - ((820 / 237) : ℂ) * ζ ^ 5 + ((3025 / 474) : ℂ) * ζ ^ 6 - ((199 / 237) : ℂ) * ζ ^ 8 - ((224 / 79) : ℂ) * ζ ^ 9 - ((2125 / 474) : ℂ) * ζ ^ 11 - ((865 / 474) : ℂ) * ζ ^ 12 - ((262 / 237) : ℂ) * ζ ^ 13 + ((994 / 237) : ℂ) * ζ ^ 15 - ((262 / 237) : ℂ) * ζ ^ 17 - ((657 / 79) : ℂ) * ζ ^ 18 + ((1082 / 237) : ℂ) * ζ ^ 21 - ((360 / 79) : ℂ) * ζ ^ 22 - ((360 / 79) : ℂ) * ζ ^ 24 + ((1082 / 237) : ℂ) * ζ ^ 25 + ((2125 / 474) : ℂ) * ζ ^ 27 + ((199 / 237) : ℂ) * ζ ^ 28 + ((262 / 237) : ℂ) * ζ ^ 29 + ((1279 / 237) : ℂ) * ζ ^ 30 + ((2125 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep05CoefficientIdentity02 :
    row18_reducedY44_combinationStep05Coefficient02 =
      row18_reducedY44_combinationStep04Coefficient02 +
        row18_reducedY44_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep05Coefficient02 row18_reducedY44_combinationStep04Coefficient02 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep05Coefficient03 : ℂ :=
  (-((503 / 79) : ℂ) - ((487 / 237) : ℂ) * ζ ^ 1 + ((283 / 237) : ℂ) * ζ ^ 2 + ((1313 / 237) : ℂ) * ζ ^ 3 - ((931 / 474) : ℂ) * ζ ^ 5 - ((85 / 79) : ℂ) * ζ ^ 6 + ((1495 / 474) : ℂ) * ζ ^ 8 + ((477 / 158) : ℂ) * ζ ^ 9 - ((1195 / 474) : ℂ) * ζ ^ 11 + ((1495 / 474) : ℂ) * ζ ^ 12 + ((487 / 237) : ℂ) * ζ ^ 13 - ((861 / 158) : ℂ) * ζ ^ 15 + ((487 / 237) : ℂ) * ζ ^ 17 + ((538 / 237) : ℂ) * ζ ^ 18 - ((826 / 237) : ℂ) * ζ ^ 21 - ((283 / 237) : ℂ) * ζ ^ 22 - ((43 / 474) : ℂ) * ζ ^ 25 + ((826 / 237) : ℂ) * ζ ^ 27 - ((1495 / 474) : ℂ) * ζ ^ 28 - ((487 / 237) : ℂ) * ζ ^ 29 - ((85 / 158) : ℂ) * ζ ^ 30 + ((1195 / 474) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep05CoefficientIdentity03 :
    row18_reducedY44_combinationStep05Coefficient03 =
      row18_reducedY44_combinationStep04Coefficient03 +
        row18_reducedY44_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep05Coefficient03 row18_reducedY44_combinationStep04Coefficient03 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep05Coefficient04 : ℂ :=
  (((1028 / 237) : ℂ) + ((239 / 1185) : ℂ) * ζ ^ 1 - ((1568 / 1185) : ℂ) * ζ ^ 2 - ((807 / 395) : ℂ) * ζ ^ 3 + ((287 / 1185) : ℂ) * ζ ^ 5 - ((479 / 395) : ℂ) * ζ ^ 6 - ((1757 / 474) : ℂ) * ζ ^ 8 - ((7411 / 2370) : ℂ) * ζ ^ 9 - ((2569 / 2370) : ℂ) * ζ ^ 11 - ((1757 / 474) : ℂ) * ζ ^ 12 - ((239 / 1185) : ℂ) * ζ ^ 13 + ((823 / 395) : ℂ) * ζ ^ 15 - ((239 / 1185) : ℂ) * ζ ^ 17 - ((131 / 1185) : ℂ) * ζ ^ 18 + ((2182 / 1185) : ℂ) * ζ ^ 21 + ((1568 / 1185) : ℂ) * ζ ^ 22 - ((16 / 395) : ℂ) * ζ ^ 25 - ((2182 / 1185) : ℂ) * ζ ^ 27 + ((1757 / 474) : ℂ) * ζ ^ 28 + ((239 / 1185) : ℂ) * ζ ^ 29 - ((479 / 790) : ℂ) * ζ ^ 30 + ((2569 / 2370) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep05CoefficientIdentity04 :
    row18_reducedY44_combinationStep05Coefficient04 =
      row18_reducedY44_combinationStep04Coefficient04 +
        row18_reducedY44_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep05Coefficient04 row18_reducedY44_combinationStep04Coefficient04 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep05Coefficient05 : ℂ :=
  (-((59 / 158) : ℂ) + ((85 / 79) : ℂ) * ζ ^ 1 - ((457 / 474) : ℂ) * ζ ^ 2 - ((71 / 237) : ℂ) * ζ ^ 5 - ((140 / 237) : ℂ) * ζ ^ 6 - ((140 / 237) : ℂ) * ζ ^ 8 - ((71 / 237) : ℂ) * ζ ^ 9 - ((307 / 158) : ℂ) * ζ ^ 11 - ((89 / 79) : ℂ) * ζ ^ 12 - ((85 / 79) : ℂ) * ζ ^ 13 - ((122 / 237) : ℂ) * ζ ^ 15 - ((85 / 79) : ℂ) * ζ ^ 17 + ((1 / 6) : ℂ) * ζ ^ 18 - ((92 / 237) : ℂ) * ζ ^ 21 + ((457 / 474) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 24 + ((326 / 237) : ℂ) * ζ ^ 25 + ((122 / 237) : ℂ) * ζ ^ 27 + ((140 / 237) : ℂ) * ζ ^ 28 + ((85 / 79) : ℂ) * ζ ^ 29 + ((127 / 237) : ℂ) * ζ ^ 30 + ((307 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep05CoefficientIdentity05 :
    row18_reducedY44_combinationStep05Coefficient05 =
      row18_reducedY44_combinationStep04Coefficient05 +
        row18_reducedY44_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep05Coefficient05 row18_reducedY44_combinationStep04Coefficient05 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep05Coefficient06 : ℂ :=
  (-((1492 / 395) : ℂ) - ((1311 / 158) : ℂ) * ζ ^ 1 - ((3914 / 395) : ℂ) * ζ ^ 2 - ((1369 / 237) : ℂ) * ζ ^ 3 + ((3022 / 1185) : ℂ) * ζ ^ 6 - ((4642 / 1185) : ℂ) * ζ ^ 8 - ((2959 / 474) : ℂ) * ζ ^ 9 + ((1367 / 158) : ℂ) * ζ ^ 11 + ((14764 / 1185) : ℂ) * ζ ^ 12 + ((1311 / 158) : ℂ) * ζ ^ 13 - ((1369 / 237) : ℂ) * ζ ^ 15 + ((1311 / 158) : ℂ) * ζ ^ 17 + ((2422 / 395) : ℂ) * ζ ^ 18 + ((1311 / 158) : ℂ) * ζ ^ 21 + ((3914 / 395) : ℂ) * ζ ^ 22 - ((3914 / 395) : ℂ) * ζ ^ 24 - ((1311 / 158) : ℂ) * ζ ^ 25 + ((1367 / 158) : ℂ) * ζ ^ 27 + ((4642 / 1185) : ℂ) * ζ ^ 28 - ((1311 / 158) : ℂ) * ζ ^ 29 - ((16384 / 1185) : ℂ) * ζ ^ 30 - ((1367 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep05CoefficientIdentity06 :
    row18_reducedY44_combinationStep05Coefficient06 =
      row18_reducedY44_combinationStep04Coefficient06 +
        row18_reducedY44_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep05Coefficient06 row18_reducedY44_combinationStep04Coefficient06 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep05Coefficient07 : ℂ :=
  (((2339 / 474) : ℂ) + ((758 / 237) : ℂ) * ζ ^ 1 - ((545 / 237) : ℂ) * ζ ^ 2 - ((2513 / 474) : ℂ) * ζ ^ 3 + ((1477 / 474) : ℂ) * ζ ^ 5 + ((385 / 237) : ℂ) * ζ ^ 6 - ((860 / 237) : ℂ) * ζ ^ 8 - ((1067 / 474) : ℂ) * ζ ^ 9 + ((241 / 79) : ℂ) * ζ ^ 11 - ((860 / 237) : ℂ) * ζ ^ 12 - ((758 / 237) : ℂ) * ζ ^ 13 + ((1237 / 237) : ℂ) * ζ ^ 15 - ((758 / 237) : ℂ) * ζ ^ 17 - ((310 / 79) : ℂ) * ζ ^ 18 + ((997 / 474) : ℂ) * ζ ^ 21 + ((545 / 237) : ℂ) * ζ ^ 22 + ((13 / 158) : ℂ) * ζ ^ 25 - ((997 / 474) : ℂ) * ζ ^ 27 + ((860 / 237) : ℂ) * ζ ^ 28 + ((758 / 237) : ℂ) * ζ ^ 29 + ((385 / 474) : ℂ) * ζ ^ 30 - ((241 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep05CoefficientIdentity07 :
    row18_reducedY44_combinationStep05Coefficient07 =
      row18_reducedY44_combinationStep04Coefficient07 +
        row18_reducedY44_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep05Coefficient07 row18_reducedY44_combinationStep04Coefficient07 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep05Coefficient08 : ℂ :=
  (((105 / 158) : ℂ) - ((26 / 237) : ℂ) * ζ ^ 1 + ((20 / 237) : ℂ) * ζ ^ 2 - ((67 / 237) : ℂ) * ζ ^ 3 - ((149 / 474) : ℂ) * ζ ^ 5 - ((25 / 237) : ℂ) * ζ ^ 6 + ((64 / 237) : ℂ) * ζ ^ 8 + ((2 / 237) : ℂ) * ζ ^ 9 + ((23 / 79) : ℂ) * ζ ^ 11 + ((64 / 237) : ℂ) * ζ ^ 12 + ((26 / 237) : ℂ) * ζ ^ 13 + ((37 / 474) : ℂ) * ζ ^ 15 + ((26 / 237) : ℂ) * ζ ^ 17 + ((15 / 79) : ℂ) * ζ ^ 18 + ((31 / 79) : ℂ) * ζ ^ 21 - ((20 / 237) : ℂ) * ζ ^ 22 + ((97 / 474) : ℂ) * ζ ^ 25 - ((31 / 79) : ℂ) * ζ ^ 27 - ((64 / 237) : ℂ) * ζ ^ 28 - ((26 / 237) : ℂ) * ζ ^ 29 - ((25 / 474) : ℂ) * ζ ^ 30 - ((23 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep05CoefficientIdentity08 :
    row18_reducedY44_combinationStep05Coefficient08 =
      row18_reducedY44_combinationStep04Coefficient08 +
        row18_reducedY44_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep05Coefficient08 row18_reducedY44_combinationStep04Coefficient08 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep05Coefficient09 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep05CoefficientIdentity09 :
    row18_reducedY44_combinationStep05Coefficient09 =
      row18_reducedY44_combinationStep04Coefficient09 +
        row18_reducedY44_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep05Coefficient09 row18_reducedY44_combinationStep04Coefficient09 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep05Coefficient10 : ℂ :=
  (((35 / 237) : ℂ) - ((19 / 237) : ℂ) * ζ ^ 1 - ((112 / 237) : ℂ) * ζ ^ 2 - ((9 / 79) : ℂ) * ζ ^ 3 - ((24 / 79) : ℂ) * ζ ^ 5 - ((23 / 237) : ℂ) * ζ ^ 6 - ((19 / 237) : ℂ) * ζ ^ 8 - ((17 / 237) : ℂ) * ζ ^ 9 - ((32 / 237) : ℂ) * ζ ^ 11 - ((89 / 237) : ℂ) * ζ ^ 12 + ((19 / 237) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 + ((19 / 237) : ℂ) * ζ ^ 17 + ((77 / 237) : ℂ) * ζ ^ 18 + ((53 / 237) : ℂ) * ζ ^ 21 + ((112 / 237) : ℂ) * ζ ^ 22 + ((112 / 237) : ℂ) * ζ ^ 24 + ((53 / 237) : ℂ) * ζ ^ 25 + ((32 / 237) : ℂ) * ζ ^ 27 + ((19 / 237) : ℂ) * ζ ^ 28 - ((19 / 237) : ℂ) * ζ ^ 29 - ((31 / 79) : ℂ) * ζ ^ 30 + ((32 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep05CoefficientIdentity10 :
    row18_reducedY44_combinationStep05Coefficient10 =
      row18_reducedY44_combinationStep04Coefficient10 +
        row18_reducedY44_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep05Coefficient10 row18_reducedY44_combinationStep04Coefficient10 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep05Coefficient11 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep05CoefficientIdentity11 :
    row18_reducedY44_combinationStep05Coefficient11 =
      row18_reducedY44_combinationStep04Coefficient11 +
        row18_reducedY44_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep05Coefficient11 row18_reducedY44_combinationStep04Coefficient11 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep05Coefficient12 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep05CoefficientIdentity12 :
    row18_reducedY44_combinationStep05Coefficient12 =
      row18_reducedY44_combinationStep04Coefficient12 +
        row18_reducedY44_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep05Coefficient12 row18_reducedY44_combinationStep04Coefficient12 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep05Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep05CoefficientIdentity13 :
    row18_reducedY44_combinationStep05Coefficient13 =
      row18_reducedY44_combinationStep04Coefficient13 +
        row18_reducedY44_combinationStep05Multiplier *
          (-((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((73 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((105 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((73 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep05Coefficient13 row18_reducedY44_combinationStep04Coefficient13 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 (-((3276 / 6241) : ℂ) - ((625 / 12482) : ℂ) * ζ ^ 1 + ((689 / 6241) : ℂ) * ζ ^ 2 - ((3167 / 12482) : ℂ) * ζ ^ 3 - ((1285 / 12482) : ℂ) * ζ ^ 4 - ((117 / 6241) : ℂ) * ζ ^ 5 + ((5201 / 12482) : ℂ) * ζ ^ 6 + ((3018 / 6241) : ℂ) * ζ ^ 7 + ((4811 / 12482) : ℂ) * ζ ^ 8 - ((784 / 6241) : ℂ) * ζ ^ 9 - ((8487 / 6241) : ℂ) * ζ ^ 10 - ((4803 / 12482) : ℂ) * ζ ^ 11 + ((6691 / 12482) : ℂ) * ζ ^ 12 + ((178 / 6241) : ℂ) * ζ ^ 13 + ((6775 / 6241) : ℂ) * ζ ^ 14 - ((4021 / 12482) : ℂ) * ζ ^ 15 - ((19101 / 12482) : ℂ) * ζ ^ 16 - ((4973 / 12482) : ℂ) * ζ ^ 17 - ((4376 / 6241) : ℂ) * ζ ^ 18 + ((66 / 6241) : ℂ) * ζ ^ 19 + ((8447 / 12482) : ℂ) * ζ ^ 20 + ((551 / 6241) : ℂ) * ζ ^ 21 - ((119 / 6241) : ℂ) * ζ ^ 22 + ((550 / 6241) : ℂ) * ζ ^ 23 - ((2929 / 12482) : ℂ) * ζ ^ 24 + ((445 / 12482) : ℂ) * ζ ^ 25 + ((1398 / 6241) : ℂ) * ζ ^ 26 + ((1144 / 6241) : ℂ) * ζ ^ 27 + ((2973 / 12482) : ℂ) * ζ ^ 28 + ((1083 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep05Coefficient14 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep05CoefficientIdentity14 :
    row18_reducedY44_combinationStep05Coefficient14 =
      row18_reducedY44_combinationStep04Coefficient14 +
        row18_reducedY44_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep05Coefficient14 row18_reducedY44_combinationStep04Coefficient14 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep05Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep05CoefficientIdentity15 :
    row18_reducedY44_combinationStep05Coefficient15 =
      row18_reducedY44_combinationStep04Coefficient15 +
        row18_reducedY44_combinationStep05Multiplier *
          (((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep05Coefficient15 row18_reducedY44_combinationStep04Coefficient15 row18_reducedY44_combinationStep05Multiplier
  close_cyclotomic_row18 (((2474 / 6241) : ℂ) - ((6163 / 12482) : ℂ) * ζ ^ 1 - ((3250 / 6241) : ℂ) * ζ ^ 2 + ((1919 / 6241) : ℂ) * ζ ^ 3 - ((7587 / 12482) : ℂ) * ζ ^ 4 + ((3018 / 6241) : ℂ) * ζ ^ 5 + ((1520 / 6241) : ℂ) * ζ ^ 6 - ((3459 / 6241) : ℂ) * ζ ^ 7 + ((315 / 12482) : ℂ) * ζ ^ 8 + ((1635 / 12482) : ℂ) * ζ ^ 9 - ((2433 / 12482) : ℂ) * ζ ^ 10 - ((203 / 12482) : ℂ) * ζ ^ 11 + ((1748 / 6241) : ℂ) * ζ ^ 12 - ((1205 / 6241) : ℂ) * ζ ^ 13 + ((837 / 12482) : ℂ) * ζ ^ 14 - ((894 / 6241) : ℂ) * ζ ^ 15 - ((247 / 12482) : ℂ) * ζ ^ 16 - ((163 / 6241) : ℂ) * ζ ^ 17 - ((1985 / 12482) : ℂ) * ζ ^ 18 + ((1125 / 6241) : ℂ) * ζ ^ 19 - ((871 / 12482) : ℂ) * ζ ^ 20 - ((706 / 6241) : ℂ) * ζ ^ 21 + ((3236 / 6241) : ℂ) * ζ ^ 22 - ((2 / 79) : ℂ) * ζ ^ 23 + ((710 / 6241) : ℂ) * ζ ^ 24 - ((240 / 6241) : ℂ) * ζ ^ 25 - ((10525 / 12482) : ℂ) * ζ ^ 26 + ((162 / 6241) : ℂ) * ζ ^ 27 + ((3337 / 12482) : ℂ) * ζ ^ 28 + ((741 / 12482) : ℂ) * ζ ^ 29 - ((705 / 12482) : ℂ) * ζ ^ 30)

private theorem row18_reducedY44_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY44_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY44_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY44_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY44_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY44_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY44_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY44_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY44_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY44_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY44_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY44_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY44_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY44_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY44_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY44_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY44_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY44_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation07
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY44_combinationStep05CoefficientIdentity00,
      row18_reducedY44_combinationStep05CoefficientIdentity01,
      row18_reducedY44_combinationStep05CoefficientIdentity02,
      row18_reducedY44_combinationStep05CoefficientIdentity03,
      row18_reducedY44_combinationStep05CoefficientIdentity04,
      row18_reducedY44_combinationStep05CoefficientIdentity05,
      row18_reducedY44_combinationStep05CoefficientIdentity06,
      row18_reducedY44_combinationStep05CoefficientIdentity07,
      row18_reducedY44_combinationStep05CoefficientIdentity08,
      row18_reducedY44_combinationStep05CoefficientIdentity09,
      row18_reducedY44_combinationStep05CoefficientIdentity10,
      row18_reducedY44_combinationStep05CoefficientIdentity11,
      row18_reducedY44_combinationStep05CoefficientIdentity12,
      row18_reducedY44_combinationStep05CoefficientIdentity13,
      row18_reducedY44_combinationStep05CoefficientIdentity14,
      row18_reducedY44_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY44_combinationStep05Multiplier * equation

private def row18_reducedY44_combinationStep06Multiplier : ℂ :=
  (-((14806 / 1185) : ℂ) - ((14956 / 1185) : ℂ) * ζ ^ 1 + ((8302 / 1185) : ℂ) * ζ ^ 2 + ((1930 / 237) : ℂ) * ζ ^ 3 - ((15928 / 1185) : ℂ) * ζ ^ 5 - ((6752 / 1185) : ℂ) * ζ ^ 6 + ((11228 / 1185) : ℂ) * ζ ^ 8 + ((6992 / 1185) : ℂ) * ζ ^ 9 - ((1370 / 237) : ℂ) * ζ ^ 11 + ((5018 / 395) : ℂ) * ζ ^ 12 + ((14956 / 1185) : ℂ) * ζ ^ 13 - ((1930 / 237) : ℂ) * ζ ^ 15 + ((14956 / 1185) : ℂ) * ζ ^ 17 + ((2168 / 395) : ℂ) * ζ ^ 18 + ((324 / 395) : ℂ) * ζ ^ 21 - ((8302 / 1185) : ℂ) * ζ ^ 22 - ((8302 / 1185) : ℂ) * ζ ^ 24 + ((324 / 395) : ℂ) * ζ ^ 25 + ((1370 / 237) : ℂ) * ζ ^ 27 - ((11228 / 1185) : ℂ) * ζ ^ 28 - ((14956 / 1185) : ℂ) * ζ ^ 29 - ((2926 / 1185) : ℂ) * ζ ^ 30 + ((1370 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY44_combinationStep06Coefficient00 : ℂ :=
  (-((249 / 79) : ℂ) - ((608 / 395) : ℂ) * ζ ^ 1 + ((1757 / 790) : ℂ) * ζ ^ 2 + ((1017 / 395) : ℂ) * ζ ^ 3 - ((379 / 395) : ℂ) * ζ ^ 5 + ((314 / 395) : ℂ) * ζ ^ 6 + ((623 / 158) : ℂ) * ζ ^ 8 + ((1166 / 395) : ℂ) * ζ ^ 9 + ((149 / 395) : ℂ) * ζ ^ 11 + ((623 / 158) : ℂ) * ζ ^ 12 + ((608 / 395) : ℂ) * ζ ^ 13 - ((788 / 395) : ℂ) * ζ ^ 15 + ((608 / 395) : ℂ) * ζ ^ 17 + ((1129 / 790) : ℂ) * ζ ^ 18 - ((409 / 395) : ℂ) * ζ ^ 21 - ((1757 / 790) : ℂ) * ζ ^ 22 - ((229 / 395) : ℂ) * ζ ^ 25 + ((409 / 395) : ℂ) * ζ ^ 27 - ((623 / 158) : ℂ) * ζ ^ 28 - ((608 / 395) : ℂ) * ζ ^ 29 + ((157 / 395) : ℂ) * ζ ^ 30 - ((149 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep06CoefficientIdentity00 :
    row18_reducedY44_combinationStep06Coefficient00 =
      row18_reducedY44_combinationStep05Coefficient00 +
        row18_reducedY44_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep06Coefficient00 row18_reducedY44_combinationStep05Coefficient00 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep06Coefficient01 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep06CoefficientIdentity01 :
    row18_reducedY44_combinationStep06Coefficient01 =
      row18_reducedY44_combinationStep05Coefficient01 +
        row18_reducedY44_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep06Coefficient01 row18_reducedY44_combinationStep05Coefficient01 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep06Coefficient02 : ℂ :=
  (((6361 / 2370) : ℂ) + ((1774 / 1185) : ℂ) * ζ ^ 1 + ((7343 / 2370) : ℂ) * ζ ^ 2 - ((179 / 237) : ℂ) * ζ ^ 3 - ((4088 / 1185) : ℂ) * ζ ^ 5 + ((12437 / 2370) : ℂ) * ζ ^ 6 + ((449 / 790) : ℂ) * ζ ^ 8 - ((3818 / 1185) : ℂ) * ζ ^ 9 - ((1324 / 237) : ℂ) * ζ ^ 11 - ((849 / 395) : ℂ) * ζ ^ 12 - ((1774 / 1185) : ℂ) * ζ ^ 13 + ((179 / 237) : ℂ) * ζ ^ 15 - ((1774 / 1185) : ℂ) * ζ ^ 17 - ((2284 / 395) : ℂ) * ζ ^ 18 + ((1954 / 395) : ℂ) * ζ ^ 21 - ((7343 / 2370) : ℂ) * ζ ^ 22 - ((7343 / 2370) : ℂ) * ζ ^ 24 + ((1954 / 395) : ℂ) * ζ ^ 25 + ((1324 / 237) : ℂ) * ζ ^ 27 - ((449 / 790) : ℂ) * ζ ^ 28 + ((1774 / 1185) : ℂ) * ζ ^ 29 + ((2998 / 1185) : ℂ) * ζ ^ 30 + ((1324 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep06CoefficientIdentity02 :
    row18_reducedY44_combinationStep06Coefficient02 =
      row18_reducedY44_combinationStep05Coefficient02 +
        row18_reducedY44_combinationStep06Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep06Coefficient02 row18_reducedY44_combinationStep05Coefficient02 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 (((290207 / 187230) : ℂ) - ((65009 / 187230) : ℂ) * ζ ^ 1 + ((385144 / 93615) : ℂ) * ζ ^ 2 - ((2351 / 12482) : ℂ) * ζ ^ 3 - ((201641 / 62410) : ℂ) * ζ ^ 4 - ((20497 / 37446) : ℂ) * ζ ^ 5 - ((21640 / 18723) : ℂ) * ζ ^ 6 + ((417748 / 93615) : ℂ) * ζ ^ 7 + ((30676 / 93615) : ℂ) * ζ ^ 8 - ((9293 / 12482) : ℂ) * ζ ^ 9 + ((164003 / 187230) : ℂ) * ζ ^ 10 - ((55341 / 31205) : ℂ) * ζ ^ 11 + ((32159 / 93615) : ℂ) * ζ ^ 12 - ((191933 / 187230) : ℂ) * ζ ^ 13 - ((66773 / 187230) : ℂ) * ζ ^ 14 + ((44447 / 12482) : ℂ) * ζ ^ 15 + ((142129 / 187230) : ℂ) * ζ ^ 16 + ((78422 / 93615) : ℂ) * ζ ^ 17 + ((22267 / 93615) : ℂ) * ζ ^ 18 - ((51629 / 18723) : ℂ) * ζ ^ 19 - ((43807 / 62410) : ℂ) * ζ ^ 20 - ((199519 / 187230) : ℂ) * ζ ^ 21 - ((211349 / 187230) : ℂ) * ζ ^ 22 - ((207721 / 187230) : ℂ) * ζ ^ 23 + ((145057 / 93615) : ℂ) * ζ ^ 24 + ((201439 / 187230) : ℂ) * ζ ^ 25 + ((17216 / 31205) : ℂ) * ζ ^ 26 - ((47458 / 93615) : ℂ) * ζ ^ 27 - ((43609 / 187230) : ℂ) * ζ ^ 28 - ((12547 / 31205) : ℂ) * ζ ^ 29 + ((4795 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep06Coefficient03 : ℂ :=
  (-((1228 / 237) : ℂ) - ((268 / 79) : ℂ) * ζ ^ 1 + ((331 / 158) : ℂ) * ζ ^ 2 + ((1439 / 237) : ℂ) * ζ ^ 3 - ((1271 / 474) : ℂ) * ζ ^ 5 - ((118 / 79) : ℂ) * ζ ^ 6 + ((1607 / 474) : ℂ) * ζ ^ 8 + ((674 / 237) : ℂ) * ζ ^ 9 - ((255 / 79) : ℂ) * ζ ^ 11 + ((1607 / 474) : ℂ) * ζ ^ 12 + ((268 / 79) : ℂ) * ζ ^ 13 - ((847 / 158) : ℂ) * ζ ^ 15 + ((268 / 79) : ℂ) * ζ ^ 17 + ((567 / 158) : ℂ) * ζ ^ 18 - ((635 / 237) : ℂ) * ζ ^ 21 - ((331 / 158) : ℂ) * ζ ^ 22 - ((337 / 474) : ℂ) * ζ ^ 25 + ((635 / 237) : ℂ) * ζ ^ 27 - ((1607 / 474) : ℂ) * ζ ^ 28 - ((268 / 79) : ℂ) * ζ ^ 29 - ((59 / 79) : ℂ) * ζ ^ 30 + ((255 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep06CoefficientIdentity03 :
    row18_reducedY44_combinationStep06Coefficient03 =
      row18_reducedY44_combinationStep05Coefficient03 +
        row18_reducedY44_combinationStep06Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep06Coefficient03 row18_reducedY44_combinationStep05Coefficient03 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 (-((732797 / 187230) : ℂ) + ((363703 / 187230) : ℂ) * ζ ^ 1 + ((228919 / 62410) : ℂ) * ζ ^ 2 - ((12641 / 6241) : ℂ) * ζ ^ 3 + ((55201 / 62410) : ℂ) * ζ ^ 4 + ((1687 / 187230) : ℂ) * ζ ^ 5 + ((1273 / 12482) : ℂ) * ζ ^ 6 - ((68321 / 37446) : ℂ) * ζ ^ 7 + ((215581 / 93615) : ℂ) * ζ ^ 8 + ((7547 / 37446) : ℂ) * ζ ^ 9 - ((548197 / 187230) : ℂ) * ζ ^ 10 + ((10235 / 12482) : ℂ) * ζ ^ 11 + ((57434 / 93615) : ℂ) * ζ ^ 12 - ((219422 / 93615) : ℂ) * ζ ^ 13 - ((246421 / 93615) : ℂ) * ζ ^ 14 - ((263249 / 187230) : ℂ) * ζ ^ 15 + ((84797 / 37446) : ℂ) * ζ ^ 16 - ((145031 / 187230) : ℂ) * ζ ^ 17 - ((479078 / 93615) : ℂ) * ζ ^ 18 - ((8665 / 12482) : ℂ) * ζ ^ 19 - ((86981 / 62410) : ℂ) * ζ ^ 20 - ((80858 / 31205) : ℂ) * ζ ^ 21 - ((219307 / 62410) : ℂ) * ζ ^ 22 + ((687383 / 187230) : ℂ) * ζ ^ 23 - ((157591 / 93615) : ℂ) * ζ ^ 24 - ((98779 / 187230) : ℂ) * ζ ^ 25 + ((8192 / 6241) : ℂ) * ζ ^ 26 - ((85289 / 187230) : ℂ) * ζ ^ 27 - ((467341 / 187230) : ℂ) * ζ ^ 28 + ((165931 / 187230) : ℂ) * ζ ^ 29 + ((8905 / 37446) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep06Coefficient04 : ℂ :=
  (((249 / 79) : ℂ) + ((608 / 395) : ℂ) * ζ ^ 1 - ((1757 / 790) : ℂ) * ζ ^ 2 - ((1017 / 395) : ℂ) * ζ ^ 3 + ((379 / 395) : ℂ) * ζ ^ 5 - ((314 / 395) : ℂ) * ζ ^ 6 - ((623 / 158) : ℂ) * ζ ^ 8 - ((1166 / 395) : ℂ) * ζ ^ 9 - ((149 / 395) : ℂ) * ζ ^ 11 - ((623 / 158) : ℂ) * ζ ^ 12 - ((608 / 395) : ℂ) * ζ ^ 13 + ((788 / 395) : ℂ) * ζ ^ 15 - ((608 / 395) : ℂ) * ζ ^ 17 - ((1129 / 790) : ℂ) * ζ ^ 18 + ((409 / 395) : ℂ) * ζ ^ 21 + ((1757 / 790) : ℂ) * ζ ^ 22 + ((229 / 395) : ℂ) * ζ ^ 25 - ((409 / 395) : ℂ) * ζ ^ 27 + ((623 / 158) : ℂ) * ζ ^ 28 + ((608 / 395) : ℂ) * ζ ^ 29 - ((157 / 395) : ℂ) * ζ ^ 30 + ((149 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep06CoefficientIdentity04 :
    row18_reducedY44_combinationStep06Coefficient04 =
      row18_reducedY44_combinationStep05Coefficient04 +
        row18_reducedY44_combinationStep06Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep06Coefficient04 row18_reducedY44_combinationStep05Coefficient04 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 (((732797 / 187230) : ℂ) - ((363703 / 187230) : ℂ) * ζ ^ 1 - ((228919 / 62410) : ℂ) * ζ ^ 2 + ((12641 / 6241) : ℂ) * ζ ^ 3 - ((55201 / 62410) : ℂ) * ζ ^ 4 - ((1687 / 187230) : ℂ) * ζ ^ 5 - ((1273 / 12482) : ℂ) * ζ ^ 6 + ((68321 / 37446) : ℂ) * ζ ^ 7 - ((215581 / 93615) : ℂ) * ζ ^ 8 - ((7547 / 37446) : ℂ) * ζ ^ 9 + ((548197 / 187230) : ℂ) * ζ ^ 10 - ((10235 / 12482) : ℂ) * ζ ^ 11 - ((57434 / 93615) : ℂ) * ζ ^ 12 + ((219422 / 93615) : ℂ) * ζ ^ 13 + ((246421 / 93615) : ℂ) * ζ ^ 14 + ((263249 / 187230) : ℂ) * ζ ^ 15 - ((84797 / 37446) : ℂ) * ζ ^ 16 + ((145031 / 187230) : ℂ) * ζ ^ 17 + ((479078 / 93615) : ℂ) * ζ ^ 18 + ((8665 / 12482) : ℂ) * ζ ^ 19 + ((86981 / 62410) : ℂ) * ζ ^ 20 + ((80858 / 31205) : ℂ) * ζ ^ 21 + ((219307 / 62410) : ℂ) * ζ ^ 22 - ((687383 / 187230) : ℂ) * ζ ^ 23 + ((157591 / 93615) : ℂ) * ζ ^ 24 + ((98779 / 187230) : ℂ) * ζ ^ 25 - ((8192 / 6241) : ℂ) * ζ ^ 26 + ((85289 / 187230) : ℂ) * ζ ^ 27 + ((467341 / 187230) : ℂ) * ζ ^ 28 - ((165931 / 187230) : ℂ) * ζ ^ 29 - ((8905 / 37446) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep06Coefficient05 : ℂ :=
  (-((59 / 158) : ℂ) + ((85 / 79) : ℂ) * ζ ^ 1 - ((457 / 474) : ℂ) * ζ ^ 2 - ((71 / 237) : ℂ) * ζ ^ 5 - ((140 / 237) : ℂ) * ζ ^ 6 - ((140 / 237) : ℂ) * ζ ^ 8 - ((71 / 237) : ℂ) * ζ ^ 9 - ((307 / 158) : ℂ) * ζ ^ 11 - ((89 / 79) : ℂ) * ζ ^ 12 - ((85 / 79) : ℂ) * ζ ^ 13 - ((122 / 237) : ℂ) * ζ ^ 15 - ((85 / 79) : ℂ) * ζ ^ 17 + ((1 / 6) : ℂ) * ζ ^ 18 - ((92 / 237) : ℂ) * ζ ^ 21 + ((457 / 474) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 24 + ((326 / 237) : ℂ) * ζ ^ 25 + ((122 / 237) : ℂ) * ζ ^ 27 + ((140 / 237) : ℂ) * ζ ^ 28 + ((85 / 79) : ℂ) * ζ ^ 29 + ((127 / 237) : ℂ) * ζ ^ 30 + ((307 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep06CoefficientIdentity05 :
    row18_reducedY44_combinationStep06Coefficient05 =
      row18_reducedY44_combinationStep05Coefficient05 +
        row18_reducedY44_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep06Coefficient05 row18_reducedY44_combinationStep05Coefficient05 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep06Coefficient06 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep06CoefficientIdentity06 :
    row18_reducedY44_combinationStep06Coefficient06 =
      row18_reducedY44_combinationStep05Coefficient06 +
        row18_reducedY44_combinationStep06Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep06Coefficient06 row18_reducedY44_combinationStep05Coefficient06 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 (-((235156 / 93615) : ℂ) - ((446134 / 93615) : ℂ) * ζ ^ 1 - ((30585 / 12482) : ℂ) * ζ ^ 2 - ((154721 / 31205) : ℂ) * ζ ^ 3 - ((166503 / 31205) : ℂ) * ζ ^ 4 + ((245552 / 31205) : ℂ) * ζ ^ 5 + ((260260 / 18723) : ℂ) * ζ ^ 6 + ((316766 / 31205) : ℂ) * ζ ^ 7 - ((292978 / 93615) : ℂ) * ζ ^ 8 - ((88212 / 6241) : ℂ) * ζ ^ 9 - ((1011442 / 93615) : ℂ) * ζ ^ 10 - ((257059 / 93615) : ℂ) * ζ ^ 11 + ((261824 / 31205) : ℂ) * ζ ^ 12 + ((904639 / 93615) : ℂ) * ζ ^ 13 + ((130421 / 187230) : ℂ) * ζ ^ 14 - ((127911 / 31205) : ℂ) * ζ ^ 15 - ((732592 / 93615) : ℂ) * ζ ^ 16 - ((520099 / 62410) : ℂ) * ζ ^ 17 - ((39094 / 6241) : ℂ) * ζ ^ 18 - ((102761 / 37446) : ℂ) * ζ ^ 19 + ((1993999 / 187230) : ℂ) * ζ ^ 20 + ((155503 / 31205) : ℂ) * ζ ^ 21 - ((359791 / 93615) : ℂ) * ζ ^ 22 - ((1705 / 237) : ℂ) * ζ ^ 23 - ((1052363 / 187230) : ℂ) * ζ ^ 24 + ((28788 / 31205) : ℂ) * ζ ^ 25 + ((518744 / 93615) : ℂ) * ζ ^ 26 + ((75791 / 37446) : ℂ) * ζ ^ 27 + ((49271 / 187230) : ℂ) * ζ ^ 28 - ((20618 / 93615) : ℂ) * ζ ^ 29 - ((9590 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep06Coefficient07 : ℂ :=
  (((2339 / 474) : ℂ) + ((758 / 237) : ℂ) * ζ ^ 1 - ((545 / 237) : ℂ) * ζ ^ 2 - ((2513 / 474) : ℂ) * ζ ^ 3 + ((1477 / 474) : ℂ) * ζ ^ 5 + ((385 / 237) : ℂ) * ζ ^ 6 - ((860 / 237) : ℂ) * ζ ^ 8 - ((1067 / 474) : ℂ) * ζ ^ 9 + ((241 / 79) : ℂ) * ζ ^ 11 - ((860 / 237) : ℂ) * ζ ^ 12 - ((758 / 237) : ℂ) * ζ ^ 13 + ((1237 / 237) : ℂ) * ζ ^ 15 - ((758 / 237) : ℂ) * ζ ^ 17 - ((310 / 79) : ℂ) * ζ ^ 18 + ((997 / 474) : ℂ) * ζ ^ 21 + ((545 / 237) : ℂ) * ζ ^ 22 + ((13 / 158) : ℂ) * ζ ^ 25 - ((997 / 474) : ℂ) * ζ ^ 27 + ((860 / 237) : ℂ) * ζ ^ 28 + ((758 / 237) : ℂ) * ζ ^ 29 + ((385 / 474) : ℂ) * ζ ^ 30 - ((241 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep06CoefficientIdentity07 :
    row18_reducedY44_combinationStep06Coefficient07 =
      row18_reducedY44_combinationStep05Coefficient07 +
        row18_reducedY44_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep06Coefficient07 row18_reducedY44_combinationStep05Coefficient07 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep06Coefficient08 : ℂ :=
  (((105 / 158) : ℂ) - ((26 / 237) : ℂ) * ζ ^ 1 + ((20 / 237) : ℂ) * ζ ^ 2 - ((67 / 237) : ℂ) * ζ ^ 3 - ((149 / 474) : ℂ) * ζ ^ 5 - ((25 / 237) : ℂ) * ζ ^ 6 + ((64 / 237) : ℂ) * ζ ^ 8 + ((2 / 237) : ℂ) * ζ ^ 9 + ((23 / 79) : ℂ) * ζ ^ 11 + ((64 / 237) : ℂ) * ζ ^ 12 + ((26 / 237) : ℂ) * ζ ^ 13 + ((37 / 474) : ℂ) * ζ ^ 15 + ((26 / 237) : ℂ) * ζ ^ 17 + ((15 / 79) : ℂ) * ζ ^ 18 + ((31 / 79) : ℂ) * ζ ^ 21 - ((20 / 237) : ℂ) * ζ ^ 22 + ((97 / 474) : ℂ) * ζ ^ 25 - ((31 / 79) : ℂ) * ζ ^ 27 - ((64 / 237) : ℂ) * ζ ^ 28 - ((26 / 237) : ℂ) * ζ ^ 29 - ((25 / 474) : ℂ) * ζ ^ 30 - ((23 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep06CoefficientIdentity08 :
    row18_reducedY44_combinationStep06Coefficient08 =
      row18_reducedY44_combinationStep05Coefficient08 +
        row18_reducedY44_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep06Coefficient08 row18_reducedY44_combinationStep05Coefficient08 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep06Coefficient09 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep06CoefficientIdentity09 :
    row18_reducedY44_combinationStep06Coefficient09 =
      row18_reducedY44_combinationStep05Coefficient09 +
        row18_reducedY44_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep06Coefficient09 row18_reducedY44_combinationStep05Coefficient09 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep06Coefficient10 : ℂ :=
  (((35 / 237) : ℂ) - ((19 / 237) : ℂ) * ζ ^ 1 - ((112 / 237) : ℂ) * ζ ^ 2 - ((9 / 79) : ℂ) * ζ ^ 3 - ((24 / 79) : ℂ) * ζ ^ 5 - ((23 / 237) : ℂ) * ζ ^ 6 - ((19 / 237) : ℂ) * ζ ^ 8 - ((17 / 237) : ℂ) * ζ ^ 9 - ((32 / 237) : ℂ) * ζ ^ 11 - ((89 / 237) : ℂ) * ζ ^ 12 + ((19 / 237) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 + ((19 / 237) : ℂ) * ζ ^ 17 + ((77 / 237) : ℂ) * ζ ^ 18 + ((53 / 237) : ℂ) * ζ ^ 21 + ((112 / 237) : ℂ) * ζ ^ 22 + ((112 / 237) : ℂ) * ζ ^ 24 + ((53 / 237) : ℂ) * ζ ^ 25 + ((32 / 237) : ℂ) * ζ ^ 27 + ((19 / 237) : ℂ) * ζ ^ 28 - ((19 / 237) : ℂ) * ζ ^ 29 - ((31 / 79) : ℂ) * ζ ^ 30 + ((32 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep06CoefficientIdentity10 :
    row18_reducedY44_combinationStep06Coefficient10 =
      row18_reducedY44_combinationStep05Coefficient10 +
        row18_reducedY44_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep06Coefficient10 row18_reducedY44_combinationStep05Coefficient10 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep06Coefficient11 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep06CoefficientIdentity11 :
    row18_reducedY44_combinationStep06Coefficient11 =
      row18_reducedY44_combinationStep05Coefficient11 +
        row18_reducedY44_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep06Coefficient11 row18_reducedY44_combinationStep05Coefficient11 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep06Coefficient12 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep06CoefficientIdentity12 :
    row18_reducedY44_combinationStep06Coefficient12 =
      row18_reducedY44_combinationStep05Coefficient12 +
        row18_reducedY44_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep06Coefficient12 row18_reducedY44_combinationStep05Coefficient12 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep06Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep06CoefficientIdentity13 :
    row18_reducedY44_combinationStep06Coefficient13 =
      row18_reducedY44_combinationStep05Coefficient13 +
        row18_reducedY44_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep06Coefficient13 row18_reducedY44_combinationStep05Coefficient13 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep06Coefficient14 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep06CoefficientIdentity14 :
    row18_reducedY44_combinationStep06Coefficient14 =
      row18_reducedY44_combinationStep05Coefficient14 +
        row18_reducedY44_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep06Coefficient14 row18_reducedY44_combinationStep05Coefficient14 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep06Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep06CoefficientIdentity15 :
    row18_reducedY44_combinationStep06Coefficient15 =
      row18_reducedY44_combinationStep05Coefficient15 +
        row18_reducedY44_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep06Coefficient15 row18_reducedY44_combinationStep05Coefficient15 row18_reducedY44_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY44_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY44_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY44_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY44_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY44_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY44_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY44_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY44_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY44_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY44_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY44_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY44_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY44_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY44_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY44_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY44_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY44_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY44_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY44_combinationStep06CoefficientIdentity00,
      row18_reducedY44_combinationStep06CoefficientIdentity01,
      row18_reducedY44_combinationStep06CoefficientIdentity02,
      row18_reducedY44_combinationStep06CoefficientIdentity03,
      row18_reducedY44_combinationStep06CoefficientIdentity04,
      row18_reducedY44_combinationStep06CoefficientIdentity05,
      row18_reducedY44_combinationStep06CoefficientIdentity06,
      row18_reducedY44_combinationStep06CoefficientIdentity07,
      row18_reducedY44_combinationStep06CoefficientIdentity08,
      row18_reducedY44_combinationStep06CoefficientIdentity09,
      row18_reducedY44_combinationStep06CoefficientIdentity10,
      row18_reducedY44_combinationStep06CoefficientIdentity11,
      row18_reducedY44_combinationStep06CoefficientIdentity12,
      row18_reducedY44_combinationStep06CoefficientIdentity13,
      row18_reducedY44_combinationStep06CoefficientIdentity14,
      row18_reducedY44_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY44_combinationStep06Multiplier * equation

private def row18_reducedY44_combinationStep07Multiplier : ℂ :=
  (((164 / 79) : ℂ) + ((122 / 237) : ℂ) * ζ ^ 1 - ((680 / 79) : ℂ) * ζ ^ 2 - ((1376 / 237) : ℂ) * ζ ^ 3 + ((2096 / 237) : ℂ) * ζ ^ 5 - ((1330 / 237) : ℂ) * ζ ^ 8 - ((24 / 79) : ℂ) * ζ ^ 9 + ((1448 / 237) : ℂ) * ζ ^ 11 + ((346 / 237) : ℂ) * ζ ^ 12 - ((122 / 237) : ℂ) * ζ ^ 13 - ((598 / 237) : ℂ) * ζ ^ 15 - ((122 / 237) : ℂ) * ζ ^ 17 + ((680 / 79) : ℂ) * ζ ^ 18 - ((1498 / 237) : ℂ) * ζ ^ 21 + ((680 / 79) : ℂ) * ζ ^ 22 + ((328 / 79) : ℂ) * ζ ^ 24 - ((658 / 79) : ℂ) * ζ ^ 25 - ((1498 / 237) : ℂ) * ζ ^ 27 + ((1330 / 237) : ℂ) * ζ ^ 28 + ((122 / 237) : ℂ) * ζ ^ 29 + ((68 / 237) : ℂ) * ζ ^ 30 - ((1448 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY44_combinationStep07Coefficient00 : ℂ :=
  (-((249 / 79) : ℂ) - ((608 / 395) : ℂ) * ζ ^ 1 + ((1757 / 790) : ℂ) * ζ ^ 2 + ((1017 / 395) : ℂ) * ζ ^ 3 - ((379 / 395) : ℂ) * ζ ^ 5 + ((314 / 395) : ℂ) * ζ ^ 6 + ((623 / 158) : ℂ) * ζ ^ 8 + ((1166 / 395) : ℂ) * ζ ^ 9 + ((149 / 395) : ℂ) * ζ ^ 11 + ((623 / 158) : ℂ) * ζ ^ 12 + ((608 / 395) : ℂ) * ζ ^ 13 - ((788 / 395) : ℂ) * ζ ^ 15 + ((608 / 395) : ℂ) * ζ ^ 17 + ((1129 / 790) : ℂ) * ζ ^ 18 - ((409 / 395) : ℂ) * ζ ^ 21 - ((1757 / 790) : ℂ) * ζ ^ 22 - ((229 / 395) : ℂ) * ζ ^ 25 + ((409 / 395) : ℂ) * ζ ^ 27 - ((623 / 158) : ℂ) * ζ ^ 28 - ((608 / 395) : ℂ) * ζ ^ 29 + ((157 / 395) : ℂ) * ζ ^ 30 - ((149 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep07CoefficientIdentity00 :
    row18_reducedY44_combinationStep07Coefficient00 =
      row18_reducedY44_combinationStep06Coefficient00 +
        row18_reducedY44_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep07Coefficient00 row18_reducedY44_combinationStep06Coefficient00 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep07Coefficient01 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep07CoefficientIdentity01 :
    row18_reducedY44_combinationStep07Coefficient01 =
      row18_reducedY44_combinationStep06Coefficient01 +
        row18_reducedY44_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep07Coefficient01 row18_reducedY44_combinationStep06Coefficient01 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep07Coefficient02 : ℂ :=
  (((2611 / 2370) : ℂ) - ((469 / 790) : ℂ) * ζ ^ 1 - ((592 / 395) : ℂ) * ζ ^ 2 + ((287 / 474) : ℂ) * ζ ^ 3 - ((2063 / 1185) : ℂ) * ζ ^ 5 - ((139 / 1185) : ℂ) * ζ ^ 6 - ((5083 / 2370) : ℂ) * ζ ^ 8 - ((328 / 1185) : ℂ) * ζ ^ 9 - ((301 / 237) : ℂ) * ζ ^ 11 - ((1637 / 1185) : ℂ) * ζ ^ 12 + ((469 / 790) : ℂ) * ζ ^ 13 - ((287 / 474) : ℂ) * ζ ^ 15 + ((469 / 790) : ℂ) * ζ ^ 17 + ((941 / 2370) : ℂ) * ζ ^ 18 + ((2719 / 2370) : ℂ) * ζ ^ 21 + ((592 / 395) : ℂ) * ζ ^ 22 + ((592 / 395) : ℂ) * ζ ^ 24 + ((2719 / 2370) : ℂ) * ζ ^ 25 + ((301 / 237) : ℂ) * ζ ^ 27 + ((5083 / 2370) : ℂ) * ζ ^ 28 - ((469 / 790) : ℂ) * ζ ^ 29 + ((1531 / 2370) : ℂ) * ζ ^ 30 + ((301 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep07CoefficientIdentity02 :
    row18_reducedY44_combinationStep07Coefficient02 =
      row18_reducedY44_combinationStep06Coefficient02 +
        row18_reducedY44_combinationStep07Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep07Coefficient02 row18_reducedY44_combinationStep06Coefficient02 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 (((11433 / 6241) : ℂ) + ((25803 / 12482) : ℂ) * ζ ^ 1 + ((22549 / 6241) : ℂ) * ζ ^ 2 - ((11512 / 6241) : ℂ) * ζ ^ 3 - ((36169 / 18723) : ℂ) * ζ ^ 4 - ((28221 / 12482) : ℂ) * ζ ^ 5 + ((76855 / 37446) : ℂ) * ζ ^ 6 + ((13779 / 6241) : ℂ) * ζ ^ 7 + ((12386 / 6241) : ℂ) * ζ ^ 8 - ((65999 / 37446) : ℂ) * ζ ^ 9 - ((14323 / 18723) : ℂ) * ζ ^ 10 - ((17819 / 18723) : ℂ) * ζ ^ 11 + ((27917 / 37446) : ℂ) * ζ ^ 12 - ((4015 / 37446) : ℂ) * ζ ^ 13 + ((1877 / 12482) : ℂ) * ζ ^ 14 - ((17438 / 18723) : ℂ) * ζ ^ 15 + ((18241 / 37446) : ℂ) * ζ ^ 16 + ((15749 / 12482) : ℂ) * ζ ^ 17 + ((68333 / 37446) : ℂ) * ζ ^ 18 - ((31831 / 37446) : ℂ) * ζ ^ 19 - ((27825 / 12482) : ℂ) * ζ ^ 20 - ((77113 / 37446) : ℂ) * ζ ^ 21 + ((6251 / 12482) : ℂ) * ζ ^ 22 + ((53435 / 37446) : ℂ) * ζ ^ 23 + ((22413 / 12482) : ℂ) * ζ ^ 24 - ((471 / 6241) : ℂ) * ζ ^ 25 - ((20596 / 18723) : ℂ) * ζ ^ 26 - ((18687 / 12482) : ℂ) * ζ ^ 27 + ((6865 / 37446) : ℂ) * ζ ^ 28 + ((5707 / 6241) : ℂ) * ζ ^ 29 + ((1810 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep07Coefficient03 : ℂ :=
  (-((39 / 158) : ℂ) - ((46 / 237) : ℂ) * ζ ^ 1 - ((97 / 474) : ℂ) * ζ ^ 2 + ((365 / 474) : ℂ) * ζ ^ 3 + ((103 / 237) : ℂ) * ζ ^ 5 + ((31 / 237) : ℂ) * ζ ^ 6 - ((113 / 474) : ℂ) * ζ ^ 8 + ((281 / 474) : ℂ) * ζ ^ 9 - ((14 / 79) : ℂ) * ζ ^ 11 - ((113 / 474) : ℂ) * ζ ^ 12 + ((46 / 237) : ℂ) * ζ ^ 13 - ((67 / 474) : ℂ) * ζ ^ 15 + ((46 / 237) : ℂ) * ζ ^ 17 - ((53 / 158) : ℂ) * ζ ^ 18 - ((91 / 158) : ℂ) * ζ ^ 21 + ((97 / 474) : ℂ) * ζ ^ 22 - ((149 / 237) : ℂ) * ζ ^ 25 + ((91 / 158) : ℂ) * ζ ^ 27 + ((113 / 474) : ℂ) * ζ ^ 28 - ((46 / 237) : ℂ) * ζ ^ 29 + ((31 / 474) : ℂ) * ζ ^ 30 + ((14 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep07CoefficientIdentity03 :
    row18_reducedY44_combinationStep07Coefficient03 =
      row18_reducedY44_combinationStep06Coefficient03 +
        row18_reducedY44_combinationStep07Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep07Coefficient03 row18_reducedY44_combinationStep06Coefficient03 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 (-((176909 / 37446) : ℂ) - ((51895 / 18723) : ℂ) * ζ ^ 1 + ((93601 / 37446) : ℂ) * ζ ^ 2 + ((54259 / 18723) : ℂ) * ζ ^ 3 - ((3164 / 6241) : ℂ) * ζ ^ 4 + ((20779 / 37446) : ℂ) * ζ ^ 5 - ((35741 / 37446) : ℂ) * ζ ^ 6 - ((8721 / 6241) : ℂ) * ζ ^ 7 - ((8744 / 18723) : ℂ) * ζ ^ 8 + ((49555 / 37446) : ℂ) * ζ ^ 9 + ((18651 / 12482) : ℂ) * ζ ^ 10 - ((32877 / 12482) : ℂ) * ζ ^ 11 - ((20235 / 12482) : ℂ) * ζ ^ 12 + ((7912 / 18723) : ℂ) * ζ ^ 13 + ((179539 / 37446) : ℂ) * ζ ^ 14 + ((27499 / 12482) : ℂ) * ζ ^ 15 - ((28267 / 18723) : ℂ) * ζ ^ 16 - ((183251 / 37446) : ℂ) * ζ ^ 17 - ((9491 / 6241) : ℂ) * ζ ^ 18 + ((27243 / 12482) : ℂ) * ζ ^ 19 + ((154492 / 18723) : ℂ) * ζ ^ 20 + ((48373 / 18723) : ℂ) * ζ ^ 21 - ((60571 / 37446) : ℂ) * ζ ^ 22 - ((28179 / 6241) : ℂ) * ζ ^ 23 - ((2095 / 37446) : ℂ) * ζ ^ 24 + ((10843 / 12482) : ℂ) * ζ ^ 25 + ((116161 / 37446) : ℂ) * ζ ^ 26 + ((6667 / 18723) : ℂ) * ζ ^ 27 - ((19372 / 18723) : ℂ) * ζ ^ 28 - ((8212 / 18723) : ℂ) * ζ ^ 29 - ((10136 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep07Coefficient04 : ℂ :=
  (((249 / 79) : ℂ) + ((608 / 395) : ℂ) * ζ ^ 1 - ((1757 / 790) : ℂ) * ζ ^ 2 - ((1017 / 395) : ℂ) * ζ ^ 3 + ((379 / 395) : ℂ) * ζ ^ 5 - ((314 / 395) : ℂ) * ζ ^ 6 - ((623 / 158) : ℂ) * ζ ^ 8 - ((1166 / 395) : ℂ) * ζ ^ 9 - ((149 / 395) : ℂ) * ζ ^ 11 - ((623 / 158) : ℂ) * ζ ^ 12 - ((608 / 395) : ℂ) * ζ ^ 13 + ((788 / 395) : ℂ) * ζ ^ 15 - ((608 / 395) : ℂ) * ζ ^ 17 - ((1129 / 790) : ℂ) * ζ ^ 18 + ((409 / 395) : ℂ) * ζ ^ 21 + ((1757 / 790) : ℂ) * ζ ^ 22 + ((229 / 395) : ℂ) * ζ ^ 25 - ((409 / 395) : ℂ) * ζ ^ 27 + ((623 / 158) : ℂ) * ζ ^ 28 + ((608 / 395) : ℂ) * ζ ^ 29 - ((157 / 395) : ℂ) * ζ ^ 30 + ((149 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep07CoefficientIdentity04 :
    row18_reducedY44_combinationStep07Coefficient04 =
      row18_reducedY44_combinationStep06Coefficient04 +
        row18_reducedY44_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep07Coefficient04 row18_reducedY44_combinationStep06Coefficient04 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep07Coefficient05 : ℂ :=
  (((39 / 79) : ℂ) + ((126 / 79) : ℂ) * ζ ^ 1 + ((15 / 158) : ℂ) * ζ ^ 2 - ((181 / 79) : ℂ) * ζ ^ 5 - ((63 / 158) : ℂ) * ζ ^ 6 - ((63 / 158) : ℂ) * ζ ^ 8 - ((181 / 79) : ℂ) * ζ ^ 9 - ((393 / 158) : ℂ) * ζ ^ 11 - ((59 / 79) : ℂ) * ζ ^ 12 - ((126 / 79) : ℂ) * ζ ^ 13 - ((50 / 79) : ℂ) * ζ ^ 15 - ((126 / 79) : ℂ) * ζ ^ 17 - ((52 / 79) : ℂ) * ζ ^ 18 + ((55 / 158) : ℂ) * ζ ^ 21 - ((15 / 158) : ℂ) * ζ ^ 22 + ((167 / 158) : ℂ) * ζ ^ 24 + ((307 / 79) : ℂ) * ζ ^ 25 + ((50 / 79) : ℂ) * ζ ^ 27 + ((63 / 158) : ℂ) * ζ ^ 28 + ((126 / 79) : ℂ) * ζ ^ 29 + ((55 / 158) : ℂ) * ζ ^ 30 + ((393 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep07CoefficientIdentity05 :
    row18_reducedY44_combinationStep07Coefficient05 =
      row18_reducedY44_combinationStep06Coefficient05 +
        row18_reducedY44_combinationStep07Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep07Coefficient05 row18_reducedY44_combinationStep06Coefficient05 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 (-((16481 / 12482) : ℂ) - ((911 / 12482) : ℂ) * ζ ^ 1 + ((11231 / 12482) : ℂ) * ζ ^ 2 - ((15391 / 12482) : ℂ) * ζ ^ 3 - ((481 / 12482) : ℂ) * ζ ^ 4 + ((58619 / 37446) : ℂ) * ζ ^ 5 + ((17361 / 12482) : ℂ) * ζ ^ 6 - ((18239 / 12482) : ℂ) * ζ ^ 7 + ((53159 / 37446) : ℂ) * ζ ^ 8 - ((286 / 18723) : ℂ) * ζ ^ 9 - ((14941 / 12482) : ℂ) * ζ ^ 10 - ((2753 / 37446) : ℂ) * ζ ^ 11 - ((7 / 237) : ℂ) * ζ ^ 12 + ((11092 / 18723) : ℂ) * ζ ^ 13 - ((8643 / 12482) : ℂ) * ζ ^ 14 + ((9185 / 6241) : ℂ) * ζ ^ 15 + ((9263 / 37446) : ℂ) * ζ ^ 16 + ((28934 / 18723) : ℂ) * ζ ^ 17 - ((57551 / 37446) : ℂ) * ζ ^ 18 + ((68033 / 37446) : ℂ) * ζ ^ 19 + ((4897 / 12482) : ℂ) * ζ ^ 20 + ((6414 / 6241) : ℂ) * ζ ^ 21 - ((81257 / 37446) : ℂ) * ζ ^ 22 + ((138737 / 37446) : ℂ) * ζ ^ 23 - ((39023 / 37446) : ℂ) * ζ ^ 24 + ((53287 / 37446) : ℂ) * ζ ^ 25 - ((13630 / 18723) : ℂ) * ζ ^ 26 + ((47423 / 37446) : ℂ) * ζ ^ 27 - ((64169 / 37446) : ℂ) * ζ ^ 28 + ((19327 / 18723) : ℂ) * ζ ^ 29 + ((4706 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep07Coefficient06 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep07CoefficientIdentity06 :
    row18_reducedY44_combinationStep07Coefficient06 =
      row18_reducedY44_combinationStep06Coefficient06 +
        row18_reducedY44_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep07Coefficient06 row18_reducedY44_combinationStep06Coefficient06 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep07Coefficient07 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep07CoefficientIdentity07 :
    row18_reducedY44_combinationStep07Coefficient07 =
      row18_reducedY44_combinationStep06Coefficient07 +
        row18_reducedY44_combinationStep07Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep07Coefficient07 row18_reducedY44_combinationStep06Coefficient07 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 (((176909 / 37446) : ℂ) + ((51895 / 18723) : ℂ) * ζ ^ 1 - ((93601 / 37446) : ℂ) * ζ ^ 2 - ((54259 / 18723) : ℂ) * ζ ^ 3 + ((3164 / 6241) : ℂ) * ζ ^ 4 - ((20779 / 37446) : ℂ) * ζ ^ 5 + ((35741 / 37446) : ℂ) * ζ ^ 6 + ((8721 / 6241) : ℂ) * ζ ^ 7 + ((8744 / 18723) : ℂ) * ζ ^ 8 - ((49555 / 37446) : ℂ) * ζ ^ 9 - ((18651 / 12482) : ℂ) * ζ ^ 10 + ((32877 / 12482) : ℂ) * ζ ^ 11 + ((20235 / 12482) : ℂ) * ζ ^ 12 - ((7912 / 18723) : ℂ) * ζ ^ 13 - ((179539 / 37446) : ℂ) * ζ ^ 14 - ((27499 / 12482) : ℂ) * ζ ^ 15 + ((28267 / 18723) : ℂ) * ζ ^ 16 + ((183251 / 37446) : ℂ) * ζ ^ 17 + ((9491 / 6241) : ℂ) * ζ ^ 18 - ((27243 / 12482) : ℂ) * ζ ^ 19 - ((154492 / 18723) : ℂ) * ζ ^ 20 - ((48373 / 18723) : ℂ) * ζ ^ 21 + ((60571 / 37446) : ℂ) * ζ ^ 22 + ((28179 / 6241) : ℂ) * ζ ^ 23 + ((2095 / 37446) : ℂ) * ζ ^ 24 - ((10843 / 12482) : ℂ) * ζ ^ 25 - ((116161 / 37446) : ℂ) * ζ ^ 26 - ((6667 / 18723) : ℂ) * ζ ^ 27 + ((19372 / 18723) : ℂ) * ζ ^ 28 + ((8212 / 18723) : ℂ) * ζ ^ 29 + ((10136 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep07Coefficient08 : ℂ :=
  (((105 / 158) : ℂ) - ((26 / 237) : ℂ) * ζ ^ 1 + ((20 / 237) : ℂ) * ζ ^ 2 - ((67 / 237) : ℂ) * ζ ^ 3 - ((149 / 474) : ℂ) * ζ ^ 5 - ((25 / 237) : ℂ) * ζ ^ 6 + ((64 / 237) : ℂ) * ζ ^ 8 + ((2 / 237) : ℂ) * ζ ^ 9 + ((23 / 79) : ℂ) * ζ ^ 11 + ((64 / 237) : ℂ) * ζ ^ 12 + ((26 / 237) : ℂ) * ζ ^ 13 + ((37 / 474) : ℂ) * ζ ^ 15 + ((26 / 237) : ℂ) * ζ ^ 17 + ((15 / 79) : ℂ) * ζ ^ 18 + ((31 / 79) : ℂ) * ζ ^ 21 - ((20 / 237) : ℂ) * ζ ^ 22 + ((97 / 474) : ℂ) * ζ ^ 25 - ((31 / 79) : ℂ) * ζ ^ 27 - ((64 / 237) : ℂ) * ζ ^ 28 - ((26 / 237) : ℂ) * ζ ^ 29 - ((25 / 474) : ℂ) * ζ ^ 30 - ((23 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep07CoefficientIdentity08 :
    row18_reducedY44_combinationStep07Coefficient08 =
      row18_reducedY44_combinationStep06Coefficient08 +
        row18_reducedY44_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep07Coefficient08 row18_reducedY44_combinationStep06Coefficient08 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep07Coefficient09 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep07CoefficientIdentity09 :
    row18_reducedY44_combinationStep07Coefficient09 =
      row18_reducedY44_combinationStep06Coefficient09 +
        row18_reducedY44_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep07Coefficient09 row18_reducedY44_combinationStep06Coefficient09 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep07Coefficient10 : ℂ :=
  (((35 / 237) : ℂ) - ((19 / 237) : ℂ) * ζ ^ 1 - ((112 / 237) : ℂ) * ζ ^ 2 - ((9 / 79) : ℂ) * ζ ^ 3 - ((24 / 79) : ℂ) * ζ ^ 5 - ((23 / 237) : ℂ) * ζ ^ 6 - ((19 / 237) : ℂ) * ζ ^ 8 - ((17 / 237) : ℂ) * ζ ^ 9 - ((32 / 237) : ℂ) * ζ ^ 11 - ((89 / 237) : ℂ) * ζ ^ 12 + ((19 / 237) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 + ((19 / 237) : ℂ) * ζ ^ 17 + ((77 / 237) : ℂ) * ζ ^ 18 + ((53 / 237) : ℂ) * ζ ^ 21 + ((112 / 237) : ℂ) * ζ ^ 22 + ((112 / 237) : ℂ) * ζ ^ 24 + ((53 / 237) : ℂ) * ζ ^ 25 + ((32 / 237) : ℂ) * ζ ^ 27 + ((19 / 237) : ℂ) * ζ ^ 28 - ((19 / 237) : ℂ) * ζ ^ 29 - ((31 / 79) : ℂ) * ζ ^ 30 + ((32 / 237) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep07CoefficientIdentity10 :
    row18_reducedY44_combinationStep07Coefficient10 =
      row18_reducedY44_combinationStep06Coefficient10 +
        row18_reducedY44_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep07Coefficient10 row18_reducedY44_combinationStep06Coefficient10 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep07Coefficient11 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep07CoefficientIdentity11 :
    row18_reducedY44_combinationStep07Coefficient11 =
      row18_reducedY44_combinationStep06Coefficient11 +
        row18_reducedY44_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep07Coefficient11 row18_reducedY44_combinationStep06Coefficient11 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep07Coefficient12 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep07CoefficientIdentity12 :
    row18_reducedY44_combinationStep07Coefficient12 =
      row18_reducedY44_combinationStep06Coefficient12 +
        row18_reducedY44_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep07Coefficient12 row18_reducedY44_combinationStep06Coefficient12 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep07Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep07CoefficientIdentity13 :
    row18_reducedY44_combinationStep07Coefficient13 =
      row18_reducedY44_combinationStep06Coefficient13 +
        row18_reducedY44_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep07Coefficient13 row18_reducedY44_combinationStep06Coefficient13 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep07Coefficient14 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep07CoefficientIdentity14 :
    row18_reducedY44_combinationStep07Coefficient14 =
      row18_reducedY44_combinationStep06Coefficient14 +
        row18_reducedY44_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep07Coefficient14 row18_reducedY44_combinationStep06Coefficient14 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep07Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep07CoefficientIdentity15 :
    row18_reducedY44_combinationStep07Coefficient15 =
      row18_reducedY44_combinationStep06Coefficient15 +
        row18_reducedY44_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep07Coefficient15 row18_reducedY44_combinationStep06Coefficient15 row18_reducedY44_combinationStep07Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY44_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY44_combinationStep07Coefficient00) * Y 0 0
      + (row18_reducedY44_combinationStep07Coefficient01) * Y 0 1
      + (row18_reducedY44_combinationStep07Coefficient02) * Y 1 0
      + (row18_reducedY44_combinationStep07Coefficient03) * Y 1 1
      + (row18_reducedY44_combinationStep07Coefficient04) * Y 2 2
      + (row18_reducedY44_combinationStep07Coefficient05) * Y 2 3
      + (row18_reducedY44_combinationStep07Coefficient06) * Y 3 2
      + (row18_reducedY44_combinationStep07Coefficient07) * Y 3 3
      + (row18_reducedY44_combinationStep07Coefficient08) * Y 4 4
      + (row18_reducedY44_combinationStep07Coefficient09) * Y 4 5
      + (row18_reducedY44_combinationStep07Coefficient10) * Y 5 4
      + (row18_reducedY44_combinationStep07Coefficient11) * Y 5 5
      + (row18_reducedY44_combinationStep07Coefficient12) * Y 6 6
      + (row18_reducedY44_combinationStep07Coefficient13) * Y 6 7
      + (row18_reducedY44_combinationStep07Coefficient14) * Y 7 6
      + (row18_reducedY44_combinationStep07Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY44_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY44_combinationStep07CoefficientIdentity00,
      row18_reducedY44_combinationStep07CoefficientIdentity01,
      row18_reducedY44_combinationStep07CoefficientIdentity02,
      row18_reducedY44_combinationStep07CoefficientIdentity03,
      row18_reducedY44_combinationStep07CoefficientIdentity04,
      row18_reducedY44_combinationStep07CoefficientIdentity05,
      row18_reducedY44_combinationStep07CoefficientIdentity06,
      row18_reducedY44_combinationStep07CoefficientIdentity07,
      row18_reducedY44_combinationStep07CoefficientIdentity08,
      row18_reducedY44_combinationStep07CoefficientIdentity09,
      row18_reducedY44_combinationStep07CoefficientIdentity10,
      row18_reducedY44_combinationStep07CoefficientIdentity11,
      row18_reducedY44_combinationStep07CoefficientIdentity12,
      row18_reducedY44_combinationStep07CoefficientIdentity13,
      row18_reducedY44_combinationStep07CoefficientIdentity14,
      row18_reducedY44_combinationStep07CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY44_combinationStep07Multiplier * equation

private def row18_reducedY44_combinationStep08Multiplier : ℂ :=
  (((238 / 237) : ℂ) - ((22 / 237) : ℂ) * ζ ^ 1 - ((94 / 237) : ℂ) * ζ ^ 2 - ((8 / 237) : ℂ) * ζ ^ 3 - ((286 / 237) : ℂ) * ζ ^ 6 + ((2 / 79) : ℂ) * ζ ^ 8 + ((62 / 79) : ℂ) * ζ ^ 9 + ((242 / 237) : ℂ) * ζ ^ 11 - ((64 / 79) : ℂ) * ζ ^ 12 + ((22 / 237) : ℂ) * ζ ^ 13 - ((8 / 237) : ℂ) * ζ ^ 15 + ((22 / 237) : ℂ) * ζ ^ 17 + ((332 / 237) : ℂ) * ζ ^ 18 + ((22 / 237) : ℂ) * ζ ^ 21 + ((94 / 237) : ℂ) * ζ ^ 22 - ((94 / 237) : ℂ) * ζ ^ 24 - ((22 / 237) : ℂ) * ζ ^ 25 + ((242 / 237) : ℂ) * ζ ^ 27 - ((2 / 79) : ℂ) * ζ ^ 28 - ((22 / 237) : ℂ) * ζ ^ 29 - ((88 / 237) : ℂ) * ζ ^ 30 - ((242 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY44_combinationStep08Coefficient00 : ℂ :=
  (-((249 / 79) : ℂ) - ((608 / 395) : ℂ) * ζ ^ 1 + ((1757 / 790) : ℂ) * ζ ^ 2 + ((1017 / 395) : ℂ) * ζ ^ 3 - ((379 / 395) : ℂ) * ζ ^ 5 + ((314 / 395) : ℂ) * ζ ^ 6 + ((623 / 158) : ℂ) * ζ ^ 8 + ((1166 / 395) : ℂ) * ζ ^ 9 + ((149 / 395) : ℂ) * ζ ^ 11 + ((623 / 158) : ℂ) * ζ ^ 12 + ((608 / 395) : ℂ) * ζ ^ 13 - ((788 / 395) : ℂ) * ζ ^ 15 + ((608 / 395) : ℂ) * ζ ^ 17 + ((1129 / 790) : ℂ) * ζ ^ 18 - ((409 / 395) : ℂ) * ζ ^ 21 - ((1757 / 790) : ℂ) * ζ ^ 22 - ((229 / 395) : ℂ) * ζ ^ 25 + ((409 / 395) : ℂ) * ζ ^ 27 - ((623 / 158) : ℂ) * ζ ^ 28 - ((608 / 395) : ℂ) * ζ ^ 29 + ((157 / 395) : ℂ) * ζ ^ 30 - ((149 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep08CoefficientIdentity00 :
    row18_reducedY44_combinationStep08Coefficient00 =
      row18_reducedY44_combinationStep07Coefficient00 +
        row18_reducedY44_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep08Coefficient00 row18_reducedY44_combinationStep07Coefficient00 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep08Coefficient01 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep08CoefficientIdentity01 :
    row18_reducedY44_combinationStep08Coefficient01 =
      row18_reducedY44_combinationStep07Coefficient01 +
        row18_reducedY44_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep08Coefficient01 row18_reducedY44_combinationStep07Coefficient01 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep08Coefficient02 : ℂ :=
  (((501 / 395) : ℂ) - ((112 / 395) : ℂ) * ζ ^ 1 - ((592 / 395) : ℂ) * ζ ^ 2 + ((48 / 79) : ℂ) * ζ ^ 3 - ((466 / 395) : ℂ) * ζ ^ 5 - ((178 / 395) : ℂ) * ζ ^ 6 - ((913 / 395) : ℂ) * ζ ^ 8 - ((121 / 395) : ℂ) * ζ ^ 9 - ((66 / 79) : ℂ) * ζ ^ 11 - ((414 / 395) : ℂ) * ζ ^ 12 + ((112 / 395) : ℂ) * ζ ^ 13 - ((48 / 79) : ℂ) * ζ ^ 15 + ((112 / 395) : ℂ) * ζ ^ 17 + ((91 / 395) : ℂ) * ζ ^ 18 + ((354 / 395) : ℂ) * ζ ^ 21 + ((592 / 395) : ℂ) * ζ ^ 22 + ((592 / 395) : ℂ) * ζ ^ 24 + ((354 / 395) : ℂ) * ζ ^ 25 + ((66 / 79) : ℂ) * ζ ^ 27 + ((913 / 395) : ℂ) * ζ ^ 28 - ((112 / 395) : ℂ) * ζ ^ 29 + ((321 / 395) : ℂ) * ζ ^ 30 + ((66 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep08CoefficientIdentity02 :
    row18_reducedY44_combinationStep08Coefficient02 =
      row18_reducedY44_combinationStep07Coefficient02 +
        row18_reducedY44_combinationStep08Multiplier *
          (-((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((57 / 158) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((57 / 158) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((57 / 158) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep08Coefficient02 row18_reducedY44_combinationStep07Coefficient02 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 (-((2715 / 12482) : ℂ) - ((1688 / 6241) : ℂ) * ζ ^ 1 + ((14197 / 37446) : ℂ) * ζ ^ 2 - ((1012 / 18723) : ℂ) * ζ ^ 3 + ((35 / 474) : ℂ) * ζ ^ 4 - ((57 / 158) : ℂ) * ζ ^ 5 + ((5 / 237) : ℂ) * ζ ^ 6 + ((224 / 6241) : ℂ) * ζ ^ 7 - ((2014 / 6241) : ℂ) * ζ ^ 8 + ((1992 / 6241) : ℂ) * ζ ^ 9 + ((425 / 37446) : ℂ) * ζ ^ 10 - ((1345 / 12482) : ℂ) * ζ ^ 11 - ((479 / 6241) : ℂ) * ζ ^ 12 - ((215 / 37446) : ℂ) * ζ ^ 13 - ((1075 / 37446) : ℂ) * ζ ^ 14 + ((3179 / 12482) : ℂ) * ζ ^ 15 - ((5161 / 37446) : ℂ) * ζ ^ 16 - ((2485 / 6241) : ℂ) * ζ ^ 17 + ((580 / 18723) : ℂ) * ζ ^ 18 - ((3025 / 37446) : ℂ) * ζ ^ 19 + ((11429 / 37446) : ℂ) * ζ ^ 20 + ((5027 / 18723) : ℂ) * ζ ^ 21 + ((88 / 6241) : ℂ) * ζ ^ 22 + ((2239 / 37446) : ℂ) * ζ ^ 23 - ((93 / 12482) : ℂ) * ζ ^ 24 + ((2893 / 37446) : ℂ) * ζ ^ 25 - ((854 / 18723) : ℂ) * ζ ^ 26 + ((76 / 18723) : ℂ) * ζ ^ 27 - ((1705 / 37446) : ℂ) * ζ ^ 28 - ((418 / 18723) : ℂ) * ζ ^ 29 + ((847 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep08Coefficient03 : ℂ :=
  (-((46 / 79) : ℂ) - ((24 / 79) : ℂ) * ζ ^ 1 - ((19 / 158) : ℂ) * ζ ^ 2 + ((77 / 158) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((2 / 79) : ℂ) * ζ ^ 6 + ((5 / 158) : ℂ) * ζ ^ 8 + ((95 / 158) : ℂ) * ζ ^ 9 + ((9 / 79) : ℂ) * ζ ^ 11 + ((5 / 158) : ℂ) * ζ ^ 12 + ((24 / 79) : ℂ) * ζ ^ 13 - ((5 / 79) : ℂ) * ζ ^ 15 + ((24 / 79) : ℂ) * ζ ^ 17 - ((23 / 158) : ℂ) * ζ ^ 18 - ((29 / 158) : ℂ) * ζ ^ 21 + ((19 / 158) : ℂ) * ζ ^ 22 - ((67 / 158) : ℂ) * ζ ^ 25 + ((29 / 158) : ℂ) * ζ ^ 27 - ((5 / 158) : ℂ) * ζ ^ 28 - ((24 / 79) : ℂ) * ζ ^ 29 + ((1 / 79) : ℂ) * ζ ^ 30 - ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep08CoefficientIdentity03 :
    row18_reducedY44_combinationStep08Coefficient03 =
      row18_reducedY44_combinationStep07Coefficient03 +
        row18_reducedY44_combinationStep08Multiplier *
          (-((5 / 79) : ℂ) - ((43 / 316) : ℂ) * ζ ^ 1 - ((9 / 158) : ℂ) * ζ ^ 2 - ((63 / 316) : ℂ) * ζ ^ 5 + ((1 / 158) : ℂ) * ζ ^ 6 + ((1 / 158) : ℂ) * ζ ^ 8 - ((63 / 316) : ℂ) * ζ ^ 9 + ((57 / 158) : ℂ) * ζ ^ 11 + ((31 / 316) : ℂ) * ζ ^ 12 + ((43 / 316) : ℂ) * ζ ^ 13 - ((3 / 79) : ℂ) * ζ ^ 15 + ((43 / 316) : ℂ) * ζ ^ 17 - ((3 / 316) : ℂ) * ζ ^ 18 + ((53 / 316) : ℂ) * ζ ^ 21 + ((9 / 158) : ℂ) * ζ ^ 22 + ((1 / 316) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((1 / 158) : ℂ) * ζ ^ 28 - ((43 / 316) : ℂ) * ζ ^ 29 - ((29 / 316) : ℂ) * ζ ^ 30 - ((57 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep08Coefficient03 row18_reducedY44_combinationStep07Coefficient03 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 (((10181 / 37446) : ℂ) - ((263 / 12482) : ℂ) * ζ ^ 1 - ((3889 / 37446) : ℂ) * ζ ^ 2 + ((4295 / 12482) : ℂ) * ζ ^ 3 - ((9163 / 37446) : ℂ) * ζ ^ 4 + ((65 / 474) : ℂ) * ζ ^ 5 + ((5815 / 18723) : ℂ) * ζ ^ 6 - ((3797 / 37446) : ℂ) * ζ ^ 7 + ((1961 / 37446) : ℂ) * ζ ^ 8 - ((4989 / 12482) : ℂ) * ζ ^ 9 - ((2514 / 6241) : ℂ) * ζ ^ 10 + ((14329 / 37446) : ℂ) * ζ ^ 11 - ((1387 / 18723) : ℂ) * ζ ^ 12 + ((11029 / 37446) : ℂ) * ζ ^ 13 + ((3925 / 37446) : ℂ) * ζ ^ 14 + ((379 / 12482) : ℂ) * ζ ^ 15 - ((1231 / 12482) : ℂ) * ζ ^ 16 - ((5091 / 12482) : ℂ) * ζ ^ 17 - ((9523 / 18723) : ℂ) * ζ ^ 18 - ((3458 / 18723) : ℂ) * ζ ^ 19 + ((6785 / 37446) : ℂ) * ζ ^ 20 + ((6847 / 37446) : ℂ) * ζ ^ 21 + ((5236 / 6241) : ℂ) * ζ ^ 22 + ((1603 / 37446) : ℂ) * ζ ^ 23 - ((7114 / 18723) : ℂ) * ζ ^ 24 - ((4137 / 12482) : ℂ) * ζ ^ 25 - ((4732 / 6241) : ℂ) * ζ ^ 26 + ((2795 / 37446) : ℂ) * ζ ^ 27 + ((7733 / 37446) : ℂ) * ζ ^ 28 + ((8525 / 37446) : ℂ) * ζ ^ 29 + ((2299 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep08Coefficient04 : ℂ :=
  (((249 / 79) : ℂ) + ((608 / 395) : ℂ) * ζ ^ 1 - ((1757 / 790) : ℂ) * ζ ^ 2 - ((1017 / 395) : ℂ) * ζ ^ 3 + ((379 / 395) : ℂ) * ζ ^ 5 - ((314 / 395) : ℂ) * ζ ^ 6 - ((623 / 158) : ℂ) * ζ ^ 8 - ((1166 / 395) : ℂ) * ζ ^ 9 - ((149 / 395) : ℂ) * ζ ^ 11 - ((623 / 158) : ℂ) * ζ ^ 12 - ((608 / 395) : ℂ) * ζ ^ 13 + ((788 / 395) : ℂ) * ζ ^ 15 - ((608 / 395) : ℂ) * ζ ^ 17 - ((1129 / 790) : ℂ) * ζ ^ 18 + ((409 / 395) : ℂ) * ζ ^ 21 + ((1757 / 790) : ℂ) * ζ ^ 22 + ((229 / 395) : ℂ) * ζ ^ 25 - ((409 / 395) : ℂ) * ζ ^ 27 + ((623 / 158) : ℂ) * ζ ^ 28 + ((608 / 395) : ℂ) * ζ ^ 29 - ((157 / 395) : ℂ) * ζ ^ 30 + ((149 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep08CoefficientIdentity04 :
    row18_reducedY44_combinationStep08Coefficient04 =
      row18_reducedY44_combinationStep07Coefficient04 +
        row18_reducedY44_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep08Coefficient04 row18_reducedY44_combinationStep07Coefficient04 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep08Coefficient05 : ℂ :=
  (((39 / 79) : ℂ) + ((126 / 79) : ℂ) * ζ ^ 1 + ((15 / 158) : ℂ) * ζ ^ 2 - ((181 / 79) : ℂ) * ζ ^ 5 - ((63 / 158) : ℂ) * ζ ^ 6 - ((63 / 158) : ℂ) * ζ ^ 8 - ((181 / 79) : ℂ) * ζ ^ 9 - ((393 / 158) : ℂ) * ζ ^ 11 - ((59 / 79) : ℂ) * ζ ^ 12 - ((126 / 79) : ℂ) * ζ ^ 13 - ((50 / 79) : ℂ) * ζ ^ 15 - ((126 / 79) : ℂ) * ζ ^ 17 - ((52 / 79) : ℂ) * ζ ^ 18 + ((55 / 158) : ℂ) * ζ ^ 21 - ((15 / 158) : ℂ) * ζ ^ 22 + ((167 / 158) : ℂ) * ζ ^ 24 + ((307 / 79) : ℂ) * ζ ^ 25 + ((50 / 79) : ℂ) * ζ ^ 27 + ((63 / 158) : ℂ) * ζ ^ 28 + ((126 / 79) : ℂ) * ζ ^ 29 + ((55 / 158) : ℂ) * ζ ^ 30 + ((393 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep08CoefficientIdentity05 :
    row18_reducedY44_combinationStep08Coefficient05 =
      row18_reducedY44_combinationStep07Coefficient05 +
        row18_reducedY44_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep08Coefficient05 row18_reducedY44_combinationStep07Coefficient05 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep08Coefficient06 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep08CoefficientIdentity06 :
    row18_reducedY44_combinationStep08Coefficient06 =
      row18_reducedY44_combinationStep07Coefficient06 +
        row18_reducedY44_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep08Coefficient06 row18_reducedY44_combinationStep07Coefficient06 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep08Coefficient07 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep08CoefficientIdentity07 :
    row18_reducedY44_combinationStep08Coefficient07 =
      row18_reducedY44_combinationStep07Coefficient07 +
        row18_reducedY44_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep08Coefficient07 row18_reducedY44_combinationStep07Coefficient07 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep08Coefficient08 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY44_combinationStep08CoefficientIdentity08 :
    row18_reducedY44_combinationStep08Coefficient08 =
      row18_reducedY44_combinationStep07Coefficient08 +
        row18_reducedY44_combinationStep08Multiplier *
          (((5 / 79) : ℂ) + ((43 / 316) : ℂ) * ζ ^ 1 + ((9 / 158) : ℂ) * ζ ^ 2 + ((63 / 316) : ℂ) * ζ ^ 5 - ((1 / 158) : ℂ) * ζ ^ 6 - ((1 / 158) : ℂ) * ζ ^ 8 + ((63 / 316) : ℂ) * ζ ^ 9 - ((57 / 158) : ℂ) * ζ ^ 11 - ((31 / 316) : ℂ) * ζ ^ 12 - ((43 / 316) : ℂ) * ζ ^ 13 + ((3 / 79) : ℂ) * ζ ^ 15 - ((43 / 316) : ℂ) * ζ ^ 17 + ((3 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 - ((9 / 158) : ℂ) * ζ ^ 22 - ((1 / 316) : ℂ) * ζ ^ 24 - ((5 / 79) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((1 / 158) : ℂ) * ζ ^ 28 + ((43 / 316) : ℂ) * ζ ^ 29 + ((29 / 316) : ℂ) * ζ ^ 30 + ((57 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep08Coefficient08 row18_reducedY44_combinationStep07Coefficient08 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 (-((10181 / 37446) : ℂ) + ((263 / 12482) : ℂ) * ζ ^ 1 + ((3889 / 37446) : ℂ) * ζ ^ 2 - ((4295 / 12482) : ℂ) * ζ ^ 3 + ((9163 / 37446) : ℂ) * ζ ^ 4 - ((65 / 474) : ℂ) * ζ ^ 5 - ((5815 / 18723) : ℂ) * ζ ^ 6 + ((3797 / 37446) : ℂ) * ζ ^ 7 - ((1961 / 37446) : ℂ) * ζ ^ 8 + ((4989 / 12482) : ℂ) * ζ ^ 9 + ((2514 / 6241) : ℂ) * ζ ^ 10 - ((14329 / 37446) : ℂ) * ζ ^ 11 + ((1387 / 18723) : ℂ) * ζ ^ 12 - ((11029 / 37446) : ℂ) * ζ ^ 13 - ((3925 / 37446) : ℂ) * ζ ^ 14 - ((379 / 12482) : ℂ) * ζ ^ 15 + ((1231 / 12482) : ℂ) * ζ ^ 16 + ((5091 / 12482) : ℂ) * ζ ^ 17 + ((9523 / 18723) : ℂ) * ζ ^ 18 + ((3458 / 18723) : ℂ) * ζ ^ 19 - ((6785 / 37446) : ℂ) * ζ ^ 20 - ((6847 / 37446) : ℂ) * ζ ^ 21 - ((5236 / 6241) : ℂ) * ζ ^ 22 - ((1603 / 37446) : ℂ) * ζ ^ 23 + ((7114 / 18723) : ℂ) * ζ ^ 24 + ((4137 / 12482) : ℂ) * ζ ^ 25 + ((4732 / 6241) : ℂ) * ζ ^ 26 - ((2795 / 37446) : ℂ) * ζ ^ 27 - ((7733 / 37446) : ℂ) * ζ ^ 28 - ((8525 / 37446) : ℂ) * ζ ^ 29 - ((2299 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep08Coefficient09 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep08CoefficientIdentity09 :
    row18_reducedY44_combinationStep08Coefficient09 =
      row18_reducedY44_combinationStep07Coefficient09 +
        row18_reducedY44_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep08Coefficient09 row18_reducedY44_combinationStep07Coefficient09 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep08Coefficient10 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep08CoefficientIdentity10 :
    row18_reducedY44_combinationStep08Coefficient10 =
      row18_reducedY44_combinationStep07Coefficient10 +
        row18_reducedY44_combinationStep08Multiplier *
          (-((16 / 79) : ℂ) - ((35 / 316) : ℂ) * ζ ^ 1 + ((61 / 316) : ℂ) * ζ ^ 2 - ((87 / 316) : ℂ) * ζ ^ 3 + ((3 / 316) : ℂ) * ζ ^ 5 + ((6 / 79) : ℂ) * ζ ^ 8 + ((31 / 316) : ℂ) * ζ ^ 9 + ((14 / 79) : ℂ) * ζ ^ 11 + ((26 / 79) : ℂ) * ζ ^ 12 + ((35 / 316) : ℂ) * ζ ^ 13 + ((49 / 316) : ℂ) * ζ ^ 15 + ((35 / 316) : ℂ) * ζ ^ 17 - ((61 / 316) : ℂ) * ζ ^ 18 - ((13 / 79) : ℂ) * ζ ^ 21 - ((61 / 316) : ℂ) * ζ ^ 22 - ((32 / 79) : ℂ) * ζ ^ 24 - ((19 / 158) : ℂ) * ζ ^ 25 - ((13 / 79) : ℂ) * ζ ^ 27 - ((6 / 79) : ℂ) * ζ ^ 28 - ((35 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((14 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep08Coefficient10 row18_reducedY44_combinationStep07Coefficient10 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 (-((1043 / 18723) : ℂ) - ((6463 / 37446) : ℂ) * ζ ^ 1 - ((1174 / 6241) : ℂ) * ζ ^ 2 - ((4463 / 12482) : ℂ) * ζ ^ 3 + ((2 / 237) : ℂ) * ζ ^ 4 - ((3 / 158) : ℂ) * ζ ^ 5 + ((163 / 474) : ℂ) * ζ ^ 6 + ((18253 / 37446) : ℂ) * ζ ^ 7 - ((9389 / 37446) : ℂ) * ζ ^ 8 + ((3917 / 18723) : ℂ) * ζ ^ 9 - ((2903 / 6241) : ℂ) * ζ ^ 10 - ((20959 / 37446) : ℂ) * ζ ^ 11 - ((435 / 12482) : ℂ) * ζ ^ 12 - ((430 / 18723) : ℂ) * ζ ^ 13 - ((7522 / 18723) : ℂ) * ζ ^ 14 + ((10226 / 18723) : ℂ) * ζ ^ 15 - ((763 / 18723) : ℂ) * ζ ^ 16 - ((8369 / 37446) : ℂ) * ζ ^ 17 + ((431 / 6241) : ℂ) * ζ ^ 18 - ((3939 / 6241) : ℂ) * ζ ^ 19 + ((4609 / 18723) : ℂ) * ζ ^ 20 - ((3629 / 37446) : ℂ) * ζ ^ 21 + ((1925 / 18723) : ℂ) * ζ ^ 22 + ((2072 / 6241) : ℂ) * ζ ^ 23 - ((186 / 6241) : ℂ) * ζ ^ 24 + ((11809 / 37446) : ℂ) * ζ ^ 25 - ((5963 / 37446) : ℂ) * ζ ^ 26 + ((2042 / 18723) : ℂ) * ζ ^ 27 + ((913 / 12482) : ℂ) * ζ ^ 28 - ((1672 / 18723) : ℂ) * ζ ^ 29 + ((3388 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep08Coefficient11 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep08CoefficientIdentity11 :
    row18_reducedY44_combinationStep08Coefficient11 =
      row18_reducedY44_combinationStep07Coefficient11 +
        row18_reducedY44_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep08Coefficient11 row18_reducedY44_combinationStep07Coefficient11 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep08Coefficient12 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep08CoefficientIdentity12 :
    row18_reducedY44_combinationStep08Coefficient12 =
      row18_reducedY44_combinationStep07Coefficient12 +
        row18_reducedY44_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep08Coefficient12 row18_reducedY44_combinationStep07Coefficient12 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep08Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep08CoefficientIdentity13 :
    row18_reducedY44_combinationStep08Coefficient13 =
      row18_reducedY44_combinationStep07Coefficient13 +
        row18_reducedY44_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep08Coefficient13 row18_reducedY44_combinationStep07Coefficient13 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep08Coefficient14 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep08CoefficientIdentity14 :
    row18_reducedY44_combinationStep08Coefficient14 =
      row18_reducedY44_combinationStep07Coefficient14 +
        row18_reducedY44_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep08Coefficient14 row18_reducedY44_combinationStep07Coefficient14 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep08Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep08CoefficientIdentity15 :
    row18_reducedY44_combinationStep08Coefficient15 =
      row18_reducedY44_combinationStep07Coefficient15 +
        row18_reducedY44_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep08Coefficient15 row18_reducedY44_combinationStep07Coefficient15 row18_reducedY44_combinationStep08Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY44_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY44_combinationStep08Coefficient00) * Y 0 0
      + (row18_reducedY44_combinationStep08Coefficient01) * Y 0 1
      + (row18_reducedY44_combinationStep08Coefficient02) * Y 1 0
      + (row18_reducedY44_combinationStep08Coefficient03) * Y 1 1
      + (row18_reducedY44_combinationStep08Coefficient04) * Y 2 2
      + (row18_reducedY44_combinationStep08Coefficient05) * Y 2 3
      + (row18_reducedY44_combinationStep08Coefficient06) * Y 3 2
      + (row18_reducedY44_combinationStep08Coefficient07) * Y 3 3
      + (row18_reducedY44_combinationStep08Coefficient08) * Y 4 4
      + (row18_reducedY44_combinationStep08Coefficient09) * Y 4 5
      + (row18_reducedY44_combinationStep08Coefficient10) * Y 5 4
      + (row18_reducedY44_combinationStep08Coefficient11) * Y 5 5
      + (row18_reducedY44_combinationStep08Coefficient12) * Y 6 6
      + (row18_reducedY44_combinationStep08Coefficient13) * Y 6 7
      + (row18_reducedY44_combinationStep08Coefficient14) * Y 7 6
      + (row18_reducedY44_combinationStep08Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY44_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation14
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY44_combinationStep08CoefficientIdentity00,
      row18_reducedY44_combinationStep08CoefficientIdentity01,
      row18_reducedY44_combinationStep08CoefficientIdentity02,
      row18_reducedY44_combinationStep08CoefficientIdentity03,
      row18_reducedY44_combinationStep08CoefficientIdentity04,
      row18_reducedY44_combinationStep08CoefficientIdentity05,
      row18_reducedY44_combinationStep08CoefficientIdentity06,
      row18_reducedY44_combinationStep08CoefficientIdentity07,
      row18_reducedY44_combinationStep08CoefficientIdentity08,
      row18_reducedY44_combinationStep08CoefficientIdentity09,
      row18_reducedY44_combinationStep08CoefficientIdentity10,
      row18_reducedY44_combinationStep08CoefficientIdentity11,
      row18_reducedY44_combinationStep08CoefficientIdentity12,
      row18_reducedY44_combinationStep08CoefficientIdentity13,
      row18_reducedY44_combinationStep08CoefficientIdentity14,
      row18_reducedY44_combinationStep08CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY44_combinationStep08Multiplier * equation

private def row18_reducedY44_combinationStep09Multiplier : ℂ :=
  (-((208 / 79) : ℂ) - ((380 / 79) : ℂ) * ζ ^ 1 + ((60 / 79) : ℂ) * ζ ^ 2 - ((132 / 79) : ℂ) * ζ ^ 3 - ((306 / 79) : ℂ) * ζ ^ 5 + ((236 / 79) : ℂ) * ζ ^ 8 + ((156 / 79) : ℂ) * ζ ^ 9 - ((24 / 79) : ℂ) * ζ ^ 11 + ((180 / 79) : ℂ) * ζ ^ 12 + ((380 / 79) : ℂ) * ζ ^ 13 + ((58 / 79) : ℂ) * ζ ^ 15 + ((380 / 79) : ℂ) * ζ ^ 17 - ((60 / 79) : ℂ) * ζ ^ 18 + ((248 / 79) : ℂ) * ζ ^ 21 - ((60 / 79) : ℂ) * ζ ^ 22 - ((416 / 79) : ℂ) * ζ ^ 24 - ((74 / 79) : ℂ) * ζ ^ 25 + ((248 / 79) : ℂ) * ζ ^ 27 - ((236 / 79) : ℂ) * ζ ^ 28 - ((380 / 79) : ℂ) * ζ ^ 29 - ((160 / 79) : ℂ) * ζ ^ 30 + ((24 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY44_combinationStep09Coefficient00 : ℂ :=
  (-((249 / 79) : ℂ) - ((608 / 395) : ℂ) * ζ ^ 1 + ((1757 / 790) : ℂ) * ζ ^ 2 + ((1017 / 395) : ℂ) * ζ ^ 3 - ((379 / 395) : ℂ) * ζ ^ 5 + ((314 / 395) : ℂ) * ζ ^ 6 + ((623 / 158) : ℂ) * ζ ^ 8 + ((1166 / 395) : ℂ) * ζ ^ 9 + ((149 / 395) : ℂ) * ζ ^ 11 + ((623 / 158) : ℂ) * ζ ^ 12 + ((608 / 395) : ℂ) * ζ ^ 13 - ((788 / 395) : ℂ) * ζ ^ 15 + ((608 / 395) : ℂ) * ζ ^ 17 + ((1129 / 790) : ℂ) * ζ ^ 18 - ((409 / 395) : ℂ) * ζ ^ 21 - ((1757 / 790) : ℂ) * ζ ^ 22 - ((229 / 395) : ℂ) * ζ ^ 25 + ((409 / 395) : ℂ) * ζ ^ 27 - ((623 / 158) : ℂ) * ζ ^ 28 - ((608 / 395) : ℂ) * ζ ^ 29 + ((157 / 395) : ℂ) * ζ ^ 30 - ((149 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep09CoefficientIdentity00 :
    row18_reducedY44_combinationStep09Coefficient00 =
      row18_reducedY44_combinationStep08Coefficient00 +
        row18_reducedY44_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep09Coefficient00 row18_reducedY44_combinationStep08Coefficient00 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep09Coefficient01 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep09CoefficientIdentity01 :
    row18_reducedY44_combinationStep09Coefficient01 =
      row18_reducedY44_combinationStep08Coefficient01 +
        row18_reducedY44_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep09Coefficient01 row18_reducedY44_combinationStep08Coefficient01 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep09Coefficient02 : ℂ :=
  (((311 / 395) : ℂ) + ((73 / 395) : ℂ) * ζ ^ 1 - ((879 / 790) : ℂ) * ζ ^ 2 + ((155 / 158) : ℂ) * ζ ^ 3 - ((451 / 395) : ℂ) * ζ ^ 5 - ((411 / 790) : ℂ) * ζ ^ 6 - ((853 / 395) : ℂ) * ζ ^ 8 - ((597 / 790) : ℂ) * ζ ^ 9 - ((223 / 158) : ℂ) * ζ ^ 11 - ((234 / 395) : ℂ) * ζ ^ 12 - ((73 / 395) : ℂ) * ζ ^ 13 - ((155 / 158) : ℂ) * ζ ^ 15 - ((73 / 395) : ℂ) * ζ ^ 17 + ((257 / 790) : ℂ) * ζ ^ 18 + ((524 / 395) : ℂ) * ζ ^ 21 + ((879 / 790) : ℂ) * ζ ^ 22 + ((879 / 790) : ℂ) * ζ ^ 24 + ((524 / 395) : ℂ) * ζ ^ 25 + ((223 / 158) : ℂ) * ζ ^ 27 + ((853 / 395) : ℂ) * ζ ^ 28 + ((73 / 395) : ℂ) * ζ ^ 29 + ((827 / 790) : ℂ) * ζ ^ 30 + ((223 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep09CoefficientIdentity02 :
    row18_reducedY44_combinationStep09Coefficient02 =
      row18_reducedY44_combinationStep08Coefficient02 +
        row18_reducedY44_combinationStep09Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep09Coefficient02 row18_reducedY44_combinationStep08Coefficient02 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 (((4978 / 6241) : ℂ) + ((1363 / 6241) : ℂ) * ζ ^ 1 - ((2345 / 12482) : ℂ) * ζ ^ 2 + ((2043 / 12482) : ℂ) * ζ ^ 3 - ((2434 / 6241) : ℂ) * ζ ^ 4 + ((1310 / 6241) : ℂ) * ζ ^ 5 + ((10323 / 12482) : ℂ) * ζ ^ 6 + ((3050 / 6241) : ℂ) * ζ ^ 7 - ((2498 / 6241) : ℂ) * ζ ^ 8 - ((1739 / 12482) : ℂ) * ζ ^ 9 + ((5095 / 12482) : ℂ) * ζ ^ 10 - ((4917 / 12482) : ℂ) * ζ ^ 11 + ((4607 / 6241) : ℂ) * ζ ^ 12 - ((1753 / 6241) : ℂ) * ζ ^ 13 - ((2961 / 6241) : ℂ) * ζ ^ 14 + ((8021 / 12482) : ℂ) * ζ ^ 15 - ((347 / 6241) : ℂ) * ζ ^ 16 + ((1852 / 6241) : ℂ) * ζ ^ 17 + ((505 / 6241) : ℂ) * ζ ^ 18 - ((728 / 6241) : ℂ) * ζ ^ 19 + ((1667 / 6241) : ℂ) * ζ ^ 20 - ((6627 / 12482) : ℂ) * ζ ^ 21 - ((4319 / 12482) : ℂ) * ζ ^ 22 + ((92 / 6241) : ℂ) * ζ ^ 23 + ((4045 / 12482) : ℂ) * ζ ^ 24 + ((7860 / 6241) : ℂ) * ζ ^ 25 + ((13 / 6241) : ℂ) * ζ ^ 26 - ((3509 / 6241) : ℂ) * ζ ^ 27 - ((573 / 6241) : ℂ) * ζ ^ 28 + ((888 / 6241) : ℂ) * ζ ^ 29 - ((90 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep09Coefficient03 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep09CoefficientIdentity03 :
    row18_reducedY44_combinationStep09Coefficient03 =
      row18_reducedY44_combinationStep08Coefficient03 +
        row18_reducedY44_combinationStep09Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep09Coefficient03 row18_reducedY44_combinationStep08Coefficient03 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 (-((4466 / 6241) : ℂ) - ((3988 / 6241) : ℂ) * ζ ^ 1 - ((6751 / 12482) : ℂ) * ζ ^ 2 - ((1189 / 12482) : ℂ) * ζ ^ 3 + ((4723 / 6241) : ℂ) * ζ ^ 4 + ((1569 / 12482) : ℂ) * ζ ^ 5 - ((125 / 6241) : ℂ) * ζ ^ 6 - ((1633 / 6241) : ℂ) * ζ ^ 7 - ((4183 / 6241) : ℂ) * ζ ^ 8 + ((5487 / 6241) : ℂ) * ζ ^ 9 + ((1469 / 6241) : ℂ) * ζ ^ 10 + ((2829 / 6241) : ℂ) * ζ ^ 11 + ((1961 / 12482) : ℂ) * ζ ^ 12 - ((293 / 6241) : ℂ) * ζ ^ 13 + ((139 / 6241) : ℂ) * ζ ^ 14 + ((2645 / 12482) : ℂ) * ζ ^ 15 - ((191 / 6241) : ℂ) * ζ ^ 16 + ((3653 / 6241) : ℂ) * ζ ^ 17 + ((2886 / 6241) : ℂ) * ζ ^ 18 + ((3632 / 6241) : ℂ) * ζ ^ 19 - ((3885 / 6241) : ℂ) * ζ ^ 20 - ((2547 / 6241) : ℂ) * ζ ^ 21 + ((2357 / 12482) : ℂ) * ζ ^ 22 + ((3984 / 6241) : ℂ) * ζ ^ 23 + ((697 / 6241) : ℂ) * ζ ^ 24 - ((627 / 6241) : ℂ) * ζ ^ 25 - ((2849 / 6241) : ℂ) * ζ ^ 26 - ((718 / 6241) : ℂ) * ζ ^ 27 + ((916 / 6241) : ℂ) * ζ ^ 28 + ((8 / 79) : ℂ) * ζ ^ 29 - ((84 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep09Coefficient04 : ℂ :=
  (((249 / 79) : ℂ) + ((608 / 395) : ℂ) * ζ ^ 1 - ((1757 / 790) : ℂ) * ζ ^ 2 - ((1017 / 395) : ℂ) * ζ ^ 3 + ((379 / 395) : ℂ) * ζ ^ 5 - ((314 / 395) : ℂ) * ζ ^ 6 - ((623 / 158) : ℂ) * ζ ^ 8 - ((1166 / 395) : ℂ) * ζ ^ 9 - ((149 / 395) : ℂ) * ζ ^ 11 - ((623 / 158) : ℂ) * ζ ^ 12 - ((608 / 395) : ℂ) * ζ ^ 13 + ((788 / 395) : ℂ) * ζ ^ 15 - ((608 / 395) : ℂ) * ζ ^ 17 - ((1129 / 790) : ℂ) * ζ ^ 18 + ((409 / 395) : ℂ) * ζ ^ 21 + ((1757 / 790) : ℂ) * ζ ^ 22 + ((229 / 395) : ℂ) * ζ ^ 25 - ((409 / 395) : ℂ) * ζ ^ 27 + ((623 / 158) : ℂ) * ζ ^ 28 + ((608 / 395) : ℂ) * ζ ^ 29 - ((157 / 395) : ℂ) * ζ ^ 30 + ((149 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep09CoefficientIdentity04 :
    row18_reducedY44_combinationStep09Coefficient04 =
      row18_reducedY44_combinationStep08Coefficient04 +
        row18_reducedY44_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep09Coefficient04 row18_reducedY44_combinationStep08Coefficient04 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep09Coefficient05 : ℂ :=
  (((39 / 79) : ℂ) + ((126 / 79) : ℂ) * ζ ^ 1 + ((15 / 158) : ℂ) * ζ ^ 2 - ((181 / 79) : ℂ) * ζ ^ 5 - ((63 / 158) : ℂ) * ζ ^ 6 - ((63 / 158) : ℂ) * ζ ^ 8 - ((181 / 79) : ℂ) * ζ ^ 9 - ((393 / 158) : ℂ) * ζ ^ 11 - ((59 / 79) : ℂ) * ζ ^ 12 - ((126 / 79) : ℂ) * ζ ^ 13 - ((50 / 79) : ℂ) * ζ ^ 15 - ((126 / 79) : ℂ) * ζ ^ 17 - ((52 / 79) : ℂ) * ζ ^ 18 + ((55 / 158) : ℂ) * ζ ^ 21 - ((15 / 158) : ℂ) * ζ ^ 22 + ((167 / 158) : ℂ) * ζ ^ 24 + ((307 / 79) : ℂ) * ζ ^ 25 + ((50 / 79) : ℂ) * ζ ^ 27 + ((63 / 158) : ℂ) * ζ ^ 28 + ((126 / 79) : ℂ) * ζ ^ 29 + ((55 / 158) : ℂ) * ζ ^ 30 + ((393 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY44_combinationStep09CoefficientIdentity05 :
    row18_reducedY44_combinationStep09Coefficient05 =
      row18_reducedY44_combinationStep08Coefficient05 +
        row18_reducedY44_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep09Coefficient05 row18_reducedY44_combinationStep08Coefficient05 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep09Coefficient06 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep09CoefficientIdentity06 :
    row18_reducedY44_combinationStep09Coefficient06 =
      row18_reducedY44_combinationStep08Coefficient06 +
        row18_reducedY44_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep09Coefficient06 row18_reducedY44_combinationStep08Coefficient06 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep09Coefficient07 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep09CoefficientIdentity07 :
    row18_reducedY44_combinationStep09Coefficient07 =
      row18_reducedY44_combinationStep08Coefficient07 +
        row18_reducedY44_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep09Coefficient07 row18_reducedY44_combinationStep08Coefficient07 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep09Coefficient08 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY44_combinationStep09CoefficientIdentity08 :
    row18_reducedY44_combinationStep09Coefficient08 =
      row18_reducedY44_combinationStep08Coefficient08 +
        row18_reducedY44_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep09Coefficient08 row18_reducedY44_combinationStep08Coefficient08 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep09Coefficient09 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep09CoefficientIdentity09 :
    row18_reducedY44_combinationStep09Coefficient09 =
      row18_reducedY44_combinationStep08Coefficient09 +
        row18_reducedY44_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep09Coefficient09 row18_reducedY44_combinationStep08Coefficient09 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep09Coefficient10 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep09CoefficientIdentity10 :
    row18_reducedY44_combinationStep09Coefficient10 =
      row18_reducedY44_combinationStep08Coefficient10 +
        row18_reducedY44_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep09Coefficient10 row18_reducedY44_combinationStep08Coefficient10 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep09Coefficient11 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep09CoefficientIdentity11 :
    row18_reducedY44_combinationStep09Coefficient11 =
      row18_reducedY44_combinationStep08Coefficient11 +
        row18_reducedY44_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep09Coefficient11 row18_reducedY44_combinationStep08Coefficient11 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep09Coefficient12 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep09CoefficientIdentity12 :
    row18_reducedY44_combinationStep09Coefficient12 =
      row18_reducedY44_combinationStep08Coefficient12 +
        row18_reducedY44_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep09Coefficient12 row18_reducedY44_combinationStep08Coefficient12 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep09Coefficient13 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep09CoefficientIdentity13 :
    row18_reducedY44_combinationStep09Coefficient13 =
      row18_reducedY44_combinationStep08Coefficient13 +
        row18_reducedY44_combinationStep09Multiplier *
          (((5 / 316) : ℂ) - ((3 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((33 / 158) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 + ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 + ((3 / 316) : ℂ) * ζ ^ 9 + ((33 / 316) : ℂ) * ζ ^ 11 + ((3 / 79) : ℂ) * ζ ^ 12 + ((3 / 316) : ℂ) * ζ ^ 13 + ((35 / 158) : ℂ) * ζ ^ 15 + ((3 / 316) : ℂ) * ζ ^ 17 + ((19 / 316) : ℂ) * ζ ^ 18 + ((45 / 158) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((1 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 - ((3 / 316) : ℂ) * ζ ^ 29 + ((13 / 79) : ℂ) * ζ ^ 30 - ((33 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep09Coefficient13 row18_reducedY44_combinationStep08Coefficient13 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 (((3058 / 6241) : ℂ) + ((392 / 6241) : ℂ) * ζ ^ 1 - ((2841 / 12482) : ℂ) * ζ ^ 2 - ((103 / 6241) : ℂ) * ζ ^ 3 + ((3836 / 6241) : ℂ) * ζ ^ 4 - ((4895 / 12482) : ℂ) * ζ ^ 5 - ((2491 / 12482) : ℂ) * ζ ^ 6 - ((12839 / 12482) : ℂ) * ζ ^ 7 + ((2017 / 12482) : ℂ) * ζ ^ 8 + ((10211 / 12482) : ℂ) * ζ ^ 9 + ((2538 / 6241) : ℂ) * ζ ^ 10 - ((1486 / 6241) : ℂ) * ζ ^ 11 - ((24711 / 12482) : ℂ) * ζ ^ 12 - ((6425 / 12482) : ℂ) * ζ ^ 13 - ((1453 / 6241) : ℂ) * ζ ^ 14 + ((5079 / 12482) : ℂ) * ζ ^ 15 + ((2641 / 12482) : ℂ) * ζ ^ 16 - ((707 / 12482) : ℂ) * ζ ^ 17 - ((12423 / 12482) : ℂ) * ζ ^ 18 - ((1465 / 6241) : ℂ) * ζ ^ 19 - ((10497 / 12482) : ℂ) * ζ ^ 20 - ((3557 / 6241) : ℂ) * ζ ^ 21 - ((2515 / 12482) : ℂ) * ζ ^ 22 + ((7701 / 6241) : ℂ) * ζ ^ 23 - ((6705 / 12482) : ℂ) * ζ ^ 24 - ((2191 / 6241) : ℂ) * ζ ^ 25 - ((6207 / 6241) : ℂ) * ζ ^ 26 - ((2633 / 6241) : ℂ) * ζ ^ 27 + ((1037 / 6241) : ℂ) * ζ ^ 28 + ((1632 / 6241) : ℂ) * ζ ^ 29 - ((198 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep09Coefficient14 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep09CoefficientIdentity14 :
    row18_reducedY44_combinationStep09Coefficient14 =
      row18_reducedY44_combinationStep08Coefficient14 +
        row18_reducedY44_combinationStep09Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep09Coefficient14 row18_reducedY44_combinationStep08Coefficient14 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep09Coefficient15 : ℂ :=
  (-(1 : ℂ))

private theorem row18_reducedY44_combinationStep09CoefficientIdentity15 :
    row18_reducedY44_combinationStep09Coefficient15 =
      row18_reducedY44_combinationStep08Coefficient15 +
        row18_reducedY44_combinationStep09Multiplier *
          (-((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((35 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep09Coefficient15 row18_reducedY44_combinationStep08Coefficient15 row18_reducedY44_combinationStep09Multiplier
  close_cyclotomic_row18 (((4466 / 6241) : ℂ) + ((3988 / 6241) : ℂ) * ζ ^ 1 + ((6751 / 12482) : ℂ) * ζ ^ 2 + ((1189 / 12482) : ℂ) * ζ ^ 3 - ((4723 / 6241) : ℂ) * ζ ^ 4 - ((1569 / 12482) : ℂ) * ζ ^ 5 + ((125 / 6241) : ℂ) * ζ ^ 6 + ((1633 / 6241) : ℂ) * ζ ^ 7 + ((4183 / 6241) : ℂ) * ζ ^ 8 - ((5487 / 6241) : ℂ) * ζ ^ 9 - ((1469 / 6241) : ℂ) * ζ ^ 10 - ((2829 / 6241) : ℂ) * ζ ^ 11 - ((1961 / 12482) : ℂ) * ζ ^ 12 + ((293 / 6241) : ℂ) * ζ ^ 13 - ((139 / 6241) : ℂ) * ζ ^ 14 - ((2645 / 12482) : ℂ) * ζ ^ 15 + ((191 / 6241) : ℂ) * ζ ^ 16 - ((3653 / 6241) : ℂ) * ζ ^ 17 - ((2886 / 6241) : ℂ) * ζ ^ 18 - ((3632 / 6241) : ℂ) * ζ ^ 19 + ((3885 / 6241) : ℂ) * ζ ^ 20 + ((2547 / 6241) : ℂ) * ζ ^ 21 - ((2357 / 12482) : ℂ) * ζ ^ 22 - ((3984 / 6241) : ℂ) * ζ ^ 23 - ((697 / 6241) : ℂ) * ζ ^ 24 + ((627 / 6241) : ℂ) * ζ ^ 25 + ((2849 / 6241) : ℂ) * ζ ^ 26 + ((718 / 6241) : ℂ) * ζ ^ 27 - ((916 / 6241) : ℂ) * ζ ^ 28 - ((8 / 79) : ℂ) * ζ ^ 29 + ((84 / 6241) : ℂ) * ζ ^ 30)

private theorem row18_reducedY44_combinationStep09
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY44_combinationStep09Coefficient00) * Y 0 0
      + (row18_reducedY44_combinationStep09Coefficient01) * Y 0 1
      + (row18_reducedY44_combinationStep09Coefficient02) * Y 1 0
      + (row18_reducedY44_combinationStep09Coefficient03) * Y 1 1
      + (row18_reducedY44_combinationStep09Coefficient04) * Y 2 2
      + (row18_reducedY44_combinationStep09Coefficient05) * Y 2 3
      + (row18_reducedY44_combinationStep09Coefficient06) * Y 3 2
      + (row18_reducedY44_combinationStep09Coefficient07) * Y 3 3
      + (row18_reducedY44_combinationStep09Coefficient08) * Y 4 4
      + (row18_reducedY44_combinationStep09Coefficient09) * Y 4 5
      + (row18_reducedY44_combinationStep09Coefficient10) * Y 5 4
      + (row18_reducedY44_combinationStep09Coefficient11) * Y 5 5
      + (row18_reducedY44_combinationStep09Coefficient12) * Y 6 6
      + (row18_reducedY44_combinationStep09Coefficient13) * Y 6 7
      + (row18_reducedY44_combinationStep09Coefficient14) * Y 7 6
      + (row18_reducedY44_combinationStep09Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY44_combinationStep08 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation17
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY44_combinationStep09CoefficientIdentity00,
      row18_reducedY44_combinationStep09CoefficientIdentity01,
      row18_reducedY44_combinationStep09CoefficientIdentity02,
      row18_reducedY44_combinationStep09CoefficientIdentity03,
      row18_reducedY44_combinationStep09CoefficientIdentity04,
      row18_reducedY44_combinationStep09CoefficientIdentity05,
      row18_reducedY44_combinationStep09CoefficientIdentity06,
      row18_reducedY44_combinationStep09CoefficientIdentity07,
      row18_reducedY44_combinationStep09CoefficientIdentity08,
      row18_reducedY44_combinationStep09CoefficientIdentity09,
      row18_reducedY44_combinationStep09CoefficientIdentity10,
      row18_reducedY44_combinationStep09CoefficientIdentity11,
      row18_reducedY44_combinationStep09CoefficientIdentity12,
      row18_reducedY44_combinationStep09CoefficientIdentity13,
      row18_reducedY44_combinationStep09CoefficientIdentity14,
      row18_reducedY44_combinationStep09CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY44_combinationStep09Multiplier * equation

private def row18_reducedY44_combinationStep10Multiplier : ℂ :=
  (((628 / 79) : ℂ) + ((2852 / 395) : ℂ) * ζ ^ 1 + ((748 / 395) : ℂ) * ζ ^ 2 - ((3008 / 395) : ℂ) * ζ ^ 3 + ((2506 / 395) : ℂ) * ζ ^ 5 + ((4832 / 395) : ℂ) * ζ ^ 6 - ((120 / 79) : ℂ) * ζ ^ 8 - ((404 / 395) : ℂ) * ζ ^ 9 + ((2604 / 395) : ℂ) * ζ ^ 11 - ((120 / 79) : ℂ) * ζ ^ 12 - ((2852 / 395) : ℂ) * ζ ^ 13 + ((2662 / 395) : ℂ) * ζ ^ 15 - ((2852 / 395) : ℂ) * ζ ^ 17 - ((4084 / 395) : ℂ) * ζ ^ 18 + ((156 / 395) : ℂ) * ζ ^ 21 - ((748 / 395) : ℂ) * ζ ^ 22 + ((346 / 395) : ℂ) * ζ ^ 25 - ((156 / 395) : ℂ) * ζ ^ 27 + ((120 / 79) : ℂ) * ζ ^ 28 + ((2852 / 395) : ℂ) * ζ ^ 29 + ((2416 / 395) : ℂ) * ζ ^ 30 - ((2604 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY44_combinationStep10Coefficient00 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep10CoefficientIdentity00 :
    row18_reducedY44_combinationStep10Coefficient00 =
      row18_reducedY44_combinationStep09Coefficient00 +
        row18_reducedY44_combinationStep10Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep10Coefficient00 row18_reducedY44_combinationStep09Coefficient00 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 (-((17787 / 6241) : ℂ) - ((609 / 395) : ℂ) * ζ ^ 1 - ((1169 / 12482) : ℂ) * ζ ^ 2 + ((7872 / 31205) : ℂ) * ζ ^ 3 + ((80599 / 31205) : ℂ) * ζ ^ 4 + ((65871 / 31205) : ℂ) * ζ ^ 5 - ((2085 / 6241) : ℂ) * ζ ^ 6 - ((205677 / 62410) : ℂ) * ζ ^ 7 - ((73562 / 31205) : ℂ) * ζ ^ 8 + ((34787 / 31205) : ℂ) * ζ ^ 9 + ((1643 / 6241) : ℂ) * ζ ^ 10 + ((229219 / 62410) : ℂ) * ζ ^ 11 + ((65769 / 62410) : ℂ) * ζ ^ 12 - ((256473 / 62410) : ℂ) * ζ ^ 13 - ((26731 / 31205) : ℂ) * ζ ^ 14 - ((134131 / 62410) : ℂ) * ζ ^ 15 - ((74443 / 31205) : ℂ) * ζ ^ 16 + ((228823 / 62410) : ℂ) * ζ ^ 17 + ((22167 / 31205) : ℂ) * ζ ^ 18 + ((19422 / 31205) : ℂ) * ζ ^ 19 + ((48167 / 31205) : ℂ) * ζ ^ 20 - ((123121 / 62410) : ℂ) * ζ ^ 21 + ((1169 / 12482) : ℂ) * ζ ^ 22 + ((49864 / 31205) : ℂ) * ζ ^ 23 - ((3972 / 31205) : ℂ) * ζ ^ 24 + ((14721 / 31205) : ℂ) * ζ ^ 25 + ((10141 / 31205) : ℂ) * ζ ^ 26 - ((42937 / 31205) : ℂ) * ζ ^ 27 - ((2497 / 6241) : ℂ) * ζ ^ 28 + ((392 / 6241) : ℂ) * ζ ^ 29 + ((9114 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep10Coefficient01 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep10CoefficientIdentity01 :
    row18_reducedY44_combinationStep10Coefficient01 =
      row18_reducedY44_combinationStep09Coefficient01 +
        row18_reducedY44_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep10Coefficient01 row18_reducedY44_combinationStep09Coefficient01 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep10Coefficient02 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep10CoefficientIdentity02 :
    row18_reducedY44_combinationStep10Coefficient02 =
      row18_reducedY44_combinationStep09Coefficient02 +
        row18_reducedY44_combinationStep10Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep10Coefficient02 row18_reducedY44_combinationStep09Coefficient02 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 (-((5261 / 31205) : ℂ) - ((51942 / 31205) : ℂ) * ζ ^ 1 - ((121997 / 62410) : ℂ) * ζ ^ 2 - ((32813 / 62410) : ℂ) * ζ ^ 3 - ((6503 / 6241) : ℂ) * ζ ^ 4 - ((14317 / 6241) : ℂ) * ζ ^ 5 + ((79673 / 62410) : ℂ) * ζ ^ 6 - ((8548 / 31205) : ℂ) * ζ ^ 7 + ((24229 / 62410) : ℂ) * ζ ^ 8 - ((62421 / 62410) : ℂ) * ζ ^ 9 - ((91783 / 62410) : ℂ) * ζ ^ 10 - ((118199 / 62410) : ℂ) * ζ ^ 11 + ((51751 / 62410) : ℂ) * ζ ^ 12 + ((87694 / 31205) : ℂ) * ζ ^ 13 - ((22683 / 62410) : ℂ) * ζ ^ 14 + ((217837 / 62410) : ℂ) * ζ ^ 15 + ((404 / 395) : ℂ) * ζ ^ 16 - ((25632 / 31205) : ℂ) * ζ ^ 17 + ((2699 / 31205) : ℂ) * ζ ^ 18 - ((26674 / 31205) : ℂ) * ζ ^ 19 + ((781 / 31205) : ℂ) * ζ ^ 20 + ((177131 / 62410) : ℂ) * ζ ^ 21 + ((26817 / 12482) : ℂ) * ζ ^ 22 + ((30117 / 31205) : ℂ) * ζ ^ 23 - ((16851 / 31205) : ℂ) * ζ ^ 24 - ((77293 / 31205) : ℂ) * ζ ^ 25 - ((67367 / 31205) : ℂ) * ζ ^ 26 - ((31971 / 31205) : ℂ) * ζ ^ 27 - ((12699 / 6241) : ℂ) * ζ ^ 28 - ((19488 / 31205) : ℂ) * ζ ^ 29 + ((54684 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep10Coefficient03 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep10CoefficientIdentity03 :
    row18_reducedY44_combinationStep10Coefficient03 =
      row18_reducedY44_combinationStep09Coefficient03 +
        row18_reducedY44_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep10Coefficient03 row18_reducedY44_combinationStep09Coefficient03 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep10Coefficient04 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep10CoefficientIdentity04 :
    row18_reducedY44_combinationStep10Coefficient04 =
      row18_reducedY44_combinationStep09Coefficient04 +
        row18_reducedY44_combinationStep10Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep10Coefficient04 row18_reducedY44_combinationStep09Coefficient04 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 (((17787 / 6241) : ℂ) + ((609 / 395) : ℂ) * ζ ^ 1 + ((1169 / 12482) : ℂ) * ζ ^ 2 - ((7872 / 31205) : ℂ) * ζ ^ 3 - ((80599 / 31205) : ℂ) * ζ ^ 4 - ((65871 / 31205) : ℂ) * ζ ^ 5 + ((2085 / 6241) : ℂ) * ζ ^ 6 + ((205677 / 62410) : ℂ) * ζ ^ 7 + ((73562 / 31205) : ℂ) * ζ ^ 8 - ((34787 / 31205) : ℂ) * ζ ^ 9 - ((1643 / 6241) : ℂ) * ζ ^ 10 - ((229219 / 62410) : ℂ) * ζ ^ 11 - ((65769 / 62410) : ℂ) * ζ ^ 12 + ((256473 / 62410) : ℂ) * ζ ^ 13 + ((26731 / 31205) : ℂ) * ζ ^ 14 + ((134131 / 62410) : ℂ) * ζ ^ 15 + ((74443 / 31205) : ℂ) * ζ ^ 16 - ((228823 / 62410) : ℂ) * ζ ^ 17 - ((22167 / 31205) : ℂ) * ζ ^ 18 - ((19422 / 31205) : ℂ) * ζ ^ 19 - ((48167 / 31205) : ℂ) * ζ ^ 20 + ((123121 / 62410) : ℂ) * ζ ^ 21 - ((1169 / 12482) : ℂ) * ζ ^ 22 - ((49864 / 31205) : ℂ) * ζ ^ 23 + ((3972 / 31205) : ℂ) * ζ ^ 24 - ((14721 / 31205) : ℂ) * ζ ^ 25 - ((10141 / 31205) : ℂ) * ζ ^ 26 + ((42937 / 31205) : ℂ) * ζ ^ 27 + ((2497 / 6241) : ℂ) * ζ ^ 28 - ((392 / 6241) : ℂ) * ζ ^ 29 - ((9114 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep10Coefficient05 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep10CoefficientIdentity05 :
    row18_reducedY44_combinationStep10Coefficient05 =
      row18_reducedY44_combinationStep09Coefficient05 +
        row18_reducedY44_combinationStep10Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY44_combinationStep10Coefficient05 row18_reducedY44_combinationStep09Coefficient05 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 (((13914 / 6241) : ℂ) + ((84837 / 31205) : ℂ) * ζ ^ 1 - ((8067 / 62410) : ℂ) * ζ ^ 2 - ((61671 / 31205) : ℂ) * ζ ^ 3 - ((57717 / 31205) : ℂ) * ζ ^ 4 - ((225231 / 62410) : ℂ) * ζ ^ 5 - ((3268 / 31205) : ℂ) * ζ ^ 6 - ((45643 / 62410) : ℂ) * ζ ^ 7 - ((18299 / 12482) : ℂ) * ζ ^ 8 + ((67227 / 62410) : ℂ) * ζ ^ 9 - ((18866 / 31205) : ℂ) * ζ ^ 10 + ((130961 / 31205) : ℂ) * ζ ^ 11 + ((182473 / 62410) : ℂ) * ζ ^ 12 - ((135783 / 62410) : ℂ) * ζ ^ 13 - ((369451 / 62410) : ℂ) * ζ ^ 14 - ((29477 / 12482) : ℂ) * ζ ^ 15 + ((149937 / 62410) : ℂ) * ζ ^ 16 + ((254171 / 62410) : ℂ) * ζ ^ 17 + ((3299 / 6241) : ℂ) * ζ ^ 18 - ((12292 / 31205) : ℂ) * ζ ^ 19 - ((162073 / 62410) : ℂ) * ζ ^ 20 + ((40649 / 31205) : ℂ) * ζ ^ 21 + ((95151 / 31205) : ℂ) * ζ ^ 22 + ((4636 / 6241) : ℂ) * ζ ^ 23 + ((18395 / 6241) : ℂ) * ζ ^ 24 + ((77246 / 31205) : ℂ) * ζ ^ 25 - ((28647 / 31205) : ℂ) * ζ ^ 26 - ((127152 / 31205) : ℂ) * ζ ^ 27 - ((149238 / 31205) : ℂ) * ζ ^ 28 - ((73566 / 31205) : ℂ) * ζ ^ 29 + ((23436 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY44_combinationStep10Coefficient06 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep10CoefficientIdentity06 :
    row18_reducedY44_combinationStep10Coefficient06 =
      row18_reducedY44_combinationStep09Coefficient06 +
        row18_reducedY44_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep10Coefficient06 row18_reducedY44_combinationStep09Coefficient06 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep10Coefficient07 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep10CoefficientIdentity07 :
    row18_reducedY44_combinationStep10Coefficient07 =
      row18_reducedY44_combinationStep09Coefficient07 +
        row18_reducedY44_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep10Coefficient07 row18_reducedY44_combinationStep09Coefficient07 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep10Coefficient08 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY44_combinationStep10CoefficientIdentity08 :
    row18_reducedY44_combinationStep10Coefficient08 =
      row18_reducedY44_combinationStep09Coefficient08 +
        row18_reducedY44_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep10Coefficient08 row18_reducedY44_combinationStep09Coefficient08 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep10Coefficient09 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep10CoefficientIdentity09 :
    row18_reducedY44_combinationStep10Coefficient09 =
      row18_reducedY44_combinationStep09Coefficient09 +
        row18_reducedY44_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep10Coefficient09 row18_reducedY44_combinationStep09Coefficient09 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep10Coefficient10 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep10CoefficientIdentity10 :
    row18_reducedY44_combinationStep10Coefficient10 =
      row18_reducedY44_combinationStep09Coefficient10 +
        row18_reducedY44_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep10Coefficient10 row18_reducedY44_combinationStep09Coefficient10 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep10Coefficient11 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep10CoefficientIdentity11 :
    row18_reducedY44_combinationStep10Coefficient11 =
      row18_reducedY44_combinationStep09Coefficient11 +
        row18_reducedY44_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep10Coefficient11 row18_reducedY44_combinationStep09Coefficient11 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep10Coefficient12 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep10CoefficientIdentity12 :
    row18_reducedY44_combinationStep10Coefficient12 =
      row18_reducedY44_combinationStep09Coefficient12 +
        row18_reducedY44_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep10Coefficient12 row18_reducedY44_combinationStep09Coefficient12 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep10Coefficient13 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep10CoefficientIdentity13 :
    row18_reducedY44_combinationStep10Coefficient13 =
      row18_reducedY44_combinationStep09Coefficient13 +
        row18_reducedY44_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep10Coefficient13 row18_reducedY44_combinationStep09Coefficient13 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep10Coefficient14 : ℂ :=
  0

private theorem row18_reducedY44_combinationStep10CoefficientIdentity14 :
    row18_reducedY44_combinationStep10Coefficient14 =
      row18_reducedY44_combinationStep09Coefficient14 +
        row18_reducedY44_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep10Coefficient14 row18_reducedY44_combinationStep09Coefficient14 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY44_combinationStep10Coefficient15 : ℂ :=
  (-(1 : ℂ))

private theorem row18_reducedY44_combinationStep10CoefficientIdentity15 :
    row18_reducedY44_combinationStep10Coefficient15 =
      row18_reducedY44_combinationStep09Coefficient15 +
        row18_reducedY44_combinationStep10Multiplier *
          0 := by
  unfold row18_reducedY44_combinationStep10Coefficient15 row18_reducedY44_combinationStep09Coefficient15 row18_reducedY44_combinationStep10Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY44_combinationStep10
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY44_combinationStep10Coefficient00) * Y 0 0
      + (row18_reducedY44_combinationStep10Coefficient01) * Y 0 1
      + (row18_reducedY44_combinationStep10Coefficient02) * Y 1 0
      + (row18_reducedY44_combinationStep10Coefficient03) * Y 1 1
      + (row18_reducedY44_combinationStep10Coefficient04) * Y 2 2
      + (row18_reducedY44_combinationStep10Coefficient05) * Y 2 3
      + (row18_reducedY44_combinationStep10Coefficient06) * Y 3 2
      + (row18_reducedY44_combinationStep10Coefficient07) * Y 3 3
      + (row18_reducedY44_combinationStep10Coefficient08) * Y 4 4
      + (row18_reducedY44_combinationStep10Coefficient09) * Y 4 5
      + (row18_reducedY44_combinationStep10Coefficient10) * Y 5 4
      + (row18_reducedY44_combinationStep10Coefficient11) * Y 5 5
      + (row18_reducedY44_combinationStep10Coefficient12) * Y 6 6
      + (row18_reducedY44_combinationStep10Coefficient13) * Y 6 7
      + (row18_reducedY44_combinationStep10Coefficient14) * Y 7 6
      + (row18_reducedY44_combinationStep10Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY44_combinationStep09 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY44_combinationStep10CoefficientIdentity00,
      row18_reducedY44_combinationStep10CoefficientIdentity01,
      row18_reducedY44_combinationStep10CoefficientIdentity02,
      row18_reducedY44_combinationStep10CoefficientIdentity03,
      row18_reducedY44_combinationStep10CoefficientIdentity04,
      row18_reducedY44_combinationStep10CoefficientIdentity05,
      row18_reducedY44_combinationStep10CoefficientIdentity06,
      row18_reducedY44_combinationStep10CoefficientIdentity07,
      row18_reducedY44_combinationStep10CoefficientIdentity08,
      row18_reducedY44_combinationStep10CoefficientIdentity09,
      row18_reducedY44_combinationStep10CoefficientIdentity10,
      row18_reducedY44_combinationStep10CoefficientIdentity11,
      row18_reducedY44_combinationStep10CoefficientIdentity12,
      row18_reducedY44_combinationStep10CoefficientIdentity13,
      row18_reducedY44_combinationStep10CoefficientIdentity14,
      row18_reducedY44_combinationStep10CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY44_combinationStep10Multiplier * equation

theorem row18_reducedY44
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 4 4 = Y 7 7 := by
  have reduced :=
    row18_reducedY44_combinationStep10 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY44_combinationStep10Coefficient00,
      row18_reducedY44_combinationStep10Coefficient01,
      row18_reducedY44_combinationStep10Coefficient02,
      row18_reducedY44_combinationStep10Coefficient03,
      row18_reducedY44_combinationStep10Coefficient04,
      row18_reducedY44_combinationStep10Coefficient05,
      row18_reducedY44_combinationStep10Coefficient06,
      row18_reducedY44_combinationStep10Coefficient07,
      row18_reducedY44_combinationStep10Coefficient08,
      row18_reducedY44_combinationStep10Coefficient09,
      row18_reducedY44_combinationStep10Coefficient10,
      row18_reducedY44_combinationStep10Coefficient11,
      row18_reducedY44_combinationStep10Coefficient12,
      row18_reducedY44_combinationStep10Coefficient13,
      row18_reducedY44_combinationStep10Coefficient14,
      row18_reducedY44_combinationStep10Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
