/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantCore

/-!
# Ambient row 18 commutant reduction 00

This generated module checks the reduced relation `reducedY00` for
matrix coordinate (0, 0).  Its import of the preceding reduction serializes
clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private def row18_reducedY00_combinationStep00Multiplier : ℂ :=
  (-((328 / 15) : ℂ) + ((74 / 5) : ℂ) * ζ ^ 1 + ((7048 / 237) : ℂ) * ζ ^ 2 - ((22858 / 1185) : ℂ) * ζ ^ 3 + ((9908 / 395) : ℂ) * ζ ^ 5 + ((168 / 5) : ℂ) * ζ ^ 8 - ((2282 / 395) : ℂ) * ζ ^ 9 + ((376 / 15) : ℂ) * ζ ^ 11 + ((152 / 15) : ℂ) * ζ ^ 12 - ((74 / 5) : ℂ) * ζ ^ 13 + ((10672 / 1185) : ℂ) * ζ ^ 15 - ((74 / 5) : ℂ) * ζ ^ 17 - ((7048 / 237) : ℂ) * ζ ^ 18 - ((40396 / 1185) : ℂ) * ζ ^ 21 - ((7048 / 237) : ℂ) * ζ ^ 22 - ((656 / 15) : ℂ) * ζ ^ 24 - ((4062 / 395) : ℂ) * ζ ^ 25 - ((40396 / 1185) : ℂ) * ζ ^ 27 - ((168 / 5) : ℂ) * ζ ^ 28 + ((74 / 5) : ℂ) * ζ ^ 29 - ((1244 / 79) : ℂ) * ζ ^ 30 - ((376 / 15) : ℂ) * ζ ^ 31)

private def row18_reducedY00_combinationStep00Coefficient00 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep00CoefficientIdentity00 :
    row18_reducedY00_combinationStep00Coefficient00 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep00Coefficient00 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep00Coefficient01 : ℂ :=
  (-((7849 / 37446) : ℂ) - ((18809 / 37446) : ℂ) * ζ ^ 1 + ((24443 / 6241) : ℂ) * ζ ^ 2 + ((42500 / 18723) : ℂ) * ζ ^ 3 - ((18809 / 37446) : ℂ) * ζ ^ 5 + ((138809 / 37446) : ℂ) * ζ ^ 6 - ((138809 / 37446) : ℂ) * ζ ^ 8 + ((18809 / 37446) : ℂ) * ζ ^ 9 - ((21250 / 18723) : ℂ) * ζ ^ 11 - ((2508 / 6241) : ℂ) * ζ ^ 12 + ((18809 / 37446) : ℂ) * ζ ^ 13 + ((26120 / 18723) : ℂ) * ζ ^ 15 + ((18809 / 37446) : ℂ) * ζ ^ 17 - ((31688 / 18723) : ℂ) * ζ ^ 18 - ((104149 / 37446) : ℂ) * ζ ^ 21 - ((24443 / 6241) : ℂ) * ζ ^ 22 + ((75433 / 37446) : ℂ) * ζ ^ 24 + ((68620 / 18723) : ℂ) * ζ ^ 27 + ((138809 / 37446) : ℂ) * ζ ^ 28 - ((18809 / 37446) : ℂ) * ζ ^ 29 + ((123761 / 37446) : ℂ) * ζ ^ 30 + ((21250 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep00CoefficientIdentity01 :
    row18_reducedY00_combinationStep00Coefficient01 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          (((21 / 79) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 + ((11 / 79) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 5 - ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 - ((75 / 316) : ℂ) * ζ ^ 9 + ((17 / 79) : ℂ) * ζ ^ 11 - ((67 / 316) : ℂ) * ζ ^ 12 - ((9 / 316) : ℂ) * ζ ^ 13 + ((19 / 79) : ℂ) * ζ ^ 15 - ((9 / 316) : ℂ) * ζ ^ 17 - ((19 / 316) : ℂ) * ζ ^ 18 + ((33 / 316) : ℂ) * ζ ^ 21 - ((11 / 79) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((21 / 79) : ℂ) * ζ ^ 25 - ((19 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 + ((9 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 - ((17 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep00Coefficient01 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 (-((1049059 / 187230) : ℂ) + ((714037 / 187230) : ℂ) * ζ ^ 1 + ((255647 / 187230) : ℂ) * ζ ^ 2 - ((84062 / 18723) : ℂ) * ζ ^ 3 + ((286913 / 31205) : ℂ) * ζ ^ 4 + ((109724 / 18723) : ℂ) * ζ ^ 5 - ((955369 / 187230) : ℂ) * ζ ^ 6 - ((88856 / 93615) : ℂ) * ζ ^ 7 + ((657727 / 93615) : ℂ) * ζ ^ 8 - ((44309 / 37446) : ℂ) * ζ ^ 9 - ((225537 / 62410) : ℂ) * ζ ^ 10 - ((28422 / 6241) : ℂ) * ζ ^ 11 + ((67025 / 18723) : ℂ) * ζ ^ 12 - ((273937 / 93615) : ℂ) * ζ ^ 13 - ((514673 / 37446) : ℂ) * ζ ^ 14 - ((85469 / 37446) : ℂ) * ζ ^ 15 - ((169 / 395) : ℂ) * ζ ^ 16 - ((88648 / 93615) : ℂ) * ζ ^ 17 + ((156881 / 62410) : ℂ) * ζ ^ 18 - ((35017 / 18723) : ℂ) * ζ ^ 19 - ((188428 / 31205) : ℂ) * ζ ^ 20 + ((39311 / 62410) : ℂ) * ζ ^ 21 + ((51038 / 31205) : ℂ) * ζ ^ 22 - ((134926 / 93615) : ℂ) * ζ ^ 23 - ((49864 / 6241) : ℂ) * ζ ^ 24 + ((16981 / 31205) : ℂ) * ζ ^ 25 + ((132097 / 37446) : ℂ) * ζ ^ 26 + ((912457 / 187230) : ℂ) * ζ ^ 27 - ((32729 / 6241) : ℂ) * ζ ^ 28 + ((38906 / 31205) : ℂ) * ζ ^ 29 + ((6392 / 1185) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep00Coefficient02 : ℂ :=
  (-((28871 / 37446) : ℂ) - ((23941 / 12482) : ℂ) * ζ ^ 1 + ((20496 / 6241) : ℂ) * ζ ^ 2 + ((39379 / 37446) : ℂ) * ζ ^ 3 - ((108839 / 18723) : ℂ) * ζ ^ 5 + ((98803 / 37446) : ℂ) * ζ ^ 6 + ((51593 / 37446) : ℂ) * ζ ^ 8 - ((18508 / 18723) : ℂ) * ζ ^ 9 - ((250945 / 37446) : ℂ) * ζ ^ 11 + ((24173 / 37446) : ℂ) * ζ ^ 12 + ((23941 / 12482) : ℂ) * ζ ^ 13 - ((39379 / 37446) : ℂ) * ζ ^ 15 + ((23941 / 12482) : ℂ) * ζ ^ 17 - ((94105 / 37446) : ℂ) * ζ ^ 18 + ((145855 / 37446) : ℂ) * ζ ^ 21 - ((20496 / 6241) : ℂ) * ζ ^ 22 - ((20496 / 6241) : ℂ) * ζ ^ 24 + ((145855 / 37446) : ℂ) * ζ ^ 25 + ((250945 / 37446) : ℂ) * ζ ^ 27 - ((51593 / 37446) : ℂ) * ζ ^ 28 - ((23941 / 12482) : ℂ) * ζ ^ 29 + ((71383 / 37446) : ℂ) * ζ ^ 30 + ((250945 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep00CoefficientIdentity02 :
    row18_reducedY00_combinationStep00Coefficient02 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep00Coefficient02 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 (-((918037 / 187230) : ℂ) + ((181949 / 37446) : ℂ) * ζ ^ 1 + ((503453 / 187230) : ℂ) * ζ ^ 2 - ((98641 / 62410) : ℂ) * ζ ^ 3 + ((193014 / 31205) : ℂ) * ζ ^ 4 + ((585863 / 187230) : ℂ) * ζ ^ 5 - ((336241 / 93615) : ℂ) * ζ ^ 6 + ((29923 / 6241) : ℂ) * ζ ^ 7 + ((56257 / 12482) : ℂ) * ζ ^ 8 - ((124549 / 187230) : ℂ) * ζ ^ 9 - ((418871 / 187230) : ℂ) * ζ ^ 10 + ((171578 / 93615) : ℂ) * ζ ^ 11 + ((26678 / 31205) : ℂ) * ζ ^ 12 - ((13640 / 18723) : ℂ) * ζ ^ 13 - ((305159 / 62410) : ℂ) * ζ ^ 14 - ((23296 / 31205) : ℂ) * ζ ^ 15 - ((115589 / 31205) : ℂ) * ζ ^ 16 - ((481018 / 93615) : ℂ) * ζ ^ 17 - ((268459 / 62410) : ℂ) * ζ ^ 18 - ((148811 / 93615) : ℂ) * ζ ^ 19 + ((5194 / 18723) : ℂ) * ζ ^ 20 - ((20233 / 93615) : ℂ) * ζ ^ 21 + ((58143 / 62410) : ℂ) * ζ ^ 22 - ((63836 / 18723) : ℂ) * ζ ^ 23 - ((1374407 / 187230) : ℂ) * ζ ^ 24 + ((46849 / 62410) : ℂ) * ζ ^ 25 - ((20069 / 62410) : ℂ) * ζ ^ 26 - ((193081 / 37446) : ℂ) * ζ ^ 27 - ((72701 / 187230) : ℂ) * ζ ^ 28 + ((90159 / 31205) : ℂ) * ζ ^ 29 + ((94 / 79) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep00Coefficient03 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep00CoefficientIdentity03 :
    row18_reducedY00_combinationStep00Coefficient03 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep00Coefficient03 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep00Coefficient04 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep00CoefficientIdentity04 :
    row18_reducedY00_combinationStep00Coefficient04 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep00Coefficient04 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep00Coefficient05 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep00CoefficientIdentity05 :
    row18_reducedY00_combinationStep00Coefficient05 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep00Coefficient05 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep00Coefficient06 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep00CoefficientIdentity06 :
    row18_reducedY00_combinationStep00Coefficient06 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep00Coefficient06 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep00Coefficient07 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep00CoefficientIdentity07 :
    row18_reducedY00_combinationStep00Coefficient07 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep00Coefficient07 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep00Coefficient08 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep00CoefficientIdentity08 :
    row18_reducedY00_combinationStep00Coefficient08 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep00Coefficient08 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep00Coefficient09 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep00CoefficientIdentity09 :
    row18_reducedY00_combinationStep00Coefficient09 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep00Coefficient09 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep00Coefficient10 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep00CoefficientIdentity10 :
    row18_reducedY00_combinationStep00Coefficient10 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep00Coefficient10 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep00Coefficient11 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep00CoefficientIdentity11 :
    row18_reducedY00_combinationStep00Coefficient11 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep00Coefficient11 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep00Coefficient12 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep00CoefficientIdentity12 :
    row18_reducedY00_combinationStep00Coefficient12 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep00Coefficient12 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep00Coefficient13 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep00CoefficientIdentity13 :
    row18_reducedY00_combinationStep00Coefficient13 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep00Coefficient13 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep00Coefficient14 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep00CoefficientIdentity14 :
    row18_reducedY00_combinationStep00Coefficient14 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep00Coefficient14 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep00Coefficient15 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep00CoefficientIdentity15 :
    row18_reducedY00_combinationStep00Coefficient15 =
      (0 : ℂ) +
        row18_reducedY00_combinationStep00Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep00Coefficient15 row18_reducedY00_combinationStep00Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY00_combinationStep00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY00_combinationStep00Coefficient00) * Y 0 0
      + (row18_reducedY00_combinationStep00Coefficient01) * Y 0 1
      + (row18_reducedY00_combinationStep00Coefficient02) * Y 1 0
      + (row18_reducedY00_combinationStep00Coefficient03) * Y 1 1
      + (row18_reducedY00_combinationStep00Coefficient04) * Y 2 2
      + (row18_reducedY00_combinationStep00Coefficient05) * Y 2 3
      + (row18_reducedY00_combinationStep00Coefficient06) * Y 3 2
      + (row18_reducedY00_combinationStep00Coefficient07) * Y 3 3
      + (row18_reducedY00_combinationStep00Coefficient08) * Y 4 4
      + (row18_reducedY00_combinationStep00Coefficient09) * Y 4 5
      + (row18_reducedY00_combinationStep00Coefficient10) * Y 5 4
      + (row18_reducedY00_combinationStep00Coefficient11) * Y 5 5
      + (row18_reducedY00_combinationStep00Coefficient12) * Y 6 6
      + (row18_reducedY00_combinationStep00Coefficient13) * Y 6 7
      + (row18_reducedY00_combinationStep00Coefficient14) * Y 7 6
      + (row18_reducedY00_combinationStep00Coefficient15) * Y 7 7) = 0 := by
  have equation :=
    row18_commutatorEquation00
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY00_combinationStep00CoefficientIdentity00,
      row18_reducedY00_combinationStep00CoefficientIdentity01,
      row18_reducedY00_combinationStep00CoefficientIdentity02,
      row18_reducedY00_combinationStep00CoefficientIdentity03,
      row18_reducedY00_combinationStep00CoefficientIdentity04,
      row18_reducedY00_combinationStep00CoefficientIdentity05,
      row18_reducedY00_combinationStep00CoefficientIdentity06,
      row18_reducedY00_combinationStep00CoefficientIdentity07,
      row18_reducedY00_combinationStep00CoefficientIdentity08,
      row18_reducedY00_combinationStep00CoefficientIdentity09,
      row18_reducedY00_combinationStep00CoefficientIdentity10,
      row18_reducedY00_combinationStep00CoefficientIdentity11,
      row18_reducedY00_combinationStep00CoefficientIdentity12,
      row18_reducedY00_combinationStep00CoefficientIdentity13,
      row18_reducedY00_combinationStep00CoefficientIdentity14,
      row18_reducedY00_combinationStep00CoefficientIdentity15]
  linear_combination
    row18_reducedY00_combinationStep00Multiplier * equation

private def row18_reducedY00_combinationStep01Multiplier : ℂ :=
  (-((454 / 395) : ℂ) + ((878 / 1185) : ℂ) * ζ ^ 1 + ((518 / 395) : ℂ) * ζ ^ 2 + ((794 / 1185) : ℂ) * ζ ^ 5 + ((972 / 395) : ℂ) * ζ ^ 6 + ((972 / 395) : ℂ) * ζ ^ 8 + ((794 / 1185) : ℂ) * ζ ^ 9 + ((1258 / 237) : ℂ) * ζ ^ 11 + ((5408 / 1185) : ℂ) * ζ ^ 12 - ((878 / 1185) : ℂ) * ζ ^ 13 + ((100 / 79) : ℂ) * ζ ^ 15 - ((878 / 1185) : ℂ) * ζ ^ 17 - ((2942 / 1185) : ℂ) * ζ ^ 18 - ((836 / 1185) : ℂ) * ζ ^ 21 - ((518 / 395) : ℂ) * ζ ^ 22 + ((26 / 1185) : ℂ) * ζ ^ 24 + ((28 / 395) : ℂ) * ζ ^ 25 - ((100 / 79) : ℂ) * ζ ^ 27 - ((972 / 395) : ℂ) * ζ ^ 28 + ((878 / 1185) : ℂ) * ζ ^ 29 - ((2492 / 1185) : ℂ) * ζ ^ 30 - ((1258 / 237) : ℂ) * ζ ^ 31)

private def row18_reducedY00_combinationStep01Coefficient00 : ℂ :=
  (((24631 / 12482) : ℂ) - ((9190 / 18723) : ℂ) * ζ ^ 1 - ((10277 / 18723) : ℂ) * ζ ^ 2 - ((20528 / 18723) : ℂ) * ζ ^ 3 - ((6197 / 18723) : ℂ) * ζ ^ 5 - ((20630 / 18723) : ℂ) * ζ ^ 6 - ((13775 / 37446) : ℂ) * ζ ^ 8 - ((14137 / 37446) : ℂ) * ζ ^ 9 + ((8973 / 12482) : ℂ) * ζ ^ 11 - ((13775 / 37446) : ℂ) * ζ ^ 12 + ((9190 / 18723) : ℂ) * ζ ^ 13 + ((23521 / 18723) : ℂ) * ζ ^ 15 + ((9190 / 18723) : ℂ) * ζ ^ 17 + ((3451 / 6241) : ℂ) * ζ ^ 18 + ((9906 / 6241) : ℂ) * ζ ^ 21 + ((10277 / 18723) : ℂ) * ζ ^ 22 - ((2993 / 18723) : ℂ) * ζ ^ 25 - ((9906 / 6241) : ℂ) * ζ ^ 27 + ((13775 / 37446) : ℂ) * ζ ^ 28 - ((9190 / 18723) : ℂ) * ζ ^ 29 - ((10315 / 18723) : ℂ) * ζ ^ 30 - ((8973 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep01CoefficientIdentity00 :
    row18_reducedY00_combinationStep01Coefficient00 =
      row18_reducedY00_combinationStep00Coefficient00 +
        row18_reducedY00_combinationStep01Multiplier *
          (-((41 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((17 / 158) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((11 / 316) : ℂ) * ζ ^ 6 + ((61 / 316) : ℂ) * ζ ^ 8 + ((37 / 158) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((17 / 158) : ℂ) * ζ ^ 22 - ((17 / 158) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((61 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((27 / 316) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep01Coefficient00 row18_reducedY00_combinationStep00Coefficient00 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 (-((104541 / 62410) : ℂ) + ((4317 / 12482) : ℂ) * ζ ^ 1 + ((56503 / 187230) : ℂ) * ζ ^ 2 + ((163909 / 187230) : ℂ) * ζ ^ 3 + ((99247 / 62410) : ℂ) * ζ ^ 4 - ((16691 / 187230) : ℂ) * ζ ^ 5 + ((10857 / 62410) : ℂ) * ζ ^ 6 - ((20119 / 18723) : ℂ) * ζ ^ 7 - ((219277 / 93615) : ℂ) * ζ ^ 8 + ((9449 / 37446) : ℂ) * ζ ^ 9 - ((7421 / 187230) : ℂ) * ζ ^ 10 - ((7097 / 12482) : ℂ) * ζ ^ 11 - ((247 / 474) : ℂ) * ζ ^ 12 - ((27778 / 31205) : ℂ) * ζ ^ 13 + ((59677 / 62410) : ℂ) * ζ ^ 14 + ((75379 / 93615) : ℂ) * ζ ^ 15 + ((77458 / 93615) : ℂ) * ζ ^ 16 + ((22790 / 18723) : ℂ) * ζ ^ 17 + ((13783 / 93615) : ℂ) * ζ ^ 18 + ((9599 / 62410) : ℂ) * ζ ^ 19 - ((57463 / 62410) : ℂ) * ζ ^ 20 - ((105754 / 93615) : ℂ) * ζ ^ 21 - ((22107 / 62410) : ℂ) * ζ ^ 22 - ((1983 / 62410) : ℂ) * ζ ^ 23 + ((3993 / 6241) : ℂ) * ζ ^ 24 + ((9422 / 18723) : ℂ) * ζ ^ 25 + ((38011 / 62410) : ℂ) * ζ ^ 26 + ((99013 / 93615) : ℂ) * ζ ^ 27 + ((6914 / 93615) : ℂ) * ζ ^ 28 - ((6907 / 12482) : ℂ) * ζ ^ 29 - ((3145 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep01Coefficient01 : ℂ :=
  (((8989 / 12482) : ℂ) - ((106169 / 37446) : ℂ) * ζ ^ 1 - ((1217 / 6241) : ℂ) * ζ ^ 2 + ((9191 / 6241) : ℂ) * ζ ^ 3 - ((106169 / 37446) : ℂ) * ζ ^ 5 + ((6555 / 12482) : ℂ) * ζ ^ 6 - ((6555 / 12482) : ℂ) * ζ ^ 8 + ((106169 / 37446) : ℂ) * ζ ^ 9 - ((9191 / 12482) : ℂ) * ζ ^ 11 + ((33910 / 18723) : ℂ) * ζ ^ 12 + ((106169 / 37446) : ℂ) * ζ ^ 13 + ((20203 / 37446) : ℂ) * ζ ^ 15 + ((106169 / 37446) : ℂ) * ζ ^ 17 + ((57451 / 37446) : ℂ) * ζ ^ 18 + ((45083 / 18723) : ℂ) * ζ ^ 21 + ((1217 / 6241) : ℂ) * ζ ^ 22 + ((38558 / 18723) : ℂ) * ζ ^ 24 + ((75349 / 37446) : ℂ) * ζ ^ 27 + ((6555 / 12482) : ℂ) * ζ ^ 28 - ((106169 / 37446) : ℂ) * ζ ^ 29 + ((87485 / 37446) : ℂ) * ζ ^ 30 + ((9191 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep01CoefficientIdentity01 :
    row18_reducedY00_combinationStep01Coefficient01 =
      row18_reducedY00_combinationStep00Coefficient01 +
        row18_reducedY00_combinationStep01Multiplier *
          (-((8 / 79) : ℂ) - ((11 / 158) : ℂ) * ζ ^ 1 - ((167 / 316) : ℂ) * ζ ^ 2 - ((75 / 316) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 + ((103 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((11 / 158) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 15 + ((11 / 158) : ℂ) * ζ ^ 17 + ((167 / 316) : ℂ) * ζ ^ 18 - ((53 / 316) : ℂ) * ζ ^ 21 + ((167 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 - ((15 / 79) : ℂ) * ζ ^ 25 - ((53 / 316) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((11 / 158) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep01Coefficient01 row18_reducedY00_combinationStep00Coefficient01 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 (-((76144 / 93615) : ℂ) + ((218867 / 93615) : ℂ) * ζ ^ 1 + ((169801 / 37446) : ℂ) * ζ ^ 2 + ((18323 / 31205) : ℂ) * ζ ^ 3 - ((5198 / 93615) : ℂ) * ζ ^ 4 - ((32597 / 62410) : ℂ) * ζ ^ 5 - ((97331 / 62410) : ℂ) * ζ ^ 6 - ((178787 / 187230) : ℂ) * ζ ^ 7 - ((304471 / 62410) : ℂ) * ζ ^ 8 - ((279007 / 93615) : ℂ) * ζ ^ 9 + ((10940 / 18723) : ℂ) * ζ ^ 10 - ((2939 / 31205) : ℂ) * ζ ^ 11 + ((56794 / 93615) : ℂ) * ζ ^ 12 + ((11517 / 62410) : ℂ) * ζ ^ 13 + ((12357 / 12482) : ℂ) * ζ ^ 14 + ((291323 / 187230) : ℂ) * ζ ^ 15 - ((63686 / 93615) : ℂ) * ζ ^ 16 - ((2809 / 62410) : ℂ) * ζ ^ 17 - ((113654 / 93615) : ℂ) * ζ ^ 18 - ((67549 / 93615) : ℂ) * ζ ^ 19 - ((179 / 395) : ℂ) * ζ ^ 20 - ((673591 / 187230) : ℂ) * ζ ^ 21 - ((22301 / 37446) : ℂ) * ζ ^ 22 + ((164411 / 93615) : ℂ) * ζ ^ 23 + ((149027 / 187230) : ℂ) * ζ ^ 24 + ((30869 / 31205) : ℂ) * ζ ^ 25 + ((204047 / 187230) : ℂ) * ζ ^ 26 + ((17432 / 93615) : ℂ) * ζ ^ 27 + ((25789 / 93615) : ℂ) * ζ ^ 28 - ((55184 / 93615) : ℂ) * ζ ^ 29 - ((8806 / 18723) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep01Coefficient02 : ℂ :=
  (-((28871 / 37446) : ℂ) - ((23941 / 12482) : ℂ) * ζ ^ 1 + ((20496 / 6241) : ℂ) * ζ ^ 2 + ((39379 / 37446) : ℂ) * ζ ^ 3 - ((108839 / 18723) : ℂ) * ζ ^ 5 + ((98803 / 37446) : ℂ) * ζ ^ 6 + ((51593 / 37446) : ℂ) * ζ ^ 8 - ((18508 / 18723) : ℂ) * ζ ^ 9 - ((250945 / 37446) : ℂ) * ζ ^ 11 + ((24173 / 37446) : ℂ) * ζ ^ 12 + ((23941 / 12482) : ℂ) * ζ ^ 13 - ((39379 / 37446) : ℂ) * ζ ^ 15 + ((23941 / 12482) : ℂ) * ζ ^ 17 - ((94105 / 37446) : ℂ) * ζ ^ 18 + ((145855 / 37446) : ℂ) * ζ ^ 21 - ((20496 / 6241) : ℂ) * ζ ^ 22 - ((20496 / 6241) : ℂ) * ζ ^ 24 + ((145855 / 37446) : ℂ) * ζ ^ 25 + ((250945 / 37446) : ℂ) * ζ ^ 27 - ((51593 / 37446) : ℂ) * ζ ^ 28 - ((23941 / 12482) : ℂ) * ζ ^ 29 + ((71383 / 37446) : ℂ) * ζ ^ 30 + ((250945 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep01CoefficientIdentity02 :
    row18_reducedY00_combinationStep01Coefficient02 =
      row18_reducedY00_combinationStep00Coefficient02 +
        row18_reducedY00_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep01Coefficient02 row18_reducedY00_combinationStep00Coefficient02 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep01Coefficient03 : ℂ :=
  (-((24631 / 12482) : ℂ) + ((9190 / 18723) : ℂ) * ζ ^ 1 + ((10277 / 18723) : ℂ) * ζ ^ 2 + ((20528 / 18723) : ℂ) * ζ ^ 3 + ((6197 / 18723) : ℂ) * ζ ^ 5 + ((20630 / 18723) : ℂ) * ζ ^ 6 + ((13775 / 37446) : ℂ) * ζ ^ 8 + ((14137 / 37446) : ℂ) * ζ ^ 9 - ((8973 / 12482) : ℂ) * ζ ^ 11 + ((13775 / 37446) : ℂ) * ζ ^ 12 - ((9190 / 18723) : ℂ) * ζ ^ 13 - ((23521 / 18723) : ℂ) * ζ ^ 15 - ((9190 / 18723) : ℂ) * ζ ^ 17 - ((3451 / 6241) : ℂ) * ζ ^ 18 - ((9906 / 6241) : ℂ) * ζ ^ 21 - ((10277 / 18723) : ℂ) * ζ ^ 22 + ((2993 / 18723) : ℂ) * ζ ^ 25 + ((9906 / 6241) : ℂ) * ζ ^ 27 - ((13775 / 37446) : ℂ) * ζ ^ 28 + ((9190 / 18723) : ℂ) * ζ ^ 29 + ((10315 / 18723) : ℂ) * ζ ^ 30 + ((8973 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep01CoefficientIdentity03 :
    row18_reducedY00_combinationStep01Coefficient03 =
      row18_reducedY00_combinationStep00Coefficient03 +
        row18_reducedY00_combinationStep01Multiplier *
          (((41 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((17 / 158) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((11 / 316) : ℂ) * ζ ^ 6 - ((61 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((17 / 158) : ℂ) * ζ ^ 22 + ((17 / 158) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((61 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((27 / 316) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep01Coefficient03 row18_reducedY00_combinationStep00Coefficient03 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 (((104541 / 62410) : ℂ) - ((4317 / 12482) : ℂ) * ζ ^ 1 - ((56503 / 187230) : ℂ) * ζ ^ 2 - ((163909 / 187230) : ℂ) * ζ ^ 3 - ((99247 / 62410) : ℂ) * ζ ^ 4 + ((16691 / 187230) : ℂ) * ζ ^ 5 - ((10857 / 62410) : ℂ) * ζ ^ 6 + ((20119 / 18723) : ℂ) * ζ ^ 7 + ((219277 / 93615) : ℂ) * ζ ^ 8 - ((9449 / 37446) : ℂ) * ζ ^ 9 + ((7421 / 187230) : ℂ) * ζ ^ 10 + ((7097 / 12482) : ℂ) * ζ ^ 11 + ((247 / 474) : ℂ) * ζ ^ 12 + ((27778 / 31205) : ℂ) * ζ ^ 13 - ((59677 / 62410) : ℂ) * ζ ^ 14 - ((75379 / 93615) : ℂ) * ζ ^ 15 - ((77458 / 93615) : ℂ) * ζ ^ 16 - ((22790 / 18723) : ℂ) * ζ ^ 17 - ((13783 / 93615) : ℂ) * ζ ^ 18 - ((9599 / 62410) : ℂ) * ζ ^ 19 + ((57463 / 62410) : ℂ) * ζ ^ 20 + ((105754 / 93615) : ℂ) * ζ ^ 21 + ((22107 / 62410) : ℂ) * ζ ^ 22 + ((1983 / 62410) : ℂ) * ζ ^ 23 - ((3993 / 6241) : ℂ) * ζ ^ 24 - ((9422 / 18723) : ℂ) * ζ ^ 25 - ((38011 / 62410) : ℂ) * ζ ^ 26 - ((99013 / 93615) : ℂ) * ζ ^ 27 - ((6914 / 93615) : ℂ) * ζ ^ 28 + ((6907 / 12482) : ℂ) * ζ ^ 29 + ((3145 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep01Coefficient04 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep01CoefficientIdentity04 :
    row18_reducedY00_combinationStep01Coefficient04 =
      row18_reducedY00_combinationStep00Coefficient04 +
        row18_reducedY00_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep01Coefficient04 row18_reducedY00_combinationStep00Coefficient04 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep01Coefficient05 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep01CoefficientIdentity05 :
    row18_reducedY00_combinationStep01Coefficient05 =
      row18_reducedY00_combinationStep00Coefficient05 +
        row18_reducedY00_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep01Coefficient05 row18_reducedY00_combinationStep00Coefficient05 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep01Coefficient06 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep01CoefficientIdentity06 :
    row18_reducedY00_combinationStep01Coefficient06 =
      row18_reducedY00_combinationStep00Coefficient06 +
        row18_reducedY00_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep01Coefficient06 row18_reducedY00_combinationStep00Coefficient06 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep01Coefficient07 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep01CoefficientIdentity07 :
    row18_reducedY00_combinationStep01Coefficient07 =
      row18_reducedY00_combinationStep00Coefficient07 +
        row18_reducedY00_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep01Coefficient07 row18_reducedY00_combinationStep00Coefficient07 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep01Coefficient08 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep01CoefficientIdentity08 :
    row18_reducedY00_combinationStep01Coefficient08 =
      row18_reducedY00_combinationStep00Coefficient08 +
        row18_reducedY00_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep01Coefficient08 row18_reducedY00_combinationStep00Coefficient08 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep01Coefficient09 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep01CoefficientIdentity09 :
    row18_reducedY00_combinationStep01Coefficient09 =
      row18_reducedY00_combinationStep00Coefficient09 +
        row18_reducedY00_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep01Coefficient09 row18_reducedY00_combinationStep00Coefficient09 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep01Coefficient10 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep01CoefficientIdentity10 :
    row18_reducedY00_combinationStep01Coefficient10 =
      row18_reducedY00_combinationStep00Coefficient10 +
        row18_reducedY00_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep01Coefficient10 row18_reducedY00_combinationStep00Coefficient10 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep01Coefficient11 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep01CoefficientIdentity11 :
    row18_reducedY00_combinationStep01Coefficient11 =
      row18_reducedY00_combinationStep00Coefficient11 +
        row18_reducedY00_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep01Coefficient11 row18_reducedY00_combinationStep00Coefficient11 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep01Coefficient12 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep01CoefficientIdentity12 :
    row18_reducedY00_combinationStep01Coefficient12 =
      row18_reducedY00_combinationStep00Coefficient12 +
        row18_reducedY00_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep01Coefficient12 row18_reducedY00_combinationStep00Coefficient12 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep01Coefficient13 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep01CoefficientIdentity13 :
    row18_reducedY00_combinationStep01Coefficient13 =
      row18_reducedY00_combinationStep00Coefficient13 +
        row18_reducedY00_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep01Coefficient13 row18_reducedY00_combinationStep00Coefficient13 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep01Coefficient14 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep01CoefficientIdentity14 :
    row18_reducedY00_combinationStep01Coefficient14 =
      row18_reducedY00_combinationStep00Coefficient14 +
        row18_reducedY00_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep01Coefficient14 row18_reducedY00_combinationStep00Coefficient14 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep01Coefficient15 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep01CoefficientIdentity15 :
    row18_reducedY00_combinationStep01Coefficient15 =
      row18_reducedY00_combinationStep00Coefficient15 +
        row18_reducedY00_combinationStep01Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep01Coefficient15 row18_reducedY00_combinationStep00Coefficient15 row18_reducedY00_combinationStep01Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY00_combinationStep01
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY00_combinationStep01Coefficient00) * Y 0 0
      + (row18_reducedY00_combinationStep01Coefficient01) * Y 0 1
      + (row18_reducedY00_combinationStep01Coefficient02) * Y 1 0
      + (row18_reducedY00_combinationStep01Coefficient03) * Y 1 1
      + (row18_reducedY00_combinationStep01Coefficient04) * Y 2 2
      + (row18_reducedY00_combinationStep01Coefficient05) * Y 2 3
      + (row18_reducedY00_combinationStep01Coefficient06) * Y 3 2
      + (row18_reducedY00_combinationStep01Coefficient07) * Y 3 3
      + (row18_reducedY00_combinationStep01Coefficient08) * Y 4 4
      + (row18_reducedY00_combinationStep01Coefficient09) * Y 4 5
      + (row18_reducedY00_combinationStep01Coefficient10) * Y 5 4
      + (row18_reducedY00_combinationStep01Coefficient11) * Y 5 5
      + (row18_reducedY00_combinationStep01Coefficient12) * Y 6 6
      + (row18_reducedY00_combinationStep01Coefficient13) * Y 6 7
      + (row18_reducedY00_combinationStep01Coefficient14) * Y 7 6
      + (row18_reducedY00_combinationStep01Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY00_combinationStep00 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation01
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY00_combinationStep01CoefficientIdentity00,
      row18_reducedY00_combinationStep01CoefficientIdentity01,
      row18_reducedY00_combinationStep01CoefficientIdentity02,
      row18_reducedY00_combinationStep01CoefficientIdentity03,
      row18_reducedY00_combinationStep01CoefficientIdentity04,
      row18_reducedY00_combinationStep01CoefficientIdentity05,
      row18_reducedY00_combinationStep01CoefficientIdentity06,
      row18_reducedY00_combinationStep01CoefficientIdentity07,
      row18_reducedY00_combinationStep01CoefficientIdentity08,
      row18_reducedY00_combinationStep01CoefficientIdentity09,
      row18_reducedY00_combinationStep01CoefficientIdentity10,
      row18_reducedY00_combinationStep01CoefficientIdentity11,
      row18_reducedY00_combinationStep01CoefficientIdentity12,
      row18_reducedY00_combinationStep01CoefficientIdentity13,
      row18_reducedY00_combinationStep01CoefficientIdentity14,
      row18_reducedY00_combinationStep01CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY00_combinationStep01Multiplier * equation

private def row18_reducedY00_combinationStep02Multiplier : ℂ :=
  (-((28838 / 18723) : ℂ) - ((4930 / 6241) : ℂ) * ζ ^ 1 - ((122566 / 31205) : ℂ) * ζ ^ 2 + ((19454 / 18723) : ℂ) * ζ ^ 3 - ((58334 / 18723) : ℂ) * ζ ^ 5 - ((728972 / 93615) : ℂ) * ζ ^ 6 - ((76720 / 18723) : ℂ) * ζ ^ 8 - ((25630 / 6241) : ℂ) * ζ ^ 9 - ((96344 / 18723) : ℂ) * ζ ^ 11 - ((76720 / 18723) : ℂ) * ζ ^ 12 + ((4930 / 6241) : ℂ) * ζ ^ 13 - ((62998 / 18723) : ℂ) * ζ ^ 15 + ((4930 / 6241) : ℂ) * ζ ^ 17 + ((361274 / 93615) : ℂ) * ζ ^ 18 - ((4664 / 18723) : ℂ) * ζ ^ 21 + ((122566 / 31205) : ℂ) * ζ ^ 22 + ((43544 / 18723) : ℂ) * ζ ^ 25 + ((4664 / 18723) : ℂ) * ζ ^ 27 + ((76720 / 18723) : ℂ) * ζ ^ 28 - ((4930 / 6241) : ℂ) * ζ ^ 29 - ((364486 / 93615) : ℂ) * ζ ^ 30 + ((96344 / 18723) : ℂ) * ζ ^ 31)

private def row18_reducedY00_combinationStep02Coefficient00 : ℂ :=
  (((51551 / 37446) : ℂ) - ((61814 / 93615) : ℂ) * ζ ^ 1 + ((101876 / 93615) : ℂ) * ζ ^ 2 - ((9833 / 31205) : ℂ) * ζ ^ 3 + ((64768 / 93615) : ℂ) * ζ ^ 5 + ((174119 / 93615) : ℂ) * ζ ^ 6 + ((30428 / 18723) : ℂ) * ζ ^ 8 + ((69606 / 31205) : ℂ) * ζ ^ 9 + ((79439 / 31205) : ℂ) * ζ ^ 11 + ((30428 / 18723) : ℂ) * ζ ^ 12 + ((61814 / 93615) : ℂ) * ζ ^ 13 + ((52027 / 31205) : ℂ) * ζ ^ 15 + ((61814 / 93615) : ℂ) * ζ ^ 17 - ((24081 / 31205) : ℂ) * ζ ^ 18 + ((91313 / 93615) : ℂ) * ζ ^ 21 - ((101876 / 93615) : ℂ) * ζ ^ 22 - ((42194 / 31205) : ℂ) * ζ ^ 25 - ((91313 / 93615) : ℂ) * ζ ^ 27 - ((30428 / 18723) : ℂ) * ζ ^ 28 - ((61814 / 93615) : ℂ) * ζ ^ 29 + ((174119 / 187230) : ℂ) * ζ ^ 30 - ((79439 / 31205) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep02CoefficientIdentity00 :
    row18_reducedY00_combinationStep02Coefficient00 =
      row18_reducedY00_combinationStep01Coefficient00 +
        row18_reducedY00_combinationStep02Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep02Coefficient00 row18_reducedY00_combinationStep01Coefficient00 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 (((969023 / 1479117) : ℂ) + ((2157167 / 14791170) : ℂ) * ζ ^ 1 - ((1628770 / 1479117) : ℂ) * ζ ^ 2 - ((1860592 / 2465195) : ℂ) * ζ ^ 3 + ((639797 / 1479117) : ℂ) * ζ ^ 4 - ((6222663 / 4930390) : ℂ) * ζ ^ 5 - ((2164432 / 1479117) : ℂ) * ζ ^ 6 + ((4037752 / 2465195) : ℂ) * ζ ^ 7 - ((450197 / 14791170) : ℂ) * ζ ^ 8 - ((22426747 / 14791170) : ℂ) * ζ ^ 9 + ((6522539 / 2958234) : ℂ) * ζ ^ 10 - ((15892051 / 14791170) : ℂ) * ζ ^ 11 - ((10996871 / 14791170) : ℂ) * ζ ^ 12 + ((40609783 / 14791170) : ℂ) * ζ ^ 13 - ((2706559 / 986078) : ℂ) * ζ ^ 14 + ((6784696 / 7395585) : ℂ) * ζ ^ 15 + ((25979821 / 14791170) : ℂ) * ζ ^ 16 - ((2205567 / 986078) : ℂ) * ζ ^ 17 + ((648137 / 493039) : ℂ) * ζ ^ 18 - ((19968 / 493039) : ℂ) * ζ ^ 19 - ((2766401 / 2465195) : ℂ) * ζ ^ 20 + ((2956253 / 2465195) : ℂ) * ζ ^ 21 - ((258557 / 1479117) : ℂ) * ζ ^ 22 + ((2034223 / 14791170) : ℂ) * ζ ^ 23 - ((1121091 / 4930390) : ℂ) * ζ ^ 24 + ((3626684 / 7395585) : ℂ) * ζ ^ 25 + ((282536 / 1479117) : ℂ) * ζ ^ 26 - ((2385991 / 4930390) : ℂ) * ζ ^ 27 + ((841283 / 2465195) : ℂ) * ζ ^ 28 - ((13513 / 31205) : ℂ) * ζ ^ 29 + ((337204 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep02Coefficient01 : ℂ :=
  (-((80203 / 18723) : ℂ) + ((48778 / 18723) : ℂ) * ζ ^ 1 + ((5447 / 6241) : ℂ) * ζ ^ 2 - ((17821 / 6241) : ℂ) * ζ ^ 3 + ((48778 / 18723) : ℂ) * ζ ^ 5 - ((63862 / 18723) : ℂ) * ζ ^ 6 + ((63862 / 18723) : ℂ) * ζ ^ 8 - ((48778 / 18723) : ℂ) * ζ ^ 9 + ((17821 / 12482) : ℂ) * ζ ^ 11 + ((4693 / 18723) : ℂ) * ζ ^ 12 - ((48778 / 18723) : ℂ) * ζ ^ 13 - ((10700 / 6241) : ℂ) * ζ ^ 15 - ((48778 / 18723) : ℂ) * ζ ^ 17 - ((10556 / 6241) : ℂ) * ζ ^ 18 - ((205525 / 37446) : ℂ) * ζ ^ 21 - ((5447 / 6241) : ℂ) * ζ ^ 22 - ((95530 / 18723) : ℂ) * ζ ^ 24 - ((28521 / 6241) : ℂ) * ζ ^ 27 - ((63862 / 18723) : ℂ) * ζ ^ 28 + ((48778 / 18723) : ℂ) * ζ ^ 29 - ((19723 / 6241) : ℂ) * ζ ^ 30 - ((17821 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep02CoefficientIdentity01 :
    row18_reducedY00_combinationStep02Coefficient01 =
      row18_reducedY00_combinationStep01Coefficient01 +
        row18_reducedY00_combinationStep02Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep02Coefficient01 row18_reducedY00_combinationStep01Coefficient01 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 (((6903778 / 1479117) : ℂ) - ((5126305 / 986078) : ℂ) * ζ ^ 1 - ((8661747 / 4930390) : ℂ) * ζ ^ 2 + ((16158835 / 2958234) : ℂ) * ζ ^ 3 - ((12631291 / 2465195) : ℂ) * ζ ^ 4 - ((3951233 / 4930390) : ℂ) * ζ ^ 5 + ((35117156 / 7395585) : ℂ) * ζ ^ 6 - ((7676453 / 2958234) : ℂ) * ζ ^ 7 - ((1558798 / 1479117) : ℂ) * ζ ^ 8 + ((43218709 / 7395585) : ℂ) * ζ ^ 9 - ((6405613 / 2958234) : ℂ) * ζ ^ 10 - ((1584040 / 1479117) : ℂ) * ζ ^ 11 + ((14643877 / 2465195) : ℂ) * ζ ^ 12 - ((13782197 / 4930390) : ℂ) * ζ ^ 13 + ((54689 / 62410) : ℂ) * ζ ^ 14 + ((10596205 / 2958234) : ℂ) * ζ ^ 15 - ((38135923 / 14791170) : ℂ) * ζ ^ 16 + ((35829547 / 14791170) : ℂ) * ζ ^ 17 + ((3915994 / 1479117) : ℂ) * ζ ^ 18 - ((9910081 / 2958234) : ℂ) * ζ ^ 19 + ((16291378 / 7395585) : ℂ) * ζ ^ 20 + ((11655329 / 4930390) : ℂ) * ζ ^ 21 - ((4846523 / 2465195) : ℂ) * ζ ^ 22 + ((147345 / 986078) : ℂ) * ζ ^ 23 + ((45883577 / 14791170) : ℂ) * ζ ^ 24 - ((2043509 / 986078) : ℂ) * ζ ^ 25 - ((1767599 / 14791170) : ℂ) * ζ ^ 26 + ((2318299 / 986078) : ℂ) * ζ ^ 27 - ((30794897 / 14791170) : ℂ) * ζ ^ 28 + ((10637281 / 14791170) : ℂ) * ζ ^ 29 + ((313118 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep02Coefficient02 : ℂ :=
  (-((28871 / 37446) : ℂ) - ((23941 / 12482) : ℂ) * ζ ^ 1 + ((20496 / 6241) : ℂ) * ζ ^ 2 + ((39379 / 37446) : ℂ) * ζ ^ 3 - ((108839 / 18723) : ℂ) * ζ ^ 5 + ((98803 / 37446) : ℂ) * ζ ^ 6 + ((51593 / 37446) : ℂ) * ζ ^ 8 - ((18508 / 18723) : ℂ) * ζ ^ 9 - ((250945 / 37446) : ℂ) * ζ ^ 11 + ((24173 / 37446) : ℂ) * ζ ^ 12 + ((23941 / 12482) : ℂ) * ζ ^ 13 - ((39379 / 37446) : ℂ) * ζ ^ 15 + ((23941 / 12482) : ℂ) * ζ ^ 17 - ((94105 / 37446) : ℂ) * ζ ^ 18 + ((145855 / 37446) : ℂ) * ζ ^ 21 - ((20496 / 6241) : ℂ) * ζ ^ 22 - ((20496 / 6241) : ℂ) * ζ ^ 24 + ((145855 / 37446) : ℂ) * ζ ^ 25 + ((250945 / 37446) : ℂ) * ζ ^ 27 - ((51593 / 37446) : ℂ) * ζ ^ 28 - ((23941 / 12482) : ℂ) * ζ ^ 29 + ((71383 / 37446) : ℂ) * ζ ^ 30 + ((250945 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep02CoefficientIdentity02 :
    row18_reducedY00_combinationStep02Coefficient02 =
      row18_reducedY00_combinationStep01Coefficient02 +
        row18_reducedY00_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep02Coefficient02 row18_reducedY00_combinationStep01Coefficient02 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep02Coefficient03 : ℂ :=
  (-((24631 / 12482) : ℂ) + ((9190 / 18723) : ℂ) * ζ ^ 1 + ((10277 / 18723) : ℂ) * ζ ^ 2 + ((20528 / 18723) : ℂ) * ζ ^ 3 + ((6197 / 18723) : ℂ) * ζ ^ 5 + ((20630 / 18723) : ℂ) * ζ ^ 6 + ((13775 / 37446) : ℂ) * ζ ^ 8 + ((14137 / 37446) : ℂ) * ζ ^ 9 - ((8973 / 12482) : ℂ) * ζ ^ 11 + ((13775 / 37446) : ℂ) * ζ ^ 12 - ((9190 / 18723) : ℂ) * ζ ^ 13 - ((23521 / 18723) : ℂ) * ζ ^ 15 - ((9190 / 18723) : ℂ) * ζ ^ 17 - ((3451 / 6241) : ℂ) * ζ ^ 18 - ((9906 / 6241) : ℂ) * ζ ^ 21 - ((10277 / 18723) : ℂ) * ζ ^ 22 + ((2993 / 18723) : ℂ) * ζ ^ 25 + ((9906 / 6241) : ℂ) * ζ ^ 27 - ((13775 / 37446) : ℂ) * ζ ^ 28 + ((9190 / 18723) : ℂ) * ζ ^ 29 + ((10315 / 18723) : ℂ) * ζ ^ 30 + ((8973 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep02CoefficientIdentity03 :
    row18_reducedY00_combinationStep02Coefficient03 =
      row18_reducedY00_combinationStep01Coefficient03 +
        row18_reducedY00_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep02Coefficient03 row18_reducedY00_combinationStep01Coefficient03 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep02Coefficient04 : ℂ :=
  (((11171 / 18723) : ℂ) + ((5288 / 31205) : ℂ) * ζ ^ 1 - ((51087 / 31205) : ℂ) * ζ ^ 2 - ((73141 / 93615) : ℂ) * ζ ^ 3 - ((95753 / 93615) : ℂ) * ζ ^ 5 - ((92423 / 31205) : ℂ) * ζ ^ 6 - ((24877 / 12482) : ℂ) * ζ ^ 8 - ((488321 / 187230) : ℂ) * ζ ^ 9 - ((114013 / 62410) : ℂ) * ζ ^ 11 - ((24877 / 12482) : ℂ) * ζ ^ 12 - ((5288 / 31205) : ℂ) * ζ ^ 13 - ((38476 / 93615) : ℂ) * ζ ^ 15 - ((5288 / 31205) : ℂ) * ζ ^ 17 + ((41336 / 31205) : ℂ) * ζ ^ 18 + ((57277 / 93615) : ℂ) * ζ ^ 21 + ((51087 / 31205) : ℂ) * ζ ^ 22 + ((111617 / 93615) : ℂ) * ζ ^ 25 - ((57277 / 93615) : ℂ) * ζ ^ 27 + ((24877 / 12482) : ℂ) * ζ ^ 28 + ((5288 / 31205) : ℂ) * ζ ^ 29 - ((92423 / 62410) : ℂ) * ζ ^ 30 + ((114013 / 62410) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep02CoefficientIdentity04 :
    row18_reducedY00_combinationStep02Coefficient04 =
      row18_reducedY00_combinationStep01Coefficient04 +
        row18_reducedY00_combinationStep02Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep02Coefficient04 row18_reducedY00_combinationStep01Coefficient04 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 (-((969023 / 1479117) : ℂ) - ((2157167 / 14791170) : ℂ) * ζ ^ 1 + ((1628770 / 1479117) : ℂ) * ζ ^ 2 + ((1860592 / 2465195) : ℂ) * ζ ^ 3 - ((639797 / 1479117) : ℂ) * ζ ^ 4 + ((6222663 / 4930390) : ℂ) * ζ ^ 5 + ((2164432 / 1479117) : ℂ) * ζ ^ 6 - ((4037752 / 2465195) : ℂ) * ζ ^ 7 + ((450197 / 14791170) : ℂ) * ζ ^ 8 + ((22426747 / 14791170) : ℂ) * ζ ^ 9 - ((6522539 / 2958234) : ℂ) * ζ ^ 10 + ((15892051 / 14791170) : ℂ) * ζ ^ 11 + ((10996871 / 14791170) : ℂ) * ζ ^ 12 - ((40609783 / 14791170) : ℂ) * ζ ^ 13 + ((2706559 / 986078) : ℂ) * ζ ^ 14 - ((6784696 / 7395585) : ℂ) * ζ ^ 15 - ((25979821 / 14791170) : ℂ) * ζ ^ 16 + ((2205567 / 986078) : ℂ) * ζ ^ 17 - ((648137 / 493039) : ℂ) * ζ ^ 18 + ((19968 / 493039) : ℂ) * ζ ^ 19 + ((2766401 / 2465195) : ℂ) * ζ ^ 20 - ((2956253 / 2465195) : ℂ) * ζ ^ 21 + ((258557 / 1479117) : ℂ) * ζ ^ 22 - ((2034223 / 14791170) : ℂ) * ζ ^ 23 + ((1121091 / 4930390) : ℂ) * ζ ^ 24 - ((3626684 / 7395585) : ℂ) * ζ ^ 25 - ((282536 / 1479117) : ℂ) * ζ ^ 26 + ((2385991 / 4930390) : ℂ) * ζ ^ 27 - ((841283 / 2465195) : ℂ) * ζ ^ 28 + ((13513 / 31205) : ℂ) * ζ ^ 29 - ((337204 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep02Coefficient05 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep02CoefficientIdentity05 :
    row18_reducedY00_combinationStep02Coefficient05 =
      row18_reducedY00_combinationStep01Coefficient05 +
        row18_reducedY00_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep02Coefficient05 row18_reducedY00_combinationStep01Coefficient05 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep02Coefficient06 : ℂ :=
  (-((17990 / 18723) : ℂ) + ((1231 / 12482) : ℂ) * ζ ^ 1 - ((5956 / 6241) : ℂ) * ζ ^ 2 - ((102158 / 93615) : ℂ) * ζ ^ 3 + ((3696 / 6241) : ℂ) * ζ ^ 6 - ((3344 / 18723) : ℂ) * ζ ^ 8 - ((15837 / 12482) : ℂ) * ζ ^ 9 + ((170713 / 187230) : ℂ) * ζ ^ 11 + ((9652 / 6241) : ℂ) * ζ ^ 12 - ((1231 / 12482) : ℂ) * ζ ^ 13 - ((102158 / 93615) : ℂ) * ζ ^ 15 - ((1231 / 12482) : ℂ) * ζ ^ 17 - ((122 / 18723) : ℂ) * ζ ^ 18 - ((1231 / 12482) : ℂ) * ζ ^ 21 + ((5956 / 6241) : ℂ) * ζ ^ 22 - ((5956 / 6241) : ℂ) * ζ ^ 24 + ((1231 / 12482) : ℂ) * ζ ^ 25 + ((170713 / 187230) : ℂ) * ζ ^ 27 + ((3344 / 18723) : ℂ) * ζ ^ 28 + ((1231 / 12482) : ℂ) * ζ ^ 29 - ((21212 / 18723) : ℂ) * ζ ^ 30 - ((170713 / 187230) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep02CoefficientIdentity06 :
    row18_reducedY00_combinationStep02Coefficient06 =
      row18_reducedY00_combinationStep01Coefficient06 +
        row18_reducedY00_combinationStep02Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep02Coefficient06 row18_reducedY00_combinationStep01Coefficient06 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 (((565057 / 493039) : ℂ) - ((99092 / 1479117) : ℂ) * ζ ^ 1 + ((10707176 / 7395585) : ℂ) * ζ ^ 2 + ((1763207 / 2465195) : ℂ) * ζ ^ 3 - ((7592258 / 7395585) : ℂ) * ζ ^ 4 + ((1585289 / 14791170) : ℂ) * ζ ^ 5 - ((14600789 / 14791170) : ℂ) * ζ ^ 6 - ((830415 / 986078) : ℂ) * ζ ^ 7 + ((9207081 / 4930390) : ℂ) * ζ ^ 8 + ((3353947 / 14791170) : ℂ) * ζ ^ 9 + ((258673 / 14791170) : ℂ) * ζ ^ 10 - ((300061 / 4930390) : ℂ) * ζ ^ 11 - ((193801 / 187230) : ℂ) * ζ ^ 12 - ((4096996 / 7395585) : ℂ) * ζ ^ 13 - ((5288423 / 14791170) : ℂ) * ζ ^ 14 + ((2027626 / 7395585) : ℂ) * ζ ^ 15 + ((2634554 / 7395585) : ℂ) * ζ ^ 16 - ((111413 / 493039) : ℂ) * ζ ^ 17 + ((1047128 / 2465195) : ℂ) * ζ ^ 18 - ((8454889 / 14791170) : ℂ) * ζ ^ 19 - ((26821 / 986078) : ℂ) * ζ ^ 20 + ((182931 / 986078) : ℂ) * ζ ^ 21 - ((4831442 / 7395585) : ℂ) * ζ ^ 22 + ((1211942 / 1479117) : ℂ) * ζ ^ 23 + ((54199 / 2465195) : ℂ) * ζ ^ 24 - ((171877 / 2958234) : ℂ) * ζ ^ 25 + ((6213581 / 7395585) : ℂ) * ζ ^ 26 - ((5159233 / 4930390) : ℂ) * ζ ^ 27 - ((6171109 / 14791170) : ℂ) * ζ ^ 28 + ((588509 / 986078) : ℂ) * ζ ^ 29 + ((120430 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep02Coefficient07 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep02CoefficientIdentity07 :
    row18_reducedY00_combinationStep02Coefficient07 =
      row18_reducedY00_combinationStep01Coefficient07 +
        row18_reducedY00_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep02Coefficient07 row18_reducedY00_combinationStep01Coefficient07 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep02Coefficient08 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep02CoefficientIdentity08 :
    row18_reducedY00_combinationStep02Coefficient08 =
      row18_reducedY00_combinationStep01Coefficient08 +
        row18_reducedY00_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep02Coefficient08 row18_reducedY00_combinationStep01Coefficient08 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep02Coefficient09 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep02CoefficientIdentity09 :
    row18_reducedY00_combinationStep02Coefficient09 =
      row18_reducedY00_combinationStep01Coefficient09 +
        row18_reducedY00_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep02Coefficient09 row18_reducedY00_combinationStep01Coefficient09 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep02Coefficient10 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep02CoefficientIdentity10 :
    row18_reducedY00_combinationStep02Coefficient10 =
      row18_reducedY00_combinationStep01Coefficient10 +
        row18_reducedY00_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep02Coefficient10 row18_reducedY00_combinationStep01Coefficient10 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep02Coefficient11 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep02CoefficientIdentity11 :
    row18_reducedY00_combinationStep02Coefficient11 =
      row18_reducedY00_combinationStep01Coefficient11 +
        row18_reducedY00_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep02Coefficient11 row18_reducedY00_combinationStep01Coefficient11 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep02Coefficient12 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep02CoefficientIdentity12 :
    row18_reducedY00_combinationStep02Coefficient12 =
      row18_reducedY00_combinationStep01Coefficient12 +
        row18_reducedY00_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep02Coefficient12 row18_reducedY00_combinationStep01Coefficient12 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep02Coefficient13 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep02CoefficientIdentity13 :
    row18_reducedY00_combinationStep02Coefficient13 =
      row18_reducedY00_combinationStep01Coefficient13 +
        row18_reducedY00_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep02Coefficient13 row18_reducedY00_combinationStep01Coefficient13 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep02Coefficient14 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep02CoefficientIdentity14 :
    row18_reducedY00_combinationStep02Coefficient14 =
      row18_reducedY00_combinationStep01Coefficient14 +
        row18_reducedY00_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep02Coefficient14 row18_reducedY00_combinationStep01Coefficient14 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep02Coefficient15 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep02CoefficientIdentity15 :
    row18_reducedY00_combinationStep02Coefficient15 =
      row18_reducedY00_combinationStep01Coefficient15 +
        row18_reducedY00_combinationStep02Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep02Coefficient15 row18_reducedY00_combinationStep01Coefficient15 row18_reducedY00_combinationStep02Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY00_combinationStep02
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY00_combinationStep02Coefficient00) * Y 0 0
      + (row18_reducedY00_combinationStep02Coefficient01) * Y 0 1
      + (row18_reducedY00_combinationStep02Coefficient02) * Y 1 0
      + (row18_reducedY00_combinationStep02Coefficient03) * Y 1 1
      + (row18_reducedY00_combinationStep02Coefficient04) * Y 2 2
      + (row18_reducedY00_combinationStep02Coefficient05) * Y 2 3
      + (row18_reducedY00_combinationStep02Coefficient06) * Y 3 2
      + (row18_reducedY00_combinationStep02Coefficient07) * Y 3 3
      + (row18_reducedY00_combinationStep02Coefficient08) * Y 4 4
      + (row18_reducedY00_combinationStep02Coefficient09) * Y 4 5
      + (row18_reducedY00_combinationStep02Coefficient10) * Y 5 4
      + (row18_reducedY00_combinationStep02Coefficient11) * Y 5 5
      + (row18_reducedY00_combinationStep02Coefficient12) * Y 6 6
      + (row18_reducedY00_combinationStep02Coefficient13) * Y 6 7
      + (row18_reducedY00_combinationStep02Coefficient14) * Y 7 6
      + (row18_reducedY00_combinationStep02Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY00_combinationStep01 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation02
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY00_combinationStep02CoefficientIdentity00,
      row18_reducedY00_combinationStep02CoefficientIdentity01,
      row18_reducedY00_combinationStep02CoefficientIdentity02,
      row18_reducedY00_combinationStep02CoefficientIdentity03,
      row18_reducedY00_combinationStep02CoefficientIdentity04,
      row18_reducedY00_combinationStep02CoefficientIdentity05,
      row18_reducedY00_combinationStep02CoefficientIdentity06,
      row18_reducedY00_combinationStep02CoefficientIdentity07,
      row18_reducedY00_combinationStep02CoefficientIdentity08,
      row18_reducedY00_combinationStep02CoefficientIdentity09,
      row18_reducedY00_combinationStep02CoefficientIdentity10,
      row18_reducedY00_combinationStep02CoefficientIdentity11,
      row18_reducedY00_combinationStep02CoefficientIdentity12,
      row18_reducedY00_combinationStep02CoefficientIdentity13,
      row18_reducedY00_combinationStep02CoefficientIdentity14,
      row18_reducedY00_combinationStep02CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY00_combinationStep02Multiplier * equation

private def row18_reducedY00_combinationStep03Multiplier : ℂ :=
  (-((1622 / 18723) : ℂ) + ((7306 / 6241) : ℂ) * ζ ^ 1 - ((57376 / 18723) : ℂ) * ζ ^ 2 - ((35814 / 6241) : ℂ) * ζ ^ 5 - ((55754 / 18723) : ℂ) * ζ ^ 6 - ((55754 / 18723) : ℂ) * ζ ^ 8 - ((35814 / 6241) : ℂ) * ζ ^ 9 - ((81878 / 18723) : ℂ) * ζ ^ 11 - ((17860 / 18723) : ℂ) * ζ ^ 12 - ((7306 / 6241) : ℂ) * ζ ^ 13 - ((19552 / 6241) : ℂ) * ζ ^ 15 - ((7306 / 6241) : ℂ) * ζ ^ 17 + ((6784 / 6241) : ℂ) * ζ ^ 18 + ((14254 / 6241) : ℂ) * ζ ^ 21 + ((57376 / 18723) : ℂ) * ζ ^ 22 + ((35402 / 18723) : ℂ) * ζ ^ 24 + ((43120 / 6241) : ℂ) * ζ ^ 25 + ((19552 / 6241) : ℂ) * ζ ^ 27 + ((55754 / 18723) : ℂ) * ζ ^ 28 + ((7306 / 6241) : ℂ) * ζ ^ 29 - ((37894 / 18723) : ℂ) * ζ ^ 30 + ((81878 / 18723) : ℂ) * ζ ^ 31)

private def row18_reducedY00_combinationStep03Coefficient00 : ℂ :=
  (((88 / 79) : ℂ) - ((222 / 395) : ℂ) * ζ ^ 1 + ((1028 / 395) : ℂ) * ζ ^ 2 + ((261 / 790) : ℂ) * ζ ^ 3 + ((483 / 790) : ℂ) * ζ ^ 5 + ((1322 / 395) : ℂ) * ζ ^ 6 + ((191 / 79) : ℂ) * ζ ^ 8 + ((1573 / 790) : ℂ) * ζ ^ 9 + ((656 / 395) : ℂ) * ζ ^ 11 + ((191 / 79) : ℂ) * ζ ^ 12 + ((222 / 395) : ℂ) * ζ ^ 13 + ((333 / 395) : ℂ) * ζ ^ 15 + ((222 / 395) : ℂ) * ζ ^ 17 - ((294 / 395) : ℂ) * ζ ^ 18 + ((183 / 790) : ℂ) * ζ ^ 21 - ((1028 / 395) : ℂ) * ζ ^ 22 - ((927 / 790) : ℂ) * ζ ^ 25 - ((183 / 790) : ℂ) * ζ ^ 27 - ((191 / 79) : ℂ) * ζ ^ 28 - ((222 / 395) : ℂ) * ζ ^ 29 + ((661 / 395) : ℂ) * ζ ^ 30 - ((656 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep03CoefficientIdentity00 :
    row18_reducedY00_combinationStep03Coefficient00 =
      row18_reducedY00_combinationStep02Coefficient00 +
        row18_reducedY00_combinationStep03Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep03Coefficient00 row18_reducedY00_combinationStep02Coefficient00 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 (((248821 / 986078) : ℂ) + ((136265 / 2958234) : ℂ) * ζ ^ 1 - ((2860574 / 1479117) : ℂ) * ζ ^ 2 - ((698276 / 1479117) : ℂ) * ζ ^ 3 - ((1325047 / 2958234) : ℂ) * ζ ^ 4 - ((625562 / 1479117) : ℂ) * ζ ^ 5 + ((311353 / 986078) : ℂ) * ζ ^ 6 + ((770314 / 1479117) : ℂ) * ζ ^ 7 - ((2023727 / 2958234) : ℂ) * ζ ^ 8 + ((371111 / 2958234) : ℂ) * ζ ^ 9 + ((229703 / 2958234) : ℂ) * ζ ^ 10 + ((85411 / 1479117) : ℂ) * ζ ^ 11 + ((368571 / 986078) : ℂ) * ζ ^ 12 + ((1142963 / 1479117) : ℂ) * ζ ^ 13 - ((115973 / 1479117) : ℂ) * ζ ^ 14 + ((11863 / 2958234) : ℂ) * ζ ^ 15 - ((464105 / 2958234) : ℂ) * ζ ^ 16 - ((235201 / 986078) : ℂ) * ζ ^ 17 - ((206600 / 1479117) : ℂ) * ζ ^ 18 + ((532282 / 1479117) : ℂ) * ζ ^ 19 + ((635117 / 1479117) : ℂ) * ζ ^ 20 + ((365068 / 493039) : ℂ) * ζ ^ 21 + ((34789 / 493039) : ℂ) * ζ ^ 22 - ((747511 / 986078) : ℂ) * ζ ^ 23 - ((287407 / 2958234) : ℂ) * ζ ^ 24 + ((136549 / 1479117) : ℂ) * ζ ^ 25 - ((905093 / 1479117) : ℂ) * ζ ^ 26 + ((1717525 / 2958234) : ℂ) * ζ ^ 27 + ((106432 / 1479117) : ℂ) * ζ ^ 28 - ((560289 / 986078) : ℂ) * ζ ^ 29 - ((204695 / 986078) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep03Coefficient01 : ℂ :=
  (-((33 / 158) : ℂ) + ((23 / 158) : ℂ) * ζ ^ 1 - ((7 / 158) : ℂ) * ζ ^ 2 - ((14 / 79) : ℂ) * ζ ^ 3 + ((23 / 158) : ℂ) * ζ ^ 5 - ((20 / 79) : ℂ) * ζ ^ 6 + ((20 / 79) : ℂ) * ζ ^ 8 - ((23 / 158) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((45 / 158) : ℂ) * ζ ^ 12 - ((23 / 158) : ℂ) * ζ ^ 13 - ((11 / 158) : ℂ) * ζ ^ 15 - ((23 / 158) : ℂ) * ζ ^ 17 + ((16 / 79) : ℂ) * ζ ^ 18 - ((29 / 79) : ℂ) * ζ ^ 21 + ((7 / 158) : ℂ) * ζ ^ 22 - ((4 / 79) : ℂ) * ζ ^ 24 - ((39 / 158) : ℂ) * ζ ^ 27 - ((20 / 79) : ℂ) * ζ ^ 28 + ((23 / 158) : ℂ) * ζ ^ 29 + ((5 / 158) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep03CoefficientIdentity01 :
    row18_reducedY00_combinationStep03Coefficient01 =
      row18_reducedY00_combinationStep02Coefficient01 +
        row18_reducedY00_combinationStep03Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep03Coefficient01 row18_reducedY00_combinationStep02Coefficient01 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 (-((12080167 / 2958234) : ℂ) + ((3790378 / 1479117) : ℂ) * ζ ^ 1 + ((766249 / 986078) : ℂ) * ζ ^ 2 - ((3931394 / 1479117) : ℂ) * ζ ^ 3 + ((1160302 / 493039) : ℂ) * ζ ^ 4 + ((105965 / 2958234) : ℂ) * ζ ^ 5 - ((7260101 / 1479117) : ℂ) * ζ ^ 6 - ((757009 / 493039) : ℂ) * ζ ^ 7 + ((739988 / 1479117) : ℂ) * ζ ^ 8 - ((8760455 / 2958234) : ℂ) * ζ ^ 9 + ((3534725 / 2958234) : ℂ) * ζ ^ 10 - ((4385917 / 2958234) : ℂ) * ζ ^ 11 - ((2068105 / 493039) : ℂ) * ζ ^ 12 + ((49606 / 493039) : ℂ) * ζ ^ 13 - ((4871317 / 1479117) : ℂ) * ζ ^ 14 - ((5773780 / 1479117) : ℂ) * ζ ^ 15 + ((780606 / 493039) : ℂ) * ζ ^ 16 - ((2588918 / 1479117) : ℂ) * ζ ^ 17 - ((4414543 / 1479117) : ℂ) * ζ ^ 18 + ((952997 / 2958234) : ℂ) * ζ ^ 19 - ((7733179 / 2958234) : ℂ) * ζ ^ 20 - ((4232179 / 1479117) : ℂ) * ζ ^ 21 + ((1632146 / 1479117) : ℂ) * ζ ^ 22 + ((267738 / 493039) : ℂ) * ζ ^ 23 - ((757696 / 1479117) : ℂ) * ζ ^ 24 + ((1503749 / 986078) : ℂ) * ζ ^ 25 - ((1581529 / 986078) : ℂ) * ζ ^ 26 + ((454861 / 2958234) : ℂ) * ζ ^ 27 + ((728549 / 986078) : ℂ) * ζ ^ 28 + ((226010 / 1479117) : ℂ) * ζ ^ 29 + ((573146 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep03Coefficient02 : ℂ :=
  (-((28871 / 37446) : ℂ) - ((23941 / 12482) : ℂ) * ζ ^ 1 + ((20496 / 6241) : ℂ) * ζ ^ 2 + ((39379 / 37446) : ℂ) * ζ ^ 3 - ((108839 / 18723) : ℂ) * ζ ^ 5 + ((98803 / 37446) : ℂ) * ζ ^ 6 + ((51593 / 37446) : ℂ) * ζ ^ 8 - ((18508 / 18723) : ℂ) * ζ ^ 9 - ((250945 / 37446) : ℂ) * ζ ^ 11 + ((24173 / 37446) : ℂ) * ζ ^ 12 + ((23941 / 12482) : ℂ) * ζ ^ 13 - ((39379 / 37446) : ℂ) * ζ ^ 15 + ((23941 / 12482) : ℂ) * ζ ^ 17 - ((94105 / 37446) : ℂ) * ζ ^ 18 + ((145855 / 37446) : ℂ) * ζ ^ 21 - ((20496 / 6241) : ℂ) * ζ ^ 22 - ((20496 / 6241) : ℂ) * ζ ^ 24 + ((145855 / 37446) : ℂ) * ζ ^ 25 + ((250945 / 37446) : ℂ) * ζ ^ 27 - ((51593 / 37446) : ℂ) * ζ ^ 28 - ((23941 / 12482) : ℂ) * ζ ^ 29 + ((71383 / 37446) : ℂ) * ζ ^ 30 + ((250945 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep03CoefficientIdentity02 :
    row18_reducedY00_combinationStep03Coefficient02 =
      row18_reducedY00_combinationStep02Coefficient02 +
        row18_reducedY00_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep03Coefficient02 row18_reducedY00_combinationStep02Coefficient02 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep03Coefficient03 : ℂ :=
  (-((24631 / 12482) : ℂ) + ((9190 / 18723) : ℂ) * ζ ^ 1 + ((10277 / 18723) : ℂ) * ζ ^ 2 + ((20528 / 18723) : ℂ) * ζ ^ 3 + ((6197 / 18723) : ℂ) * ζ ^ 5 + ((20630 / 18723) : ℂ) * ζ ^ 6 + ((13775 / 37446) : ℂ) * ζ ^ 8 + ((14137 / 37446) : ℂ) * ζ ^ 9 - ((8973 / 12482) : ℂ) * ζ ^ 11 + ((13775 / 37446) : ℂ) * ζ ^ 12 - ((9190 / 18723) : ℂ) * ζ ^ 13 - ((23521 / 18723) : ℂ) * ζ ^ 15 - ((9190 / 18723) : ℂ) * ζ ^ 17 - ((3451 / 6241) : ℂ) * ζ ^ 18 - ((9906 / 6241) : ℂ) * ζ ^ 21 - ((10277 / 18723) : ℂ) * ζ ^ 22 + ((2993 / 18723) : ℂ) * ζ ^ 25 + ((9906 / 6241) : ℂ) * ζ ^ 27 - ((13775 / 37446) : ℂ) * ζ ^ 28 + ((9190 / 18723) : ℂ) * ζ ^ 29 + ((10315 / 18723) : ℂ) * ζ ^ 30 + ((8973 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep03CoefficientIdentity03 :
    row18_reducedY00_combinationStep03Coefficient03 =
      row18_reducedY00_combinationStep02Coefficient03 +
        row18_reducedY00_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep03Coefficient03 row18_reducedY00_combinationStep02Coefficient03 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep03Coefficient04 : ℂ :=
  (((11171 / 18723) : ℂ) + ((5288 / 31205) : ℂ) * ζ ^ 1 - ((51087 / 31205) : ℂ) * ζ ^ 2 - ((73141 / 93615) : ℂ) * ζ ^ 3 - ((95753 / 93615) : ℂ) * ζ ^ 5 - ((92423 / 31205) : ℂ) * ζ ^ 6 - ((24877 / 12482) : ℂ) * ζ ^ 8 - ((488321 / 187230) : ℂ) * ζ ^ 9 - ((114013 / 62410) : ℂ) * ζ ^ 11 - ((24877 / 12482) : ℂ) * ζ ^ 12 - ((5288 / 31205) : ℂ) * ζ ^ 13 - ((38476 / 93615) : ℂ) * ζ ^ 15 - ((5288 / 31205) : ℂ) * ζ ^ 17 + ((41336 / 31205) : ℂ) * ζ ^ 18 + ((57277 / 93615) : ℂ) * ζ ^ 21 + ((51087 / 31205) : ℂ) * ζ ^ 22 + ((111617 / 93615) : ℂ) * ζ ^ 25 - ((57277 / 93615) : ℂ) * ζ ^ 27 + ((24877 / 12482) : ℂ) * ζ ^ 28 + ((5288 / 31205) : ℂ) * ζ ^ 29 - ((92423 / 62410) : ℂ) * ζ ^ 30 + ((114013 / 62410) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep03CoefficientIdentity04 :
    row18_reducedY00_combinationStep03Coefficient04 =
      row18_reducedY00_combinationStep02Coefficient04 +
        row18_reducedY00_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep03Coefficient04 row18_reducedY00_combinationStep02Coefficient04 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep03Coefficient05 : ℂ :=
  (-((20987 / 37446) : ℂ) + ((6289 / 18723) : ℂ) * ζ ^ 1 - ((67339 / 37446) : ℂ) * ζ ^ 2 - ((6111 / 6241) : ℂ) * ζ ^ 5 - ((23176 / 18723) : ℂ) * ζ ^ 6 - ((23176 / 18723) : ℂ) * ζ ^ 8 - ((6111 / 6241) : ℂ) * ζ ^ 9 - ((28049 / 12482) : ℂ) * ζ ^ 11 - ((22372 / 18723) : ℂ) * ζ ^ 12 - ((6289 / 18723) : ℂ) * ζ ^ 13 - ((27113 / 18723) : ℂ) * ζ ^ 15 - ((6289 / 18723) : ℂ) * ζ ^ 17 + ((10615 / 12482) : ℂ) * ζ ^ 18 + ((6022 / 18723) : ℂ) * ζ ^ 21 + ((67339 / 37446) : ℂ) * ζ ^ 22 + ((14507 / 37446) : ℂ) * ζ ^ 24 + ((24622 / 18723) : ℂ) * ζ ^ 25 + ((27113 / 18723) : ℂ) * ζ ^ 27 + ((23176 / 18723) : ℂ) * ζ ^ 28 + ((6289 / 18723) : ℂ) * ζ ^ 29 - ((268 / 6241) : ℂ) * ζ ^ 30 + ((28049 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep03CoefficientIdentity05 :
    row18_reducedY00_combinationStep03Coefficient05 =
      row18_reducedY00_combinationStep02Coefficient05 +
        row18_reducedY00_combinationStep03Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep03Coefficient05 row18_reducedY00_combinationStep02Coefficient05 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 (((1648241 / 2958234) : ℂ) - ((284411 / 986078) : ℂ) * ζ ^ 1 + ((1595347 / 986078) : ℂ) * ζ ^ 2 + ((416235 / 986078) : ℂ) * ζ ^ 3 - ((4108639 / 2958234) : ℂ) * ζ ^ 4 + ((524527 / 493039) : ℂ) * ζ ^ 5 - ((228519 / 986078) : ℂ) * ζ ^ 6 - ((1900909 / 986078) : ℂ) * ζ ^ 7 + ((1428063 / 986078) : ℂ) * ζ ^ 8 - ((463048 / 1479117) : ℂ) * ζ ^ 9 - ((163028 / 493039) : ℂ) * ζ ^ 10 + ((2372098 / 1479117) : ℂ) * ζ ^ 11 + ((106531 / 493039) : ℂ) * ζ ^ 12 - ((315019 / 493039) : ℂ) * ζ ^ 13 + ((4750495 / 2958234) : ℂ) * ζ ^ 14 - ((478724 / 493039) : ℂ) * ζ ^ 15 - ((1479305 / 1479117) : ℂ) * ζ ^ 16 + ((1591165 / 1479117) : ℂ) * ζ ^ 17 - ((1770376 / 1479117) : ℂ) * ζ ^ 18 - ((329103 / 493039) : ℂ) * ζ ^ 19 + ((958697 / 1479117) : ℂ) * ζ ^ 20 - ((2520863 / 2958234) : ℂ) * ζ ^ 21 - ((143661 / 986078) : ℂ) * ζ ^ 22 + ((593207 / 2958234) : ℂ) * ζ ^ 23 - ((238721 / 986078) : ℂ) * ζ ^ 24 - ((127805 / 2958234) : ℂ) * ζ ^ 25 - ((707315 / 2958234) : ℂ) * ζ ^ 26 + ((713174 / 1479117) : ℂ) * ζ ^ 27 - ((906907 / 2958234) : ℂ) * ζ ^ 28 + ((460141 / 1479117) : ℂ) * ζ ^ 29 - ((286573 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep03Coefficient06 : ℂ :=
  (-((17990 / 18723) : ℂ) + ((1231 / 12482) : ℂ) * ζ ^ 1 - ((5956 / 6241) : ℂ) * ζ ^ 2 - ((102158 / 93615) : ℂ) * ζ ^ 3 + ((3696 / 6241) : ℂ) * ζ ^ 6 - ((3344 / 18723) : ℂ) * ζ ^ 8 - ((15837 / 12482) : ℂ) * ζ ^ 9 + ((170713 / 187230) : ℂ) * ζ ^ 11 + ((9652 / 6241) : ℂ) * ζ ^ 12 - ((1231 / 12482) : ℂ) * ζ ^ 13 - ((102158 / 93615) : ℂ) * ζ ^ 15 - ((1231 / 12482) : ℂ) * ζ ^ 17 - ((122 / 18723) : ℂ) * ζ ^ 18 - ((1231 / 12482) : ℂ) * ζ ^ 21 + ((5956 / 6241) : ℂ) * ζ ^ 22 - ((5956 / 6241) : ℂ) * ζ ^ 24 + ((1231 / 12482) : ℂ) * ζ ^ 25 + ((170713 / 187230) : ℂ) * ζ ^ 27 + ((3344 / 18723) : ℂ) * ζ ^ 28 + ((1231 / 12482) : ℂ) * ζ ^ 29 - ((21212 / 18723) : ℂ) * ζ ^ 30 - ((170713 / 187230) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep03CoefficientIdentity06 :
    row18_reducedY00_combinationStep03Coefficient06 =
      row18_reducedY00_combinationStep02Coefficient06 +
        row18_reducedY00_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep03Coefficient06 row18_reducedY00_combinationStep02Coefficient06 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep03Coefficient07 : ℂ :=
  (((9839 / 37446) : ℂ) - ((1840 / 18723) : ℂ) * ζ ^ 1 - ((28352 / 18723) : ℂ) * ζ ^ 2 - ((8057 / 12482) : ℂ) * ζ ^ 3 + ((3013 / 37446) : ℂ) * ζ ^ 5 - ((27839 / 18723) : ℂ) * ζ ^ 6 - ((14839 / 18723) : ℂ) * ζ ^ 8 + ((2989 / 12482) : ℂ) * ζ ^ 9 + ((5523 / 6241) : ℂ) * ζ ^ 11 - ((14839 / 18723) : ℂ) * ζ ^ 12 + ((1840 / 18723) : ℂ) * ζ ^ 13 + ((5144 / 6241) : ℂ) * ζ ^ 15 + ((1840 / 18723) : ℂ) * ζ ^ 17 - ((171 / 6241) : ℂ) * ζ ^ 18 + ((27851 / 37446) : ℂ) * ζ ^ 21 + ((28352 / 18723) : ℂ) * ζ ^ 22 - ((2231 / 12482) : ℂ) * ζ ^ 25 - ((27851 / 37446) : ℂ) * ζ ^ 27 + ((14839 / 18723) : ℂ) * ζ ^ 28 - ((1840 / 18723) : ℂ) * ζ ^ 29 - ((27839 / 37446) : ℂ) * ζ ^ 30 - ((5523 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep03CoefficientIdentity07 :
    row18_reducedY00_combinationStep03Coefficient07 =
      row18_reducedY00_combinationStep02Coefficient07 +
        row18_reducedY00_combinationStep03Multiplier *
          (-((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep03Coefficient07 row18_reducedY00_combinationStep02Coefficient07 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 (-((248821 / 986078) : ℂ) - ((136265 / 2958234) : ℂ) * ζ ^ 1 + ((2860574 / 1479117) : ℂ) * ζ ^ 2 + ((698276 / 1479117) : ℂ) * ζ ^ 3 + ((1325047 / 2958234) : ℂ) * ζ ^ 4 + ((625562 / 1479117) : ℂ) * ζ ^ 5 - ((311353 / 986078) : ℂ) * ζ ^ 6 - ((770314 / 1479117) : ℂ) * ζ ^ 7 + ((2023727 / 2958234) : ℂ) * ζ ^ 8 - ((371111 / 2958234) : ℂ) * ζ ^ 9 - ((229703 / 2958234) : ℂ) * ζ ^ 10 - ((85411 / 1479117) : ℂ) * ζ ^ 11 - ((368571 / 986078) : ℂ) * ζ ^ 12 - ((1142963 / 1479117) : ℂ) * ζ ^ 13 + ((115973 / 1479117) : ℂ) * ζ ^ 14 - ((11863 / 2958234) : ℂ) * ζ ^ 15 + ((464105 / 2958234) : ℂ) * ζ ^ 16 + ((235201 / 986078) : ℂ) * ζ ^ 17 + ((206600 / 1479117) : ℂ) * ζ ^ 18 - ((532282 / 1479117) : ℂ) * ζ ^ 19 - ((635117 / 1479117) : ℂ) * ζ ^ 20 - ((365068 / 493039) : ℂ) * ζ ^ 21 - ((34789 / 493039) : ℂ) * ζ ^ 22 + ((747511 / 986078) : ℂ) * ζ ^ 23 + ((287407 / 2958234) : ℂ) * ζ ^ 24 - ((136549 / 1479117) : ℂ) * ζ ^ 25 + ((905093 / 1479117) : ℂ) * ζ ^ 26 - ((1717525 / 2958234) : ℂ) * ζ ^ 27 - ((106432 / 1479117) : ℂ) * ζ ^ 28 + ((560289 / 986078) : ℂ) * ζ ^ 29 + ((204695 / 986078) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep03Coefficient08 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep03CoefficientIdentity08 :
    row18_reducedY00_combinationStep03Coefficient08 =
      row18_reducedY00_combinationStep02Coefficient08 +
        row18_reducedY00_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep03Coefficient08 row18_reducedY00_combinationStep02Coefficient08 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep03Coefficient09 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep03CoefficientIdentity09 :
    row18_reducedY00_combinationStep03Coefficient09 =
      row18_reducedY00_combinationStep02Coefficient09 +
        row18_reducedY00_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep03Coefficient09 row18_reducedY00_combinationStep02Coefficient09 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep03Coefficient10 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep03CoefficientIdentity10 :
    row18_reducedY00_combinationStep03Coefficient10 =
      row18_reducedY00_combinationStep02Coefficient10 +
        row18_reducedY00_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep03Coefficient10 row18_reducedY00_combinationStep02Coefficient10 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep03Coefficient11 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep03CoefficientIdentity11 :
    row18_reducedY00_combinationStep03Coefficient11 =
      row18_reducedY00_combinationStep02Coefficient11 +
        row18_reducedY00_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep03Coefficient11 row18_reducedY00_combinationStep02Coefficient11 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep03Coefficient12 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep03CoefficientIdentity12 :
    row18_reducedY00_combinationStep03Coefficient12 =
      row18_reducedY00_combinationStep02Coefficient12 +
        row18_reducedY00_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep03Coefficient12 row18_reducedY00_combinationStep02Coefficient12 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep03Coefficient13 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep03CoefficientIdentity13 :
    row18_reducedY00_combinationStep03Coefficient13 =
      row18_reducedY00_combinationStep02Coefficient13 +
        row18_reducedY00_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep03Coefficient13 row18_reducedY00_combinationStep02Coefficient13 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep03Coefficient14 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep03CoefficientIdentity14 :
    row18_reducedY00_combinationStep03Coefficient14 =
      row18_reducedY00_combinationStep02Coefficient14 +
        row18_reducedY00_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep03Coefficient14 row18_reducedY00_combinationStep02Coefficient14 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep03Coefficient15 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep03CoefficientIdentity15 :
    row18_reducedY00_combinationStep03Coefficient15 =
      row18_reducedY00_combinationStep02Coefficient15 +
        row18_reducedY00_combinationStep03Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep03Coefficient15 row18_reducedY00_combinationStep02Coefficient15 row18_reducedY00_combinationStep03Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY00_combinationStep03
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY00_combinationStep03Coefficient00) * Y 0 0
      + (row18_reducedY00_combinationStep03Coefficient01) * Y 0 1
      + (row18_reducedY00_combinationStep03Coefficient02) * Y 1 0
      + (row18_reducedY00_combinationStep03Coefficient03) * Y 1 1
      + (row18_reducedY00_combinationStep03Coefficient04) * Y 2 2
      + (row18_reducedY00_combinationStep03Coefficient05) * Y 2 3
      + (row18_reducedY00_combinationStep03Coefficient06) * Y 3 2
      + (row18_reducedY00_combinationStep03Coefficient07) * Y 3 3
      + (row18_reducedY00_combinationStep03Coefficient08) * Y 4 4
      + (row18_reducedY00_combinationStep03Coefficient09) * Y 4 5
      + (row18_reducedY00_combinationStep03Coefficient10) * Y 5 4
      + (row18_reducedY00_combinationStep03Coefficient11) * Y 5 5
      + (row18_reducedY00_combinationStep03Coefficient12) * Y 6 6
      + (row18_reducedY00_combinationStep03Coefficient13) * Y 6 7
      + (row18_reducedY00_combinationStep03Coefficient14) * Y 7 6
      + (row18_reducedY00_combinationStep03Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY00_combinationStep02 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation03
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY00_combinationStep03CoefficientIdentity00,
      row18_reducedY00_combinationStep03CoefficientIdentity01,
      row18_reducedY00_combinationStep03CoefficientIdentity02,
      row18_reducedY00_combinationStep03CoefficientIdentity03,
      row18_reducedY00_combinationStep03CoefficientIdentity04,
      row18_reducedY00_combinationStep03CoefficientIdentity05,
      row18_reducedY00_combinationStep03CoefficientIdentity06,
      row18_reducedY00_combinationStep03CoefficientIdentity07,
      row18_reducedY00_combinationStep03CoefficientIdentity08,
      row18_reducedY00_combinationStep03CoefficientIdentity09,
      row18_reducedY00_combinationStep03CoefficientIdentity10,
      row18_reducedY00_combinationStep03CoefficientIdentity11,
      row18_reducedY00_combinationStep03CoefficientIdentity12,
      row18_reducedY00_combinationStep03CoefficientIdentity13,
      row18_reducedY00_combinationStep03CoefficientIdentity14,
      row18_reducedY00_combinationStep03CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY00_combinationStep03Multiplier * equation

private def row18_reducedY00_combinationStep04Multiplier : ℂ :=
  (-((14 / 79) : ℂ) - ((120 / 79) : ℂ) * ζ ^ 1 - ((218 / 79) : ℂ) * ζ ^ 2 + ((52 / 79) : ℂ) * ζ ^ 5 - ((204 / 79) : ℂ) * ζ ^ 6 - ((204 / 79) : ℂ) * ζ ^ 8 + ((52 / 79) : ℂ) * ζ ^ 9 + ((94 / 79) : ℂ) * ζ ^ 11 - ((2 / 79) : ℂ) * ζ ^ 12 + ((120 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 + ((120 / 79) : ℂ) * ζ ^ 17 + ((148 / 79) : ℂ) * ζ ^ 18 + ((34 / 79) : ℂ) * ζ ^ 21 + ((218 / 79) : ℂ) * ζ ^ 22 + ((56 / 79) : ℂ) * ζ ^ 24 - ((172 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((204 / 79) : ℂ) * ζ ^ 28 - ((120 / 79) : ℂ) * ζ ^ 29 - ((202 / 79) : ℂ) * ζ ^ 30 - ((94 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY00_combinationStep04Coefficient00 : ℂ :=
  (((121 / 79) : ℂ) - ((342 / 395) : ℂ) * ζ ^ 1 + ((1961 / 790) : ℂ) * ζ ^ 2 + ((323 / 395) : ℂ) * ζ ^ 3 + ((289 / 395) : ℂ) * ζ ^ 5 + ((1332 / 395) : ℂ) * ζ ^ 6 + ((387 / 158) : ℂ) * ζ ^ 8 + ((1024 / 395) : ℂ) * ζ ^ 9 + ((701 / 395) : ℂ) * ζ ^ 11 + ((387 / 158) : ℂ) * ζ ^ 12 + ((342 / 395) : ℂ) * ζ ^ 13 + ((308 / 395) : ℂ) * ζ ^ 15 + ((342 / 395) : ℂ) * ζ ^ 17 - ((703 / 790) : ℂ) * ζ ^ 18 + ((19 / 395) : ℂ) * ζ ^ 21 - ((1961 / 790) : ℂ) * ζ ^ 22 - ((631 / 395) : ℂ) * ζ ^ 25 - ((19 / 395) : ℂ) * ζ ^ 27 - ((387 / 158) : ℂ) * ζ ^ 28 - ((342 / 395) : ℂ) * ζ ^ 29 + ((666 / 395) : ℂ) * ζ ^ 30 - ((701 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep04CoefficientIdentity00 :
    row18_reducedY00_combinationStep04Coefficient00 =
      row18_reducedY00_combinationStep03Coefficient00 +
        row18_reducedY00_combinationStep04Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep04Coefficient00 row18_reducedY00_combinationStep03Coefficient00 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 (-((2474 / 6241) : ℂ) + ((6163 / 12482) : ℂ) * ζ ^ 1 + ((3250 / 6241) : ℂ) * ζ ^ 2 - ((1919 / 6241) : ℂ) * ζ ^ 3 + ((7587 / 12482) : ℂ) * ζ ^ 4 - ((3018 / 6241) : ℂ) * ζ ^ 5 - ((1520 / 6241) : ℂ) * ζ ^ 6 + ((3459 / 6241) : ℂ) * ζ ^ 7 - ((315 / 12482) : ℂ) * ζ ^ 8 - ((1635 / 12482) : ℂ) * ζ ^ 9 + ((2433 / 12482) : ℂ) * ζ ^ 10 + ((203 / 12482) : ℂ) * ζ ^ 11 - ((1748 / 6241) : ℂ) * ζ ^ 12 + ((1205 / 6241) : ℂ) * ζ ^ 13 - ((837 / 12482) : ℂ) * ζ ^ 14 + ((894 / 6241) : ℂ) * ζ ^ 15 + ((247 / 12482) : ℂ) * ζ ^ 16 + ((163 / 6241) : ℂ) * ζ ^ 17 + ((1985 / 12482) : ℂ) * ζ ^ 18 - ((1125 / 6241) : ℂ) * ζ ^ 19 + ((871 / 12482) : ℂ) * ζ ^ 20 + ((706 / 6241) : ℂ) * ζ ^ 21 - ((3236 / 6241) : ℂ) * ζ ^ 22 + ((2 / 79) : ℂ) * ζ ^ 23 - ((710 / 6241) : ℂ) * ζ ^ 24 + ((240 / 6241) : ℂ) * ζ ^ 25 + ((10525 / 12482) : ℂ) * ζ ^ 26 - ((162 / 6241) : ℂ) * ζ ^ 27 - ((3337 / 12482) : ℂ) * ζ ^ 28 - ((741 / 12482) : ℂ) * ζ ^ 29 + ((705 / 12482) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep04Coefficient01 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep04CoefficientIdentity01 :
    row18_reducedY00_combinationStep04Coefficient01 =
      row18_reducedY00_combinationStep03Coefficient01 +
        row18_reducedY00_combinationStep04Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep04Coefficient01 row18_reducedY00_combinationStep03Coefficient01 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 (-((2719 / 12482) : ℂ) + ((390 / 6241) : ℂ) * ζ ^ 1 - ((1601 / 6241) : ℂ) * ζ ^ 2 - ((2752 / 6241) : ℂ) * ζ ^ 3 - ((518 / 6241) : ℂ) * ζ ^ 4 + ((676 / 6241) : ℂ) * ζ ^ 5 - ((1552 / 6241) : ℂ) * ζ ^ 6 + ((1011 / 6241) : ℂ) * ζ ^ 7 - ((495 / 6241) : ℂ) * ζ ^ 8 - ((1661 / 6241) : ℂ) * ζ ^ 9 + ((1017 / 6241) : ℂ) * ζ ^ 10 - ((893 / 12482) : ℂ) * ζ ^ 11 + ((1643 / 12482) : ℂ) * ζ ^ 12 + ((887 / 6241) : ℂ) * ζ ^ 13 - ((55 / 6241) : ℂ) * ζ ^ 14 - ((204 / 6241) : ℂ) * ζ ^ 15 - ((886 / 6241) : ℂ) * ζ ^ 16 + ((638 / 6241) : ℂ) * ζ ^ 17 + ((2889 / 12482) : ℂ) * ζ ^ 18 + ((2551 / 12482) : ℂ) * ζ ^ 19 + ((5915 / 12482) : ℂ) * ζ ^ 20 - ((4831 / 12482) : ℂ) * ζ ^ 21 - ((1303 / 6241) : ℂ) * ζ ^ 22 + ((594 / 6241) : ℂ) * ζ ^ 23 + ((2049 / 6241) : ℂ) * ζ ^ 24 + ((442 / 6241) : ℂ) * ζ ^ 25 + ((72 / 6241) : ℂ) * ζ ^ 26 - ((3541 / 12482) : ℂ) * ζ ^ 27 - ((889 / 12482) : ℂ) * ζ ^ 28 + ((425 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep04Coefficient02 : ℂ :=
  (-((28871 / 37446) : ℂ) - ((23941 / 12482) : ℂ) * ζ ^ 1 + ((20496 / 6241) : ℂ) * ζ ^ 2 + ((39379 / 37446) : ℂ) * ζ ^ 3 - ((108839 / 18723) : ℂ) * ζ ^ 5 + ((98803 / 37446) : ℂ) * ζ ^ 6 + ((51593 / 37446) : ℂ) * ζ ^ 8 - ((18508 / 18723) : ℂ) * ζ ^ 9 - ((250945 / 37446) : ℂ) * ζ ^ 11 + ((24173 / 37446) : ℂ) * ζ ^ 12 + ((23941 / 12482) : ℂ) * ζ ^ 13 - ((39379 / 37446) : ℂ) * ζ ^ 15 + ((23941 / 12482) : ℂ) * ζ ^ 17 - ((94105 / 37446) : ℂ) * ζ ^ 18 + ((145855 / 37446) : ℂ) * ζ ^ 21 - ((20496 / 6241) : ℂ) * ζ ^ 22 - ((20496 / 6241) : ℂ) * ζ ^ 24 + ((145855 / 37446) : ℂ) * ζ ^ 25 + ((250945 / 37446) : ℂ) * ζ ^ 27 - ((51593 / 37446) : ℂ) * ζ ^ 28 - ((23941 / 12482) : ℂ) * ζ ^ 29 + ((71383 / 37446) : ℂ) * ζ ^ 30 + ((250945 / 37446) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep04CoefficientIdentity02 :
    row18_reducedY00_combinationStep04Coefficient02 =
      row18_reducedY00_combinationStep03Coefficient02 +
        row18_reducedY00_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep04Coefficient02 row18_reducedY00_combinationStep03Coefficient02 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep04Coefficient03 : ℂ :=
  (-((24631 / 12482) : ℂ) + ((9190 / 18723) : ℂ) * ζ ^ 1 + ((10277 / 18723) : ℂ) * ζ ^ 2 + ((20528 / 18723) : ℂ) * ζ ^ 3 + ((6197 / 18723) : ℂ) * ζ ^ 5 + ((20630 / 18723) : ℂ) * ζ ^ 6 + ((13775 / 37446) : ℂ) * ζ ^ 8 + ((14137 / 37446) : ℂ) * ζ ^ 9 - ((8973 / 12482) : ℂ) * ζ ^ 11 + ((13775 / 37446) : ℂ) * ζ ^ 12 - ((9190 / 18723) : ℂ) * ζ ^ 13 - ((23521 / 18723) : ℂ) * ζ ^ 15 - ((9190 / 18723) : ℂ) * ζ ^ 17 - ((3451 / 6241) : ℂ) * ζ ^ 18 - ((9906 / 6241) : ℂ) * ζ ^ 21 - ((10277 / 18723) : ℂ) * ζ ^ 22 + ((2993 / 18723) : ℂ) * ζ ^ 25 + ((9906 / 6241) : ℂ) * ζ ^ 27 - ((13775 / 37446) : ℂ) * ζ ^ 28 + ((9190 / 18723) : ℂ) * ζ ^ 29 + ((10315 / 18723) : ℂ) * ζ ^ 30 + ((8973 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep04CoefficientIdentity03 :
    row18_reducedY00_combinationStep04Coefficient03 =
      row18_reducedY00_combinationStep03Coefficient03 +
        row18_reducedY00_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep04Coefficient03 row18_reducedY00_combinationStep03Coefficient03 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep04Coefficient04 : ℂ :=
  (((11171 / 18723) : ℂ) + ((5288 / 31205) : ℂ) * ζ ^ 1 - ((51087 / 31205) : ℂ) * ζ ^ 2 - ((73141 / 93615) : ℂ) * ζ ^ 3 - ((95753 / 93615) : ℂ) * ζ ^ 5 - ((92423 / 31205) : ℂ) * ζ ^ 6 - ((24877 / 12482) : ℂ) * ζ ^ 8 - ((488321 / 187230) : ℂ) * ζ ^ 9 - ((114013 / 62410) : ℂ) * ζ ^ 11 - ((24877 / 12482) : ℂ) * ζ ^ 12 - ((5288 / 31205) : ℂ) * ζ ^ 13 - ((38476 / 93615) : ℂ) * ζ ^ 15 - ((5288 / 31205) : ℂ) * ζ ^ 17 + ((41336 / 31205) : ℂ) * ζ ^ 18 + ((57277 / 93615) : ℂ) * ζ ^ 21 + ((51087 / 31205) : ℂ) * ζ ^ 22 + ((111617 / 93615) : ℂ) * ζ ^ 25 - ((57277 / 93615) : ℂ) * ζ ^ 27 + ((24877 / 12482) : ℂ) * ζ ^ 28 + ((5288 / 31205) : ℂ) * ζ ^ 29 - ((92423 / 62410) : ℂ) * ζ ^ 30 + ((114013 / 62410) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep04CoefficientIdentity04 :
    row18_reducedY00_combinationStep04Coefficient04 =
      row18_reducedY00_combinationStep03Coefficient04 +
        row18_reducedY00_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep04Coefficient04 row18_reducedY00_combinationStep03Coefficient04 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep04Coefficient05 : ℂ :=
  (-((20987 / 37446) : ℂ) + ((6289 / 18723) : ℂ) * ζ ^ 1 - ((67339 / 37446) : ℂ) * ζ ^ 2 - ((6111 / 6241) : ℂ) * ζ ^ 5 - ((23176 / 18723) : ℂ) * ζ ^ 6 - ((23176 / 18723) : ℂ) * ζ ^ 8 - ((6111 / 6241) : ℂ) * ζ ^ 9 - ((28049 / 12482) : ℂ) * ζ ^ 11 - ((22372 / 18723) : ℂ) * ζ ^ 12 - ((6289 / 18723) : ℂ) * ζ ^ 13 - ((27113 / 18723) : ℂ) * ζ ^ 15 - ((6289 / 18723) : ℂ) * ζ ^ 17 + ((10615 / 12482) : ℂ) * ζ ^ 18 + ((6022 / 18723) : ℂ) * ζ ^ 21 + ((67339 / 37446) : ℂ) * ζ ^ 22 + ((14507 / 37446) : ℂ) * ζ ^ 24 + ((24622 / 18723) : ℂ) * ζ ^ 25 + ((27113 / 18723) : ℂ) * ζ ^ 27 + ((23176 / 18723) : ℂ) * ζ ^ 28 + ((6289 / 18723) : ℂ) * ζ ^ 29 - ((268 / 6241) : ℂ) * ζ ^ 30 + ((28049 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep04CoefficientIdentity05 :
    row18_reducedY00_combinationStep04Coefficient05 =
      row18_reducedY00_combinationStep03Coefficient05 +
        row18_reducedY00_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep04Coefficient05 row18_reducedY00_combinationStep03Coefficient05 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep04Coefficient06 : ℂ :=
  (-((17990 / 18723) : ℂ) + ((1231 / 12482) : ℂ) * ζ ^ 1 - ((5956 / 6241) : ℂ) * ζ ^ 2 - ((102158 / 93615) : ℂ) * ζ ^ 3 + ((3696 / 6241) : ℂ) * ζ ^ 6 - ((3344 / 18723) : ℂ) * ζ ^ 8 - ((15837 / 12482) : ℂ) * ζ ^ 9 + ((170713 / 187230) : ℂ) * ζ ^ 11 + ((9652 / 6241) : ℂ) * ζ ^ 12 - ((1231 / 12482) : ℂ) * ζ ^ 13 - ((102158 / 93615) : ℂ) * ζ ^ 15 - ((1231 / 12482) : ℂ) * ζ ^ 17 - ((122 / 18723) : ℂ) * ζ ^ 18 - ((1231 / 12482) : ℂ) * ζ ^ 21 + ((5956 / 6241) : ℂ) * ζ ^ 22 - ((5956 / 6241) : ℂ) * ζ ^ 24 + ((1231 / 12482) : ℂ) * ζ ^ 25 + ((170713 / 187230) : ℂ) * ζ ^ 27 + ((3344 / 18723) : ℂ) * ζ ^ 28 + ((1231 / 12482) : ℂ) * ζ ^ 29 - ((21212 / 18723) : ℂ) * ζ ^ 30 - ((170713 / 187230) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep04CoefficientIdentity06 :
    row18_reducedY00_combinationStep04Coefficient06 =
      row18_reducedY00_combinationStep03Coefficient06 +
        row18_reducedY00_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep04Coefficient06 row18_reducedY00_combinationStep03Coefficient06 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep04Coefficient07 : ℂ :=
  (((9839 / 37446) : ℂ) - ((1840 / 18723) : ℂ) * ζ ^ 1 - ((28352 / 18723) : ℂ) * ζ ^ 2 - ((8057 / 12482) : ℂ) * ζ ^ 3 + ((3013 / 37446) : ℂ) * ζ ^ 5 - ((27839 / 18723) : ℂ) * ζ ^ 6 - ((14839 / 18723) : ℂ) * ζ ^ 8 + ((2989 / 12482) : ℂ) * ζ ^ 9 + ((5523 / 6241) : ℂ) * ζ ^ 11 - ((14839 / 18723) : ℂ) * ζ ^ 12 + ((1840 / 18723) : ℂ) * ζ ^ 13 + ((5144 / 6241) : ℂ) * ζ ^ 15 + ((1840 / 18723) : ℂ) * ζ ^ 17 - ((171 / 6241) : ℂ) * ζ ^ 18 + ((27851 / 37446) : ℂ) * ζ ^ 21 + ((28352 / 18723) : ℂ) * ζ ^ 22 - ((2231 / 12482) : ℂ) * ζ ^ 25 - ((27851 / 37446) : ℂ) * ζ ^ 27 + ((14839 / 18723) : ℂ) * ζ ^ 28 - ((1840 / 18723) : ℂ) * ζ ^ 29 - ((27839 / 37446) : ℂ) * ζ ^ 30 - ((5523 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep04CoefficientIdentity07 :
    row18_reducedY00_combinationStep04Coefficient07 =
      row18_reducedY00_combinationStep03Coefficient07 +
        row18_reducedY00_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep04Coefficient07 row18_reducedY00_combinationStep03Coefficient07 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep04Coefficient08 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep04CoefficientIdentity08 :
    row18_reducedY00_combinationStep04Coefficient08 =
      row18_reducedY00_combinationStep03Coefficient08 +
        row18_reducedY00_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep04Coefficient08 row18_reducedY00_combinationStep03Coefficient08 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep04Coefficient09 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep04CoefficientIdentity09 :
    row18_reducedY00_combinationStep04Coefficient09 =
      row18_reducedY00_combinationStep03Coefficient09 +
        row18_reducedY00_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep04Coefficient09 row18_reducedY00_combinationStep03Coefficient09 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep04Coefficient10 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep04CoefficientIdentity10 :
    row18_reducedY00_combinationStep04Coefficient10 =
      row18_reducedY00_combinationStep03Coefficient10 +
        row18_reducedY00_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep04Coefficient10 row18_reducedY00_combinationStep03Coefficient10 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep04Coefficient11 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep04CoefficientIdentity11 :
    row18_reducedY00_combinationStep04Coefficient11 =
      row18_reducedY00_combinationStep03Coefficient11 +
        row18_reducedY00_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep04Coefficient11 row18_reducedY00_combinationStep03Coefficient11 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep04Coefficient12 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep04CoefficientIdentity12 :
    row18_reducedY00_combinationStep04Coefficient12 =
      row18_reducedY00_combinationStep03Coefficient12 +
        row18_reducedY00_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep04Coefficient12 row18_reducedY00_combinationStep03Coefficient12 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep04Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep04CoefficientIdentity13 :
    row18_reducedY00_combinationStep04Coefficient13 =
      row18_reducedY00_combinationStep03Coefficient13 +
        row18_reducedY00_combinationStep04Multiplier *
          (-((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 + ((73 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((8 / 79) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((105 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((73 / 316) : ℂ) * ζ ^ 22 - ((15 / 158) : ℂ) * ζ ^ 25 - ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep04Coefficient13 row18_reducedY00_combinationStep03Coefficient13 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 (-((3276 / 6241) : ℂ) - ((625 / 12482) : ℂ) * ζ ^ 1 + ((689 / 6241) : ℂ) * ζ ^ 2 - ((3167 / 12482) : ℂ) * ζ ^ 3 - ((1285 / 12482) : ℂ) * ζ ^ 4 - ((117 / 6241) : ℂ) * ζ ^ 5 + ((5201 / 12482) : ℂ) * ζ ^ 6 + ((3018 / 6241) : ℂ) * ζ ^ 7 + ((4811 / 12482) : ℂ) * ζ ^ 8 - ((784 / 6241) : ℂ) * ζ ^ 9 - ((8487 / 6241) : ℂ) * ζ ^ 10 - ((4803 / 12482) : ℂ) * ζ ^ 11 + ((6691 / 12482) : ℂ) * ζ ^ 12 + ((178 / 6241) : ℂ) * ζ ^ 13 + ((6775 / 6241) : ℂ) * ζ ^ 14 - ((4021 / 12482) : ℂ) * ζ ^ 15 - ((19101 / 12482) : ℂ) * ζ ^ 16 - ((4973 / 12482) : ℂ) * ζ ^ 17 - ((4376 / 6241) : ℂ) * ζ ^ 18 + ((66 / 6241) : ℂ) * ζ ^ 19 + ((8447 / 12482) : ℂ) * ζ ^ 20 + ((551 / 6241) : ℂ) * ζ ^ 21 - ((119 / 6241) : ℂ) * ζ ^ 22 + ((550 / 6241) : ℂ) * ζ ^ 23 - ((2929 / 12482) : ℂ) * ζ ^ 24 + ((445 / 12482) : ℂ) * ζ ^ 25 + ((1398 / 6241) : ℂ) * ζ ^ 26 + ((1144 / 6241) : ℂ) * ζ ^ 27 + ((2973 / 12482) : ℂ) * ζ ^ 28 + ((1083 / 6241) : ℂ) * ζ ^ 29 + ((329 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep04Coefficient14 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep04CoefficientIdentity14 :
    row18_reducedY00_combinationStep04Coefficient14 =
      row18_reducedY00_combinationStep03Coefficient14 +
        row18_reducedY00_combinationStep04Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep04Coefficient14 row18_reducedY00_combinationStep03Coefficient14 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep04Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep04CoefficientIdentity15 :
    row18_reducedY00_combinationStep04Coefficient15 =
      row18_reducedY00_combinationStep03Coefficient15 +
        row18_reducedY00_combinationStep04Multiplier *
          (((19 / 158) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 + ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 + ((21 / 79) : ℂ) * ζ ^ 9 - ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 + ((6 / 79) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 + ((13 / 316) : ℂ) * ζ ^ 25 - ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 + ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep04Coefficient15 row18_reducedY00_combinationStep03Coefficient15 row18_reducedY00_combinationStep04Multiplier
  close_cyclotomic_row18 (((2474 / 6241) : ℂ) - ((6163 / 12482) : ℂ) * ζ ^ 1 - ((3250 / 6241) : ℂ) * ζ ^ 2 + ((1919 / 6241) : ℂ) * ζ ^ 3 - ((7587 / 12482) : ℂ) * ζ ^ 4 + ((3018 / 6241) : ℂ) * ζ ^ 5 + ((1520 / 6241) : ℂ) * ζ ^ 6 - ((3459 / 6241) : ℂ) * ζ ^ 7 + ((315 / 12482) : ℂ) * ζ ^ 8 + ((1635 / 12482) : ℂ) * ζ ^ 9 - ((2433 / 12482) : ℂ) * ζ ^ 10 - ((203 / 12482) : ℂ) * ζ ^ 11 + ((1748 / 6241) : ℂ) * ζ ^ 12 - ((1205 / 6241) : ℂ) * ζ ^ 13 + ((837 / 12482) : ℂ) * ζ ^ 14 - ((894 / 6241) : ℂ) * ζ ^ 15 - ((247 / 12482) : ℂ) * ζ ^ 16 - ((163 / 6241) : ℂ) * ζ ^ 17 - ((1985 / 12482) : ℂ) * ζ ^ 18 + ((1125 / 6241) : ℂ) * ζ ^ 19 - ((871 / 12482) : ℂ) * ζ ^ 20 - ((706 / 6241) : ℂ) * ζ ^ 21 + ((3236 / 6241) : ℂ) * ζ ^ 22 - ((2 / 79) : ℂ) * ζ ^ 23 + ((710 / 6241) : ℂ) * ζ ^ 24 - ((240 / 6241) : ℂ) * ζ ^ 25 - ((10525 / 12482) : ℂ) * ζ ^ 26 + ((162 / 6241) : ℂ) * ζ ^ 27 + ((3337 / 12482) : ℂ) * ζ ^ 28 + ((741 / 12482) : ℂ) * ζ ^ 29 - ((705 / 12482) : ℂ) * ζ ^ 30)

private theorem row18_reducedY00_combinationStep04
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY00_combinationStep04Coefficient00) * Y 0 0
      + (row18_reducedY00_combinationStep04Coefficient01) * Y 0 1
      + (row18_reducedY00_combinationStep04Coefficient02) * Y 1 0
      + (row18_reducedY00_combinationStep04Coefficient03) * Y 1 1
      + (row18_reducedY00_combinationStep04Coefficient04) * Y 2 2
      + (row18_reducedY00_combinationStep04Coefficient05) * Y 2 3
      + (row18_reducedY00_combinationStep04Coefficient06) * Y 3 2
      + (row18_reducedY00_combinationStep04Coefficient07) * Y 3 3
      + (row18_reducedY00_combinationStep04Coefficient08) * Y 4 4
      + (row18_reducedY00_combinationStep04Coefficient09) * Y 4 5
      + (row18_reducedY00_combinationStep04Coefficient10) * Y 5 4
      + (row18_reducedY00_combinationStep04Coefficient11) * Y 5 5
      + (row18_reducedY00_combinationStep04Coefficient12) * Y 6 6
      + (row18_reducedY00_combinationStep04Coefficient13) * Y 6 7
      + (row18_reducedY00_combinationStep04Coefficient14) * Y 7 6
      + (row18_reducedY00_combinationStep04Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY00_combinationStep03 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation07
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY00_combinationStep04CoefficientIdentity00,
      row18_reducedY00_combinationStep04CoefficientIdentity01,
      row18_reducedY00_combinationStep04CoefficientIdentity02,
      row18_reducedY00_combinationStep04CoefficientIdentity03,
      row18_reducedY00_combinationStep04CoefficientIdentity04,
      row18_reducedY00_combinationStep04CoefficientIdentity05,
      row18_reducedY00_combinationStep04CoefficientIdentity06,
      row18_reducedY00_combinationStep04CoefficientIdentity07,
      row18_reducedY00_combinationStep04CoefficientIdentity08,
      row18_reducedY00_combinationStep04CoefficientIdentity09,
      row18_reducedY00_combinationStep04CoefficientIdentity10,
      row18_reducedY00_combinationStep04CoefficientIdentity11,
      row18_reducedY00_combinationStep04CoefficientIdentity12,
      row18_reducedY00_combinationStep04CoefficientIdentity13,
      row18_reducedY00_combinationStep04CoefficientIdentity14,
      row18_reducedY00_combinationStep04CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY00_combinationStep04Multiplier * equation

private def row18_reducedY00_combinationStep05Multiplier : ℂ :=
  (-((207446 / 93615) : ℂ) - ((306412 / 93615) : ℂ) * ζ ^ 1 + ((460102 / 93615) : ℂ) * ζ ^ 2 + ((1542 / 6241) : ℂ) * ζ ^ 3 - ((572216 / 93615) : ℂ) * ζ ^ 5 + ((54428 / 93615) : ℂ) * ζ ^ 6 + ((137916 / 31205) : ℂ) * ζ ^ 8 + ((6768 / 31205) : ℂ) * ζ ^ 9 - ((15570 / 6241) : ℂ) * ζ ^ 11 + ((405674 / 93615) : ℂ) * ζ ^ 12 + ((306412 / 93615) : ℂ) * ζ ^ 13 - ((1542 / 6241) : ℂ) * ζ ^ 15 + ((306412 / 93615) : ℂ) * ζ ^ 17 - ((252656 / 93615) : ℂ) * ζ ^ 18 + ((265804 / 93615) : ℂ) * ζ ^ 21 - ((460102 / 93615) : ℂ) * ζ ^ 22 - ((460102 / 93615) : ℂ) * ζ ^ 24 + ((265804 / 93615) : ℂ) * ζ ^ 25 + ((15570 / 6241) : ℂ) * ζ ^ 27 - ((137916 / 31205) : ℂ) * ζ ^ 28 - ((306412 / 93615) : ℂ) * ζ ^ 29 + ((46354 / 93615) : ℂ) * ζ ^ 30 + ((15570 / 6241) : ℂ) * ζ ^ 31)

private def row18_reducedY00_combinationStep05Coefficient00 : ℂ :=
  (((121 / 79) : ℂ) - ((342 / 395) : ℂ) * ζ ^ 1 + ((1961 / 790) : ℂ) * ζ ^ 2 + ((323 / 395) : ℂ) * ζ ^ 3 + ((289 / 395) : ℂ) * ζ ^ 5 + ((1332 / 395) : ℂ) * ζ ^ 6 + ((387 / 158) : ℂ) * ζ ^ 8 + ((1024 / 395) : ℂ) * ζ ^ 9 + ((701 / 395) : ℂ) * ζ ^ 11 + ((387 / 158) : ℂ) * ζ ^ 12 + ((342 / 395) : ℂ) * ζ ^ 13 + ((308 / 395) : ℂ) * ζ ^ 15 + ((342 / 395) : ℂ) * ζ ^ 17 - ((703 / 790) : ℂ) * ζ ^ 18 + ((19 / 395) : ℂ) * ζ ^ 21 - ((1961 / 790) : ℂ) * ζ ^ 22 - ((631 / 395) : ℂ) * ζ ^ 25 - ((19 / 395) : ℂ) * ζ ^ 27 - ((387 / 158) : ℂ) * ζ ^ 28 - ((342 / 395) : ℂ) * ζ ^ 29 + ((666 / 395) : ℂ) * ζ ^ 30 - ((701 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep05CoefficientIdentity00 :
    row18_reducedY00_combinationStep05Coefficient00 =
      row18_reducedY00_combinationStep04Coefficient00 +
        row18_reducedY00_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep05Coefficient00 row18_reducedY00_combinationStep04Coefficient00 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep05Coefficient01 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep05CoefficientIdentity01 :
    row18_reducedY00_combinationStep05Coefficient01 =
      row18_reducedY00_combinationStep04Coefficient01 +
        row18_reducedY00_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep05Coefficient01 row18_reducedY00_combinationStep04Coefficient01 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep05Coefficient02 : ℂ :=
  (-((46246 / 93615) : ℂ) - ((224723 / 187230) : ℂ) * ζ ^ 1 + ((420589 / 187230) : ℂ) * ζ ^ 2 + ((83083 / 37446) : ℂ) * ζ ^ 3 - ((526807 / 93615) : ℂ) * ζ ^ 5 + ((425221 / 187230) : ℂ) * ζ ^ 6 + ((151988 / 93615) : ℂ) * ζ ^ 8 - ((151042 / 93615) : ℂ) * ζ ^ 9 - ((130318 / 18723) : ℂ) * ζ ^ 11 - ((772 / 31205) : ℂ) * ζ ^ 12 + ((224723 / 187230) : ℂ) * ζ ^ 13 - ((83083 / 37446) : ℂ) * ζ ^ 15 + ((224723 / 187230) : ℂ) * ζ ^ 17 - ((328097 / 187230) : ℂ) * ζ ^ 18 + ((276297 / 62410) : ℂ) * ζ ^ 21 - ((420589 / 187230) : ℂ) * ζ ^ 22 - ((420589 / 187230) : ℂ) * ζ ^ 24 + ((276297 / 62410) : ℂ) * ζ ^ 25 + ((130318 / 18723) : ℂ) * ζ ^ 27 - ((151988 / 93615) : ℂ) * ζ ^ 28 - ((224723 / 187230) : ℂ) * ζ ^ 29 + ((38871 / 62410) : ℂ) * ζ ^ 30 + ((130318 / 18723) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep05CoefficientIdentity02 :
    row18_reducedY00_combinationStep05Coefficient02 =
      row18_reducedY00_combinationStep04Coefficient02 +
        row18_reducedY00_combinationStep05Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((19 / 316) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((3 / 79) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((8 / 79) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 - ((13 / 316) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((15 / 158) : ℂ) * ζ ^ 25 + ((13 / 316) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep05Coefficient02 row18_reducedY00_combinationStep04Coefficient02 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 (-((2852501 / 14791170) : ℂ) - ((3306483 / 4930390) : ℂ) * ζ ^ 1 + ((9859783 / 7395585) : ℂ) * ζ ^ 2 - ((411247 / 2958234) : ℂ) * ζ ^ 3 - ((16881031 / 14791170) : ℂ) * ζ ^ 4 + ((2410651 / 2958234) : ℂ) * ζ ^ 5 - ((5752708 / 7395585) : ℂ) * ζ ^ 6 + ((13603196 / 7395585) : ℂ) * ζ ^ 7 - ((1666702 / 7395585) : ℂ) * ζ ^ 8 - ((339289 / 986078) : ℂ) * ζ ^ 9 + ((9359107 / 14791170) : ℂ) * ζ ^ 10 - ((7345822 / 7395585) : ℂ) * ζ ^ 11 + ((26594 / 93615) : ℂ) * ζ ^ 12 - ((5280893 / 14791170) : ℂ) * ζ ^ 13 + ((1719101 / 14791170) : ℂ) * ζ ^ 14 + ((17962351 / 14791170) : ℂ) * ζ ^ 15 - ((1838661 / 4930390) : ℂ) * ζ ^ 16 - ((841753 / 7395585) : ℂ) * ζ ^ 17 - ((19003 / 1479117) : ℂ) * ζ ^ 18 - ((2303377 / 2465195) : ℂ) * ζ ^ 19 + ((2049223 / 4930390) : ℂ) * ζ ^ 20 - ((9746609 / 14791170) : ℂ) * ζ ^ 21 - ((53393 / 2958234) : ℂ) * ζ ^ 22 - ((476747 / 986078) : ℂ) * ζ ^ 23 + ((6564253 / 7395585) : ℂ) * ζ ^ 24 + ((3063419 / 14791170) : ℂ) * ζ ^ 25 + ((1165799 / 7395585) : ℂ) * ζ ^ 26 - ((712853 / 2465195) : ℂ) * ζ ^ 27 - ((410397 / 4930390) : ℂ) * ζ ^ 28 - ((771961 / 7395585) : ℂ) * ζ ^ 29 + ((54495 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep05Coefficient03 : ℂ :=
  (-((31643 / 37446) : ℂ) - ((3848 / 18723) : ℂ) * ζ ^ 1 + ((52201 / 37446) : ℂ) * ζ ^ 2 + ((7070 / 6241) : ℂ) * ζ ^ 3 + ((745 / 18723) : ℂ) * ζ ^ 5 + ((28313 / 18723) : ℂ) * ζ ^ 6 + ((30863 / 37446) : ℂ) * ζ ^ 8 + ((2258 / 6241) : ℂ) * ζ ^ 9 - ((4812 / 6241) : ℂ) * ζ ^ 11 + ((30863 / 37446) : ℂ) * ζ ^ 12 + ((3848 / 18723) : ℂ) * ζ ^ 13 - ((5539 / 6241) : ℂ) * ζ ^ 15 + ((3848 / 18723) : ℂ) * ζ ^ 17 - ((1475 / 12482) : ℂ) * ζ ^ 18 - ((17362 / 18723) : ℂ) * ζ ^ 21 - ((52201 / 37446) : ℂ) * ζ ^ 22 - ((1531 / 6241) : ℂ) * ζ ^ 25 + ((17362 / 18723) : ℂ) * ζ ^ 27 - ((30863 / 37446) : ℂ) * ζ ^ 28 - ((3848 / 18723) : ℂ) * ζ ^ 29 + ((28313 / 37446) : ℂ) * ζ ^ 30 + ((4812 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep05CoefficientIdentity03 :
    row18_reducedY00_combinationStep05Coefficient03 =
      row18_reducedY00_combinationStep04Coefficient03 +
        row18_reducedY00_combinationStep05Multiplier *
          (((69 / 316) : ℂ) - ((85 / 316) : ℂ) * ζ ^ 1 + ((9 / 316) : ℂ) * ζ ^ 2 + ((13 / 158) : ℂ) * ζ ^ 3 - ((85 / 316) : ℂ) * ζ ^ 5 + ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((13 / 316) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((85 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((85 / 316) : ℂ) * ζ ^ 17 + ((41 / 316) : ℂ) * ζ ^ 18 + ((45 / 79) : ℂ) * ζ ^ 21 - ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 + ((2 / 79) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((85 / 316) : ℂ) * ζ ^ 29 + ((27 / 158) : ℂ) * ζ ^ 30 + ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep05Coefficient03 row18_reducedY00_combinationStep04Coefficient03 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 (-((23845637 / 14791170) : ℂ) + ((8545261 / 14791170) : ℂ) * ζ ^ 1 + ((15461957 / 14791170) : ℂ) * ζ ^ 2 - ((11685391 / 7395585) : ℂ) * ζ ^ 3 + ((4189943 / 2958234) : ℂ) * ζ ^ 4 - ((9077767 / 14791170) : ℂ) * ζ ^ 5 + ((1979645 / 2958234) : ℂ) * ζ ^ 6 - ((13021783 / 14791170) : ℂ) * ζ ^ 7 + ((738716 / 2465195) : ℂ) * ζ ^ 8 - ((2830133 / 14791170) : ℂ) * ζ ^ 9 - ((15546587 / 14791170) : ℂ) * ζ ^ 10 + ((438459 / 986078) : ℂ) * ζ ^ 11 - ((542561 / 2465195) : ℂ) * ζ ^ 12 - ((5021786 / 7395585) : ℂ) * ζ ^ 13 - ((6543641 / 7395585) : ℂ) * ζ ^ 14 - ((5298361 / 14791170) : ℂ) * ζ ^ 15 + ((1315133 / 2958234) : ℂ) * ζ ^ 16 - ((6323549 / 14791170) : ℂ) * ζ ^ 17 - ((14408653 / 7395585) : ℂ) * ζ ^ 18 + ((2995553 / 2958234) : ℂ) * ζ ^ 19 - ((1099261 / 986078) : ℂ) * ζ ^ 20 + ((354867 / 2465195) : ℂ) * ζ ^ 21 - ((8206827 / 4930390) : ℂ) * ζ ^ 22 + ((9786603 / 4930390) : ℂ) * ζ ^ 23 - ((2482329 / 2465195) : ℂ) * ζ ^ 24 + ((5518337 / 14791170) : ℂ) * ζ ^ 25 + ((459332 / 1479117) : ℂ) * ζ ^ 26 - ((3824081 / 14791170) : ℂ) * ζ ^ 27 - ((2133199 / 2958234) : ℂ) * ζ ^ 28 + ((6607151 / 14791170) : ℂ) * ζ ^ 29 + ((101205 / 986078) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep05Coefficient04 : ℂ :=
  (-((42 / 79) : ℂ) + ((342 / 395) : ℂ) * ζ ^ 1 - ((1961 / 790) : ℂ) * ζ ^ 2 - ((323 / 395) : ℂ) * ζ ^ 3 - ((289 / 395) : ℂ) * ζ ^ 5 - ((1332 / 395) : ℂ) * ζ ^ 6 - ((387 / 158) : ℂ) * ζ ^ 8 - ((1024 / 395) : ℂ) * ζ ^ 9 - ((701 / 395) : ℂ) * ζ ^ 11 - ((387 / 158) : ℂ) * ζ ^ 12 - ((342 / 395) : ℂ) * ζ ^ 13 - ((308 / 395) : ℂ) * ζ ^ 15 - ((342 / 395) : ℂ) * ζ ^ 17 + ((703 / 790) : ℂ) * ζ ^ 18 - ((19 / 395) : ℂ) * ζ ^ 21 + ((1961 / 790) : ℂ) * ζ ^ 22 + ((631 / 395) : ℂ) * ζ ^ 25 + ((19 / 395) : ℂ) * ζ ^ 27 + ((387 / 158) : ℂ) * ζ ^ 28 + ((342 / 395) : ℂ) * ζ ^ 29 - ((666 / 395) : ℂ) * ζ ^ 30 + ((701 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep05CoefficientIdentity04 :
    row18_reducedY00_combinationStep05Coefficient04 =
      row18_reducedY00_combinationStep04Coefficient04 +
        row18_reducedY00_combinationStep05Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep05Coefficient04 row18_reducedY00_combinationStep04Coefficient04 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 (((23845637 / 14791170) : ℂ) - ((8545261 / 14791170) : ℂ) * ζ ^ 1 - ((15461957 / 14791170) : ℂ) * ζ ^ 2 + ((11685391 / 7395585) : ℂ) * ζ ^ 3 - ((4189943 / 2958234) : ℂ) * ζ ^ 4 + ((9077767 / 14791170) : ℂ) * ζ ^ 5 - ((1979645 / 2958234) : ℂ) * ζ ^ 6 + ((13021783 / 14791170) : ℂ) * ζ ^ 7 - ((738716 / 2465195) : ℂ) * ζ ^ 8 + ((2830133 / 14791170) : ℂ) * ζ ^ 9 + ((15546587 / 14791170) : ℂ) * ζ ^ 10 - ((438459 / 986078) : ℂ) * ζ ^ 11 + ((542561 / 2465195) : ℂ) * ζ ^ 12 + ((5021786 / 7395585) : ℂ) * ζ ^ 13 + ((6543641 / 7395585) : ℂ) * ζ ^ 14 + ((5298361 / 14791170) : ℂ) * ζ ^ 15 - ((1315133 / 2958234) : ℂ) * ζ ^ 16 + ((6323549 / 14791170) : ℂ) * ζ ^ 17 + ((14408653 / 7395585) : ℂ) * ζ ^ 18 - ((2995553 / 2958234) : ℂ) * ζ ^ 19 + ((1099261 / 986078) : ℂ) * ζ ^ 20 - ((354867 / 2465195) : ℂ) * ζ ^ 21 + ((8206827 / 4930390) : ℂ) * ζ ^ 22 - ((9786603 / 4930390) : ℂ) * ζ ^ 23 + ((2482329 / 2465195) : ℂ) * ζ ^ 24 - ((5518337 / 14791170) : ℂ) * ζ ^ 25 - ((459332 / 1479117) : ℂ) * ζ ^ 26 + ((3824081 / 14791170) : ℂ) * ζ ^ 27 + ((2133199 / 2958234) : ℂ) * ζ ^ 28 - ((6607151 / 14791170) : ℂ) * ζ ^ 29 - ((101205 / 986078) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep05Coefficient05 : ℂ :=
  (-((20987 / 37446) : ℂ) + ((6289 / 18723) : ℂ) * ζ ^ 1 - ((67339 / 37446) : ℂ) * ζ ^ 2 - ((6111 / 6241) : ℂ) * ζ ^ 5 - ((23176 / 18723) : ℂ) * ζ ^ 6 - ((23176 / 18723) : ℂ) * ζ ^ 8 - ((6111 / 6241) : ℂ) * ζ ^ 9 - ((28049 / 12482) : ℂ) * ζ ^ 11 - ((22372 / 18723) : ℂ) * ζ ^ 12 - ((6289 / 18723) : ℂ) * ζ ^ 13 - ((27113 / 18723) : ℂ) * ζ ^ 15 - ((6289 / 18723) : ℂ) * ζ ^ 17 + ((10615 / 12482) : ℂ) * ζ ^ 18 + ((6022 / 18723) : ℂ) * ζ ^ 21 + ((67339 / 37446) : ℂ) * ζ ^ 22 + ((14507 / 37446) : ℂ) * ζ ^ 24 + ((24622 / 18723) : ℂ) * ζ ^ 25 + ((27113 / 18723) : ℂ) * ζ ^ 27 + ((23176 / 18723) : ℂ) * ζ ^ 28 + ((6289 / 18723) : ℂ) * ζ ^ 29 - ((268 / 6241) : ℂ) * ζ ^ 30 + ((28049 / 12482) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep05CoefficientIdentity05 :
    row18_reducedY00_combinationStep05Coefficient05 =
      row18_reducedY00_combinationStep04Coefficient05 +
        row18_reducedY00_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep05Coefficient05 row18_reducedY00_combinationStep04Coefficient05 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep05Coefficient06 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep05CoefficientIdentity06 :
    row18_reducedY00_combinationStep05Coefficient06 =
      row18_reducedY00_combinationStep04Coefficient06 +
        row18_reducedY00_combinationStep05Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep05Coefficient06 row18_reducedY00_combinationStep04Coefficient06 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 (-((1815494 / 2465195) : ℂ) + ((6136769 / 7395585) : ℂ) * ζ ^ 1 + ((2710117 / 14791170) : ℂ) * ζ ^ 2 - ((7391464 / 7395585) : ℂ) * ζ ^ 3 - ((17920351 / 7395585) : ℂ) * ζ ^ 4 + ((11518757 / 7395585) : ℂ) * ζ ^ 5 + ((18695702 / 7395585) : ℂ) * ζ ^ 6 + ((5552804 / 2465195) : ℂ) * ζ ^ 7 - ((942137 / 7395585) : ℂ) * ζ ^ 8 - ((4277312 / 1479117) : ℂ) * ζ ^ 9 - ((10954234 / 7395585) : ℂ) * ζ ^ 10 - ((15632419 / 7395585) : ℂ) * ζ ^ 11 + ((1957978 / 7395585) : ℂ) * ζ ^ 12 + ((11689327 / 7395585) : ℂ) * ζ ^ 13 + ((3199399 / 4930390) : ℂ) * ζ ^ 14 + ((1348771 / 2465195) : ℂ) * ζ ^ 15 - ((2610352 / 1479117) : ℂ) * ζ ^ 16 - ((20831129 / 4930390) : ℂ) * ζ ^ 17 - ((5125132 / 2465195) : ℂ) * ζ ^ 18 - ((1791629 / 2958234) : ℂ) * ζ ^ 19 + ((80212499 / 14791170) : ℂ) * ζ ^ 20 + ((9648686 / 7395585) : ℂ) * ζ ^ 21 - ((3873093 / 2465195) : ℂ) * ζ ^ 22 - ((6523501 / 2465195) : ℂ) * ζ ^ 23 - ((20714117 / 14791170) : ℂ) * ζ ^ 24 + ((2897494 / 2465195) : ℂ) * ζ ^ 25 + ((4844574 / 2465195) : ℂ) * ζ ^ 26 + ((2249009 / 4930390) : ℂ) * ζ ^ 27 - ((584531 / 2958234) : ℂ) * ζ ^ 28 - ((1725778 / 7395585) : ℂ) * ζ ^ 29 - ((108990 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep05Coefficient07 : ℂ :=
  (((9839 / 37446) : ℂ) - ((1840 / 18723) : ℂ) * ζ ^ 1 - ((28352 / 18723) : ℂ) * ζ ^ 2 - ((8057 / 12482) : ℂ) * ζ ^ 3 + ((3013 / 37446) : ℂ) * ζ ^ 5 - ((27839 / 18723) : ℂ) * ζ ^ 6 - ((14839 / 18723) : ℂ) * ζ ^ 8 + ((2989 / 12482) : ℂ) * ζ ^ 9 + ((5523 / 6241) : ℂ) * ζ ^ 11 - ((14839 / 18723) : ℂ) * ζ ^ 12 + ((1840 / 18723) : ℂ) * ζ ^ 13 + ((5144 / 6241) : ℂ) * ζ ^ 15 + ((1840 / 18723) : ℂ) * ζ ^ 17 - ((171 / 6241) : ℂ) * ζ ^ 18 + ((27851 / 37446) : ℂ) * ζ ^ 21 + ((28352 / 18723) : ℂ) * ζ ^ 22 - ((2231 / 12482) : ℂ) * ζ ^ 25 - ((27851 / 37446) : ℂ) * ζ ^ 27 + ((14839 / 18723) : ℂ) * ζ ^ 28 - ((1840 / 18723) : ℂ) * ζ ^ 29 - ((27839 / 37446) : ℂ) * ζ ^ 30 - ((5523 / 6241) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep05CoefficientIdentity07 :
    row18_reducedY00_combinationStep05Coefficient07 =
      row18_reducedY00_combinationStep04Coefficient07 +
        row18_reducedY00_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep05Coefficient07 row18_reducedY00_combinationStep04Coefficient07 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep05Coefficient08 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep05CoefficientIdentity08 :
    row18_reducedY00_combinationStep05Coefficient08 =
      row18_reducedY00_combinationStep04Coefficient08 +
        row18_reducedY00_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep05Coefficient08 row18_reducedY00_combinationStep04Coefficient08 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep05Coefficient09 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep05CoefficientIdentity09 :
    row18_reducedY00_combinationStep05Coefficient09 =
      row18_reducedY00_combinationStep04Coefficient09 +
        row18_reducedY00_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep05Coefficient09 row18_reducedY00_combinationStep04Coefficient09 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep05Coefficient10 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep05CoefficientIdentity10 :
    row18_reducedY00_combinationStep05Coefficient10 =
      row18_reducedY00_combinationStep04Coefficient10 +
        row18_reducedY00_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep05Coefficient10 row18_reducedY00_combinationStep04Coefficient10 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep05Coefficient11 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep05CoefficientIdentity11 :
    row18_reducedY00_combinationStep05Coefficient11 =
      row18_reducedY00_combinationStep04Coefficient11 +
        row18_reducedY00_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep05Coefficient11 row18_reducedY00_combinationStep04Coefficient11 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep05Coefficient12 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep05CoefficientIdentity12 :
    row18_reducedY00_combinationStep05Coefficient12 =
      row18_reducedY00_combinationStep04Coefficient12 +
        row18_reducedY00_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep05Coefficient12 row18_reducedY00_combinationStep04Coefficient12 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep05Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep05CoefficientIdentity13 :
    row18_reducedY00_combinationStep05Coefficient13 =
      row18_reducedY00_combinationStep04Coefficient13 +
        row18_reducedY00_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep05Coefficient13 row18_reducedY00_combinationStep04Coefficient13 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep05Coefficient14 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep05CoefficientIdentity14 :
    row18_reducedY00_combinationStep05Coefficient14 =
      row18_reducedY00_combinationStep04Coefficient14 +
        row18_reducedY00_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep05Coefficient14 row18_reducedY00_combinationStep04Coefficient14 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep05Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep05CoefficientIdentity15 :
    row18_reducedY00_combinationStep05Coefficient15 =
      row18_reducedY00_combinationStep04Coefficient15 +
        row18_reducedY00_combinationStep05Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep05Coefficient15 row18_reducedY00_combinationStep04Coefficient15 row18_reducedY00_combinationStep05Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY00_combinationStep05
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY00_combinationStep05Coefficient00) * Y 0 0
      + (row18_reducedY00_combinationStep05Coefficient01) * Y 0 1
      + (row18_reducedY00_combinationStep05Coefficient02) * Y 1 0
      + (row18_reducedY00_combinationStep05Coefficient03) * Y 1 1
      + (row18_reducedY00_combinationStep05Coefficient04) * Y 2 2
      + (row18_reducedY00_combinationStep05Coefficient05) * Y 2 3
      + (row18_reducedY00_combinationStep05Coefficient06) * Y 3 2
      + (row18_reducedY00_combinationStep05Coefficient07) * Y 3 3
      + (row18_reducedY00_combinationStep05Coefficient08) * Y 4 4
      + (row18_reducedY00_combinationStep05Coefficient09) * Y 4 5
      + (row18_reducedY00_combinationStep05Coefficient10) * Y 5 4
      + (row18_reducedY00_combinationStep05Coefficient11) * Y 5 5
      + (row18_reducedY00_combinationStep05Coefficient12) * Y 6 6
      + (row18_reducedY00_combinationStep05Coefficient13) * Y 6 7
      + (row18_reducedY00_combinationStep05Coefficient14) * Y 7 6
      + (row18_reducedY00_combinationStep05Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY00_combinationStep04 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation12
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY00_combinationStep05CoefficientIdentity00,
      row18_reducedY00_combinationStep05CoefficientIdentity01,
      row18_reducedY00_combinationStep05CoefficientIdentity02,
      row18_reducedY00_combinationStep05CoefficientIdentity03,
      row18_reducedY00_combinationStep05CoefficientIdentity04,
      row18_reducedY00_combinationStep05CoefficientIdentity05,
      row18_reducedY00_combinationStep05CoefficientIdentity06,
      row18_reducedY00_combinationStep05CoefficientIdentity07,
      row18_reducedY00_combinationStep05CoefficientIdentity08,
      row18_reducedY00_combinationStep05CoefficientIdentity09,
      row18_reducedY00_combinationStep05CoefficientIdentity10,
      row18_reducedY00_combinationStep05CoefficientIdentity11,
      row18_reducedY00_combinationStep05CoefficientIdentity12,
      row18_reducedY00_combinationStep05CoefficientIdentity13,
      row18_reducedY00_combinationStep05CoefficientIdentity14,
      row18_reducedY00_combinationStep05CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY00_combinationStep05Multiplier * equation

private def row18_reducedY00_combinationStep06Multiplier : ℂ :=
  (((16856 / 6241) : ℂ) + ((48314 / 18723) : ℂ) * ζ ^ 1 - ((122744 / 18723) : ℂ) * ζ ^ 2 - ((101200 / 18723) : ℂ) * ζ ^ 3 + ((168616 / 18723) : ℂ) * ζ ^ 5 - ((84454 / 18723) : ℂ) * ζ ^ 8 + ((18164 / 18723) : ℂ) * ζ ^ 9 + ((83036 / 18723) : ℂ) * ζ ^ 11 - ((16682 / 18723) : ℂ) * ζ ^ 12 - ((48314 / 18723) : ℂ) * ζ ^ 13 - ((19102 / 18723) : ℂ) * ζ ^ 15 - ((48314 / 18723) : ℂ) * ζ ^ 17 + ((122744 / 18723) : ℂ) * ζ ^ 18 - ((49838 / 6241) : ℂ) * ζ ^ 21 + ((122744 / 18723) : ℂ) * ζ ^ 22 + ((33712 / 6241) : ℂ) * ζ ^ 24 - ((120302 / 18723) : ℂ) * ζ ^ 25 - ((49838 / 6241) : ℂ) * ζ ^ 27 + ((84454 / 18723) : ℂ) * ζ ^ 28 + ((48314 / 18723) : ℂ) * ζ ^ 29 + ((21012 / 6241) : ℂ) * ζ ^ 30 - ((83036 / 18723) : ℂ) * ζ ^ 31)

private def row18_reducedY00_combinationStep06Coefficient00 : ℂ :=
  (((121 / 79) : ℂ) - ((342 / 395) : ℂ) * ζ ^ 1 + ((1961 / 790) : ℂ) * ζ ^ 2 + ((323 / 395) : ℂ) * ζ ^ 3 + ((289 / 395) : ℂ) * ζ ^ 5 + ((1332 / 395) : ℂ) * ζ ^ 6 + ((387 / 158) : ℂ) * ζ ^ 8 + ((1024 / 395) : ℂ) * ζ ^ 9 + ((701 / 395) : ℂ) * ζ ^ 11 + ((387 / 158) : ℂ) * ζ ^ 12 + ((342 / 395) : ℂ) * ζ ^ 13 + ((308 / 395) : ℂ) * ζ ^ 15 + ((342 / 395) : ℂ) * ζ ^ 17 - ((703 / 790) : ℂ) * ζ ^ 18 + ((19 / 395) : ℂ) * ζ ^ 21 - ((1961 / 790) : ℂ) * ζ ^ 22 - ((631 / 395) : ℂ) * ζ ^ 25 - ((19 / 395) : ℂ) * ζ ^ 27 - ((387 / 158) : ℂ) * ζ ^ 28 - ((342 / 395) : ℂ) * ζ ^ 29 + ((666 / 395) : ℂ) * ζ ^ 30 - ((701 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep06CoefficientIdentity00 :
    row18_reducedY00_combinationStep06Coefficient00 =
      row18_reducedY00_combinationStep05Coefficient00 +
        row18_reducedY00_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep06Coefficient00 row18_reducedY00_combinationStep05Coefficient00 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep06Coefficient01 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep06CoefficientIdentity01 :
    row18_reducedY00_combinationStep06Coefficient01 =
      row18_reducedY00_combinationStep05Coefficient01 +
        row18_reducedY00_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep06Coefficient01 row18_reducedY00_combinationStep05Coefficient01 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep06Coefficient02 : ℂ :=
  (((452 / 395) : ℂ) - ((297 / 395) : ℂ) * ζ ^ 1 - ((1004 / 395) : ℂ) * ζ ^ 2 + ((37 / 79) : ℂ) * ζ ^ 3 - ((876 / 395) : ℂ) * ζ ^ 5 - ((446 / 395) : ℂ) * ζ ^ 6 - ((1076 / 395) : ℂ) * ζ ^ 8 - ((141 / 395) : ℂ) * ζ ^ 9 - ((120 / 79) : ℂ) * ζ ^ 11 - ((558 / 395) : ℂ) * ζ ^ 12 + ((297 / 395) : ℂ) * ζ ^ 13 - ((37 / 79) : ℂ) * ζ ^ 15 + ((297 / 395) : ℂ) * ζ ^ 17 + ((552 / 395) : ℂ) * ζ ^ 18 + ((579 / 395) : ℂ) * ζ ^ 21 + ((1004 / 395) : ℂ) * ζ ^ 22 + ((1004 / 395) : ℂ) * ζ ^ 24 + ((579 / 395) : ℂ) * ζ ^ 25 + ((120 / 79) : ℂ) * ζ ^ 27 + ((1076 / 395) : ℂ) * ζ ^ 28 - ((297 / 395) : ℂ) * ζ ^ 29 + ((72 / 395) : ℂ) * ζ ^ 30 + ((120 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep06CoefficientIdentity02 :
    row18_reducedY00_combinationStep06Coefficient02 =
      row18_reducedY00_combinationStep05Coefficient02 +
        row18_reducedY00_combinationStep06Multiplier *
          (((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 + ((17 / 158) : ℂ) * ζ ^ 6 - ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 + ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 + ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 + ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep06Coefficient02 row18_reducedY00_combinationStep05Coefficient02 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 (-((1942850 / 1479117) : ℂ) - ((737057 / 2958234) : ℂ) * ζ ^ 1 + ((5898205 / 1479117) : ℂ) * ζ ^ 2 + ((618667 / 493039) : ℂ) * ζ ^ 3 + ((1644320 / 1479117) : ℂ) * ζ ^ 4 - ((5229473 / 2958234) : ℂ) * ζ ^ 5 - ((759683 / 2958234) : ℂ) * ζ ^ 6 - ((981638 / 1479117) : ℂ) * ζ ^ 7 + ((1183069 / 1479117) : ℂ) * ζ ^ 8 - ((2862929 / 2958234) : ℂ) * ζ ^ 9 + ((884440 / 1479117) : ℂ) * ζ ^ 10 - ((9339 / 493039) : ℂ) * ζ ^ 11 + ((657859 / 986078) : ℂ) * ζ ^ 12 - ((637027 / 986078) : ℂ) * ζ ^ 13 - ((1120717 / 2958234) : ℂ) * ζ ^ 14 - ((2049082 / 1479117) : ℂ) * ζ ^ 15 + ((651739 / 2958234) : ℂ) * ζ ^ 16 + ((1470467 / 986078) : ℂ) * ζ ^ 17 + ((7975505 / 2958234) : ℂ) * ζ ^ 18 + ((244475 / 986078) : ℂ) * ζ ^ 19 - ((5796421 / 2958234) : ℂ) * ζ ^ 20 - ((2790241 / 986078) : ℂ) * ζ ^ 21 - ((2128439 / 2958234) : ℂ) * ζ ^ 22 + ((712425 / 986078) : ℂ) * ζ ^ 23 + ((6603073 / 2958234) : ℂ) * ζ ^ 24 + ((569554 / 493039) : ℂ) * ζ ^ 25 - ((302780 / 1479117) : ℂ) * ζ ^ 26 - ((4652237 / 2958234) : ℂ) * ζ ^ 27 - ((1335485 / 2958234) : ℂ) * ζ ^ 28 + ((253349 / 493039) : ℂ) * ζ ^ 29 + ((103795 / 493039) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep06Coefficient03 : ℂ :=
  (-((46 / 79) : ℂ) - ((24 / 79) : ℂ) * ζ ^ 1 - ((19 / 158) : ℂ) * ζ ^ 2 + ((77 / 158) : ℂ) * ζ ^ 3 + ((19 / 158) : ℂ) * ζ ^ 5 + ((2 / 79) : ℂ) * ζ ^ 6 + ((5 / 158) : ℂ) * ζ ^ 8 + ((95 / 158) : ℂ) * ζ ^ 9 + ((9 / 79) : ℂ) * ζ ^ 11 + ((5 / 158) : ℂ) * ζ ^ 12 + ((24 / 79) : ℂ) * ζ ^ 13 - ((5 / 79) : ℂ) * ζ ^ 15 + ((24 / 79) : ℂ) * ζ ^ 17 - ((23 / 158) : ℂ) * ζ ^ 18 - ((29 / 158) : ℂ) * ζ ^ 21 + ((19 / 158) : ℂ) * ζ ^ 22 - ((67 / 158) : ℂ) * ζ ^ 25 + ((29 / 158) : ℂ) * ζ ^ 27 - ((5 / 158) : ℂ) * ζ ^ 28 - ((24 / 79) : ℂ) * ζ ^ 29 + ((1 / 79) : ℂ) * ζ ^ 30 - ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep06CoefficientIdentity03 :
    row18_reducedY00_combinationStep06Coefficient03 =
      row18_reducedY00_combinationStep05Coefficient03 +
        row18_reducedY00_combinationStep06Multiplier *
          (((8 / 79) : ℂ) + ((57 / 316) : ℂ) * ζ ^ 1 + ((149 / 316) : ℂ) * ζ ^ 2 - ((77 / 316) : ℂ) * ζ ^ 3 + ((49 / 158) : ℂ) * ζ ^ 5 - ((3 / 79) : ℂ) * ζ ^ 8 + ((105 / 316) : ℂ) * ζ ^ 9 - ((7 / 79) : ℂ) * ζ ^ 11 - ((13 / 79) : ℂ) * ζ ^ 12 - ((57 / 316) : ℂ) * ζ ^ 13 + ((9 / 79) : ℂ) * ζ ^ 15 - ((57 / 316) : ℂ) * ζ ^ 17 - ((149 / 316) : ℂ) * ζ ^ 18 - ((67 / 158) : ℂ) * ζ ^ 21 - ((149 / 316) : ℂ) * ζ ^ 22 + ((16 / 79) : ℂ) * ζ ^ 24 - ((41 / 316) : ℂ) * ζ ^ 25 - ((67 / 158) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 + ((57 / 316) : ℂ) * ζ ^ 29 + ((6 / 79) : ℂ) * ζ ^ 30 + ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep06Coefficient03 row18_reducedY00_combinationStep05Coefficient03 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 (((31807 / 2958234) : ℂ) + ((15854 / 18723) : ℂ) * ζ ^ 1 + ((7659977 / 2958234) : ℂ) * ζ ^ 2 - ((777685 / 1479117) : ℂ) * ζ ^ 3 - ((6960262 / 1479117) : ℂ) * ζ ^ 4 - ((127009 / 986078) : ℂ) * ζ ^ 5 + ((7807727 / 2958234) : ℂ) * ζ ^ 6 + ((4051403 / 1479117) : ℂ) * ζ ^ 7 + ((1579949 / 1479117) : ℂ) * ζ ^ 8 - ((78745 / 2958234) : ℂ) * ζ ^ 9 - ((2046743 / 2958234) : ℂ) * ζ ^ 10 - ((11332247 / 2958234) : ℂ) * ζ ^ 11 - ((2229131 / 986078) : ℂ) * ζ ^ 12 + ((550900 / 1479117) : ℂ) * ζ ^ 13 + ((16863647 / 2958234) : ℂ) * ζ ^ 14 + ((11115481 / 2958234) : ℂ) * ζ ^ 15 + ((41537 / 1479117) : ℂ) * ζ ^ 16 - ((14859571 / 2958234) : ℂ) * ζ ^ 17 - ((2196284 / 493039) : ℂ) * ζ ^ 18 - ((4086283 / 2958234) : ℂ) * ζ ^ 19 + ((10360666 / 1479117) : ℂ) * ζ ^ 20 + ((2181122 / 493039) : ℂ) * ζ ^ 21 + ((1427845 / 2958234) : ℂ) * ζ ^ 22 - ((6796523 / 1479117) : ℂ) * ζ ^ 23 - ((6039755 / 2958234) : ℂ) * ζ ^ 24 - ((1068943 / 986078) : ℂ) * ζ ^ 25 + ((2467111 / 986078) : ℂ) * ζ ^ 26 + ((1530217 / 1479117) : ℂ) * ζ ^ 27 - ((466849 / 1479117) : ℂ) * ζ ^ 28 - ((18988 / 493039) : ℂ) * ζ ^ 29 - ((581252 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep06Coefficient04 : ℂ :=
  (-((42 / 79) : ℂ) + ((342 / 395) : ℂ) * ζ ^ 1 - ((1961 / 790) : ℂ) * ζ ^ 2 - ((323 / 395) : ℂ) * ζ ^ 3 - ((289 / 395) : ℂ) * ζ ^ 5 - ((1332 / 395) : ℂ) * ζ ^ 6 - ((387 / 158) : ℂ) * ζ ^ 8 - ((1024 / 395) : ℂ) * ζ ^ 9 - ((701 / 395) : ℂ) * ζ ^ 11 - ((387 / 158) : ℂ) * ζ ^ 12 - ((342 / 395) : ℂ) * ζ ^ 13 - ((308 / 395) : ℂ) * ζ ^ 15 - ((342 / 395) : ℂ) * ζ ^ 17 + ((703 / 790) : ℂ) * ζ ^ 18 - ((19 / 395) : ℂ) * ζ ^ 21 + ((1961 / 790) : ℂ) * ζ ^ 22 + ((631 / 395) : ℂ) * ζ ^ 25 + ((19 / 395) : ℂ) * ζ ^ 27 + ((387 / 158) : ℂ) * ζ ^ 28 + ((342 / 395) : ℂ) * ζ ^ 29 - ((666 / 395) : ℂ) * ζ ^ 30 + ((701 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep06CoefficientIdentity04 :
    row18_reducedY00_combinationStep06Coefficient04 =
      row18_reducedY00_combinationStep05Coefficient04 +
        row18_reducedY00_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep06Coefficient04 row18_reducedY00_combinationStep05Coefficient04 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep06Coefficient05 : ℂ :=
  (((18 / 79) : ℂ) + ((65 / 79) : ℂ) * ζ ^ 1 - ((165 / 158) : ℂ) * ζ ^ 2 - ((252 / 79) : ℂ) * ζ ^ 5 - ((201 / 158) : ℂ) * ζ ^ 6 - ((201 / 158) : ℂ) * ζ ^ 8 - ((252 / 79) : ℂ) * ζ ^ 9 - ((437 / 158) : ℂ) * ζ ^ 11 - ((62 / 79) : ℂ) * ζ ^ 12 - ((65 / 79) : ℂ) * ζ ^ 13 - ((135 / 79) : ℂ) * ζ ^ 15 - ((65 / 79) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 + ((187 / 158) : ℂ) * ζ ^ 21 + ((165 / 158) : ℂ) * ζ ^ 22 + ((177 / 158) : ℂ) * ζ ^ 24 + ((317 / 79) : ℂ) * ζ ^ 25 + ((135 / 79) : ℂ) * ζ ^ 27 + ((201 / 158) : ℂ) * ζ ^ 28 + ((65 / 79) : ℂ) * ζ ^ 29 - ((77 / 158) : ℂ) * ζ ^ 30 + ((437 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep06CoefficientIdentity05 :
    row18_reducedY00_combinationStep06Coefficient05 =
      row18_reducedY00_combinationStep05Coefficient05 +
        row18_reducedY00_combinationStep06Multiplier *
          (-((69 / 316) : ℂ) + ((85 / 316) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((13 / 158) : ℂ) * ζ ^ 3 + ((85 / 316) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 + ((39 / 158) : ℂ) * ζ ^ 8 - ((85 / 316) : ℂ) * ζ ^ 9 + ((13 / 316) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((85 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((85 / 316) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 - ((45 / 79) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 - ((119 / 316) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 27 - ((39 / 158) : ℂ) * ζ ^ 28 + ((85 / 316) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((13 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep06Coefficient05 row18_reducedY00_combinationStep05Coefficient05 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 (-((4076597 / 2958234) : ℂ) - ((958021 / 2958234) : ℂ) * ζ ^ 1 + ((1276657 / 986078) : ℂ) * ζ ^ 2 - ((2600017 / 2958234) : ℂ) * ζ ^ 3 - ((300137 / 2958234) : ℂ) * ζ ^ 4 + ((1960253 / 986078) : ℂ) * ζ ^ 5 + ((4834517 / 2958234) : ℂ) * ζ ^ 6 - ((1753207 / 986078) : ℂ) * ζ ^ 7 + ((1193825 / 986078) : ℂ) * ζ ^ 8 + ((62486 / 1479117) : ℂ) * ζ ^ 9 - ((1118895 / 986078) : ℂ) * ζ ^ 10 - ((32131 / 2958234) : ℂ) * ζ ^ 11 + ((109544 / 1479117) : ℂ) * ζ ^ 12 + ((780521 / 1479117) : ℂ) * ζ ^ 13 - ((3155665 / 2958234) : ℂ) * ζ ^ 14 + ((1522852 / 1479117) : ℂ) * ζ ^ 15 + ((429193 / 986078) : ℂ) * ζ ^ 16 + ((945779 / 493039) : ℂ) * ζ ^ 17 - ((5494817 / 2958234) : ℂ) * ζ ^ 18 + ((3328573 / 2958234) : ℂ) * ζ ^ 19 + ((146949 / 986078) : ℂ) * ζ ^ 20 + ((643166 / 1479117) : ℂ) * ζ ^ 21 - ((3025009 / 986078) : ℂ) * ζ ^ 22 + ((2986879 / 986078) : ℂ) * ζ ^ 23 - ((3514301 / 2958234) : ℂ) * ζ ^ 24 + ((3657545 / 2958234) : ℂ) * ζ ^ 25 - ((960533 / 1479117) : ℂ) * ζ ^ 26 + ((4064005 / 2958234) : ℂ) * ζ ^ 27 - ((5545043 / 2958234) : ℂ) * ζ ^ 28 + ((305373 / 493039) : ℂ) * ζ ^ 29 + ((269867 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep06Coefficient06 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep06CoefficientIdentity06 :
    row18_reducedY00_combinationStep06Coefficient06 =
      row18_reducedY00_combinationStep05Coefficient06 +
        row18_reducedY00_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep06Coefficient06 row18_reducedY00_combinationStep05Coefficient06 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep06Coefficient07 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep06CoefficientIdentity07 :
    row18_reducedY00_combinationStep06Coefficient07 =
      row18_reducedY00_combinationStep05Coefficient07 +
        row18_reducedY00_combinationStep06Multiplier *
          (-((8 / 79) : ℂ) - ((57 / 316) : ℂ) * ζ ^ 1 - ((149 / 316) : ℂ) * ζ ^ 2 + ((77 / 316) : ℂ) * ζ ^ 3 - ((49 / 158) : ℂ) * ζ ^ 5 + ((3 / 79) : ℂ) * ζ ^ 8 - ((105 / 316) : ℂ) * ζ ^ 9 + ((7 / 79) : ℂ) * ζ ^ 11 + ((13 / 79) : ℂ) * ζ ^ 12 + ((57 / 316) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((57 / 316) : ℂ) * ζ ^ 17 + ((149 / 316) : ℂ) * ζ ^ 18 + ((67 / 158) : ℂ) * ζ ^ 21 + ((149 / 316) : ℂ) * ζ ^ 22 - ((16 / 79) : ℂ) * ζ ^ 24 + ((41 / 316) : ℂ) * ζ ^ 25 + ((67 / 158) : ℂ) * ζ ^ 27 - ((3 / 79) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((6 / 79) : ℂ) * ζ ^ 30 - ((7 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep06Coefficient07 row18_reducedY00_combinationStep05Coefficient07 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 (-((31807 / 2958234) : ℂ) - ((15854 / 18723) : ℂ) * ζ ^ 1 - ((7659977 / 2958234) : ℂ) * ζ ^ 2 + ((777685 / 1479117) : ℂ) * ζ ^ 3 + ((6960262 / 1479117) : ℂ) * ζ ^ 4 + ((127009 / 986078) : ℂ) * ζ ^ 5 - ((7807727 / 2958234) : ℂ) * ζ ^ 6 - ((4051403 / 1479117) : ℂ) * ζ ^ 7 - ((1579949 / 1479117) : ℂ) * ζ ^ 8 + ((78745 / 2958234) : ℂ) * ζ ^ 9 + ((2046743 / 2958234) : ℂ) * ζ ^ 10 + ((11332247 / 2958234) : ℂ) * ζ ^ 11 + ((2229131 / 986078) : ℂ) * ζ ^ 12 - ((550900 / 1479117) : ℂ) * ζ ^ 13 - ((16863647 / 2958234) : ℂ) * ζ ^ 14 - ((11115481 / 2958234) : ℂ) * ζ ^ 15 - ((41537 / 1479117) : ℂ) * ζ ^ 16 + ((14859571 / 2958234) : ℂ) * ζ ^ 17 + ((2196284 / 493039) : ℂ) * ζ ^ 18 + ((4086283 / 2958234) : ℂ) * ζ ^ 19 - ((10360666 / 1479117) : ℂ) * ζ ^ 20 - ((2181122 / 493039) : ℂ) * ζ ^ 21 - ((1427845 / 2958234) : ℂ) * ζ ^ 22 + ((6796523 / 1479117) : ℂ) * ζ ^ 23 + ((6039755 / 2958234) : ℂ) * ζ ^ 24 + ((1068943 / 986078) : ℂ) * ζ ^ 25 - ((2467111 / 986078) : ℂ) * ζ ^ 26 - ((1530217 / 1479117) : ℂ) * ζ ^ 27 + ((466849 / 1479117) : ℂ) * ζ ^ 28 + ((18988 / 493039) : ℂ) * ζ ^ 29 + ((581252 / 1479117) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep06Coefficient08 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep06CoefficientIdentity08 :
    row18_reducedY00_combinationStep06Coefficient08 =
      row18_reducedY00_combinationStep05Coefficient08 +
        row18_reducedY00_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep06Coefficient08 row18_reducedY00_combinationStep05Coefficient08 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep06Coefficient09 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep06CoefficientIdentity09 :
    row18_reducedY00_combinationStep06Coefficient09 =
      row18_reducedY00_combinationStep05Coefficient09 +
        row18_reducedY00_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep06Coefficient09 row18_reducedY00_combinationStep05Coefficient09 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep06Coefficient10 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep06CoefficientIdentity10 :
    row18_reducedY00_combinationStep06Coefficient10 =
      row18_reducedY00_combinationStep05Coefficient10 +
        row18_reducedY00_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep06Coefficient10 row18_reducedY00_combinationStep05Coefficient10 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep06Coefficient11 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep06CoefficientIdentity11 :
    row18_reducedY00_combinationStep06Coefficient11 =
      row18_reducedY00_combinationStep05Coefficient11 +
        row18_reducedY00_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep06Coefficient11 row18_reducedY00_combinationStep05Coefficient11 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep06Coefficient12 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep06CoefficientIdentity12 :
    row18_reducedY00_combinationStep06Coefficient12 =
      row18_reducedY00_combinationStep05Coefficient12 +
        row18_reducedY00_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep06Coefficient12 row18_reducedY00_combinationStep05Coefficient12 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep06Coefficient13 : ℂ :=
  (((42 / 79) : ℂ) + ((9 / 79) : ℂ) * ζ ^ 1 + ((1 / 158) : ℂ) * ζ ^ 2 + ((4 / 79) : ℂ) * ζ ^ 5 - ((83 / 158) : ℂ) * ζ ^ 6 - ((83 / 158) : ℂ) * ζ ^ 8 + ((4 / 79) : ℂ) * ζ ^ 9 - ((49 / 158) : ℂ) * ζ ^ 11 - ((104 / 79) : ℂ) * ζ ^ 12 - ((9 / 79) : ℂ) * ζ ^ 13 + ((40 / 79) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 17 - ((19 / 79) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 - ((1 / 158) : ℂ) * ζ ^ 22 + ((121 / 158) : ℂ) * ζ ^ 24 + ((5 / 79) : ℂ) * ζ ^ 25 - ((40 / 79) : ℂ) * ζ ^ 27 + ((83 / 158) : ℂ) * ζ ^ 28 + ((9 / 79) : ℂ) * ζ ^ 29 + ((125 / 158) : ℂ) * ζ ^ 30 + ((49 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep06CoefficientIdentity13 :
    row18_reducedY00_combinationStep06Coefficient13 =
      row18_reducedY00_combinationStep05Coefficient13 +
        row18_reducedY00_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep06Coefficient13 row18_reducedY00_combinationStep05Coefficient13 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep06Coefficient14 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep06CoefficientIdentity14 :
    row18_reducedY00_combinationStep06Coefficient14 =
      row18_reducedY00_combinationStep05Coefficient14 +
        row18_reducedY00_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep06Coefficient14 row18_reducedY00_combinationStep05Coefficient14 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep06Coefficient15 : ℂ :=
  (-((33 / 79) : ℂ) + ((24 / 79) : ℂ) * ζ ^ 1 + ((19 / 158) : ℂ) * ζ ^ 2 - ((77 / 158) : ℂ) * ζ ^ 3 - ((19 / 158) : ℂ) * ζ ^ 5 - ((2 / 79) : ℂ) * ζ ^ 6 - ((5 / 158) : ℂ) * ζ ^ 8 - ((95 / 158) : ℂ) * ζ ^ 9 - ((9 / 79) : ℂ) * ζ ^ 11 - ((5 / 158) : ℂ) * ζ ^ 12 - ((24 / 79) : ℂ) * ζ ^ 13 + ((5 / 79) : ℂ) * ζ ^ 15 - ((24 / 79) : ℂ) * ζ ^ 17 + ((23 / 158) : ℂ) * ζ ^ 18 + ((29 / 158) : ℂ) * ζ ^ 21 - ((19 / 158) : ℂ) * ζ ^ 22 + ((67 / 158) : ℂ) * ζ ^ 25 - ((29 / 158) : ℂ) * ζ ^ 27 + ((5 / 158) : ℂ) * ζ ^ 28 + ((24 / 79) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30 + ((9 / 79) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep06CoefficientIdentity15 :
    row18_reducedY00_combinationStep06Coefficient15 =
      row18_reducedY00_combinationStep05Coefficient15 +
        row18_reducedY00_combinationStep06Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep06Coefficient15 row18_reducedY00_combinationStep05Coefficient15 row18_reducedY00_combinationStep06Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY00_combinationStep06
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY00_combinationStep06Coefficient00) * Y 0 0
      + (row18_reducedY00_combinationStep06Coefficient01) * Y 0 1
      + (row18_reducedY00_combinationStep06Coefficient02) * Y 1 0
      + (row18_reducedY00_combinationStep06Coefficient03) * Y 1 1
      + (row18_reducedY00_combinationStep06Coefficient04) * Y 2 2
      + (row18_reducedY00_combinationStep06Coefficient05) * Y 2 3
      + (row18_reducedY00_combinationStep06Coefficient06) * Y 3 2
      + (row18_reducedY00_combinationStep06Coefficient07) * Y 3 3
      + (row18_reducedY00_combinationStep06Coefficient08) * Y 4 4
      + (row18_reducedY00_combinationStep06Coefficient09) * Y 4 5
      + (row18_reducedY00_combinationStep06Coefficient10) * Y 5 4
      + (row18_reducedY00_combinationStep06Coefficient11) * Y 5 5
      + (row18_reducedY00_combinationStep06Coefficient12) * Y 6 6
      + (row18_reducedY00_combinationStep06Coefficient13) * Y 6 7
      + (row18_reducedY00_combinationStep06Coefficient14) * Y 7 6
      + (row18_reducedY00_combinationStep06Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY00_combinationStep05 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation13
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY00_combinationStep06CoefficientIdentity00,
      row18_reducedY00_combinationStep06CoefficientIdentity01,
      row18_reducedY00_combinationStep06CoefficientIdentity02,
      row18_reducedY00_combinationStep06CoefficientIdentity03,
      row18_reducedY00_combinationStep06CoefficientIdentity04,
      row18_reducedY00_combinationStep06CoefficientIdentity05,
      row18_reducedY00_combinationStep06CoefficientIdentity06,
      row18_reducedY00_combinationStep06CoefficientIdentity07,
      row18_reducedY00_combinationStep06CoefficientIdentity08,
      row18_reducedY00_combinationStep06CoefficientIdentity09,
      row18_reducedY00_combinationStep06CoefficientIdentity10,
      row18_reducedY00_combinationStep06CoefficientIdentity11,
      row18_reducedY00_combinationStep06CoefficientIdentity12,
      row18_reducedY00_combinationStep06CoefficientIdentity13,
      row18_reducedY00_combinationStep06CoefficientIdentity14,
      row18_reducedY00_combinationStep06CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY00_combinationStep06Multiplier * equation

private def row18_reducedY00_combinationStep07Multiplier : ℂ :=
  (-((208 / 79) : ℂ) - ((380 / 79) : ℂ) * ζ ^ 1 + ((60 / 79) : ℂ) * ζ ^ 2 - ((132 / 79) : ℂ) * ζ ^ 3 - ((306 / 79) : ℂ) * ζ ^ 5 + ((236 / 79) : ℂ) * ζ ^ 8 + ((156 / 79) : ℂ) * ζ ^ 9 - ((24 / 79) : ℂ) * ζ ^ 11 + ((180 / 79) : ℂ) * ζ ^ 12 + ((380 / 79) : ℂ) * ζ ^ 13 + ((58 / 79) : ℂ) * ζ ^ 15 + ((380 / 79) : ℂ) * ζ ^ 17 - ((60 / 79) : ℂ) * ζ ^ 18 + ((248 / 79) : ℂ) * ζ ^ 21 - ((60 / 79) : ℂ) * ζ ^ 22 - ((416 / 79) : ℂ) * ζ ^ 24 - ((74 / 79) : ℂ) * ζ ^ 25 + ((248 / 79) : ℂ) * ζ ^ 27 - ((236 / 79) : ℂ) * ζ ^ 28 - ((380 / 79) : ℂ) * ζ ^ 29 - ((160 / 79) : ℂ) * ζ ^ 30 + ((24 / 79) : ℂ) * ζ ^ 31)

private def row18_reducedY00_combinationStep07Coefficient00 : ℂ :=
  (((121 / 79) : ℂ) - ((342 / 395) : ℂ) * ζ ^ 1 + ((1961 / 790) : ℂ) * ζ ^ 2 + ((323 / 395) : ℂ) * ζ ^ 3 + ((289 / 395) : ℂ) * ζ ^ 5 + ((1332 / 395) : ℂ) * ζ ^ 6 + ((387 / 158) : ℂ) * ζ ^ 8 + ((1024 / 395) : ℂ) * ζ ^ 9 + ((701 / 395) : ℂ) * ζ ^ 11 + ((387 / 158) : ℂ) * ζ ^ 12 + ((342 / 395) : ℂ) * ζ ^ 13 + ((308 / 395) : ℂ) * ζ ^ 15 + ((342 / 395) : ℂ) * ζ ^ 17 - ((703 / 790) : ℂ) * ζ ^ 18 + ((19 / 395) : ℂ) * ζ ^ 21 - ((1961 / 790) : ℂ) * ζ ^ 22 - ((631 / 395) : ℂ) * ζ ^ 25 - ((19 / 395) : ℂ) * ζ ^ 27 - ((387 / 158) : ℂ) * ζ ^ 28 - ((342 / 395) : ℂ) * ζ ^ 29 + ((666 / 395) : ℂ) * ζ ^ 30 - ((701 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep07CoefficientIdentity00 :
    row18_reducedY00_combinationStep07Coefficient00 =
      row18_reducedY00_combinationStep06Coefficient00 +
        row18_reducedY00_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep07Coefficient00 row18_reducedY00_combinationStep06Coefficient00 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep07Coefficient01 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep07CoefficientIdentity01 :
    row18_reducedY00_combinationStep07Coefficient01 =
      row18_reducedY00_combinationStep06Coefficient01 +
        row18_reducedY00_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep07Coefficient01 row18_reducedY00_combinationStep06Coefficient01 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep07Coefficient02 : ℂ :=
  (((262 / 395) : ℂ) - ((112 / 395) : ℂ) * ζ ^ 1 - ((1703 / 790) : ℂ) * ζ ^ 2 + ((133 / 158) : ℂ) * ζ ^ 3 - ((861 / 395) : ℂ) * ζ ^ 5 - ((947 / 790) : ℂ) * ζ ^ 6 - ((1016 / 395) : ℂ) * ζ ^ 8 - ((637 / 790) : ℂ) * ζ ^ 9 - ((331 / 158) : ℂ) * ζ ^ 11 - ((378 / 395) : ℂ) * ζ ^ 12 + ((112 / 395) : ℂ) * ζ ^ 13 - ((133 / 158) : ℂ) * ζ ^ 15 + ((112 / 395) : ℂ) * ζ ^ 17 + ((1179 / 790) : ℂ) * ζ ^ 18 + ((749 / 395) : ℂ) * ζ ^ 21 + ((1703 / 790) : ℂ) * ζ ^ 22 + ((1703 / 790) : ℂ) * ζ ^ 24 + ((749 / 395) : ℂ) * ζ ^ 25 + ((331 / 158) : ℂ) * ζ ^ 27 + ((1016 / 395) : ℂ) * ζ ^ 28 - ((112 / 395) : ℂ) * ζ ^ 29 + ((329 / 790) : ℂ) * ζ ^ 30 + ((331 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep07CoefficientIdentity02 :
    row18_reducedY00_combinationStep07Coefficient02 =
      row18_reducedY00_combinationStep06Coefficient02 +
        row18_reducedY00_combinationStep07Multiplier *
          (-((19 / 158) : ℂ) - ((13 / 316) : ℂ) * ζ ^ 1 - ((11 / 316) : ℂ) * ζ ^ 2 - ((6 / 79) : ℂ) * ζ ^ 3 - ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 - ((21 / 79) : ℂ) * ζ ^ 9 + ((15 / 316) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((13 / 316) : ℂ) * ζ ^ 13 - ((6 / 79) : ℂ) * ζ ^ 15 + ((13 / 316) : ℂ) * ζ ^ 17 - ((27 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 - ((13 / 316) : ℂ) * ζ ^ 25 + ((15 / 316) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((13 / 316) : ℂ) * ζ ^ 29 + ((12 / 79) : ℂ) * ζ ^ 30 - ((15 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep07Coefficient02 row18_reducedY00_combinationStep06Coefficient02 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 (((4978 / 6241) : ℂ) + ((1363 / 6241) : ℂ) * ζ ^ 1 - ((2345 / 12482) : ℂ) * ζ ^ 2 + ((2043 / 12482) : ℂ) * ζ ^ 3 - ((2434 / 6241) : ℂ) * ζ ^ 4 + ((1310 / 6241) : ℂ) * ζ ^ 5 + ((10323 / 12482) : ℂ) * ζ ^ 6 + ((3050 / 6241) : ℂ) * ζ ^ 7 - ((2498 / 6241) : ℂ) * ζ ^ 8 - ((1739 / 12482) : ℂ) * ζ ^ 9 + ((5095 / 12482) : ℂ) * ζ ^ 10 - ((4917 / 12482) : ℂ) * ζ ^ 11 + ((4607 / 6241) : ℂ) * ζ ^ 12 - ((1753 / 6241) : ℂ) * ζ ^ 13 - ((2961 / 6241) : ℂ) * ζ ^ 14 + ((8021 / 12482) : ℂ) * ζ ^ 15 - ((347 / 6241) : ℂ) * ζ ^ 16 + ((1852 / 6241) : ℂ) * ζ ^ 17 + ((505 / 6241) : ℂ) * ζ ^ 18 - ((728 / 6241) : ℂ) * ζ ^ 19 + ((1667 / 6241) : ℂ) * ζ ^ 20 - ((6627 / 12482) : ℂ) * ζ ^ 21 - ((4319 / 12482) : ℂ) * ζ ^ 22 + ((92 / 6241) : ℂ) * ζ ^ 23 + ((4045 / 12482) : ℂ) * ζ ^ 24 + ((7860 / 6241) : ℂ) * ζ ^ 25 + ((13 / 6241) : ℂ) * ζ ^ 26 - ((3509 / 6241) : ℂ) * ζ ^ 27 - ((573 / 6241) : ℂ) * ζ ^ 28 + ((888 / 6241) : ℂ) * ζ ^ 29 - ((90 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep07Coefficient03 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep07CoefficientIdentity03 :
    row18_reducedY00_combinationStep07Coefficient03 =
      row18_reducedY00_combinationStep06Coefficient03 +
        row18_reducedY00_combinationStep07Multiplier *
          (((4 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 - ((3 / 158) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((13 / 158) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((8 / 79) : ℂ) * ζ ^ 24 - ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((3 / 158) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((3 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep07Coefficient03 row18_reducedY00_combinationStep06Coefficient03 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 (-((4466 / 6241) : ℂ) - ((3988 / 6241) : ℂ) * ζ ^ 1 - ((6751 / 12482) : ℂ) * ζ ^ 2 - ((1189 / 12482) : ℂ) * ζ ^ 3 + ((4723 / 6241) : ℂ) * ζ ^ 4 + ((1569 / 12482) : ℂ) * ζ ^ 5 - ((125 / 6241) : ℂ) * ζ ^ 6 - ((1633 / 6241) : ℂ) * ζ ^ 7 - ((4183 / 6241) : ℂ) * ζ ^ 8 + ((5487 / 6241) : ℂ) * ζ ^ 9 + ((1469 / 6241) : ℂ) * ζ ^ 10 + ((2829 / 6241) : ℂ) * ζ ^ 11 + ((1961 / 12482) : ℂ) * ζ ^ 12 - ((293 / 6241) : ℂ) * ζ ^ 13 + ((139 / 6241) : ℂ) * ζ ^ 14 + ((2645 / 12482) : ℂ) * ζ ^ 15 - ((191 / 6241) : ℂ) * ζ ^ 16 + ((3653 / 6241) : ℂ) * ζ ^ 17 + ((2886 / 6241) : ℂ) * ζ ^ 18 + ((3632 / 6241) : ℂ) * ζ ^ 19 - ((3885 / 6241) : ℂ) * ζ ^ 20 - ((2547 / 6241) : ℂ) * ζ ^ 21 + ((2357 / 12482) : ℂ) * ζ ^ 22 + ((3984 / 6241) : ℂ) * ζ ^ 23 + ((697 / 6241) : ℂ) * ζ ^ 24 - ((627 / 6241) : ℂ) * ζ ^ 25 - ((2849 / 6241) : ℂ) * ζ ^ 26 - ((718 / 6241) : ℂ) * ζ ^ 27 + ((916 / 6241) : ℂ) * ζ ^ 28 + ((8 / 79) : ℂ) * ζ ^ 29 - ((84 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep07Coefficient04 : ℂ :=
  (-((42 / 79) : ℂ) + ((342 / 395) : ℂ) * ζ ^ 1 - ((1961 / 790) : ℂ) * ζ ^ 2 - ((323 / 395) : ℂ) * ζ ^ 3 - ((289 / 395) : ℂ) * ζ ^ 5 - ((1332 / 395) : ℂ) * ζ ^ 6 - ((387 / 158) : ℂ) * ζ ^ 8 - ((1024 / 395) : ℂ) * ζ ^ 9 - ((701 / 395) : ℂ) * ζ ^ 11 - ((387 / 158) : ℂ) * ζ ^ 12 - ((342 / 395) : ℂ) * ζ ^ 13 - ((308 / 395) : ℂ) * ζ ^ 15 - ((342 / 395) : ℂ) * ζ ^ 17 + ((703 / 790) : ℂ) * ζ ^ 18 - ((19 / 395) : ℂ) * ζ ^ 21 + ((1961 / 790) : ℂ) * ζ ^ 22 + ((631 / 395) : ℂ) * ζ ^ 25 + ((19 / 395) : ℂ) * ζ ^ 27 + ((387 / 158) : ℂ) * ζ ^ 28 + ((342 / 395) : ℂ) * ζ ^ 29 - ((666 / 395) : ℂ) * ζ ^ 30 + ((701 / 395) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep07CoefficientIdentity04 :
    row18_reducedY00_combinationStep07Coefficient04 =
      row18_reducedY00_combinationStep06Coefficient04 +
        row18_reducedY00_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep07Coefficient04 row18_reducedY00_combinationStep06Coefficient04 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep07Coefficient05 : ℂ :=
  (((18 / 79) : ℂ) + ((65 / 79) : ℂ) * ζ ^ 1 - ((165 / 158) : ℂ) * ζ ^ 2 - ((252 / 79) : ℂ) * ζ ^ 5 - ((201 / 158) : ℂ) * ζ ^ 6 - ((201 / 158) : ℂ) * ζ ^ 8 - ((252 / 79) : ℂ) * ζ ^ 9 - ((437 / 158) : ℂ) * ζ ^ 11 - ((62 / 79) : ℂ) * ζ ^ 12 - ((65 / 79) : ℂ) * ζ ^ 13 - ((135 / 79) : ℂ) * ζ ^ 15 - ((65 / 79) : ℂ) * ζ ^ 17 + ((12 / 79) : ℂ) * ζ ^ 18 + ((187 / 158) : ℂ) * ζ ^ 21 + ((165 / 158) : ℂ) * ζ ^ 22 + ((177 / 158) : ℂ) * ζ ^ 24 + ((317 / 79) : ℂ) * ζ ^ 25 + ((135 / 79) : ℂ) * ζ ^ 27 + ((201 / 158) : ℂ) * ζ ^ 28 + ((65 / 79) : ℂ) * ζ ^ 29 - ((77 / 158) : ℂ) * ζ ^ 30 + ((437 / 158) : ℂ) * ζ ^ 31)

private theorem row18_reducedY00_combinationStep07CoefficientIdentity05 :
    row18_reducedY00_combinationStep07Coefficient05 =
      row18_reducedY00_combinationStep06Coefficient05 +
        row18_reducedY00_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep07Coefficient05 row18_reducedY00_combinationStep06Coefficient05 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep07Coefficient06 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep07CoefficientIdentity06 :
    row18_reducedY00_combinationStep07Coefficient06 =
      row18_reducedY00_combinationStep06Coefficient06 +
        row18_reducedY00_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep07Coefficient06 row18_reducedY00_combinationStep06Coefficient06 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep07Coefficient07 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep07CoefficientIdentity07 :
    row18_reducedY00_combinationStep07Coefficient07 =
      row18_reducedY00_combinationStep06Coefficient07 +
        row18_reducedY00_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep07Coefficient07 row18_reducedY00_combinationStep06Coefficient07 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep07Coefficient08 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep07CoefficientIdentity08 :
    row18_reducedY00_combinationStep07Coefficient08 =
      row18_reducedY00_combinationStep06Coefficient08 +
        row18_reducedY00_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep07Coefficient08 row18_reducedY00_combinationStep06Coefficient08 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep07Coefficient09 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep07CoefficientIdentity09 :
    row18_reducedY00_combinationStep07Coefficient09 =
      row18_reducedY00_combinationStep06Coefficient09 +
        row18_reducedY00_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep07Coefficient09 row18_reducedY00_combinationStep06Coefficient09 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep07Coefficient10 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep07CoefficientIdentity10 :
    row18_reducedY00_combinationStep07Coefficient10 =
      row18_reducedY00_combinationStep06Coefficient10 +
        row18_reducedY00_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep07Coefficient10 row18_reducedY00_combinationStep06Coefficient10 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep07Coefficient11 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep07CoefficientIdentity11 :
    row18_reducedY00_combinationStep07Coefficient11 =
      row18_reducedY00_combinationStep06Coefficient11 +
        row18_reducedY00_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep07Coefficient11 row18_reducedY00_combinationStep06Coefficient11 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep07Coefficient12 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep07CoefficientIdentity12 :
    row18_reducedY00_combinationStep07Coefficient12 =
      row18_reducedY00_combinationStep06Coefficient12 +
        row18_reducedY00_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep07Coefficient12 row18_reducedY00_combinationStep06Coefficient12 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep07Coefficient13 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep07CoefficientIdentity13 :
    row18_reducedY00_combinationStep07Coefficient13 =
      row18_reducedY00_combinationStep06Coefficient13 +
        row18_reducedY00_combinationStep07Multiplier *
          (((5 / 316) : ℂ) - ((3 / 316) : ℂ) * ζ ^ 1 + ((35 / 316) : ℂ) * ζ ^ 2 - ((33 / 158) : ℂ) * ζ ^ 3 - ((3 / 316) : ℂ) * ζ ^ 5 + ((10 / 79) : ℂ) * ζ ^ 6 - ((10 / 79) : ℂ) * ζ ^ 8 + ((3 / 316) : ℂ) * ζ ^ 9 + ((33 / 316) : ℂ) * ζ ^ 11 + ((3 / 79) : ℂ) * ζ ^ 12 + ((3 / 316) : ℂ) * ζ ^ 13 + ((35 / 158) : ℂ) * ζ ^ 15 + ((3 / 316) : ℂ) * ζ ^ 17 + ((19 / 316) : ℂ) * ζ ^ 18 + ((45 / 158) : ℂ) * ζ ^ 21 - ((35 / 316) : ℂ) * ζ ^ 22 + ((59 / 316) : ℂ) * ζ ^ 24 + ((1 / 79) : ℂ) * ζ ^ 27 + ((10 / 79) : ℂ) * ζ ^ 28 - ((3 / 316) : ℂ) * ζ ^ 29 + ((13 / 79) : ℂ) * ζ ^ 30 - ((33 / 316) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep07Coefficient13 row18_reducedY00_combinationStep06Coefficient13 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 (((3058 / 6241) : ℂ) + ((392 / 6241) : ℂ) * ζ ^ 1 - ((2841 / 12482) : ℂ) * ζ ^ 2 - ((103 / 6241) : ℂ) * ζ ^ 3 + ((3836 / 6241) : ℂ) * ζ ^ 4 - ((4895 / 12482) : ℂ) * ζ ^ 5 - ((2491 / 12482) : ℂ) * ζ ^ 6 - ((12839 / 12482) : ℂ) * ζ ^ 7 + ((2017 / 12482) : ℂ) * ζ ^ 8 + ((10211 / 12482) : ℂ) * ζ ^ 9 + ((2538 / 6241) : ℂ) * ζ ^ 10 - ((1486 / 6241) : ℂ) * ζ ^ 11 - ((24711 / 12482) : ℂ) * ζ ^ 12 - ((6425 / 12482) : ℂ) * ζ ^ 13 - ((1453 / 6241) : ℂ) * ζ ^ 14 + ((5079 / 12482) : ℂ) * ζ ^ 15 + ((2641 / 12482) : ℂ) * ζ ^ 16 - ((707 / 12482) : ℂ) * ζ ^ 17 - ((12423 / 12482) : ℂ) * ζ ^ 18 - ((1465 / 6241) : ℂ) * ζ ^ 19 - ((10497 / 12482) : ℂ) * ζ ^ 20 - ((3557 / 6241) : ℂ) * ζ ^ 21 - ((2515 / 12482) : ℂ) * ζ ^ 22 + ((7701 / 6241) : ℂ) * ζ ^ 23 - ((6705 / 12482) : ℂ) * ζ ^ 24 - ((2191 / 6241) : ℂ) * ζ ^ 25 - ((6207 / 6241) : ℂ) * ζ ^ 26 - ((2633 / 6241) : ℂ) * ζ ^ 27 + ((1037 / 6241) : ℂ) * ζ ^ 28 + ((1632 / 6241) : ℂ) * ζ ^ 29 - ((198 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep07Coefficient14 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep07CoefficientIdentity14 :
    row18_reducedY00_combinationStep07Coefficient14 =
      row18_reducedY00_combinationStep06Coefficient14 +
        row18_reducedY00_combinationStep07Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep07Coefficient14 row18_reducedY00_combinationStep06Coefficient14 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep07Coefficient15 : ℂ :=
  (-(1 : ℂ))

private theorem row18_reducedY00_combinationStep07CoefficientIdentity15 :
    row18_reducedY00_combinationStep07Coefficient15 =
      row18_reducedY00_combinationStep06Coefficient15 +
        row18_reducedY00_combinationStep07Multiplier *
          (-((4 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((35 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 + ((3 / 158) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((13 / 158) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 + ((35 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((35 / 316) : ℂ) * ζ ^ 22 - ((8 / 79) : ℂ) * ζ ^ 24 + ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((3 / 158) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((3 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep07Coefficient15 row18_reducedY00_combinationStep06Coefficient15 row18_reducedY00_combinationStep07Multiplier
  close_cyclotomic_row18 (((4466 / 6241) : ℂ) + ((3988 / 6241) : ℂ) * ζ ^ 1 + ((6751 / 12482) : ℂ) * ζ ^ 2 + ((1189 / 12482) : ℂ) * ζ ^ 3 - ((4723 / 6241) : ℂ) * ζ ^ 4 - ((1569 / 12482) : ℂ) * ζ ^ 5 + ((125 / 6241) : ℂ) * ζ ^ 6 + ((1633 / 6241) : ℂ) * ζ ^ 7 + ((4183 / 6241) : ℂ) * ζ ^ 8 - ((5487 / 6241) : ℂ) * ζ ^ 9 - ((1469 / 6241) : ℂ) * ζ ^ 10 - ((2829 / 6241) : ℂ) * ζ ^ 11 - ((1961 / 12482) : ℂ) * ζ ^ 12 + ((293 / 6241) : ℂ) * ζ ^ 13 - ((139 / 6241) : ℂ) * ζ ^ 14 - ((2645 / 12482) : ℂ) * ζ ^ 15 + ((191 / 6241) : ℂ) * ζ ^ 16 - ((3653 / 6241) : ℂ) * ζ ^ 17 - ((2886 / 6241) : ℂ) * ζ ^ 18 - ((3632 / 6241) : ℂ) * ζ ^ 19 + ((3885 / 6241) : ℂ) * ζ ^ 20 + ((2547 / 6241) : ℂ) * ζ ^ 21 - ((2357 / 12482) : ℂ) * ζ ^ 22 - ((3984 / 6241) : ℂ) * ζ ^ 23 - ((697 / 6241) : ℂ) * ζ ^ 24 + ((627 / 6241) : ℂ) * ζ ^ 25 + ((2849 / 6241) : ℂ) * ζ ^ 26 + ((718 / 6241) : ℂ) * ζ ^ 27 - ((916 / 6241) : ℂ) * ζ ^ 28 - ((8 / 79) : ℂ) * ζ ^ 29 + ((84 / 6241) : ℂ) * ζ ^ 30)

private theorem row18_reducedY00_combinationStep07
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY00_combinationStep07Coefficient00) * Y 0 0
      + (row18_reducedY00_combinationStep07Coefficient01) * Y 0 1
      + (row18_reducedY00_combinationStep07Coefficient02) * Y 1 0
      + (row18_reducedY00_combinationStep07Coefficient03) * Y 1 1
      + (row18_reducedY00_combinationStep07Coefficient04) * Y 2 2
      + (row18_reducedY00_combinationStep07Coefficient05) * Y 2 3
      + (row18_reducedY00_combinationStep07Coefficient06) * Y 3 2
      + (row18_reducedY00_combinationStep07Coefficient07) * Y 3 3
      + (row18_reducedY00_combinationStep07Coefficient08) * Y 4 4
      + (row18_reducedY00_combinationStep07Coefficient09) * Y 4 5
      + (row18_reducedY00_combinationStep07Coefficient10) * Y 5 4
      + (row18_reducedY00_combinationStep07Coefficient11) * Y 5 5
      + (row18_reducedY00_combinationStep07Coefficient12) * Y 6 6
      + (row18_reducedY00_combinationStep07Coefficient13) * Y 6 7
      + (row18_reducedY00_combinationStep07Coefficient14) * Y 7 6
      + (row18_reducedY00_combinationStep07Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY00_combinationStep06 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation17
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY00_combinationStep07CoefficientIdentity00,
      row18_reducedY00_combinationStep07CoefficientIdentity01,
      row18_reducedY00_combinationStep07CoefficientIdentity02,
      row18_reducedY00_combinationStep07CoefficientIdentity03,
      row18_reducedY00_combinationStep07CoefficientIdentity04,
      row18_reducedY00_combinationStep07CoefficientIdentity05,
      row18_reducedY00_combinationStep07CoefficientIdentity06,
      row18_reducedY00_combinationStep07CoefficientIdentity07,
      row18_reducedY00_combinationStep07CoefficientIdentity08,
      row18_reducedY00_combinationStep07CoefficientIdentity09,
      row18_reducedY00_combinationStep07CoefficientIdentity10,
      row18_reducedY00_combinationStep07CoefficientIdentity11,
      row18_reducedY00_combinationStep07CoefficientIdentity12,
      row18_reducedY00_combinationStep07CoefficientIdentity13,
      row18_reducedY00_combinationStep07CoefficientIdentity14,
      row18_reducedY00_combinationStep07CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY00_combinationStep07Multiplier * equation

private def row18_reducedY00_combinationStep08Multiplier : ℂ :=
  (((116 / 79) : ℂ) + ((84 / 395) : ℂ) * ζ ^ 1 + ((2028 / 395) : ℂ) * ζ ^ 2 + ((44 / 395) : ℂ) * ζ ^ 3 + ((1162 / 395) : ℂ) * ζ ^ 5 + ((3232 / 395) : ℂ) * ζ ^ 6 + ((320 / 79) : ℂ) * ζ ^ 8 + ((1632 / 395) : ℂ) * ζ ^ 9 + ((1588 / 395) : ℂ) * ζ ^ 11 + ((320 / 79) : ℂ) * ζ ^ 12 - ((84 / 395) : ℂ) * ζ ^ 13 + ((1034 / 395) : ℂ) * ζ ^ 15 - ((84 / 395) : ℂ) * ζ ^ 17 - ((1204 / 395) : ℂ) * ζ ^ 18 - ((128 / 395) : ℂ) * ζ ^ 21 - ((2028 / 395) : ℂ) * ζ ^ 22 - ((1078 / 395) : ℂ) * ζ ^ 25 + ((128 / 395) : ℂ) * ζ ^ 27 - ((320 / 79) : ℂ) * ζ ^ 28 + ((84 / 395) : ℂ) * ζ ^ 29 + ((1616 / 395) : ℂ) * ζ ^ 30 - ((1588 / 395) : ℂ) * ζ ^ 31)

private def row18_reducedY00_combinationStep08Coefficient00 : ℂ :=
  ((1 : ℂ))

private theorem row18_reducedY00_combinationStep08CoefficientIdentity00 :
    row18_reducedY00_combinationStep08Coefficient00 =
      row18_reducedY00_combinationStep07Coefficient00 +
        row18_reducedY00_combinationStep08Multiplier *
          (((3 / 79) : ℂ) - ((11 / 316) : ℂ) * ζ ^ 1 - ((85 / 316) : ℂ) * ζ ^ 2 - ((1 / 316) : ℂ) * ζ ^ 3 - ((15 / 158) : ℂ) * ζ ^ 5 - ((8 / 79) : ℂ) * ζ ^ 6 - ((35 / 316) : ℂ) * ζ ^ 8 + ((13 / 316) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((35 / 316) : ℂ) * ζ ^ 12 + ((11 / 316) : ℂ) * ζ ^ 13 - ((9 / 158) : ℂ) * ζ ^ 15 + ((11 / 316) : ℂ) * ζ ^ 17 - ((53 / 316) : ℂ) * ζ ^ 18 + ((3 / 79) : ℂ) * ζ ^ 21 + ((85 / 316) : ℂ) * ζ ^ 22 + ((19 / 316) : ℂ) * ζ ^ 25 - ((3 / 79) : ℂ) * ζ ^ 27 + ((35 / 316) : ℂ) * ζ ^ 28 - ((11 / 316) : ℂ) * ζ ^ 29 - ((4 / 79) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep08Coefficient00 row18_reducedY00_combinationStep07Coefficient00 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 (((3666 / 6241) : ℂ) - ((359 / 395) : ℂ) * ζ ^ 1 + ((28395 / 12482) : ℂ) * ζ ^ 2 + ((18142 / 31205) : ℂ) * ζ ^ 3 - ((61567 / 31205) : ℂ) * ζ ^ 4 + ((48886 / 31205) : ℂ) * ζ ^ 5 + ((7092 / 6241) : ℂ) * ζ ^ 6 - ((135209 / 62410) : ℂ) * ζ ^ 7 + ((10440 / 6241) : ℂ) * ζ ^ 8 + ((32496 / 31205) : ℂ) * ζ ^ 9 - ((20027 / 6241) : ℂ) * ζ ^ 10 + ((26947 / 12482) : ℂ) * ζ ^ 11 + ((24187 / 62410) : ℂ) * ζ ^ 12 - ((172891 / 62410) : ℂ) * ζ ^ 13 + ((70053 / 31205) : ℂ) * ζ ^ 14 - ((40753 / 62410) : ℂ) * ζ ^ 15 - ((80253 / 31205) : ℂ) * ζ ^ 16 + ((143187 / 62410) : ℂ) * ζ ^ 17 - ((34616 / 31205) : ℂ) * ζ ^ 18 - ((18261 / 31205) : ℂ) * ζ ^ 19 + ((57961 / 31205) : ℂ) * ζ ^ 20 - ((85517 / 62410) : ℂ) * ζ ^ 21 - ((6435 / 12482) : ℂ) * ζ ^ 22 + ((30983 / 31205) : ℂ) * ζ ^ 23 - ((15983 / 31205) : ℂ) * ζ ^ 24 - ((921 / 31205) : ℂ) * ζ ^ 25 + ((19067 / 31205) : ℂ) * ζ ^ 26 - ((2615 / 6241) : ℂ) * ζ ^ 27 - ((2391 / 31205) : ℂ) * ζ ^ 28 + ((696 / 31205) : ℂ) * ζ ^ 29 + ((5558 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep08Coefficient01 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep08CoefficientIdentity01 :
    row18_reducedY00_combinationStep08Coefficient01 =
      row18_reducedY00_combinationStep07Coefficient01 +
        row18_reducedY00_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep08Coefficient01 row18_reducedY00_combinationStep07Coefficient01 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep08Coefficient02 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep08CoefficientIdentity02 :
    row18_reducedY00_combinationStep08Coefficient02 =
      row18_reducedY00_combinationStep07Coefficient02 +
        row18_reducedY00_combinationStep08Multiplier *
          (-((19 / 158) : ℂ) - ((39 / 316) : ℂ) * ζ ^ 1 + ((11 / 316) : ℂ) * ζ ^ 2 - ((97 / 316) : ℂ) * ζ ^ 3 - ((12 / 79) : ℂ) * ζ ^ 5 + ((17 / 158) : ℂ) * ζ ^ 6 + ((59 / 316) : ℂ) * ζ ^ 8 + ((15 / 316) : ℂ) * ζ ^ 9 + ((21 / 79) : ℂ) * ζ ^ 11 - ((23 / 316) : ℂ) * ζ ^ 12 + ((39 / 316) : ℂ) * ζ ^ 13 + ((97 / 316) : ℂ) * ζ ^ 15 + ((39 / 316) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 + ((9 / 316) : ℂ) * ζ ^ 21 - ((11 / 316) : ℂ) * ζ ^ 22 - ((11 / 316) : ℂ) * ζ ^ 24 + ((9 / 316) : ℂ) * ζ ^ 25 - ((21 / 79) : ℂ) * ζ ^ 27 - ((59 / 316) : ℂ) * ζ ^ 28 - ((39 / 316) : ℂ) * ζ ^ 29 - ((12 / 79) : ℂ) * ζ ^ 30 - ((21 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep08Coefficient02 row18_reducedY00_combinationStep07Coefficient02 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 (((15188 / 31205) : ℂ) - ((15301 / 31205) : ℂ) * ζ ^ 1 - ((171517 / 62410) : ℂ) * ζ ^ 2 - ((3103 / 12482) : ℂ) * ζ ^ 3 - ((12077 / 31205) : ℂ) * ζ ^ 4 - ((23955 / 6241) : ℂ) * ζ ^ 5 + ((18347 / 62410) : ℂ) * ζ ^ 6 - ((44181 / 31205) : ℂ) * ζ ^ 7 - ((30965 / 12482) : ℂ) * ζ ^ 8 - ((22157 / 62410) : ℂ) * ζ ^ 9 - ((8803 / 62410) : ℂ) * ζ ^ 10 - ((31625 / 12482) : ℂ) * ζ ^ 11 + ((37091 / 62410) : ℂ) * ζ ^ 12 + ((7978 / 6241) : ℂ) * ζ ^ 13 - ((157039 / 62410) : ℂ) * ζ ^ 14 + ((111521 / 62410) : ℂ) * ζ ^ 15 + ((7933 / 31205) : ℂ) * ζ ^ 16 - ((22082 / 31205) : ℂ) * ζ ^ 17 + ((54962 / 31205) : ℂ) * ζ ^ 18 + ((2394 / 6241) : ℂ) * ζ ^ 19 + ((1007 / 31205) : ℂ) * ζ ^ 20 + ((130511 / 62410) : ℂ) * ζ ^ 21 + ((23421 / 62410) : ℂ) * ζ ^ 22 + ((12392 / 31205) : ℂ) * ζ ^ 23 + ((45326 / 31205) : ℂ) * ζ ^ 24 - ((6231 / 31205) : ℂ) * ζ ^ 25 - ((8143 / 31205) : ℂ) * ζ ^ 26 + ((40259 / 31205) : ℂ) * ζ ^ 27 - ((5673 / 31205) : ℂ) * ζ ^ 28 - ((2976 / 6241) : ℂ) * ζ ^ 29 + ((33348 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep08Coefficient03 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep08CoefficientIdentity03 :
    row18_reducedY00_combinationStep08Coefficient03 =
      row18_reducedY00_combinationStep07Coefficient03 +
        row18_reducedY00_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep08Coefficient03 row18_reducedY00_combinationStep07Coefficient03 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep08Coefficient04 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep08CoefficientIdentity04 :
    row18_reducedY00_combinationStep08Coefficient04 =
      row18_reducedY00_combinationStep07Coefficient04 +
        row18_reducedY00_combinationStep08Multiplier *
          (-((3 / 79) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 + ((85 / 316) : ℂ) * ζ ^ 2 + ((1 / 316) : ℂ) * ζ ^ 3 + ((15 / 158) : ℂ) * ζ ^ 5 + ((8 / 79) : ℂ) * ζ ^ 6 + ((35 / 316) : ℂ) * ζ ^ 8 - ((13 / 316) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 11 + ((35 / 316) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((9 / 158) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((53 / 316) : ℂ) * ζ ^ 18 - ((3 / 79) : ℂ) * ζ ^ 21 - ((85 / 316) : ℂ) * ζ ^ 22 - ((19 / 316) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 - ((35 / 316) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 + ((4 / 79) : ℂ) * ζ ^ 30 + ((7 / 158) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep08Coefficient04 row18_reducedY00_combinationStep07Coefficient04 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 (-((3666 / 6241) : ℂ) + ((359 / 395) : ℂ) * ζ ^ 1 - ((28395 / 12482) : ℂ) * ζ ^ 2 - ((18142 / 31205) : ℂ) * ζ ^ 3 + ((61567 / 31205) : ℂ) * ζ ^ 4 - ((48886 / 31205) : ℂ) * ζ ^ 5 - ((7092 / 6241) : ℂ) * ζ ^ 6 + ((135209 / 62410) : ℂ) * ζ ^ 7 - ((10440 / 6241) : ℂ) * ζ ^ 8 - ((32496 / 31205) : ℂ) * ζ ^ 9 + ((20027 / 6241) : ℂ) * ζ ^ 10 - ((26947 / 12482) : ℂ) * ζ ^ 11 - ((24187 / 62410) : ℂ) * ζ ^ 12 + ((172891 / 62410) : ℂ) * ζ ^ 13 - ((70053 / 31205) : ℂ) * ζ ^ 14 + ((40753 / 62410) : ℂ) * ζ ^ 15 + ((80253 / 31205) : ℂ) * ζ ^ 16 - ((143187 / 62410) : ℂ) * ζ ^ 17 + ((34616 / 31205) : ℂ) * ζ ^ 18 + ((18261 / 31205) : ℂ) * ζ ^ 19 - ((57961 / 31205) : ℂ) * ζ ^ 20 + ((85517 / 62410) : ℂ) * ζ ^ 21 + ((6435 / 12482) : ℂ) * ζ ^ 22 - ((30983 / 31205) : ℂ) * ζ ^ 23 + ((15983 / 31205) : ℂ) * ζ ^ 24 + ((921 / 31205) : ℂ) * ζ ^ 25 - ((19067 / 31205) : ℂ) * ζ ^ 26 + ((2615 / 6241) : ℂ) * ζ ^ 27 + ((2391 / 31205) : ℂ) * ζ ^ 28 - ((696 / 31205) : ℂ) * ζ ^ 29 - ((5558 / 31205) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep08Coefficient05 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep08CoefficientIdentity05 :
    row18_reducedY00_combinationStep08Coefficient05 =
      row18_reducedY00_combinationStep07Coefficient05 +
        row18_reducedY00_combinationStep08Multiplier *
          (((69 / 316) : ℂ) - ((9 / 158) : ℂ) * ζ ^ 1 - ((9 / 316) : ℂ) * ζ ^ 2 - ((2 / 79) : ℂ) * ζ ^ 5 - ((39 / 158) : ℂ) * ζ ^ 6 - ((39 / 158) : ℂ) * ζ ^ 8 - ((2 / 79) : ℂ) * ζ ^ 9 + ((45 / 79) : ℂ) * ζ ^ 11 - ((6 / 79) : ℂ) * ζ ^ 12 + ((9 / 158) : ℂ) * ζ ^ 13 + ((85 / 316) : ℂ) * ζ ^ 15 + ((9 / 158) : ℂ) * ζ ^ 17 - ((41 / 316) : ℂ) * ζ ^ 18 + ((13 / 316) : ℂ) * ζ ^ 21 + ((9 / 316) : ℂ) * ζ ^ 22 + ((119 / 316) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 - ((85 / 316) : ℂ) * ζ ^ 27 + ((39 / 158) : ℂ) * ζ ^ 28 - ((9 / 158) : ℂ) * ζ ^ 29 - ((27 / 158) : ℂ) * ζ ^ 30 - ((45 / 79) : ℂ) * ζ ^ 31) := by
  unfold row18_reducedY00_combinationStep08Coefficient05 row18_reducedY00_combinationStep07Coefficient05 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 (((3423 / 6241) : ℂ) + ((24514 / 31205) : ℂ) * ζ ^ 1 + ((285 / 12482) : ℂ) * ζ ^ 2 - ((8556 / 31205) : ℂ) * ζ ^ 3 - ((21876 / 31205) : ℂ) * ζ ^ 4 - ((210537 / 62410) : ℂ) * ζ ^ 5 - ((273 / 6241) : ℂ) * ζ ^ 6 - ((28593 / 62410) : ℂ) * ζ ^ 7 - ((19375 / 12482) : ℂ) * ζ ^ 8 + ((46049 / 62410) : ℂ) * ζ ^ 9 - ((51617 / 31205) : ℂ) * ζ ^ 10 - ((56227 / 31205) : ℂ) * ζ ^ 11 - ((2591 / 62410) : ℂ) * ζ ^ 12 + ((62199 / 62410) : ℂ) * ζ ^ 13 - ((121029 / 62410) : ℂ) * ζ ^ 14 - ((9459 / 62410) : ℂ) * ζ ^ 15 + ((23557 / 62410) : ℂ) * ζ ^ 16 - ((52643 / 62410) : ℂ) * ζ ^ 17 - ((1776 / 6241) : ℂ) * ζ ^ 18 + ((10593 / 6241) : ℂ) * ζ ^ 19 - ((61537 / 62410) : ℂ) * ζ ^ 20 + ((49113 / 31205) : ℂ) * ζ ^ 21 + ((40738 / 31205) : ℂ) * ζ ^ 22 - ((32862 / 31205) : ℂ) * ζ ^ 23 + ((37369 / 31205) : ℂ) * ζ ^ 24 + ((24052 / 31205) : ℂ) * ζ ^ 25 + ((9259 / 31205) : ℂ) * ζ ^ 26 + ((32628 / 31205) : ℂ) * ζ ^ 27 - ((3690 / 6241) : ℂ) * ζ ^ 28 - ((51282 / 31205) : ℂ) * ζ ^ 29 + ((14292 / 6241) : ℂ) * ζ ^ 30)

private def row18_reducedY00_combinationStep08Coefficient06 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep08CoefficientIdentity06 :
    row18_reducedY00_combinationStep08Coefficient06 =
      row18_reducedY00_combinationStep07Coefficient06 +
        row18_reducedY00_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep08Coefficient06 row18_reducedY00_combinationStep07Coefficient06 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep08Coefficient07 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep08CoefficientIdentity07 :
    row18_reducedY00_combinationStep08Coefficient07 =
      row18_reducedY00_combinationStep07Coefficient07 +
        row18_reducedY00_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep08Coefficient07 row18_reducedY00_combinationStep07Coefficient07 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep08Coefficient08 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep08CoefficientIdentity08 :
    row18_reducedY00_combinationStep08Coefficient08 =
      row18_reducedY00_combinationStep07Coefficient08 +
        row18_reducedY00_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep08Coefficient08 row18_reducedY00_combinationStep07Coefficient08 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep08Coefficient09 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep08CoefficientIdentity09 :
    row18_reducedY00_combinationStep08Coefficient09 =
      row18_reducedY00_combinationStep07Coefficient09 +
        row18_reducedY00_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep08Coefficient09 row18_reducedY00_combinationStep07Coefficient09 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep08Coefficient10 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep08CoefficientIdentity10 :
    row18_reducedY00_combinationStep08Coefficient10 =
      row18_reducedY00_combinationStep07Coefficient10 +
        row18_reducedY00_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep08Coefficient10 row18_reducedY00_combinationStep07Coefficient10 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep08Coefficient11 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep08CoefficientIdentity11 :
    row18_reducedY00_combinationStep08Coefficient11 =
      row18_reducedY00_combinationStep07Coefficient11 +
        row18_reducedY00_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep08Coefficient11 row18_reducedY00_combinationStep07Coefficient11 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep08Coefficient12 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep08CoefficientIdentity12 :
    row18_reducedY00_combinationStep08Coefficient12 =
      row18_reducedY00_combinationStep07Coefficient12 +
        row18_reducedY00_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep08Coefficient12 row18_reducedY00_combinationStep07Coefficient12 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep08Coefficient13 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep08CoefficientIdentity13 :
    row18_reducedY00_combinationStep08Coefficient13 =
      row18_reducedY00_combinationStep07Coefficient13 +
        row18_reducedY00_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep08Coefficient13 row18_reducedY00_combinationStep07Coefficient13 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep08Coefficient14 : ℂ :=
  0

private theorem row18_reducedY00_combinationStep08CoefficientIdentity14 :
    row18_reducedY00_combinationStep08Coefficient14 =
      row18_reducedY00_combinationStep07Coefficient14 +
        row18_reducedY00_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep08Coefficient14 row18_reducedY00_combinationStep07Coefficient14 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 0

private def row18_reducedY00_combinationStep08Coefficient15 : ℂ :=
  (-(1 : ℂ))

private theorem row18_reducedY00_combinationStep08CoefficientIdentity15 :
    row18_reducedY00_combinationStep08Coefficient15 =
      row18_reducedY00_combinationStep07Coefficient15 +
        row18_reducedY00_combinationStep08Multiplier *
          0 := by
  unfold row18_reducedY00_combinationStep08Coefficient15 row18_reducedY00_combinationStep07Coefficient15 row18_reducedY00_combinationStep08Multiplier
  close_cyclotomic_row18 0

private theorem row18_reducedY00_combinationStep08
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    (
      (row18_reducedY00_combinationStep08Coefficient00) * Y 0 0
      + (row18_reducedY00_combinationStep08Coefficient01) * Y 0 1
      + (row18_reducedY00_combinationStep08Coefficient02) * Y 1 0
      + (row18_reducedY00_combinationStep08Coefficient03) * Y 1 1
      + (row18_reducedY00_combinationStep08Coefficient04) * Y 2 2
      + (row18_reducedY00_combinationStep08Coefficient05) * Y 2 3
      + (row18_reducedY00_combinationStep08Coefficient06) * Y 3 2
      + (row18_reducedY00_combinationStep08Coefficient07) * Y 3 3
      + (row18_reducedY00_combinationStep08Coefficient08) * Y 4 4
      + (row18_reducedY00_combinationStep08Coefficient09) * Y 4 5
      + (row18_reducedY00_combinationStep08Coefficient10) * Y 5 4
      + (row18_reducedY00_combinationStep08Coefficient11) * Y 5 5
      + (row18_reducedY00_combinationStep08Coefficient12) * Y 6 6
      + (row18_reducedY00_combinationStep08Coefficient13) * Y 6 7
      + (row18_reducedY00_combinationStep08Coefficient14) * Y 7 6
      + (row18_reducedY00_combinationStep08Coefficient15) * Y 7 7) = 0 := by
  have previous :=
    row18_reducedY00_combinationStep07 Y commutesA commutesDiagonal
  have equation :=
    row18_commutatorEquation20
      Y commutesA commutesDiagonal
  rw [
      row18_reducedY00_combinationStep08CoefficientIdentity00,
      row18_reducedY00_combinationStep08CoefficientIdentity01,
      row18_reducedY00_combinationStep08CoefficientIdentity02,
      row18_reducedY00_combinationStep08CoefficientIdentity03,
      row18_reducedY00_combinationStep08CoefficientIdentity04,
      row18_reducedY00_combinationStep08CoefficientIdentity05,
      row18_reducedY00_combinationStep08CoefficientIdentity06,
      row18_reducedY00_combinationStep08CoefficientIdentity07,
      row18_reducedY00_combinationStep08CoefficientIdentity08,
      row18_reducedY00_combinationStep08CoefficientIdentity09,
      row18_reducedY00_combinationStep08CoefficientIdentity10,
      row18_reducedY00_combinationStep08CoefficientIdentity11,
      row18_reducedY00_combinationStep08CoefficientIdentity12,
      row18_reducedY00_combinationStep08CoefficientIdentity13,
      row18_reducedY00_combinationStep08CoefficientIdentity14,
      row18_reducedY00_combinationStep08CoefficientIdentity15]
  linear_combination
    previous
      + row18_reducedY00_combinationStep08Multiplier * equation

theorem row18_reducedY00
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Y 0 0 = Y 7 7 := by
  have reduced :=
    row18_reducedY00_combinationStep08 Y commutesA commutesDiagonal
  simp only [
      row18_reducedY00_combinationStep08Coefficient00,
      row18_reducedY00_combinationStep08Coefficient01,
      row18_reducedY00_combinationStep08Coefficient02,
      row18_reducedY00_combinationStep08Coefficient03,
      row18_reducedY00_combinationStep08Coefficient04,
      row18_reducedY00_combinationStep08Coefficient05,
      row18_reducedY00_combinationStep08Coefficient06,
      row18_reducedY00_combinationStep08Coefficient07,
      row18_reducedY00_combinationStep08Coefficient08,
      row18_reducedY00_combinationStep08Coefficient09,
      row18_reducedY00_combinationStep08Coefficient10,
      row18_reducedY00_combinationStep08Coefficient11,
      row18_reducedY00_combinationStep08Coefficient12,
      row18_reducedY00_combinationStep08Coefficient13,
      row18_reducedY00_combinationStep08Coefficient14,
      row18_reducedY00_combinationStep08Coefficient15] at reduced
  linear_combination reduced


end InductiveMcKay
end McKayConjecture
