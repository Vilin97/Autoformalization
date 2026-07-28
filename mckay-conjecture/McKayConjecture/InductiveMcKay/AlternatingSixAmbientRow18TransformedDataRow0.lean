/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalDataCore

/-!
# Transformed-generator data for ambient row 18, output row 0

This generated module checks the scalar products in output row 0.
It imports the preceding output-row module to serialize clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private theorem row18_transformedGeneratorA_term_0_0_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 0 =
      (((125 / 3476) : ℂ) - ((1183 / 17380) : ℂ) * ζ ^ 1 + ((19 / 1738) : ℂ) * ζ ^ 2 + ((371 / 4345) : ℂ) * ζ ^ 3 - ((146 / 4345) : ℂ) * ζ ^ 5 - ((249 / 1738) : ℂ) * ζ ^ 6 + ((185 / 869) : ℂ) * ζ ^ 8 - ((141 / 4345) : ℂ) * ζ ^ 9 + ((1113 / 17380) : ℂ) * ζ ^ 11 - ((29 / 869) : ℂ) * ζ ^ 12 + ((1183 / 17380) : ℂ) * ζ ^ 13 - ((1883 / 8690) : ℂ) * ζ ^ 15 + ((1183 / 17380) : ℂ) * ζ ^ 17 + ((293 / 3476) : ℂ) * ζ ^ 18 + ((1673 / 8690) : ℂ) * ζ ^ 21 - ((19 / 1738) : ℂ) * ζ ^ 22 + ((195 / 1738) : ℂ) * ζ ^ 24 - ((599 / 17380) : ℂ) * ζ ^ 25 - ((1247 / 17380) : ℂ) * ζ ^ 27 - ((185 / 869) : ℂ) * ζ ^ 28 - ((1183 / 17380) : ℂ) * ζ ^ 29 - ((731 / 3476) : ℂ) * ζ ^ 30 - ((1113 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1633 / 17380) : ℂ) + ((623 / 4345) : ℂ) * ζ ^ 1 - ((241 / 3476) : ℂ) * ζ ^ 2 + ((43 / 8690) : ℂ) * ζ ^ 3 + ((411 / 3476) : ℂ) * ζ ^ 4 - ((651 / 8690) : ℂ) * ζ ^ 5 + ((1739 / 8690) : ℂ) * ζ ^ 6 - ((46 / 4345) : ℂ) * ζ ^ 7 - ((794 / 4345) : ℂ) * ζ ^ 8 - ((977 / 8690) : ℂ) * ζ ^ 9 - ((1071 / 17380) : ℂ) * ζ ^ 10 - ((3479 / 8690) : ℂ) * ζ ^ 11 + ((147 / 4345) : ℂ) * ζ ^ 12 - ((697 / 17380) : ℂ) * ζ ^ 13 + ((667 / 17380) : ℂ) * ζ ^ 14 + ((2613 / 8690) : ℂ) * ζ ^ 15 - ((1649 / 17380) : ℂ) * ζ ^ 16 - ((114 / 4345) : ℂ) * ζ ^ 17 + ((2683 / 17380) : ℂ) * ζ ^ 18 - ((113 / 1738) : ℂ) * ζ ^ 19 + ((1857 / 17380) : ℂ) * ζ ^ 20 - ((2259 / 17380) : ℂ) * ζ ^ 21 + ((1059 / 17380) : ℂ) * ζ ^ 22 + ((163 / 1580) : ℂ) * ζ ^ 23 - ((169 / 1738) : ℂ) * ζ ^ 24 + ((2759 / 17380) : ℂ) * ζ ^ 25 - ((187 / 1580) : ℂ) * ζ ^ 26 + ((2377 / 8690) : ℂ) * ζ ^ 27 + ((199 / 4345) : ℂ) * ζ ^ 28 - ((741 / 17380) : ℂ) * ζ ^ 29 + ((2337 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_0_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 0 =
      (((1883 / 17380) : ℂ) - ((309 / 4345) : ℂ) * ζ ^ 1 + ((207 / 1738) : ℂ) * ζ ^ 2 + ((239 / 8690) : ℂ) * ζ ^ 3 - ((1269 / 8690) : ℂ) * ζ ^ 5 + ((285 / 1738) : ℂ) * ζ ^ 6 - ((2589 / 17380) : ℂ) * ζ ^ 8 - ((893 / 17380) : ℂ) * ζ ^ 9 - ((27 / 8690) : ℂ) * ζ ^ 11 - ((487 / 17380) : ℂ) * ζ ^ 12 + ((309 / 4345) : ℂ) * ζ ^ 13 + ((467 / 4345) : ℂ) * ζ ^ 15 + ((309 / 4345) : ℂ) * ζ ^ 17 - ((5 / 44) : ℂ) * ζ ^ 18 - ((2503 / 17380) : ℂ) * ζ ^ 21 - ((207 / 1738) : ℂ) * ζ ^ 22 + ((1361 / 17380) : ℂ) * ζ ^ 24 + ((651 / 8690) : ℂ) * ζ ^ 25 + ((153 / 8690) : ℂ) * ζ ^ 27 + ((2589 / 17380) : ℂ) * ζ ^ 28 - ((309 / 4345) : ℂ) * ζ ^ 29 - ((139 / 3476) : ℂ) * ζ ^ 30 + ((27 / 8690) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((427 / 3476) : ℂ) + ((426 / 4345) : ℂ) * ζ ^ 1 - ((435 / 3476) : ℂ) * ζ ^ 2 - ((1069 / 17380) : ℂ) * ζ ^ 3 + ((505 / 3476) : ℂ) * ζ ^ 4 + ((1179 / 17380) : ℂ) * ζ ^ 5 - ((1449 / 17380) : ℂ) * ζ ^ 6 + ((7 / 790) : ℂ) * ζ ^ 7 + ((1063 / 17380) : ℂ) * ζ ^ 8 + ((139 / 1580) : ℂ) * ζ ^ 9 - ((997 / 17380) : ℂ) * ζ ^ 10 - ((999 / 17380) : ℂ) * ζ ^ 11 + ((31 / 4345) : ℂ) * ζ ^ 12 - ((591 / 17380) : ℂ) * ζ ^ 13 - ((142 / 4345) : ℂ) * ζ ^ 14 - ((401 / 8690) : ℂ) * ζ ^ 15 - ((31 / 3476) : ℂ) * ζ ^ 16 + ((83 / 8690) : ℂ) * ζ ^ 17 + ((518 / 4345) : ℂ) * ζ ^ 18 - ((3 / 17380) : ℂ) * ζ ^ 19 - ((63 / 1738) : ℂ) * ζ ^ 20 + ((302 / 4345) : ℂ) * ζ ^ 21 + ((897 / 17380) : ℂ) * ζ ^ 22 - ((141 / 8690) : ℂ) * ζ ^ 23 - ((1123 / 17380) : ℂ) * ζ ^ 24 - ((21 / 1580) : ℂ) * ζ ^ 25 + ((179 / 8690) : ℂ) * ζ ^ 26 - ((397 / 17380) : ℂ) * ζ ^ 27 - ((117 / 4345) : ℂ) * ζ ^ 28 + ((57 / 4345) : ℂ) * ζ ^ 29 + ((57 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_0_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 0 =
      (-((50 / 869) : ℂ) - ((1211 / 17380) : ℂ) * ζ ^ 1 - ((3629 / 17380) : ℂ) * ζ ^ 2 - ((833 / 17380) : ℂ) * ζ ^ 3 - ((1223 / 17380) : ℂ) * ζ ^ 5 - ((1104 / 4345) : ℂ) * ζ ^ 6 + ((829 / 3476) : ℂ) * ζ ^ 8 + ((433 / 4345) : ℂ) * ζ ^ 9 + ((2689 / 17380) : ℂ) * ζ ^ 11 + ((861 / 3476) : ℂ) * ζ ^ 12 + ((1211 / 17380) : ℂ) * ζ ^ 13 - ((923 / 17380) : ℂ) * ζ ^ 15 + ((1211 / 17380) : ℂ) * ζ ^ 17 + ((4177 / 17380) : ℂ) * ζ ^ 18 + ((2787 / 17380) : ℂ) * ζ ^ 21 + ((3629 / 17380) : ℂ) * ζ ^ 22 - ((389 / 1738) : ℂ) * ζ ^ 24 + ((3 / 4345) : ℂ) * ζ ^ 25 - ((3211 / 17380) : ℂ) * ζ ^ 27 - ((829 / 3476) : ℂ) * ζ ^ 28 - ((1211 / 17380) : ℂ) * ζ ^ 29 - ((212 / 4345) : ℂ) * ζ ^ 30 - ((2689 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((50 / 869) : ℂ) + ((1117 / 8690) : ℂ) * ζ ^ 1 + ((1069 / 3476) : ℂ) * ζ ^ 2 + ((2549 / 17380) : ℂ) * ζ ^ 3 - ((43 / 17380) : ℂ) * ζ ^ 4 + ((9 / 1738) : ℂ) * ζ ^ 5 + ((1151 / 8690) : ℂ) * ζ ^ 6 - ((359 / 17380) : ℂ) * ζ ^ 7 - ((663 / 3476) : ℂ) * ζ ^ 8 - ((83 / 316) : ℂ) * ζ ^ 9 - ((611 / 3476) : ℂ) * ζ ^ 10 - ((1431 / 8690) : ℂ) * ζ ^ 11 - ((747 / 17380) : ℂ) * ζ ^ 12 + ((86 / 869) : ℂ) * ζ ^ 13 + ((3103 / 17380) : ℂ) * ζ ^ 14 + ((1118 / 4345) : ℂ) * ζ ^ 15 + ((183 / 4345) : ℂ) * ζ ^ 16 - ((673 / 17380) : ℂ) * ζ ^ 17 - ((12 / 79) : ℂ) * ζ ^ 18 - ((3053 / 17380) : ℂ) * ζ ^ 19 - ((1071 / 4345) : ℂ) * ζ ^ 20 - ((1487 / 8690) : ℂ) * ζ ^ 21 - ((387 / 8690) : ℂ) * ζ ^ 22 + ((57 / 869) : ℂ) * ζ ^ 23 + ((225 / 1738) : ℂ) * ζ ^ 24 + ((39 / 395) : ℂ) * ζ ^ 25 + ((777 / 17380) : ℂ) * ζ ^ 26 + ((3 / 395) : ℂ) * ζ ^ 27 - ((18 / 4345) : ℂ) * ζ ^ 28 - ((18 / 4345) : ℂ) * ζ ^ 29 - ((9 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_0_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 0 =
      (-((63 / 790) : ℂ) + ((31 / 316) : ℂ) * ζ ^ 1 + ((379 / 1580) : ℂ) * ζ ^ 2 - ((27 / 395) : ℂ) * ζ ^ 3 + ((63 / 316) : ℂ) * ζ ^ 5 + ((84 / 395) : ℂ) * ζ ^ 6 - ((231 / 790) : ℂ) * ζ ^ 8 + ((7 / 79) : ℂ) * ζ ^ 9 - ((113 / 790) : ℂ) * ζ ^ 11 - ((73 / 790) : ℂ) * ζ ^ 12 - ((31 / 316) : ℂ) * ζ ^ 13 + ((347 / 1580) : ℂ) * ζ ^ 15 - ((31 / 316) : ℂ) * ζ ^ 17 + ((43 / 1580) : ℂ) * ζ ^ 18 - ((30 / 79) : ℂ) * ζ ^ 21 - ((379 / 1580) : ℂ) * ζ ^ 22 - ((3 / 20) : ℂ) * ζ ^ 24 - ((8 / 79) : ℂ) * ζ ^ 25 + ((71 / 395) : ℂ) * ζ ^ 27 + ((231 / 790) : ℂ) * ζ ^ 28 + ((31 / 316) : ℂ) * ζ ^ 29 + ((42 / 395) : ℂ) * ζ ^ 30 + ((113 / 790) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((21 / 158) : ℂ) + ((147 / 1580) : ℂ) * ζ ^ 1 - ((67 / 316) : ℂ) * ζ ^ 2 - ((1 / 158) : ℂ) * ζ ^ 3 + ((173 / 1580) : ℂ) * ζ ^ 4 - ((19 / 790) : ℂ) * ζ ^ 5 - ((7 / 790) : ℂ) * ζ ^ 6 - ((11 / 158) : ℂ) * ζ ^ 7 + ((271 / 1580) : ℂ) * ζ ^ 8 - ((19 / 395) : ℂ) * ζ ^ 9 - ((71 / 1580) : ℂ) * ζ ^ 10 + ((169 / 790) : ℂ) * ζ ^ 11 + ((331 / 1580) : ℂ) * ζ ^ 12 - ((23 / 395) : ℂ) * ζ ^ 13 - ((29 / 158) : ℂ) * ζ ^ 14 - ((127 / 395) : ℂ) * ζ ^ 15 - ((389 / 1580) : ℂ) * ζ ^ 16 - ((139 / 790) : ℂ) * ζ ^ 17 + ((27 / 1580) : ℂ) * ζ ^ 18 + ((123 / 395) : ℂ) * ζ ^ 19 + ((47 / 158) : ℂ) * ζ ^ 20 + ((53 / 158) : ℂ) * ζ ^ 21 + ((191 / 790) : ℂ) * ζ ^ 22 - ((23 / 790) : ℂ) * ζ ^ 23 - ((66 / 395) : ℂ) * ζ ^ 24 - ((141 / 790) : ℂ) * ζ ^ 25 - ((86 / 395) : ℂ) * ζ ^ 26 - ((54 / 395) : ℂ) * ζ ^ 27 - ((31 / 395) : ℂ) * ζ ^ 28 + ((32 / 395) : ℂ) * ζ ^ 29 + ((44 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_0_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 0 =
      (-((8 / 4345) : ℂ) + ((427 / 3476) : ℂ) * ζ ^ 1 - ((19 / 869) : ℂ) * ζ ^ 2 - ((309 / 4345) : ℂ) * ζ ^ 3 + ((339 / 1738) : ℂ) * ζ ^ 5 + ((18 / 869) : ℂ) * ζ ^ 6 + ((269 / 4345) : ℂ) * ζ ^ 8 - ((25 / 869) : ℂ) * ζ ^ 9 + ((939 / 8690) : ℂ) * ζ ^ 11 - ((1877 / 17380) : ℂ) * ζ ^ 12 - ((427 / 3476) : ℂ) * ζ ^ 13 + ((369 / 17380) : ℂ) * ζ ^ 15 - ((427 / 3476) : ℂ) * ζ ^ 17 - ((443 / 3476) : ℂ) * ζ ^ 18 - ((51 / 1738) : ℂ) * ζ ^ 21 + ((19 / 869) : ℂ) * ζ ^ 22 + ((893 / 8690) : ℂ) * ζ ^ 24 - ((251 / 3476) : ℂ) * ζ ^ 25 - ((41 / 8690) : ℂ) * ζ ^ 27 - ((269 / 4345) : ℂ) * ζ ^ 28 + ((427 / 3476) : ℂ) * ζ ^ 29 + ((269 / 1738) : ℂ) * ζ ^ 30 - ((939 / 8690) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((71 / 4345) : ℂ) - ((90 / 869) : ℂ) * ζ ^ 1 + ((273 / 17380) : ℂ) * ζ ^ 2 + ((357 / 8690) : ℂ) * ζ ^ 3 - ((62 / 4345) : ℂ) * ζ ^ 4 - ((46 / 869) : ℂ) * ζ ^ 5 - ((13 / 1738) : ℂ) * ζ ^ 6 - ((177 / 3476) : ℂ) * ζ ^ 7 - ((669 / 17380) : ℂ) * ζ ^ 8 + ((58 / 869) : ℂ) * ζ ^ 9 + ((151 / 3476) : ℂ) * ζ ^ 10 - ((459 / 8690) : ℂ) * ζ ^ 11 + ((1751 / 17380) : ℂ) * ζ ^ 12 - ((351 / 17380) : ℂ) * ζ ^ 13 - ((831 / 17380) : ℂ) * ζ ^ 14 + ((29 / 220) : ℂ) * ζ ^ 15 - ((236 / 4345) : ℂ) * ζ ^ 16 - ((433 / 8690) : ℂ) * ζ ^ 17 + ((499 / 8690) : ℂ) * ζ ^ 18 - ((623 / 4345) : ℂ) * ζ ^ 19 - ((91 / 4345) : ℂ) * ζ ^ 20 + ((461 / 8690) : ℂ) * ζ ^ 21 - ((335 / 3476) : ℂ) * ζ ^ 22 + ((9 / 110) : ℂ) * ζ ^ 23 + ((153 / 17380) : ℂ) * ζ ^ 24 - ((2 / 4345) : ℂ) * ζ ^ 25 + ((321 / 8690) : ℂ) * ζ ^ 26 - ((9 / 4345) : ℂ) * ζ ^ 27 + ((14 / 4345) : ℂ) * ζ ^ 28 - ((7 / 3476) : ℂ) * ζ ^ 29 - ((49 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_0_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 0 =
      (((1 / 22) : ℂ) + ((1 / 44) : ℂ) * ζ ^ 1 + ((3 / 44) : ℂ) * ζ ^ 3 - ((9 / 44) : ℂ) * ζ ^ 5 - ((1 / 11) : ℂ) * ζ ^ 8 - ((5 / 44) : ℂ) * ζ ^ 9 - ((3 / 22) : ℂ) * ζ ^ 11 - ((3 / 44) : ℂ) * ζ ^ 12 - ((1 / 44) : ℂ) * ζ ^ 13 + ((1 / 44) : ℂ) * ζ ^ 15 - ((1 / 44) : ℂ) * ζ ^ 17 - ((1 / 4) : ℂ) * ζ ^ 18 + ((7 / 44) : ℂ) * ζ ^ 21 + ((2 / 11) : ℂ) * ζ ^ 24 + ((5 / 22) : ℂ) * ζ ^ 25 + ((1 / 44) : ℂ) * ζ ^ 27 + ((1 / 11) : ℂ) * ζ ^ 28 + ((1 / 44) : ℂ) * ζ ^ 29 + ((3 / 22) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_0_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 0 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_0_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 0 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_0_0 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        0 0 =
      alternatingSixAmbientRow18TransformedGeneratorA
        0 0 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_0_0_0,
      row18_transformedGeneratorA_term_0_0_1,
      row18_transformedGeneratorA_term_0_0_2,
      row18_transformedGeneratorA_term_0_0_3,
      row18_transformedGeneratorA_term_0_0_4,
      row18_transformedGeneratorA_term_0_0_5,
      row18_transformedGeneratorA_term_0_0_6,
      row18_transformedGeneratorA_term_0_0_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_1_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 1 =
      (-((1061 / 17380) : ℂ) - ((1763 / 17380) : ℂ) * ζ ^ 1 - ((2067 / 8690) : ℂ) * ζ ^ 2 + ((1369 / 8690) : ℂ) * ζ ^ 3 + ((2043 / 8690) : ℂ) * ζ ^ 5 + ((421 / 4345) : ℂ) * ζ ^ 6 + ((813 / 17380) : ℂ) * ζ ^ 8 + ((1134 / 4345) : ℂ) * ζ ^ 9 - ((999 / 17380) : ℂ) * ζ ^ 11 - ((929 / 4345) : ℂ) * ζ ^ 12 + ((1763 / 17380) : ℂ) * ζ ^ 13 - ((3447 / 17380) : ℂ) * ζ ^ 15 + ((1763 / 17380) : ℂ) * ζ ^ 17 + ((3437 / 17380) : ℂ) * ζ ^ 18 - ((577 / 8690) : ℂ) * ζ ^ 21 + ((2067 / 8690) : ℂ) * ζ ^ 22 + ((563 / 17380) : ℂ) * ζ ^ 24 - ((5849 / 17380) : ℂ) * ζ ^ 25 - ((111 / 4345) : ℂ) * ζ ^ 27 - ((813 / 17380) : ℂ) * ζ ^ 28 - ((1763 / 17380) : ℂ) * ζ ^ 29 - ((457 / 4345) : ℂ) * ζ ^ 30 + ((999 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((247 / 8690) : ℂ) + ((787 / 8690) : ℂ) * ζ ^ 1 + ((2459 / 8690) : ℂ) * ζ ^ 2 - ((31 / 395) : ℂ) * ζ ^ 3 - ((413 / 8690) : ℂ) * ζ ^ 4 - ((7691 / 17380) : ℂ) * ζ ^ 5 - ((217 / 869) : ℂ) * ζ ^ 6 + ((733 / 8690) : ℂ) * ζ ^ 7 + ((853 / 8690) : ℂ) * ζ ^ 8 + ((31 / 1580) : ℂ) * ζ ^ 9 + ((2697 / 17380) : ℂ) * ζ ^ 10 - ((757 / 3476) : ℂ) * ζ ^ 11 + ((3089 / 17380) : ℂ) * ζ ^ 12 + ((3347 / 17380) : ℂ) * ζ ^ 13 - ((2637 / 8690) : ℂ) * ζ ^ 14 + ((1667 / 8690) : ℂ) * ζ ^ 15 - ((199 / 869) : ℂ) * ζ ^ 16 - ((3123 / 17380) : ℂ) * ζ ^ 17 - ((939 / 4345) : ℂ) * ζ ^ 18 - ((46 / 4345) : ℂ) * ζ ^ 19 + ((1162 / 4345) : ℂ) * ζ ^ 20 + ((568 / 4345) : ℂ) * ζ ^ 21 + ((1851 / 8690) : ℂ) * ζ ^ 22 + ((71 / 8690) : ℂ) * ζ ^ 23 - ((49 / 869) : ℂ) * ζ ^ 24 + ((641 / 17380) : ℂ) * ζ ^ 25 - ((371 / 1580) : ℂ) * ζ ^ 26 + ((527 / 3476) : ℂ) * ζ ^ 27 - ((487 / 17380) : ℂ) * ζ ^ 28 - ((399 / 8690) : ℂ) * ζ ^ 29 + ((2109 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_1_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 1 =
      (-((1807 / 4345) : ℂ) - ((21 / 110) : ℂ) * ζ ^ 1 + ((423 / 1738) : ℂ) * ζ ^ 2 + ((481 / 17380) : ℂ) * ζ ^ 3 - ((5679 / 17380) : ℂ) * ζ ^ 5 + ((115 / 3476) : ℂ) * ζ ^ 6 + ((2756 / 4345) : ℂ) * ζ ^ 8 - ((857 / 8690) : ℂ) * ζ ^ 9 - ((1412 / 4345) : ℂ) * ζ ^ 11 + ((3771 / 8690) : ℂ) * ζ ^ 12 + ((21 / 110) : ℂ) * ζ ^ 13 - ((311 / 4345) : ℂ) * ζ ^ 15 + ((21 / 110) : ℂ) * ζ ^ 17 - ((987 / 3476) : ℂ) * ζ ^ 18 + ((9851 / 17380) : ℂ) * ζ ^ 21 - ((423 / 1738) : ℂ) * ζ ^ 22 - ((8001 / 17380) : ℂ) * ζ ^ 24 + ((2361 / 17380) : ℂ) * ζ ^ 25 + ((4377 / 17380) : ℂ) * ζ ^ 27 - ((2756 / 4345) : ℂ) * ζ ^ 28 - ((21 / 110) : ℂ) * ζ ^ 29 - ((87 / 3476) : ℂ) * ζ ^ 30 + ((1412 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((7123 / 17380) : ℂ) + ((936 / 4345) : ℂ) * ζ ^ 1 - ((5163 / 17380) : ℂ) * ζ ^ 2 - ((256 / 4345) : ℂ) * ζ ^ 3 - ((2147 / 8690) : ℂ) * ζ ^ 4 + ((801 / 17380) : ℂ) * ζ ^ 5 + ((1103 / 8690) : ℂ) * ζ ^ 6 + ((94 / 4345) : ℂ) * ζ ^ 7 - ((6023 / 17380) : ℂ) * ζ ^ 8 + ((13 / 3476) : ℂ) * ζ ^ 9 + ((1271 / 17380) : ℂ) * ζ ^ 10 + ((5201 / 17380) : ℂ) * ζ ^ 11 - ((4291 / 17380) : ℂ) * ζ ^ 12 - ((161 / 8690) : ℂ) * ζ ^ 13 + ((1203 / 17380) : ℂ) * ζ ^ 14 + ((221 / 8690) : ℂ) * ζ ^ 15 + ((909 / 17380) : ℂ) * ζ ^ 16 + ((31 / 395) : ℂ) * ζ ^ 17 - ((29 / 3476) : ℂ) * ζ ^ 18 - ((348 / 4345) : ℂ) * ζ ^ 19 - ((2021 / 17380) : ℂ) * ζ ^ 20 - ((2897 / 17380) : ℂ) * ζ ^ 21 - ((21 / 1580) : ℂ) * ζ ^ 22 + ((657 / 8690) : ℂ) * ζ ^ 23 + ((2987 / 17380) : ℂ) * ζ ^ 24 + ((73 / 8690) : ℂ) * ζ ^ 25 - ((999 / 8690) : ℂ) * ζ ^ 26 - ((151 / 8690) : ℂ) * ζ ^ 27 + ((3017 / 17380) : ℂ) * ζ ^ 28 + ((171 / 17380) : ℂ) * ζ ^ 29 - ((342 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_1_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 1 =
      (-((436 / 4345) : ℂ) + ((29 / 316) : ℂ) * ζ ^ 1 + ((437 / 3476) : ℂ) * ζ ^ 2 + ((1901 / 8690) : ℂ) * ζ ^ 3 + ((39 / 316) : ℂ) * ζ ^ 5 - ((75 / 1738) : ℂ) * ζ ^ 6 - ((483 / 17380) : ℂ) * ζ ^ 8 + ((6 / 79) : ℂ) * ζ ^ 9 - ((3061 / 17380) : ℂ) * ζ ^ 11 - ((721 / 4345) : ℂ) * ζ ^ 12 - ((29 / 316) : ℂ) * ζ ^ 13 - ((2843 / 17380) : ℂ) * ζ ^ 15 - ((29 / 316) : ℂ) * ζ ^ 17 + ((427 / 3476) : ℂ) * ζ ^ 18 - ((27 / 158) : ℂ) * ζ ^ 21 - ((437 / 3476) : ℂ) * ζ ^ 22 - ((1062 / 4345) : ℂ) * ζ ^ 24 - ((5 / 158) : ℂ) * ζ ^ 25 + ((7409 / 17380) : ℂ) * ζ ^ 27 + ((483 / 17380) : ℂ) * ζ ^ 28 + ((29 / 316) : ℂ) * ζ ^ 29 + ((53 / 869) : ℂ) * ζ ^ 30 + ((3061 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((1647 / 8690) : ℂ) - ((39 / 1738) : ℂ) * ζ ^ 1 - ((166 / 869) : ℂ) * ζ ^ 2 - ((1107 / 4345) : ℂ) * ζ ^ 3 - ((169 / 869) : ℂ) * ζ ^ 4 + ((327 / 17380) : ℂ) * ζ ^ 5 + ((587 / 8690) : ℂ) * ζ ^ 6 + ((313 / 17380) : ℂ) * ζ ^ 7 + ((1527 / 17380) : ℂ) * ζ ^ 8 - ((1829 / 8690) : ℂ) * ζ ^ 9 - ((69 / 1738) : ℂ) * ζ ^ 10 + ((291 / 4345) : ℂ) * ζ ^ 11 + ((123 / 395) : ℂ) * ζ ^ 12 + ((291 / 3476) : ℂ) * ζ ^ 13 + ((1099 / 17380) : ℂ) * ζ ^ 14 - ((43 / 869) : ℂ) * ζ ^ 15 - ((403 / 17380) : ℂ) * ζ ^ 16 - ((313 / 4345) : ℂ) * ζ ^ 17 - ((2481 / 17380) : ℂ) * ζ ^ 18 - ((276 / 4345) : ℂ) * ζ ^ 19 + ((27 / 316) : ℂ) * ζ ^ 20 - ((321 / 8690) : ℂ) * ζ ^ 21 + ((555 / 3476) : ℂ) * ζ ^ 22 + ((441 / 1580) : ℂ) * ζ ^ 23 + ((1178 / 4345) : ℂ) * ζ ^ 24 - ((303 / 17380) : ℂ) * ζ ^ 25 - ((699 / 4345) : ℂ) * ζ ^ 26 - ((519 / 3476) : ℂ) * ζ ^ 27 - ((33 / 316) : ℂ) * ζ ^ 28 + ((123 / 8690) : ℂ) * ζ ^ 29 + ((51 / 1738) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_1_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 1 =
      (((81 / 790) : ℂ) - ((21 / 79) : ℂ) * ζ ^ 1 - ((98 / 395) : ℂ) * ζ ^ 2 - ((261 / 790) : ℂ) * ζ ^ 3 - ((73 / 316) : ℂ) * ζ ^ 5 - ((139 / 790) : ℂ) * ζ ^ 6 - ((53 / 790) : ℂ) * ζ ^ 8 + ((2 / 79) : ℂ) * ζ ^ 9 + ((214 / 395) : ℂ) * ζ ^ 11 - ((193 / 1580) : ℂ) * ζ ^ 12 + ((21 / 79) : ℂ) * ζ ^ 13 + ((443 / 1580) : ℂ) * ζ ^ 15 + ((21 / 79) : ℂ) * ζ ^ 17 - ((61 / 395) : ℂ) * ζ ^ 18 + ((17 / 79) : ℂ) * ζ ^ 21 + ((98 / 395) : ℂ) * ζ ^ 22 + ((629 / 1580) : ℂ) * ζ ^ 24 - ((11 / 316) : ℂ) * ζ ^ 25 - ((619 / 1580) : ℂ) * ζ ^ 27 + ((53 / 790) : ℂ) * ζ ^ 28 - ((21 / 79) : ℂ) * ζ ^ 29 - ((49 / 1580) : ℂ) * ζ ^ 30 - ((214 / 395) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((51 / 395) : ℂ) + ((133 / 790) : ℂ) * ζ ^ 1 + ((7 / 79) : ℂ) * ζ ^ 2 + ((833 / 1580) : ℂ) * ζ ^ 3 - ((159 / 1580) : ℂ) * ζ ^ 4 + ((1 / 20) : ℂ) * ζ ^ 5 - ((291 / 790) : ℂ) * ζ ^ 6 - ((397 / 1580) : ℂ) * ζ ^ 7 - ((18 / 395) : ℂ) * ζ ^ 8 + ((77 / 316) : ℂ) * ζ ^ 9 + ((73 / 316) : ℂ) * ζ ^ 10 - ((37 / 158) : ℂ) * ζ ^ 11 - ((219 / 790) : ℂ) * ζ ^ 12 + ((171 / 1580) : ℂ) * ζ ^ 13 + ((131 / 1580) : ℂ) * ζ ^ 14 + ((6 / 395) : ℂ) * ζ ^ 15 - ((16 / 395) : ℂ) * ζ ^ 16 + ((117 / 1580) : ℂ) * ζ ^ 17 + ((107 / 316) : ℂ) * ζ ^ 18 + ((187 / 790) : ℂ) * ζ ^ 19 + ((319 / 1580) : ℂ) * ζ ^ 20 - ((15 / 158) : ℂ) * ζ ^ 21 - ((77 / 158) : ℂ) * ζ ^ 22 - ((441 / 790) : ℂ) * ζ ^ 23 - ((143 / 395) : ℂ) * ζ ^ 24 - ((13 / 158) : ℂ) * ζ ^ 25 + ((181 / 395) : ℂ) * ζ ^ 26 + ((341 / 790) : ℂ) * ζ ^ 27 + ((102 / 395) : ℂ) * ζ ^ 28 - ((34 / 395) : ℂ) * ζ ^ 29 - ((87 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_1_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 1 =
      (((2319 / 17380) : ℂ) + ((1049 / 8690) : ℂ) * ζ ^ 1 - ((1261 / 17380) : ℂ) * ζ ^ 2 + ((2569 / 17380) : ℂ) * ζ ^ 3 + ((2087 / 8690) : ℂ) * ζ ^ 5 - ((1187 / 8690) : ℂ) * ζ ^ 6 - ((5727 / 17380) : ℂ) * ζ ^ 8 - ((493 / 8690) : ℂ) * ζ ^ 9 + ((1363 / 17380) : ℂ) * ζ ^ 11 - ((4111 / 17380) : ℂ) * ζ ^ 12 - ((1049 / 8690) : ℂ) * ζ ^ 13 + ((189 / 17380) : ℂ) * ζ ^ 15 - ((1049 / 8690) : ℂ) * ζ ^ 17 - ((168 / 4345) : ℂ) * ζ ^ 18 - ((4091 / 17380) : ℂ) * ζ ^ 21 + ((1261 / 17380) : ℂ) * ζ ^ 22 + ((2423 / 17380) : ℂ) * ζ ^ 24 - ((519 / 4345) : ℂ) * ζ ^ 25 - ((3067 / 17380) : ℂ) * ζ ^ 27 + ((5727 / 17380) : ℂ) * ζ ^ 28 + ((1049 / 8690) : ℂ) * ζ ^ 29 + ((1173 / 17380) : ℂ) * ζ ^ 30 - ((1363 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1563 / 17380) : ℂ) - ((2017 / 17380) : ℂ) * ζ ^ 1 + ((2129 / 17380) : ℂ) * ζ ^ 2 - ((2709 / 17380) : ℂ) * ζ ^ 3 + ((378 / 4345) : ℂ) * ζ ^ 4 - ((489 / 17380) : ℂ) * ζ ^ 5 + ((606 / 4345) : ℂ) * ζ ^ 6 + ((1041 / 4345) : ℂ) * ζ ^ 7 + ((1019 / 3476) : ℂ) * ζ ^ 8 + ((1773 / 17380) : ℂ) * ζ ^ 9 - ((723 / 8690) : ℂ) * ζ ^ 10 - ((3153 / 17380) : ℂ) * ζ ^ 11 - ((4109 / 17380) : ℂ) * ζ ^ 12 - ((23 / 869) : ℂ) * ζ ^ 13 + ((2161 / 17380) : ℂ) * ζ ^ 14 + ((3111 / 17380) : ℂ) * ζ ^ 15 + ((257 / 1738) : ℂ) * ζ ^ 16 + ((34 / 4345) : ℂ) * ζ ^ 17 - ((579 / 3476) : ℂ) * ζ ^ 18 - ((3373 / 17380) : ℂ) * ζ ^ 19 - ((29 / 1580) : ℂ) * ζ ^ 20 + ((4303 / 17380) : ℂ) * ζ ^ 21 + ((193 / 790) : ℂ) * ζ ^ 22 + ((307 / 8690) : ℂ) * ζ ^ 23 - ((1491 / 17380) : ℂ) * ζ ^ 24 - ((3161 / 17380) : ℂ) * ζ ^ 25 - ((423 / 1738) : ℂ) * ζ ^ 26 - ((1153 / 17380) : ℂ) * ζ ^ 27 + ((39 / 4345) : ℂ) * ζ ^ 28 + ((91 / 4345) : ℂ) * ζ ^ 29 + ((91 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_1_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 1 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_1_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 1 =
      (-((23 / 220) : ℂ) + ((41 / 220) : ℂ) * ζ ^ 1 + ((9 / 110) : ℂ) * ζ ^ 2 - ((17 / 220) : ℂ) * ζ ^ 5 + ((21 / 110) : ℂ) * ζ ^ 6 + ((6 / 55) : ℂ) * ζ ^ 8 - ((7 / 220) : ℂ) * ζ ^ 9 + ((31 / 110) : ℂ) * ζ ^ 12 - ((41 / 220) : ℂ) * ζ ^ 13 - ((41 / 220) : ℂ) * ζ ^ 17 + ((1 / 220) : ℂ) * ζ ^ 18 - ((8 / 55) : ℂ) * ζ ^ 21 - ((9 / 110) : ℂ) * ζ ^ 22 + ((29 / 220) : ℂ) * ζ ^ 24 + ((29 / 110) : ℂ) * ζ ^ 25 - ((6 / 55) : ℂ) * ζ ^ 28 + ((41 / 220) : ℂ) * ζ ^ 29 + ((13 / 110) : ℂ) * ζ ^ 30) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((23 / 220) : ℂ) - ((7 / 220) : ℂ) * ζ ^ 1 - ((17 / 110) : ℂ) * ζ ^ 2 + ((39 / 220) : ℂ) * ζ ^ 4 + ((29 / 110) : ℂ) * ζ ^ 5 - ((67 / 220) : ℂ) * ζ ^ 6 - ((1 / 220) : ℂ) * ζ ^ 8 - ((53 / 220) : ℂ) * ζ ^ 9 + ((4 / 55) : ℂ) * ζ ^ 10 - ((129 / 220) : ℂ) * ζ ^ 12 - ((13 / 110) : ℂ) * ζ ^ 14 + ((7 / 220) : ℂ) * ζ ^ 17 + ((3 / 44) : ℂ) * ζ ^ 18 - ((39 / 220) : ℂ) * ζ ^ 20 - ((9 / 220) : ℂ) * ζ ^ 21 + ((43 / 220) : ℂ) * ζ ^ 22 - ((13 / 55) : ℂ) * ζ ^ 24 + ((1 / 110) : ℂ) * ζ ^ 25 - ((4 / 55) : ℂ) * ζ ^ 26 + ((91 / 220) : ℂ) * ζ ^ 28)

private theorem row18_transformedGeneratorA_term_0_1_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 1 =
      (((41 / 220) : ℂ) + ((13 / 110) : ℂ) * ζ ^ 1 - ((8 / 55) : ℂ) * ζ ^ 3 + ((2 / 55) : ℂ) * ζ ^ 5 - ((19 / 110) : ℂ) * ζ ^ 8 + ((13 / 220) : ℂ) * ζ ^ 9 - ((6 / 55) : ℂ) * ζ ^ 11 + ((21 / 220) : ℂ) * ζ ^ 12 - ((13 / 110) : ℂ) * ζ ^ 13 + ((12 / 55) : ℂ) * ζ ^ 15 - ((13 / 110) : ℂ) * ζ ^ 17 - ((27 / 220) : ℂ) * ζ ^ 21 - ((23 / 220) : ℂ) * ζ ^ 24 + ((9 / 110) : ℂ) * ζ ^ 25 - ((29 / 220) : ℂ) * ζ ^ 27 + ((19 / 110) : ℂ) * ζ ^ 28 + ((13 / 110) : ℂ) * ζ ^ 29 + ((6 / 55) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_0_1 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        0 1 =
      alternatingSixAmbientRow18TransformedGeneratorA
        0 1 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_0_1_0,
      row18_transformedGeneratorA_term_0_1_1,
      row18_transformedGeneratorA_term_0_1_2,
      row18_transformedGeneratorA_term_0_1_3,
      row18_transformedGeneratorA_term_0_1_4,
      row18_transformedGeneratorA_term_0_1_5,
      row18_transformedGeneratorA_term_0_1_6,
      row18_transformedGeneratorA_term_0_1_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_2_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 2 =
      (((603 / 8690) : ℂ) - ((684 / 4345) : ℂ) * ζ ^ 1 - ((1611 / 17380) : ℂ) * ζ ^ 2 + ((657 / 17380) : ℂ) * ζ ^ 3 - ((202 / 4345) : ℂ) * ζ ^ 5 + ((421 / 17380) : ℂ) * ζ ^ 6 + ((838 / 4345) : ℂ) * ζ ^ 8 + ((758 / 4345) : ℂ) * ζ ^ 9 + ((3559 / 17380) : ℂ) * ζ ^ 11 - ((411 / 4345) : ℂ) * ζ ^ 12 + ((684 / 4345) : ℂ) * ζ ^ 13 - ((2003 / 17380) : ℂ) * ζ ^ 15 + ((684 / 4345) : ℂ) * ζ ^ 17 - ((911 / 8690) : ℂ) * ζ ^ 18 + ((967 / 17380) : ℂ) * ζ ^ 21 + ((1611 / 17380) : ℂ) * ζ ^ 22 + ((457 / 17380) : ℂ) * ζ ^ 24 - ((482 / 4345) : ℂ) * ζ ^ 25 - ((881 / 17380) : ℂ) * ζ ^ 27 - ((838 / 4345) : ℂ) * ζ ^ 28 - ((684 / 4345) : ℂ) * ζ ^ 29 + ((1083 / 17380) : ℂ) * ζ ^ 30 - ((3559 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1107 / 8690) : ℂ) + ((155 / 869) : ℂ) * ζ ^ 1 + ((493 / 3476) : ℂ) * ζ ^ 2 - ((1803 / 17380) : ℂ) * ζ ^ 3 + ((1203 / 8690) : ℂ) * ζ ^ 4 - ((656 / 4345) : ℂ) * ζ ^ 5 - ((757 / 8690) : ℂ) * ζ ^ 6 + ((1901 / 17380) : ℂ) * ζ ^ 7 - ((4959 / 17380) : ℂ) * ζ ^ 8 - ((2611 / 17380) : ℂ) * ζ ^ 9 + ((127 / 8690) : ℂ) * ζ ^ 10 - ((4233 / 17380) : ℂ) * ζ ^ 11 + ((1731 / 17380) : ℂ) * ζ ^ 12 + ((2489 / 17380) : ℂ) * ζ ^ 13 - ((433 / 3476) : ℂ) * ζ ^ 14 + ((3507 / 17380) : ℂ) * ζ ^ 15 - ((189 / 4345) : ℂ) * ζ ^ 16 - ((1489 / 8690) : ℂ) * ζ ^ 17 + ((1 / 316) : ℂ) * ζ ^ 18 - ((773 / 17380) : ℂ) * ζ ^ 19 + ((313 / 4345) : ℂ) * ζ ^ 20 + ((307 / 8690) : ℂ) * ζ ^ 21 - ((171 / 3476) : ℂ) * ζ ^ 22 + ((691 / 17380) : ℂ) * ζ ^ 23 + ((189 / 4345) : ℂ) * ζ ^ 24 - ((93 / 3476) : ℂ) * ζ ^ 25 + ((863 / 17380) : ℂ) * ζ ^ 26 + ((519 / 4345) : ℂ) * ζ ^ 27 + ((109 / 17380) : ℂ) * ζ ^ 28 + ((741 / 17380) : ℂ) * ζ ^ 29 + ((969 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_2_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 2 =
      (-((824 / 4345) : ℂ) + ((1503 / 17380) : ℂ) * ζ ^ 1 + ((27 / 17380) : ℂ) * ζ ^ 2 + ((927 / 17380) : ℂ) * ζ ^ 3 + ((1169 / 17380) : ℂ) * ζ ^ 5 - ((768 / 4345) : ℂ) * ζ ^ 6 + ((1873 / 17380) : ℂ) * ζ ^ 8 - ((761 / 17380) : ℂ) * ζ ^ 9 - ((1601 / 17380) : ℂ) * ζ ^ 11 + ((657 / 8690) : ℂ) * ζ ^ 12 - ((1503 / 17380) : ℂ) * ζ ^ 13 - ((107 / 4345) : ℂ) * ζ ^ 15 - ((1503 / 17380) : ℂ) * ζ ^ 17 + ((2999 / 17380) : ℂ) * ζ ^ 18 - ((3251 / 17380) : ℂ) * ζ ^ 21 - ((27 / 17380) : ℂ) * ζ ^ 22 - ((1997 / 17380) : ℂ) * ζ ^ 24 + ((167 / 8690) : ℂ) * ζ ^ 25 - ((1523 / 8690) : ℂ) * ζ ^ 27 - ((1873 / 17380) : ℂ) * ζ ^ 28 + ((1503 / 17380) : ℂ) * ζ ^ 29 - ((1493 / 8690) : ℂ) * ζ ^ 30 + ((1601 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((761 / 4345) : ℂ) - ((33 / 1580) : ℂ) * ζ ^ 1 - ((117 / 1738) : ℂ) * ζ ^ 2 - ((1437 / 8690) : ℂ) * ζ ^ 3 + ((169 / 4345) : ℂ) * ζ ^ 4 - ((43 / 8690) : ℂ) * ζ ^ 5 + ((21 / 17380) : ℂ) * ζ ^ 6 + ((3789 / 17380) : ℂ) * ζ ^ 7 - ((619 / 8690) : ℂ) * ζ ^ 8 - ((328 / 4345) : ℂ) * ζ ^ 9 + ((2671 / 17380) : ℂ) * ζ ^ 10 - ((1697 / 17380) : ℂ) * ζ ^ 11 - ((383 / 3476) : ℂ) * ζ ^ 12 + ((81 / 8690) : ℂ) * ζ ^ 13 + ((323 / 8690) : ℂ) * ζ ^ 14 + ((601 / 8690) : ℂ) * ζ ^ 15 - ((7 / 395) : ℂ) * ζ ^ 16 - ((933 / 17380) : ℂ) * ζ ^ 17 + ((258 / 4345) : ℂ) * ζ ^ 18 - ((21 / 1580) : ℂ) * ζ ^ 19 - ((947 / 17380) : ℂ) * ζ ^ 20 + ((58 / 869) : ℂ) * ζ ^ 21 - ((9 / 869) : ℂ) * ζ ^ 22 - ((261 / 8690) : ℂ) * ζ ^ 23 + ((1191 / 8690) : ℂ) * ζ ^ 24 - ((223 / 17380) : ℂ) * ζ ^ 25 - ((52 / 395) : ℂ) * ζ ^ 26 + ((563 / 17380) : ℂ) * ζ ^ 27 + ((152 / 4345) : ℂ) * ζ ^ 28 - ((57 / 4345) : ℂ) * ζ ^ 29)

private theorem row18_transformedGeneratorA_term_0_2_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 2 =
      (((72 / 869) : ℂ) - ((536 / 4345) : ℂ) * ζ ^ 1 - ((701 / 17380) : ℂ) * ζ ^ 2 + ((1759 / 8690) : ℂ) * ζ ^ 3 - ((647 / 17380) : ℂ) * ζ ^ 5 + ((549 / 4345) : ℂ) * ζ ^ 6 - ((45 / 869) : ℂ) * ζ ^ 8 + ((619 / 8690) : ℂ) * ζ ^ 9 - ((3109 / 17380) : ℂ) * ζ ^ 11 + ((525 / 3476) : ℂ) * ζ ^ 12 + ((536 / 4345) : ℂ) * ζ ^ 13 - ((728 / 4345) : ℂ) * ζ ^ 15 + ((536 / 4345) : ℂ) * ζ ^ 17 + ((3 / 55) : ℂ) * ζ ^ 18 + ((1329 / 8690) : ℂ) * ζ ^ 21 + ((701 / 17380) : ℂ) * ζ ^ 22 + ((147 / 1738) : ℂ) * ζ ^ 24 - ((1497 / 17380) : ℂ) * ζ ^ 25 + ((5041 / 17380) : ℂ) * ζ ^ 27 + ((45 / 869) : ℂ) * ζ ^ 28 - ((536 / 4345) : ℂ) * ζ ^ 29 + ((1269 / 8690) : ℂ) * ζ ^ 30 + ((3109 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((72 / 869) : ℂ) + ((12 / 79) : ℂ) * ζ ^ 1 + ((7 / 8690) : ℂ) * ζ ^ 2 - ((743 / 3476) : ℂ) * ζ ^ 3 + ((476 / 4345) : ℂ) * ζ ^ 4 - ((3063 / 17380) : ℂ) * ζ ^ 5 - ((221 / 1580) : ℂ) * ζ ^ 6 + ((305 / 3476) : ℂ) * ζ ^ 7 - ((771 / 8690) : ℂ) * ζ ^ 8 - ((3 / 55) : ℂ) * ζ ^ 9 + ((173 / 8690) : ℂ) * ζ ^ 10 - ((431 / 8690) : ℂ) * ζ ^ 11 - ((3849 / 17380) : ℂ) * ζ ^ 12 - ((254 / 4345) : ℂ) * ζ ^ 13 - ((1197 / 8690) : ℂ) * ζ ^ 14 - ((124 / 4345) : ℂ) * ζ ^ 15 + ((24 / 395) : ℂ) * ζ ^ 16 + ((457 / 17380) : ℂ) * ζ ^ 17 - ((981 / 8690) : ℂ) * ζ ^ 18 - ((103 / 3476) : ℂ) * ζ ^ 19 - ((699 / 3476) : ℂ) * ζ ^ 20 - ((408 / 4345) : ℂ) * ζ ^ 21 + ((107 / 3476) : ℂ) * ζ ^ 22 + ((369 / 4345) : ℂ) * ζ ^ 23 - ((333 / 17380) : ℂ) * ζ ^ 24 + ((381 / 8690) : ℂ) * ζ ^ 25 + ((48 / 869) : ℂ) * ζ ^ 26 + ((69 / 4345) : ℂ) * ζ ^ 27 + ((393 / 8690) : ℂ) * ζ ^ 28 + ((18 / 4345) : ℂ) * ζ ^ 29 - ((63 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_2_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 2 =
      (((18 / 395) : ℂ) + ((251 / 1580) : ℂ) * ζ ^ 1 - ((129 / 1580) : ℂ) * ζ ^ 2 - ((141 / 395) : ℂ) * ζ ^ 3 + ((63 / 1580) : ℂ) * ζ ^ 5 - ((71 / 1580) : ℂ) * ζ ^ 6 - ((321 / 1580) : ℂ) * ζ ^ 8 - ((63 / 395) : ℂ) * ζ ^ 9 + ((8 / 395) : ℂ) * ζ ^ 11 + ((47 / 1580) : ℂ) * ζ ^ 12 - ((251 / 1580) : ℂ) * ζ ^ 13 + ((451 / 1580) : ℂ) * ζ ^ 15 - ((251 / 1580) : ℂ) * ζ ^ 17 - ((113 / 1580) : ℂ) * ζ ^ 18 - ((91 / 790) : ℂ) * ζ ^ 21 + ((129 / 1580) : ℂ) * ζ ^ 22 - ((84 / 395) : ℂ) * ζ ^ 24 + ((47 / 395) : ℂ) * ζ ^ 25 - ((57 / 395) : ℂ) * ζ ^ 27 + ((321 / 1580) : ℂ) * ζ ^ 28 + ((251 / 1580) : ℂ) * ζ ^ 29 - ((43 / 1580) : ℂ) * ζ ^ 30 - ((8 / 395) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((102 / 395) : ℂ) + ((9 / 316) : ℂ) * ζ ^ 1 - ((3 / 316) : ℂ) * ζ ^ 2 + ((14 / 79) : ℂ) * ζ ^ 3 + ((141 / 395) : ℂ) * ζ ^ 4 - ((37 / 790) : ℂ) * ζ ^ 5 - ((7 / 79) : ℂ) * ζ ^ 6 - ((8 / 79) : ℂ) * ζ ^ 7 - ((31 / 158) : ℂ) * ζ ^ 8 - ((7 / 158) : ℂ) * ζ ^ 9 + ((139 / 790) : ℂ) * ζ ^ 10 + ((159 / 790) : ℂ) * ζ ^ 11 + ((19 / 790) : ℂ) * ζ ^ 12 - ((16 / 395) : ℂ) * ζ ^ 13 + ((1 / 316) : ℂ) * ζ ^ 14 - ((183 / 790) : ℂ) * ζ ^ 15 + ((1 / 395) : ℂ) * ζ ^ 16 - ((1 / 790) : ℂ) * ζ ^ 17 + ((63 / 790) : ℂ) * ζ ^ 18 + ((76 / 395) : ℂ) * ζ ^ 19 - ((67 / 1580) : ℂ) * ζ ^ 20 + ((23 / 790) : ℂ) * ζ ^ 21 - ((19 / 395) : ℂ) * ζ ^ 22 - ((137 / 790) : ℂ) * ζ ^ 23 + ((3 / 158) : ℂ) * ζ ^ 24 + ((58 / 395) : ℂ) * ζ ^ 25 - ((3 / 395) : ℂ) * ζ ^ 26 + ((69 / 790) : ℂ) * ζ ^ 27 + ((17 / 395) : ℂ) * ζ ^ 28 - ((32 / 395) : ℂ) * ζ ^ 29 - ((1 / 79) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_2_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 2 =
      (-((398 / 4345) : ℂ) + ((413 / 8690) : ℂ) * ζ ^ 1 - ((971 / 17380) : ℂ) * ζ ^ 2 + ((27 / 17380) : ℂ) * ζ ^ 3 + ((2103 / 17380) : ℂ) * ζ ^ 5 - ((131 / 4345) : ℂ) * ζ ^ 6 + ((2711 / 17380) : ℂ) * ζ ^ 8 + ((289 / 8690) : ℂ) * ζ ^ 9 + ((2399 / 17380) : ℂ) * ζ ^ 11 + ((149 / 8690) : ℂ) * ζ ^ 12 - ((413 / 8690) : ℂ) * ζ ^ 13 - ((1773 / 17380) : ℂ) * ζ ^ 15 - ((413 / 8690) : ℂ) * ζ ^ 17 + ((137 / 4345) : ℂ) * ζ ^ 18 - ((463 / 4345) : ℂ) * ζ ^ 21 + ((971 / 17380) : ℂ) * ζ ^ 22 + ((303 / 8690) : ℂ) * ζ ^ 24 - ((1277 / 17380) : ℂ) * ζ ^ 25 + ((857 / 8690) : ℂ) * ζ ^ 27 - ((2711 / 17380) : ℂ) * ζ ^ 28 + ((413 / 8690) : ℂ) * ζ ^ 29 - ((521 / 8690) : ℂ) * ζ ^ 30 - ((2399 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((461 / 4345) : ℂ) + ((153 / 17380) : ℂ) * ζ ^ 1 + ((1213 / 17380) : ℂ) * ζ ^ 2 + ((657 / 17380) : ℂ) * ζ ^ 3 - ((295 / 3476) : ℂ) * ζ ^ 4 - ((241 / 4345) : ℂ) * ζ ^ 5 + ((349 / 8690) : ℂ) * ζ ^ 6 - ((243 / 8690) : ℂ) * ζ ^ 7 + ((183 / 4345) : ℂ) * ζ ^ 8 + ((997 / 17380) : ℂ) * ζ ^ 9 + ((801 / 8690) : ℂ) * ζ ^ 10 - ((939 / 8690) : ℂ) * ζ ^ 11 + ((45 / 869) : ℂ) * ζ ^ 12 - ((15 / 316) : ℂ) * ζ ^ 13 - ((823 / 17380) : ℂ) * ζ ^ 14 + ((1217 / 8690) : ℂ) * ζ ^ 15 - ((18 / 395) : ℂ) * ζ ^ 16 - ((53 / 1580) : ℂ) * ζ ^ 17 + ((507 / 17380) : ℂ) * ζ ^ 18 - ((679 / 4345) : ℂ) * ζ ^ 19 - ((122 / 4345) : ℂ) * ζ ^ 20 + ((817 / 8690) : ℂ) * ζ ^ 21 - ((1161 / 8690) : ℂ) * ζ ^ 22 + ((177 / 3476) : ℂ) * ζ ^ 23 - ((969 / 8690) : ℂ) * ζ ^ 24 - ((1081 / 17380) : ℂ) * ζ ^ 25 - ((11 / 316) : ℂ) * ζ ^ 26 - ((447 / 17380) : ℂ) * ζ ^ 27 + ((14 / 869) : ℂ) * ζ ^ 28 + ((7 / 3476) : ℂ) * ζ ^ 29 + ((49 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_2_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 2 =
      (((1 / 22) : ℂ) + ((1 / 44) : ℂ) * ζ ^ 1 + ((3 / 44) : ℂ) * ζ ^ 3 - ((9 / 44) : ℂ) * ζ ^ 5 - ((1 / 11) : ℂ) * ζ ^ 8 - ((5 / 44) : ℂ) * ζ ^ 9 - ((3 / 22) : ℂ) * ζ ^ 11 - ((3 / 44) : ℂ) * ζ ^ 12 - ((1 / 44) : ℂ) * ζ ^ 13 + ((1 / 44) : ℂ) * ζ ^ 15 - ((1 / 44) : ℂ) * ζ ^ 17 - ((1 / 4) : ℂ) * ζ ^ 18 + ((7 / 44) : ℂ) * ζ ^ 21 + ((2 / 11) : ℂ) * ζ ^ 24 + ((5 / 22) : ℂ) * ζ ^ 25 + ((1 / 44) : ℂ) * ζ ^ 27 + ((1 / 11) : ℂ) * ζ ^ 28 + ((1 / 44) : ℂ) * ζ ^ 29 + ((3 / 22) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_2_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 2 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_2_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 2 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_0_2 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        0 2 =
      alternatingSixAmbientRow18TransformedGeneratorA
        0 2 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_0_2_0,
      row18_transformedGeneratorA_term_0_2_1,
      row18_transformedGeneratorA_term_0_2_2,
      row18_transformedGeneratorA_term_0_2_3,
      row18_transformedGeneratorA_term_0_2_4,
      row18_transformedGeneratorA_term_0_2_5,
      row18_transformedGeneratorA_term_0_2_6,
      row18_transformedGeneratorA_term_0_2_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_3_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 3 =
      (((203 / 3476) : ℂ) - ((6543 / 17380) : ℂ) * ζ ^ 1 - ((369 / 8690) : ℂ) * ζ ^ 2 + ((317 / 3476) : ℂ) * ζ ^ 3 - ((2779 / 17380) : ℂ) * ζ ^ 5 - ((1173 / 4345) : ℂ) * ζ ^ 6 - ((93 / 1738) : ℂ) * ζ ^ 8 + ((991 / 17380) : ℂ) * ζ ^ 9 - ((271 / 3476) : ℂ) * ζ ^ 11 - ((94 / 869) : ℂ) * ζ ^ 12 + ((6543 / 17380) : ℂ) * ζ ^ 13 - ((1273 / 3476) : ℂ) * ζ ^ 15 + ((6543 / 17380) : ℂ) * ζ ^ 17 + ((117 / 8690) : ℂ) * ζ ^ 18 + ((2841 / 17380) : ℂ) * ζ ^ 21 + ((369 / 8690) : ℂ) * ζ ^ 22 + ((383 / 3476) : ℂ) * ζ ^ 24 - ((941 / 4345) : ℂ) * ζ ^ 25 + ((355 / 3476) : ℂ) * ζ ^ 27 + ((93 / 1738) : ℂ) * ζ ^ 28 - ((6543 / 17380) : ℂ) * ζ ^ 29 - ((2073 / 8690) : ℂ) * ζ ^ 30 + ((271 / 3476) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((791 / 8690) : ℂ) + ((4527 / 17380) : ℂ) * ζ ^ 1 + ((213 / 17380) : ℂ) * ζ ^ 2 + ((191 / 1738) : ℂ) * ζ ^ 3 + ((47 / 17380) : ℂ) * ζ ^ 4 - ((2579 / 17380) : ℂ) * ζ ^ 5 + ((108 / 395) : ℂ) * ζ ^ 6 - ((503 / 4345) : ℂ) * ζ ^ 7 + ((4253 / 17380) : ℂ) * ζ ^ 8 + ((2173 / 8690) : ℂ) * ζ ^ 9 - ((4407 / 17380) : ℂ) * ζ ^ 10 - ((2249 / 8690) : ℂ) * ζ ^ 11 + ((537 / 8690) : ℂ) * ζ ^ 12 - ((135 / 3476) : ℂ) * ζ ^ 13 + ((99 / 790) : ℂ) * ζ ^ 14 + ((7193 / 17380) : ℂ) * ζ ^ 15 - ((3931 / 17380) : ℂ) * ζ ^ 16 - ((417 / 17380) : ℂ) * ζ ^ 17 + ((6179 / 17380) : ℂ) * ζ ^ 18 - ((1033 / 3476) : ℂ) * ζ ^ 19 + ((3849 / 17380) : ℂ) * ζ ^ 20 + ((299 / 3476) : ℂ) * ζ ^ 21 - ((71 / 869) : ℂ) * ζ ^ 22 + ((73 / 220) : ℂ) * ζ ^ 23 - ((152 / 869) : ℂ) * ζ ^ 24 - ((4167 / 17380) : ℂ) * ζ ^ 25 + ((239 / 1738) : ℂ) * ζ ^ 26 + ((2543 / 17380) : ℂ) * ζ ^ 27 - ((2147 / 17380) : ℂ) * ζ ^ 28 + ((399 / 8690) : ℂ) * ζ ^ 29 + ((1083 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_3_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 3 =
      (-((3613 / 17380) : ℂ) - ((1329 / 8690) : ℂ) * ζ ^ 1 - ((39 / 158) : ℂ) * ζ ^ 2 - ((1319 / 17380) : ℂ) * ζ ^ 3 - ((1389 / 17380) : ℂ) * ζ ^ 5 + ((11 / 316) : ℂ) * ζ ^ 6 - ((1073 / 8690) : ℂ) * ζ ^ 8 - ((346 / 4345) : ℂ) * ζ ^ 9 + ((4717 / 17380) : ℂ) * ζ ^ 11 + ((2091 / 8690) : ℂ) * ζ ^ 12 + ((1329 / 8690) : ℂ) * ζ ^ 13 - ((131 / 4345) : ℂ) * ζ ^ 15 + ((1329 / 8690) : ℂ) * ζ ^ 17 + ((81 / 316) : ℂ) * ζ ^ 18 + ((524 / 4345) : ℂ) * ζ ^ 21 + ((39 / 158) : ℂ) * ζ ^ 22 - ((471 / 17380) : ℂ) * ζ ^ 24 - ((1269 / 17380) : ℂ) * ζ ^ 25 + ((1797 / 17380) : ℂ) * ζ ^ 27 + ((1073 / 8690) : ℂ) * ζ ^ 28 - ((1329 / 8690) : ℂ) * ζ ^ 29 - ((9 / 158) : ℂ) * ζ ^ 30 - ((4717 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((877 / 4345) : ℂ) + ((2139 / 17380) : ℂ) * ζ ^ 1 + ((306 / 869) : ℂ) * ζ ^ 2 + ((356 / 4345) : ℂ) * ζ ^ 3 - ((7519 / 17380) : ℂ) * ζ ^ 4 + ((21 / 869) : ℂ) * ζ ^ 5 - ((763 / 3476) : ℂ) * ζ ^ 6 - ((194 / 4345) : ℂ) * ζ ^ 7 + ((203 / 395) : ℂ) * ζ ^ 8 + ((1187 / 17380) : ℂ) * ζ ^ 9 - ((941 / 8690) : ℂ) * ζ ^ 10 - ((3637 / 17380) : ℂ) * ζ ^ 11 + ((3269 / 17380) : ℂ) * ζ ^ 12 + ((299 / 17380) : ℂ) * ζ ^ 13 - ((2979 / 17380) : ℂ) * ζ ^ 14 + ((64 / 4345) : ℂ) * ζ ^ 15 + ((387 / 8690) : ℂ) * ζ ^ 16 + ((197 / 4345) : ℂ) * ζ ^ 17 + ((227 / 4345) : ℂ) * ζ ^ 18 + ((21 / 790) : ℂ) * ζ ^ 19 + ((89 / 1580) : ℂ) * ζ ^ 20 - ((2089 / 8690) : ℂ) * ζ ^ 21 + ((411 / 8690) : ℂ) * ζ ^ 22 + ((2253 / 17380) : ℂ) * ζ ^ 23 - ((547 / 4345) : ℂ) * ζ ^ 24 + ((29 / 1738) : ℂ) * ζ ^ 25 + ((2433 / 17380) : ℂ) * ζ ^ 26 + ((7 / 1738) : ℂ) * ζ ^ 27 - ((4273 / 17380) : ℂ) * ζ ^ 28 - ((171 / 17380) : ℂ) * ζ ^ 29 + ((1767 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_3_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 3 =
      (((607 / 17380) : ℂ) - ((1487 / 17380) : ℂ) * ζ ^ 1 + ((2339 / 8690) : ℂ) * ζ ^ 2 - ((1691 / 8690) : ℂ) * ζ ^ 3 + ((1307 / 8690) : ℂ) * ζ ^ 5 + ((5287 / 17380) : ℂ) * ζ ^ 6 - ((419 / 4345) : ℂ) * ζ ^ 8 + ((247 / 8690) : ℂ) * ζ ^ 9 + ((49 / 220) : ℂ) * ζ ^ 11 + ((288 / 4345) : ℂ) * ζ ^ 12 + ((1487 / 17380) : ℂ) * ζ ^ 13 - ((148 / 4345) : ℂ) * ζ ^ 15 + ((1487 / 17380) : ℂ) * ζ ^ 17 - ((4299 / 17380) : ℂ) * ζ ^ 18 + ((321 / 4345) : ℂ) * ζ ^ 21 - ((2339 / 8690) : ℂ) * ζ ^ 22 - ((1191 / 17380) : ℂ) * ζ ^ 24 - ((4101 / 17380) : ℂ) * ζ ^ 25 - ((4409 / 17380) : ℂ) * ζ ^ 27 + ((419 / 4345) : ℂ) * ζ ^ 28 - ((1487 / 17380) : ℂ) * ζ ^ 29 - ((447 / 8690) : ℂ) * ζ ^ 30 - ((49 / 220) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((943 / 17380) : ℂ) + ((2041 / 17380) : ℂ) * ζ ^ 1 - ((1887 / 8690) : ℂ) * ζ ^ 2 + ((1016 / 4345) : ℂ) * ζ ^ 3 - ((1449 / 17380) : ℂ) * ζ ^ 4 - ((1499 / 17380) : ℂ) * ζ ^ 5 + ((283 / 8690) : ℂ) * ζ ^ 6 + ((51 / 17380) : ℂ) * ζ ^ 7 + ((53 / 3476) : ℂ) * ζ ^ 8 + ((1171 / 17380) : ℂ) * ζ ^ 9 - ((117 / 8690) : ℂ) * ζ ^ 10 + ((1033 / 17380) : ℂ) * ζ ^ 11 - ((59 / 869) : ℂ) * ζ ^ 12 - ((2747 / 17380) : ℂ) * ζ ^ 13 - ((2159 / 8690) : ℂ) * ζ ^ 14 + ((409 / 4345) : ℂ) * ζ ^ 15 + ((299 / 1738) : ℂ) * ζ ^ 16 + ((219 / 4345) : ℂ) * ζ ^ 17 + ((159 / 790) : ℂ) * ζ ^ 18 - ((877 / 8690) : ℂ) * ζ ^ 19 - ((597 / 17380) : ℂ) * ζ ^ 20 - ((123 / 869) : ℂ) * ζ ^ 21 - ((163 / 3476) : ℂ) * ζ ^ 22 - ((267 / 3476) : ℂ) * ζ ^ 23 + ((463 / 17380) : ℂ) * ζ ^ 24 + ((1533 / 17380) : ℂ) * ζ ^ 25 + ((6 / 395) : ℂ) * ζ ^ 26 + ((513 / 17380) : ℂ) * ζ ^ 27 - ((18 / 4345) : ℂ) * ζ ^ 28 - ((123 / 8690) : ℂ) * ζ ^ 29 + ((12 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_3_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 3 =
      (((101 / 1580) : ℂ) + ((197 / 395) : ℂ) * ζ ^ 1 + ((67 / 790) : ℂ) * ζ ^ 2 + ((37 / 158) : ℂ) * ζ ^ 3 + ((109 / 1580) : ℂ) * ζ ^ 5 + ((271 / 1580) : ℂ) * ζ ^ 6 + ((171 / 790) : ℂ) * ζ ^ 8 - ((44 / 395) : ℂ) * ζ ^ 9 - ((5 / 158) : ℂ) * ζ ^ 11 - ((126 / 395) : ℂ) * ζ ^ 12 - ((197 / 395) : ℂ) * ζ ^ 13 + ((39 / 316) : ℂ) * ζ ^ 15 - ((197 / 395) : ℂ) * ζ ^ 17 - ((17 / 1580) : ℂ) * ζ ^ 18 - ((59 / 395) : ℂ) * ζ ^ 21 - ((67 / 790) : ℂ) * ζ ^ 22 + ((133 / 395) : ℂ) * ζ ^ 24 + ((679 / 1580) : ℂ) * ζ ^ 25 - ((31 / 316) : ℂ) * ζ ^ 27 - ((171 / 790) : ℂ) * ζ ^ 28 + ((197 / 395) : ℂ) * ζ ^ 29 + ((493 / 1580) : ℂ) * ζ ^ 30 + ((5 / 158) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((53 / 316) : ℂ) - ((501 / 790) : ℂ) * ζ ^ 1 + ((19 / 790) : ℂ) * ζ ^ 2 - ((603 / 1580) : ℂ) * ζ ^ 3 - ((29 / 790) : ℂ) * ζ ^ 4 + ((897 / 1580) : ℂ) * ζ ^ 5 + ((15 / 316) : ℂ) * ζ ^ 6 + ((167 / 1580) : ℂ) * ζ ^ 7 - ((609 / 1580) : ℂ) * ζ ^ 8 + ((93 / 1580) : ℂ) * ζ ^ 9 + ((7 / 790) : ℂ) * ζ ^ 10 - ((341 / 790) : ℂ) * ζ ^ 11 + ((101 / 316) : ℂ) * ζ ^ 12 + ((191 / 1580) : ℂ) * ζ ^ 13 + ((411 / 1580) : ℂ) * ζ ^ 14 + ((137 / 790) : ℂ) * ζ ^ 15 - ((829 / 1580) : ℂ) * ζ ^ 16 + ((1 / 20) : ℂ) * ζ ^ 17 - ((583 / 1580) : ℂ) * ζ ^ 18 + ((147 / 790) : ℂ) * ζ ^ 19 + ((263 / 790) : ℂ) * ζ ^ 20 + ((31 / 790) : ℂ) * ζ ^ 21 + ((109 / 790) : ℂ) * ζ ^ 22 - ((209 / 790) : ℂ) * ζ ^ 23 - ((71 / 790) : ℂ) * ζ ^ 24 - ((327 / 790) : ℂ) * ζ ^ 25 - ((7 / 395) : ℂ) * ζ ^ 26 + ((71 / 395) : ℂ) * ζ ^ 27 + ((29 / 395) : ℂ) * ζ ^ 28 + ((34 / 395) : ℂ) * ζ ^ 29 - ((24 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_3_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 3 =
      (((199 / 3476) : ℂ) - ((749 / 17380) : ℂ) * ζ ^ 1 - ((1927 / 4345) : ℂ) * ζ ^ 2 + ((147 / 869) : ℂ) * ζ ^ 3 - ((277 / 17380) : ℂ) * ζ ^ 5 - ((2301 / 8690) : ℂ) * ζ ^ 6 - ((265 / 1738) : ℂ) * ζ ^ 8 - ((953 / 4345) : ℂ) * ζ ^ 9 - ((206 / 869) : ℂ) * ζ ^ 11 - ((10 / 869) : ℂ) * ζ ^ 12 + ((749 / 17380) : ℂ) * ζ ^ 13 - ((761 / 3476) : ℂ) * ζ ^ 15 + ((749 / 17380) : ℂ) * ζ ^ 17 + ((5469 / 17380) : ℂ) * ζ ^ 18 - ((777 / 17380) : ℂ) * ζ ^ 21 + ((1927 / 4345) : ℂ) * ζ ^ 22 - ((73 / 3476) : ℂ) * ζ ^ 24 - ((118 / 4345) : ℂ) * ζ ^ 25 + ((1021 / 3476) : ℂ) * ζ ^ 27 + ((265 / 1738) : ℂ) * ζ ^ 28 - ((749 / 17380) : ℂ) * ζ ^ 29 - ((6141 / 17380) : ℂ) * ζ ^ 30 + ((206 / 869) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((239 / 17380) : ℂ) + ((513 / 8690) : ℂ) * ζ ^ 1 + ((6861 / 17380) : ℂ) * ζ ^ 2 - ((67 / 790) : ℂ) * ζ ^ 3 + ((443 / 17380) : ℂ) * ζ ^ 4 + ((1229 / 17380) : ℂ) * ζ ^ 5 - ((373 / 1738) : ℂ) * ζ ^ 6 + ((19 / 17380) : ℂ) * ζ ^ 7 + ((2931 / 8690) : ℂ) * ζ ^ 8 + ((787 / 4345) : ℂ) * ζ ^ 9 + ((4989 / 17380) : ℂ) * ζ ^ 10 - ((1131 / 17380) : ℂ) * ζ ^ 11 - ((1306 / 4345) : ℂ) * ζ ^ 12 - ((261 / 4345) : ℂ) * ζ ^ 13 + ((2007 / 17380) : ℂ) * ζ ^ 14 - ((466 / 4345) : ℂ) * ζ ^ 15 + ((1207 / 8690) : ℂ) * ζ ^ 16 + ((2613 / 17380) : ℂ) * ζ ^ 17 - ((71 / 4345) : ℂ) * ζ ^ 18 - ((1059 / 17380) : ℂ) * ζ ^ 19 - ((1431 / 17380) : ℂ) * ζ ^ 20 - ((811 / 17380) : ℂ) * ζ ^ 21 + ((883 / 17380) : ℂ) * ζ ^ 22 + ((3797 / 17380) : ℂ) * ζ ^ 23 - ((1477 / 8690) : ℂ) * ζ ^ 24 + ((707 / 4345) : ℂ) * ζ ^ 25 - ((3219 / 17380) : ℂ) * ζ ^ 26 - ((508 / 4345) : ℂ) * ζ ^ 27 + ((13 / 790) : ℂ) * ζ ^ 28 - ((91 / 4345) : ℂ) * ζ ^ 29 + ((7 / 220) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_3_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 3 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_3_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 3 =
      (-((4 / 55) : ℂ) + ((91 / 220) : ℂ) * ζ ^ 2 - ((17 / 110) : ℂ) * ζ ^ 3 + ((29 / 220) : ℂ) * ζ ^ 6 + ((43 / 220) : ℂ) * ζ ^ 8 + ((1 / 110) : ℂ) * ζ ^ 11 + ((6 / 55) : ℂ) * ζ ^ 12 + ((51 / 220) : ℂ) * ζ ^ 15 - ((53 / 220) : ℂ) * ζ ^ 18 - ((91 / 220) : ℂ) * ζ ^ 22 - ((21 / 110) : ℂ) * ζ ^ 24 + ((7 / 220) : ℂ) * ζ ^ 27 - ((43 / 220) : ℂ) * ζ ^ 28 + ((13 / 55) : ℂ) * ζ ^ 30 - ((1 / 110) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((4 / 55) : ℂ) - ((91 / 220) : ℂ) * ζ ^ 2)

private theorem row18_transformedGeneratorA_term_0_3_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 3 =
      (((41 / 220) : ℂ) + ((13 / 110) : ℂ) * ζ ^ 1 - ((8 / 55) : ℂ) * ζ ^ 3 + ((2 / 55) : ℂ) * ζ ^ 5 - ((19 / 110) : ℂ) * ζ ^ 8 + ((13 / 220) : ℂ) * ζ ^ 9 - ((6 / 55) : ℂ) * ζ ^ 11 + ((21 / 220) : ℂ) * ζ ^ 12 - ((13 / 110) : ℂ) * ζ ^ 13 + ((12 / 55) : ℂ) * ζ ^ 15 - ((13 / 110) : ℂ) * ζ ^ 17 - ((27 / 220) : ℂ) * ζ ^ 21 - ((23 / 220) : ℂ) * ζ ^ 24 + ((9 / 110) : ℂ) * ζ ^ 25 - ((29 / 220) : ℂ) * ζ ^ 27 + ((19 / 110) : ℂ) * ζ ^ 28 + ((13 / 110) : ℂ) * ζ ^ 29 + ((6 / 55) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_0_3 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        0 3 =
      alternatingSixAmbientRow18TransformedGeneratorA
        0 3 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_0_3_0,
      row18_transformedGeneratorA_term_0_3_1,
      row18_transformedGeneratorA_term_0_3_2,
      row18_transformedGeneratorA_term_0_3_3,
      row18_transformedGeneratorA_term_0_3_4,
      row18_transformedGeneratorA_term_0_3_5,
      row18_transformedGeneratorA_term_0_3_6,
      row18_transformedGeneratorA_term_0_3_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_4_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 4 =
      (-((247 / 3476) : ℂ) + ((73 / 17380) : ℂ) * ζ ^ 1 + ((125 / 869) : ℂ) * ζ ^ 2 + ((663 / 8690) : ℂ) * ζ ^ 3 - ((24 / 4345) : ℂ) * ζ ^ 5 + ((13 / 869) : ℂ) * ζ ^ 6 + ((217 / 869) : ℂ) * ζ ^ 8 - ((809 / 4345) : ℂ) * ζ ^ 9 + ((87 / 17380) : ℂ) * ζ ^ 11 - ((60 / 869) : ℂ) * ζ ^ 12 - ((73 / 17380) : ℂ) * ζ ^ 13 - ((401 / 4345) : ℂ) * ζ ^ 15 - ((73 / 17380) : ℂ) * ζ ^ 17 + ((139 / 3476) : ℂ) * ζ ^ 18 + ((26 / 4345) : ℂ) * ζ ^ 21 - ((125 / 869) : ℂ) * ζ ^ 22 - ((109 / 1738) : ℂ) * ζ ^ 24 + ((169 / 17380) : ℂ) * ζ ^ 25 + ((4017 / 17380) : ℂ) * ζ ^ 27 - ((217 / 869) : ℂ) * ζ ^ 28 + ((73 / 17380) : ℂ) * ζ ^ 29 + ((325 / 3476) : ℂ) * ζ ^ 30 - ((87 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((227 / 17380) : ℂ) - ((579 / 8690) : ℂ) * ζ ^ 1 - ((3249 / 17380) : ℂ) * ζ ^ 2 - ((947 / 4345) : ℂ) * ζ ^ 3 - ((59 / 1580) : ℂ) * ζ ^ 4 - ((228 / 4345) : ℂ) * ζ ^ 5 + ((91 / 8690) : ℂ) * ζ ^ 6 + ((369 / 1738) : ℂ) * ζ ^ 7 - ((956 / 4345) : ℂ) * ζ ^ 8 + ((2833 / 8690) : ℂ) * ζ ^ 9 + ((323 / 17380) : ℂ) * ζ ^ 10 + ((504 / 4345) : ℂ) * ζ ^ 11 + ((226 / 869) : ℂ) * ζ ^ 12 - ((239 / 3476) : ℂ) * ζ ^ 13 + ((499 / 3476) : ℂ) * ζ ^ 14 - ((618 / 4345) : ℂ) * ζ ^ 15 - ((2003 / 17380) : ℂ) * ζ ^ 16 + ((273 / 4345) : ℂ) * ζ ^ 17 - ((1929 / 17380) : ℂ) * ζ ^ 18 - ((98 / 869) : ℂ) * ζ ^ 19 + ((3013 / 17380) : ℂ) * ζ ^ 20 + ((1519 / 17380) : ℂ) * ζ ^ 21 + ((1099 / 17380) : ℂ) * ζ ^ 22 + ((101 / 1580) : ℂ) * ζ ^ 23 + ((143 / 790) : ℂ) * ζ ^ 24 - ((1193 / 17380) : ℂ) * ζ ^ 25 - ((647 / 17380) : ℂ) * ζ ^ 26 - ((1887 / 8690) : ℂ) * ζ ^ 27 - ((199 / 4345) : ℂ) * ζ ^ 28 - ((741 / 17380) : ℂ) * ζ ^ 29 - ((2337 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_4_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 4 =
      (((831 / 17380) : ℂ) + ((1909 / 8690) : ℂ) * ζ ^ 1 - ((152 / 4345) : ℂ) * ζ ^ 2 + ((1069 / 8690) : ℂ) * ζ ^ 3 + ((776 / 4345) : ℂ) * ζ ^ 5 - ((318 / 4345) : ℂ) * ζ ^ 6 - ((23 / 17380) : ℂ) * ζ ^ 8 - ((1061 / 17380) : ℂ) * ζ ^ 9 - ((917 / 8690) : ℂ) * ζ ^ 11 - ((1769 / 17380) : ℂ) * ζ ^ 12 - ((1909 / 8690) : ℂ) * ζ ^ 13 - ((403 / 4345) : ℂ) * ζ ^ 15 - ((1909 / 8690) : ℂ) * ζ ^ 17 - ((651 / 17380) : ℂ) * ζ ^ 18 - ((851 / 17380) : ℂ) * ζ ^ 21 + ((152 / 4345) : ℂ) * ζ ^ 22 + ((2367 / 17380) : ℂ) * ζ ^ 24 + ((357 / 8690) : ℂ) * ζ ^ 25 + ((723 / 8690) : ℂ) * ζ ^ 27 + ((23 / 17380) : ℂ) * ζ ^ 28 + ((1909 / 8690) : ℂ) * ζ ^ 29 - ((151 / 17380) : ℂ) * ζ ^ 30 + ((917 / 8690) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1083 / 17380) : ℂ) - ((335 / 1738) : ℂ) * ζ ^ 1 + ((503 / 17380) : ℂ) * ζ ^ 2 - ((2309 / 17380) : ℂ) * ζ ^ 3 + ((63 / 1580) : ℂ) * ζ ^ 4 - ((291 / 17380) : ℂ) * ζ ^ 5 + ((2593 / 17380) : ℂ) * ζ ^ 6 + ((697 / 8690) : ℂ) * ζ ^ 7 - ((1927 / 17380) : ℂ) * ζ ^ 8 + ((163 / 3476) : ℂ) * ζ ^ 9 - ((167 / 17380) : ℂ) * ζ ^ 10 + ((17 / 3476) : ℂ) * ζ ^ 11 + ((9 / 395) : ℂ) * ζ ^ 12 + ((39 / 17380) : ℂ) * ζ ^ 13 + ((75 / 1738) : ℂ) * ζ ^ 14 - ((287 / 8690) : ℂ) * ζ ^ 15 - ((7 / 316) : ℂ) * ζ ^ 16 + ((16 / 869) : ℂ) * ζ ^ 17 - ((577 / 4345) : ℂ) * ζ ^ 18 - ((183 / 17380) : ℂ) * ζ ^ 19 + ((41 / 869) : ℂ) * ζ ^ 20 + ((281 / 4345) : ℂ) * ζ ^ 21 - ((681 / 17380) : ℂ) * ζ ^ 22 - ((41 / 1738) : ℂ) * ζ ^ 23 + ((1103 / 17380) : ℂ) * ζ ^ 24 - ((21 / 1580) : ℂ) * ζ ^ 25 - ((203 / 8690) : ℂ) * ζ ^ 26 - ((349 / 17380) : ℂ) * ζ ^ 27 + ((117 / 4345) : ℂ) * ζ ^ 28 + ((57 / 4345) : ℂ) * ζ ^ 29 - ((57 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_4_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 4 =
      (((51 / 869) : ℂ) - ((1491 / 17380) : ℂ) * ζ ^ 1 + ((4681 / 17380) : ℂ) * ζ ^ 2 - ((1393 / 17380) : ℂ) * ζ ^ 3 - ((1453 / 17380) : ℂ) * ζ ^ 5 + ((636 / 4345) : ℂ) * ζ ^ 6 - ((1057 / 3476) : ℂ) * ζ ^ 8 + ((1731 / 8690) : ℂ) * ζ ^ 9 + ((1499 / 17380) : ℂ) * ζ ^ 11 - ((405 / 3476) : ℂ) * ζ ^ 12 + ((1491 / 17380) : ℂ) * ζ ^ 13 + ((467 / 17380) : ℂ) * ζ ^ 15 + ((1491 / 17380) : ℂ) * ζ ^ 17 - ((2163 / 17380) : ℂ) * ζ ^ 18 + ((1047 / 17380) : ℂ) * ζ ^ 21 - ((4681 / 17380) : ℂ) * ζ ^ 22 + ((221 / 1738) : ℂ) * ζ ^ 24 - ((19 / 8690) : ℂ) * ζ ^ 25 - ((4021 / 17380) : ℂ) * ζ ^ 27 + ((1057 / 3476) : ℂ) * ζ ^ 28 - ((1491 / 17380) : ℂ) * ζ ^ 29 - ((62 / 4345) : ℂ) * ζ ^ 30 - ((1499 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((51 / 869) : ℂ) + ((117 / 4345) : ℂ) * ζ ^ 1 - ((4351 / 17380) : ℂ) * ζ ^ 2 + ((1063 / 17380) : ℂ) * ζ ^ 3 + ((63 / 17380) : ℂ) * ζ ^ 4 + ((103 / 4345) : ℂ) * ζ ^ 5 - ((61 / 8690) : ℂ) * ζ ^ 6 + ((1127 / 17380) : ℂ) * ζ ^ 7 + ((189 / 1580) : ℂ) * ζ ^ 8 - ((2391 / 17380) : ℂ) * ζ ^ 9 - ((313 / 17380) : ℂ) * ζ ^ 10 - ((799 / 8690) : ℂ) * ζ ^ 11 - ((69 / 17380) : ℂ) * ζ ^ 12 + ((443 / 4345) : ℂ) * ζ ^ 13 - ((751 / 17380) : ℂ) * ζ ^ 14 + ((101 / 869) : ℂ) * ζ ^ 15 + ((33 / 395) : ℂ) * ζ ^ 16 - ((1141 / 17380) : ℂ) * ζ ^ 17 + ((519 / 4345) : ℂ) * ζ ^ 18 - ((817 / 17380) : ℂ) * ζ ^ 19 + ((541 / 4345) : ℂ) * ζ ^ 20 - ((67 / 790) : ℂ) * ζ ^ 21 + ((15 / 1738) : ℂ) * ζ ^ 22 - ((78 / 4345) : ℂ) * ζ ^ 23 - ((441 / 8690) : ℂ) * ζ ^ 24 + ((12 / 395) : ℂ) * ζ ^ 25 - ((69 / 3476) : ℂ) * ζ ^ 26 - ((21 / 4345) : ℂ) * ζ ^ 27 + ((18 / 4345) : ℂ) * ζ ^ 28 - ((18 / 4345) : ℂ) * ζ ^ 29 + ((9 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_4_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 4 =
      (((91 / 790) : ℂ) - ((89 / 1580) : ℂ) * ζ ^ 1 - ((59 / 1580) : ℂ) * ζ ^ 2 - ((126 / 395) : ℂ) * ζ ^ 3 - ((117 / 1580) : ℂ) * ζ ^ 5 - ((54 / 395) : ℂ) * ζ ^ 6 - ((63 / 790) : ℂ) * ζ ^ 8 - ((3 / 395) : ℂ) * ζ ^ 9 + ((111 / 790) : ℂ) * ζ ^ 11 + ((101 / 790) : ℂ) * ζ ^ 12 + ((89 / 1580) : ℂ) * ζ ^ 13 + ((591 / 1580) : ℂ) * ζ ^ 15 + ((89 / 1580) : ℂ) * ζ ^ 17 - ((43 / 1580) : ℂ) * ζ ^ 18 - ((38 / 395) : ℂ) * ζ ^ 21 + ((59 / 1580) : ℂ) * ζ ^ 22 - ((351 / 1580) : ℂ) * ζ ^ 24 + ((7 / 395) : ℂ) * ζ ^ 25 - ((37 / 395) : ℂ) * ζ ^ 27 + ((63 / 790) : ℂ) * ζ ^ 28 - ((89 / 1580) : ℂ) * ζ ^ 29 + ((38 / 395) : ℂ) * ζ ^ 30 - ((111 / 790) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((259 / 790) : ℂ) + ((47 / 316) : ℂ) * ζ ^ 1 + ((207 / 1580) : ℂ) * ζ ^ 2 + ((1 / 10) : ℂ) * ζ ^ 3 + ((111 / 316) : ℂ) * ζ ^ 4 - ((111 / 790) : ℂ) * ζ ^ 5 + ((143 / 790) : ℂ) * ζ ^ 6 - ((139 / 790) : ℂ) * ζ ^ 7 - ((127 / 316) : ℂ) * ζ ^ 8 + ((1 / 395) : ℂ) * ζ ^ 9 - ((137 / 1580) : ℂ) * ζ ^ 10 + ((51 / 158) : ℂ) * ζ ^ 11 + ((117 / 1580) : ℂ) * ζ ^ 12 - ((61 / 395) : ℂ) * ζ ^ 13 + ((33 / 158) : ℂ) * ζ ^ 14 - ((109 / 395) : ℂ) * ζ ^ 15 - ((59 / 1580) : ℂ) * ζ ^ 16 - ((13 / 790) : ℂ) * ζ ^ 17 - ((219 / 1580) : ℂ) * ζ ^ 18 + ((149 / 395) : ℂ) * ζ ^ 19 - ((123 / 790) : ℂ) * ζ ^ 20 + ((151 / 790) : ℂ) * ζ ^ 21 - ((63 / 790) : ℂ) * ζ ^ 22 - ((137 / 790) : ℂ) * ζ ^ 23 + ((66 / 395) : ℂ) * ζ ^ 24 - ((23 / 158) : ℂ) * ζ ^ 25 + ((54 / 395) : ℂ) * ζ ^ 26 - ((2 / 79) : ℂ) * ζ ^ 27 + ((31 / 395) : ℂ) * ζ ^ 28 + ((32 / 395) : ℂ) * ζ ^ 29 - ((44 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_4_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 4 =
      (-((1072 / 4345) : ℂ) - ((1211 / 17380) : ℂ) * ζ ^ 1 + ((173 / 8690) : ℂ) * ζ ^ 2 + ((99 / 790) : ℂ) * ζ ^ 3 + ((1121 / 8690) : ℂ) * ζ ^ 5 + ((211 / 4345) : ℂ) * ζ ^ 6 + ((1066 / 4345) : ℂ) * ζ ^ 8 + ((1141 / 8690) : ℂ) * ζ ^ 9 + ((43 / 790) : ℂ) * ζ ^ 11 + ((5387 / 17380) : ℂ) * ζ ^ 12 + ((1211 / 17380) : ℂ) * ζ ^ 13 - ((217 / 1580) : ℂ) * ζ ^ 15 + ((1211 / 17380) : ℂ) * ζ ^ 17 + ((667 / 17380) : ℂ) * ζ ^ 18 - ((527 / 4345) : ℂ) * ζ ^ 21 - ((173 / 8690) : ℂ) * ζ ^ 22 - ((2273 / 8690) : ℂ) * ζ ^ 24 - ((3453 / 17380) : ℂ) * ζ ^ 25 - ((21 / 395) : ℂ) * ζ ^ 27 - ((1066 / 4345) : ℂ) * ζ ^ 28 - ((1211 / 17380) : ℂ) * ζ ^ 29 - ((1119 / 8690) : ℂ) * ζ ^ 30 - ((43 / 790) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((227 / 869) : ℂ) + ((93 / 1738) : ℂ) * ζ ^ 1 - ((519 / 17380) : ℂ) * ζ ^ 2 - ((381 / 4345) : ℂ) * ζ ^ 3 - ((104 / 395) : ℂ) * ζ ^ 4 - ((323 / 1738) : ℂ) * ζ ^ 5 - ((19 / 869) : ℂ) * ζ ^ 6 + ((123 / 1580) : ℂ) * ζ ^ 7 + ((375 / 3476) : ℂ) * ζ ^ 8 + ((1009 / 8690) : ℂ) * ζ ^ 9 - ((91 / 3476) : ℂ) * ζ ^ 10 - ((867 / 8690) : ℂ) * ζ ^ 11 - ((379 / 3476) : ℂ) * ζ ^ 12 - ((831 / 17380) : ℂ) * ζ ^ 13 + ((1041 / 17380) : ℂ) * ζ ^ 14 + ((2477 / 17380) : ℂ) * ζ ^ 15 + ((524 / 4345) : ℂ) * ζ ^ 16 - ((13 / 869) : ℂ) * ζ ^ 17 - ((272 / 4345) : ℂ) * ζ ^ 18 - ((743 / 4345) : ℂ) * ζ ^ 19 - ((61 / 869) : ℂ) * ζ ^ 20 + ((287 / 8690) : ℂ) * ζ ^ 21 + ((311 / 3476) : ℂ) * ζ ^ 22 + ((534 / 4345) : ℂ) * ζ ^ 23 + ((171 / 3476) : ℂ) * ζ ^ 24 + ((227 / 8690) : ℂ) * ζ ^ 25 - ((108 / 4345) : ℂ) * ζ ^ 26 - ((3 / 158) : ℂ) * ζ ^ 27 - ((14 / 4345) : ℂ) * ζ ^ 28 - ((7 / 3476) : ℂ) * ζ ^ 29 + ((49 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_4_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 4 =
      (((1 / 22) : ℂ) + ((1 / 44) : ℂ) * ζ ^ 1 + ((3 / 44) : ℂ) * ζ ^ 3 - ((9 / 44) : ℂ) * ζ ^ 5 - ((1 / 11) : ℂ) * ζ ^ 8 - ((5 / 44) : ℂ) * ζ ^ 9 - ((3 / 22) : ℂ) * ζ ^ 11 - ((3 / 44) : ℂ) * ζ ^ 12 - ((1 / 44) : ℂ) * ζ ^ 13 + ((1 / 44) : ℂ) * ζ ^ 15 - ((1 / 44) : ℂ) * ζ ^ 17 - ((1 / 4) : ℂ) * ζ ^ 18 + ((7 / 44) : ℂ) * ζ ^ 21 + ((2 / 11) : ℂ) * ζ ^ 24 + ((5 / 22) : ℂ) * ζ ^ 25 + ((1 / 44) : ℂ) * ζ ^ 27 + ((1 / 11) : ℂ) * ζ ^ 28 + ((1 / 44) : ℂ) * ζ ^ 29 + ((3 / 22) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_4_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 4 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_4_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 4 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_0_4 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        0 4 =
      alternatingSixAmbientRow18TransformedGeneratorA
        0 4 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_0_4_0,
      row18_transformedGeneratorA_term_0_4_1,
      row18_transformedGeneratorA_term_0_4_2,
      row18_transformedGeneratorA_term_0_4_3,
      row18_transformedGeneratorA_term_0_4_4,
      row18_transformedGeneratorA_term_0_4_5,
      row18_transformedGeneratorA_term_0_4_6,
      row18_transformedGeneratorA_term_0_4_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_5_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 5 =
      (-((4887 / 17380) : ℂ) + ((3057 / 17380) : ℂ) * ζ ^ 1 + ((203 / 4345) : ℂ) * ζ ^ 2 - ((123 / 790) : ℂ) * ζ ^ 3 - ((611 / 4345) : ℂ) * ζ ^ 5 + ((1317 / 4345) : ℂ) * ζ ^ 6 + ((1931 / 17380) : ℂ) * ζ ^ 8 + ((393 / 8690) : ℂ) * ζ ^ 9 + ((113 / 1580) : ℂ) * ζ ^ 11 - ((281 / 8690) : ℂ) * ζ ^ 12 - ((3057 / 17380) : ℂ) * ζ ^ 13 - ((381 / 1580) : ℂ) * ζ ^ 15 - ((3057 / 17380) : ℂ) * ζ ^ 17 - ((3591 / 17380) : ℂ) * ζ ^ 18 + ((453 / 8690) : ℂ) * ζ ^ 21 - ((203 / 4345) : ℂ) * ζ ^ 22 + ((2551 / 17380) : ℂ) * ζ ^ 24 + ((5501 / 17380) : ℂ) * ζ ^ 25 + ((87 / 395) : ℂ) * ζ ^ 27 - ((1931 / 17380) : ℂ) * ζ ^ 28 + ((3057 / 17380) : ℂ) * ζ ^ 29 + ((2157 / 8690) : ℂ) * ζ ^ 30 - ((113 / 1580) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((216 / 869) : ℂ) - ((1371 / 8690) : ℂ) * ζ ^ 1 - ((21 / 4345) : ℂ) * ζ ^ 2 + ((138 / 4345) : ℂ) * ζ ^ 3 - ((997 / 4345) : ℂ) * ζ ^ 4 + ((7691 / 17380) : ℂ) * ζ ^ 5 - ((2589 / 8690) : ℂ) * ζ ^ 6 - ((45 / 1738) : ℂ) * ζ ^ 7 + ((2567 / 8690) : ℂ) * ζ ^ 8 - ((5193 / 17380) : ℂ) * ζ ^ 9 + ((865 / 3476) : ℂ) * ζ ^ 10 + ((1275 / 3476) : ℂ) * ζ ^ 11 + ((351 / 3476) : ℂ) * ζ ^ 12 + ((857 / 17380) : ℂ) * ζ ^ 13 - ((103 / 790) : ℂ) * ζ ^ 14 + ((261 / 1738) : ℂ) * ζ ^ 15 - ((1412 / 4345) : ℂ) * ζ ^ 16 - ((303 / 3476) : ℂ) * ζ ^ 17 - ((266 / 4345) : ℂ) * ζ ^ 18 - ((1789 / 4345) : ℂ) * ζ ^ 19 + ((645 / 1738) : ℂ) * ζ ^ 20 - ((1262 / 4345) : ℂ) * ζ ^ 21 - ((689 / 8690) : ℂ) * ζ ^ 22 + ((1831 / 4345) : ℂ) * ζ ^ 23 - ((951 / 4345) : ℂ) * ζ ^ 24 + ((1473 / 17380) : ℂ) * ζ ^ 25 + ((1169 / 17380) : ℂ) * ζ ^ 26 - ((5061 / 17380) : ℂ) * ζ ^ 27 + ((487 / 17380) : ℂ) * ζ ^ 28 - ((399 / 8690) : ℂ) * ζ ^ 29 - ((2109 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_5_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 5 =
      (-((1929 / 8690) : ℂ) - ((39 / 790) : ℂ) * ζ ^ 1 - ((75 / 869) : ℂ) * ζ ^ 2 - ((329 / 17380) : ℂ) * ζ ^ 3 - ((279 / 1580) : ℂ) * ζ ^ 5 + ((587 / 3476) : ℂ) * ζ ^ 6 - ((883 / 8690) : ℂ) * ζ ^ 8 + ((4 / 395) : ℂ) * ζ ^ 9 + ((901 / 8690) : ℂ) * ζ ^ 11 + ((938 / 4345) : ℂ) * ζ ^ 12 + ((39 / 790) : ℂ) * ζ ^ 13 + ((34 / 4345) : ℂ) * ζ ^ 15 + ((39 / 790) : ℂ) * ζ ^ 17 - ((57 / 3476) : ℂ) * ζ ^ 18 + ((111 / 1580) : ℂ) * ζ ^ 21 + ((75 / 869) : ℂ) * ζ ^ 22 + ((1299 / 17380) : ℂ) * ζ ^ 24 + ((201 / 1580) : ℂ) * ζ ^ 25 + ((4767 / 17380) : ℂ) * ζ ^ 27 + ((883 / 8690) : ℂ) * ζ ^ 28 - ((39 / 790) : ℂ) * ζ ^ 29 + ((597 / 3476) : ℂ) * ζ ^ 30 - ((901 / 8690) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((3753 / 17380) : ℂ) + ((411 / 8690) : ℂ) * ζ ^ 1 + ((285 / 3476) : ℂ) * ζ ^ 2 + ((566 / 4345) : ℂ) * ζ ^ 3 - ((3291 / 8690) : ℂ) * ζ ^ 4 + ((1197 / 17380) : ℂ) * ζ ^ 5 - ((97 / 1738) : ℂ) * ζ ^ 6 - ((728 / 4345) : ℂ) * ζ ^ 7 + ((7831 / 17380) : ℂ) * ζ ^ 8 + ((69 / 1580) : ℂ) * ζ ^ 9 - ((2603 / 17380) : ℂ) * ζ ^ 10 - ((159 / 1580) : ℂ) * ζ ^ 11 + ((531 / 3476) : ℂ) * ζ ^ 12 + ((29 / 1738) : ℂ) * ζ ^ 13 - ((681 / 17380) : ℂ) * ζ ^ 14 - ((56 / 4345) : ℂ) * ζ ^ 15 + ((747 / 17380) : ℂ) * ζ ^ 16 + ((60 / 869) : ℂ) * ζ ^ 17 - ((113 / 17380) : ℂ) * ζ ^ 18 - ((507 / 8690) : ℂ) * ζ ^ 19 + ((1583 / 17380) : ℂ) * ζ ^ 20 - ((3043 / 17380) : ℂ) * ζ ^ 21 + ((393 / 17380) : ℂ) * ζ ^ 22 + ((1119 / 8690) : ℂ) * ζ ^ 23 - ((2967 / 17380) : ℂ) * ζ ^ 24 + ((19 / 1738) : ℂ) * ζ ^ 25 + ((981 / 8690) : ℂ) * ζ ^ 26 - ((59 / 1738) : ℂ) * ζ ^ 27 - ((3017 / 17380) : ℂ) * ζ ^ 28 + ((171 / 17380) : ℂ) * ζ ^ 29 + ((342 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_5_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 5 =
      (((509 / 1738) : ℂ) + ((149 / 3476) : ℂ) * ζ ^ 1 - ((1139 / 17380) : ℂ) * ζ ^ 2 + ((877 / 4345) : ℂ) * ζ ^ 3 + ((485 / 3476) : ℂ) * ζ ^ 5 - ((504 / 4345) : ℂ) * ζ ^ 6 - ((375 / 3476) : ℂ) * ζ ^ 8 + ((9 / 869) : ℂ) * ζ ^ 9 - ((4299 / 17380) : ℂ) * ζ ^ 11 + ((199 / 1738) : ℂ) * ζ ^ 12 - ((149 / 3476) : ℂ) * ζ ^ 13 + ((1393 / 17380) : ℂ) * ζ ^ 15 - ((149 / 3476) : ℂ) * ζ ^ 17 + ((1767 / 17380) : ℂ) * ζ ^ 18 - ((155 / 1738) : ℂ) * ζ ^ 21 + ((1139 / 17380) : ℂ) * ζ ^ 22 + ((149 / 869) : ℂ) * ζ ^ 24 - ((84 / 869) : ℂ) * ζ ^ 25 + ((4781 / 17380) : ℂ) * ζ ^ 27 + ((375 / 3476) : ℂ) * ζ ^ 28 + ((149 / 3476) : ℂ) * ζ ^ 29 - ((569 / 8690) : ℂ) * ζ ^ 30 + ((4299 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((177 / 869) : ℂ) + ((15 / 1738) : ℂ) * ζ ^ 1 - ((103 / 8690) : ℂ) * ζ ^ 2 - ((171 / 790) : ℂ) * ζ ^ 3 + ((1813 / 8690) : ℂ) * ζ ^ 4 + ((3 / 17380) : ℂ) * ζ ^ 5 - ((193 / 4345) : ℂ) * ζ ^ 6 - ((353 / 17380) : ℂ) * ζ ^ 7 - ((3323 / 17380) : ℂ) * ζ ^ 8 - ((141 / 869) : ℂ) * ζ ^ 9 + ((432 / 4345) : ℂ) * ζ ^ 10 - ((1209 / 8690) : ℂ) * ζ ^ 11 - ((1372 / 4345) : ℂ) * ζ ^ 12 + ((519 / 17380) : ℂ) * ζ ^ 13 - ((723 / 17380) : ℂ) * ζ ^ 14 - ((269 / 4345) : ℂ) * ζ ^ 15 + ((1703 / 17380) : ℂ) * ζ ^ 16 - ((119 / 4345) : ℂ) * ζ ^ 17 + ((1789 / 17380) : ℂ) * ζ ^ 18 + ((543 / 4345) : ℂ) * ζ ^ 19 - ((2929 / 17380) : ℂ) * ζ ^ 20 - ((85 / 1738) : ℂ) * ζ ^ 21 - ((643 / 17380) : ℂ) * ζ ^ 22 + ((1223 / 17380) : ℂ) * ζ ^ 23 - ((872 / 4345) : ℂ) * ζ ^ 24 - ((483 / 17380) : ℂ) * ζ ^ 25 + ((6 / 79) : ℂ) * ζ ^ 26 + ((93 / 3476) : ℂ) * ζ ^ 27 + ((33 / 316) : ℂ) * ζ ^ 28 + ((123 / 8690) : ℂ) * ζ ^ 29 - ((51 / 1738) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_5_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 5 =
      (((319 / 790) : ℂ) - ((21 / 79) : ℂ) * ζ ^ 1 - ((82 / 395) : ℂ) * ζ ^ 2 + ((301 / 790) : ℂ) * ζ ^ 3 - ((109 / 316) : ℂ) * ζ ^ 5 - ((431 / 790) : ℂ) * ζ ^ 6 - ((307 / 790) : ℂ) * ζ ^ 8 - ((22 / 79) : ℂ) * ζ ^ 9 - ((144 / 395) : ℂ) * ζ ^ 11 - ((647 / 1580) : ℂ) * ζ ^ 12 + ((21 / 79) : ℂ) * ζ ^ 13 - ((273 / 1580) : ℂ) * ζ ^ 15 + ((21 / 79) : ℂ) * ζ ^ 17 + ((271 / 395) : ℂ) * ζ ^ 18 + ((41 / 79) : ℂ) * ζ ^ 21 + ((82 / 395) : ℂ) * ζ ^ 22 + ((511 / 1580) : ℂ) * ζ ^ 24 + ((25 / 316) : ℂ) * ζ ^ 25 - ((311 / 1580) : ℂ) * ζ ^ 27 + ((307 / 790) : ℂ) * ζ ^ 28 - ((21 / 79) : ℂ) * ζ ^ 29 - ((751 / 1580) : ℂ) * ζ ^ 30 + ((144 / 395) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((68 / 395) : ℂ) + ((43 / 790) : ℂ) * ζ ^ 1 + ((49 / 395) : ℂ) * ζ ^ 2 - ((291 / 1580) : ℂ) * ζ ^ 3 + ((227 / 1580) : ℂ) * ζ ^ 4 + ((43 / 1580) : ℂ) * ζ ^ 5 + ((27 / 158) : ℂ) * ζ ^ 6 + ((727 / 1580) : ℂ) * ζ ^ 7 - ((37 / 395) : ℂ) * ζ ^ 8 + ((89 / 316) : ℂ) * ζ ^ 9 - ((181 / 1580) : ℂ) * ζ ^ 10 - ((7 / 10) : ℂ) * ζ ^ 11 + ((117 / 790) : ℂ) * ζ ^ 12 + ((99 / 1580) : ℂ) * ζ ^ 13 - ((19 / 316) : ℂ) * ζ ^ 14 + ((103 / 395) : ℂ) * ζ ^ 15 - ((26 / 395) : ℂ) * ζ ^ 16 + ((57 / 316) : ℂ) * ζ ^ 17 - ((391 / 1580) : ℂ) * ζ ^ 18 - ((181 / 790) : ℂ) * ζ ^ 19 + ((137 / 1580) : ℂ) * ζ ^ 20 - ((171 / 790) : ℂ) * ζ ^ 21 + ((249 / 790) : ℂ) * ζ ^ 22 - ((83 / 790) : ℂ) * ζ ^ 23 + ((10 / 79) : ℂ) * ζ ^ 24 - ((7 / 158) : ℂ) * ζ ^ 25 - ((147 / 395) : ℂ) * ζ ^ 26 + ((167 / 790) : ℂ) * ζ ^ 27 - ((102 / 395) : ℂ) * ζ ^ 28 - ((34 / 395) : ℂ) * ζ ^ 29 + ((87 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_5_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 5 =
      (-((3909 / 17380) : ℂ) + ((1073 / 8690) : ℂ) * ζ ^ 1 + ((8727 / 17380) : ℂ) * ζ ^ 2 - ((3247 / 17380) : ℂ) * ζ ^ 3 + ((1777 / 4345) : ℂ) * ζ ^ 5 + ((3609 / 8690) : ℂ) * ζ ^ 6 + ((10007 / 17380) : ℂ) * ζ ^ 8 + ((1547 / 4345) : ℂ) * ζ ^ 9 + ((8661 / 17380) : ℂ) * ζ ^ 11 + ((3911 / 17380) : ℂ) * ζ ^ 12 - ((1073 / 8690) : ℂ) * ζ ^ 13 + ((3193 / 17380) : ℂ) * ζ ^ 15 - ((1073 / 8690) : ℂ) * ζ ^ 17 - ((1774 / 4345) : ℂ) * ζ ^ 18 - ((9277 / 17380) : ℂ) * ζ ^ 21 - ((8727 / 17380) : ℂ) * ζ ^ 22 - ((6473 / 17380) : ℂ) * ζ ^ 24 - ((2481 / 8690) : ℂ) * ζ ^ 25 - ((8489 / 17380) : ℂ) * ζ ^ 27 - ((10007 / 17380) : ℂ) * ζ ^ 28 + ((1073 / 8690) : ℂ) * ζ ^ 29 + ((2669 / 17380) : ℂ) * ζ ^ 30 - ((8661 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((933 / 3476) : ℂ) - ((413 / 3476) : ℂ) * ζ ^ 1 - ((7859 / 17380) : ℂ) * ζ ^ 2 + ((369 / 1580) : ℂ) * ζ ^ 3 - ((2307 / 8690) : ℂ) * ζ ^ 4 - ((4047 / 17380) : ℂ) * ζ ^ 5 + ((1527 / 8690) : ℂ) * ζ ^ 6 - ((651 / 4345) : ℂ) * ζ ^ 7 - ((3403 / 17380) : ℂ) * ζ ^ 8 + ((789 / 17380) : ℂ) * ζ ^ 9 - ((273 / 1738) : ℂ) * ζ ^ 10 - ((57 / 17380) : ℂ) * ζ ^ 11 + ((4739 / 17380) : ℂ) * ζ ^ 12 + ((1 / 869) : ℂ) * ζ ^ 13 - ((575 / 3476) : ℂ) * ζ ^ 14 + ((3807 / 17380) : ℂ) * ζ ^ 15 - ((949 / 8690) : ℂ) * ζ ^ 16 - ((46 / 869) : ℂ) * ζ ^ 17 + ((2949 / 17380) : ℂ) * ζ ^ 18 - ((377 / 3476) : ℂ) * ζ ^ 19 - ((299 / 17380) : ℂ) * ζ ^ 20 + ((3799 / 17380) : ℂ) * ζ ^ 21 - ((1499 / 8690) : ℂ) * ζ ^ 22 - ((527 / 8690) : ℂ) * ζ ^ 23 + ((2793 / 17380) : ℂ) * ζ ^ 24 - ((3161 / 17380) : ℂ) * ζ ^ 25 + ((93 / 790) : ℂ) * ζ ^ 26 + ((1031 / 17380) : ℂ) * ζ ^ 27 - ((39 / 4345) : ℂ) * ζ ^ 28 + ((91 / 4345) : ℂ) * ζ ^ 29 - ((91 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_5_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 5 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_5_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 5 =
      (((23 / 220) : ℂ) - ((41 / 220) : ℂ) * ζ ^ 1 - ((9 / 110) : ℂ) * ζ ^ 2 + ((17 / 220) : ℂ) * ζ ^ 5 - ((21 / 110) : ℂ) * ζ ^ 6 - ((6 / 55) : ℂ) * ζ ^ 8 + ((7 / 220) : ℂ) * ζ ^ 9 - ((31 / 110) : ℂ) * ζ ^ 12 + ((41 / 220) : ℂ) * ζ ^ 13 + ((41 / 220) : ℂ) * ζ ^ 17 - ((1 / 220) : ℂ) * ζ ^ 18 + ((8 / 55) : ℂ) * ζ ^ 21 + ((9 / 110) : ℂ) * ζ ^ 22 - ((29 / 220) : ℂ) * ζ ^ 24 - ((29 / 110) : ℂ) * ζ ^ 25 + ((6 / 55) : ℂ) * ζ ^ 28 - ((41 / 220) : ℂ) * ζ ^ 29 - ((13 / 110) : ℂ) * ζ ^ 30) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((23 / 220) : ℂ) + ((7 / 220) : ℂ) * ζ ^ 1 + ((17 / 110) : ℂ) * ζ ^ 2 - ((39 / 220) : ℂ) * ζ ^ 4 - ((29 / 110) : ℂ) * ζ ^ 5 + ((67 / 220) : ℂ) * ζ ^ 6 + ((1 / 220) : ℂ) * ζ ^ 8 + ((53 / 220) : ℂ) * ζ ^ 9 - ((4 / 55) : ℂ) * ζ ^ 10 + ((129 / 220) : ℂ) * ζ ^ 12 + ((13 / 110) : ℂ) * ζ ^ 14 - ((7 / 220) : ℂ) * ζ ^ 17 - ((3 / 44) : ℂ) * ζ ^ 18 + ((39 / 220) : ℂ) * ζ ^ 20 + ((9 / 220) : ℂ) * ζ ^ 21 - ((43 / 220) : ℂ) * ζ ^ 22 + ((13 / 55) : ℂ) * ζ ^ 24 - ((1 / 110) : ℂ) * ζ ^ 25 + ((4 / 55) : ℂ) * ζ ^ 26 - ((91 / 220) : ℂ) * ζ ^ 28)

private theorem row18_transformedGeneratorA_term_0_5_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 5 =
      (((41 / 220) : ℂ) + ((13 / 110) : ℂ) * ζ ^ 1 - ((8 / 55) : ℂ) * ζ ^ 3 + ((2 / 55) : ℂ) * ζ ^ 5 - ((19 / 110) : ℂ) * ζ ^ 8 + ((13 / 220) : ℂ) * ζ ^ 9 - ((6 / 55) : ℂ) * ζ ^ 11 + ((21 / 220) : ℂ) * ζ ^ 12 - ((13 / 110) : ℂ) * ζ ^ 13 + ((12 / 55) : ℂ) * ζ ^ 15 - ((13 / 110) : ℂ) * ζ ^ 17 - ((27 / 220) : ℂ) * ζ ^ 21 - ((23 / 220) : ℂ) * ζ ^ 24 + ((9 / 110) : ℂ) * ζ ^ 25 - ((29 / 220) : ℂ) * ζ ^ 27 + ((19 / 110) : ℂ) * ζ ^ 28 + ((13 / 110) : ℂ) * ζ ^ 29 + ((6 / 55) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_0_5 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        0 5 =
      alternatingSixAmbientRow18TransformedGeneratorA
        0 5 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_0_5_0,
      row18_transformedGeneratorA_term_0_5_1,
      row18_transformedGeneratorA_term_0_5_2,
      row18_transformedGeneratorA_term_0_5_3,
      row18_transformedGeneratorA_term_0_5_4,
      row18_transformedGeneratorA_term_0_5_5,
      row18_transformedGeneratorA_term_0_5_6,
      row18_transformedGeneratorA_term_0_5_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_6_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 6 =
      (-((454 / 4345) : ℂ) + ((17 / 110) : ℂ) * ζ ^ 1 - ((1079 / 17380) : ℂ) * ζ ^ 2 + ((2073 / 17380) : ℂ) * ζ ^ 3 - ((703 / 4345) : ℂ) * ζ ^ 5 + ((1809 / 17380) : ℂ) * ζ ^ 6 + ((1172 / 4345) : ℂ) * ζ ^ 8 - ((558 / 4345) : ℂ) * ζ ^ 9 - ((1099 / 17380) : ℂ) * ζ ^ 11 - ((34 / 4345) : ℂ) * ζ ^ 12 - ((17 / 110) : ℂ) * ζ ^ 13 - ((3907 / 17380) : ℂ) * ζ ^ 15 - ((17 / 110) : ℂ) * ζ ^ 17 - ((169 / 8690) : ℂ) * ζ ^ 18 - ((217 / 17380) : ℂ) * ζ ^ 21 + ((1079 / 17380) : ℂ) * ζ ^ 22 + ((403 / 17380) : ℂ) * ζ ^ 24 + ((2749 / 8690) : ℂ) * ζ ^ 25 + ((1791 / 17380) : ℂ) * ζ ^ 27 - ((1172 / 4345) : ℂ) * ζ ^ 28 + ((17 / 110) : ℂ) * ζ ^ 29 + ((947 / 17380) : ℂ) * ζ ^ 30 + ((1099 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((202 / 4345) : ℂ) - ((1413 / 8690) : ℂ) * ζ ^ 1 + ((1989 / 17380) : ℂ) * ζ ^ 2 - ((201 / 1580) : ℂ) * ζ ^ 3 - ((50 / 869) : ℂ) * ζ ^ 4 + ((287 / 790) : ℂ) * ζ ^ 5 - ((1073 / 8690) : ℂ) * ζ ^ 6 + ((2309 / 17380) : ℂ) * ζ ^ 7 - ((2041 / 17380) : ℂ) * ζ ^ 8 - ((917 / 17380) : ℂ) * ζ ^ 9 + ((247 / 8690) : ℂ) * ζ ^ 10 + ((9 / 316) : ℂ) * ζ ^ 11 + ((307 / 1580) : ℂ) * ζ ^ 12 - ((333 / 17380) : ℂ) * ζ ^ 13 - ((997 / 17380) : ℂ) * ζ ^ 14 + ((967 / 17380) : ℂ) * ζ ^ 15 - ((724 / 4345) : ℂ) * ζ ^ 16 + ((111 / 8690) : ℂ) * ζ ^ 17 - ((809 / 17380) : ℂ) * ζ ^ 18 - ((1769 / 17380) : ℂ) * ζ ^ 19 + ((1809 / 8690) : ℂ) * ζ ^ 20 - ((609 / 8690) : ℂ) * ζ ^ 21 - ((1303 / 17380) : ℂ) * ζ ^ 22 + ((245 / 3476) : ℂ) * ζ ^ 23 + ((35 / 869) : ℂ) * ζ ^ 24 - ((1297 / 17380) : ℂ) * ζ ^ 25 + ((1841 / 17380) : ℂ) * ζ ^ 26 - ((73 / 869) : ℂ) * ζ ^ 27 - ((109 / 17380) : ℂ) * ζ ^ 28 + ((741 / 17380) : ℂ) * ζ ^ 29 - ((969 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_6_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 6 =
      (((601 / 1738) : ℂ) + ((983 / 17380) : ℂ) * ζ ^ 1 - ((1489 / 17380) : ℂ) * ζ ^ 2 - ((3959 / 17380) : ℂ) * ζ ^ 3 + ((2989 / 17380) : ℂ) * ζ ^ 5 + ((747 / 8690) : ℂ) * ζ ^ 6 - ((897 / 3476) : ℂ) * ζ ^ 8 - ((1901 / 17380) : ℂ) * ζ ^ 9 + ((4937 / 17380) : ℂ) * ζ ^ 11 - ((357 / 1738) : ℂ) * ζ ^ 12 - ((983 / 17380) : ℂ) * ζ ^ 13 - ((296 / 4345) : ℂ) * ζ ^ 15 - ((983 / 17380) : ℂ) * ζ ^ 17 - ((373 / 17380) : ℂ) * ζ ^ 18 - ((3371 / 17380) : ℂ) * ζ ^ 21 + ((1489 / 17380) : ℂ) * ζ ^ 22 + ((1145 / 3476) : ℂ) * ζ ^ 24 - ((1003 / 8690) : ℂ) * ζ ^ 25 - ((1439 / 8690) : ℂ) * ζ ^ 27 + ((897 / 3476) : ℂ) * ζ ^ 28 + ((983 / 17380) : ℂ) * ζ ^ 29 + ((958 / 4345) : ℂ) * ζ ^ 30 - ((4937 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((3131 / 8690) : ℂ) - ((1187 / 17380) : ℂ) * ζ ^ 1 + ((1421 / 8690) : ℂ) * ζ ^ 2 + ((1091 / 4345) : ℂ) * ζ ^ 3 + ((1271 / 8690) : ℂ) * ζ ^ 4 - ((877 / 8690) : ℂ) * ζ ^ 5 - ((233 / 3476) : ℂ) * ζ ^ 6 - ((3449 / 17380) : ℂ) * ζ ^ 7 + ((17 / 790) : ℂ) * ζ ^ 8 + ((573 / 4345) : ℂ) * ζ ^ 9 - ((137 / 1580) : ℂ) * ζ ^ 10 - ((773 / 17380) : ℂ) * ζ ^ 11 + ((487 / 3476) : ℂ) * ζ ^ 12 + ((27 / 1738) : ℂ) * ζ ^ 13 - ((207 / 4345) : ℂ) * ζ ^ 14 + ((97 / 8690) : ℂ) * ζ ^ 15 - ((58 / 4345) : ℂ) * ζ ^ 16 - ((733 / 17380) : ℂ) * ζ ^ 17 - ((199 / 4345) : ℂ) * ζ ^ 18 + ((777 / 17380) : ℂ) * ζ ^ 19 + ((1137 / 17380) : ℂ) * ζ ^ 20 + ((162 / 4345) : ℂ) * ζ ^ 21 - ((9 / 4345) : ℂ) * ζ ^ 22 - ((373 / 8690) : ℂ) * ζ ^ 23 - ((1201 / 8690) : ℂ) * ζ ^ 24 - ((19 / 3476) : ℂ) * ζ ^ 25 + ((584 / 4345) : ℂ) * ζ ^ 26 + ((563 / 17380) : ℂ) * ζ ^ 27 - ((152 / 4345) : ℂ) * ζ ^ 28 - ((57 / 4345) : ℂ) * ζ ^ 29)

private theorem row18_transformedGeneratorA_term_0_6_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 6 =
      (-((71 / 869) : ℂ) - ((1197 / 8690) : ℂ) * ζ ^ 1 - ((351 / 17380) : ℂ) * ζ ^ 2 + ((47 / 395) : ℂ) * ζ ^ 3 - ((1477 / 17380) : ℂ) * ζ ^ 5 - ((81 / 4345) : ℂ) * ζ ^ 6 - ((12 / 869) : ℂ) * ζ ^ 8 + ((512 / 4345) : ℂ) * ζ ^ 9 - ((309 / 1580) : ℂ) * ζ ^ 11 - ((69 / 3476) : ℂ) * ζ ^ 12 + ((1197 / 8690) : ℂ) * ζ ^ 13 - ((28 / 395) : ℂ) * ζ ^ 15 + ((1197 / 8690) : ℂ) * ζ ^ 17 - ((1481 / 8690) : ℂ) * ζ ^ 18 + ((227 / 4345) : ℂ) * ζ ^ 21 + ((351 / 17380) : ℂ) * ζ ^ 22 - ((315 / 1738) : ℂ) * ζ ^ 24 - ((917 / 17380) : ℂ) * ζ ^ 25 + ((301 / 1580) : ℂ) * ζ ^ 27 + ((12 / 869) : ℂ) * ζ ^ 28 - ((1197 / 8690) : ℂ) * ζ ^ 29 - ((721 / 8690) : ℂ) * ζ ^ 30 + ((309 / 1580) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((71 / 869) : ℂ) + ((949 / 8690) : ℂ) * ζ ^ 1 - ((252 / 4345) : ℂ) * ζ ^ 2 - ((3257 / 17380) : ℂ) * ζ ^ 3 - ((471 / 4345) : ℂ) * ζ ^ 4 + ((11 / 1580) : ℂ) * ζ ^ 5 + ((251 / 17380) : ℂ) * ζ ^ 6 + ((97 / 1580) : ℂ) * ζ ^ 7 + ((153 / 8690) : ℂ) * ζ ^ 8 - ((332 / 4345) : ℂ) * ζ ^ 9 + ((1511 / 8690) : ℂ) * ζ ^ 10 + ((1533 / 8690) : ℂ) * ζ ^ 11 + ((3033 / 17380) : ℂ) * ζ ^ 12 - ((241 / 4345) : ℂ) * ζ ^ 13 + ((21 / 8690) : ℂ) * ζ ^ 14 - ((593 / 4345) : ℂ) * ζ ^ 15 + ((282 / 4345) : ℂ) * ζ ^ 16 + ((837 / 17380) : ℂ) * ζ ^ 17 + ((1263 / 8690) : ℂ) * ζ ^ 18 - ((151 / 17380) : ℂ) * ζ ^ 19 + ((25 / 316) : ℂ) * ζ ^ 20 - ((578 / 4345) : ℂ) * ζ ^ 21 + ((89 / 17380) : ℂ) * ζ ^ 22 + ((6 / 55) : ℂ) * ζ ^ 23 + ((1701 / 17380) : ℂ) * ζ ^ 24 + ((93 / 8690) : ℂ) * ζ ^ 25 - ((348 / 4345) : ℂ) * ζ ^ 26 - ((309 / 4345) : ℂ) * ζ ^ 27 - ((393 / 8690) : ℂ) * ζ ^ 28 + ((18 / 4345) : ℂ) * ζ ^ 29 + ((63 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_6_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 6 =
      (-((4 / 395) : ℂ) + ((43 / 316) : ℂ) * ζ ^ 1 - ((191 / 1580) : ℂ) * ζ ^ 2 - ((42 / 395) : ℂ) * ζ ^ 3 + ((43 / 316) : ℂ) * ζ ^ 5 - ((49 / 1580) : ℂ) * ζ ^ 6 - ((267 / 1580) : ℂ) * ζ ^ 8 + ((9 / 79) : ℂ) * ζ ^ 9 + ((21 / 395) : ℂ) * ζ ^ 11 + ((9 / 1580) : ℂ) * ζ ^ 12 - ((43 / 316) : ℂ) * ζ ^ 13 + ((487 / 1580) : ℂ) * ζ ^ 15 - ((43 / 316) : ℂ) * ζ ^ 17 + ((113 / 1580) : ℂ) * ζ ^ 18 - ((13 / 158) : ℂ) * ζ ^ 21 + ((191 / 1580) : ℂ) * ζ ^ 22 - ((63 / 395) : ℂ) * ζ ^ 24 - ((19 / 395) : ℂ) * ζ ^ 27 + ((267 / 1580) : ℂ) * ζ ^ 28 + ((43 / 316) : ℂ) * ζ ^ 29 - ((277 / 1580) : ℂ) * ζ ^ 30 - ((21 / 395) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((16 / 79) : ℂ) - ((63 / 1580) : ℂ) * ζ ^ 1 + ((143 / 1580) : ℂ) * ζ ^ 2 + ((61 / 395) : ℂ) * ζ ^ 3 + ((41 / 395) : ℂ) * ζ ^ 4 - ((29 / 790) : ℂ) * ζ ^ 5 - ((33 / 395) : ℂ) * ζ ^ 6 - ((31 / 395) : ℂ) * ζ ^ 7 - ((27 / 790) : ℂ) * ζ ^ 8 - ((97 / 790) : ℂ) * ζ ^ 9 - ((7 / 158) : ℂ) * ζ ^ 10 + ((29 / 158) : ℂ) * ζ ^ 11 + ((41 / 158) : ℂ) * ζ ^ 12 + ((44 / 395) : ℂ) * ζ ^ 13 - ((9 / 316) : ℂ) * ζ ^ 14 - ((241 / 790) : ℂ) * ζ ^ 15 - ((113 / 395) : ℂ) * ζ ^ 16 - ((71 / 790) : ℂ) * ζ ^ 17 + ((33 / 790) : ℂ) * ζ ^ 18 + ((20 / 79) : ℂ) * ζ ^ 19 + ((291 / 1580) : ℂ) * ζ ^ 20 + ((9 / 790) : ℂ) * ζ ^ 21 - ((9 / 79) : ℂ) * ζ ^ 22 - ((151 / 790) : ℂ) * ζ ^ 23 - ((3 / 158) : ℂ) * ζ ^ 24 + ((14 / 79) : ℂ) * ζ ^ 25 + ((7 / 79) : ℂ) * ζ ^ 26 + ((59 / 790) : ℂ) * ζ ^ 27 - ((17 / 395) : ℂ) * ζ ^ 28 - ((32 / 395) : ℂ) * ζ ^ 29 + ((1 / 79) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_6_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 6 =
      (-((62 / 395) : ℂ) - ((343 / 1738) : ℂ) * ζ ^ 1 + ((201 / 3476) : ℂ) * ζ ^ 2 + ((591 / 17380) : ℂ) * ζ ^ 3 + ((289 / 3476) : ℂ) * ζ ^ 5 - ((34 / 869) : ℂ) * ζ ^ 6 + ((239 / 1580) : ℂ) * ζ ^ 8 + ((71 / 869) : ℂ) * ζ ^ 9 + ((3 / 220) : ℂ) * ζ ^ 11 + ((73 / 395) : ℂ) * ζ ^ 12 + ((343 / 1738) : ℂ) * ζ ^ 13 - ((1189 / 17380) : ℂ) * ζ ^ 15 + ((343 / 1738) : ℂ) * ζ ^ 17 + ((50 / 869) : ℂ) * ζ ^ 18 + ((63 / 1738) : ℂ) * ζ ^ 21 - ((201 / 3476) : ℂ) * ζ ^ 22 - ((153 / 790) : ℂ) * ζ ^ 24 - ((975 / 3476) : ℂ) * ζ ^ 25 - ((267 / 4345) : ℂ) * ζ ^ 27 - ((239 / 1580) : ℂ) * ζ ^ 28 - ((343 / 1738) : ℂ) * ζ ^ 29 + ((59 / 1738) : ℂ) * ζ ^ 30 - ((3 / 220) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((149 / 869) : ℂ) + ((501 / 3476) : ℂ) * ζ ^ 1 - ((967 / 17380) : ℂ) * ζ ^ 2 - ((1083 / 17380) : ℂ) * ζ ^ 3 - ((3349 / 17380) : ℂ) * ζ ^ 4 - ((445 / 1738) : ℂ) * ζ ^ 5 - ((47 / 4345) : ℂ) * ζ ^ 6 + ((57 / 790) : ℂ) * ζ ^ 7 + ((3 / 110) : ℂ) * ζ ^ 8 + ((2941 / 17380) : ℂ) * ζ ^ 9 - ((951 / 8690) : ℂ) * ζ ^ 10 - ((777 / 8690) : ℂ) * ζ ^ 11 - ((261 / 4345) : ℂ) * ζ ^ 12 - ((1257 / 17380) : ℂ) * ζ ^ 13 + ((613 / 17380) : ℂ) * ζ ^ 14 + ((157 / 790) : ℂ) * ζ ^ 15 + ((486 / 4345) : ℂ) * ζ ^ 16 - ((403 / 17380) : ℂ) * ζ ^ 17 - ((417 / 17380) : ℂ) * ζ ^ 18 - ((787 / 4345) : ℂ) * ζ ^ 19 - ((274 / 4345) : ℂ) * ζ ^ 20 + ((41 / 790) : ℂ) * ζ ^ 21 + ((111 / 790) : ℂ) * ζ ^ 22 + ((1893 / 17380) : ℂ) * ζ ^ 23 + ((1473 / 8690) : ℂ) * ζ ^ 24 + ((347 / 17380) : ℂ) * ζ ^ 25 + ((1 / 44) : ℂ) * ζ ^ 26 + ((141 / 17380) : ℂ) * ζ ^ 27 - ((14 / 869) : ℂ) * ζ ^ 28 + ((7 / 3476) : ℂ) * ζ ^ 29 - ((49 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_6_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 6 =
      (((1 / 22) : ℂ) + ((1 / 44) : ℂ) * ζ ^ 1 + ((3 / 44) : ℂ) * ζ ^ 3 - ((9 / 44) : ℂ) * ζ ^ 5 - ((1 / 11) : ℂ) * ζ ^ 8 - ((5 / 44) : ℂ) * ζ ^ 9 - ((3 / 22) : ℂ) * ζ ^ 11 - ((3 / 44) : ℂ) * ζ ^ 12 - ((1 / 44) : ℂ) * ζ ^ 13 + ((1 / 44) : ℂ) * ζ ^ 15 - ((1 / 44) : ℂ) * ζ ^ 17 - ((1 / 4) : ℂ) * ζ ^ 18 + ((7 / 44) : ℂ) * ζ ^ 21 + ((2 / 11) : ℂ) * ζ ^ 24 + ((5 / 22) : ℂ) * ζ ^ 25 + ((1 / 44) : ℂ) * ζ ^ 27 + ((1 / 11) : ℂ) * ζ ^ 28 + ((1 / 44) : ℂ) * ζ ^ 29 + ((3 / 22) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_6_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 6 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_6_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 6 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_0_6 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        0 6 =
      alternatingSixAmbientRow18TransformedGeneratorA
        0 6 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_0_6_0,
      row18_transformedGeneratorA_term_0_6_1,
      row18_transformedGeneratorA_term_0_6_2,
      row18_transformedGeneratorA_term_0_6_3,
      row18_transformedGeneratorA_term_0_6_4,
      row18_transformedGeneratorA_term_0_6_5,
      row18_transformedGeneratorA_term_0_6_6,
      row18_transformedGeneratorA_term_0_6_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_7_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 7 =
      (-((633 / 1580) : ℂ) + ((3173 / 17380) : ℂ) * ζ ^ 1 + ((203 / 869) : ℂ) * ζ ^ 2 + ((103 / 3476) : ℂ) * ζ ^ 3 + ((3409 / 17380) : ℂ) * ζ ^ 5 - ((113 / 869) : ℂ) * ζ ^ 6 + ((167 / 790) : ℂ) * ζ ^ 8 - ((3281 / 17380) : ℂ) * ζ ^ 9 + ((355 / 3476) : ℂ) * ζ ^ 11 - ((109 / 790) : ℂ) * ζ ^ 12 - ((3173 / 17380) : ℂ) * ζ ^ 13 + ((247 / 3476) : ℂ) * ζ ^ 15 - ((3173 / 17380) : ℂ) * ζ ^ 17 - ((4 / 869) : ℂ) * ζ ^ 18 - ((361 / 17380) : ℂ) * ζ ^ 21 - ((203 / 869) : ℂ) * ζ ^ 22 + ((109 / 1580) : ℂ) * ζ ^ 24 - ((59 / 4345) : ℂ) * ζ ^ 25 + ((1105 / 3476) : ℂ) * ζ ^ 27 - ((167 / 790) : ℂ) * ζ ^ 28 + ((3173 / 17380) : ℂ) * ζ ^ 29 + ((83 / 869) : ℂ) * ζ ^ 30 - ((355 / 3476) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((1599 / 4345) : ℂ) - ((1031 / 17380) : ℂ) * ζ ^ 1 - ((5047 / 17380) : ℂ) * ζ ^ 2 - ((2227 / 8690) : ℂ) * ζ ^ 3 - ((4861 / 17380) : ℂ) * ζ ^ 4 - ((541 / 3476) : ℂ) * ζ ^ 5 + ((2383 / 8690) : ℂ) * ζ ^ 6 + ((1088 / 4345) : ℂ) * ζ ^ 7 + ((2587 / 17380) : ℂ) * ζ ^ 8 + ((125 / 1738) : ℂ) * ζ ^ 9 - ((523 / 3476) : ℂ) * ζ ^ 10 + ((767 / 4345) : ℂ) * ζ ^ 11 + ((377 / 1738) : ℂ) * ζ ^ 12 - ((2833 / 17380) : ℂ) * ζ ^ 13 + ((2681 / 8690) : ℂ) * ζ ^ 14 - ((3533 / 17380) : ℂ) * ζ ^ 15 - ((5697 / 17380) : ℂ) * ζ ^ 16 + ((2119 / 17380) : ℂ) * ζ ^ 17 - ((1359 / 17380) : ℂ) * ζ ^ 18 - ((213 / 1580) : ℂ) * ζ ^ 19 + ((659 / 1580) : ℂ) * ζ ^ 20 + ((2049 / 17380) : ℂ) * ζ ^ 21 - ((226 / 4345) : ℂ) * ζ ^ 22 + ((127 / 3476) : ℂ) * ζ ^ 23 - ((436 / 4345) : ℂ) * ζ ^ 24 + ((2697 / 17380) : ℂ) * ζ ^ 25 + ((261 / 8690) : ℂ) * ζ ^ 26 - ((5361 / 17380) : ℂ) * ζ ^ 27 + ((2147 / 17380) : ℂ) * ζ ^ 28 + ((399 / 8690) : ℂ) * ζ ^ 29 - ((1083 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_7_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 7 =
      (-((7473 / 17380) : ℂ) - ((729 / 8690) : ℂ) * ζ ^ 1 + ((78 / 869) : ℂ) * ζ ^ 2 - ((5669 / 17380) : ℂ) * ζ ^ 3 - ((1959 / 17380) : ℂ) * ζ ^ 5 - ((823 / 3476) : ℂ) * ζ ^ 6 + ((2851 / 4345) : ℂ) * ζ ^ 8 - ((887 / 8690) : ℂ) * ζ ^ 9 + ((437 / 17380) : ℂ) * ζ ^ 11 + ((1778 / 4345) : ℂ) * ζ ^ 12 + ((729 / 8690) : ℂ) * ζ ^ 13 + ((304 / 4345) : ℂ) * ζ ^ 15 + ((729 / 8690) : ℂ) * ζ ^ 17 + ((153 / 3476) : ℂ) * ζ ^ 18 + ((2184 / 4345) : ℂ) * ζ ^ 21 - ((78 / 869) : ℂ) * ζ ^ 22 - ((6231 / 17380) : ℂ) * ζ ^ 24 + ((501 / 17380) : ℂ) * ζ ^ 25 - ((93 / 17380) : ℂ) * ζ ^ 27 - ((2851 / 4345) : ℂ) * ζ ^ 28 - ((729 / 8690) : ℂ) * ζ ^ 29 - ((78 / 869) : ℂ) * ζ ^ 30 - ((437 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((1842 / 4345) : ℂ) + ((2367 / 17380) : ℂ) * ζ ^ 1 - ((1191 / 8690) : ℂ) * ζ ^ 2 + ((73 / 395) : ℂ) * ζ ^ 3 - ((3357 / 17380) : ℂ) * ζ ^ 4 + ((423 / 8690) : ℂ) * ζ ^ 5 + ((2579 / 17380) : ℂ) * ζ ^ 6 - ((641 / 4345) : ℂ) * ζ ^ 7 - ((1781 / 4345) : ℂ) * ζ ^ 8 - ((2619 / 17380) : ℂ) * ζ ^ 9 + ((1607 / 8690) : ℂ) * ζ ^ 10 + ((6093 / 17380) : ℂ) * ζ ^ 11 - ((981 / 3476) : ℂ) * ζ ^ 12 + ((101 / 17380) : ℂ) * ζ ^ 13 + ((2457 / 17380) : ℂ) * ζ ^ 14 + ((25 / 1738) : ℂ) * ζ ^ 15 + ((441 / 8690) : ℂ) * ζ ^ 16 + ((201 / 4345) : ℂ) * ζ ^ 17 - ((65 / 1738) : ℂ) * ζ ^ 18 + ((42 / 869) : ℂ) * ζ ^ 19 - ((1417 / 17380) : ℂ) * ζ ^ 20 - ((1847 / 8690) : ℂ) * ζ ^ 21 - ((246 / 4345) : ℂ) * ζ ^ 22 + ((867 / 17380) : ℂ) * ζ ^ 23 + ((552 / 4345) : ℂ) * ζ ^ 24 + ((7 / 790) : ℂ) * ζ ^ 25 - ((2397 / 17380) : ℂ) * ζ ^ 26 + ((221 / 8690) : ℂ) * ζ ^ 27 + ((4273 / 17380) : ℂ) * ζ ^ 28 - ((171 / 17380) : ℂ) * ζ ^ 29 - ((1767 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_7_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 7 =
      (((249 / 1580) : ℂ) - ((3821 / 17380) : ℂ) * ζ ^ 1 - ((1431 / 4345) : ℂ) * ζ ^ 2 - ((348 / 4345) : ℂ) * ζ ^ 3 - ((332 / 4345) : ℂ) * ζ ^ 5 - ((2521 / 17380) : ℂ) * ζ ^ 6 - ((31 / 790) : ℂ) * ζ ^ 8 + ((1561 / 8690) : ℂ) * ζ ^ 9 + ((3301 / 17380) : ℂ) * ζ ^ 11 - ((93 / 790) : ℂ) * ζ ^ 12 + ((3821 / 17380) : ℂ) * ζ ^ 13 - ((1431 / 8690) : ℂ) * ζ ^ 15 + ((3821 / 17380) : ℂ) * ζ ^ 17 + ((397 / 17380) : ℂ) * ζ ^ 18 - ((62 / 4345) : ℂ) * ζ ^ 21 + ((1431 / 4345) : ℂ) * ζ ^ 22 - ((7 / 1580) : ℂ) * ζ ^ 24 - ((2493 / 17380) : ℂ) * ζ ^ 25 - ((3269 / 17380) : ℂ) * ζ ^ 27 + ((31 / 790) : ℂ) * ζ ^ 28 - ((3821 / 17380) : ℂ) * ζ ^ 29 + ((243 / 4345) : ℂ) * ζ ^ 30 - ((3301 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1189 / 17380) : ℂ) + ((5367 / 17380) : ℂ) * ζ ^ 1 + ((365 / 869) : ℂ) * ζ ^ 2 + ((29 / 158) : ℂ) * ζ ^ 3 + ((339 / 3476) : ℂ) * ζ ^ 4 - ((251 / 3476) : ℂ) * ζ ^ 5 - ((22 / 395) : ℂ) * ζ ^ 6 + ((185 / 3476) : ℂ) * ζ ^ 7 - ((2061 / 17380) : ℂ) * ζ ^ 8 - ((331 / 1580) : ℂ) * ζ ^ 9 - ((201 / 4345) : ℂ) * ζ ^ 10 - ((83 / 3476) : ℂ) * ζ ^ 11 + ((276 / 4345) : ℂ) * ζ ^ 12 + ((1673 / 17380) : ℂ) * ζ ^ 13 + ((1971 / 8690) : ℂ) * ζ ^ 14 + ((546 / 4345) : ℂ) * ζ ^ 15 - ((169 / 1738) : ℂ) * ζ ^ 16 - ((114 / 869) : ℂ) * ζ ^ 17 - ((1403 / 8690) : ℂ) * ζ ^ 18 - ((1007 / 8690) : ℂ) * ζ ^ 19 - ((77 / 1580) : ℂ) * ζ ^ 20 - ((125 / 869) : ℂ) * ζ ^ 21 - ((1317 / 17380) : ℂ) * ζ ^ 22 - ((1283 / 17380) : ℂ) * ζ ^ 23 + ((761 / 17380) : ℂ) * ζ ^ 24 + ((2109 / 17380) : ℂ) * ζ ^ 25 + ((303 / 4345) : ℂ) * ζ ^ 26 + ((801 / 17380) : ℂ) * ζ ^ 27 + ((18 / 4345) : ℂ) * ζ ^ 28 - ((123 / 8690) : ℂ) * ζ ^ 29 - ((12 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_7_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 7 =
      (((699 / 1580) : ℂ) - ((7 / 395) : ℂ) * ζ ^ 1 + ((293 / 790) : ℂ) * ζ ^ 2 + ((85 / 158) : ℂ) * ζ ^ 3 - ((299 / 1580) : ℂ) * ζ ^ 5 + ((11 / 20) : ℂ) * ζ ^ 6 - ((531 / 790) : ℂ) * ζ ^ 8 - ((121 / 395) : ℂ) * ζ ^ 9 - ((5 / 158) : ℂ) * ζ ^ 11 - ((84 / 395) : ℂ) * ζ ^ 12 + ((7 / 395) : ℂ) * ζ ^ 13 - ((21 / 316) : ℂ) * ζ ^ 15 + ((7 / 395) : ℂ) * ζ ^ 17 - ((823 / 1580) : ℂ) * ζ ^ 18 - ((136 / 395) : ℂ) * ζ ^ 21 - ((293 / 790) : ℂ) * ζ ^ 22 + ((152 / 395) : ℂ) * ζ ^ 24 + ((271 / 1580) : ℂ) * ζ ^ 25 + ((65 / 316) : ℂ) * ζ ^ 27 + ((531 / 790) : ℂ) * ζ ^ 28 - ((7 / 395) : ℂ) * ζ ^ 29 + ((307 / 1580) : ℂ) * ζ ^ 30 + ((5 / 158) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((333 / 1580) : ℂ) - ((123 / 790) : ℂ) * ζ ^ 1 - ((187 / 790) : ℂ) * ζ ^ 2 - ((507 / 1580) : ℂ) * ζ ^ 3 + ((63 / 790) : ℂ) * ζ ^ 4 + ((489 / 1580) : ℂ) * ζ ^ 5 + ((3 / 20) : ℂ) * ζ ^ 6 + ((71 / 1580) : ℂ) * ζ ^ 7 + ((389 / 1580) : ℂ) * ζ ^ 8 + ((849 / 1580) : ℂ) * ζ ^ 9 - ((99 / 790) : ℂ) * ζ ^ 10 - ((341 / 790) : ℂ) * ζ ^ 11 - ((709 / 1580) : ℂ) * ζ ^ 12 - ((109 / 316) : ℂ) * ζ ^ 13 - ((447 / 1580) : ℂ) * ζ ^ 14 + ((53 / 790) : ℂ) * ζ ^ 15 + ((661 / 1580) : ℂ) * ζ ^ 16 + ((467 / 1580) : ℂ) * ζ ^ 17 + ((439 / 1580) : ℂ) * ζ ^ 18 + ((183 / 790) : ℂ) * ζ ^ 19 - ((7 / 158) : ℂ) * ζ ^ 20 + ((11 / 790) : ℂ) * ζ ^ 21 + ((27 / 790) : ℂ) * ζ ^ 22 - ((179 / 790) : ℂ) * ζ ^ 23 - ((23 / 158) : ℂ) * ζ ^ 24 - ((317 / 790) : ℂ) * ζ ^ 25 - ((27 / 395) : ℂ) * ζ ^ 26 + ((47 / 395) : ℂ) * ζ ^ 27 - ((29 / 395) : ℂ) * ζ ^ 28 + ((34 / 395) : ℂ) * ζ ^ 29 + ((24 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_7_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 7 =
      (-((47 / 316) : ℂ) - ((71 / 3476) : ℂ) * ζ ^ 1 + ((11 / 790) : ℂ) * ζ ^ 2 - ((2141 / 8690) : ℂ) * ζ ^ 3 + ((507 / 3476) : ℂ) * ζ ^ 5 - ((11 / 790) : ℂ) * ζ ^ 6 + ((63 / 158) : ℂ) * ζ ^ 8 + ((161 / 1738) : ℂ) * ζ ^ 9 - ((521 / 4345) : ℂ) * ζ ^ 11 + ((71 / 3476) : ℂ) * ζ ^ 13 + ((483 / 17380) : ℂ) * ζ ^ 15 + ((71 / 3476) : ℂ) * ζ ^ 17 + ((209 / 1580) : ℂ) * ζ ^ 18 + ((141 / 3476) : ℂ) * ζ ^ 21 - ((11 / 790) : ℂ) * ζ ^ 22 - ((67 / 316) : ℂ) * ζ ^ 24 - ((289 / 1738) : ℂ) * ζ ^ 25 - ((2069 / 17380) : ℂ) * ζ ^ 27 - ((63 / 158) : ℂ) * ζ ^ 28 - ((71 / 3476) : ℂ) * ζ ^ 29 + ((209 / 1580) : ℂ) * ζ ^ 30 + ((521 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((3341 / 17380) : ℂ) + ((12 / 869) : ℂ) * ζ ^ 1 - ((1131 / 17380) : ℂ) * ζ ^ 2 + ((779 / 4345) : ℂ) * ζ ^ 3 - ((709 / 3476) : ℂ) * ζ ^ 4 - ((641 / 3476) : ℂ) * ζ ^ 5 - ((437 / 4345) : ℂ) * ζ ^ 6 - ((4571 / 17380) : ℂ) * ζ ^ 7 - ((417 / 1738) : ℂ) * ζ ^ 8 + ((653 / 8690) : ℂ) * ζ ^ 9 - ((813 / 17380) : ℂ) * ζ ^ 10 + ((3873 / 17380) : ℂ) * ζ ^ 11 + ((2927 / 8690) : ℂ) * ζ ^ 12 - ((21 / 869) : ℂ) * ζ ^ 13 - ((1293 / 17380) : ℂ) * ζ ^ 14 + ((343 / 8690) : ℂ) * ζ ^ 15 - ((871 / 8690) : ℂ) * ζ ^ 16 + ((747 / 17380) : ℂ) * ζ ^ 17 + ((23 / 1738) : ℂ) * ζ ^ 18 - ((291 / 17380) : ℂ) * ζ ^ 19 + ((813 / 17380) : ℂ) * ζ ^ 20 - ((2491 / 17380) : ℂ) * ζ ^ 21 - ((2131 / 17380) : ℂ) * ζ ^ 22 + ((775 / 3476) : ℂ) * ζ ^ 23 + ((1064 / 4345) : ℂ) * ζ ^ 24 + ((1561 / 8690) : ℂ) * ζ ^ 25 + ((5403 / 17380) : ℂ) * ζ ^ 26 + ((643 / 8690) : ℂ) * ζ ^ 27 - ((13 / 790) : ℂ) * ζ ^ 28 - ((91 / 4345) : ℂ) * ζ ^ 29 - ((7 / 220) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_0_7_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 7 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_0_7_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 7 =
      (((4 / 55) : ℂ) - ((91 / 220) : ℂ) * ζ ^ 2 + ((17 / 110) : ℂ) * ζ ^ 3 - ((29 / 220) : ℂ) * ζ ^ 6 - ((43 / 220) : ℂ) * ζ ^ 8 - ((1 / 110) : ℂ) * ζ ^ 11 - ((6 / 55) : ℂ) * ζ ^ 12 - ((51 / 220) : ℂ) * ζ ^ 15 + ((53 / 220) : ℂ) * ζ ^ 18 + ((91 / 220) : ℂ) * ζ ^ 22 + ((21 / 110) : ℂ) * ζ ^ 24 - ((7 / 220) : ℂ) * ζ ^ 27 + ((43 / 220) : ℂ) * ζ ^ 28 - ((13 / 55) : ℂ) * ζ ^ 30 + ((1 / 110) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((4 / 55) : ℂ) + ((91 / 220) : ℂ) * ζ ^ 2)

private theorem row18_transformedGeneratorA_term_0_7_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          0 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 7 =
      (((41 / 220) : ℂ) + ((13 / 110) : ℂ) * ζ ^ 1 - ((8 / 55) : ℂ) * ζ ^ 3 + ((2 / 55) : ℂ) * ζ ^ 5 - ((19 / 110) : ℂ) * ζ ^ 8 + ((13 / 220) : ℂ) * ζ ^ 9 - ((6 / 55) : ℂ) * ζ ^ 11 + ((21 / 220) : ℂ) * ζ ^ 12 - ((13 / 110) : ℂ) * ζ ^ 13 + ((12 / 55) : ℂ) * ζ ^ 15 - ((13 / 110) : ℂ) * ζ ^ 17 - ((27 / 220) : ℂ) * ζ ^ 21 - ((23 / 220) : ℂ) * ζ ^ 24 + ((9 / 110) : ℂ) * ζ ^ 25 - ((29 / 220) : ℂ) * ζ ^ 27 + ((19 / 110) : ℂ) * ζ ^ 28 + ((13 / 110) : ℂ) * ζ ^ 29 + ((6 / 55) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_0_7 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        0 7 =
      alternatingSixAmbientRow18TransformedGeneratorA
        0 7 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_0_7_0,
      row18_transformedGeneratorA_term_0_7_1,
      row18_transformedGeneratorA_term_0_7_2,
      row18_transformedGeneratorA_term_0_7_3,
      row18_transformedGeneratorA_term_0_7_4,
      row18_transformedGeneratorA_term_0_7_5,
      row18_transformedGeneratorA_term_0_7_6,
      row18_transformedGeneratorA_term_0_7_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

/-- The checked transformed-generator equality on output row
0 of ambient row 18. -/
theorem alternatingSixAmbientRow18TransformedGeneratorA_fromIntermediate_row0
    (j : Fin 8) :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        0 j =
      alternatingSixAmbientRow18TransformedGeneratorA
        0 j := by
  fin_cases j
  · exact row18_transformedGeneratorA_0_0
  · exact row18_transformedGeneratorA_0_1
  · exact row18_transformedGeneratorA_0_2
  · exact row18_transformedGeneratorA_0_3
  · exact row18_transformedGeneratorA_0_4
  · exact row18_transformedGeneratorA_0_5
  · exact row18_transformedGeneratorA_0_6
  · exact row18_transformedGeneratorA_0_7


end InductiveMcKay
end McKayConjecture
