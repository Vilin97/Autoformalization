/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18TransformedDataRow4

/-!
# Transformed-generator data for ambient row 18, output row 5

This generated module checks the scalar products in output row 5.
It imports the preceding output-row module to serialize clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private theorem row18_transformedGeneratorA_term_5_0_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 0 =
      (((351 / 1580) : ℂ) + ((523 / 3476) : ℂ) * ζ ^ 1 + ((1233 / 8690) : ℂ) * ζ ^ 2 - ((17 / 158) : ℂ) * ζ ^ 3 - ((197 / 3476) : ℂ) * ζ ^ 5 - ((241 / 17380) : ℂ) * ζ ^ 6 - ((169 / 790) : ℂ) * ζ ^ 8 - ((547 / 3476) : ℂ) * ζ ^ 9 + ((31 / 316) : ℂ) * ζ ^ 11 - ((167 / 790) : ℂ) * ζ ^ 12 - ((523 / 3476) : ℂ) * ζ ^ 13 + ((71 / 316) : ℂ) * ζ ^ 15 - ((523 / 3476) : ℂ) * ζ ^ 17 - ((2503 / 17380) : ℂ) * ζ ^ 18 - ((6 / 869) : ℂ) * ζ ^ 21 - ((1233 / 8690) : ℂ) * ζ ^ 22 + ((357 / 1580) : ℂ) * ζ ^ 24 + ((180 / 869) : ℂ) * ζ ^ 25 - ((16 / 79) : ℂ) * ζ ^ 27 + ((169 / 790) : ℂ) * ζ ^ 28 + ((523 / 3476) : ℂ) * ζ ^ 29 + ((93 / 4345) : ℂ) * ζ ^ 30 - ((31 / 316) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((721 / 3476) : ℂ) - ((2311 / 17380) : ℂ) * ζ ^ 1 - ((161 / 869) : ℂ) * ζ ^ 2 + ((1161 / 8690) : ℂ) * ζ ^ 3 + ((183 / 1580) : ℂ) * ζ ^ 4 + ((888 / 4345) : ℂ) * ζ ^ 5 + ((617 / 4345) : ℂ) * ζ ^ 6 - ((9 / 220) : ℂ) * ζ ^ 7 + ((243 / 3476) : ℂ) * ζ ^ 8 - ((379 / 17380) : ℂ) * ζ ^ 9 - ((322 / 4345) : ℂ) * ζ ^ 10 - ((214 / 4345) : ℂ) * ζ ^ 11 + ((629 / 8690) : ℂ) * ζ ^ 12 + ((661 / 8690) : ℂ) * ζ ^ 13 - ((78 / 4345) : ℂ) * ζ ^ 14 - ((129 / 4345) : ℂ) * ζ ^ 15 - ((369 / 4345) : ℂ) * ζ ^ 16 + ((1093 / 8690) : ℂ) * ζ ^ 17 + ((927 / 17380) : ℂ) * ζ ^ 18 - ((417 / 17380) : ℂ) * ζ ^ 19 + ((141 / 3476) : ℂ) * ζ ^ 20 - ((1147 / 8690) : ℂ) * ζ ^ 21 + ((1031 / 17380) : ℂ) * ζ ^ 22 - ((1773 / 17380) : ℂ) * ζ ^ 23 - ((59 / 1738) : ℂ) * ζ ^ 24 - ((487 / 17380) : ℂ) * ζ ^ 25 + ((11 / 316) : ℂ) * ζ ^ 26 + ((1351 / 17380) : ℂ) * ζ ^ 27 - ((333 / 3476) : ℂ) * ζ ^ 28 + ((619 / 17380) : ℂ) * ζ ^ 29 + ((123 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_0_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 0 =
      (-((5939 / 17380) : ℂ) + ((719 / 17380) : ℂ) * ζ ^ 1 + ((807 / 4345) : ℂ) * ζ ^ 2 + ((1313 / 17380) : ℂ) * ζ ^ 3 + ((4947 / 17380) : ℂ) * ζ ^ 5 + ((6377 / 17380) : ℂ) * ζ ^ 6 + ((757 / 17380) : ℂ) * ζ ^ 8 + ((551 / 8690) : ℂ) * ζ ^ 9 - ((5409 / 17380) : ℂ) * ζ ^ 11 - ((1679 / 17380) : ℂ) * ζ ^ 12 - ((719 / 17380) : ℂ) * ζ ^ 13 + ((569 / 8690) : ℂ) * ζ ^ 15 - ((719 / 17380) : ℂ) * ζ ^ 17 - ((827 / 8690) : ℂ) * ζ ^ 18 - ((4273 / 17380) : ℂ) * ζ ^ 21 - ((807 / 4345) : ℂ) * ζ ^ 22 - ((953 / 17380) : ℂ) * ζ ^ 24 - ((1057 / 4345) : ℂ) * ζ ^ 25 + ((4361 / 17380) : ℂ) * ζ ^ 27 - ((757 / 17380) : ℂ) * ζ ^ 28 + ((719 / 17380) : ℂ) * ζ ^ 29 + ((3141 / 17380) : ℂ) * ζ ^ 30 + ((5409 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((5783 / 17380) : ℂ) - ((347 / 17380) : ℂ) * ζ ^ 1 - ((2477 / 17380) : ℂ) * ζ ^ 2 - ((94 / 4345) : ℂ) * ζ ^ 3 - ((5133 / 17380) : ℂ) * ζ ^ 4 - ((3051 / 17380) : ℂ) * ζ ^ 5 - ((151 / 790) : ℂ) * ζ ^ 6 - ((1737 / 17380) : ℂ) * ζ ^ 7 + ((1303 / 17380) : ℂ) * ζ ^ 8 + ((227 / 4345) : ℂ) * ζ ^ 9 + ((392 / 4345) : ℂ) * ζ ^ 10 + ((551 / 4345) : ℂ) * ζ ^ 11 + ((378 / 4345) : ℂ) * ζ ^ 12 + ((119 / 8690) : ℂ) * ζ ^ 13 - ((3207 / 17380) : ℂ) * ζ ^ 14 - ((3667 / 17380) : ℂ) * ζ ^ 15 + ((33 / 1580) : ℂ) * ζ ^ 16 - ((1481 / 17380) : ℂ) * ζ ^ 17 + ((229 / 8690) : ℂ) * ζ ^ 18 + ((342 / 4345) : ℂ) * ζ ^ 19 + ((200 / 869) : ℂ) * ζ ^ 20 + ((175 / 1738) : ℂ) * ζ ^ 21 + ((255 / 3476) : ℂ) * ζ ^ 22 + ((2019 / 17380) : ℂ) * ζ ^ 23 + ((1039 / 17380) : ℂ) * ζ ^ 24 - ((573 / 17380) : ℂ) * ζ ^ 25 - ((1381 / 17380) : ℂ) * ζ ^ 26 - ((589 / 17380) : ℂ) * ζ ^ 27 - ((186 / 4345) : ℂ) * ζ ^ 28 - ((252 / 4345) : ℂ) * ζ ^ 29 - ((159 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_0_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 0 =
      (-((1313 / 17380) : ℂ) - ((5623 / 17380) : ℂ) * ζ ^ 1 - ((2351 / 8690) : ℂ) * ζ ^ 2 - ((1061 / 8690) : ℂ) * ζ ^ 3 - ((497 / 8690) : ℂ) * ζ ^ 5 - ((552 / 4345) : ℂ) * ζ ^ 6 + ((5409 / 17380) : ℂ) * ζ ^ 8 + ((1944 / 4345) : ℂ) * ζ ^ 9 - ((886 / 4345) : ℂ) * ζ ^ 11 + ((3207 / 17380) : ℂ) * ζ ^ 12 + ((5623 / 17380) : ℂ) * ζ ^ 13 - ((5287 / 17380) : ℂ) * ζ ^ 15 + ((5623 / 17380) : ℂ) * ζ ^ 17 + ((1244 / 4345) : ℂ) * ζ ^ 18 + ((574 / 4345) : ℂ) * ζ ^ 21 + ((2351 / 8690) : ℂ) * ζ ^ 22 - ((4361 / 17380) : ℂ) * ζ ^ 24 - ((4629 / 17380) : ℂ) * ζ ^ 25 - ((1019 / 17380) : ℂ) * ζ ^ 27 - ((5409 / 17380) : ℂ) * ζ ^ 28 - ((5623 / 17380) : ℂ) * ζ ^ 29 - ((707 / 8690) : ℂ) * ζ ^ 30 + ((886 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((1313 / 17380) : ℂ) + ((1348 / 4345) : ℂ) * ζ ^ 1 + ((4603 / 17380) : ℂ) * ζ ^ 2 + ((4069 / 17380) : ℂ) * ζ ^ 3 - ((1 / 110) : ℂ) * ζ ^ 4 - ((81 / 395) : ℂ) * ζ ^ 5 - ((889 / 4345) : ℂ) * ζ ^ 6 - ((661 / 17380) : ℂ) * ζ ^ 7 - ((287 / 1738) : ℂ) * ζ ^ 8 - ((355 / 1738) : ℂ) * ζ ^ 9 - ((1453 / 17380) : ℂ) * ζ ^ 10 + ((1379 / 17380) : ℂ) * ζ ^ 11 + ((2401 / 17380) : ℂ) * ζ ^ 12 + ((707 / 4345) : ℂ) * ζ ^ 13 + ((1281 / 8690) : ℂ) * ζ ^ 14 + ((1453 / 17380) : ℂ) * ζ ^ 15 + ((147 / 1738) : ℂ) * ζ ^ 16 - ((733 / 3476) : ℂ) * ζ ^ 17 - ((3629 / 17380) : ℂ) * ζ ^ 18 - ((3227 / 17380) : ℂ) * ζ ^ 19 - ((1021 / 17380) : ℂ) * ζ ^ 20 - ((149 / 17380) : ℂ) * ζ ^ 21 + ((1037 / 17380) : ℂ) * ζ ^ 22 + ((1901 / 17380) : ℂ) * ζ ^ 23 + ((819 / 8690) : ℂ) * ζ ^ 24 + ((1263 / 17380) : ℂ) * ζ ^ 25 - ((107 / 8690) : ℂ) * ζ ^ 26 - ((39 / 1738) : ℂ) * ζ ^ 27 - ((261 / 8690) : ℂ) * ζ ^ 28 - ((48 / 4345) : ℂ) * ζ ^ 29 - ((27 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_0_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 0 =
      (((91 / 395) : ℂ) + ((421 / 1580) : ℂ) * ζ ^ 1 + ((51 / 395) : ℂ) * ζ ^ 2 + ((56 / 395) : ℂ) * ζ ^ 3 - ((48 / 395) : ℂ) * ζ ^ 5 - ((46 / 395) : ℂ) * ζ ^ 6 - ((151 / 790) : ℂ) * ζ ^ 8 - ((251 / 790) : ℂ) * ζ ^ 9 + ((97 / 395) : ℂ) * ζ ^ 11 + ((139 / 1580) : ℂ) * ζ ^ 12 - ((421 / 1580) : ℂ) * ζ ^ 13 - ((53 / 790) : ℂ) * ζ ^ 15 - ((421 / 1580) : ℂ) * ζ ^ 17 - ((247 / 1580) : ℂ) * ζ ^ 18 - ((67 / 1580) : ℂ) * ζ ^ 21 - ((51 / 395) : ℂ) * ζ ^ 22 + ((353 / 1580) : ℂ) * ζ ^ 24 + ((613 / 1580) : ℂ) * ζ ^ 25 - ((47 / 1580) : ℂ) * ζ ^ 27 + ((151 / 790) : ℂ) * ζ ^ 28 + ((421 / 1580) : ℂ) * ζ ^ 29 - ((17 / 1580) : ℂ) * ζ ^ 30 - ((97 / 395) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((63 / 395) : ℂ) - ((391 / 1580) : ℂ) * ζ ^ 1 - ((81 / 1580) : ℂ) * ζ ^ 2 - ((261 / 1580) : ℂ) * ζ ^ 3 + ((43 / 395) : ℂ) * ζ ^ 4 + ((31 / 158) : ℂ) * ζ ^ 5 + ((74 / 395) : ℂ) * ζ ^ 6 + ((113 / 1580) : ℂ) * ζ ^ 7 - ((3 / 158) : ℂ) * ζ ^ 8 - ((1 / 1580) : ℂ) * ζ ^ 9 - ((183 / 1580) : ℂ) * ζ ^ 10 - ((125 / 316) : ℂ) * ζ ^ 11 - ((259 / 1580) : ℂ) * ζ ^ 12 + ((41 / 395) : ℂ) * ζ ^ 13 + ((59 / 395) : ℂ) * ζ ^ 14 + ((133 / 790) : ℂ) * ζ ^ 15 + ((321 / 1580) : ℂ) * ζ ^ 16 + ((81 / 316) : ℂ) * ζ ^ 17 + ((19 / 395) : ℂ) * ζ ^ 18 - ((293 / 1580) : ℂ) * ζ ^ 19 - ((159 / 1580) : ℂ) * ζ ^ 20 + ((23 / 1580) : ℂ) * ζ ^ 21 - ((113 / 1580) : ℂ) * ζ ^ 22 - ((3 / 316) : ℂ) * ζ ^ 23 + ((21 / 395) : ℂ) * ζ ^ 24 + ((48 / 395) : ℂ) * ζ ^ 25 + ((63 / 790) : ℂ) * ζ ^ 26 - ((89 / 1580) : ℂ) * ζ ^ 27 - ((23 / 316) : ℂ) * ζ ^ 28 - ((7 / 79) : ℂ) * ζ ^ 29 - ((33 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_0_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 0 =
      (-((133 / 17380) : ℂ) + ((1603 / 17380) : ℂ) * ζ ^ 1 - ((1461 / 17380) : ℂ) * ζ ^ 2 + ((201 / 3476) : ℂ) * ζ ^ 3 + ((356 / 4345) : ℂ) * ζ ^ 5 + ((1761 / 17380) : ℂ) * ζ ^ 6 - ((544 / 4345) : ℂ) * ζ ^ 8 - ((9 / 220) : ℂ) * ζ ^ 9 - ((105 / 3476) : ℂ) * ζ ^ 11 - ((12 / 4345) : ℂ) * ζ ^ 12 - ((1603 / 17380) : ℂ) * ζ ^ 13 + ((177 / 3476) : ℂ) * ζ ^ 15 - ((1603 / 17380) : ℂ) * ζ ^ 17 + ((532 / 4345) : ℂ) * ζ ^ 18 - ((514 / 4345) : ℂ) * ζ ^ 21 + ((1461 / 17380) : ℂ) * ζ ^ 22 - ((233 / 8690) : ℂ) * ζ ^ 24 + ((179 / 17380) : ℂ) * ζ ^ 25 - ((115 / 1738) : ℂ) * ζ ^ 27 + ((544 / 4345) : ℂ) * ζ ^ 28 + ((1603 / 17380) : ℂ) * ζ ^ 29 - ((1927 / 17380) : ℂ) * ζ ^ 30 + ((105 / 3476) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((31 / 4345) : ℂ) - ((663 / 8690) : ℂ) * ζ ^ 1 + ((1161 / 8690) : ℂ) * ζ ^ 2 - ((39 / 869) : ℂ) * ζ ^ 3 - ((346 / 4345) : ℂ) * ζ ^ 4 - ((217 / 4345) : ℂ) * ζ ^ 5 - ((479 / 3476) : ℂ) * ζ ^ 6 + ((1019 / 8690) : ℂ) * ζ ^ 7 + ((599 / 4345) : ℂ) * ζ ^ 8 + ((523 / 17380) : ℂ) * ζ ^ 9 + ((2899 / 17380) : ℂ) * ζ ^ 10 - ((923 / 8690) : ℂ) * ζ ^ 11 + ((1 / 110) : ℂ) * ζ ^ 12 - ((101 / 17380) : ℂ) * ζ ^ 13 - ((614 / 4345) : ℂ) * ζ ^ 14 - ((288 / 4345) : ℂ) * ζ ^ 15 - ((677 / 17380) : ℂ) * ζ ^ 16 - ((699 / 17380) : ℂ) * ζ ^ 17 - ((104 / 4345) : ℂ) * ζ ^ 18 + ((879 / 8690) : ℂ) * ζ ^ 19 + ((65 / 1738) : ℂ) * ζ ^ 20 + ((961 / 17380) : ℂ) * ζ ^ 21 + ((2111 / 17380) : ℂ) * ζ ^ 22 - ((279 / 3476) : ℂ) * ζ ^ 23 + ((163 / 8690) : ℂ) * ζ ^ 24 + ((119 / 17380) : ℂ) * ζ ^ 25 - ((1369 / 17380) : ℂ) * ζ ^ 26 + ((357 / 8690) : ℂ) * ζ ^ 27 - ((379 / 8690) : ℂ) * ζ ^ 28 - ((27 / 8690) : ℂ) * ζ ^ 29 + ((119 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_0_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 0 =
      (-((1 / 11) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 1 - ((7 / 44) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 3 + ((3 / 44) : ℂ) * ζ ^ 5 - ((9 / 44) : ℂ) * ζ ^ 6 + ((2 / 11) : ℂ) * ζ ^ 8 + ((9 / 44) : ℂ) * ζ ^ 9 - ((7 / 44) : ℂ) * ζ ^ 11 + ((3 / 22) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 13 + ((3 / 44) : ℂ) * ζ ^ 15 + ((1 / 11) : ℂ) * ζ ^ 17 - ((1 / 44) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 21 + ((7 / 44) : ℂ) * ζ ^ 22 - ((5 / 44) : ℂ) * ζ ^ 24 - ((7 / 44) : ℂ) * ζ ^ 25 + ((3 / 44) : ℂ) * ζ ^ 27 - ((2 / 11) : ℂ) * ζ ^ 28 - ((1 / 11) : ℂ) * ζ ^ 29 - ((1 / 11) : ℂ) * ζ ^ 30 + ((7 / 44) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_0_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 0 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_0_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 0 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_5_0 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        5 0 =
      alternatingSixAmbientRow18TransformedGeneratorA
        5 0 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_5_0_0,
      row18_transformedGeneratorA_term_5_0_1,
      row18_transformedGeneratorA_term_5_0_2,
      row18_transformedGeneratorA_term_5_0_3,
      row18_transformedGeneratorA_term_5_0_4,
      row18_transformedGeneratorA_term_5_0_5,
      row18_transformedGeneratorA_term_5_0_6,
      row18_transformedGeneratorA_term_5_0_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_1_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 1 =
      (-((247 / 17380) : ℂ) - ((4501 / 17380) : ℂ) * ζ ^ 1 - ((63 / 316) : ℂ) * ζ ^ 2 - ((1022 / 4345) : ℂ) * ζ ^ 3 - ((3403 / 17380) : ℂ) * ζ ^ 5 - ((29 / 316) : ℂ) * ζ ^ 6 + ((4311 / 17380) : ℂ) * ζ ^ 8 + ((613 / 4345) : ℂ) * ζ ^ 9 + ((399 / 17380) : ℂ) * ζ ^ 11 - ((1197 / 17380) : ℂ) * ζ ^ 12 + ((4501 / 17380) : ℂ) * ζ ^ 13 + ((1691 / 8690) : ℂ) * ζ ^ 15 + ((4501 / 17380) : ℂ) * ζ ^ 17 + ((3 / 79) : ℂ) * ζ ^ 18 + ((2061 / 8690) : ℂ) * ζ ^ 21 + ((63 / 316) : ℂ) * ζ ^ 22 - ((999 / 17380) : ℂ) * ζ ^ 24 - ((549 / 8690) : ℂ) * ζ ^ 25 - ((5231 / 17380) : ℂ) * ζ ^ 27 - ((4311 / 17380) : ℂ) * ζ ^ 28 - ((4501 / 17380) : ℂ) * ζ ^ 29 - ((19 / 316) : ℂ) * ζ ^ 30 - ((399 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((391 / 17380) : ℂ) + ((4907 / 17380) : ℂ) * ζ ^ 1 + ((3281 / 17380) : ℂ) * ζ ^ 2 + ((798 / 4345) : ℂ) * ζ ^ 3 - ((1231 / 17380) : ℂ) * ζ ^ 4 - ((117 / 3476) : ℂ) * ζ ^ 5 - ((201 / 3476) : ℂ) * ζ ^ 6 - ((1129 / 4345) : ℂ) * ζ ^ 7 - ((57 / 395) : ℂ) * ζ ^ 8 - ((159 / 1580) : ℂ) * ζ ^ 9 + ((3139 / 17380) : ℂ) * ζ ^ 10 + ((3129 / 17380) : ℂ) * ζ ^ 11 + ((1731 / 4345) : ℂ) * ζ ^ 12 + ((513 / 8690) : ℂ) * ζ ^ 13 - ((35 / 869) : ℂ) * ζ ^ 14 - ((1841 / 17380) : ℂ) * ζ ^ 15 - ((1149 / 3476) : ℂ) * ζ ^ 16 - ((2687 / 17380) : ℂ) * ζ ^ 17 - ((49 / 790) : ℂ) * ζ ^ 18 + ((3709 / 17380) : ℂ) * ζ ^ 19 + ((3767 / 17380) : ℂ) * ζ ^ 20 - ((53 / 3476) : ℂ) * ζ ^ 21 - ((323 / 8690) : ℂ) * ζ ^ 22 - ((933 / 8690) : ℂ) * ζ ^ 23 + ((39 / 3476) : ℂ) * ζ ^ 24 - ((14 / 869) : ℂ) * ζ ^ 25 + ((599 / 17380) : ℂ) * ζ ^ 26 + ((7 / 158) : ℂ) * ζ ^ 27 - ((417 / 4345) : ℂ) * ζ ^ 28 + ((109 / 3476) : ℂ) * ζ ^ 29 + ((111 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_1_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 1 =
      (((41 / 17380) : ℂ) - ((28 / 395) : ℂ) * ζ ^ 1 + ((29 / 1580) : ℂ) * ζ ^ 2 + ((6373 / 17380) : ℂ) * ζ ^ 3 - ((161 / 1580) : ℂ) * ζ ^ 5 - ((489 / 1580) : ℂ) * ζ ^ 6 - ((752 / 4345) : ℂ) * ζ ^ 8 + ((17 / 790) : ℂ) * ζ ^ 9 + ((2951 / 17380) : ℂ) * ζ ^ 11 + ((863 / 8690) : ℂ) * ζ ^ 12 + ((28 / 395) : ℂ) * ζ ^ 13 - ((183 / 4345) : ℂ) * ζ ^ 15 + ((28 / 395) : ℂ) * ζ ^ 17 - ((311 / 790) : ℂ) * ζ ^ 18 + ((297 / 790) : ℂ) * ζ ^ 21 - ((29 / 1580) : ℂ) * ζ ^ 22 + ((621 / 8690) : ℂ) * ζ ^ 24 + ((49 / 1580) : ℂ) * ζ ^ 25 - ((1367 / 8690) : ℂ) * ζ ^ 27 + ((752 / 4345) : ℂ) * ζ ^ 28 - ((28 / 395) : ℂ) * ζ ^ 29 + ((13 / 1580) : ℂ) * ζ ^ 30 - ((2951 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((53 / 8690) : ℂ) + ((153 / 1738) : ℂ) * ζ ^ 1 - ((2 / 55) : ℂ) * ζ ^ 2 - ((1691 / 4345) : ℂ) * ζ ^ 3 + ((2731 / 17380) : ℂ) * ζ ^ 4 + ((6141 / 17380) : ℂ) * ζ ^ 5 + ((10731 / 17380) : ℂ) * ζ ^ 6 + ((1614 / 4345) : ℂ) * ζ ^ 7 + ((58 / 4345) : ℂ) * ζ ^ 8 - ((4413 / 8690) : ℂ) * ζ ^ 9 - ((1715 / 3476) : ℂ) * ζ ^ 10 - ((234 / 869) : ℂ) * ζ ^ 11 + ((723 / 17380) : ℂ) * ζ ^ 12 + ((666 / 4345) : ℂ) * ζ ^ 13 + ((95 / 1738) : ℂ) * ζ ^ 14 - ((17 / 1738) : ℂ) * ζ ^ 15 - ((351 / 3476) : ℂ) * ζ ^ 16 - ((1347 / 17380) : ℂ) * ζ ^ 17 + ((361 / 790) : ℂ) * ζ ^ 18 + ((1 / 20) : ℂ) * ζ ^ 19 - ((187 / 1580) : ℂ) * ζ ^ 20 - ((9671 / 17380) : ℂ) * ζ ^ 21 - ((303 / 1738) : ℂ) * ζ ^ 22 - ((161 / 790) : ℂ) * ζ ^ 23 + ((529 / 8690) : ℂ) * ζ ^ 24 + ((769 / 17380) : ℂ) * ζ ^ 25 + ((5427 / 17380) : ℂ) * ζ ^ 26 - ((643 / 17380) : ℂ) * ζ ^ 27 + ((137 / 1738) : ℂ) * ζ ^ 28 + ((351 / 3476) : ℂ) * ζ ^ 29 + ((954 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_1_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 1 =
      (-((2423 / 17380) : ℂ) + ((91 / 1738) : ℂ) * ζ ^ 1 + ((2751 / 17380) : ℂ) * ζ ^ 2 + ((1037 / 17380) : ℂ) * ζ ^ 3 + ((1123 / 3476) : ℂ) * ζ ^ 5 + ((3339 / 17380) : ℂ) * ζ ^ 6 - ((3253 / 8690) : ℂ) * ζ ^ 8 + ((42 / 869) : ℂ) * ζ ^ 9 - ((139 / 4345) : ℂ) * ζ ^ 11 - ((5193 / 17380) : ℂ) * ζ ^ 12 - ((91 / 1738) : ℂ) * ζ ^ 13 + ((663 / 4345) : ℂ) * ζ ^ 15 - ((91 / 1738) : ℂ) * ζ ^ 17 + ((1097 / 17380) : ℂ) * ζ ^ 18 - ((1465 / 3476) : ℂ) * ζ ^ 21 - ((2751 / 17380) : ℂ) * ζ ^ 22 + ((5499 / 17380) : ℂ) * ζ ^ 24 - ((941 / 3476) : ℂ) * ζ ^ 25 + ((1519 / 17380) : ℂ) * ζ ^ 27 + ((3253 / 8690) : ℂ) * ζ ^ 28 + ((91 / 1738) : ℂ) * ζ ^ 29 + ((8 / 4345) : ℂ) * ζ ^ 30 + ((139 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((2073 / 17380) : ℂ) - ((149 / 3476) : ℂ) * ζ ^ 1 + ((59 / 1580) : ℂ) * ζ ^ 2 - ((479 / 3476) : ℂ) * ζ ^ 3 - ((1183 / 4345) : ℂ) * ζ ^ 4 - ((1024 / 4345) : ℂ) * ζ ^ 5 - ((267 / 8690) : ℂ) * ζ ^ 6 + ((476 / 4345) : ℂ) * ζ ^ 7 + ((1391 / 8690) : ℂ) * ζ ^ 8 + ((2911 / 17380) : ℂ) * ζ ^ 9 - ((1003 / 17380) : ℂ) * ζ ^ 10 + ((728 / 4345) : ℂ) * ζ ^ 11 - ((493 / 8690) : ℂ) * ζ ^ 12 + ((442 / 4345) : ℂ) * ζ ^ 13 - ((683 / 17380) : ℂ) * ζ ^ 14 - ((93 / 1580) : ℂ) * ζ ^ 15 - ((288 / 4345) : ℂ) * ζ ^ 16 - ((527 / 4345) : ℂ) * ζ ^ 17 - ((141 / 1738) : ℂ) * ζ ^ 18 - ((327 / 3476) : ℂ) * ζ ^ 19 + ((1739 / 17380) : ℂ) * ζ ^ 20 + ((2867 / 8690) : ℂ) * ζ ^ 21 + ((432 / 4345) : ℂ) * ζ ^ 22 + ((117 / 4345) : ℂ) * ζ ^ 23 + ((33 / 1580) : ℂ) * ζ ^ 24 - ((53 / 1580) : ℂ) * ζ ^ 25 - ((2437 / 17380) : ℂ) * ζ ^ 26 - ((2371 / 17380) : ℂ) * ζ ^ 27 - ((27 / 790) : ℂ) * ζ ^ 28 + ((199 / 8690) : ℂ) * ζ ^ 29 + ((153 / 1738) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_1_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 1 =
      (((373 / 1580) : ℂ) + ((173 / 1580) : ℂ) * ζ ^ 1 + ((19 / 1580) : ℂ) * ζ ^ 2 - ((451 / 1580) : ℂ) * ζ ^ 3 - ((69 / 395) : ℂ) * ζ ^ 5 + ((63 / 790) : ℂ) * ζ ^ 6 + ((453 / 790) : ℂ) * ζ ^ 8 - ((1 / 1580) : ℂ) * ζ ^ 9 - ((707 / 1580) : ℂ) * ζ ^ 11 + ((99 / 790) : ℂ) * ζ ^ 12 - ((173 / 1580) : ℂ) * ζ ^ 13 - ((481 / 1580) : ℂ) * ζ ^ 15 - ((173 / 1580) : ℂ) * ζ ^ 17 + ((633 / 1580) : ℂ) * ζ ^ 18 - ((153 / 790) : ℂ) * ζ ^ 21 - ((19 / 1580) : ℂ) * ζ ^ 22 - ((96 / 395) : ℂ) * ζ ^ 24 + ((449 / 1580) : ℂ) * ζ ^ 25 + ((309 / 790) : ℂ) * ζ ^ 27 - ((453 / 790) : ℂ) * ζ ^ 28 + ((173 / 1580) : ℂ) * ζ ^ 29 - ((267 / 1580) : ℂ) * ζ ^ 30 + ((707 / 1580) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((99 / 316) : ℂ) - ((66 / 395) : ℂ) * ζ ^ 1 - ((153 / 1580) : ℂ) * ζ ^ 2 + ((377 / 1580) : ℂ) * ζ ^ 3 + ((144 / 395) : ℂ) * ζ ^ 4 + ((157 / 395) : ℂ) * ζ ^ 5 + ((22 / 395) : ℂ) * ζ ^ 6 - ((477 / 1580) : ℂ) * ζ ^ 7 - ((185 / 316) : ℂ) * ζ ^ 8 - ((37 / 158) : ℂ) * ζ ^ 9 + ((111 / 790) : ℂ) * ζ ^ 10 + ((871 / 1580) : ℂ) * ζ ^ 11 + ((339 / 1580) : ℂ) * ζ ^ 12 - ((111 / 1580) : ℂ) * ζ ^ 13 + ((17 / 790) : ℂ) * ζ ^ 14 + ((61 / 1580) : ℂ) * ζ ^ 15 + ((1 / 790) : ℂ) * ζ ^ 16 - ((41 / 395) : ℂ) * ζ ^ 17 - ((61 / 790) : ℂ) * ζ ^ 18 - ((91 / 395) : ℂ) * ζ ^ 19 - ((25 / 79) : ℂ) * ζ ^ 20 - ((173 / 790) : ℂ) * ζ ^ 21 + ((663 / 1580) : ℂ) * ζ ^ 22 + ((699 / 1580) : ℂ) * ζ ^ 23 + ((93 / 790) : ℂ) * ζ ^ 24 - ((101 / 395) : ℂ) * ζ ^ 25 - ((611 / 1580) : ℂ) * ζ ^ 26 - ((173 / 1580) : ℂ) * ζ ^ 27 + ((19 / 395) : ℂ) * ζ ^ 28 + ((189 / 1580) : ℂ) * ζ ^ 29 + ((261 / 1580) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_1_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 1 =
      (((47 / 869) : ℂ) + ((47 / 17380) : ℂ) * ζ ^ 1 - ((309 / 1738) : ℂ) * ζ ^ 2 - ((523 / 1580) : ℂ) * ζ ^ 3 - ((437 / 8690) : ℂ) * ζ ^ 5 - ((168 / 869) : ℂ) * ζ ^ 6 - ((1 / 44) : ℂ) * ζ ^ 8 - ((606 / 4345) : ℂ) * ζ ^ 9 + ((327 / 790) : ℂ) * ζ ^ 11 + ((277 / 1738) : ℂ) * ζ ^ 12 - ((47 / 17380) : ℂ) * ζ ^ 13 + ((201 / 790) : ℂ) * ζ ^ 15 - ((47 / 17380) : ℂ) * ζ ^ 17 + ((62 / 869) : ℂ) * ζ ^ 18 + ((459 / 4345) : ℂ) * ζ ^ 21 + ((309 / 1738) : ℂ) * ζ ^ 22 + ((741 / 3476) : ℂ) * ζ ^ 24 + ((921 / 17380) : ℂ) * ζ ^ 25 - ((383 / 790) : ℂ) * ζ ^ 27 + ((1 / 44) : ℂ) * ζ ^ 28 + ((47 / 17380) : ℂ) * ζ ^ 29 - ((65 / 1738) : ℂ) * ζ ^ 30 - ((327 / 790) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((967 / 17380) : ℂ) + ((817 / 17380) : ℂ) * ζ ^ 1 + ((4571 / 17380) : ℂ) * ζ ^ 2 + ((273 / 790) : ℂ) * ζ ^ 3 + ((2159 / 17380) : ℂ) * ζ ^ 4 - ((469 / 8690) : ℂ) * ζ ^ 5 + ((31 / 869) : ℂ) * ζ ^ 6 - ((159 / 1580) : ℂ) * ζ ^ 7 + ((2009 / 17380) : ℂ) * ζ ^ 8 + ((389 / 17380) : ℂ) * ζ ^ 9 - ((659 / 8690) : ℂ) * ζ ^ 10 - ((273 / 869) : ℂ) * ζ ^ 11 - ((1479 / 8690) : ℂ) * ζ ^ 12 - ((527 / 8690) : ℂ) * ζ ^ 13 + ((3089 / 17380) : ℂ) * ζ ^ 14 + ((1979 / 17380) : ℂ) * ζ ^ 15 + ((339 / 4345) : ℂ) * ζ ^ 16 + ((472 / 4345) : ℂ) * ζ ^ 17 + ((258 / 4345) : ℂ) * ζ ^ 18 + ((291 / 4345) : ℂ) * ζ ^ 19 - ((159 / 4345) : ℂ) * ζ ^ 20 - ((159 / 1580) : ℂ) * ζ ^ 21 - ((1701 / 8690) : ℂ) * ζ ^ 22 - ((89 / 316) : ℂ) * ζ ^ 23 - ((449 / 1738) : ℂ) * ζ ^ 24 - ((37 / 869) : ℂ) * ζ ^ 25 + ((942 / 4345) : ℂ) * ζ ^ 26 + ((2451 / 8690) : ℂ) * ζ ^ 27 + ((832 / 4345) : ℂ) * ζ ^ 28 - ((26 / 4345) : ℂ) * ζ ^ 29 - ((442 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_1_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 1 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_1_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 1 =
      (((41 / 220) : ℂ) + ((7 / 55) : ℂ) * ζ ^ 1 + ((27 / 220) : ℂ) * ζ ^ 2 + ((19 / 220) : ℂ) * ζ ^ 3 + ((17 / 110) : ℂ) * ζ ^ 5 + ((63 / 220) : ℂ) * ζ ^ 6 - ((19 / 110) : ℂ) * ζ ^ 8 + ((7 / 110) : ℂ) * ζ ^ 9 - ((27 / 220) : ℂ) * ζ ^ 11 - ((89 / 220) : ℂ) * ζ ^ 12 - ((7 / 55) : ℂ) * ζ ^ 13 - ((1 / 220) : ℂ) * ζ ^ 15 - ((7 / 55) : ℂ) * ζ ^ 17 - ((13 / 110) : ℂ) * ζ ^ 18 - ((23 / 110) : ℂ) * ζ ^ 21 - ((27 / 220) : ℂ) * ζ ^ 22 + ((8 / 55) : ℂ) * ζ ^ 24 - ((3 / 110) : ℂ) * ζ ^ 25 + ((43 / 220) : ℂ) * ζ ^ 27 + ((19 / 110) : ℂ) * ζ ^ 28 + ((7 / 55) : ℂ) * ζ ^ 29 + ((39 / 220) : ℂ) * ζ ^ 30 + ((27 / 220) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((41 / 220) : ℂ) + ((7 / 110) : ℂ) * ζ ^ 1 - ((51 / 220) : ℂ) * ζ ^ 2 - ((61 / 220) : ℂ) * ζ ^ 3 - ((12 / 55) : ℂ) * ζ ^ 4 - ((3 / 110) : ℂ) * ζ ^ 5 - ((73 / 220) : ℂ) * ζ ^ 6 - ((6 / 55) : ℂ) * ζ ^ 7 - ((3 / 220) : ℂ) * ζ ^ 8 - ((1 / 55) : ℂ) * ζ ^ 9 + ((6 / 55) : ℂ) * ζ ^ 10 + ((2 / 55) : ℂ) * ζ ^ 11 + ((27 / 55) : ℂ) * ζ ^ 12 - ((39 / 220) : ℂ) * ζ ^ 14 - ((13 / 110) : ℂ) * ζ ^ 15 - ((7 / 110) : ℂ) * ζ ^ 17 + ((5 / 22) : ℂ) * ζ ^ 18 + ((21 / 110) : ℂ) * ζ ^ 19 + ((12 / 55) : ℂ) * ζ ^ 20 + ((9 / 110) : ℂ) * ζ ^ 21 + ((37 / 220) : ℂ) * ζ ^ 22 + ((6 / 55) : ℂ) * ζ ^ 23 + ((9 / 220) : ℂ) * ζ ^ 24 - ((1 / 55) : ℂ) * ζ ^ 25 - ((6 / 55) : ℂ) * ζ ^ 26 - ((6 / 55) : ℂ) * ζ ^ 27 - ((57 / 220) : ℂ) * ζ ^ 28)

private theorem row18_transformedGeneratorA_term_5_1_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 1 =
      (-((27 / 220) : ℂ) - ((4 / 55) : ℂ) * ζ ^ 1 - ((7 / 55) : ℂ) * ζ ^ 2 + ((7 / 110) : ℂ) * ζ ^ 3 + ((3 / 55) : ℂ) * ζ ^ 5 + ((2 / 55) : ℂ) * ζ ^ 6 - ((17 / 110) : ℂ) * ζ ^ 8 - ((2 / 55) : ℂ) * ζ ^ 9 + ((19 / 110) : ℂ) * ζ ^ 11 + ((13 / 220) : ℂ) * ζ ^ 12 + ((4 / 55) : ℂ) * ζ ^ 13 - ((21 / 220) : ℂ) * ζ ^ 15 + ((4 / 55) : ℂ) * ζ ^ 17 + ((29 / 220) : ℂ) * ζ ^ 18 - ((13 / 220) : ℂ) * ζ ^ 21 + ((7 / 55) : ℂ) * ζ ^ 22 - ((9 / 220) : ℂ) * ζ ^ 24 - ((7 / 55) : ℂ) * ζ ^ 25 + ((23 / 220) : ℂ) * ζ ^ 27 + ((17 / 110) : ℂ) * ζ ^ 28 - ((4 / 55) : ℂ) * ζ ^ 29 - ((4 / 55) : ℂ) * ζ ^ 30 - ((19 / 110) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_5_1 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        5 1 =
      alternatingSixAmbientRow18TransformedGeneratorA
        5 1 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_5_1_0,
      row18_transformedGeneratorA_term_5_1_1,
      row18_transformedGeneratorA_term_5_1_2,
      row18_transformedGeneratorA_term_5_1_3,
      row18_transformedGeneratorA_term_5_1_4,
      row18_transformedGeneratorA_term_5_1_5,
      row18_transformedGeneratorA_term_5_1_6,
      row18_transformedGeneratorA_term_5_1_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_2_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 2 =
      (((141 / 1580) : ℂ) + ((109 / 17380) : ℂ) * ζ ^ 1 - ((773 / 8690) : ℂ) * ζ ^ 2 - ((2263 / 17380) : ℂ) * ζ ^ 3 - ((2103 / 17380) : ℂ) * ζ ^ 5 - ((2049 / 17380) : ℂ) * ζ ^ 6 + ((57 / 1580) : ℂ) * ζ ^ 8 - ((1279 / 8690) : ℂ) * ζ ^ 9 + ((2909 / 17380) : ℂ) * ζ ^ 11 - ((26 / 395) : ℂ) * ζ ^ 12 - ((109 / 17380) : ℂ) * ζ ^ 13 + ((773 / 4345) : ℂ) * ζ ^ 15 - ((109 / 17380) : ℂ) * ζ ^ 17 + ((87 / 4345) : ℂ) * ζ ^ 18 + ((917 / 17380) : ℂ) * ζ ^ 21 + ((773 / 8690) : ℂ) * ζ ^ 22 + ((147 / 1580) : ℂ) * ζ ^ 24 + ((7 / 55) : ℂ) * ζ ^ 25 - ((2331 / 17380) : ℂ) * ζ ^ 27 - ((57 / 1580) : ℂ) * ζ ^ 28 + ((109 / 17380) : ℂ) * ζ ^ 29 - ((818 / 4345) : ℂ) * ζ ^ 30 - ((2909 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((259 / 3476) : ℂ) + ((87 / 3476) : ℂ) * ζ ^ 1 + ((457 / 8690) : ℂ) * ζ ^ 2 + ((2051 / 17380) : ℂ) * ζ ^ 3 + ((1791 / 17380) : ℂ) * ζ ^ 4 + ((7 / 79) : ℂ) * ζ ^ 5 + ((819 / 17380) : ℂ) * ζ ^ 6 - ((3001 / 17380) : ℂ) * ζ ^ 7 - ((32 / 395) : ℂ) * ζ ^ 8 + ((223 / 4345) : ℂ) * ζ ^ 9 + ((81 / 3476) : ℂ) * ζ ^ 10 + ((103 / 4345) : ℂ) * ζ ^ 11 + ((2511 / 17380) : ℂ) * ζ ^ 12 + ((267 / 17380) : ℂ) * ζ ^ 13 + ((7 / 4345) : ℂ) * ζ ^ 14 + ((39 / 3476) : ℂ) * ζ ^ 15 - ((453 / 4345) : ℂ) * ζ ^ 16 - ((67 / 17380) : ℂ) * ζ ^ 17 + ((194 / 4345) : ℂ) * ζ ^ 18 + ((307 / 3476) : ℂ) * ζ ^ 19 + ((112 / 4345) : ℂ) * ζ ^ 20 - ((1799 / 17380) : ℂ) * ζ ^ 21 - ((239 / 4345) : ℂ) * ζ ^ 22 - ((293 / 17380) : ℂ) * ζ ^ 23 - ((97 / 4345) : ℂ) * ζ ^ 24 + ((1 / 395) : ℂ) * ζ ^ 25 + ((133 / 3476) : ℂ) * ζ ^ 26 - ((9 / 869) : ℂ) * ζ ^ 27 - ((401 / 17380) : ℂ) * ζ ^ 28 + ((367 / 17380) : ℂ) * ζ ^ 29 + ((51 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_2_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 2 =
      (((1351 / 8690) : ℂ) + ((516 / 4345) : ℂ) * ζ ^ 1 + ((131 / 1738) : ℂ) * ζ ^ 2 - ((2043 / 8690) : ℂ) * ζ ^ 3 + ((1701 / 8690) : ℂ) * ζ ^ 5 + ((107 / 869) : ℂ) * ζ ^ 6 + ((349 / 17380) : ℂ) * ζ ^ 8 - ((749 / 8690) : ℂ) * ζ ^ 9 + ((27 / 220) : ℂ) * ζ ^ 11 - ((257 / 4345) : ℂ) * ζ ^ 12 - ((516 / 4345) : ℂ) * ζ ^ 13 + ((831 / 4345) : ℂ) * ζ ^ 15 - ((516 / 4345) : ℂ) * ζ ^ 17 - ((885 / 3476) : ℂ) * ζ ^ 18 + ((41 / 8690) : ℂ) * ζ ^ 21 - ((131 / 1738) : ℂ) * ζ ^ 22 - ((334 / 4345) : ℂ) * ζ ^ 24 - ((669 / 8690) : ℂ) * ζ ^ 25 - ((1637 / 17380) : ℂ) * ζ ^ 27 - ((349 / 17380) : ℂ) * ζ ^ 28 + ((516 / 4345) : ℂ) * ζ ^ 29 + ((651 / 3476) : ℂ) * ζ ^ 30 - ((27 / 220) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1429 / 8690) : ℂ) - ((29 / 395) : ℂ) * ζ ^ 1 - ((1421 / 17380) : ℂ) * ζ ^ 2 + ((1939 / 17380) : ℂ) * ζ ^ 3 + ((911 / 8690) : ℂ) * ζ ^ 4 + ((863 / 8690) : ℂ) * ζ ^ 5 + ((571 / 4345) : ℂ) * ζ ^ 6 - ((1363 / 8690) : ℂ) * ζ ^ 7 - ((189 / 4345) : ℂ) * ζ ^ 8 + ((1941 / 17380) : ℂ) * ζ ^ 9 - ((593 / 8690) : ℂ) * ζ ^ 10 + ((475 / 3476) : ℂ) * ζ ^ 11 + ((1579 / 17380) : ℂ) * ζ ^ 12 - ((161 / 3476) : ℂ) * ζ ^ 13 + ((861 / 17380) : ℂ) * ζ ^ 14 - ((361 / 8690) : ℂ) * ζ ^ 15 - ((62 / 4345) : ℂ) * ζ ^ 16 - ((381 / 17380) : ℂ) * ζ ^ 17 + ((142 / 4345) : ℂ) * ζ ^ 18 + ((3447 / 17380) : ℂ) * ζ ^ 19 - ((177 / 17380) : ℂ) * ζ ^ 20 - ((613 / 8690) : ℂ) * ζ ^ 21 + ((173 / 1738) : ℂ) * ζ ^ 22 + ((334 / 4345) : ℂ) * ζ ^ 23 + ((62 / 4345) : ℂ) * ζ ^ 24 + ((23 / 220) : ℂ) * ζ ^ 25 + ((1773 / 17380) : ℂ) * ζ ^ 26 - ((177 / 3476) : ℂ) * ζ ^ 27 - ((331 / 4345) : ℂ) * ζ ^ 28 + ((159 / 4345) : ℂ) * ζ ^ 29)

private theorem row18_transformedGeneratorA_term_5_2_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 2 =
      (-((488 / 4345) : ℂ) - ((558 / 4345) : ℂ) * ζ ^ 1 + ((31 / 790) : ℂ) * ζ ^ 2 + ((103 / 4345) : ℂ) * ζ ^ 3 - ((324 / 4345) : ℂ) * ζ ^ 5 + ((22 / 395) : ℂ) * ζ ^ 6 + ((19 / 4345) : ℂ) * ζ ^ 8 + ((699 / 17380) : ℂ) * ζ ^ 9 + ((89 / 17380) : ℂ) * ζ ^ 11 + ((343 / 17380) : ℂ) * ζ ^ 12 + ((558 / 4345) : ℂ) * ζ ^ 13 - ((1113 / 17380) : ℂ) * ζ ^ 15 + ((558 / 4345) : ℂ) * ζ ^ 17 + ((199 / 1580) : ℂ) * ζ ^ 18 + ((31 / 220) : ℂ) * ζ ^ 21 - ((31 / 790) : ℂ) * ζ ^ 22 - ((1549 / 17380) : ℂ) * ζ ^ 24 - ((234 / 4345) : ℂ) * ζ ^ 25 + ((1957 / 8690) : ℂ) * ζ ^ 27 - ((19 / 4345) : ℂ) * ζ ^ 28 - ((558 / 4345) : ℂ) * ζ ^ 29 - ((51 / 1580) : ℂ) * ζ ^ 30 - ((89 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((488 / 4345) : ℂ) + ((106 / 869) : ℂ) * ζ ^ 1 - ((387 / 17380) : ℂ) * ζ ^ 2 + ((84 / 4345) : ℂ) * ζ ^ 3 - ((443 / 1738) : ℂ) * ζ ^ 4 + ((1373 / 17380) : ℂ) * ζ ^ 5 - ((541 / 8690) : ℂ) * ζ ^ 6 - ((217 / 3476) : ℂ) * ζ ^ 7 + ((2327 / 17380) : ℂ) * ζ ^ 8 - ((343 / 8690) : ℂ) * ζ ^ 9 - ((1613 / 17380) : ℂ) * ζ ^ 10 - ((2 / 79) : ℂ) * ζ ^ 11 - ((267 / 4345) : ℂ) * ζ ^ 12 - ((108 / 869) : ℂ) * ζ ^ 13 + ((3407 / 17380) : ℂ) * ζ ^ 14 - ((5 / 158) : ℂ) * ζ ^ 15 - ((233 / 8690) : ℂ) * ζ ^ 16 + ((1011 / 17380) : ℂ) * ζ ^ 17 - ((2077 / 17380) : ℂ) * ζ ^ 18 - ((2137 / 17380) : ℂ) * ζ ^ 19 + ((1563 / 17380) : ℂ) * ζ ^ 20 - ((1033 / 8690) : ℂ) * ζ ^ 21 + ((133 / 8690) : ℂ) * ζ ^ 22 + ((1933 / 17380) : ℂ) * ζ ^ 23 + ((188 / 4345) : ℂ) * ζ ^ 24 + ((43 / 4345) : ℂ) * ζ ^ 25 + ((9 / 790) : ℂ) * ζ ^ 26 + ((13 / 1738) : ℂ) * ζ ^ 27 - ((42 / 4345) : ℂ) * ζ ^ 28 + ((96 / 4345) : ℂ) * ζ ^ 29 - ((189 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_2_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 2 =
      (-((63 / 790) : ℂ) - ((57 / 1580) : ℂ) * ζ ^ 1 + ((39 / 790) : ℂ) * ζ ^ 2 + ((25 / 316) : ℂ) * ζ ^ 3 - ((171 / 1580) : ℂ) * ζ ^ 5 - ((19 / 790) : ℂ) * ζ ^ 6 - ((77 / 1580) : ℂ) * ζ ^ 8 + ((69 / 1580) : ℂ) * ζ ^ 9 - ((5 / 316) : ℂ) * ζ ^ 11 - ((41 / 1580) : ℂ) * ζ ^ 12 + ((57 / 1580) : ℂ) * ζ ^ 13 - ((13 / 79) : ℂ) * ζ ^ 15 + ((57 / 1580) : ℂ) * ζ ^ 17 - ((37 / 790) : ℂ) * ζ ^ 18 + ((39 / 1580) : ℂ) * ζ ^ 21 - ((39 / 790) : ℂ) * ζ ^ 22 + ((53 / 1580) : ℂ) * ζ ^ 24 + ((57 / 790) : ℂ) * ζ ^ 25 + ((3 / 79) : ℂ) * ζ ^ 27 + ((77 / 1580) : ℂ) * ζ ^ 28 - ((57 / 1580) : ℂ) * ζ ^ 29 - ((9 / 1580) : ℂ) * ζ ^ 30 + ((5 / 316) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((119 / 790) : ℂ) + ((89 / 1580) : ℂ) * ζ ^ 1 + ((11 / 158) : ℂ) * ζ ^ 2 - ((29 / 1580) : ℂ) * ζ ^ 3 - ((43 / 395) : ℂ) * ζ ^ 4 + ((43 / 790) : ℂ) * ζ ^ 5 + ((143 / 1580) : ℂ) * ζ ^ 6 + ((1 / 158) : ℂ) * ζ ^ 7 + ((59 / 395) : ℂ) * ζ ^ 8 - ((111 / 1580) : ℂ) * ζ ^ 9 - ((57 / 790) : ℂ) * ζ ^ 10 - ((83 / 790) : ℂ) * ζ ^ 11 + ((131 / 1580) : ℂ) * ζ ^ 12 - ((4 / 395) : ℂ) * ζ ^ 13 - ((7 / 790) : ℂ) * ζ ^ 14 + ((66 / 395) : ℂ) * ζ ^ 15 - ((13 / 790) : ℂ) * ζ ^ 16 + ((53 / 1580) : ℂ) * ζ ^ 17 - ((51 / 790) : ℂ) * ζ ^ 18 - ((109 / 790) : ℂ) * ζ ^ 19 + ((6 / 79) : ℂ) * ζ ^ 20 + ((6 / 79) : ℂ) * ζ ^ 21 + ((39 / 1580) : ℂ) * ζ ^ 22 + ((259 / 1580) : ℂ) * ζ ^ 23 + ((4 / 395) : ℂ) * ζ ^ 24 - ((48 / 395) : ℂ) * ζ ^ 25 + ((41 / 1580) : ℂ) * ζ ^ 26 + ((5 / 316) : ℂ) * ζ ^ 27 + ((1 / 1580) : ℂ) * ζ ^ 28 + ((101 / 1580) : ℂ) * ζ ^ 29 + ((3 / 316) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_2_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 2 =
      (((39 / 1738) : ℂ) + ((191 / 1580) : ℂ) * ζ ^ 1 - ((116 / 4345) : ℂ) * ζ ^ 2 + ((861 / 8690) : ℂ) * ζ ^ 3 + ((12 / 395) : ℂ) * ζ ^ 5 + ((357 / 8690) : ℂ) * ζ ^ 6 - ((233 / 3476) : ℂ) * ζ ^ 8 - ((18 / 395) : ℂ) * ζ ^ 9 - ((69 / 4345) : ℂ) * ζ ^ 11 - ((75 / 1738) : ℂ) * ζ ^ 12 - ((191 / 1580) : ℂ) * ζ ^ 13 + ((111 / 8690) : ℂ) * ζ ^ 15 - ((191 / 1580) : ℂ) * ζ ^ 17 + ((513 / 4345) : ℂ) * ζ ^ 18 - ((41 / 790) : ℂ) * ζ ^ 21 + ((116 / 4345) : ℂ) * ζ ^ 22 - ((117 / 3476) : ℂ) * ζ ^ 24 + ((143 / 1580) : ℂ) * ζ ^ 25 - ((1571 / 17380) : ℂ) * ζ ^ 27 + ((233 / 3476) : ℂ) * ζ ^ 28 + ((191 / 1580) : ℂ) * ζ ^ 29 - ((603 / 17380) : ℂ) * ζ ^ 30 + ((69 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((399 / 17380) : ℂ) - ((1847 / 17380) : ℂ) * ζ ^ 1 + ((2051 / 17380) : ℂ) * ζ ^ 2 + ((69 / 17380) : ℂ) * ζ ^ 3 + ((399 / 17380) : ℂ) * ζ ^ 4 + ((1301 / 8690) : ℂ) * ζ ^ 5 - ((229 / 4345) : ℂ) * ζ ^ 6 + ((67 / 395) : ℂ) * ζ ^ 7 - ((67 / 8690) : ℂ) * ζ ^ 8 - ((353 / 3476) : ℂ) * ζ ^ 9 + ((65 / 869) : ℂ) * ζ ^ 10 - ((3829 / 17380) : ℂ) * ζ ^ 11 + ((183 / 17380) : ℂ) * ζ ^ 12 - ((9 / 3476) : ℂ) * ζ ^ 13 - ((81 / 4345) : ℂ) * ζ ^ 14 + ((1031 / 17380) : ℂ) * ζ ^ 15 + ((83 / 17380) : ℂ) * ζ ^ 16 - ((202 / 4345) : ℂ) * ζ ^ 17 - ((987 / 8690) : ℂ) * ζ ^ 18 + ((7 / 790) : ℂ) * ζ ^ 19 - ((28 / 869) : ℂ) * ζ ^ 20 - ((125 / 3476) : ℂ) * ζ ^ 21 + ((60 / 869) : ℂ) * ζ ^ 22 - ((2019 / 17380) : ℂ) * ζ ^ 23 + ((204 / 4345) : ℂ) * ζ ^ 24 + ((1451 / 17380) : ℂ) * ζ ^ 25 + ((1 / 395) : ℂ) * ζ ^ 26 + ((663 / 4345) : ℂ) * ζ ^ 27 - ((137 / 4345) : ℂ) * ζ ^ 28 + ((139 / 8690) : ℂ) * ζ ^ 29 - ((119 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_2_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 2 =
      (-((1 / 11) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 1 - ((7 / 44) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 3 + ((3 / 44) : ℂ) * ζ ^ 5 - ((9 / 44) : ℂ) * ζ ^ 6 + ((2 / 11) : ℂ) * ζ ^ 8 + ((9 / 44) : ℂ) * ζ ^ 9 - ((7 / 44) : ℂ) * ζ ^ 11 + ((3 / 22) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 13 + ((3 / 44) : ℂ) * ζ ^ 15 + ((1 / 11) : ℂ) * ζ ^ 17 - ((1 / 44) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 21 + ((7 / 44) : ℂ) * ζ ^ 22 - ((5 / 44) : ℂ) * ζ ^ 24 - ((7 / 44) : ℂ) * ζ ^ 25 + ((3 / 44) : ℂ) * ζ ^ 27 - ((2 / 11) : ℂ) * ζ ^ 28 - ((1 / 11) : ℂ) * ζ ^ 29 - ((1 / 11) : ℂ) * ζ ^ 30 + ((7 / 44) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_2_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 2 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_2_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 2 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_5_2 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        5 2 =
      alternatingSixAmbientRow18TransformedGeneratorA
        5 2 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_5_2_0,
      row18_transformedGeneratorA_term_5_2_1,
      row18_transformedGeneratorA_term_5_2_2,
      row18_transformedGeneratorA_term_5_2_3,
      row18_transformedGeneratorA_term_5_2_4,
      row18_transformedGeneratorA_term_5_2_5,
      row18_transformedGeneratorA_term_5_2_6,
      row18_transformedGeneratorA_term_5_2_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_3_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 3 =
      (((1421 / 8690) : ℂ) + ((383 / 4345) : ℂ) * ζ ^ 1 + ((4469 / 17380) : ℂ) * ζ ^ 2 - ((159 / 1738) : ℂ) * ζ ^ 3 - ((877 / 8690) : ℂ) * ζ ^ 5 + ((9 / 220) : ℂ) * ζ ^ 6 - ((1313 / 8690) : ℂ) * ζ ^ 8 + ((1371 / 17380) : ℂ) * ζ ^ 9 - ((72 / 869) : ℂ) * ζ ^ 11 - ((5033 / 17380) : ℂ) * ζ ^ 12 - ((383 / 4345) : ℂ) * ζ ^ 13 + ((675 / 3476) : ℂ) * ζ ^ 15 - ((383 / 4345) : ℂ) * ζ ^ 17 - ((3837 / 17380) : ℂ) * ζ ^ 18 - ((199 / 17380) : ℂ) * ζ ^ 21 - ((4469 / 17380) : ℂ) * ζ ^ 22 + ((6869 / 17380) : ℂ) * ζ ^ 24 + ((1643 / 8690) : ℂ) * ζ ^ 25 - ((164 / 869) : ℂ) * ζ ^ 27 + ((1313 / 8690) : ℂ) * ζ ^ 28 + ((383 / 4345) : ℂ) * ζ ^ 29 + ((1599 / 8690) : ℂ) * ζ ^ 30 + ((72 / 869) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1349 / 8690) : ℂ) - ((331 / 8690) : ℂ) * ζ ^ 1 - ((3167 / 17380) : ℂ) * ζ ^ 2 + ((323 / 8690) : ℂ) * ζ ^ 3 + ((12 / 395) : ℂ) * ζ ^ 4 + ((3511 / 17380) : ℂ) * ζ ^ 5 + ((111 / 869) : ℂ) * ζ ^ 6 - ((133 / 3476) : ℂ) * ζ ^ 7 + ((1413 / 17380) : ℂ) * ζ ^ 8 - ((409 / 1580) : ℂ) * ζ ^ 9 - ((309 / 1738) : ℂ) * ζ ^ 10 + ((1429 / 17380) : ℂ) * ζ ^ 11 + ((1957 / 8690) : ℂ) * ζ ^ 12 + ((706 / 4345) : ℂ) * ζ ^ 13 - ((203 / 1580) : ℂ) * ζ ^ 14 - ((639 / 4345) : ℂ) * ζ ^ 15 - ((2103 / 17380) : ℂ) * ζ ^ 16 + ((226 / 4345) : ℂ) * ζ ^ 17 - ((651 / 17380) : ℂ) * ζ ^ 18 + ((201 / 3476) : ℂ) * ζ ^ 19 + ((3099 / 17380) : ℂ) * ζ ^ 20 - ((109 / 1738) : ℂ) * ζ ^ 21 + ((1841 / 17380) : ℂ) * ζ ^ 22 - ((443 / 4345) : ℂ) * ζ ^ 23 - ((17 / 79) : ℂ) * ζ ^ 24 + ((1159 / 17380) : ℂ) * ζ ^ 25 + ((485 / 3476) : ℂ) * ζ ^ 26 - ((155 / 3476) : ℂ) * ζ ^ 27 - ((351 / 4345) : ℂ) * ζ ^ 28 + ((73 / 1738) : ℂ) * ζ ^ 29 + ((57 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_3_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 3 =
      (-((497 / 8690) : ℂ) + ((3209 / 8690) : ℂ) * ζ ^ 1 + ((679 / 17380) : ℂ) * ζ ^ 2 + ((137 / 395) : ℂ) * ζ ^ 3 - ((289 / 4345) : ℂ) * ζ ^ 5 - ((537 / 8690) : ℂ) * ζ ^ 6 + ((5497 / 17380) : ℂ) * ζ ^ 8 - ((2731 / 17380) : ℂ) * ζ ^ 9 - ((217 / 790) : ℂ) * ζ ^ 11 - ((41 / 220) : ℂ) * ζ ^ 12 - ((3209 / 8690) : ℂ) * ζ ^ 13 - ((3 / 395) : ℂ) * ζ ^ 15 - ((3209 / 8690) : ℂ) * ζ ^ 17 + ((82 / 4345) : ℂ) * ζ ^ 18 - ((1479 / 4345) : ℂ) * ζ ^ 21 - ((679 / 17380) : ℂ) * ζ ^ 22 + ((1227 / 17380) : ℂ) * ζ ^ 24 + ((3787 / 8690) : ℂ) * ζ ^ 25 - ((59 / 1580) : ℂ) * ζ ^ 27 - ((5497 / 17380) : ℂ) * ζ ^ 28 + ((3209 / 8690) : ℂ) * ζ ^ 29 + ((7043 / 17380) : ℂ) * ζ ^ 30 + ((217 / 790) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((929 / 17380) : ℂ) - ((1341 / 3476) : ℂ) * ζ ^ 1 + ((13 / 220) : ℂ) * ζ ^ 2 - ((3287 / 17380) : ℂ) * ζ ^ 3 - ((467 / 4345) : ℂ) * ζ ^ 4 + ((1953 / 17380) : ℂ) * ζ ^ 5 - ((4167 / 17380) : ℂ) * ζ ^ 6 + ((4143 / 17380) : ℂ) * ζ ^ 7 - ((143 / 790) : ℂ) * ζ ^ 8 + ((150 / 869) : ℂ) * ζ ^ 9 + ((119 / 4345) : ℂ) * ζ ^ 10 - ((7047 / 17380) : ℂ) * ζ ^ 11 + ((2307 / 17380) : ℂ) * ζ ^ 12 + ((2121 / 8690) : ℂ) * ζ ^ 13 + ((3637 / 8690) : ℂ) * ζ ^ 14 + ((173 / 8690) : ℂ) * ζ ^ 15 - ((642 / 4345) : ℂ) * ζ ^ 16 + ((531 / 3476) : ℂ) * ζ ^ 17 - ((439 / 1580) : ℂ) * ζ ^ 18 - ((131 / 869) : ℂ) * ζ ^ 19 + ((827 / 3476) : ℂ) * ζ ^ 20 + ((4561 / 17380) : ℂ) * ζ ^ 21 - ((2121 / 17380) : ℂ) * ζ ^ 22 - ((1544 / 4345) : ℂ) * ζ ^ 23 + ((229 / 3476) : ℂ) * ζ ^ 24 + ((751 / 17380) : ℂ) * ζ ^ 25 - ((174 / 869) : ℂ) * ζ ^ 26 + ((197 / 1738) : ℂ) * ζ ^ 27 - ((401 / 8690) : ℂ) * ζ ^ 28 - ((1203 / 8690) : ℂ) * ζ ^ 29 - ((4929 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_3_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 3 =
      (((83 / 1738) : ℂ) + ((108 / 4345) : ℂ) * ζ ^ 1 - ((3129 / 17380) : ℂ) * ζ ^ 2 - ((161 / 4345) : ℂ) * ζ ^ 3 + ((941 / 17380) : ℂ) * ζ ^ 5 - ((1361 / 17380) : ℂ) * ζ ^ 6 + ((137 / 869) : ℂ) * ζ ^ 8 - ((4789 / 17380) : ℂ) * ζ ^ 9 + ((1821 / 8690) : ℂ) * ζ ^ 11 + ((719 / 3476) : ℂ) * ζ ^ 12 - ((108 / 4345) : ℂ) * ζ ^ 13 + ((911 / 17380) : ℂ) * ζ ^ 15 - ((108 / 4345) : ℂ) * ζ ^ 17 + ((13 / 220) : ℂ) * ζ ^ 18 + ((239 / 4345) : ℂ) * ζ ^ 21 + ((3129 / 17380) : ℂ) * ζ ^ 22 - ((953 / 3476) : ℂ) * ζ ^ 24 - ((509 / 17380) : ℂ) * ζ ^ 25 + ((808 / 4345) : ℂ) * ζ ^ 27 - ((137 / 869) : ℂ) * ζ ^ 28 + ((108 / 4345) : ℂ) * ζ ^ 29 - ((3603 / 17380) : ℂ) * ζ ^ 30 - ((1821 / 8690) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((59 / 869) : ℂ) - ((6 / 869) : ℂ) * ζ ^ 1 + ((107 / 316) : ℂ) * ζ ^ 2 - ((403 / 4345) : ℂ) * ζ ^ 3 + ((1021 / 4345) : ℂ) * ζ ^ 4 - ((3369 / 17380) : ℂ) * ζ ^ 5 - ((1909 / 17380) : ℂ) * ζ ^ 6 + ((349 / 4345) : ℂ) * ζ ^ 7 + ((171 / 8690) : ℂ) * ζ ^ 8 + ((1623 / 17380) : ℂ) * ζ ^ 9 - ((41 / 17380) : ℂ) * ζ ^ 10 - ((3521 / 17380) : ℂ) * ζ ^ 11 - ((423 / 8690) : ℂ) * ζ ^ 12 - ((17 / 1580) : ℂ) * ζ ^ 13 + ((191 / 17380) : ℂ) * ζ ^ 14 - ((131 / 3476) : ℂ) * ζ ^ 15 + ((964 / 4345) : ℂ) * ζ ^ 16 + ((659 / 4345) : ℂ) * ζ ^ 17 - ((469 / 3476) : ℂ) * ζ ^ 18 + ((101 / 1580) : ℂ) * ζ ^ 19 - ((2099 / 8690) : ℂ) * ζ ^ 20 - ((31 / 8690) : ℂ) * ζ ^ 21 - ((489 / 17380) : ℂ) * ζ ^ 22 + ((299 / 8690) : ℂ) * ζ ^ 23 + ((193 / 8690) : ℂ) * ζ ^ 24 + ((439 / 8690) : ℂ) * ζ ^ 25 + ((877 / 17380) : ℂ) * ζ ^ 26 - ((166 / 4345) : ℂ) * ζ ^ 27 + ((21 / 869) : ℂ) * ζ ^ 28 - ((7 / 158) : ℂ) * ζ ^ 29 + ((36 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_3_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 3 =
      (((102 / 395) : ℂ) - ((149 / 395) : ℂ) * ζ ^ 1 + ((84 / 395) : ℂ) * ζ ^ 2 - ((53 / 1580) : ℂ) * ζ ^ 3 + ((197 / 1580) : ℂ) * ζ ^ 5 - ((171 / 1580) : ℂ) * ζ ^ 6 - ((141 / 395) : ℂ) * ζ ^ 8 + ((381 / 790) : ℂ) * ζ ^ 9 - ((541 / 1580) : ℂ) * ζ ^ 11 + ((29 / 790) : ℂ) * ζ ^ 12 + ((149 / 395) : ℂ) * ζ ^ 13 - ((239 / 790) : ℂ) * ζ ^ 15 + ((149 / 395) : ℂ) * ζ ^ 17 - ((159 / 790) : ℂ) * ζ ^ 18 + ((123 / 395) : ℂ) * ζ ^ 21 - ((84 / 395) : ℂ) * ζ ^ 22 + ((411 / 1580) : ℂ) * ζ ^ 24 - ((793 / 1580) : ℂ) * ζ ^ 25 + ((389 / 1580) : ℂ) * ζ ^ 27 + ((141 / 395) : ℂ) * ζ ^ 28 - ((149 / 395) : ℂ) * ζ ^ 29 - ((593 / 1580) : ℂ) * ζ ^ 30 + ((541 / 1580) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((53 / 158) : ℂ) + ((105 / 316) : ℂ) * ζ ^ 1 - ((147 / 395) : ℂ) * ζ ^ 2 + ((41 / 1580) : ℂ) * ζ ^ 3 + ((477 / 1580) : ℂ) * ζ ^ 4 - ((249 / 790) : ℂ) * ζ ^ 5 + ((126 / 395) : ℂ) * ζ ^ 6 - ((19 / 316) : ℂ) * ζ ^ 7 - ((11 / 158) : ℂ) * ζ ^ 8 - ((31 / 1580) : ℂ) * ζ ^ 9 - ((42 / 395) : ℂ) * ζ ^ 10 + ((1071 / 1580) : ℂ) * ζ ^ 11 - ((192 / 395) : ℂ) * ζ ^ 12 - ((77 / 1580) : ℂ) * ζ ^ 13 - ((93 / 790) : ℂ) * ζ ^ 14 + ((3 / 79) : ℂ) * ζ ^ 15 + ((647 / 1580) : ℂ) * ζ ^ 16 - ((213 / 790) : ℂ) * ζ ^ 17 + ((213 / 790) : ℂ) * ζ ^ 18 - ((89 / 790) : ℂ) * ζ ^ 19 - ((113 / 395) : ℂ) * ζ ^ 20 - ((231 / 790) : ℂ) * ζ ^ 21 - ((29 / 316) : ℂ) * ζ ^ 22 + ((96 / 395) : ℂ) * ζ ^ 23 + ((13 / 395) : ℂ) * ζ ^ 24 + ((23 / 316) : ℂ) * ζ ^ 25 - ((177 / 1580) : ℂ) * ζ ^ 26 - ((147 / 790) : ℂ) * ζ ^ 27 - ((5 / 316) : ℂ) * ζ ^ 28 - ((39 / 790) : ℂ) * ζ ^ 29 + ((18 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_3_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 3 =
      (-((2257 / 17380) : ℂ) + ((729 / 17380) : ℂ) * ζ ^ 1 + ((585 / 3476) : ℂ) * ζ ^ 2 - ((236 / 4345) : ℂ) * ζ ^ 3 - ((2109 / 8690) : ℂ) * ζ ^ 5 + ((89 / 3476) : ℂ) * ζ ^ 6 + ((13 / 8690) : ℂ) * ζ ^ 8 - ((4283 / 17380) : ℂ) * ζ ^ 9 + ((5067 / 17380) : ℂ) * ζ ^ 11 - ((631 / 8690) : ℂ) * ζ ^ 12 - ((729 / 17380) : ℂ) * ζ ^ 13 + ((3121 / 17380) : ℂ) * ζ ^ 15 - ((729 / 17380) : ℂ) * ζ ^ 17 + ((129 / 1738) : ℂ) * ζ ^ 18 + ((401 / 8690) : ℂ) * ζ ^ 21 - ((585 / 3476) : ℂ) * ζ ^ 22 - ((101 / 4345) : ℂ) * ζ ^ 24 + ((4947 / 17380) : ℂ) * ζ ^ 25 - ((3633 / 17380) : ℂ) * ζ ^ 27 - ((13 / 8690) : ℂ) * ζ ^ 28 + ((729 / 17380) : ℂ) * ζ ^ 29 + ((126 / 869) : ℂ) * ζ ^ 30 - ((5067 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((223 / 1738) : ℂ) + ((32 / 4345) : ℂ) * ζ ^ 1 - ((579 / 8690) : ℂ) * ζ ^ 2 - ((459 / 17380) : ℂ) * ζ ^ 3 - ((1329 / 8690) : ℂ) * ζ ^ 4 + ((2096 / 4345) : ℂ) * ζ ^ 5 + ((425 / 3476) : ℂ) * ζ ^ 6 - ((89 / 3476) : ℂ) * ζ ^ 7 - ((371 / 1580) : ℂ) * ζ ^ 8 - ((337 / 17380) : ℂ) * ζ ^ 9 + ((2293 / 17380) : ℂ) * ζ ^ 10 - ((5563 / 17380) : ℂ) * ζ ^ 11 - ((753 / 17380) : ℂ) * ζ ^ 12 - ((1358 / 4345) : ℂ) * ζ ^ 13 + ((481 / 1580) : ℂ) * ζ ^ 14 + ((2749 / 8690) : ℂ) * ζ ^ 15 - ((2433 / 8690) : ℂ) * ζ ^ 16 + ((1307 / 17380) : ℂ) * ζ ^ 17 - ((747 / 8690) : ℂ) * ζ ^ 18 + ((409 / 4345) : ℂ) * ζ ^ 19 + ((514 / 4345) : ℂ) * ζ ^ 20 - ((3033 / 17380) : ℂ) * ζ ^ 21 - ((601 / 17380) : ℂ) * ζ ^ 22 - ((917 / 17380) : ℂ) * ζ ^ 23 + ((471 / 8690) : ℂ) * ζ ^ 24 - ((1979 / 8690) : ℂ) * ζ ^ 25 - ((1153 / 17380) : ℂ) * ζ ^ 26 + ((733 / 4345) : ℂ) * ζ ^ 27 + ((313 / 8690) : ℂ) * ζ ^ 28 + ((1074 / 4345) : ℂ) * ζ ^ 29 - ((17 / 110) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_3_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 3 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_3_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 3 =
      (-((6 / 55) : ℂ) - ((6 / 55) : ℂ) * ζ ^ 1 - ((57 / 220) : ℂ) * ζ ^ 2 - ((21 / 110) : ℂ) * ζ ^ 3 + ((9 / 110) : ℂ) * ζ ^ 5 + ((8 / 55) : ℂ) * ζ ^ 6 + ((37 / 220) : ℂ) * ζ ^ 8 + ((43 / 220) : ℂ) * ζ ^ 9 - ((1 / 55) : ℂ) * ζ ^ 11 + ((9 / 55) : ℂ) * ζ ^ 12 + ((6 / 55) : ℂ) * ζ ^ 13 + ((2 / 55) : ℂ) * ζ ^ 15 + ((6 / 55) : ℂ) * ζ ^ 17 + ((3 / 110) : ℂ) * ζ ^ 18 + ((2 / 55) : ℂ) * ζ ^ 21 + ((57 / 220) : ℂ) * ζ ^ 22 - ((63 / 220) : ℂ) * ζ ^ 24 - ((21 / 110) : ℂ) * ζ ^ 25 - ((7 / 110) : ℂ) * ζ ^ 27 - ((37 / 220) : ℂ) * ζ ^ 28 - ((6 / 55) : ℂ) * ζ ^ 29 - ((9 / 220) : ℂ) * ζ ^ 30 + ((1 / 55) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((6 / 55) : ℂ) + ((6 / 55) : ℂ) * ζ ^ 1 + ((57 / 220) : ℂ) * ζ ^ 2)

private theorem row18_transformedGeneratorA_term_5_3_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 3 =
      (-((27 / 220) : ℂ) - ((4 / 55) : ℂ) * ζ ^ 1 - ((7 / 55) : ℂ) * ζ ^ 2 + ((7 / 110) : ℂ) * ζ ^ 3 + ((3 / 55) : ℂ) * ζ ^ 5 + ((2 / 55) : ℂ) * ζ ^ 6 - ((17 / 110) : ℂ) * ζ ^ 8 - ((2 / 55) : ℂ) * ζ ^ 9 + ((19 / 110) : ℂ) * ζ ^ 11 + ((13 / 220) : ℂ) * ζ ^ 12 + ((4 / 55) : ℂ) * ζ ^ 13 - ((21 / 220) : ℂ) * ζ ^ 15 + ((4 / 55) : ℂ) * ζ ^ 17 + ((29 / 220) : ℂ) * ζ ^ 18 - ((13 / 220) : ℂ) * ζ ^ 21 + ((7 / 55) : ℂ) * ζ ^ 22 - ((9 / 220) : ℂ) * ζ ^ 24 - ((7 / 55) : ℂ) * ζ ^ 25 + ((23 / 220) : ℂ) * ζ ^ 27 + ((17 / 110) : ℂ) * ζ ^ 28 - ((4 / 55) : ℂ) * ζ ^ 29 - ((4 / 55) : ℂ) * ζ ^ 30 - ((19 / 110) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_5_3 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        5 3 =
      alternatingSixAmbientRow18TransformedGeneratorA
        5 3 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_5_3_0,
      row18_transformedGeneratorA_term_5_3_1,
      row18_transformedGeneratorA_term_5_3_2,
      row18_transformedGeneratorA_term_5_3_3,
      row18_transformedGeneratorA_term_5_3_4,
      row18_transformedGeneratorA_term_5_3_5,
      row18_transformedGeneratorA_term_5_3_6,
      row18_transformedGeneratorA_term_5_3_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_4_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 4 =
      (((1589 / 17380) : ℂ) + ((525 / 3476) : ℂ) * ζ ^ 1 - ((1123 / 8690) : ℂ) * ζ ^ 2 - ((153 / 1738) : ℂ) * ζ ^ 3 + ((423 / 3476) : ℂ) * ζ ^ 5 - ((1849 / 17380) : ℂ) * ζ ^ 6 + ((699 / 8690) : ℂ) * ζ ^ 8 - ((7 / 3476) : ℂ) * ζ ^ 9 - ((103 / 3476) : ℂ) * ζ ^ 11 - ((573 / 8690) : ℂ) * ζ ^ 12 - ((525 / 3476) : ℂ) * ζ ^ 13 + ((305 / 3476) : ℂ) * ζ ^ 15 - ((525 / 3476) : ℂ) * ζ ^ 17 + ((2503 / 17380) : ℂ) * ζ ^ 18 - ((313 / 1738) : ℂ) * ζ ^ 21 + ((1123 / 8690) : ℂ) * ζ ^ 22 - ((717 / 17380) : ℂ) * ζ ^ 24 + ((51 / 1738) : ℂ) * ζ ^ 25 + ((37 / 1738) : ℂ) * ζ ^ 27 - ((699 / 8690) : ℂ) * ζ ^ 28 + ((525 / 3476) : ℂ) * ζ ^ 29 - ((38 / 4345) : ℂ) * ζ ^ 30 + ((103 / 3476) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1333 / 17380) : ℂ) - ((1713 / 17380) : ℂ) * ζ ^ 1 + ((734 / 4345) : ℂ) * ζ ^ 2 + ((109 / 790) : ℂ) * ζ ^ 3 + ((2477 / 17380) : ℂ) * ζ ^ 4 - ((233 / 8690) : ℂ) * ζ ^ 5 + ((3 / 790) : ℂ) * ζ ^ 6 - ((2213 / 17380) : ℂ) * ζ ^ 7 - ((4077 / 17380) : ℂ) * ζ ^ 8 - ((173 / 17380) : ℂ) * ζ ^ 9 - ((567 / 8690) : ℂ) * ζ ^ 10 + ((919 / 8690) : ℂ) * ζ ^ 11 + ((463 / 8690) : ℂ) * ζ ^ 12 + ((511 / 4345) : ℂ) * ζ ^ 13 + ((22 / 395) : ℂ) * ζ ^ 14 - ((508 / 4345) : ℂ) * ζ ^ 15 - ((247 / 4345) : ℂ) * ζ ^ 16 - ((387 / 4345) : ℂ) * ζ ^ 17 - ((2967 / 17380) : ℂ) * ζ ^ 18 - ((247 / 17380) : ℂ) * ζ ^ 19 - ((63 / 3476) : ℂ) * ζ ^ 20 + ((243 / 4345) : ℂ) * ζ ^ 21 + ((1121 / 17380) : ℂ) * ζ ^ 22 + ((2539 / 17380) : ℂ) * ζ ^ 23 + ((60 / 869) : ℂ) * ζ ^ 24 - ((773 / 17380) : ℂ) * ζ ^ 25 - ((679 / 17380) : ℂ) * ζ ^ 26 - ((279 / 17380) : ℂ) * ζ ^ 27 + ((1223 / 17380) : ℂ) * ζ ^ 28 - ((155 / 3476) : ℂ) * ζ ^ 29 - ((123 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_4_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 4 =
      (((641 / 3476) : ℂ) - ((1229 / 17380) : ℂ) * ζ ^ 1 + ((149 / 4345) : ℂ) * ζ ^ 2 - ((11 / 1580) : ℂ) * ζ ^ 3 + ((2393 / 17380) : ℂ) * ζ ^ 5 - ((1231 / 17380) : ℂ) * ζ ^ 6 - ((853 / 3476) : ℂ) * ζ ^ 8 + ((559 / 8690) : ℂ) * ζ ^ 9 - ((147 / 1580) : ℂ) * ζ ^ 11 - ((65 / 3476) : ℂ) * ζ ^ 12 + ((1229 / 17380) : ℂ) * ζ ^ 13 - ((1 / 5) : ℂ) * ζ ^ 15 + ((1229 / 17380) : ℂ) * ζ ^ 17 + ((268 / 4345) : ℂ) * ζ ^ 18 + ((483 / 17380) : ℂ) * ζ ^ 21 - ((149 / 4345) : ℂ) * ζ ^ 22 + ((177 / 3476) : ℂ) * ζ ^ 24 - ((1811 / 8690) : ℂ) * ζ ^ 25 + ((223 / 1580) : ℂ) * ζ ^ 27 + ((853 / 3476) : ℂ) * ζ ^ 28 - ((1229 / 17380) : ℂ) * ζ ^ 29 - ((2873 / 17380) : ℂ) * ζ ^ 30 + ((147 / 1580) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((3361 / 17380) : ℂ) + ((1601 / 17380) : ℂ) * ζ ^ 1 + ((31 / 3476) : ℂ) * ζ ^ 2 + ((659 / 8690) : ℂ) * ζ ^ 3 + ((3391 / 17380) : ℂ) * ζ ^ 4 - ((4351 / 17380) : ℂ) * ζ ^ 5 + ((359 / 4345) : ℂ) * ζ ^ 6 - ((115 / 3476) : ℂ) * ζ ^ 7 + ((633 / 17380) : ℂ) * ζ ^ 8 + ((124 / 4345) : ℂ) * ζ ^ 9 + ((519 / 8690) : ℂ) * ζ ^ 10 + ((2801 / 8690) : ℂ) * ζ ^ 11 - ((7 / 395) : ℂ) * ζ ^ 12 - ((37 / 790) : ℂ) * ζ ^ 13 + ((703 / 17380) : ℂ) * ζ ^ 14 + ((903 / 17380) : ℂ) * ζ ^ 15 - ((77 / 1580) : ℂ) * ζ ^ 16 - ((2721 / 17380) : ℂ) * ζ ^ 17 - ((53 / 790) : ℂ) * ζ ^ 18 - ((221 / 8690) : ℂ) * ζ ^ 19 - ((1901 / 8690) : ℂ) * ζ ^ 20 - ((167 / 8690) : ℂ) * ζ ^ 21 + ((153 / 17380) : ℂ) * ζ ^ 22 + ((973 / 17380) : ℂ) * ζ ^ 23 - ((51 / 3476) : ℂ) * ζ ^ 24 + ((47 / 17380) : ℂ) * ζ ^ 25 + ((1167 / 17380) : ℂ) * ζ ^ 26 - ((137 / 3476) : ℂ) * ζ ^ 27 - ((6 / 395) : ℂ) * ζ ^ 29 + ((159 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_4_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 4 =
      (((3117 / 17380) : ℂ) + ((527 / 17380) : ℂ) * ζ ^ 1 - ((523 / 4345) : ℂ) * ζ ^ 2 + ((697 / 4345) : ℂ) * ζ ^ 3 - ((507 / 8690) : ℂ) * ζ ^ 5 - ((652 / 4345) : ℂ) * ζ ^ 6 + ((2379 / 17380) : ℂ) * ζ ^ 8 - ((876 / 4345) : ℂ) * ζ ^ 9 + ((523 / 8690) : ℂ) * ζ ^ 11 + ((357 / 17380) : ℂ) * ζ ^ 12 - ((527 / 17380) : ℂ) * ζ ^ 13 + ((823 / 17380) : ℂ) * ζ ^ 15 - ((527 / 17380) : ℂ) * ζ ^ 17 - ((136 / 4345) : ℂ) * ζ ^ 18 - ((1637 / 8690) : ℂ) * ζ ^ 21 + ((523 / 4345) : ℂ) * ζ ^ 22 + ((1039 / 17380) : ℂ) * ζ ^ 24 + ((1541 / 17380) : ℂ) * ζ ^ 25 + ((1131 / 17380) : ℂ) * ζ ^ 27 - ((2379 / 17380) : ℂ) * ζ ^ 28 + ((527 / 17380) : ℂ) * ζ ^ 29 + ((353 / 8690) : ℂ) * ζ ^ 30 - ((523 / 8690) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((3117 / 17380) : ℂ) - ((74 / 4345) : ℂ) * ζ ^ 1 + ((1729 / 17380) : ℂ) * ζ ^ 2 - ((4471 / 17380) : ℂ) * ζ ^ 3 + ((3027 / 8690) : ℂ) * ζ ^ 4 - ((157 / 1738) : ℂ) * ζ ^ 5 + ((873 / 8690) : ℂ) * ζ ^ 6 + ((1033 / 17380) : ℂ) * ζ ^ 7 - ((19 / 79) : ℂ) * ζ ^ 8 + ((1403 / 8690) : ℂ) * ζ ^ 9 - ((2703 / 17380) : ℂ) * ζ ^ 10 - ((521 / 17380) : ℂ) * ζ ^ 11 + ((1451 / 17380) : ℂ) * ζ ^ 12 - ((159 / 4345) : ℂ) * ζ ^ 13 + ((1237 / 8690) : ℂ) * ζ ^ 14 - ((987 / 17380) : ℂ) * ζ ^ 15 + ((107 / 8690) : ℂ) * ζ ^ 16 + ((2353 / 17380) : ℂ) * ζ ^ 17 - ((1929 / 17380) : ℂ) * ζ ^ 18 + ((223 / 3476) : ℂ) * ζ ^ 19 - ((203 / 3476) : ℂ) * ζ ^ 20 + ((909 / 17380) : ℂ) * ζ ^ 21 - ((289 / 3476) : ℂ) * ζ ^ 22 + ((291 / 17380) : ℂ) * ζ ^ 23 - ((29 / 1738) : ℂ) * ζ ^ 24 - ((67 / 3476) : ℂ) * ζ ^ 25 + ((487 / 8690) : ℂ) * ζ ^ 26 - ((441 / 8690) : ℂ) * ζ ^ 27 + ((309 / 8690) : ℂ) * ζ ^ 28 - ((12 / 869) : ℂ) * ζ ^ 29 + ((27 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_4_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 4 =
      (-((63 / 790) : ℂ) - ((87 / 1580) : ℂ) * ζ ^ 1 + ((137 / 395) : ℂ) * ζ ^ 2 - ((7 / 79) : ℂ) * ζ ^ 3 - ((83 / 790) : ℂ) * ζ ^ 5 + ((211 / 790) : ℂ) * ζ ^ 6 - ((211 / 790) : ℂ) * ζ ^ 8 + ((81 / 395) : ℂ) * ζ ^ 9 + ((7 / 158) : ℂ) * ζ ^ 11 - ((171 / 1580) : ℂ) * ζ ^ 12 + ((87 / 1580) : ℂ) * ζ ^ 13 - ((45 / 158) : ℂ) * ζ ^ 15 + ((87 / 1580) : ℂ) * ζ ^ 17 - ((239 / 1580) : ℂ) * ζ ^ 18 + ((319 / 1580) : ℂ) * ζ ^ 21 - ((137 / 395) : ℂ) * ζ ^ 22 + ((183 / 1580) : ℂ) * ζ ^ 24 + ((1 / 20) : ℂ) * ζ ^ 25 - ((39 / 316) : ℂ) * ζ ^ 27 + ((211 / 790) : ℂ) * ζ ^ 28 - ((87 / 1580) : ℂ) * ζ ^ 29 + ((251 / 1580) : ℂ) * ζ ^ 30 - ((7 / 158) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((119 / 790) : ℂ) + ((169 / 1580) : ℂ) * ζ ^ 1 - ((399 / 1580) : ℂ) * ζ ^ 2 + ((257 / 1580) : ℂ) * ζ ^ 3 - ((127 / 790) : ℂ) * ζ ^ 4 + ((7 / 790) : ℂ) * ζ ^ 5 + ((41 / 790) : ℂ) * ζ ^ 6 - ((89 / 1580) : ℂ) * ζ ^ 7 + ((132 / 395) : ℂ) * ζ ^ 8 - ((413 / 1580) : ℂ) * ζ ^ 9 - ((163 / 1580) : ℂ) * ζ ^ 10 - ((41 / 1580) : ℂ) * ζ ^ 11 - ((45 / 316) : ℂ) * ζ ^ 12 + ((69 / 395) : ℂ) * ζ ^ 13 - ((30 / 79) : ℂ) * ζ ^ 14 + ((277 / 790) : ℂ) * ζ ^ 15 + ((67 / 1580) : ℂ) * ζ ^ 16 - ((121 / 1580) : ℂ) * ζ ^ 17 + ((9 / 395) : ℂ) * ζ ^ 18 - ((411 / 1580) : ℂ) * ζ ^ 19 + ((431 / 1580) : ℂ) * ζ ^ 20 - ((199 / 1580) : ℂ) * ζ ^ 21 + ((33 / 1580) : ℂ) * ζ ^ 22 + ((223 / 1580) : ℂ) * ζ ^ 23 - ((1 / 79) : ℂ) * ζ ^ 24 + ((48 / 395) : ℂ) * ζ ^ 25 - ((19 / 158) : ℂ) * ζ ^ 26 + ((5 / 316) : ℂ) * ζ ^ 27 + ((51 / 1580) : ℂ) * ζ ^ 28 - ((13 / 395) : ℂ) * ζ ^ 29 + ((33 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_4_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 4 =
      (-((65 / 3476) : ℂ) + ((119 / 17380) : ℂ) * ζ ^ 1 + ((2899 / 17380) : ℂ) * ζ ^ 2 + ((1193 / 17380) : ℂ) * ζ ^ 3 + ((318 / 4345) : ℂ) * ζ ^ 5 + ((2401 / 17380) : ℂ) * ζ ^ 6 - ((23 / 1738) : ℂ) * ζ ^ 8 - ((573 / 17380) : ℂ) * ζ ^ 9 - ((659 / 17380) : ℂ) * ζ ^ 11 - ((153 / 869) : ℂ) * ζ ^ 12 - ((119 / 17380) : ℂ) * ζ ^ 13 + ((713 / 17380) : ℂ) * ζ ^ 15 - ((119 / 17380) : ℂ) * ζ ^ 17 - ((263 / 4345) : ℂ) * ζ ^ 18 - ((689 / 8690) : ℂ) * ζ ^ 21 - ((2899 / 17380) : ℂ) * ζ ^ 22 + ((100 / 869) : ℂ) * ζ ^ 24 - ((1153 / 17380) : ℂ) * ζ ^ 25 + ((593 / 8690) : ℂ) * ζ ^ 27 + ((23 / 1738) : ℂ) * ζ ^ 28 + ((119 / 17380) : ℂ) * ζ ^ 29 + ((2623 / 17380) : ℂ) * ζ ^ 30 + ((659 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((1 / 55) : ℂ) + ((9 / 869) : ℂ) * ζ ^ 1 - ((1371 / 8690) : ℂ) * ζ ^ 2 - ((1121 / 8690) : ℂ) * ζ ^ 3 + ((96 / 4345) : ℂ) * ζ ^ 4 + ((39 / 4345) : ℂ) * ζ ^ 5 - ((661 / 17380) : ℂ) * ζ ^ 6 + ((593 / 8690) : ℂ) * ζ ^ 7 + ((178 / 4345) : ℂ) * ζ ^ 8 + ((169 / 1580) : ℂ) * ζ ^ 9 + ((653 / 3476) : ℂ) * ζ ^ 10 - ((2 / 869) : ℂ) * ζ ^ 11 + ((21 / 869) : ℂ) * ζ ^ 12 - ((557 / 17380) : ℂ) * ζ ^ 13 - ((83 / 869) : ℂ) * ζ ^ 14 - ((817 / 8690) : ℂ) * ζ ^ 15 - ((2477 / 17380) : ℂ) * ζ ^ 16 - ((109 / 3476) : ℂ) * ζ ^ 17 + ((53 / 4345) : ℂ) * ζ ^ 18 + ((267 / 1738) : ℂ) * ζ ^ 19 + ((1539 / 8690) : ℂ) * ζ ^ 20 + ((2153 / 17380) : ℂ) * ζ ^ 21 + ((1201 / 17380) : ℂ) * ζ ^ 22 - ((181 / 1580) : ℂ) * ζ ^ 23 - ((1011 / 8690) : ℂ) * ζ ^ 24 - ((417 / 3476) : ℂ) * ζ ^ 25 - ((587 / 17380) : ℂ) * ζ ^ 26 + ((299 / 8690) : ℂ) * ζ ^ 27 + ((219 / 8690) : ℂ) * ζ ^ 28 + ((197 / 8690) : ℂ) * ζ ^ 29 - ((119 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_4_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 4 =
      (-((1 / 11) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 1 - ((7 / 44) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 3 + ((3 / 44) : ℂ) * ζ ^ 5 - ((9 / 44) : ℂ) * ζ ^ 6 + ((2 / 11) : ℂ) * ζ ^ 8 + ((9 / 44) : ℂ) * ζ ^ 9 - ((7 / 44) : ℂ) * ζ ^ 11 + ((3 / 22) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 13 + ((3 / 44) : ℂ) * ζ ^ 15 + ((1 / 11) : ℂ) * ζ ^ 17 - ((1 / 44) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 21 + ((7 / 44) : ℂ) * ζ ^ 22 - ((5 / 44) : ℂ) * ζ ^ 24 - ((7 / 44) : ℂ) * ζ ^ 25 + ((3 / 44) : ℂ) * ζ ^ 27 - ((2 / 11) : ℂ) * ζ ^ 28 - ((1 / 11) : ℂ) * ζ ^ 29 - ((1 / 11) : ℂ) * ζ ^ 30 + ((7 / 44) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_4_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 4 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_4_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 4 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_5_4 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        5 4 =
      alternatingSixAmbientRow18TransformedGeneratorA
        5 4 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_5_4_0,
      row18_transformedGeneratorA_term_5_4_1,
      row18_transformedGeneratorA_term_5_4_2,
      row18_transformedGeneratorA_term_5_4_3,
      row18_transformedGeneratorA_term_5_4_4,
      row18_transformedGeneratorA_term_5_4_5,
      row18_transformedGeneratorA_term_5_4_6,
      row18_transformedGeneratorA_term_5_4_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_5_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 5 =
      (((1429 / 17380) : ℂ) - ((47 / 3476) : ℂ) * ζ ^ 1 - ((2007 / 17380) : ℂ) * ζ ^ 2 - ((68 / 869) : ℂ) * ζ ^ 3 - ((259 / 3476) : ℂ) * ζ ^ 5 + ((1147 / 17380) : ℂ) * ζ ^ 6 + ((13 / 17380) : ℂ) * ζ ^ 8 - ((9 / 1738) : ℂ) * ζ ^ 9 + ((665 / 3476) : ℂ) * ζ ^ 11 - ((2501 / 17380) : ℂ) * ζ ^ 12 + ((47 / 3476) : ℂ) * ζ ^ 13 + ((25 / 869) : ℂ) * ζ ^ 15 + ((47 / 3476) : ℂ) * ζ ^ 17 + ((1993 / 8690) : ℂ) * ζ ^ 18 + ((303 / 1738) : ℂ) * ζ ^ 21 + ((2007 / 17380) : ℂ) * ζ ^ 22 + ((183 / 17380) : ℂ) * ζ ^ 24 + ((53 / 869) : ℂ) * ζ ^ 25 - ((439 / 3476) : ℂ) * ζ ^ 27 - ((13 / 17380) : ℂ) * ζ ^ 28 - ((47 / 3476) : ℂ) * ζ ^ 29 - ((2349 / 17380) : ℂ) * ζ ^ 30 - ((665 / 3476) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((257 / 3476) : ℂ) + ((513 / 17380) : ℂ) * ζ ^ 1 + ((1519 / 17380) : ℂ) * ζ ^ 2 + ((372 / 4345) : ℂ) * ζ ^ 3 + ((2509 / 17380) : ℂ) * ζ ^ 4 - ((347 / 17380) : ℂ) * ζ ^ 5 - ((853 / 3476) : ℂ) * ζ ^ 6 - ((377 / 4345) : ℂ) * ζ ^ 7 - ((1291 / 8690) : ℂ) * ζ ^ 8 - ((43 / 316) : ℂ) * ζ ^ 9 + ((2579 / 17380) : ℂ) * ζ ^ 10 - ((189 / 17380) : ℂ) * ζ ^ 11 + ((87 / 1738) : ℂ) * ζ ^ 12 + ((1077 / 8690) : ℂ) * ζ ^ 13 + ((288 / 4345) : ℂ) * ζ ^ 14 + ((501 / 3476) : ℂ) * ζ ^ 15 - ((2217 / 17380) : ℂ) * ζ ^ 16 - ((199 / 3476) : ℂ) * ζ ^ 17 - ((89 / 790) : ℂ) * ζ ^ 18 - ((89 / 3476) : ℂ) * ζ ^ 19 - ((879 / 17380) : ℂ) * ζ ^ 20 - ((1709 / 17380) : ℂ) * ζ ^ 21 + ((413 / 1738) : ℂ) * ζ ^ 22 + ((513 / 8690) : ℂ) * ζ ^ 23 - ((271 / 17380) : ℂ) * ζ ^ 24 + ((311 / 4345) : ℂ) * ζ ^ 25 - ((1717 / 17380) : ℂ) * ζ ^ 26 + ((9 / 8690) : ℂ) * ζ ^ 27 + ((298 / 4345) : ℂ) * ζ ^ 28 - ((713 / 17380) : ℂ) * ζ ^ 29 - ((111 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_5_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 5 =
      (-((2199 / 17380) : ℂ) + ((1192 / 4345) : ℂ) * ζ ^ 1 - ((181 / 1580) : ℂ) * ζ ^ 2 + ((5613 / 17380) : ℂ) * ζ ^ 3 + ((1649 / 17380) : ℂ) * ζ ^ 5 + ((21 / 1580) : ℂ) * ζ ^ 6 + ((588 / 4345) : ℂ) * ζ ^ 8 - ((559 / 4345) : ℂ) * ζ ^ 9 - ((5979 / 17380) : ℂ) * ζ ^ 11 - ((846 / 4345) : ℂ) * ζ ^ 12 - ((1192 / 4345) : ℂ) * ζ ^ 13 - ((1831 / 8690) : ℂ) * ζ ^ 15 - ((1192 / 4345) : ℂ) * ζ ^ 17 + ((1 / 10) : ℂ) * ζ ^ 18 - ((764 / 4345) : ℂ) * ζ ^ 21 + ((181 / 1580) : ℂ) * ζ ^ 22 - ((9 / 8690) : ℂ) * ζ ^ 24 + ((3119 / 17380) : ℂ) * ζ ^ 25 + ((1733 / 8690) : ℂ) * ζ ^ 27 - ((588 / 4345) : ℂ) * ζ ^ 28 + ((1192 / 4345) : ℂ) * ζ ^ 29 + ((293 / 1580) : ℂ) * ζ ^ 30 + ((5979 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((97 / 790) : ℂ) - ((1189 / 4345) : ℂ) * ζ ^ 1 + ((118 / 869) : ℂ) * ζ ^ 2 - ((1487 / 8690) : ℂ) * ζ ^ 3 - ((299 / 3476) : ℂ) * ζ ^ 4 + ((207 / 3476) : ℂ) * ζ ^ 5 - ((597 / 1580) : ℂ) * ζ ^ 6 + ((1329 / 8690) : ℂ) * ζ ^ 7 - ((333 / 1738) : ℂ) * ζ ^ 8 - ((283 / 8690) : ℂ) * ζ ^ 9 + ((3923 / 17380) : ℂ) * ζ ^ 10 - ((94 / 395) : ℂ) * ζ ^ 11 + ((1081 / 3476) : ℂ) * ζ ^ 12 + ((91 / 395) : ℂ) * ζ ^ 13 + ((2367 / 8690) : ℂ) * ζ ^ 14 + ((107 / 869) : ℂ) * ζ ^ 15 - ((1149 / 17380) : ℂ) * ζ ^ 16 + ((1687 / 17380) : ℂ) * ζ ^ 17 - ((1201 / 8690) : ℂ) * ζ ^ 18 - ((3491 / 17380) : ℂ) * ζ ^ 19 + ((2111 / 17380) : ℂ) * ζ ^ 20 + ((343 / 3476) : ℂ) * ζ ^ 21 - ((1499 / 8690) : ℂ) * ζ ^ 22 - ((2633 / 8690) : ℂ) * ζ ^ 23 - ((27 / 869) : ℂ) * ζ ^ 24 - ((621 / 17380) : ℂ) * ζ ^ 25 - ((1009 / 3476) : ℂ) * ζ ^ 26 + ((123 / 3476) : ℂ) * ζ ^ 27 - ((482 / 4345) : ℂ) * ζ ^ 28 - ((2709 / 17380) : ℂ) * ζ ^ 29 - ((954 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_5_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 5 =
      (((213 / 1580) : ℂ) - ((1277 / 8690) : ℂ) * ζ ^ 1 + ((2839 / 17380) : ℂ) * ζ ^ 2 + ((23 / 3476) : ℂ) * ζ ^ 3 - ((5647 / 17380) : ℂ) * ζ ^ 5 + ((4021 / 17380) : ℂ) * ζ ^ 6 - ((96 / 395) : ℂ) * ζ ^ 8 - ((278 / 4345) : ℂ) * ζ ^ 9 + ((170 / 869) : ℂ) * ζ ^ 11 - ((377 / 1580) : ℂ) * ζ ^ 12 + ((1277 / 8690) : ℂ) * ζ ^ 13 + ((100 / 869) : ℂ) * ζ ^ 15 + ((1277 / 8690) : ℂ) * ζ ^ 17 - ((1807 / 17380) : ℂ) * ζ ^ 18 + ((4683 / 17380) : ℂ) * ζ ^ 21 - ((2839 / 17380) : ℂ) * ζ ^ 22 + ((131 / 1580) : ℂ) * ζ ^ 24 + ((3093 / 17380) : ℂ) * ζ ^ 25 - ((579 / 3476) : ℂ) * ζ ^ 27 + ((96 / 395) : ℂ) * ζ ^ 28 - ((1277 / 8690) : ℂ) * ζ ^ 29 + ((819 / 8690) : ℂ) * ζ ^ 30 - ((170 / 869) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((2693 / 17380) : ℂ) + ((2789 / 17380) : ℂ) * ζ ^ 1 + ((521 / 17380) : ℂ) * ζ ^ 2 - ((2177 / 17380) : ℂ) * ζ ^ 3 + ((98 / 4345) : ℂ) * ζ ^ 4 + ((1066 / 4345) : ℂ) * ζ ^ 5 - ((683 / 8690) : ℂ) * ζ ^ 6 + ((537 / 4345) : ℂ) * ζ ^ 7 - ((1289 / 4345) : ℂ) * ζ ^ 8 - ((2489 / 17380) : ℂ) * ζ ^ 9 + ((207 / 17380) : ℂ) * ζ ^ 10 - ((109 / 1738) : ℂ) * ζ ^ 11 + ((45 / 1738) : ℂ) * ζ ^ 12 - ((1753 / 8690) : ℂ) * ζ ^ 13 + ((555 / 3476) : ℂ) * ζ ^ 14 + ((2887 / 17380) : ℂ) * ζ ^ 15 - ((9 / 79) : ℂ) * ζ ^ 16 + ((1369 / 8690) : ℂ) * ζ ^ 17 - ((333 / 4345) : ℂ) * ζ ^ 18 - ((493 / 17380) : ℂ) * ζ ^ 19 + ((695 / 3476) : ℂ) * ζ ^ 20 - ((2383 / 8690) : ℂ) * ζ ^ 21 - ((841 / 8690) : ℂ) * ζ ^ 22 + ((73 / 1738) : ℂ) * ζ ^ 23 + ((1257 / 17380) : ℂ) * ζ ^ 24 - ((1277 / 17380) : ℂ) * ζ ^ 25 + ((1151 / 17380) : ℂ) * ζ ^ 26 + ((819 / 17380) : ℂ) * ζ ^ 27 + ((133 / 8690) : ℂ) * ζ ^ 28 + ((49 / 790) : ℂ) * ζ ^ 29 - ((153 / 1738) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_5_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 5 =
      (((47 / 1580) : ℂ) - ((3 / 1580) : ℂ) * ζ ^ 1 - ((379 / 1580) : ℂ) * ζ ^ 2 - ((29 / 1580) : ℂ) * ζ ^ 3 + ((59 / 395) : ℂ) * ζ ^ 5 - ((84 / 395) : ℂ) * ζ ^ 6 + ((76 / 395) : ℂ) * ζ ^ 8 + ((61 / 1580) : ℂ) * ζ ^ 9 - ((463 / 1580) : ℂ) * ζ ^ 11 + ((231 / 790) : ℂ) * ζ ^ 12 + ((3 / 1580) : ℂ) * ζ ^ 13 + ((31 / 1580) : ℂ) * ζ ^ 15 + ((3 / 1580) : ℂ) * ζ ^ 17 - ((43 / 1580) : ℂ) * ζ ^ 18 - ((71 / 395) : ℂ) * ζ ^ 21 + ((379 / 1580) : ℂ) * ζ ^ 22 - ((1 / 5) : ℂ) * ζ ^ 24 - ((239 / 1580) : ℂ) * ζ ^ 25 + ((221 / 790) : ℂ) * ζ ^ 27 - ((76 / 395) : ℂ) * ζ ^ 28 - ((3 / 1580) : ℂ) * ζ ^ 29 + ((227 / 1580) : ℂ) * ζ ^ 30 + ((463 / 1580) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((169 / 1580) : ℂ) - ((7 / 395) : ℂ) * ζ ^ 1 + ((55 / 316) : ℂ) * ζ ^ 2 + ((9 / 316) : ℂ) * ζ ^ 3 + ((14 / 79) : ℂ) * ζ ^ 4 + ((3 / 395) : ℂ) * ζ ^ 5 + ((32 / 395) : ℂ) * ζ ^ 6 + ((113 / 1580) : ℂ) * ζ ^ 7 + ((39 / 1580) : ℂ) * ζ ^ 8 + ((143 / 790) : ℂ) * ζ ^ 9 + ((14 / 395) : ℂ) * ζ ^ 10 + ((143 / 316) : ℂ) * ζ ^ 11 - ((413 / 1580) : ℂ) * ζ ^ 12 - ((251 / 1580) : ℂ) * ζ ^ 13 + ((239 / 790) : ℂ) * ζ ^ 14 - ((121 / 316) : ℂ) * ζ ^ 15 + ((39 / 790) : ℂ) * ζ ^ 16 - ((64 / 395) : ℂ) * ζ ^ 17 + ((37 / 158) : ℂ) * ζ ^ 18 + ((29 / 395) : ℂ) * ζ ^ 19 - ((201 / 790) : ℂ) * ζ ^ 20 + ((23 / 790) : ℂ) * ζ ^ 21 - ((417 / 1580) : ℂ) * ζ ^ 22 + ((121 / 1580) : ℂ) * ζ ^ 23 - ((22 / 79) : ℂ) * ζ ^ 24 - ((19 / 158) : ℂ) * ζ ^ 25 + ((493 / 1580) : ℂ) * ζ ^ 26 - ((317 / 1580) : ℂ) * ζ ^ 27 - ((2 / 395) : ℂ) * ζ ^ 28 + ((3 / 316) : ℂ) * ζ ^ 29 - ((261 / 1580) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_5_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 5 =
      (((1201 / 8690) : ℂ) + ((427 / 3476) : ℂ) * ζ ^ 1 + ((727 / 4345) : ℂ) * ζ ^ 2 + ((581 / 17380) : ℂ) * ζ ^ 3 + ((339 / 1738) : ℂ) * ζ ^ 5 + ((1321 / 8690) : ℂ) * ζ ^ 6 - ((1471 / 17380) : ℂ) * ζ ^ 8 - ((25 / 869) : ℂ) * ζ ^ 9 - ((9 / 8690) : ℂ) * ζ ^ 11 - ((839 / 8690) : ℂ) * ζ ^ 12 - ((427 / 3476) : ℂ) * ζ ^ 13 - ((46 / 4345) : ℂ) * ζ ^ 15 - ((427 / 3476) : ℂ) * ζ ^ 17 - ((256 / 4345) : ℂ) * ζ ^ 18 - ((51 / 1738) : ℂ) * ζ ^ 21 - ((727 / 4345) : ℂ) * ζ ^ 22 + ((3349 / 17380) : ℂ) * ζ ^ 24 - ((251 / 3476) : ℂ) * ζ ^ 25 + ((493 / 4345) : ℂ) * ζ ^ 27 + ((1471 / 17380) : ℂ) * ζ ^ 28 + ((427 / 3476) : ℂ) * ζ ^ 29 - ((1 / 4345) : ℂ) * ζ ^ 30 + ((9 / 8690) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((2429 / 17380) : ℂ) - ((1271 / 17380) : ℂ) * ζ ^ 1 - ((1427 / 17380) : ℂ) * ζ ^ 2 - ((181 / 8690) : ℂ) * ζ ^ 3 + ((4709 / 17380) : ℂ) * ζ ^ 4 - ((593 / 8690) : ℂ) * ζ ^ 5 - ((276 / 4345) : ℂ) * ζ ^ 6 + ((655 / 3476) : ℂ) * ζ ^ 7 + ((2261 / 17380) : ℂ) * ζ ^ 8 - ((1 / 316) : ℂ) * ζ ^ 9 + ((267 / 1738) : ℂ) * ζ ^ 10 - ((119 / 4345) : ℂ) * ζ ^ 11 - ((427 / 8690) : ℂ) * ζ ^ 12 + ((3111 / 8690) : ℂ) * ζ ^ 13 - ((4803 / 17380) : ℂ) * ζ ^ 14 - ((2037 / 17380) : ℂ) * ζ ^ 15 + ((831 / 4345) : ℂ) * ζ ^ 16 - ((498 / 4345) : ℂ) * ζ ^ 17 + ((27 / 869) : ℂ) * ζ ^ 18 - ((133 / 4345) : ℂ) * ζ ^ 19 - ((652 / 4345) : ℂ) * ζ ^ 20 + ((223 / 3476) : ℂ) * ζ ^ 21 + ((1349 / 8690) : ℂ) * ζ ^ 22 - ((791 / 17380) : ℂ) * ζ ^ 23 - ((721 / 8690) : ℂ) * ζ ^ 24 + ((807 / 4345) : ℂ) * ζ ^ 25 - ((346 / 4345) : ℂ) * ζ ^ 26 + ((267 / 8690) : ℂ) * ζ ^ 27 - ((78 / 395) : ℂ) * ζ ^ 29 + ((442 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_5_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 5 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_5_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 5 =
      (-((41 / 220) : ℂ) - ((7 / 55) : ℂ) * ζ ^ 1 - ((27 / 220) : ℂ) * ζ ^ 2 - ((19 / 220) : ℂ) * ζ ^ 3 - ((17 / 110) : ℂ) * ζ ^ 5 - ((63 / 220) : ℂ) * ζ ^ 6 + ((19 / 110) : ℂ) * ζ ^ 8 - ((7 / 110) : ℂ) * ζ ^ 9 + ((27 / 220) : ℂ) * ζ ^ 11 + ((89 / 220) : ℂ) * ζ ^ 12 + ((7 / 55) : ℂ) * ζ ^ 13 + ((1 / 220) : ℂ) * ζ ^ 15 + ((7 / 55) : ℂ) * ζ ^ 17 + ((13 / 110) : ℂ) * ζ ^ 18 + ((23 / 110) : ℂ) * ζ ^ 21 + ((27 / 220) : ℂ) * ζ ^ 22 - ((8 / 55) : ℂ) * ζ ^ 24 + ((3 / 110) : ℂ) * ζ ^ 25 - ((43 / 220) : ℂ) * ζ ^ 27 - ((19 / 110) : ℂ) * ζ ^ 28 - ((7 / 55) : ℂ) * ζ ^ 29 - ((39 / 220) : ℂ) * ζ ^ 30 - ((27 / 220) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((41 / 220) : ℂ) - ((7 / 110) : ℂ) * ζ ^ 1 + ((51 / 220) : ℂ) * ζ ^ 2 + ((61 / 220) : ℂ) * ζ ^ 3 + ((12 / 55) : ℂ) * ζ ^ 4 + ((3 / 110) : ℂ) * ζ ^ 5 + ((73 / 220) : ℂ) * ζ ^ 6 + ((6 / 55) : ℂ) * ζ ^ 7 + ((3 / 220) : ℂ) * ζ ^ 8 + ((1 / 55) : ℂ) * ζ ^ 9 - ((6 / 55) : ℂ) * ζ ^ 10 - ((2 / 55) : ℂ) * ζ ^ 11 - ((27 / 55) : ℂ) * ζ ^ 12 + ((39 / 220) : ℂ) * ζ ^ 14 + ((13 / 110) : ℂ) * ζ ^ 15 + ((7 / 110) : ℂ) * ζ ^ 17 - ((5 / 22) : ℂ) * ζ ^ 18 - ((21 / 110) : ℂ) * ζ ^ 19 - ((12 / 55) : ℂ) * ζ ^ 20 - ((9 / 110) : ℂ) * ζ ^ 21 - ((37 / 220) : ℂ) * ζ ^ 22 - ((6 / 55) : ℂ) * ζ ^ 23 - ((9 / 220) : ℂ) * ζ ^ 24 + ((1 / 55) : ℂ) * ζ ^ 25 + ((6 / 55) : ℂ) * ζ ^ 26 + ((6 / 55) : ℂ) * ζ ^ 27 + ((57 / 220) : ℂ) * ζ ^ 28)

private theorem row18_transformedGeneratorA_term_5_5_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 5 =
      (-((27 / 220) : ℂ) - ((4 / 55) : ℂ) * ζ ^ 1 - ((7 / 55) : ℂ) * ζ ^ 2 + ((7 / 110) : ℂ) * ζ ^ 3 + ((3 / 55) : ℂ) * ζ ^ 5 + ((2 / 55) : ℂ) * ζ ^ 6 - ((17 / 110) : ℂ) * ζ ^ 8 - ((2 / 55) : ℂ) * ζ ^ 9 + ((19 / 110) : ℂ) * ζ ^ 11 + ((13 / 220) : ℂ) * ζ ^ 12 + ((4 / 55) : ℂ) * ζ ^ 13 - ((21 / 220) : ℂ) * ζ ^ 15 + ((4 / 55) : ℂ) * ζ ^ 17 + ((29 / 220) : ℂ) * ζ ^ 18 - ((13 / 220) : ℂ) * ζ ^ 21 + ((7 / 55) : ℂ) * ζ ^ 22 - ((9 / 220) : ℂ) * ζ ^ 24 - ((7 / 55) : ℂ) * ζ ^ 25 + ((23 / 220) : ℂ) * ζ ^ 27 + ((17 / 110) : ℂ) * ζ ^ 28 - ((4 / 55) : ℂ) * ζ ^ 29 - ((4 / 55) : ℂ) * ζ ^ 30 - ((19 / 110) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_5_5 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        5 5 =
      alternatingSixAmbientRow18TransformedGeneratorA
        5 5 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_5_5_0,
      row18_transformedGeneratorA_term_5_5_1,
      row18_transformedGeneratorA_term_5_5_2,
      row18_transformedGeneratorA_term_5_5_3,
      row18_transformedGeneratorA_term_5_5_4,
      row18_transformedGeneratorA_term_5_5_5,
      row18_transformedGeneratorA_term_5_5_6,
      row18_transformedGeneratorA_term_5_5_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_6_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 6 =
      (((3359 / 17380) : ℂ) + ((1711 / 17380) : ℂ) * ζ ^ 1 - ((1437 / 8690) : ℂ) * ζ ^ 2 - ((1697 / 17380) : ℂ) * ζ ^ 3 + ((793 / 17380) : ℂ) * ζ ^ 5 - ((161 / 17380) : ℂ) * ζ ^ 6 - ((547 / 17380) : ℂ) * ζ ^ 8 - ((783 / 4345) : ℂ) * ζ ^ 9 + ((2481 / 17380) : ℂ) * ζ ^ 11 - ((469 / 4345) : ℂ) * ζ ^ 12 - ((1711 / 17380) : ℂ) * ζ ^ 13 + ((1809 / 8690) : ℂ) * ζ ^ 15 - ((1711 / 17380) : ℂ) * ζ ^ 17 + ((203 / 4345) : ℂ) * ζ ^ 18 + ((493 / 17380) : ℂ) * ζ ^ 21 + ((1437 / 8690) : ℂ) * ζ ^ 22 + ((973 / 17380) : ℂ) * ζ ^ 24 + ((459 / 8690) : ℂ) * ζ ^ 25 - ((1519 / 17380) : ℂ) * ζ ^ 27 + ((547 / 17380) : ℂ) * ζ ^ 28 + ((1711 / 17380) : ℂ) * ζ ^ 29 - ((277 / 4345) : ℂ) * ζ ^ 30 - ((2481 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((3103 / 17380) : ℂ) - ((1039 / 17380) : ℂ) * ζ ^ 1 + ((1273 / 8690) : ℂ) * ζ ^ 2 + ((1101 / 17380) : ℂ) * ζ ^ 3 + ((611 / 3476) : ℂ) * ζ ^ 4 + ((59 / 8690) : ℂ) * ζ ^ 5 - ((689 / 3476) : ℂ) * ζ ^ 6 - ((177 / 1580) : ℂ) * ζ ^ 7 - ((161 / 1738) : ℂ) * ζ ^ 8 + ((534 / 4345) : ℂ) * ζ ^ 9 + ((151 / 1580) : ℂ) * ζ ^ 10 + ((23 / 790) : ℂ) * ζ ^ 11 + ((393 / 17380) : ℂ) * ζ ^ 12 - ((817 / 17380) : ℂ) * ζ ^ 13 + ((19 / 4345) : ℂ) * ζ ^ 14 + ((57 / 17380) : ℂ) * ζ ^ 15 - ((119 / 4345) : ℂ) * ζ ^ 16 + ((19 / 1580) : ℂ) * ζ ^ 17 - ((34 / 869) : ℂ) * ζ ^ 18 + ((1593 / 17380) : ℂ) * ζ ^ 19 - ((479 / 8690) : ℂ) * ζ ^ 20 - ((263 / 3476) : ℂ) * ζ ^ 21 + ((15 / 869) : ℂ) * ζ ^ 22 + ((1007 / 17380) : ℂ) * ζ ^ 23 + ((57 / 8690) : ℂ) * ζ ^ 24 + ((38 / 4345) : ℂ) * ζ ^ 25 - ((23 / 3476) : ℂ) * ζ ^ 26 - ((181 / 4345) : ℂ) * ζ ^ 27 + ((843 / 17380) : ℂ) * ζ ^ 28 - ((211 / 17380) : ℂ) * ζ ^ 29 - ((51 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_6_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 6 =
      (-((6 / 395) : ℂ) + ((109 / 8690) : ℂ) * ζ ^ 1 + ((991 / 8690) : ℂ) * ζ ^ 2 + ((603 / 8690) : ℂ) * ζ ^ 3 - ((1883 / 8690) : ℂ) * ζ ^ 5 + ((809 / 8690) : ℂ) * ζ ^ 6 + ((137 / 1580) : ℂ) * ζ ^ 8 - ((523 / 8690) : ℂ) * ζ ^ 9 - ((2203 / 17380) : ℂ) * ζ ^ 11 + ((49 / 395) : ℂ) * ζ ^ 12 - ((109 / 8690) : ℂ) * ζ ^ 13 - ((987 / 8690) : ℂ) * ζ ^ 15 - ((109 / 8690) : ℂ) * ζ ^ 17 + ((2359 / 17380) : ℂ) * ζ ^ 18 - ((559 / 4345) : ℂ) * ζ ^ 21 - ((991 / 8690) : ℂ) * ζ ^ 22 + ((8 / 395) : ℂ) * ζ ^ 24 + ((996 / 4345) : ℂ) * ζ ^ 25 + ((787 / 17380) : ℂ) * ζ ^ 27 - ((137 / 1580) : ℂ) * ζ ^ 28 + ((109 / 8690) : ℂ) * ζ ^ 29 - ((2851 / 17380) : ℂ) * ζ ^ 30 + ((2203 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((27 / 4345) : ℂ) - ((131 / 8690) : ℂ) * ζ ^ 1 - ((109 / 17380) : ℂ) * ζ ^ 2 + ((491 / 3476) : ℂ) * ζ ^ 3 + ((62 / 4345) : ℂ) * ζ ^ 4 - ((38 / 4345) : ℂ) * ζ ^ 5 - ((2437 / 8690) : ℂ) * ζ ^ 6 - ((149 / 8690) : ℂ) * ζ ^ 7 + ((19 / 4345) : ℂ) * ζ ^ 8 + ((2851 / 17380) : ℂ) * ζ ^ 9 + ((1104 / 4345) : ℂ) * ζ ^ 10 + ((1227 / 17380) : ℂ) * ζ ^ 11 - ((4863 / 17380) : ℂ) * ζ ^ 12 - ((2099 / 17380) : ℂ) * ζ ^ 13 - ((2637 / 17380) : ℂ) * ζ ^ 14 + ((673 / 8690) : ℂ) * ζ ^ 15 + ((723 / 4345) : ℂ) * ζ ^ 16 + ((3363 / 17380) : ℂ) * ζ ^ 17 - ((111 / 869) : ℂ) * ζ ^ 18 - ((3293 / 17380) : ℂ) * ζ ^ 19 - ((71 / 1580) : ℂ) * ζ ^ 20 + ((327 / 1738) : ℂ) * ζ ^ 21 + ((281 / 8690) : ℂ) * ζ ^ 22 + ((18 / 395) : ℂ) * ζ ^ 23 - ((238 / 4345) : ℂ) * ζ ^ 24 - ((1911 / 17380) : ℂ) * ζ ^ 25 - ((2179 / 17380) : ℂ) * ζ ^ 26 + ((1099 / 17380) : ℂ) * ζ ^ 27 + ((47 / 395) : ℂ) * ζ ^ 28 + ((159 / 4345) : ℂ) * ζ ^ 29)

private theorem row18_transformedGeneratorA_term_5_6_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 6 =
      (((17 / 4345) : ℂ) - ((168 / 4345) : ℂ) * ζ ^ 1 - ((322 / 4345) : ℂ) * ζ ^ 2 - ((559 / 8690) : ℂ) * ζ ^ 3 + ((896 / 4345) : ℂ) * ζ ^ 5 - ((238 / 4345) : ℂ) * ζ ^ 6 - ((1046 / 4345) : ℂ) * ζ ^ 8 - ((171 / 17380) : ℂ) * ζ ^ 9 + ((4689 / 17380) : ℂ) * ζ ^ 11 - ((3787 / 17380) : ℂ) * ζ ^ 12 + ((168 / 4345) : ℂ) * ζ ^ 13 + ((1017 / 17380) : ℂ) * ζ ^ 15 + ((168 / 4345) : ℂ) * ζ ^ 17 + ((619 / 17380) : ℂ) * ζ ^ 18 - ((1591 / 17380) : ℂ) * ζ ^ 21 + ((322 / 4345) : ℂ) * ζ ^ 22 + ((2351 / 17380) : ℂ) * ζ ^ 24 - ((1064 / 4345) : ℂ) * ζ ^ 25 - ((333 / 8690) : ℂ) * ζ ^ 27 + ((1046 / 4345) : ℂ) * ζ ^ 28 - ((168 / 4345) : ℂ) * ζ ^ 29 + ((2509 / 17380) : ℂ) * ζ ^ 30 - ((4689 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((17 / 4345) : ℂ) + ((196 / 4345) : ℂ) * ζ ^ 1 + ((291 / 3476) : ℂ) * ζ ^ 2 + ((53 / 8690) : ℂ) * ζ ^ 3 - ((773 / 8690) : ℂ) * ζ ^ 4 - ((4519 / 17380) : ℂ) * ζ ^ 5 + ((73 / 4345) : ℂ) * ζ ^ 6 + ((673 / 17380) : ℂ) * ζ ^ 7 + ((2187 / 17380) : ℂ) * ζ ^ 8 + ((2151 / 8690) : ℂ) * ζ ^ 9 - ((211 / 3476) : ℂ) * ζ ^ 10 + ((13 / 110) : ℂ) * ζ ^ 11 - ((20 / 869) : ℂ) * ζ ^ 12 - ((596 / 4345) : ℂ) * ζ ^ 13 - ((1283 / 17380) : ℂ) * ζ ^ 14 + ((39 / 395) : ℂ) * ζ ^ 15 - ((357 / 8690) : ℂ) * ζ ^ 16 + ((2381 / 17380) : ℂ) * ζ ^ 17 - ((1117 / 17380) : ℂ) * ζ ^ 18 - ((119 / 17380) : ℂ) * ζ ^ 19 - ((287 / 17380) : ℂ) * ζ ^ 20 + ((849 / 8690) : ℂ) * ζ ^ 21 - ((53 / 1738) : ℂ) * ζ ^ 22 + ((23 / 3476) : ℂ) * ζ ^ 23 + ((197 / 4345) : ℂ) * ζ ^ 24 - ((123 / 4345) : ℂ) * ζ ^ 25 - ((35 / 1738) : ℂ) * ζ ^ 26 - ((797 / 8690) : ℂ) * ζ ^ 27 + ((18 / 4345) : ℂ) * ζ ^ 28 + ((12 / 4345) : ℂ) * ζ ^ 29 + ((189 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_6_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 6 =
      (((91 / 395) : ℂ) + ((311 / 1580) : ℂ) * ζ ^ 1 + ((117 / 790) : ℂ) * ζ ^ 2 - ((41 / 1580) : ℂ) * ζ ^ 3 + ((53 / 1580) : ℂ) * ζ ^ 5 + ((69 / 395) : ℂ) * ζ ^ 6 - ((207 / 1580) : ℂ) * ζ ^ 8 - ((367 / 1580) : ℂ) * ζ ^ 9 + ((43 / 1580) : ℂ) * ζ ^ 11 + ((129 / 1580) : ℂ) * ζ ^ 12 - ((311 / 1580) : ℂ) * ζ ^ 13 - ((104 / 395) : ℂ) * ζ ^ 15 - ((311 / 1580) : ℂ) * ζ ^ 17 + ((7 / 395) : ℂ) * ζ ^ 18 - ((347 / 1580) : ℂ) * ζ ^ 21 - ((117 / 790) : ℂ) * ζ ^ 22 + ((363 / 1580) : ℂ) * ζ ^ 24 + ((129 / 790) : ℂ) * ζ ^ 25 - ((91 / 790) : ℂ) * ζ ^ 27 + ((207 / 1580) : ℂ) * ζ ^ 28 + ((311 / 1580) : ℂ) * ζ ^ 29 + ((363 / 1580) : ℂ) * ζ ^ 30 - ((43 / 1580) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((63 / 395) : ℂ) - ((231 / 1580) : ℂ) * ζ ^ 1 - ((11 / 790) : ℂ) * ζ ^ 2 + ((89 / 1580) : ℂ) * ζ ^ 3 + ((141 / 790) : ℂ) * ζ ^ 4 - ((9 / 790) : ℂ) * ζ ^ 5 - ((157 / 1580) : ℂ) * ζ ^ 6 - ((9 / 158) : ℂ) * ζ ^ 7 + ((11 / 790) : ℂ) * ζ ^ 8 + ((161 / 1580) : ℂ) * ζ ^ 9 + ((24 / 395) : ℂ) * ζ ^ 10 - ((13 / 79) : ℂ) * ζ ^ 11 - ((319 / 1580) : ℂ) * ζ ^ 12 - ((10 / 79) : ℂ) * ζ ^ 13 - ((7 / 158) : ℂ) * ζ ^ 14 + ((13 / 79) : ℂ) * ζ ^ 15 + ((31 / 158) : ℂ) * ζ ^ 16 + ((111 / 1580) : ℂ) * ζ ^ 17 - ((117 / 790) : ℂ) * ζ ^ 18 - ((211 / 790) : ℂ) * ζ ^ 19 - ((42 / 395) : ℂ) * ζ ^ 20 + ((14 / 79) : ℂ) * ζ ^ 21 + ((53 / 316) : ℂ) * ζ ^ 22 + ((41 / 316) : ℂ) * ζ ^ 23 - ((4 / 79) : ℂ) * ζ ^ 24 - ((48 / 395) : ℂ) * ζ ^ 25 + ((23 / 1580) : ℂ) * ζ ^ 26 + ((39 / 1580) : ℂ) * ζ ^ 27 + ((63 / 1580) : ℂ) * ζ ^ 28 + ((91 / 1580) : ℂ) * ζ ^ 29 - ((3 / 316) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_6_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 6 =
      (-((448 / 4345) : ℂ) + ((1577 / 17380) : ℂ) * ζ ^ 1 + ((1433 / 8690) : ℂ) * ζ ^ 2 + ((71 / 869) : ℂ) * ζ ^ 3 + ((574 / 4345) : ℂ) * ζ ^ 5 + ((1076 / 4345) : ℂ) * ζ ^ 6 - ((1949 / 17380) : ℂ) * ζ ^ 8 + ((39 / 4345) : ℂ) * ζ ^ 9 - ((98 / 869) : ℂ) * ζ ^ 11 - ((801 / 8690) : ℂ) * ζ ^ 12 - ((1577 / 17380) : ℂ) * ζ ^ 13 + ((86 / 869) : ℂ) * ζ ^ 15 - ((1577 / 17380) : ℂ) * ζ ^ 17 - ((362 / 4345) : ℂ) * ζ ^ 18 - ((1181 / 4345) : ℂ) * ζ ^ 21 - ((1433 / 8690) : ℂ) * ζ ^ 22 + ((851 / 17380) : ℂ) * ζ ^ 24 - ((719 / 17380) : ℂ) * ζ ^ 25 + ((355 / 3476) : ℂ) * ζ ^ 27 + ((1949 / 17380) : ℂ) * ζ ^ 28 + ((1577 / 17380) : ℂ) * ζ ^ 29 + ((2007 / 17380) : ℂ) * ζ ^ 30 + ((98 / 869) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((1783 / 17380) : ℂ) - ((251 / 3476) : ℂ) * ζ ^ 1 - ((691 / 3476) : ℂ) * ζ ^ 2 - ((679 / 3476) : ℂ) * ζ ^ 3 - ((1223 / 17380) : ℂ) * ζ ^ 4 - ((93 / 790) : ℂ) * ζ ^ 5 - ((9 / 79) : ℂ) * ζ ^ 6 + ((4 / 395) : ℂ) * ζ ^ 7 + ((1381 / 8690) : ℂ) * ζ ^ 8 + ((3127 / 17380) : ℂ) * ζ ^ 9 + ((966 / 4345) : ℂ) * ζ ^ 10 + ((1323 / 17380) : ℂ) * ζ ^ 11 - ((37 / 3476) : ℂ) * ζ ^ 12 + ((1087 / 17380) : ℂ) * ζ ^ 13 - ((738 / 4345) : ℂ) * ζ ^ 14 - ((3237 / 17380) : ℂ) * ζ ^ 15 - ((1537 / 17380) : ℂ) * ζ ^ 16 - ((279 / 4345) : ℂ) * ζ ^ 17 + ((141 / 1738) : ℂ) * ζ ^ 18 + ((167 / 790) : ℂ) * ζ ^ 19 + ((72 / 395) : ℂ) * ζ ^ 20 + ((3559 / 17380) : ℂ) * ζ ^ 21 + ((408 / 4345) : ℂ) * ζ ^ 22 - ((1987 / 17380) : ℂ) * ζ ^ 23 - ((788 / 4345) : ℂ) * ζ ^ 24 - ((2557 / 17380) : ℂ) * ζ ^ 25 - ((58 / 869) : ℂ) * ζ ^ 26 - ((35 / 869) : ℂ) * ζ ^ 27 + ((217 / 4345) : ℂ) * ζ ^ 28 - ((309 / 8690) : ℂ) * ζ ^ 29 + ((119 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_6_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 6 =
      (-((1 / 11) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 1 - ((7 / 44) : ℂ) * ζ ^ 2 - ((1 / 22) : ℂ) * ζ ^ 3 + ((3 / 44) : ℂ) * ζ ^ 5 - ((9 / 44) : ℂ) * ζ ^ 6 + ((2 / 11) : ℂ) * ζ ^ 8 + ((9 / 44) : ℂ) * ζ ^ 9 - ((7 / 44) : ℂ) * ζ ^ 11 + ((3 / 22) : ℂ) * ζ ^ 12 + ((1 / 11) : ℂ) * ζ ^ 13 + ((3 / 44) : ℂ) * ζ ^ 15 + ((1 / 11) : ℂ) * ζ ^ 17 - ((1 / 44) : ℂ) * ζ ^ 18 + ((5 / 44) : ℂ) * ζ ^ 21 + ((7 / 44) : ℂ) * ζ ^ 22 - ((5 / 44) : ℂ) * ζ ^ 24 - ((7 / 44) : ℂ) * ζ ^ 25 + ((3 / 44) : ℂ) * ζ ^ 27 - ((2 / 11) : ℂ) * ζ ^ 28 - ((1 / 11) : ℂ) * ζ ^ 29 - ((1 / 11) : ℂ) * ζ ^ 30 + ((7 / 44) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_6_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 6 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_6_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 6 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_5_6 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        5 6 =
      alternatingSixAmbientRow18TransformedGeneratorA
        5 6 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_5_6_0,
      row18_transformedGeneratorA_term_5_6_1,
      row18_transformedGeneratorA_term_5_6_2,
      row18_transformedGeneratorA_term_5_6_3,
      row18_transformedGeneratorA_term_5_6_4,
      row18_transformedGeneratorA_term_5_6_5,
      row18_transformedGeneratorA_term_5_6_6,
      row18_transformedGeneratorA_term_5_6_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_7_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 7 =
      (((212 / 4345) : ℂ) + ((186 / 869) : ℂ) * ζ ^ 1 - ((1229 / 17380) : ℂ) * ζ ^ 2 - ((433 / 8690) : ℂ) * ζ ^ 3 + ((229 / 869) : ℂ) * ζ ^ 5 + ((2009 / 17380) : ℂ) * ζ ^ 6 + ((263 / 8690) : ℂ) * ζ ^ 8 - ((101 / 3476) : ℂ) * ζ ^ 9 - ((898 / 4345) : ℂ) * ζ ^ 11 - ((997 / 17380) : ℂ) * ζ ^ 12 - ((186 / 869) : ℂ) * ζ ^ 13 + ((199 / 17380) : ℂ) * ζ ^ 15 - ((186 / 869) : ℂ) * ζ ^ 17 + ((1267 / 17380) : ℂ) * ζ ^ 18 - ((369 / 3476) : ℂ) * ζ ^ 21 + ((1229 / 17380) : ℂ) * ζ ^ 22 - ((3109 / 17380) : ℂ) * ζ ^ 24 - ((43 / 869) : ℂ) * ζ ^ 25 + ((1249 / 8690) : ℂ) * ζ ^ 27 - ((263 / 8690) : ℂ) * ζ ^ 28 + ((186 / 869) : ℂ) * ζ ^ 29 + ((288 / 4345) : ℂ) * ζ ^ 30 + ((898 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((16 / 395) : ℂ) - ((1953 / 8690) : ℂ) * ζ ^ 1 + ((23 / 17380) : ℂ) * ζ ^ 2 + ((1433 / 8690) : ℂ) * ζ ^ 3 + ((249 / 1738) : ℂ) * ζ ^ 4 - ((29 / 316) : ℂ) * ζ ^ 5 - ((71 / 790) : ℂ) * ζ ^ 6 - ((1503 / 17380) : ℂ) * ζ ^ 7 - ((353 / 1580) : ℂ) * ζ ^ 8 - ((391 / 17380) : ℂ) * ζ ^ 9 + ((864 / 4345) : ℂ) * ζ ^ 10 + ((4611 / 17380) : ℂ) * ζ ^ 11 - ((71 / 4345) : ℂ) * ζ ^ 12 + ((71 / 869) : ℂ) * ζ ^ 13 - ((39 / 3476) : ℂ) * ζ ^ 14 - ((1289 / 4345) : ℂ) * ζ ^ 15 - ((2463 / 17380) : ℂ) * ζ ^ 16 - ((153 / 8690) : ℂ) * ζ ^ 17 + ((243 / 3476) : ℂ) * ζ ^ 18 + ((2227 / 17380) : ℂ) * ζ ^ 19 + ((661 / 17380) : ℂ) * ζ ^ 20 - ((541 / 4345) : ℂ) * ζ ^ 21 - ((1381 / 17380) : ℂ) * ζ ^ 22 + ((219 / 4345) : ℂ) * ζ ^ 23 + ((678 / 4345) : ℂ) * ζ ^ 24 + ((1373 / 17380) : ℂ) * ζ ^ 25 - ((261 / 1580) : ℂ) * ζ ^ 26 - ((113 / 3476) : ℂ) * ζ ^ 27 + ((94 / 869) : ℂ) * ζ ^ 28 - ((281 / 8690) : ℂ) * ζ ^ 29 - ((57 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_7_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 7 =
      (((1479 / 4345) : ℂ) - ((1351 / 8690) : ℂ) * ζ ^ 1 - ((61 / 1580) : ℂ) * ζ ^ 2 + ((189 / 790) : ℂ) * ζ ^ 3 - ((3923 / 8690) : ℂ) * ζ ^ 5 - ((267 / 790) : ℂ) * ζ ^ 6 - ((2493 / 17380) : ℂ) * ζ ^ 8 - ((1351 / 17380) : ℂ) * ζ ^ 9 + ((333 / 790) : ℂ) * ζ ^ 11 + ((201 / 17380) : ℂ) * ζ ^ 12 + ((1351 / 8690) : ℂ) * ζ ^ 13 + ((49 / 790) : ℂ) * ζ ^ 15 + ((1351 / 8690) : ℂ) * ζ ^ 17 - ((163 / 395) : ℂ) * ζ ^ 18 + ((3017 / 8690) : ℂ) * ζ ^ 21 + ((61 / 1580) : ℂ) * ζ ^ 22 + ((5217 / 17380) : ℂ) * ζ ^ 24 + ((1286 / 4345) : ℂ) * ζ ^ 25 - ((529 / 1580) : ℂ) * ζ ^ 27 + ((2493 / 17380) : ℂ) * ζ ^ 28 - ((1351 / 8690) : ℂ) * ζ ^ 29 - ((187 / 1580) : ℂ) * ζ ^ 30 - ((333 / 790) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((5981 / 17380) : ℂ) + ((3299 / 17380) : ℂ) * ζ ^ 1 + ((269 / 17380) : ℂ) * ζ ^ 2 - ((7627 / 17380) : ℂ) * ζ ^ 3 + ((914 / 4345) : ℂ) * ζ ^ 4 + ((6987 / 17380) : ℂ) * ζ ^ 5 + ((1863 / 3476) : ℂ) * ζ ^ 6 + ((1479 / 3476) : ℂ) * ζ ^ 7 + ((303 / 4345) : ℂ) * ζ ^ 8 - ((232 / 869) : ℂ) * ζ ^ 9 - ((1624 / 4345) : ℂ) * ζ ^ 10 - ((6893 / 17380) : ℂ) * ζ ^ 11 - ((1891 / 17380) : ℂ) * ζ ^ 12 - ((119 / 8690) : ℂ) * ζ ^ 13 + ((249 / 8690) : ℂ) * ζ ^ 14 + ((514 / 4345) : ℂ) * ζ ^ 15 - ((288 / 4345) : ℂ) * ζ ^ 16 + ((2689 / 17380) : ℂ) * ζ ^ 17 + ((9337 / 17380) : ℂ) * ζ ^ 18 + ((193 / 1738) : ℂ) * ζ ^ 19 - ((2437 / 17380) : ℂ) * ζ ^ 20 - ((7753 / 17380) : ℂ) * ζ ^ 21 - ((3259 / 17380) : ℂ) * ζ ^ 22 - ((164 / 869) : ℂ) * ζ ^ 23 - ((1743 / 17380) : ℂ) * ζ ^ 24 - ((279 / 17380) : ℂ) * ζ ^ 25 + ((169 / 790) : ℂ) * ζ ^ 26 - ((441 / 8690) : ℂ) * ζ ^ 27 + ((68 / 869) : ℂ) * ζ ^ 28 + ((168 / 869) : ℂ) * ζ ^ 29 + ((4929 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_7_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 7 =
      (-((1457 / 8690) : ℂ) - ((96 / 869) : ℂ) * ζ ^ 1 + ((93 / 1580) : ℂ) * ζ ^ 2 - ((360 / 869) : ℂ) * ζ ^ 3 + ((255 / 3476) : ℂ) * ζ ^ 5 - ((13 / 1580) : ℂ) * ζ ^ 6 + ((4201 / 8690) : ℂ) * ζ ^ 8 - ((203 / 3476) : ℂ) * ζ ^ 9 - ((177 / 1738) : ℂ) * ζ ^ 11 + ((3601 / 17380) : ℂ) * ζ ^ 12 + ((96 / 869) : ℂ) * ζ ^ 13 - ((755 / 3476) : ℂ) * ζ ^ 15 + ((96 / 869) : ℂ) * ζ ^ 17 + ((241 / 1580) : ℂ) * ζ ^ 18 + ((405 / 1738) : ℂ) * ζ ^ 21 - ((93 / 1580) : ℂ) * ζ ^ 22 - ((2383 / 17380) : ℂ) * ζ ^ 24 - ((639 / 3476) : ℂ) * ζ ^ 25 + ((34 / 869) : ℂ) * ζ ^ 27 - ((4201 / 8690) : ℂ) * ζ ^ 28 - ((96 / 869) : ℂ) * ζ ^ 29 + ((371 / 1580) : ℂ) * ζ ^ 30 + ((177 / 1738) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((641 / 4345) : ℂ) + ((502 / 4345) : ℂ) * ζ ^ 1 + ((1861 / 17380) : ℂ) * ζ ^ 2 + ((1669 / 4345) : ℂ) * ζ ^ 3 - ((127 / 4345) : ℂ) * ζ ^ 4 - ((703 / 3476) : ℂ) * ζ ^ 5 - ((33 / 1580) : ℂ) * ζ ^ 6 - ((27 / 79) : ℂ) * ζ ^ 7 - ((116 / 4345) : ℂ) * ζ ^ 8 - ((397 / 17380) : ℂ) * ζ ^ 9 - ((3423 / 17380) : ℂ) * ζ ^ 10 + ((481 / 1580) : ℂ) * ζ ^ 11 + ((1833 / 8690) : ℂ) * ζ ^ 12 + ((105 / 3476) : ℂ) * ζ ^ 13 + ((241 / 3476) : ℂ) * ζ ^ 14 - ((1057 / 17380) : ℂ) * ζ ^ 15 - ((106 / 4345) : ℂ) * ζ ^ 16 - ((57 / 790) : ℂ) * ζ ^ 17 - ((589 / 3476) : ℂ) * ζ ^ 18 - ((1583 / 17380) : ℂ) * ζ ^ 19 - ((37 / 869) : ℂ) * ζ ^ 20 - ((177 / 8690) : ℂ) * ζ ^ 21 + ((43 / 17380) : ℂ) * ζ ^ 22 + ((273 / 4345) : ℂ) * ζ ^ 23 + ((289 / 8690) : ℂ) * ζ ^ 24 + ((763 / 8690) : ℂ) * ζ ^ 25 + ((953 / 17380) : ℂ) * ζ ^ 26 - ((58 / 4345) : ℂ) * ζ ^ 27 - ((23 / 4345) : ℂ) * ζ ^ 28 - ((353 / 8690) : ℂ) * ζ ^ 29 - ((36 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_7_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 7 =
      (-((17 / 395) : ℂ) - ((357 / 790) : ℂ) * ζ ^ 1 - ((89 / 395) : ℂ) * ζ ^ 2 - ((347 / 1580) : ℂ) * ζ ^ 3 - ((917 / 1580) : ℂ) * ζ ^ 5 - ((719 / 1580) : ℂ) * ζ ^ 6 + ((377 / 790) : ℂ) * ζ ^ 8 + ((139 / 790) : ℂ) * ζ ^ 9 + ((391 / 1580) : ℂ) * ζ ^ 11 + ((151 / 790) : ℂ) * ζ ^ 12 + ((357 / 790) : ℂ) * ζ ^ 13 + ((82 / 395) : ℂ) * ζ ^ 15 + ((357 / 790) : ℂ) * ζ ^ 17 - ((48 / 395) : ℂ) * ζ ^ 18 + ((579 / 790) : ℂ) * ζ ^ 21 + ((89 / 395) : ℂ) * ζ ^ 22 - ((51 / 1580) : ℂ) * ζ ^ 24 + ((203 / 1580) : ℂ) * ζ ^ 25 - ((389 / 1580) : ℂ) * ζ ^ 27 - ((377 / 790) : ℂ) * ζ ^ 28 - ((357 / 790) : ℂ) * ζ ^ 29 - ((507 / 1580) : ℂ) * ζ ^ 30 - ((391 / 1580) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((27 / 790) : ℂ) + ((663 / 1580) : ℂ) * ζ ^ 1 + ((57 / 790) : ℂ) * ζ ^ 2 + ((173 / 1580) : ℂ) * ζ ^ 3 - ((17 / 316) : ℂ) * ζ ^ 4 + ((21 / 158) : ℂ) * ζ ^ 5 + ((61 / 395) : ℂ) * ζ ^ 6 - ((177 / 1580) : ℂ) * ζ ^ 7 - ((166 / 395) : ℂ) * ζ ^ 8 - ((477 / 1580) : ℂ) * ζ ^ 9 + ((21 / 790) : ℂ) * ζ ^ 10 + ((403 / 1580) : ℂ) * ζ ^ 11 + ((109 / 790) : ℂ) * ζ ^ 12 + ((523 / 1580) : ℂ) * ζ ^ 13 + ((311 / 790) : ℂ) * ζ ^ 14 - ((32 / 395) : ℂ) * ζ ^ 15 - ((95 / 316) : ℂ) * ζ ^ 16 - ((51 / 790) : ℂ) * ζ ^ 17 + ((179 / 790) : ℂ) * ζ ^ 18 - ((39 / 790) : ℂ) * ζ ^ 19 - ((5 / 158) : ℂ) * ζ ^ 20 - ((27 / 158) : ℂ) * ζ ^ 21 - ((17 / 1580) : ℂ) * ζ ^ 22 + ((41 / 395) : ℂ) * ζ ^ 23 - ((17 / 158) : ℂ) * ζ ^ 24 + ((107 / 1580) : ℂ) * ζ ^ 25 - ((77 / 1580) : ℂ) * ζ ^ 26 - ((83 / 395) : ℂ) * ζ ^ 27 - ((43 / 1580) : ℂ) * ζ ^ 28 - ((63 / 790) : ℂ) * ζ ^ 29 - ((18 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_7_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 7 =
      (-((221 / 3476) : ℂ) + ((4989 / 17380) : ℂ) * ζ ^ 1 + ((10697 / 17380) : ℂ) * ζ ^ 2 + ((1884 / 4345) : ℂ) * ζ ^ 3 + ((3581 / 8690) : ℂ) * ζ ^ 5 + ((13813 / 17380) : ℂ) * ζ ^ 6 - ((489 / 869) : ℂ) * ζ ^ 8 - ((1933 / 17380) : ℂ) * ζ ^ 9 - ((8043 / 17380) : ℂ) * ζ ^ 11 - ((717 / 1738) : ℂ) * ζ ^ 12 - ((4989 / 17380) : ℂ) * ζ ^ 13 - ((799 / 17380) : ℂ) * ζ ^ 15 - ((4989 / 17380) : ℂ) * ζ ^ 17 - ((2323 / 8690) : ℂ) * ζ ^ 18 - ((2987 / 4345) : ℂ) * ζ ^ 21 - ((10697 / 17380) : ℂ) * ζ ^ 22 + ((9 / 1738) : ℂ) * ζ ^ 24 - ((2173 / 17380) : ℂ) * ζ ^ 25 + ((11367 / 17380) : ℂ) * ζ ^ 27 + ((489 / 869) : ℂ) * ζ ^ 28 + ((4989 / 17380) : ℂ) * ζ ^ 29 + ((2137 / 8690) : ℂ) * ζ ^ 30 + ((8043 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((49 / 790) : ℂ) - ((2059 / 8690) : ℂ) * ζ ^ 1 - ((4689 / 8690) : ℂ) * ζ ^ 2 - ((9629 / 17380) : ℂ) * ζ ^ 3 - ((2061 / 8690) : ℂ) * ζ ^ 4 - ((982 / 4345) : ℂ) * ζ ^ 5 - ((3577 / 17380) : ℂ) * ζ ^ 6 + ((3363 / 17380) : ℂ) * ζ ^ 7 + ((6683 / 17380) : ℂ) * ζ ^ 8 + ((597 / 1580) : ℂ) * ζ ^ 9 + ((1047 / 3476) : ℂ) * ζ ^ 10 + ((611 / 3476) : ℂ) * ζ ^ 11 + ((409 / 3476) : ℂ) * ζ ^ 12 + ((122 / 4345) : ℂ) * ζ ^ 13 - ((9861 / 17380) : ℂ) * ζ ^ 14 - ((302 / 869) : ℂ) * ζ ^ 15 - ((1251 / 8690) : ℂ) * ζ ^ 16 - ((1079 / 17380) : ℂ) * ζ ^ 17 + ((1641 / 8690) : ℂ) * ζ ^ 18 + ((637 / 4345) : ℂ) * ζ ^ 19 + ((183 / 869) : ℂ) * ζ ^ 20 + ((7127 / 17380) : ℂ) * ζ ^ 21 + ((4889 / 17380) : ℂ) * ζ ^ 22 + ((1679 / 17380) : ℂ) * ζ ^ 23 - ((109 / 8690) : ℂ) * ζ ^ 24 - ((1249 / 8690) : ℂ) * ζ ^ 25 - ((5199 / 17380) : ℂ) * ζ ^ 26 - ((1038 / 4345) : ℂ) * ζ ^ 27 - ((1977 / 8690) : ℂ) * ζ ^ 28 - ((38 / 869) : ℂ) * ζ ^ 29 + ((17 / 110) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_5_7_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 7 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_5_7_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 7 =
      (((6 / 55) : ℂ) + ((6 / 55) : ℂ) * ζ ^ 1 + ((57 / 220) : ℂ) * ζ ^ 2 + ((21 / 110) : ℂ) * ζ ^ 3 - ((9 / 110) : ℂ) * ζ ^ 5 - ((8 / 55) : ℂ) * ζ ^ 6 - ((37 / 220) : ℂ) * ζ ^ 8 - ((43 / 220) : ℂ) * ζ ^ 9 + ((1 / 55) : ℂ) * ζ ^ 11 - ((9 / 55) : ℂ) * ζ ^ 12 - ((6 / 55) : ℂ) * ζ ^ 13 - ((2 / 55) : ℂ) * ζ ^ 15 - ((6 / 55) : ℂ) * ζ ^ 17 - ((3 / 110) : ℂ) * ζ ^ 18 - ((2 / 55) : ℂ) * ζ ^ 21 - ((57 / 220) : ℂ) * ζ ^ 22 + ((63 / 220) : ℂ) * ζ ^ 24 + ((21 / 110) : ℂ) * ζ ^ 25 + ((7 / 110) : ℂ) * ζ ^ 27 + ((37 / 220) : ℂ) * ζ ^ 28 + ((6 / 55) : ℂ) * ζ ^ 29 + ((9 / 220) : ℂ) * ζ ^ 30 - ((1 / 55) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((6 / 55) : ℂ) - ((6 / 55) : ℂ) * ζ ^ 1 - ((57 / 220) : ℂ) * ζ ^ 2)

private theorem row18_transformedGeneratorA_term_5_7_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          5 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 7 =
      (-((27 / 220) : ℂ) - ((4 / 55) : ℂ) * ζ ^ 1 - ((7 / 55) : ℂ) * ζ ^ 2 + ((7 / 110) : ℂ) * ζ ^ 3 + ((3 / 55) : ℂ) * ζ ^ 5 + ((2 / 55) : ℂ) * ζ ^ 6 - ((17 / 110) : ℂ) * ζ ^ 8 - ((2 / 55) : ℂ) * ζ ^ 9 + ((19 / 110) : ℂ) * ζ ^ 11 + ((13 / 220) : ℂ) * ζ ^ 12 + ((4 / 55) : ℂ) * ζ ^ 13 - ((21 / 220) : ℂ) * ζ ^ 15 + ((4 / 55) : ℂ) * ζ ^ 17 + ((29 / 220) : ℂ) * ζ ^ 18 - ((13 / 220) : ℂ) * ζ ^ 21 + ((7 / 55) : ℂ) * ζ ^ 22 - ((9 / 220) : ℂ) * ζ ^ 24 - ((7 / 55) : ℂ) * ζ ^ 25 + ((23 / 220) : ℂ) * ζ ^ 27 + ((17 / 110) : ℂ) * ζ ^ 28 - ((4 / 55) : ℂ) * ζ ^ 29 - ((4 / 55) : ℂ) * ζ ^ 30 - ((19 / 110) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_5_7 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        5 7 =
      alternatingSixAmbientRow18TransformedGeneratorA
        5 7 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_5_7_0,
      row18_transformedGeneratorA_term_5_7_1,
      row18_transformedGeneratorA_term_5_7_2,
      row18_transformedGeneratorA_term_5_7_3,
      row18_transformedGeneratorA_term_5_7_4,
      row18_transformedGeneratorA_term_5_7_5,
      row18_transformedGeneratorA_term_5_7_6,
      row18_transformedGeneratorA_term_5_7_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

/-- The checked transformed-generator equality on output row
5 of ambient row 18. -/
theorem alternatingSixAmbientRow18TransformedGeneratorA_fromIntermediate_row5
    (j : Fin 8) :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        5 j =
      alternatingSixAmbientRow18TransformedGeneratorA
        5 j := by
  fin_cases j
  · exact row18_transformedGeneratorA_5_0
  · exact row18_transformedGeneratorA_5_1
  · exact row18_transformedGeneratorA_5_2
  · exact row18_transformedGeneratorA_5_3
  · exact row18_transformedGeneratorA_5_4
  · exact row18_transformedGeneratorA_5_5
  · exact row18_transformedGeneratorA_5_6
  · exact row18_transformedGeneratorA_5_7


end InductiveMcKay
end McKayConjecture
