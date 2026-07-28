/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18TransformedDataRow2

/-!
# Transformed-generator data for ambient row 18, output row 3

This generated module checks the scalar products in output row 3.
It imports the preceding output-row module to serialize clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private theorem row18_transformedGeneratorA_term_3_0_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 0 =
      (((3359 / 17380) : ℂ) - ((89 / 8690) : ℂ) * ζ ^ 1 + ((1437 / 8690) : ℂ) * ζ ^ 2 - ((1421 / 17380) : ℂ) * ζ ^ 3 + ((1921 / 17380) : ℂ) * ζ ^ 5 + ((161 / 17380) : ℂ) * ζ ^ 6 - ((547 / 17380) : ℂ) * ζ ^ 8 - ((1519 / 17380) : ℂ) * ζ ^ 9 + ((232 / 4345) : ℂ) * ζ ^ 11 - ((469 / 4345) : ℂ) * ζ ^ 12 + ((89 / 8690) : ℂ) * ζ ^ 13 + ((1107 / 8690) : ℂ) * ζ ^ 15 + ((89 / 8690) : ℂ) * ζ ^ 17 - ((203 / 4345) : ℂ) * ζ ^ 18 - ((196 / 4345) : ℂ) * ζ ^ 21 - ((1437 / 8690) : ℂ) * ζ ^ 22 + ((973 / 17380) : ℂ) * ζ ^ 24 - ((2099 / 17380) : ℂ) * ζ ^ 25 - ((783 / 4345) : ℂ) * ζ ^ 27 + ((547 / 17380) : ℂ) * ζ ^ 28 - ((89 / 8690) : ℂ) * ζ ^ 29 + ((277 / 4345) : ℂ) * ζ ^ 30 - ((232 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((3103 / 17380) : ℂ) + ((273 / 8690) : ℂ) * ζ ^ 1 - ((798 / 4345) : ℂ) * ζ ^ 2 + ((245 / 3476) : ℂ) * ζ ^ 3 + ((389 / 3476) : ℂ) * ζ ^ 4 - ((2487 / 17380) : ℂ) * ζ ^ 5 + ((881 / 8690) : ℂ) * ζ ^ 6 - ((54 / 4345) : ℂ) * ζ ^ 7 - ((106 / 869) : ℂ) * ζ ^ 8 + ((786 / 4345) : ℂ) * ζ ^ 9 - ((34 / 395) : ℂ) * ζ ^ 10 + ((136 / 4345) : ℂ) * ζ ^ 11 + ((173 / 790) : ℂ) * ζ ^ 12 - ((63 / 17380) : ℂ) * ζ ^ 13 + ((252 / 4345) : ℂ) * ζ ^ 14 - ((125 / 1738) : ℂ) * ζ ^ 15 - ((49 / 869) : ℂ) * ζ ^ 16 + ((80 / 869) : ℂ) * ζ ^ 17 + ((137 / 1738) : ℂ) * ζ ^ 18 + ((168 / 4345) : ℂ) * ζ ^ 19 - ((163 / 3476) : ℂ) * ζ ^ 20 - ((171 / 3476) : ℂ) * ζ ^ 21 + ((347 / 4345) : ℂ) * ζ ^ 22 - ((1181 / 17380) : ℂ) * ζ ^ 23 + ((122 / 4345) : ℂ) * ζ ^ 24 - ((18 / 4345) : ℂ) * ζ ^ 25 + ((129 / 8690) : ℂ) * ζ ^ 26 + ((459 / 8690) : ℂ) * ζ ^ 27 - ((95 / 1738) : ℂ) * ζ ^ 28 - ((537 / 8690) : ℂ) * ζ ^ 29 + ((1189 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_0_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 0 =
      (-((6 / 395) : ℂ) + ((419 / 17380) : ℂ) * ζ ^ 1 - ((991 / 8690) : ℂ) * ζ ^ 2 - ((207 / 4345) : ℂ) * ζ ^ 3 - ((192 / 4345) : ℂ) * ζ ^ 5 - ((809 / 8690) : ℂ) * ζ ^ 6 + ((137 / 1580) : ℂ) * ζ ^ 8 + ((787 / 17380) : ℂ) * ζ ^ 9 + ((766 / 4345) : ℂ) * ζ ^ 11 + ((49 / 395) : ℂ) * ζ ^ 12 - ((419 / 17380) : ℂ) * ζ ^ 13 - ((1469 / 8690) : ℂ) * ζ ^ 15 - ((419 / 17380) : ℂ) * ζ ^ 17 - ((2359 / 17380) : ℂ) * ζ ^ 18 + ((997 / 17380) : ℂ) * ζ ^ 21 + ((991 / 8690) : ℂ) * ζ ^ 22 + ((8 / 395) : ℂ) * ζ ^ 24 + ((1187 / 17380) : ℂ) * ζ ^ 25 - ((523 / 8690) : ℂ) * ζ ^ 27 - ((137 / 1580) : ℂ) * ζ ^ 28 + ((419 / 17380) : ℂ) * ζ ^ 29 + ((2851 / 17380) : ℂ) * ζ ^ 30 - ((766 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((27 / 4345) : ℂ) - ((251 / 17380) : ℂ) * ζ ^ 1 + ((1101 / 17380) : ℂ) * ζ ^ 2 + ((249 / 4345) : ℂ) * ζ ^ 3 - ((7 / 395) : ℂ) * ζ ^ 4 + ((911 / 17380) : ℂ) * ζ ^ 5 + ((27 / 790) : ℂ) * ζ ^ 6 + ((167 / 17380) : ℂ) * ζ ^ 7 + ((39 / 3476) : ℂ) * ζ ^ 8 - ((751 / 17380) : ℂ) * ζ ^ 9 - ((411 / 3476) : ℂ) * ζ ^ 10 + ((1029 / 17380) : ℂ) * ζ ^ 11 - ((1281 / 8690) : ℂ) * ζ ^ 12 + ((171 / 8690) : ℂ) * ζ ^ 13 - ((41 / 8690) : ℂ) * ζ ^ 14 + ((537 / 4345) : ℂ) * ζ ^ 15 + ((971 / 8690) : ℂ) * ζ ^ 16 - ((111 / 17380) : ℂ) * ζ ^ 17 + ((159 / 1580) : ℂ) * ζ ^ 18 - ((783 / 17380) : ℂ) * ζ ^ 19 - ((23 / 316) : ℂ) * ζ ^ 20 - ((443 / 17380) : ℂ) * ζ ^ 21 - ((23 / 395) : ℂ) * ζ ^ 22 - ((271 / 3476) : ℂ) * ζ ^ 23 - ((261 / 4345) : ℂ) * ζ ^ 24 + ((12 / 4345) : ℂ) * ζ ^ 25 + ((57 / 1580) : ℂ) * ζ ^ 26 + ((1 / 869) : ℂ) * ζ ^ 27 + ((51 / 4345) : ℂ) * ζ ^ 28 + ((177 / 4345) : ℂ) * ζ ^ 29 + ((84 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_0_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 0 =
      (((17 / 4345) : ℂ) - ((113 / 4345) : ℂ) * ζ ^ 1 + ((322 / 4345) : ℂ) * ζ ^ 2 - ((843 / 17380) : ℂ) * ζ ^ 3 - ((101 / 17380) : ℂ) * ζ ^ 5 + ((238 / 4345) : ℂ) * ζ ^ 6 - ((1046 / 4345) : ℂ) * ζ ^ 8 - ((333 / 8690) : ℂ) * ζ ^ 9 + ((1217 / 8690) : ℂ) * ζ ^ 11 - ((3787 / 17380) : ℂ) * ζ ^ 12 + ((113 / 4345) : ℂ) * ζ ^ 13 + ((4427 / 17380) : ℂ) * ζ ^ 15 + ((113 / 4345) : ℂ) * ζ ^ 17 - ((619 / 17380) : ℂ) * ζ ^ 18 - ((3571 / 17380) : ℂ) * ζ ^ 21 - ((322 / 4345) : ℂ) * ζ ^ 22 + ((2351 / 17380) : ℂ) * ζ ^ 24 - ((351 / 17380) : ℂ) * ζ ^ 25 - ((171 / 17380) : ℂ) * ζ ^ 27 + ((1046 / 4345) : ℂ) * ζ ^ 28 - ((113 / 4345) : ℂ) * ζ ^ 29 - ((2509 / 17380) : ℂ) * ζ ^ 30 - ((1217 / 8690) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((17 / 4345) : ℂ) + ((221 / 17380) : ℂ) * ζ ^ 1 - ((1403 / 8690) : ℂ) * ζ ^ 2 - ((2721 / 17380) : ℂ) * ζ ^ 3 - ((2441 / 8690) : ℂ) * ζ ^ 4 - ((993 / 4345) : ℂ) * ζ ^ 5 - ((1359 / 17380) : ℂ) * ζ ^ 6 - ((1917 / 17380) : ℂ) * ζ ^ 7 + ((2281 / 8690) : ℂ) * ζ ^ 8 + ((139 / 790) : ℂ) * ζ ^ 9 + ((449 / 1580) : ℂ) * ζ ^ 10 + ((2379 / 17380) : ℂ) * ζ ^ 11 + ((1971 / 17380) : ℂ) * ζ ^ 12 - ((601 / 4345) : ℂ) * ζ ^ 13 - ((201 / 1580) : ℂ) * ζ ^ 14 - ((4137 / 17380) : ℂ) * ζ ^ 15 - ((142 / 4345) : ℂ) * ζ ^ 16 + ((747 / 8690) : ℂ) * ζ ^ 17 + ((3427 / 17380) : ℂ) * ζ ^ 18 + ((2047 / 8690) : ℂ) * ζ ^ 19 + ((2631 / 17380) : ℂ) * ζ ^ 20 + ((2479 / 17380) : ℂ) * ζ ^ 21 - ((609 / 17380) : ℂ) * ζ ^ 22 + ((9 / 316) : ℂ) * ζ ^ 23 - ((977 / 8690) : ℂ) * ζ ^ 24 - ((1279 / 17380) : ℂ) * ζ ^ 25 - ((581 / 3476) : ℂ) * ζ ^ 26 - ((851 / 8690) : ℂ) * ζ ^ 27 - ((669 / 8690) : ℂ) * ζ ^ 28 - ((102 / 4345) : ℂ) * ζ ^ 29 - ((48 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_0_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 0 =
      (((91 / 395) : ℂ) + ((141 / 1580) : ℂ) * ζ ^ 1 - ((117 / 790) : ℂ) * ζ ^ 2 - ((14 / 395) : ℂ) * ζ ^ 3 - ((457 / 1580) : ℂ) * ζ ^ 5 - ((69 / 395) : ℂ) * ζ ^ 6 - ((207 / 1580) : ℂ) * ζ ^ 8 - ((91 / 790) : ℂ) * ζ ^ 9 + ((403 / 1580) : ℂ) * ζ ^ 11 + ((129 / 1580) : ℂ) * ζ ^ 12 - ((141 / 1580) : ℂ) * ζ ^ 13 + ((109 / 1580) : ℂ) * ζ ^ 15 - ((141 / 1580) : ℂ) * ζ ^ 17 - ((7 / 395) : ℂ) * ζ ^ 18 - ((1 / 790) : ℂ) * ζ ^ 21 + ((117 / 790) : ℂ) * ζ ^ 22 + ((363 / 1580) : ℂ) * ζ ^ 24 + ((299 / 790) : ℂ) * ζ ^ 25 - ((367 / 1580) : ℂ) * ζ ^ 27 + ((207 / 1580) : ℂ) * ζ ^ 28 + ((141 / 1580) : ℂ) * ζ ^ 29 - ((363 / 1580) : ℂ) * ζ ^ 30 - ((403 / 1580) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((63 / 395) : ℂ) + ((57 / 1580) : ℂ) * ζ ^ 1 - ((9 / 790) : ℂ) * ζ ^ 2 - ((63 / 1580) : ℂ) * ζ ^ 3 + ((3 / 20) : ℂ) * ζ ^ 4 + ((217 / 1580) : ℂ) * ζ ^ 5 + ((1 / 79) : ℂ) * ζ ^ 6 + ((181 / 1580) : ℂ) * ζ ^ 7 + ((113 / 1580) : ℂ) * ζ ^ 8 - ((41 / 395) : ℂ) * ζ ^ 9 + ((99 / 1580) : ℂ) * ζ ^ 10 - ((84 / 395) : ℂ) * ζ ^ 11 - ((33 / 395) : ℂ) * ζ ^ 12 - ((29 / 790) : ℂ) * ζ ^ 13 + ((259 / 1580) : ℂ) * ζ ^ 14 + ((129 / 790) : ℂ) * ζ ^ 15 + ((41 / 316) : ℂ) * ζ ^ 16 + ((239 / 1580) : ℂ) * ζ ^ 17 + ((169 / 790) : ℂ) * ζ ^ 18 - ((109 / 1580) : ℂ) * ζ ^ 19 - ((199 / 1580) : ℂ) * ζ ^ 20 + ((1 / 1580) : ℂ) * ζ ^ 21 - ((119 / 1580) : ℂ) * ζ ^ 22 - ((191 / 1580) : ℂ) * ζ ^ 23 - ((87 / 790) : ℂ) * ζ ^ 24 + ((51 / 790) : ℂ) * ζ ^ 25 + ((3 / 158) : ℂ) * ζ ^ 26 - ((159 / 1580) : ℂ) * ζ ^ 27 - ((17 / 158) : ℂ) * ζ ^ 28 - ((1 / 79) : ℂ) * ζ ^ 29 - ((22 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_0_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 0 =
      (-((448 / 4345) : ℂ) - ((71 / 3476) : ℂ) * ζ ^ 1 - ((1433 / 8690) : ℂ) * ζ ^ 2 + ((1733 / 17380) : ℂ) * ζ ^ 3 + ((157 / 869) : ℂ) * ζ ^ 5 - ((1076 / 4345) : ℂ) * ζ ^ 6 - ((1949 / 17380) : ℂ) * ζ ^ 8 + ((355 / 3476) : ℂ) * ζ ^ 9 + ((2991 / 17380) : ℂ) * ζ ^ 11 - ((801 / 8690) : ℂ) * ζ ^ 12 + ((71 / 3476) : ℂ) * ζ ^ 13 + ((563 / 17380) : ℂ) * ζ ^ 15 + ((71 / 3476) : ℂ) * ζ ^ 17 + ((362 / 4345) : ℂ) * ζ ^ 18 + ((27 / 869) : ℂ) * ζ ^ 21 + ((1433 / 8690) : ℂ) * ζ ^ 22 + ((851 / 17380) : ℂ) * ζ ^ 24 - ((699 / 3476) : ℂ) * ζ ^ 25 + ((39 / 4345) : ℂ) * ζ ^ 27 + ((1949 / 17380) : ℂ) * ζ ^ 28 - ((71 / 3476) : ℂ) * ζ ^ 29 - ((2007 / 17380) : ℂ) * ζ ^ 30 - ((2991 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((1783 / 17380) : ℂ) + ((1 / 1580) : ℂ) * ζ ^ 1 + ((98 / 869) : ℂ) * ζ ^ 2 - ((1103 / 8690) : ℂ) * ζ ^ 3 - ((73 / 1580) : ℂ) * ζ ^ 4 - ((1827 / 17380) : ℂ) * ζ ^ 5 + ((361 / 3476) : ℂ) * ζ ^ 6 + ((683 / 17380) : ℂ) * ζ ^ 7 + ((428 / 4345) : ℂ) * ζ ^ 8 - ((211 / 8690) : ℂ) * ζ ^ 9 - ((67 / 790) : ℂ) * ζ ^ 10 - ((1291 / 17380) : ℂ) * ζ ^ 11 + ((129 / 1738) : ℂ) * ζ ^ 12 - ((89 / 1580) : ℂ) * ζ ^ 13 + ((733 / 8690) : ℂ) * ζ ^ 14 + ((1109 / 17380) : ℂ) * ζ ^ 15 - ((57 / 1580) : ℂ) * ζ ^ 16 + ((941 / 17380) : ℂ) * ζ ^ 17 + ((41 / 1580) : ℂ) * ζ ^ 18 - ((873 / 17380) : ℂ) * ζ ^ 19 + ((853 / 17380) : ℂ) * ζ ^ 20 - ((77 / 1580) : ℂ) * ζ ^ 21 - ((389 / 4345) : ℂ) * ζ ^ 22 + ((102 / 4345) : ℂ) * ζ ^ 23 - ((378 / 4345) : ℂ) * ζ ^ 24 + ((145 / 3476) : ℂ) * ζ ^ 25 - ((74 / 4345) : ℂ) * ζ ^ 26 + ((403 / 17380) : ℂ) * ζ ^ 27 + ((23 / 17380) : ℂ) * ζ ^ 28 + ((101 / 4345) : ℂ) * ζ ^ 29 + ((63 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_0_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 0 =
      (-((1 / 11) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 1 + ((7 / 44) : ℂ) * ζ ^ 2 + ((5 / 44) : ℂ) * ζ ^ 3 + ((1 / 44) : ℂ) * ζ ^ 5 + ((9 / 44) : ℂ) * ζ ^ 6 + ((2 / 11) : ℂ) * ζ ^ 8 + ((3 / 44) : ℂ) * ζ ^ 9 - ((5 / 22) : ℂ) * ζ ^ 11 + ((3 / 22) : ℂ) * ζ ^ 12 + ((5 / 44) : ℂ) * ζ ^ 13 - ((1 / 22) : ℂ) * ζ ^ 15 + ((5 / 44) : ℂ) * ζ ^ 17 + ((1 / 44) : ℂ) * ζ ^ 18 + ((9 / 44) : ℂ) * ζ ^ 21 - ((7 / 44) : ℂ) * ζ ^ 22 - ((5 / 44) : ℂ) * ζ ^ 24 - ((3 / 22) : ℂ) * ζ ^ 25 + ((9 / 44) : ℂ) * ζ ^ 27 - ((2 / 11) : ℂ) * ζ ^ 28 - ((5 / 44) : ℂ) * ζ ^ 29 + ((1 / 11) : ℂ) * ζ ^ 30 + ((5 / 22) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_0_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 0 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_0_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 0 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_3_0 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        3 0 =
      alternatingSixAmbientRow18TransformedGeneratorA
        3 0 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_3_0_0,
      row18_transformedGeneratorA_term_3_0_1,
      row18_transformedGeneratorA_term_3_0_2,
      row18_transformedGeneratorA_term_3_0_3,
      row18_transformedGeneratorA_term_3_0_4,
      row18_transformedGeneratorA_term_3_0_5,
      row18_transformedGeneratorA_term_3_0_6,
      row18_transformedGeneratorA_term_3_0_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_1_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 1 =
      (((212 / 4345) : ℂ) - ((841 / 4345) : ℂ) * ζ ^ 1 + ((1229 / 17380) : ℂ) * ζ ^ 2 + ((643 / 3476) : ℂ) * ζ ^ 3 - ((667 / 17380) : ℂ) * ζ ^ 5 - ((2009 / 17380) : ℂ) * ζ ^ 6 + ((263 / 8690) : ℂ) * ζ ^ 8 + ((1249 / 8690) : ℂ) * ζ ^ 9 - ((137 / 1738) : ℂ) * ζ ^ 11 - ((997 / 17380) : ℂ) * ζ ^ 12 + ((841 / 4345) : ℂ) * ζ ^ 13 + ((273 / 3476) : ℂ) * ζ ^ 15 + ((841 / 4345) : ℂ) * ζ ^ 17 - ((1267 / 17380) : ℂ) * ζ ^ 18 + ((2229 / 8690) : ℂ) * ζ ^ 21 - ((1229 / 17380) : ℂ) * ζ ^ 22 - ((3109 / 17380) : ℂ) * ζ ^ 24 - ((2697 / 17380) : ℂ) * ζ ^ 25 - ((101 / 3476) : ℂ) * ζ ^ 27 - ((263 / 8690) : ℂ) * ζ ^ 28 - ((841 / 4345) : ℂ) * ζ ^ 29 - ((288 / 4345) : ℂ) * ζ ^ 30 + ((137 / 1738) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((16 / 395) : ℂ) + ((173 / 790) : ℂ) * ζ ^ 1 - ((1109 / 17380) : ℂ) * ζ ^ 2 - ((817 / 3476) : ℂ) * ζ ^ 3 - ((164 / 4345) : ℂ) * ζ ^ 4 - ((644 / 4345) : ℂ) * ζ ^ 5 + ((59 / 220) : ℂ) * ζ ^ 6 + ((3369 / 17380) : ℂ) * ζ ^ 7 - ((91 / 790) : ℂ) * ζ ^ 8 - ((417 / 8690) : ℂ) * ζ ^ 9 - ((1163 / 17380) : ℂ) * ζ ^ 10 - ((3 / 110) : ℂ) * ζ ^ 11 + ((4293 / 17380) : ℂ) * ζ ^ 12 - ((221 / 17380) : ℂ) * ζ ^ 13 + ((1 / 869) : ℂ) * ζ ^ 14 - ((468 / 4345) : ℂ) * ζ ^ 15 - ((417 / 8690) : ℂ) * ζ ^ 16 - ((1737 / 17380) : ℂ) * ζ ^ 17 + ((1983 / 17380) : ℂ) * ζ ^ 18 + ((3887 / 17380) : ℂ) * ζ ^ 19 + ((1117 / 17380) : ℂ) * ζ ^ 20 - ((483 / 3476) : ℂ) * ζ ^ 21 - ((518 / 4345) : ℂ) * ζ ^ 22 - ((23 / 158) : ℂ) * ζ ^ 23 + ((2483 / 17380) : ℂ) * ζ ^ 24 + ((767 / 8690) : ℂ) * ζ ^ 25 + ((101 / 3476) : ℂ) * ζ ^ 26 + ((433 / 17380) : ℂ) * ζ ^ 27 - ((358 / 4345) : ℂ) * ζ ^ 28 - ((207 / 3476) : ℂ) * ζ ^ 29 + ((1073 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_1_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 1 =
      (((1479 / 4345) : ℂ) + ((907 / 1580) : ℂ) * ζ ^ 1 + ((61 / 1580) : ℂ) * ζ ^ 2 - ((4053 / 17380) : ℂ) * ζ ^ 3 + ((119 / 395) : ℂ) * ζ ^ 5 + ((267 / 790) : ℂ) * ζ ^ 6 - ((2493 / 17380) : ℂ) * ζ ^ 8 - ((529 / 1580) : ℂ) * ζ ^ 9 - ((1981 / 17380) : ℂ) * ζ ^ 11 + ((201 / 17380) : ℂ) * ζ ^ 12 - ((907 / 1580) : ℂ) * ζ ^ 13 - ((3793 / 17380) : ℂ) * ζ ^ 15 - ((907 / 1580) : ℂ) * ζ ^ 17 + ((163 / 395) : ℂ) * ζ ^ 18 - ((261 / 395) : ℂ) * ζ ^ 21 - ((61 / 1580) : ℂ) * ζ ^ 22 + ((5217 / 17380) : ℂ) * ζ ^ 24 + ((431 / 1580) : ℂ) * ζ ^ 25 - ((1351 / 17380) : ℂ) * ζ ^ 27 + ((2493 / 17380) : ℂ) * ζ ^ 28 + ((907 / 1580) : ℂ) * ζ ^ 29 + ((187 / 1580) : ℂ) * ζ ^ 30 + ((1981 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((5981 / 17380) : ℂ) - ((2441 / 4345) : ℂ) * ζ ^ 1 - ((1477 / 17380) : ℂ) * ζ ^ 2 + ((893 / 3476) : ℂ) * ζ ^ 3 + ((2483 / 8690) : ℂ) * ζ ^ 4 + ((1031 / 17380) : ℂ) * ζ ^ 5 - ((3183 / 17380) : ℂ) * ζ ^ 6 - ((4397 / 17380) : ℂ) * ζ ^ 7 - ((3 / 17380) : ℂ) * ζ ^ 8 + ((721 / 4345) : ℂ) * ζ ^ 9 + ((3979 / 17380) : ℂ) * ζ ^ 10 + ((751 / 3476) : ℂ) * ζ ^ 11 - ((2221 / 17380) : ℂ) * ζ ^ 12 + ((49 / 316) : ℂ) * ζ ^ 13 - ((936 / 4345) : ℂ) * ζ ^ 14 + ((1383 / 17380) : ℂ) * ζ ^ 15 - ((721 / 8690) : ℂ) * ζ ^ 16 + ((1307 / 8690) : ℂ) * ζ ^ 17 - ((49 / 220) : ℂ) * ζ ^ 18 - ((1589 / 8690) : ℂ) * ζ ^ 19 - ((523 / 4345) : ℂ) * ζ ^ 20 + ((2457 / 8690) : ℂ) * ζ ^ 21 + ((3031 / 17380) : ℂ) * ζ ^ 22 + ((731 / 3476) : ℂ) * ζ ^ 23 - ((3 / 1580) : ℂ) * ζ ^ 24 - ((681 / 17380) : ℂ) * ζ ^ 25 - ((345 / 3476) : ℂ) * ζ ^ 26 - ((213 / 17380) : ℂ) * ζ ^ 27 + ((29 / 316) : ℂ) * ζ ^ 28 - ((9 / 79) : ℂ) * ζ ^ 29 - ((504 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_1_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 1 =
      (-((1457 / 8690) : ℂ) - ((394 / 869) : ℂ) * ζ ^ 1 - ((93 / 1580) : ℂ) * ζ ^ 2 - ((587 / 3476) : ℂ) * ζ ^ 3 - ((2195 / 3476) : ℂ) * ζ ^ 5 + ((13 / 1580) : ℂ) * ζ ^ 6 + ((4201 / 8690) : ℂ) * ζ ^ 8 + ((34 / 869) : ℂ) * ζ ^ 9 - ((223 / 3476) : ℂ) * ζ ^ 11 + ((3601 / 17380) : ℂ) * ζ ^ 12 + ((394 / 869) : ℂ) * ζ ^ 13 + ((421 / 1738) : ℂ) * ζ ^ 15 + ((394 / 869) : ℂ) * ζ ^ 17 - ((241 / 1580) : ℂ) * ζ ^ 18 + ((897 / 1738) : ℂ) * ζ ^ 21 + ((93 / 1580) : ℂ) * ζ ^ 22 - ((2383 / 17380) : ℂ) * ζ ^ 24 + ((619 / 3476) : ℂ) * ζ ^ 25 - ((203 / 3476) : ℂ) * ζ ^ 27 - ((4201 / 8690) : ℂ) * ζ ^ 28 - ((394 / 869) : ℂ) * ζ ^ 29 - ((371 / 1580) : ℂ) * ζ ^ 30 + ((223 / 3476) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((641 / 4345) : ℂ) + ((1179 / 3476) : ℂ) * ζ ^ 1 - ((498 / 4345) : ℂ) * ζ ^ 2 + ((1777 / 17380) : ℂ) * ζ ^ 3 - ((19 / 3476) : ℂ) * ζ ^ 4 + ((1717 / 4345) : ℂ) * ζ ^ 5 + ((41 / 1738) : ℂ) * ζ ^ 6 + ((2639 / 17380) : ℂ) * ζ ^ 7 - ((109 / 3476) : ℂ) * ζ ^ 8 - ((207 / 3476) : ℂ) * ζ ^ 9 + ((2087 / 17380) : ℂ) * ζ ^ 10 + ((1699 / 17380) : ℂ) * ζ ^ 11 - ((7 / 1580) : ℂ) * ζ ^ 12 - ((465 / 1738) : ℂ) * ζ ^ 13 - ((3359 / 17380) : ℂ) * ζ ^ 14 - ((3939 / 17380) : ℂ) * ζ ^ 15 + ((2157 / 17380) : ℂ) * ζ ^ 16 + ((17 / 158) : ℂ) * ζ ^ 17 + ((7239 / 17380) : ℂ) * ζ ^ 18 - ((883 / 17380) : ℂ) * ζ ^ 19 - ((1333 / 8690) : ℂ) * ζ ^ 20 - ((687 / 1738) : ℂ) * ζ ^ 21 - ((1547 / 17380) : ℂ) * ζ ^ 22 - ((1689 / 17380) : ℂ) * ζ ^ 23 - ((201 / 17380) : ℂ) * ζ ^ 24 - ((311 / 8690) : ℂ) * ζ ^ 25 + ((1379 / 17380) : ℂ) * ζ ^ 26 - ((281 / 4345) : ℂ) * ζ ^ 27 + ((3319 / 17380) : ℂ) * ζ ^ 28 + ((413 / 4345) : ℂ) * ζ ^ 29 + ((136 / 869) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_1_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 1 =
      (-((17 / 395) : ℂ) + ((21 / 790) : ℂ) * ζ ^ 1 + ((89 / 395) : ℂ) * ζ ^ 2 - ((109 / 395) : ℂ) * ζ ^ 3 - ((19 / 1580) : ℂ) * ζ ^ 5 + ((719 / 1580) : ℂ) * ζ ^ 6 + ((377 / 790) : ℂ) * ζ ^ 8 - ((389 / 1580) : ℂ) * ζ ^ 9 - ((361 / 790) : ℂ) * ζ ^ 11 + ((151 / 790) : ℂ) * ζ ^ 12 - ((21 / 790) : ℂ) * ζ ^ 13 - ((481 / 1580) : ℂ) * ζ ^ 15 - ((21 / 790) : ℂ) * ζ ^ 17 + ((48 / 395) : ℂ) * ζ ^ 18 - ((11 / 395) : ℂ) * ζ ^ 21 - ((89 / 395) : ℂ) * ζ ^ 22 - ((51 / 1580) : ℂ) * ζ ^ 24 + ((61 / 1580) : ℂ) * ζ ^ 25 + ((139 / 790) : ℂ) * ζ ^ 27 - ((377 / 790) : ℂ) * ζ ^ 28 + ((21 / 790) : ℂ) * ζ ^ 29 + ((507 / 1580) : ℂ) * ζ ^ 30 + ((361 / 790) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((27 / 790) : ℂ) - ((1 / 5) : ℂ) * ζ ^ 1 - ((169 / 1580) : ℂ) * ζ ^ 2 + ((67 / 158) : ℂ) * ζ ^ 3 - ((27 / 1580) : ℂ) * ζ ^ 4 + ((21 / 79) : ℂ) * ζ ^ 5 - ((329 / 1580) : ℂ) * ζ ^ 6 - ((53 / 316) : ℂ) * ζ ^ 7 - ((1 / 2) : ℂ) * ζ ^ 8 + ((19 / 79) : ℂ) * ζ ^ 9 + ((3 / 158) : ℂ) * ζ ^ 10 + ((2 / 5) : ℂ) * ζ ^ 11 - ((41 / 1580) : ℂ) * ζ ^ 12 - ((223 / 1580) : ℂ) * ζ ^ 13 - ((93 / 790) : ℂ) * ζ ^ 14 + ((29 / 316) : ℂ) * ζ ^ 15 + ((107 / 790) : ℂ) * ζ ^ 16 + ((19 / 316) : ℂ) * ζ ^ 17 - ((421 / 1580) : ℂ) * ζ ^ 18 - ((279 / 790) : ℂ) * ζ ^ 19 - ((437 / 1580) : ℂ) * ζ ^ 20 - ((353 / 1580) : ℂ) * ζ ^ 21 + ((119 / 395) : ℂ) * ζ ^ 22 + ((7 / 20) : ℂ) * ζ ^ 23 + ((139 / 790) : ℂ) * ζ ^ 24 - ((431 / 1580) : ℂ) * ζ ^ 25 - ((291 / 1580) : ℂ) * ζ ^ 26 + ((13 / 395) : ℂ) * ζ ^ 27 + ((71 / 395) : ℂ) * ζ ^ 28 - ((19 / 1580) : ℂ) * ζ ^ 29 + ((87 / 790) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_1_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 1 =
      (-((221 / 3476) : ℂ) - ((3831 / 17380) : ℂ) * ζ ^ 1 - ((10697 / 17380) : ℂ) * ζ ^ 2 + ((764 / 4345) : ℂ) * ζ ^ 3 + ((6737 / 17380) : ℂ) * ζ ^ 5 - ((13813 / 17380) : ℂ) * ζ ^ 6 - ((489 / 869) : ℂ) * ζ ^ 8 + ((11367 / 17380) : ℂ) * ζ ^ 9 + ((2223 / 4345) : ℂ) * ζ ^ 11 - ((717 / 1738) : ℂ) * ζ ^ 12 + ((3831 / 17380) : ℂ) * ζ ^ 13 + ((2053 / 8690) : ℂ) * ζ ^ 15 + ((3831 / 17380) : ℂ) * ζ ^ 17 + ((2323 / 8690) : ℂ) * ζ ^ 18 + ((507 / 17380) : ℂ) * ζ ^ 21 + ((10697 / 17380) : ℂ) * ζ ^ 22 + ((9 / 1738) : ℂ) * ζ ^ 24 - ((2642 / 4345) : ℂ) * ζ ^ 25 - ((1933 / 17380) : ℂ) * ζ ^ 27 + ((489 / 869) : ℂ) * ζ ^ 28 - ((3831 / 17380) : ℂ) * ζ ^ 29 - ((2137 / 8690) : ℂ) * ζ ^ 30 - ((2223 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((49 / 790) : ℂ) + ((708 / 4345) : ℂ) * ζ ^ 1 + ((4577 / 8690) : ℂ) * ζ ^ 2 - ((875 / 3476) : ℂ) * ζ ^ 3 - ((437 / 3476) : ℂ) * ζ ^ 4 - ((2117 / 4345) : ℂ) * ζ ^ 5 + ((3199 / 17380) : ℂ) * ζ ^ 6 + ((1103 / 17380) : ℂ) * ζ ^ 7 + ((4677 / 17380) : ℂ) * ζ ^ 8 - ((3667 / 17380) : ℂ) * ζ ^ 9 - ((433 / 1738) : ℂ) * ζ ^ 10 - ((4883 / 17380) : ℂ) * ζ ^ 11 + ((437 / 4345) : ℂ) * ζ ^ 12 + ((3387 / 8690) : ℂ) * ζ ^ 13 + ((5939 / 17380) : ℂ) * ζ ^ 14 + ((1453 / 17380) : ℂ) * ζ ^ 15 - ((206 / 869) : ℂ) * ζ ^ 16 - ((1073 / 3476) : ℂ) * ζ ^ 17 - ((80 / 869) : ℂ) * ζ ^ 18 + ((3607 / 17380) : ℂ) * ζ ^ 19 + ((2301 / 8690) : ℂ) * ζ ^ 20 + ((2241 / 17380) : ℂ) * ζ ^ 21 - ((757 / 8690) : ℂ) * ζ ^ 22 - ((1811 / 17380) : ℂ) * ζ ^ 23 + ((109 / 4345) : ℂ) * ζ ^ 24 + ((595 / 3476) : ℂ) * ζ ^ 25 + ((169 / 869) : ℂ) * ζ ^ 26 + ((344 / 4345) : ℂ) * ζ ^ 27 - ((897 / 4345) : ℂ) * ζ ^ 28 - ((884 / 4345) : ℂ) * ζ ^ 29 - ((468 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_1_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 1 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_1_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 1 =
      (((6 / 55) : ℂ) + ((7 / 55) : ℂ) * ζ ^ 1 - ((57 / 220) : ℂ) * ζ ^ 2 - ((19 / 220) : ℂ) * ζ ^ 3 + ((17 / 110) : ℂ) * ζ ^ 5 + ((8 / 55) : ℂ) * ζ ^ 6 - ((37 / 220) : ℂ) * ζ ^ 8 + ((7 / 110) : ℂ) * ζ ^ 9 + ((27 / 220) : ℂ) * ζ ^ 11 - ((9 / 55) : ℂ) * ζ ^ 12 - ((7 / 55) : ℂ) * ζ ^ 13 + ((1 / 220) : ℂ) * ζ ^ 15 - ((7 / 55) : ℂ) * ζ ^ 17 + ((3 / 110) : ℂ) * ζ ^ 18 - ((23 / 110) : ℂ) * ζ ^ 21 + ((57 / 220) : ℂ) * ζ ^ 22 + ((63 / 220) : ℂ) * ζ ^ 24 - ((3 / 110) : ℂ) * ζ ^ 25 - ((43 / 220) : ℂ) * ζ ^ 27 + ((37 / 220) : ℂ) * ζ ^ 28 + ((7 / 55) : ℂ) * ζ ^ 29 - ((9 / 220) : ℂ) * ζ ^ 30 - ((27 / 220) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((6 / 55) : ℂ) + ((7 / 110) : ℂ) * ζ ^ 1 + ((4 / 55) : ℂ) * ζ ^ 2 + ((61 / 220) : ℂ) * ζ ^ 3 - ((3 / 55) : ℂ) * ζ ^ 4 - ((3 / 110) : ℂ) * ζ ^ 5 - ((127 / 220) : ℂ) * ζ ^ 6 + ((6 / 55) : ℂ) * ζ ^ 7 + ((13 / 220) : ℂ) * ζ ^ 8 - ((1 / 55) : ℂ) * ζ ^ 9 + ((41 / 220) : ℂ) * ζ ^ 10 - ((2 / 55) : ℂ) * ζ ^ 11 - ((7 / 55) : ℂ) * ζ ^ 12 + ((9 / 220) : ℂ) * ζ ^ 14 + ((13 / 110) : ℂ) * ζ ^ 15 - ((7 / 110) : ℂ) * ζ ^ 17 + ((7 / 44) : ℂ) * ζ ^ 18 - ((21 / 110) : ℂ) * ζ ^ 19 + ((3 / 55) : ℂ) * ζ ^ 20 + ((9 / 110) : ℂ) * ζ ^ 21 + ((19 / 110) : ℂ) * ζ ^ 22 - ((6 / 55) : ℂ) * ζ ^ 23 - ((39 / 220) : ℂ) * ζ ^ 24 - ((1 / 55) : ℂ) * ζ ^ 25 - ((41 / 220) : ℂ) * ζ ^ 26 + ((6 / 55) : ℂ) * ζ ^ 27 + ((27 / 220) : ℂ) * ζ ^ 28)

private theorem row18_transformedGeneratorA_term_3_1_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 1 =
      (-((27 / 220) : ℂ) - ((9 / 220) : ℂ) * ζ ^ 1 + ((7 / 55) : ℂ) * ζ ^ 2 - ((6 / 55) : ℂ) * ζ ^ 3 - ((7 / 220) : ℂ) * ζ ^ 5 - ((2 / 55) : ℂ) * ζ ^ 6 - ((17 / 110) : ℂ) * ζ ^ 8 + ((23 / 220) : ℂ) * ζ ^ 9 + ((37 / 220) : ℂ) * ζ ^ 11 + ((13 / 220) : ℂ) * ζ ^ 12 + ((9 / 220) : ℂ) * ζ ^ 13 + ((9 / 55) : ℂ) * ζ ^ 15 + ((9 / 220) : ℂ) * ζ ^ 17 - ((29 / 220) : ℂ) * ζ ^ 18 - ((13 / 55) : ℂ) * ζ ^ 21 - ((7 / 55) : ℂ) * ζ ^ 22 - ((9 / 220) : ℂ) * ζ ^ 24 - ((1 / 110) : ℂ) * ζ ^ 25 - ((2 / 55) : ℂ) * ζ ^ 27 + ((17 / 110) : ℂ) * ζ ^ 28 - ((9 / 220) : ℂ) * ζ ^ 29 + ((4 / 55) : ℂ) * ζ ^ 30 - ((37 / 220) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_3_1 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        3 1 =
      alternatingSixAmbientRow18TransformedGeneratorA
        3 1 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_3_1_0,
      row18_transformedGeneratorA_term_3_1_1,
      row18_transformedGeneratorA_term_3_1_2,
      row18_transformedGeneratorA_term_3_1_3,
      row18_transformedGeneratorA_term_3_1_4,
      row18_transformedGeneratorA_term_3_1_5,
      row18_transformedGeneratorA_term_3_1_6,
      row18_transformedGeneratorA_term_3_1_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_2_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 2 =
      (((1589 / 17380) : ℂ) - ((95 / 869) : ℂ) * ζ ^ 1 + ((1123 / 8690) : ℂ) * ζ ^ 2 + ((259 / 1738) : ℂ) * ζ ^ 3 - ((1 / 3476) : ℂ) * ζ ^ 5 + ((1849 / 17380) : ℂ) * ζ ^ 6 + ((699 / 8690) : ℂ) * ζ ^ 8 + ((37 / 1738) : ℂ) * ζ ^ 9 + ((27 / 869) : ℂ) * ζ ^ 11 - ((573 / 8690) : ℂ) * ζ ^ 12 + ((95 / 869) : ℂ) * ζ ^ 13 - ((95 / 3476) : ℂ) * ζ ^ 15 + ((95 / 869) : ℂ) * ζ ^ 17 - ((2503 / 17380) : ℂ) * ζ ^ 18 + ((409 / 3476) : ℂ) * ζ ^ 21 - ((1123 / 8690) : ℂ) * ζ ^ 22 - ((717 / 17380) : ℂ) * ζ ^ 24 - ((379 / 3476) : ℂ) * ζ ^ 25 - ((7 / 3476) : ℂ) * ζ ^ 27 - ((699 / 8690) : ℂ) * ζ ^ 28 - ((95 / 869) : ℂ) * ζ ^ 29 + ((38 / 4345) : ℂ) * ζ ^ 30 - ((27 / 869) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1333 / 17380) : ℂ) + ((57 / 395) : ℂ) * ζ ^ 1 - ((1191 / 8690) : ℂ) * ζ ^ 2 - ((1541 / 8690) : ℂ) * ζ ^ 3 + ((1437 / 17380) : ℂ) * ζ ^ 4 - ((1459 / 17380) : ℂ) * ζ ^ 5 + ((601 / 17380) : ℂ) * ζ ^ 6 + ((353 / 4345) : ℂ) * ζ ^ 7 - ((2757 / 17380) : ℂ) * ζ ^ 8 + ((1471 / 17380) : ℂ) * ζ ^ 9 + ((1399 / 17380) : ℂ) * ζ ^ 10 - ((563 / 8690) : ℂ) * ζ ^ 11 + ((672 / 4345) : ℂ) * ζ ^ 12 + ((207 / 8690) : ℂ) * ζ ^ 13 - ((437 / 8690) : ℂ) * ζ ^ 14 + ((145 / 3476) : ℂ) * ζ ^ 15 - ((1129 / 17380) : ℂ) * ζ ^ 16 - ((193 / 17380) : ℂ) * ζ ^ 17 + ((2397 / 17380) : ℂ) * ζ ^ 18 + ((469 / 8690) : ℂ) * ζ ^ 19 - ((39 / 8690) : ℂ) * ζ ^ 20 - ((63 / 869) : ℂ) * ζ ^ 21 - ((709 / 8690) : ℂ) * ζ ^ 22 + ((631 / 17380) : ℂ) * ζ ^ 23 + ((543 / 8690) : ℂ) * ζ ^ 24 - ((53 / 17380) : ℂ) * ζ ^ 25 + ((307 / 17380) : ℂ) * ζ ^ 26 - ((207 / 17380) : ℂ) * ζ ^ 27 - ((819 / 17380) : ℂ) * ζ ^ 28 + ((2 / 395) : ℂ) * ζ ^ 29 + ((493 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_2_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 2 =
      (((641 / 3476) : ℂ) - ((117 / 790) : ℂ) * ζ ^ 1 - ((149 / 4345) : ℂ) * ζ ^ 2 - ((111 / 17380) : ℂ) * ζ ^ 3 - ((327 / 1580) : ℂ) * ζ ^ 5 + ((1231 / 17380) : ℂ) * ζ ^ 6 - ((853 / 3476) : ℂ) * ζ ^ 8 + ((223 / 1580) : ℂ) * ζ ^ 9 - ((93 / 4345) : ℂ) * ζ ^ 11 - ((65 / 3476) : ℂ) * ζ ^ 12 + ((117 / 790) : ℂ) * ζ ^ 13 + ((626 / 4345) : ℂ) * ζ ^ 15 + ((117 / 790) : ℂ) * ζ ^ 17 - ((268 / 4345) : ℂ) * ζ ^ 18 + ((1 / 10) : ℂ) * ζ ^ 21 + ((149 / 4345) : ℂ) * ζ ^ 22 + ((177 / 3476) : ℂ) * ζ ^ 24 + ((93 / 1580) : ℂ) * ζ ^ 25 + ((559 / 8690) : ℂ) * ζ ^ 27 + ((853 / 3476) : ℂ) * ζ ^ 28 - ((117 / 790) : ℂ) * ζ ^ 29 + ((2873 / 17380) : ℂ) * ζ ^ 30 + ((93 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((3361 / 17380) : ℂ) + ((1579 / 8690) : ℂ) * ζ ^ 1 - ((603 / 17380) : ℂ) * ζ ^ 2 + ((1717 / 17380) : ℂ) * ζ ^ 3 + ((3877 / 17380) : ℂ) * ζ ^ 4 - ((763 / 4345) : ℂ) * ζ ^ 5 - ((801 / 17380) : ℂ) * ζ ^ 6 + ((1 / 869) : ℂ) * ζ ^ 7 - ((621 / 17380) : ℂ) * ζ ^ 8 + ((401 / 8690) : ℂ) * ζ ^ 9 - ((137 / 1580) : ℂ) * ζ ^ 10 - ((91 / 8690) : ℂ) * ζ ^ 11 - ((16 / 4345) : ℂ) * ζ ^ 12 - ((399 / 17380) : ℂ) * ζ ^ 13 + ((769 / 8690) : ℂ) * ζ ^ 14 - ((1069 / 17380) : ℂ) * ζ ^ 15 - ((241 / 8690) : ℂ) * ζ ^ 16 + ((1281 / 17380) : ℂ) * ζ ^ 17 + ((23 / 1738) : ℂ) * ζ ^ 18 - ((219 / 4345) : ℂ) * ζ ^ 19 - ((1213 / 17380) : ℂ) * ζ ^ 20 + ((1327 / 17380) : ℂ) * ζ ^ 21 + ((251 / 8690) : ℂ) * ζ ^ 22 - ((426 / 4345) : ℂ) * ζ ^ 23 + ((278 / 4345) : ℂ) * ζ ^ 24 - ((743 / 8690) : ℂ) * ζ ^ 25 - ((1909 / 17380) : ℂ) * ζ ^ 26 + ((65 / 869) : ℂ) * ζ ^ 27 + ((131 / 4345) : ℂ) * ζ ^ 28 - ((84 / 4345) : ℂ) * ζ ^ 29)

private theorem row18_transformedGeneratorA_term_3_2_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 2 =
      (((3117 / 17380) : ℂ) + ((1657 / 17380) : ℂ) * ζ ^ 1 + ((523 / 4345) : ℂ) * ζ ^ 2 - ((2977 / 17380) : ℂ) * ζ ^ 3 + ((3611 / 17380) : ℂ) * ζ ^ 5 + ((652 / 4345) : ℂ) * ζ ^ 6 + ((2379 / 17380) : ℂ) * ζ ^ 8 + ((1131 / 17380) : ℂ) * ζ ^ 9 + ((6251 / 17380) : ℂ) * ζ ^ 11 + ((357 / 17380) : ℂ) * ζ ^ 12 - ((1657 / 17380) : ℂ) * ζ ^ 13 + ((1963 / 17380) : ℂ) * ζ ^ 15 - ((1657 / 17380) : ℂ) * ζ ^ 17 + ((136 / 4345) : ℂ) * ζ ^ 18 - ((1917 / 8690) : ℂ) * ζ ^ 21 - ((523 / 4345) : ℂ) * ζ ^ 22 + ((1039 / 17380) : ℂ) * ζ ^ 24 - ((977 / 8690) : ℂ) * ζ ^ 25 - ((876 / 4345) : ℂ) * ζ ^ 27 - ((2379 / 17380) : ℂ) * ζ ^ 28 + ((1657 / 17380) : ℂ) * ζ ^ 29 - ((353 / 8690) : ℂ) * ζ ^ 30 - ((6251 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((3117 / 17380) : ℂ) - ((1769 / 17380) : ℂ) * ζ ^ 1 - ((497 / 3476) : ℂ) * ζ ^ 2 + ((2 / 11) : ℂ) * ζ ^ 3 + ((751 / 3476) : ℂ) * ζ ^ 4 - ((207 / 3476) : ℂ) * ζ ^ 5 + ((31 / 8690) : ℂ) * ζ ^ 6 - ((1181 / 17380) : ℂ) * ζ ^ 7 - ((347 / 3476) : ℂ) * ζ ^ 8 + ((73 / 790) : ℂ) * ζ ^ 9 + ((1318 / 4345) : ℂ) * ζ ^ 10 + ((593 / 8690) : ℂ) * ζ ^ 11 + ((805 / 3476) : ℂ) * ζ ^ 12 + ((116 / 4345) : ℂ) * ζ ^ 13 - ((833 / 17380) : ℂ) * ζ ^ 14 + ((989 / 8690) : ℂ) * ζ ^ 15 + ((207 / 4345) : ℂ) * ζ ^ 16 + ((556 / 4345) : ℂ) * ζ ^ 17 + ((1049 / 17380) : ℂ) * ζ ^ 18 + ((5 / 158) : ℂ) * ζ ^ 19 - ((899 / 8690) : ℂ) * ζ ^ 20 + ((17 / 110) : ℂ) * ζ ^ 21 - ((1389 / 17380) : ℂ) * ζ ^ 22 - ((113 / 17380) : ℂ) * ζ ^ 23 - ((2413 / 17380) : ℂ) * ζ ^ 24 - ((477 / 8690) : ℂ) * ζ ^ 25 - ((157 / 790) : ℂ) * ζ ^ 26 - ((7 / 8690) : ℂ) * ζ ^ 27 - ((1051 / 8690) : ℂ) * ζ ^ 28 + ((54 / 4345) : ℂ) * ζ ^ 29 - ((336 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_2_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 2 =
      (-((63 / 790) : ℂ) + ((11 / 316) : ℂ) * ζ ^ 1 - ((137 / 395) : ℂ) * ζ ^ 2 + ((3 / 20) : ℂ) * ζ ^ 3 - ((59 / 158) : ℂ) * ζ ^ 5 - ((211 / 790) : ℂ) * ζ ^ 6 - ((211 / 790) : ℂ) * ζ ^ 8 - ((39 / 316) : ℂ) * ζ ^ 9 - ((139 / 395) : ℂ) * ζ ^ 11 - ((171 / 1580) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 - ((403 / 1580) : ℂ) * ζ ^ 15 - ((11 / 316) : ℂ) * ζ ^ 17 + ((239 / 1580) : ℂ) * ζ ^ 18 + ((7 / 158) : ℂ) * ζ ^ 21 + ((137 / 395) : ℂ) * ζ ^ 22 + ((183 / 1580) : ℂ) * ζ ^ 24 + ((129 / 316) : ℂ) * ζ ^ 25 + ((81 / 395) : ℂ) * ζ ^ 27 + ((211 / 790) : ℂ) * ζ ^ 28 + ((11 / 316) : ℂ) * ζ ^ 29 - ((251 / 1580) : ℂ) * ζ ^ 30 + ((139 / 395) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((119 / 790) : ℂ) + ((29 / 316) : ℂ) * ζ ^ 1 + ((91 / 395) : ℂ) * ζ ^ 2 - ((133 / 1580) : ℂ) * ζ ^ 3 - ((77 / 790) : ℂ) * ζ ^ 4 + ((181 / 1580) : ℂ) * ζ ^ 5 + ((4 / 395) : ℂ) * ζ ^ 6 + ((91 / 790) : ℂ) * ζ ^ 7 + ((327 / 1580) : ℂ) * ζ ^ 8 - ((81 / 790) : ℂ) * ζ ^ 9 + ((113 / 1580) : ℂ) * ζ ^ 10 + ((1 / 316) : ℂ) * ζ ^ 11 - ((37 / 1580) : ℂ) * ζ ^ 12 - ((6 / 395) : ℂ) * ζ ^ 13 + ((299 / 1580) : ℂ) * ζ ^ 14 + ((26 / 395) : ℂ) * ζ ^ 15 + ((31 / 790) : ℂ) * ζ ^ 16 + ((197 / 1580) : ℂ) * ζ ^ 17 + ((63 / 1580) : ℂ) * ζ ^ 18 - ((35 / 158) : ℂ) * ζ ^ 19 + ((63 / 395) : ℂ) * ζ ^ 20 + ((147 / 790) : ℂ) * ζ ^ 21 - ((28 / 395) : ℂ) * ζ ^ 22 + ((49 / 316) : ℂ) * ζ ^ 23 + ((129 / 1580) : ℂ) * ζ ^ 24 - ((38 / 395) : ℂ) * ζ ^ 25 - ((1 / 790) : ℂ) * ζ ^ 26 + ((29 / 316) : ℂ) * ζ ^ 27 - ((9 / 395) : ℂ) * ζ ^ 28 + ((59 / 1580) : ℂ) * ζ ^ 29 + ((1 / 158) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_2_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 2 =
      (-((65 / 3476) : ℂ) + ((7 / 17380) : ℂ) * ζ ^ 1 - ((2899 / 17380) : ℂ) * ζ ^ 2 - ((227 / 8690) : ℂ) * ζ ^ 3 + ((953 / 8690) : ℂ) * ζ ^ 5 - ((2401 / 17380) : ℂ) * ζ ^ 6 - ((23 / 1738) : ℂ) * ζ ^ 8 + ((593 / 8690) : ℂ) * ζ ^ 9 + ((458 / 4345) : ℂ) * ζ ^ 11 - ((153 / 869) : ℂ) * ζ ^ 12 - ((7 / 17380) : ℂ) * ζ ^ 13 + ((863 / 8690) : ℂ) * ζ ^ 15 - ((7 / 17380) : ℂ) * ζ ^ 17 + ((263 / 4345) : ℂ) * ζ ^ 18 - ((267 / 8690) : ℂ) * ζ ^ 21 + ((2899 / 17380) : ℂ) * ζ ^ 22 + ((100 / 869) : ℂ) * ζ ^ 24 - ((1899 / 17380) : ℂ) * ζ ^ 25 - ((573 / 17380) : ℂ) * ζ ^ 27 + ((23 / 1738) : ℂ) * ζ ^ 28 + ((7 / 17380) : ℂ) * ζ ^ 29 - ((2623 / 17380) : ℂ) * ζ ^ 30 - ((458 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((1 / 55) : ℂ) - ((17 / 790) : ℂ) * ζ ^ 1 + ((283 / 4345) : ℂ) * ζ ^ 2 - ((1719 / 17380) : ℂ) * ζ ^ 3 - ((1611 / 17380) : ℂ) * ζ ^ 4 - ((2649 / 17380) : ℂ) * ζ ^ 5 + ((71 / 17380) : ℂ) * ζ ^ 6 - ((1033 / 17380) : ℂ) * ζ ^ 7 + ((881 / 8690) : ℂ) * ζ ^ 8 - ((761 / 8690) : ℂ) * ζ ^ 9 - ((39 / 1738) : ℂ) * ζ ^ 10 - ((1049 / 8690) : ℂ) * ζ ^ 11 + ((741 / 3476) : ℂ) * ζ ^ 12 + ((261 / 17380) : ℂ) * ζ ^ 13 + ((941 / 4345) : ℂ) * ζ ^ 14 + ((236 / 4345) : ℂ) * ζ ^ 15 - ((1487 / 17380) : ℂ) * ζ ^ 16 - ((251 / 8690) : ℂ) * ζ ^ 17 + ((207 / 8690) : ℂ) * ζ ^ 18 + ((977 / 17380) : ℂ) * ζ ^ 19 + ((532 / 4345) : ℂ) * ζ ^ 20 + ((271 / 17380) : ℂ) * ζ ^ 21 - ((113 / 869) : ℂ) * ζ ^ 22 + ((117 / 1738) : ℂ) * ζ ^ 23 - ((1201 / 8690) : ℂ) * ζ ^ 24 + ((345 / 3476) : ℂ) * ζ ^ 25 - ((67 / 790) : ℂ) * ζ ^ 26 + ((179 / 17380) : ℂ) * ζ ^ 27 - ((951 / 8690) : ℂ) * ζ ^ 28 - ((157 / 4345) : ℂ) * ζ ^ 29 - ((126 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_2_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 2 =
      (-((1 / 11) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 1 + ((7 / 44) : ℂ) * ζ ^ 2 + ((5 / 44) : ℂ) * ζ ^ 3 + ((1 / 44) : ℂ) * ζ ^ 5 + ((9 / 44) : ℂ) * ζ ^ 6 + ((2 / 11) : ℂ) * ζ ^ 8 + ((3 / 44) : ℂ) * ζ ^ 9 - ((5 / 22) : ℂ) * ζ ^ 11 + ((3 / 22) : ℂ) * ζ ^ 12 + ((5 / 44) : ℂ) * ζ ^ 13 - ((1 / 22) : ℂ) * ζ ^ 15 + ((5 / 44) : ℂ) * ζ ^ 17 + ((1 / 44) : ℂ) * ζ ^ 18 + ((9 / 44) : ℂ) * ζ ^ 21 - ((7 / 44) : ℂ) * ζ ^ 22 - ((5 / 44) : ℂ) * ζ ^ 24 - ((3 / 22) : ℂ) * ζ ^ 25 + ((9 / 44) : ℂ) * ζ ^ 27 - ((2 / 11) : ℂ) * ζ ^ 28 - ((5 / 44) : ℂ) * ζ ^ 29 + ((1 / 11) : ℂ) * ζ ^ 30 + ((5 / 22) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_2_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 2 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_2_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 2 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_3_2 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        3 2 =
      alternatingSixAmbientRow18TransformedGeneratorA
        3 2 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_3_2_0,
      row18_transformedGeneratorA_term_3_2_1,
      row18_transformedGeneratorA_term_3_2_2,
      row18_transformedGeneratorA_term_3_2_3,
      row18_transformedGeneratorA_term_3_2_4,
      row18_transformedGeneratorA_term_3_2_5,
      row18_transformedGeneratorA_term_3_2_6,
      row18_transformedGeneratorA_term_3_2_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_3_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 3 =
      (((1429 / 17380) : ℂ) + ((167 / 3476) : ℂ) * ζ ^ 1 + ((2007 / 17380) : ℂ) * ζ ^ 2 - ((65 / 3476) : ℂ) * ζ ^ 3 - ((43 / 869) : ℂ) * ζ ^ 5 - ((1147 / 17380) : ℂ) * ζ ^ 6 + ((13 / 17380) : ℂ) * ζ ^ 8 - ((439 / 3476) : ℂ) * ζ ^ 9 - ((541 / 3476) : ℂ) * ζ ^ 11 - ((2501 / 17380) : ℂ) * ζ ^ 12 - ((167 / 3476) : ℂ) * ζ ^ 13 - ((97 / 1738) : ℂ) * ζ ^ 15 - ((167 / 3476) : ℂ) * ζ ^ 17 - ((1993 / 8690) : ℂ) * ζ ^ 18 - ((393 / 3476) : ℂ) * ζ ^ 21 - ((2007 / 17380) : ℂ) * ζ ^ 22 + ((183 / 17380) : ℂ) * ζ ^ 24 + ((339 / 3476) : ℂ) * ζ ^ 25 - ((9 / 1738) : ℂ) * ζ ^ 27 - ((13 / 17380) : ℂ) * ζ ^ 28 + ((167 / 3476) : ℂ) * ζ ^ 29 + ((2349 / 17380) : ℂ) * ζ ^ 30 + ((541 / 3476) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((257 / 3476) : ℂ) + ((71 / 17380) : ℂ) * ζ ^ 1 - ((57 / 3476) : ℂ) * ζ ^ 2 + ((431 / 17380) : ℂ) * ζ ^ 3 - ((17 / 316) : ℂ) * ζ ^ 4 + ((98 / 4345) : ℂ) * ζ ^ 5 + ((906 / 4345) : ℂ) * ζ ^ 6 + ((37 / 395) : ℂ) * ζ ^ 7 - ((1823 / 17380) : ℂ) * ζ ^ 8 - ((119 / 8690) : ℂ) * ζ ^ 9 - ((1244 / 4345) : ℂ) * ζ ^ 10 + ((849 / 8690) : ℂ) * ζ ^ 11 + ((3769 / 8690) : ℂ) * ζ ^ 12 - ((3 / 44) : ℂ) * ζ ^ 13 - ((18 / 395) : ℂ) * ζ ^ 14 - ((301 / 17380) : ℂ) * ζ ^ 15 - ((4701 / 17380) : ℂ) * ζ ^ 16 + ((1609 / 8690) : ℂ) * ζ ^ 17 + ((2621 / 17380) : ℂ) * ζ ^ 18 - ((1841 / 17380) : ℂ) * ζ ^ 19 + ((261 / 1738) : ℂ) * ζ ^ 20 - ((31 / 8690) : ℂ) * ζ ^ 21 - ((522 / 4345) : ℂ) * ζ ^ 22 + ((27 / 4345) : ℂ) * ζ ^ 23 - ((741 / 8690) : ℂ) * ζ ^ 24 + ((379 / 17380) : ℂ) * ζ ^ 25 + ((173 / 790) : ℂ) * ζ ^ 26 - ((119 / 8690) : ℂ) * ζ ^ 27 - ((2791 / 17380) : ℂ) * ζ ^ 28 - ((12 / 869) : ℂ) * ζ ^ 29 + ((551 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_3_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 3 =
      (-((2199 / 17380) : ℂ) + ((2147 / 17380) : ℂ) * ζ ^ 1 + ((181 / 1580) : ℂ) * ζ ^ 2 + ((633 / 4345) : ℂ) * ζ ^ 3 + ((1951 / 17380) : ℂ) * ζ ^ 5 - ((21 / 1580) : ℂ) * ζ ^ 6 + ((588 / 4345) : ℂ) * ζ ^ 8 + ((1733 / 8690) : ℂ) * ζ ^ 9 + ((131 / 4345) : ℂ) * ζ ^ 11 - ((846 / 4345) : ℂ) * ζ ^ 12 - ((2147 / 17380) : ℂ) * ζ ^ 13 - ((883 / 17380) : ℂ) * ζ ^ 15 - ((2147 / 17380) : ℂ) * ζ ^ 17 - ((1 / 10) : ℂ) * ζ ^ 18 + ((183 / 8690) : ℂ) * ζ ^ 21 - ((181 / 1580) : ℂ) * ζ ^ 22 - ((9 / 8690) : ℂ) * ζ ^ 24 + ((49 / 4345) : ℂ) * ζ ^ 25 - ((559 / 4345) : ℂ) * ζ ^ 27 - ((588 / 4345) : ℂ) * ζ ^ 28 + ((2147 / 17380) : ℂ) * ζ ^ 29 - ((293 / 1580) : ℂ) * ζ ^ 30 - ((131 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((97 / 790) : ℂ) - ((229 / 1580) : ℂ) * ζ ^ 1 - ((1543 / 17380) : ℂ) * ζ ^ 2 - ((1073 / 4345) : ℂ) * ζ ^ 3 - ((71 / 1738) : ℂ) * ζ ^ 4 + ((4319 / 17380) : ℂ) * ζ ^ 5 + ((849 / 17380) : ℂ) * ζ ^ 6 + ((919 / 4345) : ℂ) * ζ ^ 7 - ((195 / 869) : ℂ) * ζ ^ 8 - ((1253 / 4345) : ℂ) * ζ ^ 9 + ((47 / 3476) : ℂ) * ζ ^ 10 - ((97 / 4345) : ℂ) * ζ ^ 11 + ((1159 / 3476) : ℂ) * ζ ^ 12 - ((2333 / 17380) : ℂ) * ζ ^ 13 - ((189 / 869) : ℂ) * ζ ^ 14 + ((177 / 1580) : ℂ) * ζ ^ 15 - ((877 / 8690) : ℂ) * ζ ^ 16 + ((761 / 8690) : ℂ) * ζ ^ 17 - ((358 / 4345) : ℂ) * ζ ^ 18 + ((1841 / 17380) : ℂ) * ζ ^ 19 + ((2141 / 17380) : ℂ) * ζ ^ 20 - ((1827 / 4345) : ℂ) * ζ ^ 21 + ((161 / 869) : ℂ) * ζ ^ 22 + ((1039 / 17380) : ℂ) * ζ ^ 23 + ((24 / 869) : ℂ) * ζ ^ 24 - ((573 / 17380) : ℂ) * ζ ^ 25 + ((813 / 17380) : ℂ) * ζ ^ 26 - ((174 / 4345) : ℂ) * ζ ^ 27 - ((2533 / 17380) : ℂ) * ζ ^ 28 + ((2631 / 17380) : ℂ) * ζ ^ 29 + ((651 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_3_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 3 =
      (((213 / 1580) : ℂ) + ((301 / 1738) : ℂ) * ζ ^ 1 - ((2839 / 17380) : ℂ) * ζ ^ 2 - ((1833 / 8690) : ℂ) * ζ ^ 3 + ((423 / 3476) : ℂ) * ζ ^ 5 - ((4021 / 17380) : ℂ) * ζ ^ 6 - ((96 / 395) : ℂ) * ζ ^ 8 - ((579 / 3476) : ℂ) * ζ ^ 9 - ((1017 / 17380) : ℂ) * ζ ^ 11 - ((377 / 1580) : ℂ) * ζ ^ 12 - ((301 / 1738) : ℂ) * ζ ^ 13 - ((1981 / 17380) : ℂ) * ζ ^ 15 - ((301 / 1738) : ℂ) * ζ ^ 17 + ((1807 / 17380) : ℂ) * ζ ^ 18 - ((703 / 3476) : ℂ) * ζ ^ 21 + ((2839 / 17380) : ℂ) * ζ ^ 22 + ((131 / 1580) : ℂ) * ζ ^ 24 + ((179 / 3476) : ℂ) * ζ ^ 25 - ((278 / 4345) : ℂ) * ζ ^ 27 + ((96 / 395) : ℂ) * ζ ^ 28 + ((301 / 1738) : ℂ) * ζ ^ 29 - ((819 / 8690) : ℂ) * ζ ^ 30 + ((1017 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((2693 / 17380) : ℂ) - ((1212 / 4345) : ℂ) * ζ ^ 1 + ((83 / 17380) : ℂ) * ζ ^ 2 + ((387 / 8690) : ℂ) * ζ ^ 3 + ((1699 / 17380) : ℂ) * ζ ^ 4 + ((1247 / 17380) : ℂ) * ζ ^ 5 + ((133 / 1580) : ℂ) * ζ ^ 6 - ((4483 / 17380) : ℂ) * ζ ^ 7 - ((1255 / 3476) : ℂ) * ζ ^ 8 - ((177 / 17380) : ℂ) * ζ ^ 9 - ((1173 / 17380) : ℂ) * ζ ^ 10 + ((655 / 1738) : ℂ) * ζ ^ 11 - ((3 / 395) : ℂ) * ζ ^ 12 + ((1917 / 17380) : ℂ) * ζ ^ 13 - ((1239 / 17380) : ℂ) * ζ ^ 14 - ((719 / 17380) : ℂ) * ζ ^ 15 - ((839 / 4345) : ℂ) * ζ ^ 16 + ((751 / 8690) : ℂ) * ζ ^ 17 - ((1839 / 17380) : ℂ) * ζ ^ 18 + ((809 / 17380) : ℂ) * ζ ^ 19 + ((41 / 17380) : ℂ) * ζ ^ 20 + ((328 / 4345) : ℂ) * ζ ^ 21 + ((17 / 395) : ℂ) * ζ ^ 22 - ((709 / 17380) : ℂ) * ζ ^ 23 + ((2261 / 17380) : ℂ) * ζ ^ 24 - ((2471 / 17380) : ℂ) * ζ ^ 25 + ((1851 / 17380) : ℂ) * ζ ^ 26 - ((555 / 3476) : ℂ) * ζ ^ 27 + ((3 / 79) : ℂ) * ζ ^ 28 - ((64 / 869) : ℂ) * ζ ^ 29 + ((64 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_3_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 3 =
      (((47 / 1580) : ℂ) - ((471 / 1580) : ℂ) * ζ ^ 1 + ((379 / 1580) : ℂ) * ζ ^ 2 + ((29 / 790) : ℂ) * ζ ^ 3 + ((1 / 790) : ℂ) * ζ ^ 5 + ((84 / 395) : ℂ) * ζ ^ 6 + ((76 / 395) : ℂ) * ζ ^ 8 + ((221 / 790) : ℂ) * ζ ^ 9 + ((113 / 790) : ℂ) * ζ ^ 11 + ((231 / 790) : ℂ) * ζ ^ 12 + ((471 / 1580) : ℂ) * ζ ^ 13 + ((89 / 790) : ℂ) * ζ ^ 15 + ((471 / 1580) : ℂ) * ζ ^ 17 + ((43 / 1580) : ℂ) * ζ ^ 18 + ((123 / 395) : ℂ) * ζ ^ 21 - ((379 / 1580) : ℂ) * ζ ^ 22 - ((1 / 5) : ℂ) * ζ ^ 24 - ((473 / 1580) : ℂ) * ζ ^ 25 + ((61 / 1580) : ℂ) * ζ ^ 27 - ((76 / 395) : ℂ) * ζ ^ 28 - ((471 / 1580) : ℂ) * ζ ^ 29 - ((227 / 1580) : ℂ) * ζ ^ 30 - ((113 / 790) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((169 / 1580) : ℂ) + ((217 / 1580) : ℂ) * ζ ^ 1 - ((14 / 79) : ℂ) * ζ ^ 2 - ((7 / 790) : ℂ) * ζ ^ 3 + ((231 / 790) : ℂ) * ζ ^ 4 - ((1 / 10) : ℂ) * ζ ^ 5 - ((173 / 1580) : ℂ) * ζ ^ 6 - ((3 / 20) : ℂ) * ζ ^ 7 - ((63 / 316) : ℂ) * ζ ^ 8 + ((283 / 1580) : ℂ) * ζ ^ 9 - ((6 / 395) : ℂ) * ζ ^ 10 + ((157 / 790) : ℂ) * ζ ^ 11 - ((369 / 1580) : ℂ) * ζ ^ 12 - ((39 / 316) : ℂ) * ζ ^ 13 - ((311 / 790) : ℂ) * ζ ^ 14 - ((14 / 395) : ℂ) * ζ ^ 15 + ((399 / 1580) : ℂ) * ζ ^ 16 - ((123 / 1580) : ℂ) * ζ ^ 17 - ((383 / 1580) : ℂ) * ζ ^ 18 + ((91 / 790) : ℂ) * ζ ^ 19 - ((57 / 158) : ℂ) * ζ ^ 20 - ((573 / 1580) : ℂ) * ζ ^ 21 - ((87 / 790) : ℂ) * ζ ^ 22 + ((113 / 790) : ℂ) * ζ ^ 23 + ((97 / 1580) : ℂ) * ζ ^ 24 - ((25 / 158) : ℂ) * ζ ^ 25 + ((9 / 1580) : ℂ) * ζ ^ 26 - ((293 / 1580) : ℂ) * ζ ^ 27 + ((6 / 79) : ℂ) * ζ ^ 28 - ((23 / 395) : ℂ) * ζ ^ 29 + ((12 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_3_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 3 =
      (((1201 / 8690) : ℂ) - ((1391 / 17380) : ℂ) * ζ ^ 1 - ((727 / 4345) : ℂ) * ζ ^ 2 + ((327 / 3476) : ℂ) * ζ ^ 3 + ((397 / 17380) : ℂ) * ζ ^ 5 - ((1321 / 8690) : ℂ) * ζ ^ 6 - ((1471 / 17380) : ℂ) * ζ ^ 8 + ((493 / 4345) : ℂ) * ζ ^ 9 - ((225 / 3476) : ℂ) * ζ ^ 11 - ((839 / 8690) : ℂ) * ζ ^ 12 + ((1391 / 17380) : ℂ) * ζ ^ 13 + ((351 / 3476) : ℂ) * ζ ^ 15 + ((1391 / 17380) : ℂ) * ζ ^ 17 + ((256 / 4345) : ℂ) * ζ ^ 18 - ((563 / 17380) : ℂ) * ζ ^ 21 + ((727 / 4345) : ℂ) * ζ ^ 22 + ((3349 / 17380) : ℂ) * ζ ^ 24 - ((447 / 4345) : ℂ) * ζ ^ 25 - ((25 / 869) : ℂ) * ζ ^ 27 + ((1471 / 17380) : ℂ) * ζ ^ 28 - ((1391 / 17380) : ℂ) * ζ ^ 29 + ((1 / 4345) : ℂ) * ζ ^ 30 + ((225 / 3476) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((2429 / 17380) : ℂ) + ((7 / 316) : ℂ) * ζ ^ 1 + ((292 / 4345) : ℂ) * ζ ^ 2 - ((279 / 4345) : ℂ) * ζ ^ 3 + ((2377 / 17380) : ℂ) * ζ ^ 4 - ((1431 / 8690) : ℂ) * ζ ^ 5 - ((1319 / 17380) : ℂ) * ζ ^ 6 + ((207 / 3476) : ℂ) * ζ ^ 7 + ((4087 / 17380) : ℂ) * ζ ^ 8 - ((1577 / 17380) : ℂ) * ζ ^ 9 + ((59 / 869) : ℂ) * ζ ^ 10 - ((2357 / 8690) : ℂ) * ζ ^ 11 + ((1163 / 17380) : ℂ) * ζ ^ 12 + ((124 / 869) : ℂ) * ζ ^ 13 + ((5031 / 17380) : ℂ) * ζ ^ 14 - ((169 / 8690) : ℂ) * ζ ^ 15 + ((1081 / 8690) : ℂ) * ζ ^ 16 - ((1006 / 4345) : ℂ) * ζ ^ 17 - ((613 / 17380) : ℂ) * ζ ^ 18 + ((69 / 3476) : ℂ) * ζ ^ 19 + ((193 / 3476) : ℂ) * ζ ^ 20 + ((993 / 17380) : ℂ) * ζ ^ 21 + ((841 / 8690) : ℂ) * ζ ^ 22 + ((2383 / 17380) : ℂ) * ζ ^ 23 - ((1134 / 4345) : ℂ) * ζ ^ 24 + ((2621 / 17380) : ℂ) * ζ ^ 25 - ((169 / 869) : ℂ) * ζ ^ 26 + ((3067 / 8690) : ℂ) * ζ ^ 27 - ((1511 / 17380) : ℂ) * ζ ^ 28 - ((164 / 4345) : ℂ) * ζ ^ 29 - ((9 / 55) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_3_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 3 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_3_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 3 =
      (-((41 / 220) : ℂ) + ((6 / 55) : ℂ) * ζ ^ 1 + ((27 / 220) : ℂ) * ζ ^ 2 - ((21 / 110) : ℂ) * ζ ^ 3 - ((9 / 110) : ℂ) * ζ ^ 5 + ((63 / 220) : ℂ) * ζ ^ 6 + ((19 / 110) : ℂ) * ζ ^ 8 - ((43 / 220) : ℂ) * ζ ^ 9 - ((1 / 55) : ℂ) * ζ ^ 11 + ((89 / 220) : ℂ) * ζ ^ 12 - ((6 / 55) : ℂ) * ζ ^ 13 + ((2 / 55) : ℂ) * ζ ^ 15 - ((6 / 55) : ℂ) * ζ ^ 17 - ((13 / 110) : ℂ) * ζ ^ 18 - ((2 / 55) : ℂ) * ζ ^ 21 - ((27 / 220) : ℂ) * ζ ^ 22 - ((8 / 55) : ℂ) * ζ ^ 24 + ((21 / 110) : ℂ) * ζ ^ 25 - ((7 / 110) : ℂ) * ζ ^ 27 - ((19 / 110) : ℂ) * ζ ^ 28 + ((6 / 55) : ℂ) * ζ ^ 29 + ((39 / 220) : ℂ) * ζ ^ 30 + ((1 / 55) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((41 / 220) : ℂ) - ((6 / 55) : ℂ) * ζ ^ 1 - ((27 / 220) : ℂ) * ζ ^ 2)

private theorem row18_transformedGeneratorA_term_3_3_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 3 =
      (-((27 / 220) : ℂ) - ((9 / 220) : ℂ) * ζ ^ 1 + ((7 / 55) : ℂ) * ζ ^ 2 - ((6 / 55) : ℂ) * ζ ^ 3 - ((7 / 220) : ℂ) * ζ ^ 5 - ((2 / 55) : ℂ) * ζ ^ 6 - ((17 / 110) : ℂ) * ζ ^ 8 + ((23 / 220) : ℂ) * ζ ^ 9 + ((37 / 220) : ℂ) * ζ ^ 11 + ((13 / 220) : ℂ) * ζ ^ 12 + ((9 / 220) : ℂ) * ζ ^ 13 + ((9 / 55) : ℂ) * ζ ^ 15 + ((9 / 220) : ℂ) * ζ ^ 17 - ((29 / 220) : ℂ) * ζ ^ 18 - ((13 / 55) : ℂ) * ζ ^ 21 - ((7 / 55) : ℂ) * ζ ^ 22 - ((9 / 220) : ℂ) * ζ ^ 24 - ((1 / 110) : ℂ) * ζ ^ 25 - ((2 / 55) : ℂ) * ζ ^ 27 + ((17 / 110) : ℂ) * ζ ^ 28 - ((9 / 220) : ℂ) * ζ ^ 29 + ((4 / 55) : ℂ) * ζ ^ 30 - ((37 / 220) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_3_3 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        3 3 =
      alternatingSixAmbientRow18TransformedGeneratorA
        3 3 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_3_3_0,
      row18_transformedGeneratorA_term_3_3_1,
      row18_transformedGeneratorA_term_3_3_2,
      row18_transformedGeneratorA_term_3_3_3,
      row18_transformedGeneratorA_term_3_3_4,
      row18_transformedGeneratorA_term_3_3_5,
      row18_transformedGeneratorA_term_3_3_6,
      row18_transformedGeneratorA_term_3_3_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_4_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 4 =
      (((141 / 1580) : ℂ) + ((17 / 4345) : ℂ) * ζ ^ 1 + ((773 / 8690) : ℂ) * ζ ^ 2 - ((31 / 220) : ℂ) * ζ ^ 3 + ((829 / 17380) : ℂ) * ζ ^ 5 + ((2049 / 17380) : ℂ) * ζ ^ 6 + ((57 / 1580) : ℂ) * ζ ^ 8 - ((2331 / 17380) : ℂ) * ζ ^ 9 + ((383 / 4345) : ℂ) * ζ ^ 11 - ((26 / 395) : ℂ) * ζ ^ 12 - ((17 / 4345) : ℂ) * ζ ^ 13 + ((173 / 8690) : ℂ) * ζ ^ 15 - ((17 / 4345) : ℂ) * ζ ^ 17 - ((87 / 4345) : ℂ) * ζ ^ 18 - ((323 / 8690) : ℂ) * ζ ^ 21 - ((773 / 8690) : ℂ) * ζ ^ 22 + ((147 / 1580) : ℂ) * ζ ^ 24 - ((761 / 17380) : ℂ) * ζ ^ 25 - ((1279 / 8690) : ℂ) * ζ ^ 27 - ((57 / 1580) : ℂ) * ζ ^ 28 + ((17 / 4345) : ℂ) * ζ ^ 29 + ((818 / 4345) : ℂ) * ζ ^ 30 - ((383 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((259 / 3476) : ℂ) + ((227 / 4345) : ℂ) * ζ ^ 1 - ((67 / 4345) : ℂ) * ζ ^ 2 + ((777 / 3476) : ℂ) * ζ ^ 3 + ((2901 / 17380) : ℂ) * ζ ^ 4 - ((29 / 17380) : ℂ) * ζ ^ 5 + ((216 / 4345) : ℂ) * ζ ^ 6 - ((145 / 1738) : ℂ) * ζ ^ 7 - ((449 / 8690) : ℂ) * ζ ^ 8 + ((1409 / 8690) : ℂ) * ζ ^ 9 - ((57 / 1738) : ℂ) * ζ ^ 10 + ((557 / 8690) : ℂ) * ζ ^ 11 - ((41 / 790) : ℂ) * ζ ^ 12 - ((1433 / 17380) : ℂ) * ζ ^ 13 - ((278 / 4345) : ℂ) * ζ ^ 14 - ((311 / 8690) : ℂ) * ζ ^ 15 - ((327 / 4345) : ℂ) * ζ ^ 16 + ((81 / 790) : ℂ) * ζ ^ 17 - ((733 / 8690) : ℂ) * ζ ^ 18 - ((289 / 8690) : ℂ) * ζ ^ 19 + ((61 / 3476) : ℂ) * ζ ^ 20 + ((127 / 17380) : ℂ) * ζ ^ 21 - ((183 / 4345) : ℂ) * ζ ^ 22 + ((327 / 3476) : ℂ) * ζ ^ 23 - ((381 / 8690) : ℂ) * ζ ^ 24 - ((349 / 8690) : ℂ) * ζ ^ 25 - ((202 / 4345) : ℂ) * ζ ^ 26 + ((29 / 869) : ℂ) * ζ ^ 27 + ((348 / 4345) : ℂ) * ζ ^ 28 + ((16 / 869) : ℂ) * ζ ^ 29 - ((1189 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_4_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 4 =
      (((1351 / 8690) : ℂ) - ((31 / 220) : ℂ) * ζ ^ 1 - ((131 / 1738) : ℂ) * ζ ^ 2 + ((283 / 8690) : ℂ) * ζ ^ 3 - ((381 / 8690) : ℂ) * ζ ^ 5 - ((107 / 869) : ℂ) * ζ ^ 6 + ((349 / 17380) : ℂ) * ζ ^ 8 - ((1637 / 17380) : ℂ) * ζ ^ 9 - ((162 / 4345) : ℂ) * ζ ^ 11 - ((257 / 4345) : ℂ) * ζ ^ 12 + ((31 / 220) : ℂ) * ζ ^ 13 + ((709 / 4345) : ℂ) * ζ ^ 15 + ((31 / 220) : ℂ) * ζ ^ 17 + ((885 / 3476) : ℂ) * ζ ^ 18 + ((1953 / 17380) : ℂ) * ζ ^ 21 + ((131 / 1738) : ℂ) * ζ ^ 22 - ((334 / 4345) : ℂ) * ζ ^ 24 - ((1687 / 17380) : ℂ) * ζ ^ 25 - ((749 / 8690) : ℂ) * ζ ^ 27 - ((349 / 17380) : ℂ) * ζ ^ 28 - ((31 / 220) : ℂ) * ζ ^ 29 - ((651 / 3476) : ℂ) * ζ ^ 30 + ((162 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1429 / 8690) : ℂ) + ((2617 / 17380) : ℂ) * ζ ^ 1 + ((39 / 1580) : ℂ) * ζ ^ 2 - ((69 / 8690) : ℂ) * ζ ^ 3 + ((1189 / 8690) : ℂ) * ζ ^ 4 - ((1149 / 17380) : ℂ) * ζ ^ 5 + ((499 / 4345) : ℂ) * ζ ^ 6 - ((311 / 3476) : ℂ) * ζ ^ 7 - ((175 / 3476) : ℂ) * ζ ^ 8 + ((2517 / 17380) : ℂ) * ζ ^ 9 - ((235 / 3476) : ℂ) * ζ ^ 10 - ((285 / 3476) : ℂ) * ζ ^ 11 - ((361 / 8690) : ℂ) * ζ ^ 12 - ((563 / 8690) : ℂ) * ζ ^ 13 + ((929 / 8690) : ℂ) * ζ ^ 14 - ((1667 / 8690) : ℂ) * ζ ^ 15 + ((351 / 8690) : ℂ) * ζ ^ 16 + ((513 / 17380) : ℂ) * ζ ^ 17 - ((97 / 17380) : ℂ) * ζ ^ 18 + ((1747 / 17380) : ℂ) * ζ ^ 19 + ((307 / 17380) : ℂ) * ζ ^ 20 + ((1977 / 17380) : ℂ) * ζ ^ 21 - ((64 / 869) : ℂ) * ζ ^ 22 + ((203 / 17380) : ℂ) * ζ ^ 23 + ((17 / 869) : ℂ) * ζ ^ 24 - ((13 / 395) : ℂ) * ζ ^ 25 - ((221 / 17380) : ℂ) * ζ ^ 26 - ((19 / 4345) : ℂ) * ζ ^ 27 + ((27 / 869) : ℂ) * ζ ^ 28 - ((9 / 4345) : ℂ) * ζ ^ 29 - ((84 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_4_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 4 =
      (-((488 / 4345) : ℂ) - ((1751 / 8690) : ℂ) * ζ ^ 1 - ((31 / 790) : ℂ) * ζ ^ 2 - ((1533 / 17380) : ℂ) * ζ ^ 3 - ((701 / 17380) : ℂ) * ζ ^ 5 - ((22 / 395) : ℂ) * ζ ^ 6 + ((19 / 4345) : ℂ) * ζ ^ 8 + ((1957 / 8690) : ℂ) * ζ ^ 9 - ((229 / 4345) : ℂ) * ζ ^ 11 + ((343 / 17380) : ℂ) * ζ ^ 12 + ((1751 / 8690) : ℂ) * ζ ^ 13 + ((3 / 220) : ℂ) * ζ ^ 15 + ((1751 / 8690) : ℂ) * ζ ^ 17 - ((199 / 1580) : ℂ) * ζ ^ 18 - ((501 / 17380) : ℂ) * ζ ^ 21 + ((31 / 790) : ℂ) * ζ ^ 22 - ((1549 / 17380) : ℂ) * ζ ^ 24 - ((2801 / 17380) : ℂ) * ζ ^ 25 + ((699 / 17380) : ℂ) * ζ ^ 27 - ((19 / 4345) : ℂ) * ζ ^ 28 - ((1751 / 8690) : ℂ) * ζ ^ 29 + ((51 / 1580) : ℂ) * ζ ^ 30 + ((229 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((488 / 4345) : ℂ) + ((3733 / 17380) : ℂ) * ζ ^ 1 + ((1 / 10) : ℂ) * ζ ^ 2 + ((2523 / 17380) : ℂ) * ζ ^ 3 - ((547 / 8690) : ℂ) * ζ ^ 4 - ((1207 / 8690) : ℂ) * ζ ^ 5 + ((2149 / 17380) : ℂ) * ζ ^ 6 - ((63 / 3476) : ℂ) * ζ ^ 7 - ((12 / 4345) : ℂ) * ζ ^ 8 + ((493 / 8690) : ℂ) * ζ ^ 9 - ((2271 / 17380) : ℂ) * ζ ^ 10 + ((2083 / 17380) : ℂ) * ζ ^ 11 - ((3439 / 17380) : ℂ) * ζ ^ 12 + ((268 / 4345) : ℂ) * ζ ^ 13 + ((87 / 17380) : ℂ) * ζ ^ 14 - ((2669 / 17380) : ℂ) * ζ ^ 15 - ((153 / 4345) : ℂ) * ζ ^ 16 - ((718 / 4345) : ℂ) * ζ ^ 17 - ((233 / 17380) : ℂ) * ζ ^ 18 + ((67 / 4345) : ℂ) * ζ ^ 19 - ((271 / 3476) : ℂ) * ζ ^ 20 + ((1361 / 17380) : ℂ) * ζ ^ 21 + ((873 / 17380) : ℂ) * ζ ^ 22 - ((1547 / 17380) : ℂ) * ζ ^ 23 + ((1747 / 8690) : ℂ) * ζ ^ 24 - ((199 / 1580) : ℂ) * ζ ^ 25 + ((3057 / 17380) : ℂ) * ζ ^ 26 - ((833 / 8690) : ℂ) * ζ ^ 27 + ((621 / 8690) : ℂ) * ζ ^ 28 - ((18 / 869) : ℂ) * ζ ^ 29 + ((48 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_4_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 4 =
      (-((63 / 790) : ℂ) + ((13 / 316) : ℂ) * ζ ^ 1 - ((39 / 790) : ℂ) * ζ ^ 2 + ((3 / 395) : ℂ) * ζ ^ 3 - ((27 / 316) : ℂ) * ζ ^ 5 + ((19 / 790) : ℂ) * ζ ^ 6 - ((77 / 1580) : ℂ) * ζ ^ 8 + ((3 / 79) : ℂ) * ζ ^ 9 - ((51 / 1580) : ℂ) * ζ ^ 11 - ((41 / 1580) : ℂ) * ζ ^ 12 - ((13 / 316) : ℂ) * ζ ^ 13 - ((183 / 1580) : ℂ) * ζ ^ 15 - ((13 / 316) : ℂ) * ζ ^ 17 + ((37 / 790) : ℂ) * ζ ^ 18 - ((5 / 79) : ℂ) * ζ ^ 21 + ((39 / 790) : ℂ) * ζ ^ 22 + ((53 / 1580) : ℂ) * ζ ^ 24 + ((10 / 79) : ℂ) * ζ ^ 25 + ((69 / 1580) : ℂ) * ζ ^ 27 + ((77 / 1580) : ℂ) * ζ ^ 28 + ((13 / 316) : ℂ) * ζ ^ 29 + ((9 / 1580) : ℂ) * ζ ^ 30 + ((51 / 1580) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((119 / 790) : ℂ) + ((37 / 316) : ℂ) * ζ ^ 1 - ((7 / 158) : ℂ) * ζ ^ 2 - ((133 / 1580) : ℂ) * ζ ^ 3 - ((127 / 1580) : ℂ) * ζ ^ 4 - ((171 / 1580) : ℂ) * ζ ^ 5 - ((3 / 790) : ℂ) * ζ ^ 6 - ((13 / 316) : ℂ) * ζ ^ 7 + ((29 / 316) : ℂ) * ζ ^ 8 - ((13 / 395) : ℂ) * ζ ^ 9 - ((81 / 1580) : ℂ) * ζ ^ 10 - ((32 / 395) : ℂ) * ζ ^ 11 - ((14 / 395) : ℂ) * ζ ^ 12 + ((29 / 790) : ℂ) * ζ ^ 13 - ((35 / 316) : ℂ) * ζ ^ 14 + ((151 / 790) : ℂ) * ζ ^ 15 + ((1 / 20) : ℂ) * ζ ^ 16 + ((137 / 1580) : ℂ) * ζ ^ 17 - ((1 / 790) : ℂ) * ζ ^ 18 - ((147 / 1580) : ℂ) * ζ ^ 19 + ((151 / 1580) : ℂ) * ζ ^ 20 + ((51 / 316) : ℂ) * ζ ^ 21 - ((37 / 316) : ℂ) * ζ ^ 22 + ((223 / 1580) : ℂ) * ζ ^ 23 + ((11 / 158) : ℂ) * ζ ^ 24 + ((77 / 790) : ℂ) * ζ ^ 25 - ((47 / 790) : ℂ) * ζ ^ 26 - ((97 / 1580) : ℂ) * ζ ^ 27 + ((117 / 790) : ℂ) * ζ ^ 28 - ((27 / 395) : ℂ) * ζ ^ 29 + ((22 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_4_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 4 =
      (((39 / 1738) : ℂ) + ((3293 / 17380) : ℂ) * ζ ^ 1 + ((116 / 4345) : ℂ) * ζ ^ 2 + ((119 / 1580) : ℂ) * ζ ^ 3 + ((486 / 4345) : ℂ) * ζ ^ 5 - ((357 / 8690) : ℂ) * ζ ^ 6 - ((233 / 3476) : ℂ) * ζ ^ 8 - ((1571 / 17380) : ℂ) * ζ ^ 9 - ((37 / 1580) : ℂ) * ζ ^ 11 - ((75 / 1738) : ℂ) * ζ ^ 12 - ((3293 / 17380) : ℂ) * ζ ^ 13 - ((71 / 1580) : ℂ) * ζ ^ 15 - ((3293 / 17380) : ℂ) * ζ ^ 17 - ((513 / 4345) : ℂ) * ζ ^ 18 - ((723 / 8690) : ℂ) * ζ ^ 21 - ((116 / 4345) : ℂ) * ζ ^ 22 - ((117 / 3476) : ℂ) * ζ ^ 24 + ((1349 / 17380) : ℂ) * ζ ^ 25 - ((18 / 395) : ℂ) * ζ ^ 27 + ((233 / 3476) : ℂ) * ζ ^ 28 + ((3293 / 17380) : ℂ) * ζ ^ 29 + ((603 / 17380) : ℂ) * ζ ^ 30 + ((37 / 1580) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((399 / 17380) : ℂ) - ((723 / 3476) : ℂ) * ζ ^ 1 - ((139 / 4345) : ℂ) * ζ ^ 2 - ((148 / 4345) : ℂ) * ζ ^ 3 - ((21 / 17380) : ℂ) * ζ ^ 4 + ((669 / 17380) : ℂ) * ζ ^ 5 + ((1091 / 17380) : ℂ) * ζ ^ 6 + ((1383 / 17380) : ℂ) * ζ ^ 7 + ((229 / 4345) : ℂ) * ζ ^ 8 - ((35 / 1738) : ℂ) * ζ ^ 9 - ((369 / 1738) : ℂ) * ζ ^ 10 - ((2913 / 17380) : ℂ) * ζ ^ 11 - ((323 / 4345) : ℂ) * ζ ^ 12 + ((127 / 1580) : ℂ) * ζ ^ 13 + ((181 / 1738) : ℂ) * ζ ^ 14 + ((77 / 1580) : ℂ) * ζ ^ 15 - ((827 / 17380) : ℂ) * ζ ^ 16 - ((1637 / 17380) : ℂ) * ζ ^ 17 + ((113 / 17380) : ℂ) * ζ ^ 18 + ((27 / 3476) : ℂ) * ζ ^ 19 + ((351 / 3476) : ℂ) * ζ ^ 20 - ((647 / 17380) : ℂ) * ζ ^ 21 - ((29 / 395) : ℂ) * ζ ^ 22 - ((463 / 4345) : ℂ) * ζ ^ 23 - ((206 / 4345) : ℂ) * ζ ^ 24 + ((1081 / 17380) : ℂ) * ζ ^ 25 + ((353 / 4345) : ℂ) * ζ ^ 26 + ((339 / 3476) : ℂ) * ζ ^ 27 + ((27 / 1580) : ℂ) * ζ ^ 28 - ((1 / 395) : ℂ) * ζ ^ 29 - ((63 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_4_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 4 =
      (-((1 / 11) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 1 + ((7 / 44) : ℂ) * ζ ^ 2 + ((5 / 44) : ℂ) * ζ ^ 3 + ((1 / 44) : ℂ) * ζ ^ 5 + ((9 / 44) : ℂ) * ζ ^ 6 + ((2 / 11) : ℂ) * ζ ^ 8 + ((3 / 44) : ℂ) * ζ ^ 9 - ((5 / 22) : ℂ) * ζ ^ 11 + ((3 / 22) : ℂ) * ζ ^ 12 + ((5 / 44) : ℂ) * ζ ^ 13 - ((1 / 22) : ℂ) * ζ ^ 15 + ((5 / 44) : ℂ) * ζ ^ 17 + ((1 / 44) : ℂ) * ζ ^ 18 + ((9 / 44) : ℂ) * ζ ^ 21 - ((7 / 44) : ℂ) * ζ ^ 22 - ((5 / 44) : ℂ) * ζ ^ 24 - ((3 / 22) : ℂ) * ζ ^ 25 + ((9 / 44) : ℂ) * ζ ^ 27 - ((2 / 11) : ℂ) * ζ ^ 28 - ((5 / 44) : ℂ) * ζ ^ 29 + ((1 / 11) : ℂ) * ζ ^ 30 + ((5 / 22) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_4_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 4 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_4_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 4 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_3_4 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        3 4 =
      alternatingSixAmbientRow18TransformedGeneratorA
        3 4 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_3_4_0,
      row18_transformedGeneratorA_term_3_4_1,
      row18_transformedGeneratorA_term_3_4_2,
      row18_transformedGeneratorA_term_3_4_3,
      row18_transformedGeneratorA_term_3_4_4,
      row18_transformedGeneratorA_term_3_4_5,
      row18_transformedGeneratorA_term_3_4_6,
      row18_transformedGeneratorA_term_3_4_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_5_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 5 =
      (((1421 / 8690) : ℂ) + ((169 / 1738) : ℂ) * ζ ^ 1 - ((4469 / 17380) : ℂ) * ζ ^ 2 + ((2903 / 17380) : ℂ) * ζ ^ 3 + ((357 / 3476) : ℂ) * ζ ^ 5 - ((9 / 220) : ℂ) * ζ ^ 6 - ((1313 / 8690) : ℂ) * ζ ^ 8 - ((164 / 869) : ℂ) * ζ ^ 9 - ((676 / 4345) : ℂ) * ζ ^ 11 - ((5033 / 17380) : ℂ) * ζ ^ 12 - ((169 / 1738) : ℂ) * ζ ^ 13 - ((4657 / 17380) : ℂ) * ζ ^ 15 - ((169 / 1738) : ℂ) * ζ ^ 17 + ((3837 / 17380) : ℂ) * ζ ^ 18 + ((303 / 1738) : ℂ) * ζ ^ 21 + ((4469 / 17380) : ℂ) * ζ ^ 22 + ((6869 / 17380) : ℂ) * ζ ^ 24 - ((19 / 3476) : ℂ) * ζ ^ 25 + ((1371 / 17380) : ℂ) * ζ ^ 27 + ((1313 / 8690) : ℂ) * ζ ^ 28 + ((169 / 1738) : ℂ) * ζ ^ 29 - ((1599 / 8690) : ℂ) * ζ ^ 30 + ((676 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1349 / 8690) : ℂ) - ((344 / 4345) : ℂ) * ζ ^ 1 + ((4253 / 17380) : ℂ) * ζ ^ 2 - ((601 / 3476) : ℂ) * ζ ^ 3 + ((167 / 790) : ℂ) * ζ ^ 4 - ((51 / 8690) : ℂ) * ζ ^ 5 - ((5319 / 17380) : ℂ) * ζ ^ 6 + ((197 / 3476) : ℂ) * ζ ^ 7 - ((117 / 4345) : ℂ) * ζ ^ 8 + ((839 / 8690) : ℂ) * ζ ^ 9 + ((797 / 17380) : ℂ) * ζ ^ 10 - ((9 / 395) : ℂ) * ζ ^ 11 - ((663 / 17380) : ℂ) * ζ ^ 12 - ((4589 / 17380) : ℂ) * ζ ^ 13 + ((602 / 4345) : ℂ) * ζ ^ 14 + ((49 / 790) : ℂ) * ζ ^ 15 - ((933 / 4345) : ℂ) * ζ ^ 16 + ((3339 / 17380) : ℂ) * ζ ^ 17 - ((2547 / 17380) : ℂ) * ζ ^ 18 - ((1031 / 17380) : ℂ) * ζ ^ 19 + ((2643 / 17380) : ℂ) * ζ ^ 20 - ((3371 / 17380) : ℂ) * ζ ^ 21 + ((403 / 4345) : ℂ) * ζ ^ 22 + ((281 / 1738) : ℂ) * ζ ^ 23 - ((3511 / 17380) : ℂ) * ζ ^ 24 + ((101 / 8690) : ℂ) * ζ ^ 25 - ((59 / 17380) : ℂ) * ζ ^ 26 - ((591 / 17380) : ℂ) * ζ ^ 27 + ((477 / 4345) : ℂ) * ζ ^ 28 + ((223 / 17380) : ℂ) * ζ ^ 29 - ((1073 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_5_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 5 =
      (-((497 / 8690) : ℂ) + ((607 / 1580) : ℂ) * ζ ^ 1 - ((679 / 17380) : ℂ) * ζ ^ 2 + ((3687 / 17380) : ℂ) * ζ ^ 3 + ((134 / 395) : ℂ) * ζ ^ 5 + ((537 / 8690) : ℂ) * ζ ^ 6 + ((5497 / 17380) : ℂ) * ζ ^ 8 - ((59 / 1580) : ℂ) * ζ ^ 9 + ((2229 / 17380) : ℂ) * ζ ^ 11 - ((41 / 220) : ℂ) * ζ ^ 12 - ((607 / 1580) : ℂ) * ζ ^ 13 - ((4843 / 17380) : ℂ) * ζ ^ 15 - ((607 / 1580) : ℂ) * ζ ^ 17 - ((82 / 4345) : ℂ) * ζ ^ 18 - ((57 / 790) : ℂ) * ζ ^ 21 + ((679 / 17380) : ℂ) * ζ ^ 22 + ((1227 / 17380) : ℂ) * ζ ^ 24 + ((71 / 1580) : ℂ) * ζ ^ 25 - ((2731 / 17380) : ℂ) * ζ ^ 27 - ((5497 / 17380) : ℂ) * ζ ^ 28 + ((607 / 1580) : ℂ) * ζ ^ 29 - ((7043 / 17380) : ℂ) * ζ ^ 30 - ((2229 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((929 / 17380) : ℂ) - ((675 / 1738) : ℂ) * ζ ^ 1 + ((181 / 17380) : ℂ) * ζ ^ 2 - ((3237 / 17380) : ℂ) * ζ ^ 3 - ((1589 / 8690) : ℂ) * ζ ^ 4 + ((5433 / 17380) : ℂ) * ζ ^ 5 - ((393 / 3476) : ℂ) * ζ ^ 6 + ((3313 / 17380) : ℂ) * ζ ^ 7 - ((1931 / 17380) : ℂ) * ζ ^ 8 - ((828 / 4345) : ℂ) * ζ ^ 9 + ((2041 / 17380) : ℂ) * ζ ^ 10 - ((669 / 17380) : ℂ) * ζ ^ 11 + ((2637 / 17380) : ℂ) * ζ ^ 12 - ((1093 / 17380) : ℂ) * ζ ^ 13 - ((1007 / 4345) : ℂ) * ζ ^ 14 + ((1737 / 17380) : ℂ) * ζ ^ 15 - ((1139 / 8690) : ℂ) * ζ ^ 16 + ((59 / 4345) : ℂ) * ζ ^ 17 - ((637 / 17380) : ℂ) * ζ ^ 18 - ((3 / 158) : ℂ) * ζ ^ 19 + ((379 / 1738) : ℂ) * ζ ^ 20 - ((1472 / 4345) : ℂ) * ζ ^ 21 + ((2349 / 17380) : ℂ) * ζ ^ 22 + ((153 / 1580) : ℂ) * ζ ^ 23 - ((113 / 3476) : ℂ) * ζ ^ 24 + ((533 / 17380) : ℂ) * ζ ^ 25 + ((1487 / 17380) : ℂ) * ζ ^ 26 - ((29 / 1580) : ℂ) * ζ ^ 27 - ((1037 / 17380) : ℂ) * ζ ^ 28 + ((621 / 4345) : ℂ) * ζ ^ 29 + ((504 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_5_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 5 =
      (((83 / 1738) : ℂ) - ((969 / 4345) : ℂ) * ζ ^ 1 + ((3129 / 17380) : ℂ) * ζ ^ 2 - ((4357 / 17380) : ℂ) * ζ ^ 3 + ((267 / 17380) : ℂ) * ζ ^ 5 + ((1361 / 17380) : ℂ) * ζ ^ 6 + ((137 / 869) : ℂ) * ζ ^ 8 + ((808 / 4345) : ℂ) * ζ ^ 9 + ((3401 / 17380) : ℂ) * ζ ^ 11 + ((719 / 3476) : ℂ) * ζ ^ 12 + ((969 / 4345) : ℂ) * ζ ^ 13 + ((2649 / 8690) : ℂ) * ζ ^ 15 + ((969 / 4345) : ℂ) * ζ ^ 17 - ((13 / 220) : ℂ) * ζ ^ 18 - ((1499 / 8690) : ℂ) * ζ ^ 21 - ((3129 / 17380) : ℂ) * ζ ^ 22 - ((953 / 3476) : ℂ) * ζ ^ 24 - ((4143 / 17380) : ℂ) * ζ ^ 25 - ((4789 / 17380) : ℂ) * ζ ^ 27 - ((137 / 869) : ℂ) * ζ ^ 28 - ((969 / 4345) : ℂ) * ζ ^ 29 + ((3603 / 17380) : ℂ) * ζ ^ 30 - ((3401 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((59 / 869) : ℂ) + ((1961 / 17380) : ℂ) * ζ ^ 1 - ((2877 / 8690) : ℂ) * ζ ^ 2 + ((747 / 3476) : ℂ) * ζ ^ 3 + ((3671 / 17380) : ℂ) * ζ ^ 4 - ((324 / 4345) : ℂ) * ζ ^ 5 + ((931 / 8690) : ℂ) * ζ ^ 6 + ((219 / 17380) : ℂ) * ζ ^ 7 + ((423 / 17380) : ℂ) * ζ ^ 8 + ((4313 / 17380) : ℂ) * ζ ^ 9 + ((1377 / 17380) : ℂ) * ζ ^ 10 + ((1329 / 17380) : ℂ) * ζ ^ 11 + ((2897 / 17380) : ℂ) * ζ ^ 12 + ((102 / 4345) : ℂ) * ζ ^ 13 + ((1963 / 17380) : ℂ) * ζ ^ 14 - ((39 / 316) : ℂ) * ζ ^ 15 + ((255 / 3476) : ℂ) * ζ ^ 16 - ((106 / 869) : ℂ) * ζ ^ 17 - ((1949 / 17380) : ℂ) * ζ ^ 18 - ((1269 / 17380) : ℂ) * ζ ^ 19 - ((568 / 4345) : ℂ) * ζ ^ 20 + ((1351 / 8690) : ℂ) * ζ ^ 21 + ((1993 / 17380) : ℂ) * ζ ^ 22 - ((1299 / 17380) : ℂ) * ζ ^ 23 + ((233 / 3476) : ℂ) * ζ ^ 24 - ((7 / 395) : ℂ) * ζ ^ 25 - ((3209 / 17380) : ℂ) * ζ ^ 26 + ((1073 / 8690) : ℂ) * ζ ^ 27 - ((2991 / 17380) : ℂ) * ζ ^ 28 + ((243 / 4345) : ℂ) * ζ ^ 29 - ((136 / 869) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_5_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 5 =
      (((102 / 395) : ℂ) - ((221 / 790) : ℂ) * ζ ^ 1 - ((84 / 395) : ℂ) * ζ ^ 2 + ((83 / 790) : ℂ) * ζ ^ 3 - ((531 / 1580) : ℂ) * ζ ^ 5 + ((171 / 1580) : ℂ) * ζ ^ 6 - ((141 / 395) : ℂ) * ζ ^ 8 + ((389 / 1580) : ℂ) * ζ ^ 9 - ((329 / 790) : ℂ) * ζ ^ 11 + ((29 / 790) : ℂ) * ζ ^ 12 + ((221 / 790) : ℂ) * ζ ^ 13 + ((31 / 1580) : ℂ) * ζ ^ 15 + ((221 / 790) : ℂ) * ζ ^ 17 + ((159 / 790) : ℂ) * ζ ^ 18 + ((297 / 790) : ℂ) * ζ ^ 21 + ((84 / 395) : ℂ) * ζ ^ 22 + ((411 / 1580) : ℂ) * ζ ^ 24 + ((89 / 1580) : ℂ) * ζ ^ 25 + ((381 / 790) : ℂ) * ζ ^ 27 + ((141 / 395) : ℂ) * ζ ^ 28 - ((221 / 790) : ℂ) * ζ ^ 29 + ((593 / 1580) : ℂ) * ζ ^ 30 + ((329 / 790) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((53 / 158) : ℂ) + ((57 / 395) : ℂ) * ζ ^ 1 + ((643 / 1580) : ℂ) * ζ ^ 2 - ((11 / 790) : ℂ) * ζ ^ 3 + ((419 / 1580) : ℂ) * ζ ^ 4 + ((26 / 79) : ℂ) * ζ ^ 5 - ((419 / 1580) : ℂ) * ζ ^ 6 + ((169 / 1580) : ℂ) * ζ ^ 7 + ((4 / 395) : ℂ) * ζ ^ 8 - ((99 / 395) : ℂ) * ζ ^ 9 + ((24 / 395) : ℂ) * ζ ^ 10 + ((38 / 395) : ℂ) * ζ ^ 11 - ((509 / 1580) : ℂ) * ζ ^ 12 + ((5 / 316) : ℂ) * ζ ^ 13 - ((25 / 158) : ℂ) * ζ ^ 14 - ((641 / 1580) : ℂ) * ζ ^ 15 - ((21 / 790) : ℂ) * ζ ^ 16 - ((61 / 316) : ℂ) * ζ ^ 17 - ((363 / 1580) : ℂ) * ζ ^ 18 + ((33 / 790) : ℂ) * ζ ^ 19 - ((13 / 316) : ℂ) * ζ ^ 20 - ((637 / 1580) : ℂ) * ζ ^ 21 - ((157 / 790) : ℂ) * ζ ^ 22 + ((107 / 1580) : ℂ) * ζ ^ 23 - ((99 / 395) : ℂ) * ζ ^ 24 - ((117 / 316) : ℂ) * ζ ^ 25 + ((109 / 316) : ℂ) * ζ ^ 26 - ((38 / 395) : ℂ) * ζ ^ 27 - ((88 / 395) : ℂ) * ζ ^ 28 + ((31 / 316) : ℂ) * ζ ^ 29 - ((87 / 790) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_5_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 5 =
      (-((2257 / 17380) : ℂ) + ((2689 / 17380) : ℂ) * ζ ^ 1 - ((585 / 3476) : ℂ) * ζ ^ 2 - ((1777 / 8690) : ℂ) * ζ ^ 3 + ((2177 / 17380) : ℂ) * ζ ^ 5 - ((89 / 3476) : ℂ) * ζ ^ 6 + ((13 / 8690) : ℂ) * ζ ^ 8 - ((3633 / 17380) : ℂ) * ζ ^ 9 + ((688 / 4345) : ℂ) * ζ ^ 11 - ((631 / 8690) : ℂ) * ζ ^ 12 - ((2689 / 17380) : ℂ) * ζ ^ 13 - ((166 / 4345) : ℂ) * ζ ^ 15 - ((2689 / 17380) : ℂ) * ζ ^ 17 - ((129 / 1738) : ℂ) * ζ ^ 18 - ((4123 / 17380) : ℂ) * ζ ^ 21 + ((585 / 3476) : ℂ) * ζ ^ 22 - ((101 / 4345) : ℂ) * ζ ^ 24 + ((128 / 4345) : ℂ) * ζ ^ 25 - ((4283 / 17380) : ℂ) * ζ ^ 27 - ((13 / 8690) : ℂ) * ζ ^ 28 + ((2689 / 17380) : ℂ) * ζ ^ 29 - ((126 / 869) : ℂ) * ζ ^ 30 - ((688 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((223 / 1738) : ℂ) - ((922 / 4345) : ℂ) * ζ ^ 1 + ((691 / 8690) : ℂ) * ζ ^ 2 + ((2201 / 17380) : ℂ) * ζ ^ 3 - ((919 / 3476) : ℂ) * ζ ^ 4 + ((183 / 4345) : ℂ) * ζ ^ 5 - ((1747 / 17380) : ℂ) * ζ ^ 6 - ((4129 / 17380) : ℂ) * ζ ^ 7 - ((415 / 3476) : ℂ) * ζ ^ 8 + ((713 / 17380) : ℂ) * ζ ^ 9 - ((1599 / 8690) : ℂ) * ζ ^ 10 + ((629 / 17380) : ℂ) * ζ ^ 11 - ((114 / 4345) : ℂ) * ζ ^ 12 - ((1211 / 8690) : ℂ) * ζ ^ 13 - ((1369 / 17380) : ℂ) * ζ ^ 14 + ((537 / 3476) : ℂ) * ζ ^ 15 - ((812 / 4345) : ℂ) * ζ ^ 16 + ((249 / 1580) : ℂ) * ζ ^ 17 - ((47 / 4345) : ℂ) * ζ ^ 18 - ((59 / 1580) : ℂ) * ζ ^ 19 + ((557 / 8690) : ℂ) * ζ ^ 20 + ((1393 / 17380) : ℂ) * ζ ^ 21 - ((1387 / 8690) : ℂ) * ζ ^ 22 + ((757 / 17380) : ℂ) * ζ ^ 23 + ((72 / 4345) : ℂ) * ζ ^ 24 - ((993 / 17380) : ℂ) * ζ ^ 25 + ((743 / 4345) : ℂ) * ζ ^ 26 - ((68 / 395) : ℂ) * ζ ^ 27 + ((13 / 869) : ℂ) * ζ ^ 28 - ((52 / 4345) : ℂ) * ζ ^ 29 + ((468 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_5_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 5 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_5_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 5 =
      (-((6 / 55) : ℂ) - ((7 / 55) : ℂ) * ζ ^ 1 + ((57 / 220) : ℂ) * ζ ^ 2 + ((19 / 220) : ℂ) * ζ ^ 3 - ((17 / 110) : ℂ) * ζ ^ 5 - ((8 / 55) : ℂ) * ζ ^ 6 + ((37 / 220) : ℂ) * ζ ^ 8 - ((7 / 110) : ℂ) * ζ ^ 9 - ((27 / 220) : ℂ) * ζ ^ 11 + ((9 / 55) : ℂ) * ζ ^ 12 + ((7 / 55) : ℂ) * ζ ^ 13 - ((1 / 220) : ℂ) * ζ ^ 15 + ((7 / 55) : ℂ) * ζ ^ 17 - ((3 / 110) : ℂ) * ζ ^ 18 + ((23 / 110) : ℂ) * ζ ^ 21 - ((57 / 220) : ℂ) * ζ ^ 22 - ((63 / 220) : ℂ) * ζ ^ 24 + ((3 / 110) : ℂ) * ζ ^ 25 + ((43 / 220) : ℂ) * ζ ^ 27 - ((37 / 220) : ℂ) * ζ ^ 28 - ((7 / 55) : ℂ) * ζ ^ 29 + ((9 / 220) : ℂ) * ζ ^ 30 + ((27 / 220) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((6 / 55) : ℂ) - ((7 / 110) : ℂ) * ζ ^ 1 - ((4 / 55) : ℂ) * ζ ^ 2 - ((61 / 220) : ℂ) * ζ ^ 3 + ((3 / 55) : ℂ) * ζ ^ 4 + ((3 / 110) : ℂ) * ζ ^ 5 + ((127 / 220) : ℂ) * ζ ^ 6 - ((6 / 55) : ℂ) * ζ ^ 7 - ((13 / 220) : ℂ) * ζ ^ 8 + ((1 / 55) : ℂ) * ζ ^ 9 - ((41 / 220) : ℂ) * ζ ^ 10 + ((2 / 55) : ℂ) * ζ ^ 11 + ((7 / 55) : ℂ) * ζ ^ 12 - ((9 / 220) : ℂ) * ζ ^ 14 - ((13 / 110) : ℂ) * ζ ^ 15 + ((7 / 110) : ℂ) * ζ ^ 17 - ((7 / 44) : ℂ) * ζ ^ 18 + ((21 / 110) : ℂ) * ζ ^ 19 - ((3 / 55) : ℂ) * ζ ^ 20 - ((9 / 110) : ℂ) * ζ ^ 21 - ((19 / 110) : ℂ) * ζ ^ 22 + ((6 / 55) : ℂ) * ζ ^ 23 + ((39 / 220) : ℂ) * ζ ^ 24 + ((1 / 55) : ℂ) * ζ ^ 25 + ((41 / 220) : ℂ) * ζ ^ 26 - ((6 / 55) : ℂ) * ζ ^ 27 - ((27 / 220) : ℂ) * ζ ^ 28)

private theorem row18_transformedGeneratorA_term_3_5_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 5 =
      (-((27 / 220) : ℂ) - ((9 / 220) : ℂ) * ζ ^ 1 + ((7 / 55) : ℂ) * ζ ^ 2 - ((6 / 55) : ℂ) * ζ ^ 3 - ((7 / 220) : ℂ) * ζ ^ 5 - ((2 / 55) : ℂ) * ζ ^ 6 - ((17 / 110) : ℂ) * ζ ^ 8 + ((23 / 220) : ℂ) * ζ ^ 9 + ((37 / 220) : ℂ) * ζ ^ 11 + ((13 / 220) : ℂ) * ζ ^ 12 + ((9 / 220) : ℂ) * ζ ^ 13 + ((9 / 55) : ℂ) * ζ ^ 15 + ((9 / 220) : ℂ) * ζ ^ 17 - ((29 / 220) : ℂ) * ζ ^ 18 - ((13 / 55) : ℂ) * ζ ^ 21 - ((7 / 55) : ℂ) * ζ ^ 22 - ((9 / 220) : ℂ) * ζ ^ 24 - ((1 / 110) : ℂ) * ζ ^ 25 - ((2 / 55) : ℂ) * ζ ^ 27 + ((17 / 110) : ℂ) * ζ ^ 28 - ((9 / 220) : ℂ) * ζ ^ 29 + ((4 / 55) : ℂ) * ζ ^ 30 - ((37 / 220) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_3_5 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        3 5 =
      alternatingSixAmbientRow18TransformedGeneratorA
        3 5 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_3_5_0,
      row18_transformedGeneratorA_term_3_5_1,
      row18_transformedGeneratorA_term_3_5_2,
      row18_transformedGeneratorA_term_3_5_3,
      row18_transformedGeneratorA_term_3_5_4,
      row18_transformedGeneratorA_term_3_5_5,
      row18_transformedGeneratorA_term_3_5_6,
      row18_transformedGeneratorA_term_3_5_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_6_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 6 =
      (((351 / 1580) : ℂ) + ((15 / 158) : ℂ) * ζ ^ 1 - ((1233 / 8690) : ℂ) * ζ ^ 2 - ((6 / 869) : ℂ) * ζ ^ 3 + ((37 / 316) : ℂ) * ζ ^ 5 + ((241 / 17380) : ℂ) * ζ ^ 6 - ((169 / 790) : ℂ) * ζ ^ 8 - ((16 / 79) : ℂ) * ζ ^ 9 + ((12 / 869) : ℂ) * ζ ^ 11 - ((167 / 790) : ℂ) * ζ ^ 12 - ((15 / 158) : ℂ) * ζ ^ 13 - ((173 / 3476) : ℂ) * ζ ^ 15 - ((15 / 158) : ℂ) * ζ ^ 17 + ((2503 / 17380) : ℂ) * ζ ^ 18 + ((3 / 316) : ℂ) * ζ ^ 21 + ((1233 / 8690) : ℂ) * ζ ^ 22 + ((357 / 1580) : ℂ) * ζ ^ 24 - ((7 / 316) : ℂ) * ζ ^ 25 - ((547 / 3476) : ℂ) * ζ ^ 27 + ((169 / 790) : ℂ) * ζ ^ 28 + ((15 / 158) : ℂ) * ζ ^ 29 - ((93 / 4345) : ℂ) * ζ ^ 30 - ((12 / 869) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((721 / 3476) : ℂ) - ((457 / 8690) : ℂ) * ζ ^ 1 + ((1333 / 8690) : ℂ) * ζ ^ 2 - ((25 / 869) : ℂ) * ζ ^ 3 + ((3053 / 17380) : ℂ) * ζ ^ 4 - ((589 / 17380) : ℂ) * ζ ^ 5 - ((57 / 316) : ℂ) * ζ ^ 6 - ((637 / 8690) : ℂ) * ζ ^ 7 - ((21 / 3476) : ℂ) * ζ ^ 8 + ((3131 / 17380) : ℂ) * ζ ^ 9 + ((93 / 1580) : ℂ) * ζ ^ 10 - ((83 / 4345) : ℂ) * ζ ^ 11 - ((126 / 4345) : ℂ) * ζ ^ 12 - ((1087 / 8690) : ℂ) * ζ ^ 13 + ((109 / 8690) : ℂ) * ζ ^ 14 + ((17 / 220) : ℂ) * ζ ^ 15 - ((267 / 3476) : ℂ) * ζ ^ 16 + ((1691 / 17380) : ℂ) * ζ ^ 17 - ((357 / 17380) : ℂ) * ζ ^ 18 - ((104 / 4345) : ℂ) * ζ ^ 19 + ((117 / 4345) : ℂ) * ζ ^ 20 - ((364 / 4345) : ℂ) * ζ ^ 21 - ((367 / 8690) : ℂ) * ζ ^ 22 + ((45 / 316) : ℂ) * ζ ^ 23 - ((119 / 4345) : ℂ) * ζ ^ 24 - ((353 / 17380) : ℂ) * ζ ^ 25 - ((233 / 17380) : ℂ) * ζ ^ 26 - ((479 / 17380) : ℂ) * ζ ^ 27 + ((377 / 17380) : ℂ) * ζ ^ 28 + ((333 / 8690) : ℂ) * ζ ^ 29 - ((493 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_6_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 6 =
      (-((5939 / 17380) : ℂ) - ((762 / 4345) : ℂ) * ζ ^ 1 - ((807 / 4345) : ℂ) * ζ ^ 2 + ((1821 / 17380) : ℂ) * ζ ^ 3 + ((2451 / 17380) : ℂ) * ζ ^ 5 - ((6377 / 17380) : ℂ) * ζ ^ 6 + ((757 / 17380) : ℂ) * ζ ^ 8 + ((4361 / 17380) : ℂ) * ζ ^ 9 + ((613 / 4345) : ℂ) * ζ ^ 11 - ((1679 / 17380) : ℂ) * ζ ^ 12 + ((762 / 4345) : ℂ) * ζ ^ 13 + ((1563 / 8690) : ℂ) * ζ ^ 15 + ((762 / 4345) : ℂ) * ζ ^ 17 + ((827 / 8690) : ℂ) * ζ ^ 18 + ((1024 / 4345) : ℂ) * ζ ^ 21 + ((807 / 4345) : ℂ) * ζ ^ 22 - ((953 / 17380) : ℂ) * ζ ^ 24 - ((5499 / 17380) : ℂ) * ζ ^ 25 + ((551 / 8690) : ℂ) * ζ ^ 27 - ((757 / 17380) : ℂ) * ζ ^ 28 - ((762 / 4345) : ℂ) * ζ ^ 29 - ((3141 / 17380) : ℂ) * ζ ^ 30 - ((613 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((5783 / 17380) : ℂ) + ((140 / 869) : ℂ) * ζ ^ 1 + ((585 / 3476) : ℂ) * ζ ^ 2 - ((3111 / 17380) : ℂ) * ζ ^ 3 - ((5619 / 17380) : ℂ) * ζ ^ 4 - ((771 / 8690) : ℂ) * ζ ^ 5 + ((2687 / 17380) : ℂ) * ζ ^ 6 + ((476 / 4345) : ℂ) * ζ ^ 7 + ((2557 / 17380) : ℂ) * ζ ^ 8 - ((111 / 4345) : ℂ) * ζ ^ 9 - ((1099 / 17380) : ℂ) * ζ ^ 10 - ((273 / 1738) : ℂ) * ζ ^ 11 + ((317 / 4345) : ℂ) * ζ ^ 12 + ((463 / 17380) : ℂ) * ζ ^ 13 + ((483 / 8690) : ℂ) * ζ ^ 14 + ((179 / 3476) : ℂ) * ζ ^ 15 - ((1 / 8690) : ℂ) * ζ ^ 16 - ((3263 / 17380) : ℂ) * ζ ^ 17 + ((239 / 8690) : ℂ) * ζ ^ 18 + ((458 / 4345) : ℂ) * ζ ^ 19 + ((1411 / 17380) : ℂ) * ζ ^ 20 - ((1121 / 17380) : ℂ) * ζ ^ 21 - ((193 / 1738) : ℂ) * ζ ^ 22 - ((6 / 395) : ℂ) * ζ ^ 23 - ((82 / 4345) : ℂ) * ζ ^ 24 + ((173 / 1738) : ℂ) * ζ ^ 25 + ((193 / 1580) : ℂ) * ζ ^ 26 - ((171 / 4345) : ℂ) * ζ ^ 27 - ((317 / 4345) : ℂ) * ζ ^ 28 - ((84 / 4345) : ℂ) * ζ ^ 29)

private theorem row18_transformedGeneratorA_term_3_6_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 6 =
      (-((1313 / 17380) : ℂ) - ((1103 / 17380) : ℂ) * ζ ^ 1 + ((2351 / 8690) : ℂ) * ζ ^ 2 + ((2153 / 17380) : ℂ) * ζ ^ 3 - ((7409 / 17380) : ℂ) * ζ ^ 5 + ((552 / 4345) : ℂ) * ζ ^ 6 + ((5409 / 17380) : ℂ) * ζ ^ 8 - ((1019 / 17380) : ℂ) * ζ ^ 9 - ((4449 / 17380) : ℂ) * ζ ^ 11 + ((3207 / 17380) : ℂ) * ζ ^ 12 + ((1103 / 17380) : ℂ) * ζ ^ 13 - ((3147 / 17380) : ℂ) * ζ ^ 15 + ((1103 / 17380) : ℂ) * ζ ^ 17 - ((1244 / 4345) : ℂ) * ζ ^ 18 + ((2833 / 8690) : ℂ) * ζ ^ 21 - ((2351 / 8690) : ℂ) * ζ ^ 22 - ((4361 / 17380) : ℂ) * ζ ^ 24 + ((3153 / 8690) : ℂ) * ζ ^ 25 + ((1944 / 4345) : ℂ) * ζ ^ 27 - ((5409 / 17380) : ℂ) * ζ ^ 28 - ((1103 / 17380) : ℂ) * ζ ^ 29 + ((707 / 8690) : ℂ) * ζ ^ 30 + ((4449 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((1313 / 17380) : ℂ) + ((243 / 3476) : ℂ) * ζ ^ 1 - ((3847 / 17380) : ℂ) * ζ ^ 2 + ((119 / 8690) : ℂ) * ζ ^ 3 + ((2141 / 17380) : ℂ) * ζ ^ 4 + ((8621 / 17380) : ℂ) * ζ ^ 5 + ((437 / 4345) : ℂ) * ζ ^ 6 + ((213 / 17380) : ℂ) * ζ ^ 7 - ((1063 / 3476) : ℂ) * ζ ^ 8 - ((2141 / 8690) : ℂ) * ζ ^ 9 - ((279 / 4345) : ℂ) * ζ ^ 10 + ((84 / 869) : ℂ) * ζ ^ 11 - ((173 / 17380) : ℂ) * ζ ^ 12 + ((35 / 869) : ℂ) * ζ ^ 13 - ((4203 / 17380) : ℂ) * ζ ^ 14 - ((81 / 395) : ℂ) * ζ ^ 15 + ((214 / 4345) : ℂ) * ζ ^ 16 - ((443 / 8690) : ℂ) * ζ ^ 17 + ((4509 / 17380) : ℂ) * ζ ^ 18 - ((346 / 4345) : ℂ) * ζ ^ 19 - ((119 / 8690) : ℂ) * ζ ^ 20 - ((2039 / 8690) : ℂ) * ζ ^ 21 + ((1797 / 17380) : ℂ) * ζ ^ 22 - ((303 / 3476) : ℂ) * ζ ^ 23 + ((3761 / 17380) : ℂ) * ζ ^ 24 - ((753 / 8690) : ℂ) * ζ ^ 25 + ((1347 / 8690) : ℂ) * ζ ^ 26 - ((741 / 8690) : ℂ) * ζ ^ 27 + ((1099 / 8690) : ℂ) * ζ ^ 28 + ((138 / 4345) : ℂ) * ζ ^ 29 + ((336 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_6_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 6 =
      (((91 / 395) : ℂ) + ((271 / 1580) : ℂ) * ζ ^ 1 - ((51 / 395) : ℂ) * ζ ^ 2 - ((81 / 1580) : ℂ) * ζ ^ 3 + ((59 / 790) : ℂ) * ζ ^ 5 + ((46 / 395) : ℂ) * ζ ^ 6 - ((151 / 790) : ℂ) * ζ ^ 8 - ((47 / 1580) : ℂ) * ζ ^ 9 + ((37 / 395) : ℂ) * ζ ^ 11 + ((139 / 1580) : ℂ) * ζ ^ 12 - ((271 / 1580) : ℂ) * ζ ^ 13 - ((111 / 1580) : ℂ) * ζ ^ 15 - ((271 / 1580) : ℂ) * ζ ^ 17 + ((247 / 1580) : ℂ) * ζ ^ 18 - ((153 / 395) : ℂ) * ζ ^ 21 + ((51 / 395) : ℂ) * ζ ^ 22 + ((353 / 1580) : ℂ) * ζ ^ 24 + ((153 / 1580) : ℂ) * ζ ^ 25 - ((251 / 790) : ℂ) * ζ ^ 27 + ((151 / 790) : ℂ) * ζ ^ 28 + ((271 / 1580) : ℂ) * ζ ^ 29 + ((17 / 1580) : ℂ) * ζ ^ 30 - ((37 / 395) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((63 / 395) : ℂ) - ((23 / 1580) : ℂ) * ζ ^ 1 + ((29 / 395) : ℂ) * ζ ^ 2 - ((7 / 1580) : ℂ) * ζ ^ 3 + ((18 / 395) : ℂ) * ζ ^ 4 - ((199 / 1580) : ℂ) * ζ ^ 5 - ((197 / 790) : ℂ) * ζ ^ 6 + ((19 / 790) : ℂ) * ζ ^ 7 + ((171 / 1580) : ℂ) * ζ ^ 8 + ((21 / 790) : ℂ) * ζ ^ 9 + ((233 / 1580) : ℂ) * ζ ^ 10 - ((269 / 1580) : ℂ) * ζ ^ 11 - ((447 / 1580) : ℂ) * ζ ^ 12 - ((10 / 79) : ℂ) * ζ ^ 13 + ((13 / 316) : ℂ) * ζ ^ 14 + ((58 / 395) : ℂ) * ζ ^ 15 + ((163 / 790) : ℂ) * ζ ^ 16 + ((99 / 1580) : ℂ) * ζ ^ 17 - ((35 / 316) : ℂ) * ζ ^ 18 - ((29 / 158) : ℂ) * ζ ^ 19 + ((1 / 79) : ℂ) * ζ ^ 20 + ((173 / 790) : ℂ) * ζ ^ 21 + ((48 / 395) : ℂ) * ζ ^ 22 + ((171 / 1580) : ℂ) * ζ ^ 23 - ((13 / 316) : ℂ) * ζ ^ 24 - ((26 / 395) : ℂ) * ζ ^ 25 + ((33 / 790) : ℂ) * ζ ^ 26 + ((111 / 1580) : ℂ) * ζ ^ 27 - ((7 / 395) : ℂ) * ζ ^ 28 + ((69 / 1580) : ℂ) * ζ ^ 29 - ((1 / 158) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_6_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 6 =
      (-((133 / 17380) : ℂ) + ((431 / 3476) : ℂ) * ζ ^ 1 + ((1461 / 17380) : ℂ) * ζ ^ 2 + ((223 / 4345) : ℂ) * ζ ^ 3 + ((189 / 1738) : ℂ) * ζ ^ 5 - ((1761 / 17380) : ℂ) * ζ ^ 6 - ((544 / 4345) : ℂ) * ζ ^ 8 - ((115 / 1738) : ℂ) * ζ ^ 9 + ((291 / 4345) : ℂ) * ζ ^ 11 - ((12 / 4345) : ℂ) * ζ ^ 12 - ((431 / 3476) : ℂ) * ζ ^ 13 + ((133 / 4345) : ℂ) * ζ ^ 15 - ((431 / 3476) : ℂ) * ζ ^ 17 - ((532 / 4345) : ℂ) * ζ ^ 18 - ((24 / 869) : ℂ) * ζ ^ 21 - ((1461 / 17380) : ℂ) * ζ ^ 22 - ((233 / 8690) : ℂ) * ζ ^ 24 + ((53 / 3476) : ℂ) * ζ ^ 25 - ((9 / 220) : ℂ) * ζ ^ 27 + ((544 / 4345) : ℂ) * ζ ^ 28 + ((431 / 3476) : ℂ) * ζ ^ 29 + ((1927 / 17380) : ℂ) * ζ ^ 30 - ((291 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((31 / 4345) : ℂ) - ((1227 / 8690) : ℂ) * ζ ^ 1 - ((178 / 4345) : ℂ) * ζ ^ 2 + ((157 / 3476) : ℂ) * ζ ^ 3 + ((611 / 17380) : ℂ) * ζ ^ 4 + ((1863 / 17380) : ℂ) * ζ ^ 5 + ((597 / 3476) : ℂ) * ζ ^ 6 + ((2699 / 17380) : ℂ) * ζ ^ 7 + ((673 / 8690) : ℂ) * ζ ^ 8 + ((7 / 158) : ℂ) * ζ ^ 9 - ((2887 / 8690) : ℂ) * ζ ^ 10 - ((1193 / 8690) : ℂ) * ζ ^ 11 - ((3127 / 17380) : ℂ) * ζ ^ 12 + ((857 / 17380) : ℂ) * ζ ^ 13 + ((8 / 395) : ℂ) * ζ ^ 14 + ((283 / 4345) : ℂ) * ζ ^ 15 - ((1667 / 17380) : ℂ) * ζ ^ 16 - ((457 / 8690) : ℂ) * ζ ^ 17 - ((21 / 1738) : ℂ) * ζ ^ 18 - ((163 / 3476) : ℂ) * ζ ^ 19 + ((80 / 869) : ℂ) * ζ ^ 20 - ((197 / 3476) : ℂ) * ζ ^ 21 - ((263 / 4345) : ℂ) * ζ ^ 22 - ((1447 / 8690) : ℂ) * ζ ^ 23 + ((353 / 8690) : ℂ) * ζ ^ 24 + ((21 / 17380) : ℂ) * ζ ^ 25 + ((343 / 1738) : ℂ) * ζ ^ 26 + ((1179 / 17380) : ℂ) * ζ ^ 27 + ((791 / 8690) : ℂ) * ζ ^ 28 + ((67 / 4345) : ℂ) * ζ ^ 29 + ((126 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_6_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 6 =
      (-((1 / 11) : ℂ) - ((5 / 44) : ℂ) * ζ ^ 1 + ((7 / 44) : ℂ) * ζ ^ 2 + ((5 / 44) : ℂ) * ζ ^ 3 + ((1 / 44) : ℂ) * ζ ^ 5 + ((9 / 44) : ℂ) * ζ ^ 6 + ((2 / 11) : ℂ) * ζ ^ 8 + ((3 / 44) : ℂ) * ζ ^ 9 - ((5 / 22) : ℂ) * ζ ^ 11 + ((3 / 22) : ℂ) * ζ ^ 12 + ((5 / 44) : ℂ) * ζ ^ 13 - ((1 / 22) : ℂ) * ζ ^ 15 + ((5 / 44) : ℂ) * ζ ^ 17 + ((1 / 44) : ℂ) * ζ ^ 18 + ((9 / 44) : ℂ) * ζ ^ 21 - ((7 / 44) : ℂ) * ζ ^ 22 - ((5 / 44) : ℂ) * ζ ^ 24 - ((3 / 22) : ℂ) * ζ ^ 25 + ((9 / 44) : ℂ) * ζ ^ 27 - ((2 / 11) : ℂ) * ζ ^ 28 - ((5 / 44) : ℂ) * ζ ^ 29 + ((1 / 11) : ℂ) * ζ ^ 30 + ((5 / 22) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_6_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 6 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_6_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 6 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_3_6 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        3 6 =
      alternatingSixAmbientRow18TransformedGeneratorA
        3 6 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_3_6_0,
      row18_transformedGeneratorA_term_3_6_1,
      row18_transformedGeneratorA_term_3_6_2,
      row18_transformedGeneratorA_term_3_6_3,
      row18_transformedGeneratorA_term_3_6_4,
      row18_transformedGeneratorA_term_3_6_5,
      row18_transformedGeneratorA_term_3_6_6,
      row18_transformedGeneratorA_term_3_6_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_7_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 7 =
      (-((247 / 17380) : ℂ) + ((1143 / 17380) : ℂ) * ζ ^ 1 + ((63 / 316) : ℂ) * ζ ^ 2 - ((2049 / 17380) : ℂ) * ζ ^ 3 - ((353 / 8690) : ℂ) * ζ ^ 5 + ((29 / 316) : ℂ) * ζ ^ 6 + ((4311 / 17380) : ℂ) * ζ ^ 8 - ((5231 / 17380) : ℂ) * ζ ^ 9 - ((2073 / 17380) : ℂ) * ζ ^ 11 - ((1197 / 17380) : ℂ) * ζ ^ 12 - ((1143 / 17380) : ℂ) * ζ ^ 13 - ((677 / 8690) : ℂ) * ζ ^ 15 - ((1143 / 17380) : ℂ) * ζ ^ 17 - ((3 / 79) : ℂ) * ζ ^ 18 + ((3689 / 17380) : ℂ) * ζ ^ 21 - ((63 / 316) : ℂ) * ζ ^ 22 - ((999 / 17380) : ℂ) * ζ ^ 24 + ((1849 / 17380) : ℂ) * ζ ^ 25 + ((613 / 4345) : ℂ) * ζ ^ 27 - ((4311 / 17380) : ℂ) * ζ ^ 28 + ((1143 / 17380) : ℂ) * ζ ^ 29 + ((19 / 316) : ℂ) * ζ ^ 30 + ((2073 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((391 / 17380) : ℂ) - ((1293 / 17380) : ℂ) * ζ ^ 1 - ((903 / 3476) : ℂ) * ζ ^ 2 + ((2987 / 17380) : ℂ) * ζ ^ 3 + ((2213 / 17380) : ℂ) * ζ ^ 4 + ((1681 / 8690) : ℂ) * ζ ^ 5 + ((823 / 8690) : ℂ) * ζ ^ 6 - ((21 / 158) : ℂ) * ζ ^ 7 - ((297 / 1580) : ℂ) * ζ ^ 8 + ((719 / 8690) : ℂ) * ζ ^ 9 - ((371 / 8690) : ℂ) * ζ ^ 10 + ((1303 / 4345) : ℂ) * ζ ^ 11 + ((64 / 4345) : ℂ) * ζ ^ 12 - ((2589 / 17380) : ℂ) * ζ ^ 13 + ((17 / 869) : ℂ) * ζ ^ 14 - ((3197 / 17380) : ℂ) * ζ ^ 15 - ((3261 / 17380) : ℂ) * ζ ^ 16 + ((1431 / 4345) : ℂ) * ζ ^ 17 + ((83 / 3476) : ℂ) * ζ ^ 18 + ((609 / 17380) : ℂ) * ζ ^ 19 + ((139 / 8690) : ℂ) * ζ ^ 20 - ((1181 / 4345) : ℂ) * ζ ^ 21 - ((349 / 4345) : ℂ) * ζ ^ 22 + ((757 / 4345) : ℂ) * ζ ^ 23 + ((703 / 8690) : ℂ) * ζ ^ 24 + ((159 / 1580) : ℂ) * ζ ^ 25 - ((672 / 4345) : ℂ) * ζ ^ 26 - ((568 / 4345) : ℂ) * ζ ^ 27 + ((463 / 3476) : ℂ) * ζ ^ 28 + ((263 / 4345) : ℂ) * ζ ^ 29 - ((551 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_7_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 7 =
      (((41 / 17380) : ℂ) + ((9107 / 17380) : ℂ) * ζ ^ 1 - ((29 / 1580) : ℂ) * ζ ^ 2 - ((39 / 790) : ℂ) * ζ ^ 3 + ((5641 / 17380) : ℂ) * ζ ^ 5 + ((489 / 1580) : ℂ) * ζ ^ 6 - ((752 / 4345) : ℂ) * ζ ^ 8 - ((1367 / 8690) : ℂ) * ζ ^ 9 - ((129 / 395) : ℂ) * ζ ^ 11 + ((863 / 8690) : ℂ) * ζ ^ 12 - ((9107 / 17380) : ℂ) * ζ ^ 13 - ((83 / 1580) : ℂ) * ζ ^ 15 - ((9107 / 17380) : ℂ) * ζ ^ 17 + ((311 / 790) : ℂ) * ζ ^ 18 - ((2331 / 4345) : ℂ) * ζ ^ 21 + ((29 / 1580) : ℂ) * ζ ^ 22 + ((621 / 8690) : ℂ) * ζ ^ 24 + ((1733 / 8690) : ℂ) * ζ ^ 25 + ((17 / 790) : ℂ) * ζ ^ 27 + ((752 / 4345) : ℂ) * ζ ^ 28 + ((9107 / 17380) : ℂ) * ζ ^ 29 - ((13 / 1580) : ℂ) * ζ ^ 30 + ((129 / 395) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((53 / 8690) : ℂ) - ((1719 / 3476) : ℂ) * ζ ^ 1 - ((37 / 3476) : ℂ) * ζ ^ 2 + ((534 / 4345) : ℂ) * ζ ^ 3 + ((973 / 8690) : ℂ) * ζ ^ 4 - ((1539 / 17380) : ℂ) * ζ ^ 5 - ((5013 / 17380) : ℂ) * ζ ^ 6 - ((416 / 4345) : ℂ) * ζ ^ 7 + ((401 / 8690) : ℂ) * ζ ^ 8 + ((723 / 4345) : ℂ) * ζ ^ 9 + ((4417 / 17380) : ℂ) * ζ ^ 10 + ((729 / 8690) : ℂ) * ζ ^ 11 + ((333 / 17380) : ℂ) * ζ ^ 12 + ((2939 / 17380) : ℂ) * ζ ^ 13 - ((476 / 4345) : ℂ) * ζ ^ 14 + ((261 / 17380) : ℂ) * ζ ^ 15 - ((115 / 1738) : ℂ) * ζ ^ 16 + ((356 / 4345) : ℂ) * ζ ^ 17 - ((13 / 55) : ℂ) * ζ ^ 18 - ((4221 / 17380) : ℂ) * ζ ^ 19 - ((2087 / 17380) : ℂ) * ζ ^ 20 + ((307 / 1738) : ℂ) * ζ ^ 21 + ((702 / 4345) : ℂ) * ζ ^ 22 + ((3687 / 17380) : ℂ) * ζ ^ 23 + ((19 / 8690) : ℂ) * ζ ^ 24 + ((91 / 1580) : ℂ) * ζ ^ 25 - ((239 / 3476) : ℂ) * ζ ^ 26 + ((167 / 4345) : ℂ) * ζ ^ 27 + ((5 / 44) : ℂ) * ζ ^ 28 - ((57 / 316) : ℂ) * ζ ^ 29 - ((651 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_7_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 7 =
      (-((2423 / 17380) : ℂ) - ((241 / 8690) : ℂ) * ζ ^ 1 - ((2751 / 17380) : ℂ) * ζ ^ 2 + ((175 / 1738) : ℂ) * ζ ^ 3 + ((3689 / 17380) : ℂ) * ζ ^ 5 - ((3339 / 17380) : ℂ) * ζ ^ 6 - ((3253 / 8690) : ℂ) * ζ ^ 8 + ((1519 / 17380) : ℂ) * ζ ^ 9 + ((1115 / 3476) : ℂ) * ζ ^ 11 - ((5193 / 17380) : ℂ) * ζ ^ 12 + ((241 / 8690) : ℂ) * ζ ^ 13 + ((773 / 3476) : ℂ) * ζ ^ 15 + ((241 / 8690) : ℂ) * ζ ^ 17 - ((1097 / 17380) : ℂ) * ζ ^ 18 - ((481 / 17380) : ℂ) * ζ ^ 21 + ((2751 / 17380) : ℂ) * ζ ^ 22 + ((5499 / 17380) : ℂ) * ζ ^ 24 - ((4171 / 17380) : ℂ) * ζ ^ 25 + ((42 / 869) : ℂ) * ζ ^ 27 + ((3253 / 8690) : ℂ) * ζ ^ 28 - ((241 / 8690) : ℂ) * ζ ^ 29 - ((8 / 4345) : ℂ) * ζ ^ 30 - ((1115 / 3476) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((2073 / 17380) : ℂ) - ((1 / 11) : ℂ) * ζ ^ 1 - ((1253 / 17380) : ℂ) * ζ ^ 2 - ((3439 / 8690) : ℂ) * ζ ^ 3 - ((549 / 1580) : ℂ) * ζ ^ 4 - ((5743 / 17380) : ℂ) * ζ ^ 5 + ((437 / 17380) : ℂ) * ζ ^ 6 + ((2217 / 17380) : ℂ) * ζ ^ 7 + ((3901 / 17380) : ℂ) * ζ ^ 8 + ((191 / 17380) : ℂ) * ζ ^ 9 + ((179 / 1580) : ℂ) * ζ ^ 10 - ((5 / 22) : ℂ) * ζ ^ 11 - ((101 / 4345) : ℂ) * ζ ^ 12 + ((445 / 3476) : ℂ) * ζ ^ 13 - ((853 / 17380) : ℂ) * ζ ^ 14 + ((351 / 17380) : ℂ) * ζ ^ 15 + ((56 / 4345) : ℂ) * ζ ^ 16 - ((171 / 4345) : ℂ) * ζ ^ 17 + ((4581 / 17380) : ℂ) * ζ ^ 18 + ((313 / 1580) : ℂ) * ζ ^ 19 + ((5173 / 17380) : ℂ) * ζ ^ 20 + ((771 / 4345) : ℂ) * ζ ^ 21 - ((397 / 8690) : ℂ) * ζ ^ 22 - ((311 / 17380) : ℂ) * ζ ^ 23 - ((641 / 17380) : ℂ) * ζ ^ 24 - ((173 / 1580) : ℂ) * ζ ^ 25 - ((113 / 3476) : ℂ) * ζ ^ 26 - ((2599 / 17380) : ℂ) * ζ ^ 27 - ((247 / 4345) : ℂ) * ζ ^ 28 - ((336 / 4345) : ℂ) * ζ ^ 29 - ((64 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_7_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 7 =
      (((373 / 1580) : ℂ) - ((1069 / 1580) : ℂ) * ζ ^ 1 - ((19 / 1580) : ℂ) * ζ ^ 2 + ((43 / 395) : ℂ) * ζ ^ 3 - ((233 / 395) : ℂ) * ζ ^ 5 - ((63 / 790) : ℂ) * ζ ^ 6 + ((453 / 790) : ℂ) * ζ ^ 8 + ((309 / 790) : ℂ) * ζ ^ 9 + ((67 / 790) : ℂ) * ζ ^ 11 + ((99 / 790) : ℂ) * ζ ^ 12 + ((1069 / 1580) : ℂ) * ζ ^ 13 - ((112 / 395) : ℂ) * ζ ^ 15 + ((1069 / 1580) : ℂ) * ζ ^ 17 - ((633 / 1580) : ℂ) * ζ ^ 18 + ((579 / 790) : ℂ) * ζ ^ 21 + ((19 / 1580) : ℂ) * ζ ^ 22 - ((96 / 395) : ℂ) * ζ ^ 24 - ((137 / 1580) : ℂ) * ζ ^ 25 - ((1 / 1580) : ℂ) * ζ ^ 27 - ((453 / 790) : ℂ) * ζ ^ 28 - ((1069 / 1580) : ℂ) * ζ ^ 29 + ((267 / 1580) : ℂ) * ζ ^ 30 - ((67 / 790) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((99 / 316) : ℂ) + ((167 / 316) : ℂ) * ζ ^ 1 + ((1 / 10) : ℂ) * ζ ^ 2 - ((35 / 158) : ℂ) * ζ ^ 3 + ((197 / 790) : ℂ) * ζ ^ 4 + ((233 / 790) : ℂ) * ζ ^ 5 - ((43 / 1580) : ℂ) * ζ ^ 6 + ((49 / 1580) : ℂ) * ζ ^ 7 - ((571 / 1580) : ℂ) * ζ ^ 8 - ((71 / 316) : ℂ) * ζ ^ 9 - ((127 / 790) : ℂ) * ζ ^ 10 + ((161 / 790) : ℂ) * ζ ^ 11 + ((59 / 316) : ℂ) * ζ ^ 12 + ((309 / 1580) : ℂ) * ζ ^ 13 + ((11 / 158) : ℂ) * ζ ^ 14 + ((36 / 395) : ℂ) * ζ ^ 15 - ((319 / 1580) : ℂ) * ζ ^ 16 - ((159 / 1580) : ℂ) * ζ ^ 17 + ((27 / 316) : ℂ) * ζ ^ 18 - ((13 / 790) : ℂ) * ζ ^ 19 - ((83 / 395) : ℂ) * ζ ^ 20 - ((141 / 316) : ℂ) * ζ ^ 21 - ((18 / 395) : ℂ) * ζ ^ 22 + ((13 / 790) : ℂ) * ζ ^ 23 - ((351 / 1580) : ℂ) * ζ ^ 24 - ((111 / 790) : ℂ) * ζ ^ 25 + ((109 / 1580) : ℂ) * ζ ^ 26 - ((351 / 1580) : ℂ) * ζ ^ 27 - ((13 / 395) : ℂ) * ζ ^ 28 - ((11 / 395) : ℂ) * ζ ^ 29 - ((12 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_7_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 7 =
      (((47 / 869) : ℂ) + ((243 / 1580) : ℂ) * ζ ^ 1 + ((309 / 1738) : ℂ) * ζ ^ 2 - ((2377 / 17380) : ℂ) * ζ ^ 3 - ((121 / 1580) : ℂ) * ζ ^ 5 + ((168 / 869) : ℂ) * ζ ^ 6 - ((1 / 44) : ℂ) * ζ ^ 8 - ((383 / 790) : ℂ) * ζ ^ 9 + ((541 / 17380) : ℂ) * ζ ^ 11 + ((277 / 1738) : ℂ) * ζ ^ 12 - ((243 / 1580) : ℂ) * ζ ^ 13 + ((1503 / 17380) : ℂ) * ζ ^ 15 - ((243 / 1580) : ℂ) * ζ ^ 17 - ((62 / 869) : ℂ) * ζ ^ 18 - ((131 / 1580) : ℂ) * ζ ^ 21 - ((309 / 1738) : ℂ) * ζ ^ 22 + ((741 / 3476) : ℂ) * ζ ^ 24 + ((91 / 395) : ℂ) * ζ ^ 25 - ((606 / 4345) : ℂ) * ζ ^ 27 + ((1 / 44) : ℂ) * ζ ^ 28 + ((243 / 1580) : ℂ) * ζ ^ 29 + ((65 / 1738) : ℂ) * ζ ^ 30 - ((541 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((967 / 17380) : ℂ) - ((733 / 3476) : ℂ) * ζ ^ 1 - ((98 / 395) : ℂ) * ζ ^ 2 + ((1887 / 8690) : ℂ) * ζ ^ 3 + ((4491 / 17380) : ℂ) * ζ ^ 4 + ((4133 / 8690) : ℂ) * ζ ^ 5 + ((1803 / 17380) : ℂ) * ζ ^ 6 + ((137 / 1580) : ℂ) * ζ ^ 7 + ((183 / 17380) : ℂ) * ζ ^ 8 + ((1967 / 17380) : ℂ) * ζ ^ 9 - ((633 / 4345) : ℂ) * ζ ^ 10 + ((353 / 4345) : ℂ) * ζ ^ 11 - ((995 / 3476) : ℂ) * ζ ^ 12 - ((1484 / 4345) : ℂ) * ζ ^ 13 - ((3317 / 17380) : ℂ) * ζ ^ 14 + ((50 / 869) : ℂ) * ζ ^ 15 + ((1259 / 8690) : ℂ) * ζ ^ 16 + ((2913 / 8690) : ℂ) * ζ ^ 17 - ((959 / 17380) : ℂ) * ζ ^ 18 - ((3639 / 17380) : ℂ) * ζ ^ 19 - ((4209 / 17380) : ℂ) * ζ ^ 20 - ((2447 / 17380) : ℂ) * ζ ^ 21 - ((489 / 8690) : ℂ) * ζ ^ 22 - ((105 / 3476) : ℂ) * ζ ^ 23 - ((349 / 4345) : ℂ) * ζ ^ 24 - ((3 / 3476) : ℂ) * ζ ^ 25 + ((249 / 4345) : ℂ) * ζ ^ 26 - ((27 / 8690) : ℂ) * ζ ^ 27 + ((4839 / 17380) : ℂ) * ζ ^ 28 + ((20 / 79) : ℂ) * ζ ^ 29 + ((9 / 55) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_3_7_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 7 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_3_7_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 7 =
      (((41 / 220) : ℂ) - ((6 / 55) : ℂ) * ζ ^ 1 - ((27 / 220) : ℂ) * ζ ^ 2 + ((21 / 110) : ℂ) * ζ ^ 3 + ((9 / 110) : ℂ) * ζ ^ 5 - ((63 / 220) : ℂ) * ζ ^ 6 - ((19 / 110) : ℂ) * ζ ^ 8 + ((43 / 220) : ℂ) * ζ ^ 9 + ((1 / 55) : ℂ) * ζ ^ 11 - ((89 / 220) : ℂ) * ζ ^ 12 + ((6 / 55) : ℂ) * ζ ^ 13 - ((2 / 55) : ℂ) * ζ ^ 15 + ((6 / 55) : ℂ) * ζ ^ 17 + ((13 / 110) : ℂ) * ζ ^ 18 + ((2 / 55) : ℂ) * ζ ^ 21 + ((27 / 220) : ℂ) * ζ ^ 22 + ((8 / 55) : ℂ) * ζ ^ 24 - ((21 / 110) : ℂ) * ζ ^ 25 + ((7 / 110) : ℂ) * ζ ^ 27 + ((19 / 110) : ℂ) * ζ ^ 28 - ((6 / 55) : ℂ) * ζ ^ 29 - ((39 / 220) : ℂ) * ζ ^ 30 - ((1 / 55) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((41 / 220) : ℂ) + ((6 / 55) : ℂ) * ζ ^ 1 + ((27 / 220) : ℂ) * ζ ^ 2)

private theorem row18_transformedGeneratorA_term_3_7_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          3 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 7 =
      (-((27 / 220) : ℂ) - ((9 / 220) : ℂ) * ζ ^ 1 + ((7 / 55) : ℂ) * ζ ^ 2 - ((6 / 55) : ℂ) * ζ ^ 3 - ((7 / 220) : ℂ) * ζ ^ 5 - ((2 / 55) : ℂ) * ζ ^ 6 - ((17 / 110) : ℂ) * ζ ^ 8 + ((23 / 220) : ℂ) * ζ ^ 9 + ((37 / 220) : ℂ) * ζ ^ 11 + ((13 / 220) : ℂ) * ζ ^ 12 + ((9 / 220) : ℂ) * ζ ^ 13 + ((9 / 55) : ℂ) * ζ ^ 15 + ((9 / 220) : ℂ) * ζ ^ 17 - ((29 / 220) : ℂ) * ζ ^ 18 - ((13 / 55) : ℂ) * ζ ^ 21 - ((7 / 55) : ℂ) * ζ ^ 22 - ((9 / 220) : ℂ) * ζ ^ 24 - ((1 / 110) : ℂ) * ζ ^ 25 - ((2 / 55) : ℂ) * ζ ^ 27 + ((17 / 110) : ℂ) * ζ ^ 28 - ((9 / 220) : ℂ) * ζ ^ 29 + ((4 / 55) : ℂ) * ζ ^ 30 - ((37 / 220) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_3_7 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        3 7 =
      alternatingSixAmbientRow18TransformedGeneratorA
        3 7 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_3_7_0,
      row18_transformedGeneratorA_term_3_7_1,
      row18_transformedGeneratorA_term_3_7_2,
      row18_transformedGeneratorA_term_3_7_3,
      row18_transformedGeneratorA_term_3_7_4,
      row18_transformedGeneratorA_term_3_7_5,
      row18_transformedGeneratorA_term_3_7_6,
      row18_transformedGeneratorA_term_3_7_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

/-- The checked transformed-generator equality on output row
3 of ambient row 18. -/
theorem alternatingSixAmbientRow18TransformedGeneratorA_fromIntermediate_row3
    (j : Fin 8) :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        3 j =
      alternatingSixAmbientRow18TransformedGeneratorA
        3 j := by
  fin_cases j
  · exact row18_transformedGeneratorA_3_0
  · exact row18_transformedGeneratorA_3_1
  · exact row18_transformedGeneratorA_3_2
  · exact row18_transformedGeneratorA_3_3
  · exact row18_transformedGeneratorA_3_4
  · exact row18_transformedGeneratorA_3_5
  · exact row18_transformedGeneratorA_3_6
  · exact row18_transformedGeneratorA_3_7


end InductiveMcKay
end McKayConjecture
