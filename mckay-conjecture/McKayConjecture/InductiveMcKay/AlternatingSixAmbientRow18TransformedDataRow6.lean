/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18TransformedDataRow5

/-!
# Transformed-generator data for ambient row 18, output row 6

This generated module checks the scalar products in output row 6.
It imports the preceding output-row module to serialize clean builds.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

private theorem row18_transformedGeneratorA_term_6_0_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 0 =
      (-((454 / 4345) : ℂ) + ((141 / 8690) : ℂ) * ζ ^ 1 + ((1079 / 17380) : ℂ) * ζ ^ 2 + ((227 / 8690) : ℂ) * ζ ^ 3 - ((917 / 8690) : ℂ) * ζ ^ 5 - ((1809 / 17380) : ℂ) * ζ ^ 6 + ((1172 / 4345) : ℂ) * ζ ^ 8 + ((1791 / 17380) : ℂ) * ζ ^ 9 - ((3 / 220) : ℂ) * ζ ^ 11 - ((34 / 4345) : ℂ) * ζ ^ 12 - ((141 / 8690) : ℂ) * ζ ^ 13 - ((1633 / 8690) : ℂ) * ζ ^ 15 - ((141 / 8690) : ℂ) * ζ ^ 17 + ((169 / 8690) : ℂ) * ζ ^ 18 - ((487 / 8690) : ℂ) * ζ ^ 21 - ((1079 / 17380) : ℂ) * ζ ^ 22 + ((403 / 17380) : ℂ) * ζ ^ 24 + ((529 / 4345) : ℂ) * ζ ^ 25 - ((558 / 4345) : ℂ) * ζ ^ 27 - ((1172 / 4345) : ℂ) * ζ ^ 28 + ((141 / 8690) : ℂ) * ζ ^ 29 - ((947 / 17380) : ℂ) * ζ ^ 30 + ((3 / 220) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((202 / 4345) : ℂ) + ((259 / 17380) : ℂ) * ζ ^ 1 - ((591 / 8690) : ℂ) * ζ ^ 2 + ((179 / 4345) : ℂ) * ζ ^ 3 + ((827 / 17380) : ℂ) * ζ ^ 4 + ((423 / 3476) : ℂ) * ζ ^ 5 + ((3647 / 17380) : ℂ) * ζ ^ 6 - ((558 / 4345) : ℂ) * ζ ^ 7 - ((1351 / 8690) : ℂ) * ζ ^ 8 - ((3579 / 8690) : ℂ) * ζ ^ 9 - ((1939 / 17380) : ℂ) * ζ ^ 10 - ((4359 / 17380) : ℂ) * ζ ^ 11 + ((201 / 8690) : ℂ) * ζ ^ 12 + ((191 / 1738) : ℂ) * ζ ^ 13 + ((333 / 4345) : ℂ) * ζ ^ 14 + ((240 / 869) : ℂ) * ζ ^ 15 - ((10 / 79) : ℂ) * ζ ^ 16 - ((141 / 1738) : ℂ) * ζ ^ 17 + ((71 / 1580) : ℂ) * ζ ^ 18 + ((351 / 8690) : ℂ) * ζ ^ 19 + ((3037 / 17380) : ℂ) * ζ ^ 20 - ((653 / 17380) : ℂ) * ζ ^ 21 + ((119 / 17380) : ℂ) * ζ ^ 22 + ((205 / 3476) : ℂ) * ζ ^ 23 + ((54 / 869) : ℂ) * ζ ^ 24 + ((491 / 4345) : ℂ) * ζ ^ 25 + ((203 / 8690) : ℂ) * ζ ^ 26 + ((1869 / 8690) : ℂ) * ζ ^ 27 + ((85 / 869) : ℂ) * ζ ^ 28 - ((13 / 17380) : ℂ) * ζ ^ 29 + ((41 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_0_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 0 =
      (((601 / 1738) : ℂ) - ((1081 / 17380) : ℂ) * ζ ^ 1 + ((1489 / 17380) : ℂ) * ζ ^ 2 - ((459 / 8690) : ℂ) * ζ ^ 3 - ((5143 / 17380) : ℂ) * ζ ^ 5 - ((747 / 8690) : ℂ) * ζ ^ 6 - ((897 / 3476) : ℂ) * ζ ^ 8 - ((1439 / 8690) : ℂ) * ζ ^ 9 + ((4289 / 17380) : ℂ) * ζ ^ 11 - ((357 / 1738) : ℂ) * ζ ^ 12 + ((1081 / 17380) : ℂ) * ζ ^ 13 + ((3907 / 17380) : ℂ) * ζ ^ 15 + ((1081 / 17380) : ℂ) * ζ ^ 17 + ((373 / 17380) : ℂ) * ζ ^ 18 - ((489 / 8690) : ℂ) * ζ ^ 21 - ((1489 / 17380) : ℂ) * ζ ^ 22 + ((1145 / 3476) : ℂ) * ζ ^ 24 + ((2031 / 8690) : ℂ) * ζ ^ 25 - ((1901 / 17380) : ℂ) * ζ ^ 27 + ((897 / 3476) : ℂ) * ζ ^ 28 - ((1081 / 17380) : ℂ) * ζ ^ 29 - ((958 / 4345) : ℂ) * ζ ^ 30 - ((4289 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((3131 / 8690) : ℂ) + ((697 / 17380) : ℂ) * ζ ^ 1 - ((797 / 8690) : ℂ) * ζ ^ 2 + ((13 / 869) : ℂ) * ζ ^ 3 + ((2971 / 8690) : ℂ) * ζ ^ 4 + ((879 / 3476) : ℂ) * ζ ^ 5 + ((809 / 3476) : ℂ) * ζ ^ 6 + ((7 / 316) : ℂ) * ζ ^ 7 - ((348 / 4345) : ℂ) * ζ ^ 8 - ((93 / 17380) : ℂ) * ζ ^ 9 - ((403 / 4345) : ℂ) * ζ ^ 10 - ((357 / 1580) : ℂ) * ζ ^ 11 - ((191 / 17380) : ℂ) * ζ ^ 12 - ((443 / 17380) : ℂ) * ζ ^ 13 + ((2517 / 17380) : ℂ) * ζ ^ 14 + ((64 / 869) : ℂ) * ζ ^ 15 - ((58 / 869) : ℂ) * ζ ^ 16 + ((2297 / 17380) : ℂ) * ζ ^ 17 - ((215 / 3476) : ℂ) * ζ ^ 18 - ((23 / 790) : ℂ) * ζ ^ 19 - ((3181 / 17380) : ℂ) * ζ ^ 20 - ((52 / 869) : ℂ) * ζ ^ 21 - ((76 / 4345) : ℂ) * ζ ^ 22 - ((1103 / 17380) : ℂ) * ζ ^ 23 - ((91 / 3476) : ℂ) * ζ ^ 24 + ((118 / 4345) : ℂ) * ζ ^ 25 + ((551 / 8690) : ℂ) * ζ ^ 26 + ((109 / 3476) : ℂ) * ζ ^ 27 + ((96 / 4345) : ℂ) * ζ ^ 28 + ((111 / 4345) : ℂ) * ζ ^ 29 + ((111 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_0_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 0 =
      (-((71 / 869) : ℂ) - ((113 / 1580) : ℂ) * ζ ^ 1 + ((351 / 17380) : ℂ) * ζ ^ 2 - ((173 / 8690) : ℂ) * ζ ^ 3 + ((19 / 395) : ℂ) * ζ ^ 5 + ((81 / 4345) : ℂ) * ζ ^ 6 - ((12 / 869) : ℂ) * ζ ^ 8 + ((301 / 1580) : ℂ) * ζ ^ 9 - ((281 / 8690) : ℂ) * ζ ^ 11 - ((69 / 3476) : ℂ) * ζ ^ 12 + ((113 / 1580) : ℂ) * ζ ^ 13 - ((1131 / 17380) : ℂ) * ζ ^ 15 + ((113 / 1580) : ℂ) * ζ ^ 17 + ((1481 / 8690) : ℂ) * ζ ^ 18 + ((121 / 1580) : ℂ) * ζ ^ 21 - ((351 / 17380) : ℂ) * ζ ^ 22 - ((315 / 1738) : ℂ) * ζ ^ 24 - ((189 / 1580) : ℂ) * ζ ^ 25 + ((512 / 4345) : ℂ) * ζ ^ 27 + ((12 / 869) : ℂ) * ζ ^ 28 - ((113 / 1580) : ℂ) * ζ ^ 29 + ((721 / 8690) : ℂ) * ζ ^ 30 + ((281 / 8690) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((71 / 869) : ℂ) + ((103 / 790) : ℂ) * ζ ^ 1 + ((243 / 17380) : ℂ) * ζ ^ 2 + ((47 / 869) : ℂ) * ζ ^ 3 - ((1717 / 17380) : ℂ) * ζ ^ 4 - ((27 / 220) : ℂ) * ζ ^ 5 - ((267 / 17380) : ℂ) * ζ ^ 6 - ((269 / 3476) : ℂ) * ζ ^ 7 + ((151 / 3476) : ℂ) * ζ ^ 8 - ((2713 / 17380) : ℂ) * ζ ^ 9 + ((179 / 3476) : ℂ) * ζ ^ 10 + ((36 / 395) : ℂ) * ζ ^ 11 + ((3623 / 17380) : ℂ) * ζ ^ 12 + ((1807 / 8690) : ℂ) * ζ ^ 13 + ((927 / 8690) : ℂ) * ζ ^ 14 + ((529 / 17380) : ℂ) * ζ ^ 15 + ((359 / 17380) : ℂ) * ζ ^ 16 - ((3357 / 17380) : ℂ) * ζ ^ 17 - ((525 / 3476) : ℂ) * ζ ^ 18 - ((2627 / 17380) : ℂ) * ζ ^ 19 - ((571 / 17380) : ℂ) * ζ ^ 20 + ((219 / 4345) : ℂ) * ζ ^ 21 + ((301 / 3476) : ℂ) * ζ ^ 22 + ((641 / 4345) : ℂ) * ζ ^ 23 + ((269 / 4345) : ℂ) * ζ ^ 24 + ((148 / 4345) : ℂ) * ζ ^ 25 - ((2809 / 17380) : ℂ) * ζ ^ 26 - ((563 / 4345) : ℂ) * ζ ^ 27 - ((498 / 4345) : ℂ) * ζ ^ 28 - ((174 / 4345) : ℂ) * ζ ^ 29 - ((87 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_0_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 0 =
      (-((4 / 395) : ℂ) - ((23 / 395) : ℂ) * ζ ^ 1 + ((191 / 1580) : ℂ) * ζ ^ 2 + ((1 / 4) : ℂ) * ζ ^ 3 + ((319 / 1580) : ℂ) * ζ ^ 5 + ((49 / 1580) : ℂ) * ζ ^ 6 - ((267 / 1580) : ℂ) * ζ ^ 8 - ((19 / 395) : ℂ) * ζ ^ 9 - ((53 / 316) : ℂ) * ζ ^ 11 + ((9 / 1580) : ℂ) * ζ ^ 12 + ((23 / 395) : ℂ) * ζ ^ 13 - ((9 / 79) : ℂ) * ζ ^ 15 + ((23 / 395) : ℂ) * ζ ^ 17 - ((113 / 1580) : ℂ) * ζ ^ 18 + ((21 / 395) : ℂ) * ζ ^ 21 - ((191 / 1580) : ℂ) * ζ ^ 22 - ((63 / 395) : ℂ) * ζ ^ 24 - ((411 / 1580) : ℂ) * ζ ^ 25 + ((9 / 79) : ℂ) * ζ ^ 27 + ((267 / 1580) : ℂ) * ζ ^ 28 - ((23 / 395) : ℂ) * ζ ^ 29 + ((277 / 1580) : ℂ) * ζ ^ 30 + ((53 / 316) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((16 / 79) : ℂ) - ((111 / 790) : ℂ) * ζ ^ 1 - ((1 / 395) : ℂ) * ζ ^ 2 - ((113 / 1580) : ℂ) * ζ ^ 3 + ((22 / 79) : ℂ) * ζ ^ 4 + ((19 / 316) : ℂ) * ζ ^ 5 + ((389 / 1580) : ℂ) * ζ ^ 6 + ((283 / 1580) : ℂ) * ζ ^ 7 - ((31 / 158) : ℂ) * ζ ^ 8 + ((311 / 1580) : ℂ) * ζ ^ 9 - ((123 / 790) : ℂ) * ζ ^ 10 - ((87 / 790) : ℂ) * ζ ^ 11 - ((3 / 395) : ℂ) * ζ ^ 12 - ((31 / 790) : ℂ) * ζ ^ 13 - ((113 / 1580) : ℂ) * ζ ^ 14 - ((49 / 790) : ℂ) * ζ ^ 15 - ((231 / 1580) : ℂ) * ζ ^ 16 - ((1 / 158) : ℂ) * ζ ^ 17 - ((113 / 1580) : ℂ) * ζ ^ 18 - ((39 / 395) : ℂ) * ζ ^ 19 + ((15 / 316) : ℂ) * ζ ^ 20 - ((171 / 790) : ℂ) * ζ ^ 21 - ((23 / 316) : ℂ) * ζ ^ 22 - ((3 / 158) : ℂ) * ζ ^ 23 + ((31 / 395) : ℂ) * ζ ^ 24 + ((3 / 790) : ℂ) * ζ ^ 25 + ((133 / 1580) : ℂ) * ζ ^ 26 + ((34 / 395) : ℂ) * ζ ^ 27 + ((167 / 790) : ℂ) * ζ ^ 28 + ((16 / 395) : ℂ) * ζ ^ 29 + ((22 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_0_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 0 =
      (-((62 / 395) : ℂ) + ((21 / 220) : ℂ) * ζ ^ 1 - ((201 / 3476) : ℂ) * ζ ^ 2 - ((201 / 1738) : ℂ) * ζ ^ 3 - ((299 / 8690) : ℂ) * ζ ^ 5 + ((34 / 869) : ℂ) * ζ ^ 6 + ((239 / 1580) : ℂ) * ζ ^ 8 - ((267 / 4345) : ℂ) * ζ ^ 9 + ((69 / 869) : ℂ) * ζ ^ 11 + ((73 / 395) : ℂ) * ζ ^ 12 - ((21 / 220) : ℂ) * ζ ^ 13 + ((691 / 3476) : ℂ) * ζ ^ 15 - ((21 / 220) : ℂ) * ζ ^ 17 - ((50 / 869) : ℂ) * ζ ^ 18 - ((207 / 4345) : ℂ) * ζ ^ 21 + ((201 / 3476) : ℂ) * ζ ^ 22 - ((153 / 790) : ℂ) * ζ ^ 24 + ((2257 / 17380) : ℂ) * ζ ^ 25 + ((71 / 869) : ℂ) * ζ ^ 27 - ((239 / 1580) : ℂ) * ζ ^ 28 + ((21 / 220) : ℂ) * ζ ^ 29 - ((59 / 1738) : ℂ) * ζ ^ 30 - ((69 / 869) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((149 / 869) : ℂ) - ((401 / 8690) : ℂ) * ζ ^ 1 + ((384 / 4345) : ℂ) * ζ ^ 2 + ((281 / 3476) : ℂ) * ζ ^ 3 - ((3909 / 17380) : ℂ) * ζ ^ 4 + ((1811 / 17380) : ℂ) * ζ ^ 5 - ((809 / 8690) : ℂ) * ζ ^ 6 - ((258 / 4345) : ℂ) * ζ ^ 7 + ((1037 / 8690) : ℂ) * ζ ^ 8 - ((39 / 4345) : ℂ) * ζ ^ 9 - ((178 / 4345) : ℂ) * ζ ^ 10 + ((167 / 3476) : ℂ) * ζ ^ 11 - ((1673 / 17380) : ℂ) * ζ ^ 12 + ((3 / 55) : ℂ) * ζ ^ 13 - ((102 / 4345) : ℂ) * ζ ^ 14 - ((2071 / 17380) : ℂ) * ζ ^ 15 + ((514 / 4345) : ℂ) * ζ ^ 16 - ((1239 / 17380) : ℂ) * ζ ^ 17 - ((233 / 17380) : ℂ) * ζ ^ 18 + ((746 / 4345) : ℂ) * ζ ^ 19 - ((419 / 3476) : ℂ) * ζ ^ 20 + ((467 / 3476) : ℂ) * ζ ^ 21 + ((125 / 3476) : ℂ) * ζ ^ 22 - ((19 / 158) : ℂ) * ζ ^ 23 + ((2089 / 17380) : ℂ) * ζ ^ 24 - ((98 / 869) : ℂ) * ζ ^ 25 + ((93 / 17380) : ℂ) * ζ ^ 26 + ((19 / 790) : ℂ) * ζ ^ 27 - ((691 / 17380) : ℂ) * ζ ^ 28 + ((6 / 869) : ℂ) * ζ ^ 29 + ((42 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_0_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 0 =
      (((1 / 22) : ℂ) + ((1 / 22) : ℂ) * ζ ^ 1 - ((1 / 11) : ℂ) * ζ ^ 3 + ((1 / 11) : ℂ) * ζ ^ 5 - ((1 / 11) : ℂ) * ζ ^ 8 + ((1 / 44) : ℂ) * ζ ^ 9 - ((3 / 44) : ℂ) * ζ ^ 11 - ((3 / 44) : ℂ) * ζ ^ 12 - ((1 / 22) : ℂ) * ζ ^ 13 - ((5 / 44) : ℂ) * ζ ^ 15 - ((1 / 22) : ℂ) * ζ ^ 17 + ((1 / 4) : ℂ) * ζ ^ 18 + ((3 / 44) : ℂ) * ζ ^ 21 + ((2 / 11) : ℂ) * ζ ^ 24 - ((1 / 22) : ℂ) * ζ ^ 25 - ((5 / 44) : ℂ) * ζ ^ 27 + ((1 / 11) : ℂ) * ζ ^ 28 + ((1 / 22) : ℂ) * ζ ^ 29 + ((3 / 44) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_0_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 0 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_0_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 0 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_6_0 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        6 0 =
      alternatingSixAmbientRow18TransformedGeneratorA
        6 0 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_6_0_0,
      row18_transformedGeneratorA_term_6_0_1,
      row18_transformedGeneratorA_term_6_0_2,
      row18_transformedGeneratorA_term_6_0_3,
      row18_transformedGeneratorA_term_6_0_4,
      row18_transformedGeneratorA_term_6_0_5,
      row18_transformedGeneratorA_term_6_0_6,
      row18_transformedGeneratorA_term_6_0_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_1_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 1 =
      (-((633 / 1580) : ℂ) - ((501 / 1738) : ℂ) * ζ ^ 1 - ((203 / 869) : ℂ) * ζ ^ 2 - ((27 / 4345) : ℂ) * ζ ^ 3 + ((175 / 1738) : ℂ) * ζ ^ 5 + ((113 / 869) : ℂ) * ζ ^ 6 + ((167 / 790) : ℂ) * ζ ^ 8 + ((1105 / 3476) : ℂ) * ζ ^ 9 + ((469 / 17380) : ℂ) * ζ ^ 11 - ((109 / 790) : ℂ) * ζ ^ 12 + ((501 / 1738) : ℂ) * ζ ^ 13 + ((3517 / 17380) : ℂ) * ζ ^ 15 + ((501 / 1738) : ℂ) * ζ ^ 17 + ((4 / 869) : ℂ) * ζ ^ 18 - ((229 / 1738) : ℂ) * ζ ^ 21 + ((203 / 869) : ℂ) * ζ ^ 22 + ((109 / 1580) : ℂ) * ζ ^ 24 - ((338 / 869) : ℂ) * ζ ^ 25 - ((3281 / 17380) : ℂ) * ζ ^ 27 - ((167 / 790) : ℂ) * ζ ^ 28 - ((501 / 1738) : ℂ) * ζ ^ 29 - ((83 / 869) : ℂ) * ζ ^ 30 - ((469 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((1599 / 4345) : ℂ) + ((399 / 1580) : ℂ) * ζ ^ 1 + ((1163 / 4345) : ℂ) * ζ ^ 2 + ((201 / 1580) : ℂ) * ζ ^ 3 - ((1329 / 4345) : ℂ) * ζ ^ 4 - ((1709 / 3476) : ℂ) * ζ ^ 5 - ((63 / 158) : ℂ) * ζ ^ 6 - ((1017 / 17380) : ℂ) * ζ ^ 7 + ((4479 / 17380) : ℂ) * ζ ^ 8 + ((1283 / 17380) : ℂ) * ζ ^ 9 + ((2087 / 17380) : ℂ) * ζ ^ 10 - ((739 / 3476) : ℂ) * ζ ^ 11 + ((2967 / 17380) : ℂ) * ζ ^ 12 + ((2021 / 8690) : ℂ) * ζ ^ 13 - ((1139 / 8690) : ℂ) * ζ ^ 14 - ((362 / 4345) : ℂ) * ζ ^ 15 - ((7721 / 17380) : ℂ) * ζ ^ 16 - ((1048 / 4345) : ℂ) * ζ ^ 17 - ((1003 / 8690) : ℂ) * ζ ^ 18 + ((1737 / 8690) : ℂ) * ζ ^ 19 + ((1769 / 3476) : ℂ) * ζ ^ 20 + ((6279 / 17380) : ℂ) * ζ ^ 21 + ((83 / 869) : ℂ) * ζ ^ 22 - ((323 / 1580) : ℂ) * ζ ^ 23 - ((4063 / 17380) : ℂ) * ζ ^ 24 - ((1681 / 17380) : ℂ) * ζ ^ 25 - ((387 / 8690) : ℂ) * ζ ^ 26 + ((3251 / 17380) : ℂ) * ζ ^ 27 + ((1513 / 17380) : ℂ) * ζ ^ 28 - ((7 / 8690) : ℂ) * ζ ^ 29 + ((37 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_1_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 1 =
      (-((7473 / 17380) : ℂ) - ((1394 / 4345) : ℂ) * ζ ^ 1 - ((78 / 869) : ℂ) * ζ ^ 2 - ((808 / 4345) : ℂ) * ζ ^ 3 - ((4453 / 17380) : ℂ) * ζ ^ 5 + ((823 / 3476) : ℂ) * ζ ^ 6 + ((2851 / 4345) : ℂ) * ζ ^ 8 - ((93 / 17380) : ℂ) * ζ ^ 9 - ((1376 / 4345) : ℂ) * ζ ^ 11 + ((1778 / 4345) : ℂ) * ζ ^ 12 + ((1394 / 4345) : ℂ) * ζ ^ 13 + ((1273 / 17380) : ℂ) * ζ ^ 15 + ((1394 / 4345) : ℂ) * ζ ^ 17 - ((153 / 3476) : ℂ) * ζ ^ 18 + ((1308 / 4345) : ℂ) * ζ ^ 21 + ((78 / 869) : ℂ) * ζ ^ 22 - ((6231 / 17380) : ℂ) * ζ ^ 24 - ((1123 / 17380) : ℂ) * ζ ^ 25 - ((887 / 8690) : ℂ) * ζ ^ 27 - ((2851 / 4345) : ℂ) * ζ ^ 28 - ((1394 / 4345) : ℂ) * ζ ^ 29 + ((78 / 869) : ℂ) * ζ ^ 30 + ((1376 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((1842 / 4345) : ℂ) + ((5647 / 17380) : ℂ) * ζ ^ 1 + ((32 / 395) : ℂ) * ζ ^ 2 + ((221 / 3476) : ℂ) * ζ ^ 3 - ((2248 / 4345) : ℂ) * ζ ^ 4 - ((1967 / 17380) : ℂ) * ζ ^ 5 - ((3079 / 8690) : ℂ) * ζ ^ 6 - ((1081 / 17380) : ℂ) * ζ ^ 7 - ((2097 / 8690) : ℂ) * ζ ^ 8 + ((613 / 8690) : ℂ) * ζ ^ 9 + ((196 / 869) : ℂ) * ζ ^ 10 + ((2161 / 4345) : ℂ) * ζ ^ 11 + ((397 / 1738) : ℂ) * ζ ^ 12 - ((19 / 395) : ℂ) * ζ ^ 13 - ((21 / 3476) : ℂ) * ζ ^ 14 - ((1359 / 8690) : ℂ) * ζ ^ 15 - ((49 / 8690) : ℂ) * ζ ^ 16 - ((1101 / 17380) : ℂ) * ζ ^ 17 - ((83 / 395) : ℂ) * ζ ^ 18 + ((2989 / 17380) : ℂ) * ζ ^ 19 + ((347 / 4345) : ℂ) * ζ ^ 20 + ((1833 / 8690) : ℂ) * ζ ^ 21 - ((39 / 1738) : ℂ) * ζ ^ 22 + ((587 / 4345) : ℂ) * ζ ^ 23 + ((3 / 1580) : ℂ) * ζ ^ 24 + ((13 / 4345) : ℂ) * ζ ^ 25 - ((4979 / 17380) : ℂ) * ζ ^ 26 + ((247 / 17380) : ℂ) * ζ ^ 27 - ((1897 / 17380) : ℂ) * ζ ^ 28 + ((333 / 17380) : ℂ) * ζ ^ 29 - ((666 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_1_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 1 =
      (((249 / 1580) : ℂ) + ((1877 / 17380) : ℂ) * ζ ^ 1 + ((1431 / 4345) : ℂ) * ζ ^ 2 - ((699 / 17380) : ℂ) * ζ ^ 3 - ((2127 / 8690) : ℂ) * ζ ^ 5 + ((2521 / 17380) : ℂ) * ζ ^ 6 - ((31 / 790) : ℂ) * ζ ^ 8 - ((3269 / 17380) : ℂ) * ζ ^ 9 + ((947 / 17380) : ℂ) * ζ ^ 11 - ((93 / 790) : ℂ) * ζ ^ 12 - ((1877 / 17380) : ℂ) * ζ ^ 13 - ((629 / 17380) : ℂ) * ζ ^ 15 - ((1877 / 17380) : ℂ) * ζ ^ 17 - ((397 / 17380) : ℂ) * ζ ^ 18 - ((1909 / 17380) : ℂ) * ζ ^ 21 - ((1431 / 4345) : ℂ) * ζ ^ 22 - ((7 / 1580) : ℂ) * ζ ^ 24 + ((6131 / 17380) : ℂ) * ζ ^ 25 + ((1561 / 8690) : ℂ) * ζ ^ 27 + ((31 / 790) : ℂ) * ζ ^ 28 + ((1877 / 17380) : ℂ) * ζ ^ 29 - ((243 / 4345) : ℂ) * ζ ^ 30 - ((947 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1189 / 17380) : ℂ) - ((593 / 4345) : ℂ) * ζ ^ 1 - ((639 / 1580) : ℂ) * ζ ^ 2 + ((1233 / 17380) : ℂ) * ζ ^ 3 + ((117 / 1580) : ℂ) * ζ ^ 4 + ((3009 / 8690) : ℂ) * ζ ^ 5 + ((1623 / 17380) : ℂ) * ζ ^ 6 + ((81 / 8690) : ℂ) * ζ ^ 7 - ((2567 / 17380) : ℂ) * ζ ^ 8 - ((331 / 4345) : ℂ) * ζ ^ 9 - ((17 / 316) : ℂ) * ζ ^ 10 + ((179 / 790) : ℂ) * ζ ^ 11 + ((255 / 3476) : ℂ) * ζ ^ 12 - ((681 / 17380) : ℂ) * ζ ^ 13 - ((1861 / 8690) : ℂ) * ζ ^ 14 - ((2067 / 17380) : ℂ) * ζ ^ 15 - ((611 / 8690) : ℂ) * ζ ^ 16 - ((1527 / 17380) : ℂ) * ζ ^ 17 + ((2093 / 17380) : ℂ) * ζ ^ 18 - ((489 / 3476) : ℂ) * ζ ^ 19 + ((37 / 395) : ℂ) * ζ ^ 20 - ((129 / 4345) : ℂ) * ζ ^ 21 + ((175 / 869) : ℂ) * ζ ^ 22 + ((1261 / 8690) : ℂ) * ζ ^ 23 + ((9 / 17380) : ℂ) * ζ ^ 24 - ((2033 / 17380) : ℂ) * ζ ^ 25 - ((753 / 4345) : ℂ) * ζ ^ 26 - ((2969 / 17380) : ℂ) * ζ ^ 27 + ((163 / 3476) : ℂ) * ζ ^ 28 + ((1189 / 8690) : ℂ) * ζ ^ 29 + ((493 / 1738) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_1_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 1 =
      (((699 / 1580) : ℂ) + ((105 / 316) : ℂ) * ζ ^ 1 - ((293 / 790) : ℂ) * ζ ^ 2 - ((128 / 395) : ℂ) * ζ ^ 3 + ((149 / 316) : ℂ) * ζ ^ 5 - ((11 / 20) : ℂ) * ζ ^ 6 - ((531 / 790) : ℂ) * ζ ^ 8 + ((65 / 316) : ℂ) * ζ ^ 9 + ((264 / 395) : ℂ) * ζ ^ 11 - ((84 / 395) : ℂ) * ζ ^ 12 - ((105 / 316) : ℂ) * ζ ^ 13 + ((213 / 1580) : ℂ) * ζ ^ 15 - ((105 / 316) : ℂ) * ζ ^ 17 + ((823 / 1580) : ℂ) * ζ ^ 18 - ((40 / 79) : ℂ) * ζ ^ 21 + ((293 / 790) : ℂ) * ζ ^ 22 + ((152 / 395) : ℂ) * ζ ^ 24 - ((11 / 79) : ℂ) * ζ ^ 25 - ((121 / 395) : ℂ) * ζ ^ 27 + ((531 / 790) : ℂ) * ζ ^ 28 + ((105 / 316) : ℂ) * ζ ^ 29 - ((307 / 1580) : ℂ) * ζ ^ 30 - ((264 / 395) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((333 / 1580) : ℂ) - ((2 / 395) : ℂ) * ζ ^ 1 + ((499 / 1580) : ℂ) * ζ ^ 2 + ((227 / 1580) : ℂ) * ζ ^ 3 + ((159 / 790) : ℂ) * ζ ^ 4 - ((223 / 790) : ℂ) * ζ ^ 5 + ((29 / 790) : ℂ) * ζ ^ 6 - ((91 / 158) : ℂ) * ζ ^ 7 + ((55 / 316) : ℂ) * ζ ^ 8 - ((453 / 1580) : ℂ) * ζ ^ 9 + ((41 / 790) : ℂ) * ζ ^ 10 + ((191 / 790) : ℂ) * ζ ^ 11 - ((81 / 395) : ℂ) * ζ ^ 12 + ((17 / 1580) : ℂ) * ζ ^ 13 - ((37 / 1580) : ℂ) * ζ ^ 14 + ((49 / 395) : ℂ) * ζ ^ 15 + ((109 / 1580) : ℂ) * ζ ^ 16 + ((1 / 790) : ℂ) * ζ ^ 17 - ((157 / 790) : ℂ) * ζ ^ 18 + ((503 / 1580) : ℂ) * ζ ^ 19 - ((8 / 395) : ℂ) * ζ ^ 20 + ((121 / 316) : ℂ) * ζ ^ 21 - ((37 / 316) : ℂ) * ζ ^ 22 - ((87 / 1580) : ℂ) * ζ ^ 23 - ((17 / 316) : ℂ) * ζ ^ 24 + ((587 / 1580) : ℂ) * ζ ^ 25 + ((24 / 395) : ℂ) * ζ ^ 26 + ((61 / 790) : ℂ) * ζ ^ 27 - ((579 / 1580) : ℂ) * ζ ^ 28 - ((17 / 395) : ℂ) * ζ ^ 29 - ((87 / 790) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_1_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 1 =
      (-((47 / 316) : ℂ) - ((2213 / 17380) : ℂ) * ζ ^ 1 - ((11 / 790) : ℂ) * ζ ^ 2 + ((251 / 3476) : ℂ) * ζ ^ 3 - ((3799 / 17380) : ℂ) * ζ ^ 5 + ((11 / 790) : ℂ) * ζ ^ 6 + ((63 / 158) : ℂ) * ζ ^ 8 - ((2069 / 17380) : ℂ) * ζ ^ 9 - ((98 / 869) : ℂ) * ζ ^ 11 + ((2213 / 17380) : ℂ) * ζ ^ 13 + ((64 / 869) : ℂ) * ζ ^ 15 + ((2213 / 17380) : ℂ) * ζ ^ 17 - ((209 / 1580) : ℂ) * ζ ^ 18 + ((3183 / 8690) : ℂ) * ζ ^ 21 + ((11 / 790) : ℂ) * ζ ^ 22 - ((67 / 316) : ℂ) * ζ ^ 24 + ((793 / 8690) : ℂ) * ζ ^ 25 + ((161 / 1738) : ℂ) * ζ ^ 27 - ((63 / 158) : ℂ) * ζ ^ 28 - ((2213 / 17380) : ℂ) * ζ ^ 29 - ((209 / 1580) : ℂ) * ζ ^ 30 + ((98 / 869) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((3341 / 17380) : ℂ) + ((193 / 869) : ℂ) * ζ ^ 1 + ((111 / 1738) : ℂ) * ζ ^ 2 + ((256 / 4345) : ℂ) * ζ ^ 3 - ((199 / 790) : ℂ) * ζ ^ 4 + ((472 / 4345) : ℂ) * ζ ^ 5 + ((283 / 4345) : ℂ) * ζ ^ 6 + ((4691 / 17380) : ℂ) * ζ ^ 7 - ((281 / 4345) : ℂ) * ζ ^ 8 + ((494 / 4345) : ℂ) * ζ ^ 9 - ((768 / 4345) : ℂ) * ζ ^ 10 - ((263 / 1738) : ℂ) * ζ ^ 11 + ((183 / 17380) : ℂ) * ζ ^ 12 + ((284 / 4345) : ℂ) * ζ ^ 13 + ((15 / 316) : ℂ) * ζ ^ 14 - ((287 / 1738) : ℂ) * ζ ^ 15 - ((1013 / 8690) : ℂ) * ζ ^ 16 + ((33 / 1580) : ℂ) * ζ ^ 17 + ((389 / 17380) : ℂ) * ζ ^ 18 - ((59 / 17380) : ℂ) * ζ ^ 19 + ((229 / 3476) : ℂ) * ζ ^ 20 - ((123 / 1738) : ℂ) * ζ ^ 21 - ((1697 / 8690) : ℂ) * ζ ^ 22 - ((1933 / 17380) : ℂ) * ζ ^ 23 - ((867 / 17380) : ℂ) * ζ ^ 24 + ((173 / 3476) : ℂ) * ζ ^ 25 + ((476 / 4345) : ℂ) * ζ ^ 26 + ((706 / 4345) : ℂ) * ζ ^ 27 + ((793 / 4345) : ℂ) * ζ ^ 28 - ((312 / 4345) : ℂ) * ζ ^ 29 - ((312 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_1_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 1 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_1_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 1 =
      (((4 / 55) : ℂ) + ((41 / 220) : ℂ) * ζ ^ 1 + ((91 / 220) : ℂ) * ζ ^ 2 - ((17 / 220) : ℂ) * ζ ^ 5 + ((29 / 220) : ℂ) * ζ ^ 6 - ((43 / 220) : ℂ) * ζ ^ 8 - ((7 / 220) : ℂ) * ζ ^ 9 - ((6 / 55) : ℂ) * ζ ^ 12 - ((41 / 220) : ℂ) * ζ ^ 13 - ((41 / 220) : ℂ) * ζ ^ 17 - ((53 / 220) : ℂ) * ζ ^ 18 - ((8 / 55) : ℂ) * ζ ^ 21 - ((91 / 220) : ℂ) * ζ ^ 22 + ((21 / 110) : ℂ) * ζ ^ 24 + ((29 / 110) : ℂ) * ζ ^ 25 + ((43 / 220) : ℂ) * ζ ^ 28 + ((41 / 220) : ℂ) * ζ ^ 29 + ((13 / 55) : ℂ) * ζ ^ 30) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((4 / 55) : ℂ) - ((7 / 220) : ℂ) * ζ ^ 1 - ((17 / 55) : ℂ) * ζ ^ 2 - ((2 / 55) : ℂ) * ζ ^ 4 + ((29 / 110) : ℂ) * ζ ^ 5 + ((43 / 110) : ℂ) * ζ ^ 6 + ((27 / 220) : ℂ) * ζ ^ 8 - ((53 / 220) : ℂ) * ζ ^ 9 - ((23 / 220) : ℂ) * ζ ^ 10 - ((37 / 220) : ℂ) * ζ ^ 12 - ((13 / 55) : ℂ) * ζ ^ 14 + ((7 / 220) : ℂ) * ζ ^ 17 + ((3 / 22) : ℂ) * ζ ^ 18 + ((2 / 55) : ℂ) * ζ ^ 20 - ((9 / 220) : ℂ) * ζ ^ 21 - ((6 / 55) : ℂ) * ζ ^ 22 - ((13 / 110) : ℂ) * ζ ^ 24 + ((1 / 110) : ℂ) * ζ ^ 25 + ((23 / 220) : ℂ) * ζ ^ 26 + ((9 / 110) : ℂ) * ζ ^ 28)

private theorem row18_transformedGeneratorA_term_6_1_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 1 =
      (((41 / 220) : ℂ) - ((3 / 220) : ℂ) * ζ ^ 1 + ((39 / 220) : ℂ) * ζ ^ 3 + ((4 / 55) : ℂ) * ζ ^ 5 - ((19 / 110) : ℂ) * ζ ^ 8 - ((29 / 220) : ℂ) * ζ ^ 9 - ((3 / 55) : ℂ) * ζ ^ 11 + ((21 / 220) : ℂ) * ζ ^ 12 + ((3 / 220) : ℂ) * ζ ^ 13 - ((31 / 220) : ℂ) * ζ ^ 15 + ((3 / 220) : ℂ) * ζ ^ 17 + ((14 / 55) : ℂ) * ζ ^ 21 - ((23 / 220) : ℂ) * ζ ^ 24 - ((19 / 220) : ℂ) * ζ ^ 25 + ((13 / 220) : ℂ) * ζ ^ 27 + ((19 / 110) : ℂ) * ζ ^ 28 - ((3 / 220) : ℂ) * ζ ^ 29 + ((3 / 55) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_6_1 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        6 1 =
      alternatingSixAmbientRow18TransformedGeneratorA
        6 1 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_6_1_0,
      row18_transformedGeneratorA_term_6_1_1,
      row18_transformedGeneratorA_term_6_1_2,
      row18_transformedGeneratorA_term_6_1_3,
      row18_transformedGeneratorA_term_6_1_4,
      row18_transformedGeneratorA_term_6_1_5,
      row18_transformedGeneratorA_term_6_1_6,
      row18_transformedGeneratorA_term_6_1_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_2_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 2 =
      (-((247 / 3476) : ℂ) - ((2691 / 17380) : ℂ) * ζ ^ 1 - ((125 / 869) : ℂ) * ζ ^ 2 - ((3163 / 17380) : ℂ) * ζ ^ 3 - ((139 / 8690) : ℂ) * ζ ^ 5 - ((13 / 869) : ℂ) * ζ ^ 6 + ((217 / 869) : ℂ) * ζ ^ 8 + ((4017 / 17380) : ℂ) * ζ ^ 9 + ((3059 / 17380) : ℂ) * ζ ^ 11 - ((60 / 869) : ℂ) * ζ ^ 12 + ((2691 / 17380) : ℂ) * ζ ^ 13 + ((3067 / 17380) : ℂ) * ζ ^ 15 + ((2691 / 17380) : ℂ) * ζ ^ 17 - ((139 / 3476) : ℂ) * ζ ^ 18 - ((1413 / 17380) : ℂ) * ζ ^ 21 + ((125 / 869) : ℂ) * ζ ^ 22 - ((109 / 1738) : ℂ) * ζ ^ 24 - ((2413 / 17380) : ℂ) * ζ ^ 25 - ((809 / 4345) : ℂ) * ζ ^ 27 - ((217 / 869) : ℂ) * ζ ^ 28 - ((2691 / 17380) : ℂ) * ζ ^ 29 - ((325 / 3476) : ℂ) * ζ ^ 30 - ((3059 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((227 / 17380) : ℂ) + ((2287 / 17380) : ℂ) * ζ ^ 1 + ((1773 / 8690) : ℂ) * ζ ^ 2 + ((2961 / 17380) : ℂ) * ζ ^ 3 - ((487 / 17380) : ℂ) * ζ ^ 4 - ((2883 / 17380) : ℂ) * ζ ^ 5 - ((1043 / 8690) : ℂ) * ζ ^ 6 - ((289 / 3476) : ℂ) * ζ ^ 7 - ((307 / 1738) : ℂ) * ζ ^ 8 - ((717 / 3476) : ℂ) * ζ ^ 9 - ((589 / 8690) : ℂ) * ζ ^ 10 - ((571 / 8690) : ℂ) * ζ ^ 11 + ((2107 / 17380) : ℂ) * ζ ^ 12 + ((1217 / 8690) : ℂ) * ζ ^ 13 - ((631 / 17380) : ℂ) * ζ ^ 14 - ((679 / 17380) : ℂ) * ζ ^ 15 - ((2583 / 17380) : ℂ) * ζ ^ 16 - ((1157 / 8690) : ℂ) * ζ ^ 17 - ((73 / 1580) : ℂ) * ζ ^ 18 + ((1223 / 17380) : ℂ) * ζ ^ 19 + ((3229 / 17380) : ℂ) * ζ ^ 20 + ((763 / 8690) : ℂ) * ζ ^ 21 - ((877 / 17380) : ℂ) * ζ ^ 22 - ((571 / 17380) : ℂ) * ζ ^ 23 + ((637 / 17380) : ℂ) * ζ ^ 24 + ((501 / 8690) : ℂ) * ζ ^ 25 + ((959 / 8690) : ℂ) * ζ ^ 26 + ((577 / 4345) : ℂ) * ζ ^ 27 + ((701 / 17380) : ℂ) * ζ ^ 28 + ((13 / 17380) : ℂ) * ζ ^ 29 + ((17 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_2_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 2 =
      (((831 / 17380) : ℂ) + ((173 / 4345) : ℂ) * ζ ^ 1 + ((152 / 4345) : ℂ) * ζ ^ 2 + ((2757 / 17380) : ℂ) * ζ ^ 3 + ((263 / 8690) : ℂ) * ζ ^ 5 + ((318 / 4345) : ℂ) * ζ ^ 6 - ((23 / 17380) : ℂ) * ζ ^ 8 + ((723 / 8690) : ℂ) * ζ ^ 9 - ((953 / 8690) : ℂ) * ζ ^ 11 - ((1769 / 17380) : ℂ) * ζ ^ 12 - ((173 / 4345) : ℂ) * ζ ^ 13 + ((347 / 17380) : ℂ) * ζ ^ 15 - ((173 / 4345) : ℂ) * ζ ^ 17 + ((651 / 17380) : ℂ) * ζ ^ 18 - ((76 / 4345) : ℂ) * ζ ^ 21 - ((152 / 4345) : ℂ) * ζ ^ 22 + ((2367 / 17380) : ℂ) * ζ ^ 24 + ((83 / 8690) : ℂ) * ζ ^ 25 - ((1061 / 17380) : ℂ) * ζ ^ 27 + ((23 / 17380) : ℂ) * ζ ^ 28 + ((173 / 4345) : ℂ) * ζ ^ 29 + ((151 / 17380) : ℂ) * ζ ^ 30 + ((953 / 8690) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1083 / 17380) : ℂ) - ((101 / 4345) : ℂ) * ζ ^ 1 + ((521 / 17380) : ℂ) * ζ ^ 2 - ((4061 / 17380) : ℂ) * ζ ^ 3 + ((59 / 17380) : ℂ) * ζ ^ 4 - ((19 / 8690) : ℂ) * ζ ^ 5 - ((1079 / 8690) : ℂ) * ζ ^ 6 + ((854 / 4345) : ℂ) * ζ ^ 7 - ((1517 / 17380) : ℂ) * ζ ^ 8 - ((1379 / 8690) : ℂ) * ζ ^ 9 + ((618 / 4345) : ℂ) * ζ ^ 10 - ((1993 / 17380) : ℂ) * ζ ^ 11 - ((24 / 4345) : ℂ) * ζ ^ 12 - ((23 / 8690) : ℂ) * ζ ^ 13 - ((1349 / 8690) : ℂ) * ζ ^ 14 + ((52 / 869) : ℂ) * ζ ^ 15 - ((269 / 8690) : ℂ) * ζ ^ 16 - ((226 / 4345) : ℂ) * ζ ^ 17 + ((219 / 8690) : ℂ) * ζ ^ 18 - ((367 / 4345) : ℂ) * ζ ^ 19 + ((601 / 17380) : ℂ) * ζ ^ 20 - ((13 / 395) : ℂ) * ζ ^ 21 - ((511 / 4345) : ℂ) * ζ ^ 22 - ((311 / 17380) : ℂ) * ζ ^ 23 - ((189 / 8690) : ℂ) * ζ ^ 24 - ((54 / 4345) : ℂ) * ζ ^ 25 - ((256 / 4345) : ℂ) * ζ ^ 26 - ((199 / 17380) : ℂ) * ζ ^ 27 + ((296 / 4345) : ℂ) * ζ ^ 28 - ((111 / 4345) : ℂ) * ζ ^ 29)

private theorem row18_transformedGeneratorA_term_6_2_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 2 =
      (((51 / 869) : ℂ) + ((657 / 4345) : ℂ) * ζ ^ 1 - ((4681 / 17380) : ℂ) * ζ ^ 2 + ((1971 / 17380) : ℂ) * ζ ^ 3 - ((463 / 8690) : ℂ) * ζ ^ 5 - ((636 / 4345) : ℂ) * ζ ^ 6 - ((1057 / 3476) : ℂ) * ζ ^ 8 - ((4021 / 17380) : ℂ) * ζ ^ 9 - ((1509 / 8690) : ℂ) * ζ ^ 11 - ((405 / 3476) : ℂ) * ζ ^ 12 - ((657 / 4345) : ℂ) * ζ ^ 13 - ((856 / 4345) : ℂ) * ζ ^ 15 - ((657 / 4345) : ℂ) * ζ ^ 17 + ((2163 / 17380) : ℂ) * ζ ^ 18 - ((53 / 8690) : ℂ) * ζ ^ 21 + ((4681 / 17380) : ℂ) * ζ ^ 22 + ((221 / 1738) : ℂ) * ζ ^ 24 + ((1777 / 8690) : ℂ) * ζ ^ 25 + ((1731 / 8690) : ℂ) * ζ ^ 27 + ((1057 / 3476) : ℂ) * ζ ^ 28 + ((657 / 4345) : ℂ) * ζ ^ 29 + ((62 / 4345) : ℂ) * ζ ^ 30 + ((1509 / 8690) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((51 / 869) : ℂ) - ((533 / 4345) : ℂ) * ζ ^ 1 + ((345 / 1738) : ℂ) * ζ ^ 2 - ((523 / 8690) : ℂ) * ζ ^ 3 + ((219 / 4345) : ℂ) * ζ ^ 4 + ((106 / 869) : ℂ) * ζ ^ 5 - ((1219 / 17380) : ℂ) * ζ ^ 6 + ((1451 / 17380) : ℂ) * ζ ^ 7 + ((3063 / 17380) : ℂ) * ζ ^ 8 + ((126 / 4345) : ℂ) * ζ ^ 9 + ((289 / 1738) : ℂ) * ζ ^ 10 - ((196 / 4345) : ℂ) * ζ ^ 11 - ((16 / 869) : ℂ) * ζ ^ 12 - ((1077 / 8690) : ℂ) * ζ ^ 13 + ((2391 / 17380) : ℂ) * ζ ^ 14 + ((61 / 1580) : ℂ) * ζ ^ 15 + ((1007 / 17380) : ℂ) * ζ ^ 16 + ((2001 / 17380) : ℂ) * ζ ^ 17 - ((728 / 4345) : ℂ) * ζ ^ 18 - ((2117 / 17380) : ℂ) * ζ ^ 19 - ((106 / 869) : ℂ) * ζ ^ 20 - ((439 / 8690) : ℂ) * ζ ^ 21 + ((117 / 17380) : ℂ) * ζ ^ 22 + ((383 / 4345) : ℂ) * ζ ^ 23 - ((313 / 3476) : ℂ) * ζ ^ 24 - ((349 / 8690) : ℂ) * ζ ^ 25 - ((386 / 4345) : ℂ) * ζ ^ 26 - ((323 / 4345) : ℂ) * ζ ^ 27 - ((67 / 790) : ℂ) * ζ ^ 28 + ((174 / 4345) : ℂ) * ζ ^ 29 - ((609 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_2_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 2 =
      (((91 / 790) : ℂ) - ((89 / 395) : ℂ) * ζ ^ 1 + ((59 / 1580) : ℂ) * ζ ^ 2 - ((101 / 1580) : ℂ) * ζ ^ 3 + ((87 / 1580) : ℂ) * ζ ^ 5 + ((54 / 395) : ℂ) * ζ ^ 6 - ((63 / 790) : ℂ) * ζ ^ 8 - ((37 / 395) : ℂ) * ζ ^ 9 + ((253 / 1580) : ℂ) * ζ ^ 11 + ((101 / 790) : ℂ) * ζ ^ 12 + ((89 / 395) : ℂ) * ζ ^ 13 - ((4 / 395) : ℂ) * ζ ^ 15 + ((89 / 395) : ℂ) * ζ ^ 17 + ((43 / 1580) : ℂ) * ζ ^ 18 + ((141 / 790) : ℂ) * ζ ^ 21 - ((59 / 1580) : ℂ) * ζ ^ 22 - ((351 / 1580) : ℂ) * ζ ^ 24 - ((443 / 1580) : ℂ) * ζ ^ 25 - ((3 / 395) : ℂ) * ζ ^ 27 + ((63 / 790) : ℂ) * ζ ^ 28 - ((89 / 395) : ℂ) * ζ ^ 29 - ((38 / 395) : ℂ) * ζ ^ 30 - ((253 / 1580) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((259 / 790) : ℂ) + ((9 / 395) : ℂ) * ζ ^ 1 - ((71 / 1580) : ℂ) * ζ ^ 2 - ((27 / 316) : ℂ) * ζ ^ 3 + ((74 / 395) : ℂ) * ζ ^ 4 - ((193 / 1580) : ℂ) * ζ ^ 5 - ((27 / 158) : ℂ) * ζ ^ 6 - ((7 / 316) : ℂ) * ζ ^ 7 - ((307 / 1580) : ℂ) * ζ ^ 8 + ((85 / 316) : ℂ) * ζ ^ 9 - ((8 / 395) : ℂ) * ζ ^ 10 - ((47 / 790) : ℂ) * ζ ^ 11 + ((183 / 1580) : ℂ) * ζ ^ 12 - ((103 / 790) : ℂ) * ζ ^ 13 - ((143 / 1580) : ℂ) * ζ ^ 14 + ((58 / 395) : ℂ) * ζ ^ 15 - ((139 / 790) : ℂ) * ζ ^ 16 + ((33 / 790) : ℂ) * ζ ^ 17 - ((7 / 158) : ℂ) * ζ ^ 18 - ((14 / 395) : ℂ) * ζ ^ 19 + ((37 / 790) : ℂ) * ζ ^ 20 - ((157 / 790) : ℂ) * ζ ^ 21 - ((33 / 1580) : ℂ) * ζ ^ 22 - ((33 / 790) : ℂ) * ζ ^ 23 - ((17 / 395) : ℂ) * ζ ^ 24 - ((14 / 395) : ℂ) * ζ ^ 25 + ((109 / 1580) : ℂ) * ζ ^ 26 - ((107 / 790) : ℂ) * ζ ^ 27 - ((11 / 1580) : ℂ) * ζ ^ 28 - ((16 / 395) : ℂ) * ζ ^ 29 - ((1 / 158) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_2_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 2 =
      (-((1072 / 4345) : ℂ) + ((141 / 790) : ℂ) * ζ ^ 1 - ((173 / 8690) : ℂ) * ζ ^ 2 + ((1071 / 17380) : ℂ) * ζ ^ 3 - ((19 / 1580) : ℂ) * ζ ^ 5 - ((211 / 4345) : ℂ) * ζ ^ 6 + ((1066 / 4345) : ℂ) * ζ ^ 8 - ((21 / 395) : ℂ) * ζ ^ 9 + ((1037 / 17380) : ℂ) * ζ ^ 11 + ((5387 / 17380) : ℂ) * ζ ^ 12 - ((141 / 790) : ℂ) * ζ ^ 13 + ((1171 / 17380) : ℂ) * ζ ^ 15 - ((141 / 790) : ℂ) * ζ ^ 17 - ((667 / 17380) : ℂ) * ζ ^ 18 - ((71 / 395) : ℂ) * ζ ^ 21 + ((173 / 8690) : ℂ) * ζ ^ 22 - ((2273 / 8690) : ℂ) * ζ ^ 24 + ((301 / 1580) : ℂ) * ζ ^ 25 + ((1141 / 8690) : ℂ) * ζ ^ 27 - ((1066 / 4345) : ℂ) * ζ ^ 28 + ((141 / 790) : ℂ) * ζ ^ 29 + ((1119 / 8690) : ℂ) * ζ ^ 30 - ((1037 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((227 / 869) : ℂ) - ((1601 / 17380) : ℂ) * ζ ^ 1 + ((128 / 869) : ℂ) * ζ ^ 2 + ((1 / 158) : ℂ) * ζ ^ 3 - ((2171 / 17380) : ℂ) * ζ ^ 4 + ((3073 / 17380) : ℂ) * ζ ^ 5 + ((733 / 8690) : ℂ) * ζ ^ 6 - ((483 / 17380) : ℂ) * ζ ^ 7 + ((5 / 316) : ℂ) * ζ ^ 8 - ((1059 / 17380) : ℂ) * ζ ^ 9 - ((1593 / 8690) : ℂ) * ζ ^ 10 + ((7 / 3476) : ℂ) * ζ ^ 11 - ((127 / 790) : ℂ) * ζ ^ 12 + ((381 / 4345) : ℂ) * ζ ^ 13 - ((687 / 17380) : ℂ) * ζ ^ 14 - ((617 / 4345) : ℂ) * ζ ^ 15 + ((477 / 4345) : ℂ) * ζ ^ 16 - ((633 / 8690) : ℂ) * ζ ^ 17 - ((1431 / 17380) : ℂ) * ζ ^ 18 + ((128 / 869) : ℂ) * ζ ^ 19 - ((1297 / 8690) : ℂ) * ζ ^ 20 + ((2237 / 17380) : ℂ) * ζ ^ 21 + ((177 / 8690) : ℂ) * ζ ^ 22 - ((2467 / 17380) : ℂ) * ζ ^ 23 + ((972 / 4345) : ℂ) * ζ ^ 24 - ((1913 / 17380) : ℂ) * ζ ^ 25 + ((1943 / 17380) : ℂ) * ζ ^ 26 + ((587 / 17380) : ℂ) * ζ ^ 27 + ((19 / 8690) : ℂ) * ζ ^ 28 - ((6 / 869) : ℂ) * ζ ^ 29 - ((84 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_2_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 2 =
      (((1 / 22) : ℂ) + ((1 / 22) : ℂ) * ζ ^ 1 - ((1 / 11) : ℂ) * ζ ^ 3 + ((1 / 11) : ℂ) * ζ ^ 5 - ((1 / 11) : ℂ) * ζ ^ 8 + ((1 / 44) : ℂ) * ζ ^ 9 - ((3 / 44) : ℂ) * ζ ^ 11 - ((3 / 44) : ℂ) * ζ ^ 12 - ((1 / 22) : ℂ) * ζ ^ 13 - ((5 / 44) : ℂ) * ζ ^ 15 - ((1 / 22) : ℂ) * ζ ^ 17 + ((1 / 4) : ℂ) * ζ ^ 18 + ((3 / 44) : ℂ) * ζ ^ 21 + ((2 / 11) : ℂ) * ζ ^ 24 - ((1 / 22) : ℂ) * ζ ^ 25 - ((5 / 44) : ℂ) * ζ ^ 27 + ((1 / 11) : ℂ) * ζ ^ 28 + ((1 / 22) : ℂ) * ζ ^ 29 + ((3 / 44) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_2_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 2 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_2_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 2 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_6_2 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        6 2 =
      alternatingSixAmbientRow18TransformedGeneratorA
        6 2 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_6_2_0,
      row18_transformedGeneratorA_term_6_2_1,
      row18_transformedGeneratorA_term_6_2_2,
      row18_transformedGeneratorA_term_6_2_3,
      row18_transformedGeneratorA_term_6_2_4,
      row18_transformedGeneratorA_term_6_2_5,
      row18_transformedGeneratorA_term_6_2_6,
      row18_transformedGeneratorA_term_6_2_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_3_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 3 =
      (-((4887 / 17380) : ℂ) - ((297 / 790) : ℂ) * ζ ^ 1 - ((203 / 4345) : ℂ) * ζ ^ 2 + ((3843 / 17380) : ℂ) * ζ ^ 3 - ((627 / 1580) : ℂ) * ζ ^ 5 - ((1317 / 4345) : ℂ) * ζ ^ 6 + ((1931 / 17380) : ℂ) * ζ ^ 8 + ((87 / 395) : ℂ) * ζ ^ 9 - ((4749 / 17380) : ℂ) * ζ ^ 11 - ((281 / 8690) : ℂ) * ζ ^ 12 + ((297 / 790) : ℂ) * ζ ^ 13 - ((6287 / 17380) : ℂ) * ζ ^ 15 + ((297 / 790) : ℂ) * ζ ^ 17 + ((3591 / 17380) : ℂ) * ζ ^ 18 + ((133 / 1580) : ℂ) * ζ ^ 21 + ((203 / 4345) : ℂ) * ζ ^ 22 + ((2551 / 17380) : ℂ) * ζ ^ 24 + ((33 / 1580) : ℂ) * ζ ^ 25 + ((393 / 8690) : ℂ) * ζ ^ 27 - ((1931 / 17380) : ℂ) * ζ ^ 28 - ((297 / 790) : ℂ) * ζ ^ 29 - ((2157 / 8690) : ℂ) * ζ ^ 30 + ((4749 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((216 / 869) : ℂ) + ((2043 / 8690) : ℂ) * ζ ^ 1 - ((1297 / 17380) : ℂ) * ζ ^ 2 - ((771 / 17380) : ℂ) * ζ ^ 3 - ((1231 / 8690) : ℂ) * ζ ^ 4 + ((183 / 1580) : ℂ) * ζ ^ 5 + ((114 / 395) : ℂ) * ζ ^ 6 - ((423 / 17380) : ℂ) * ζ ^ 7 + ((509 / 1738) : ℂ) * ζ ^ 8 - ((697 / 8690) : ℂ) * ζ ^ 9 - ((871 / 4345) : ℂ) * ζ ^ 10 - ((1779 / 8690) : ℂ) * ζ ^ 11 - ((153 / 3476) : ℂ) * ζ ^ 12 + ((2679 / 8690) : ℂ) * ζ ^ 13 + ((3541 / 8690) : ℂ) * ζ ^ 14 + ((4459 / 17380) : ℂ) * ζ ^ 15 - ((1019 / 4345) : ℂ) * ζ ^ 16 - ((1673 / 8690) : ℂ) * ζ ^ 17 + ((777 / 17380) : ℂ) * ζ ^ 18 + ((1269 / 17380) : ℂ) * ζ ^ 19 + ((293 / 869) : ℂ) * ζ ^ 20 + ((861 / 8690) : ℂ) * ζ ^ 21 - ((353 / 8690) : ℂ) * ζ ^ 22 + ((7 / 79) : ℂ) * ζ ^ 23 - ((2369 / 17380) : ℂ) * ζ ^ 24 - ((4053 / 17380) : ℂ) * ζ ^ 25 + ((258 / 4345) : ℂ) * ζ ^ 26 + ((57 / 220) : ℂ) * ζ ^ 27 + ((305 / 3476) : ℂ) * ζ ^ 28 + ((7 / 8690) : ℂ) * ζ ^ 29 + ((19 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_3_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 3 =
      (-((1929 / 8690) : ℂ) - ((1274 / 4345) : ℂ) * ζ ^ 1 + ((75 / 869) : ℂ) * ζ ^ 2 - ((31 / 790) : ℂ) * ζ ^ 3 - ((193 / 17380) : ℂ) * ζ ^ 5 - ((587 / 3476) : ℂ) * ζ ^ 6 - ((883 / 8690) : ℂ) * ζ ^ 8 + ((4767 / 17380) : ℂ) * ζ ^ 9 - ((49 / 1580) : ℂ) * ζ ^ 11 + ((938 / 4345) : ℂ) * ζ ^ 12 + ((1274 / 4345) : ℂ) * ζ ^ 13 - ((217 / 1580) : ℂ) * ζ ^ 15 + ((1274 / 4345) : ℂ) * ζ ^ 17 + ((57 / 3476) : ℂ) * ζ ^ 18 - ((1473 / 17380) : ℂ) * ζ ^ 21 - ((75 / 869) : ℂ) * ζ ^ 22 + ((1299 / 17380) : ℂ) * ζ ^ 24 - ((4903 / 17380) : ℂ) * ζ ^ 25 + ((4 / 395) : ℂ) * ζ ^ 27 + ((883 / 8690) : ℂ) * ζ ^ 28 - ((1274 / 4345) : ℂ) * ζ ^ 29 - ((597 / 3476) : ℂ) * ζ ^ 30 + ((49 / 1580) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((3753 / 17380) : ℂ) + ((2111 / 8690) : ℂ) * ζ ^ 1 - ((521 / 4345) : ℂ) * ζ ^ 2 + ((2611 / 17380) : ℂ) * ζ ^ 3 - ((2617 / 17380) : ℂ) * ζ ^ 4 - ((365 / 1738) : ℂ) * ζ ^ 5 + ((4861 / 17380) : ℂ) * ζ ^ 6 - ((527 / 3476) : ℂ) * ζ ^ 7 + ((6321 / 17380) : ℂ) * ζ ^ 8 + ((68 / 4345) : ℂ) * ζ ^ 9 - ((2443 / 17380) : ℂ) * ζ ^ 10 + ((322 / 4345) : ℂ) * ζ ^ 11 - ((907 / 3476) : ℂ) * ζ ^ 12 + ((997 / 17380) : ℂ) * ζ ^ 13 - ((567 / 17380) : ℂ) * ζ ^ 14 - ((105 / 869) : ℂ) * ζ ^ 15 + ((268 / 4345) : ℂ) * ζ ^ 16 - ((4239 / 17380) : ℂ) * ζ ^ 17 + ((124 / 395) : ℂ) * ζ ^ 18 + ((1417 / 17380) : ℂ) * ζ ^ 19 - ((433 / 4345) : ℂ) * ζ ^ 20 + ((2043 / 17380) : ℂ) * ζ ^ 21 - ((597 / 17380) : ℂ) * ζ ^ 22 + ((4061 / 17380) : ℂ) * ζ ^ 23 - ((2637 / 17380) : ℂ) * ζ ^ 24 - ((163 / 8690) : ℂ) * ζ ^ 25 + ((1003 / 4345) : ℂ) * ζ ^ 26 - ((659 / 17380) : ℂ) * ζ ^ 27 + ((859 / 8690) : ℂ) * ζ ^ 28 - ((333 / 17380) : ℂ) * ζ ^ 29 + ((3441 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_3_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 3 =
      (((509 / 1738) : ℂ) - ((1273 / 17380) : ℂ) * ζ ^ 1 + ((1139 / 17380) : ℂ) * ζ ^ 2 + ((185 / 3476) : ℂ) * ζ ^ 3 + ((4901 / 17380) : ℂ) * ζ ^ 5 + ((504 / 4345) : ℂ) * ζ ^ 6 - ((375 / 3476) : ℂ) * ζ ^ 8 + ((4781 / 17380) : ℂ) * ζ ^ 9 + ((125 / 3476) : ℂ) * ζ ^ 11 + ((199 / 1738) : ℂ) * ζ ^ 12 + ((1273 / 17380) : ℂ) * ζ ^ 13 + ((75 / 869) : ℂ) * ζ ^ 15 + ((1273 / 17380) : ℂ) * ζ ^ 17 - ((1767 / 17380) : ℂ) * ζ ^ 18 + ((791 / 17380) : ℂ) * ζ ^ 21 - ((1139 / 17380) : ℂ) * ζ ^ 22 + ((149 / 869) : ℂ) * ζ ^ 24 - ((3087 / 8690) : ℂ) * ζ ^ 25 + ((9 / 869) : ℂ) * ζ ^ 27 + ((375 / 3476) : ℂ) * ζ ^ 28 - ((1273 / 17380) : ℂ) * ζ ^ 29 + ((569 / 8690) : ℂ) * ζ ^ 30 - ((125 / 3476) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((177 / 869) : ℂ) + ((127 / 17380) : ℂ) * ζ ^ 1 + ((309 / 17380) : ℂ) * ζ ^ 2 - ((1803 / 17380) : ℂ) * ζ ^ 3 + ((371 / 1738) : ℂ) * ζ ^ 4 - ((2441 / 8690) : ℂ) * ζ ^ 5 + ((267 / 8690) : ℂ) * ζ ^ 6 + ((102 / 4345) : ℂ) * ζ ^ 7 - ((3693 / 17380) : ℂ) * ζ ^ 8 + ((2943 / 17380) : ℂ) * ζ ^ 9 - ((95 / 869) : ℂ) * ζ ^ 10 + ((2763 / 17380) : ℂ) * ζ ^ 11 - ((4419 / 17380) : ℂ) * ζ ^ 12 - ((161 / 17380) : ℂ) * ζ ^ 13 - ((1651 / 17380) : ℂ) * ζ ^ 14 + ((7 / 17380) : ℂ) * ζ ^ 15 + ((845 / 3476) : ℂ) * ζ ^ 16 + ((313 / 3476) : ℂ) * ζ ^ 17 + ((47 / 4345) : ℂ) * ζ ^ 18 - ((1113 / 17380) : ℂ) * ζ ^ 19 - ((2729 / 8690) : ℂ) * ζ ^ 20 + ((339 / 8690) : ℂ) * ζ ^ 21 - ((1049 / 17380) : ℂ) * ζ ^ 22 + ((101 / 1738) : ℂ) * ζ ^ 23 + ((1369 / 17380) : ℂ) * ζ ^ 24 + ((951 / 17380) : ℂ) * ζ ^ 25 + ((343 / 4345) : ℂ) * ζ ^ 26 - ((2649 / 17380) : ℂ) * ζ ^ 27 + ((258 / 4345) : ℂ) * ζ ^ 28 - ((1189 / 8690) : ℂ) * ζ ^ 29 + ((116 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_3_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 3 =
      (((319 / 790) : ℂ) + ((913 / 1580) : ℂ) * ζ ^ 1 + ((82 / 395) : ℂ) * ζ ^ 2 - ((43 / 79) : ℂ) * ζ ^ 3 + ((329 / 1580) : ℂ) * ζ ^ 5 + ((431 / 790) : ℂ) * ζ ^ 6 - ((307 / 790) : ℂ) * ζ ^ 8 - ((311 / 1580) : ℂ) * ζ ^ 9 + ((2 / 79) : ℂ) * ζ ^ 11 - ((647 / 1580) : ℂ) * ζ ^ 12 - ((913 / 1580) : ℂ) * ζ ^ 13 + ((63 / 316) : ℂ) * ζ ^ 15 - ((913 / 1580) : ℂ) * ζ ^ 17 - ((271 / 395) : ℂ) * ζ ^ 18 - ((13 / 790) : ℂ) * ζ ^ 21 - ((82 / 395) : ℂ) * ζ ^ 22 + ((511 / 1580) : ℂ) * ζ ^ 24 + ((146 / 395) : ℂ) * ζ ^ 25 - ((22 / 79) : ℂ) * ζ ^ 27 + ((307 / 790) : ℂ) * ζ ^ 28 + ((913 / 1580) : ℂ) * ζ ^ 29 + ((751 / 1580) : ℂ) * ζ ^ 30 - ((2 / 79) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((68 / 395) : ℂ) - ((114 / 395) : ℂ) * ζ ^ 1 - ((101 / 1580) : ℂ) * ζ ^ 2 + ((147 / 316) : ℂ) * ζ ^ 3 - ((69 / 1580) : ℂ) * ζ ^ 4 + ((93 / 790) : ℂ) * ζ ^ 5 - ((23 / 316) : ℂ) * ζ ^ 6 - ((13 / 395) : ℂ) * ζ ^ 7 + ((97 / 790) : ℂ) * ζ ^ 8 - ((883 / 1580) : ℂ) * ζ ^ 9 + ((129 / 1580) : ℂ) * ζ ^ 10 - ((1 / 395) : ℂ) * ζ ^ 11 - ((31 / 790) : ℂ) * ζ ^ 12 + ((303 / 1580) : ℂ) * ζ ^ 13 - ((39 / 316) : ℂ) * ζ ^ 14 + ((27 / 395) : ℂ) * ζ ^ 15 - ((1 / 158) : ℂ) * ζ ^ 16 - ((13 / 395) : ℂ) * ζ ^ 17 + ((127 / 395) : ℂ) * ζ ^ 18 - ((213 / 1580) : ℂ) * ζ ^ 19 + ((191 / 790) : ℂ) * ζ ^ 20 + ((333 / 1580) : ℂ) * ζ ^ 21 + ((61 / 790) : ℂ) * ζ ^ 22 + ((173 / 1580) : ℂ) * ζ ^ 23 - ((97 / 395) : ℂ) * ζ ^ 24 + ((135 / 316) : ℂ) * ζ ^ 25 - ((123 / 1580) : ℂ) * ζ ^ 26 + ((118 / 395) : ℂ) * ζ ^ 27 - ((1 / 10) : ℂ) * ζ ^ 28 + ((17 / 395) : ℂ) * ζ ^ 29 - ((12 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_3_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 3 =
      (-((3909 / 17380) : ℂ) + ((2621 / 8690) : ℂ) * ζ ^ 1 - ((8727 / 17380) : ℂ) * ζ ^ 2 + ((4167 / 8690) : ℂ) * ζ ^ 3 - ((27 / 8690) : ℂ) * ζ ^ 5 - ((3609 / 8690) : ℂ) * ζ ^ 6 + ((10007 / 17380) : ℂ) * ζ ^ 8 - ((8489 / 17380) : ℂ) * ζ ^ 9 + ((943 / 17380) : ℂ) * ζ ^ 11 + ((3911 / 17380) : ℂ) * ζ ^ 12 - ((2621 / 8690) : ℂ) * ζ ^ 13 - ((613 / 8690) : ℂ) * ζ ^ 15 - ((2621 / 8690) : ℂ) * ζ ^ 17 + ((1774 / 4345) : ℂ) * ζ ^ 18 - ((2707 / 8690) : ℂ) * ζ ^ 21 + ((8727 / 17380) : ℂ) * ζ ^ 22 - ((6473 / 17380) : ℂ) * ζ ^ 24 + ((1324 / 4345) : ℂ) * ζ ^ 25 + ((1547 / 4345) : ℂ) * ζ ^ 27 - ((10007 / 17380) : ℂ) * ζ ^ 28 + ((2621 / 8690) : ℂ) * ζ ^ 29 - ((2669 / 17380) : ℂ) * ζ ^ 30 - ((943 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((933 / 3476) : ℂ) - ((309 / 1580) : ℂ) * ζ ^ 1 + ((4143 / 8690) : ℂ) * ζ ^ 2 - ((1609 / 3476) : ℂ) * ζ ^ 3 - ((787 / 8690) : ℂ) * ζ ^ 4 + ((2143 / 8690) : ℂ) * ζ ^ 5 + ((21 / 395) : ℂ) * ζ ^ 6 + ((233 / 1738) : ℂ) * ζ ^ 7 - ((4541 / 17380) : ℂ) * ζ ^ 8 + ((2493 / 17380) : ℂ) * ζ ^ 9 - ((17 / 869) : ℂ) * ζ ^ 10 - ((783 / 4345) : ℂ) * ζ ^ 11 - ((197 / 1738) : ℂ) * ζ ^ 12 - ((128 / 4345) : ℂ) * ζ ^ 13 + ((1973 / 8690) : ℂ) * ζ ^ 14 - ((233 / 17380) : ℂ) * ζ ^ 15 - ((857 / 8690) : ℂ) * ζ ^ 16 - ((3 / 790) : ℂ) * ζ ^ 17 - ((3461 / 17380) : ℂ) * ζ ^ 18 + ((1899 / 17380) : ℂ) * ζ ^ 19 - ((177 / 8690) : ℂ) * ζ ^ 20 + ((1691 / 8690) : ℂ) * ζ ^ 21 - ((4677 / 17380) : ℂ) * ζ ^ 22 - ((207 / 8690) : ℂ) * ζ ^ 23 + ((734 / 4345) : ℂ) * ζ ^ 24 - ((2397 / 8690) : ℂ) * ζ ^ 25 + ((2289 / 8690) : ℂ) * ζ ^ 26 - ((4087 / 17380) : ℂ) * ζ ^ 27 + ((4651 / 17380) : ℂ) * ζ ^ 28 + ((312 / 4345) : ℂ) * ζ ^ 29 - ((6 / 55) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_3_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 3 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_3_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 3 =
      (((23 / 220) : ℂ) + ((9 / 110) : ℂ) * ζ ^ 2 - ((17 / 110) : ℂ) * ζ ^ 3 + ((21 / 110) : ℂ) * ζ ^ 6 - ((6 / 55) : ℂ) * ζ ^ 8 + ((1 / 110) : ℂ) * ζ ^ 11 - ((31 / 110) : ℂ) * ζ ^ 12 + ((51 / 220) : ℂ) * ζ ^ 15 + ((1 / 220) : ℂ) * ζ ^ 18 - ((9 / 110) : ℂ) * ζ ^ 22 - ((29 / 220) : ℂ) * ζ ^ 24 + ((7 / 220) : ℂ) * ζ ^ 27 + ((6 / 55) : ℂ) * ζ ^ 28 + ((13 / 110) : ℂ) * ζ ^ 30 - ((1 / 110) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((23 / 220) : ℂ) - ((9 / 110) : ℂ) * ζ ^ 2)

private theorem row18_transformedGeneratorA_term_6_3_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 3 =
      (((41 / 220) : ℂ) - ((3 / 220) : ℂ) * ζ ^ 1 + ((39 / 220) : ℂ) * ζ ^ 3 + ((4 / 55) : ℂ) * ζ ^ 5 - ((19 / 110) : ℂ) * ζ ^ 8 - ((29 / 220) : ℂ) * ζ ^ 9 - ((3 / 55) : ℂ) * ζ ^ 11 + ((21 / 220) : ℂ) * ζ ^ 12 + ((3 / 220) : ℂ) * ζ ^ 13 - ((31 / 220) : ℂ) * ζ ^ 15 + ((3 / 220) : ℂ) * ζ ^ 17 + ((14 / 55) : ℂ) * ζ ^ 21 - ((23 / 220) : ℂ) * ζ ^ 24 - ((19 / 220) : ℂ) * ζ ^ 25 + ((13 / 220) : ℂ) * ζ ^ 27 + ((19 / 110) : ℂ) * ζ ^ 28 - ((3 / 220) : ℂ) * ζ ^ 29 + ((3 / 55) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_6_3 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        6 3 =
      alternatingSixAmbientRow18TransformedGeneratorA
        6 3 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_6_3_0,
      row18_transformedGeneratorA_term_6_3_1,
      row18_transformedGeneratorA_term_6_3_2,
      row18_transformedGeneratorA_term_6_3_3,
      row18_transformedGeneratorA_term_6_3_4,
      row18_transformedGeneratorA_term_6_3_5,
      row18_transformedGeneratorA_term_6_3_6,
      row18_transformedGeneratorA_term_6_3_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_4_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 4 =
      (((603 / 8690) : ℂ) + ((769 / 8690) : ℂ) * ζ ^ 1 + ((1611 / 17380) : ℂ) * ζ ^ 2 + ((74 / 4345) : ℂ) * ζ ^ 3 - ((673 / 8690) : ℂ) * ζ ^ 5 - ((421 / 17380) : ℂ) * ζ ^ 6 + ((838 / 4345) : ℂ) * ζ ^ 8 - ((881 / 17380) : ℂ) * ζ ^ 9 - ((1263 / 17380) : ℂ) * ζ ^ 11 - ((411 / 4345) : ℂ) * ζ ^ 12 - ((769 / 8690) : ℂ) * ζ ^ 13 - ((276 / 4345) : ℂ) * ζ ^ 15 - ((769 / 8690) : ℂ) * ζ ^ 17 + ((911 / 8690) : ℂ) * ζ ^ 18 - ((1054 / 4345) : ℂ) * ζ ^ 21 - ((1611 / 17380) : ℂ) * ζ ^ 22 + ((457 / 17380) : ℂ) * ζ ^ 24 + ((721 / 4345) : ℂ) * ζ ^ 25 + ((758 / 4345) : ℂ) * ζ ^ 27 - ((838 / 4345) : ℂ) * ζ ^ 28 + ((769 / 8690) : ℂ) * ζ ^ 29 - ((1083 / 17380) : ℂ) * ζ ^ 30 + ((1263 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1107 / 8690) : ℂ) - ((3391 / 17380) : ℂ) * ζ ^ 1 - ((818 / 4345) : ℂ) * ζ ^ 2 - ((1579 / 8690) : ℂ) * ζ ^ 3 + ((579 / 17380) : ℂ) * ζ ^ 4 + ((501 / 3476) : ℂ) * ζ ^ 5 + ((13 / 17380) : ℂ) * ζ ^ 6 + ((821 / 8690) : ℂ) * ζ ^ 7 - ((2149 / 8690) : ℂ) * ζ ^ 8 + ((21 / 790) : ℂ) * ζ ^ 9 + ((1191 / 17380) : ℂ) * ζ ^ 10 + ((923 / 3476) : ℂ) * ζ ^ 11 + ((2353 / 8690) : ℂ) * ζ ^ 12 + ((353 / 4345) : ℂ) * ζ ^ 13 + ((183 / 1738) : ℂ) * ζ ^ 14 - ((1449 / 8690) : ℂ) * ζ ^ 15 - ((33 / 395) : ℂ) * ζ ^ 16 + ((69 / 8690) : ℂ) * ζ ^ 17 - ((27 / 17380) : ℂ) * ζ ^ 18 - ((32 / 4345) : ℂ) * ζ ^ 19 + ((1833 / 17380) : ℂ) * ζ ^ 20 + ((625 / 3476) : ℂ) * ζ ^ 21 + ((2039 / 17380) : ℂ) * ζ ^ 22 + ((343 / 17380) : ℂ) * ζ ^ 23 + ((94 / 4345) : ℂ) * ζ ^ 24 - ((497 / 4345) : ℂ) * ζ ^ 25 - ((311 / 1738) : ℂ) * ζ ^ 26 - ((479 / 1738) : ℂ) * ζ ^ 27 - ((85 / 869) : ℂ) * ζ ^ 28 - ((13 / 17380) : ℂ) * ζ ^ 29 - ((41 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_4_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 4 =
      (-((824 / 4345) : ℂ) + ((3973 / 17380) : ℂ) * ζ ^ 1 - ((27 / 17380) : ℂ) * ζ ^ 2 + ((371 / 8690) : ℂ) * ζ ^ 3 + ((499 / 17380) : ℂ) * ζ ^ 5 + ((768 / 4345) : ℂ) * ζ ^ 6 + ((1873 / 17380) : ℂ) * ζ ^ 8 - ((1523 / 8690) : ℂ) * ζ ^ 9 + ((2509 / 17380) : ℂ) * ζ ^ 11 + ((657 / 8690) : ℂ) * ζ ^ 12 - ((3973 / 17380) : ℂ) * ζ ^ 13 + ((427 / 17380) : ℂ) * ζ ^ 15 - ((3973 / 17380) : ℂ) * ζ ^ 17 - ((2999 / 17380) : ℂ) * ζ ^ 18 + ((337 / 8690) : ℂ) * ζ ^ 21 + ((27 / 17380) : ℂ) * ζ ^ 22 - ((1997 / 17380) : ℂ) * ζ ^ 24 + ((1737 / 8690) : ℂ) * ζ ^ 25 - ((761 / 17380) : ℂ) * ζ ^ 27 - ((1873 / 17380) : ℂ) * ζ ^ 28 + ((3973 / 17380) : ℂ) * ζ ^ 29 + ((1493 / 8690) : ℂ) * ζ ^ 30 - ((2509 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((761 / 4345) : ℂ) - ((4357 / 17380) : ℂ) * ζ ^ 1 - ((39 / 8690) : ℂ) * ζ ^ 2 - ((49 / 869) : ℂ) * ζ ^ 3 - ((681 / 4345) : ℂ) * ζ ^ 4 + ((585 / 3476) : ℂ) * ζ ^ 5 - ((2901 / 17380) : ℂ) * ζ ^ 6 + ((325 / 3476) : ℂ) * ζ ^ 7 + ((12 / 395) : ℂ) * ζ ^ 8 - ((807 / 17380) : ℂ) * ζ ^ 9 + ((112 / 4345) : ℂ) * ζ ^ 10 - ((2843 / 17380) : ℂ) * ζ ^ 11 + ((9 / 220) : ℂ) * ζ ^ 12 + ((17 / 1580) : ℂ) * ζ ^ 13 - ((467 / 3476) : ℂ) * ζ ^ 14 + ((377 / 4345) : ℂ) * ζ ^ 15 + ((31 / 869) : ℂ) * ζ ^ 16 + ((2451 / 17380) : ℂ) * ζ ^ 17 + ((839 / 17380) : ℂ) * ζ ^ 18 - ((343 / 8690) : ℂ) * ζ ^ 19 + ((3371 / 17380) : ℂ) * ζ ^ 20 - ((281 / 4345) : ℂ) * ζ ^ 21 + ((26 / 869) : ℂ) * ζ ^ 22 - ((1231 / 17380) : ℂ) * ζ ^ 23 + ((87 / 3476) : ℂ) * ζ ^ 24 + ((118 / 4345) : ℂ) * ζ ^ 25 - ((115 / 1738) : ℂ) * ζ ^ 26 + ((593 / 17380) : ℂ) * ζ ^ 27 - ((96 / 4345) : ℂ) * ζ ^ 28 + ((111 / 4345) : ℂ) * ζ ^ 29 - ((111 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_4_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 4 =
      (((72 / 869) : ℂ) - ((1523 / 17380) : ℂ) * ζ ^ 1 + ((701 / 17380) : ℂ) * ζ ^ 2 - ((453 / 8690) : ℂ) * ζ ^ 3 + ((303 / 8690) : ℂ) * ζ ^ 5 - ((549 / 4345) : ℂ) * ζ ^ 6 - ((45 / 869) : ℂ) * ζ ^ 8 + ((5041 / 17380) : ℂ) * ζ ^ 9 - ((438 / 4345) : ℂ) * ζ ^ 11 + ((525 / 3476) : ℂ) * ζ ^ 12 + ((1523 / 17380) : ℂ) * ζ ^ 13 + ((259 / 17380) : ℂ) * ζ ^ 15 + ((1523 / 17380) : ℂ) * ζ ^ 17 - ((3 / 55) : ℂ) * ζ ^ 18 - ((409 / 17380) : ℂ) * ζ ^ 21 - ((701 / 17380) : ℂ) * ζ ^ 22 + ((147 / 1738) : ℂ) * ζ ^ 24 - ((2129 / 17380) : ℂ) * ζ ^ 25 + ((619 / 8690) : ℂ) * ζ ^ 27 + ((45 / 869) : ℂ) * ζ ^ 28 - ((1523 / 17380) : ℂ) * ζ ^ 29 - ((1269 / 8690) : ℂ) * ζ ^ 30 + ((438 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((72 / 869) : ℂ) + ((25 / 869) : ℂ) * ζ ^ 1 + ((751 / 17380) : ℂ) * ζ ^ 2 - ((273 / 8690) : ℂ) * ζ ^ 3 + ((1737 / 17380) : ℂ) * ζ ^ 4 - ((1811 / 17380) : ℂ) * ζ ^ 5 + ((2447 / 17380) : ℂ) * ζ ^ 6 + ((141 / 17380) : ℂ) * ζ ^ 7 - ((181 / 1580) : ℂ) * ζ ^ 8 - ((49 / 1580) : ℂ) * ζ ^ 9 - ((4263 / 17380) : ℂ) * ζ ^ 10 + ((712 / 4345) : ℂ) * ζ ^ 11 - ((4439 / 17380) : ℂ) * ζ ^ 12 + ((1833 / 8690) : ℂ) * ζ ^ 13 + ((249 / 8690) : ℂ) * ζ ^ 14 - ((1923 / 17380) : ℂ) * ζ ^ 15 + ((365 / 3476) : ℂ) * ζ ^ 16 - ((765 / 3476) : ℂ) * ζ ^ 17 + ((2061 / 17380) : ℂ) * ζ ^ 18 - ((391 / 17380) : ℂ) * ζ ^ 19 - ((1549 / 17380) : ℂ) * ζ ^ 20 + ((54 / 395) : ℂ) * ζ ^ 21 - ((2129 / 17380) : ℂ) * ζ ^ 22 + ((278 / 4345) : ℂ) * ζ ^ 23 + ((73 / 4345) : ℂ) * ζ ^ 24 - ((149 / 4345) : ℂ) * ζ ^ 25 + ((3241 / 17380) : ℂ) * ζ ^ 26 - ((617 / 4345) : ℂ) * ζ ^ 27 + ((498 / 4345) : ℂ) * ζ ^ 28 - ((174 / 4345) : ℂ) * ζ ^ 29 + ((87 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_4_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 4 =
      (((18 / 395) : ℂ) - ((84 / 395) : ℂ) * ζ ^ 1 + ((129 / 1580) : ℂ) * ζ ^ 2 - ((1 / 1580) : ℂ) * ζ ^ 3 - ((113 / 1580) : ℂ) * ζ ^ 5 + ((71 / 1580) : ℂ) * ζ ^ 6 - ((321 / 1580) : ℂ) * ζ ^ 8 - ((57 / 395) : ℂ) * ζ ^ 9 + ((183 / 1580) : ℂ) * ζ ^ 11 + ((47 / 1580) : ℂ) * ζ ^ 12 + ((84 / 395) : ℂ) * ζ ^ 13 + ((16 / 395) : ℂ) * ζ ^ 15 + ((84 / 395) : ℂ) * ζ ^ 17 + ((113 / 1580) : ℂ) * ζ ^ 18 + ((133 / 395) : ℂ) * ζ ^ 21 - ((129 / 1580) : ℂ) * ζ ^ 22 - ((84 / 395) : ℂ) * ζ ^ 24 - ((223 / 1580) : ℂ) * ζ ^ 25 - ((63 / 395) : ℂ) * ζ ^ 27 + ((321 / 1580) : ℂ) * ζ ^ 28 - ((84 / 395) : ℂ) * ζ ^ 29 + ((43 / 1580) : ℂ) * ζ ^ 30 - ((183 / 1580) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((102 / 395) : ℂ) - ((67 / 790) : ℂ) * ζ ^ 1 - ((31 / 395) : ℂ) * ζ ^ 2 + ((11 / 316) : ℂ) * ζ ^ 3 + ((72 / 395) : ℂ) * ζ ^ 4 - ((89 / 1580) : ℂ) * ζ ^ 5 - ((117 / 1580) : ℂ) * ζ ^ 6 + ((23 / 316) : ℂ) * ζ ^ 7 - ((27 / 790) : ℂ) * ζ ^ 8 + ((391 / 1580) : ℂ) * ζ ^ 9 + ((19 / 790) : ℂ) * ζ ^ 10 - ((1 / 790) : ℂ) * ζ ^ 11 + ((23 / 79) : ℂ) * ζ ^ 12 - ((107 / 790) : ℂ) * ζ ^ 13 + ((153 / 1580) : ℂ) * ζ ^ 14 - ((13 / 790) : ℂ) * ζ ^ 15 - ((217 / 1580) : ℂ) * ζ ^ 16 + ((121 / 790) : ℂ) * ζ ^ 17 - ((1 / 20) : ℂ) * ζ ^ 18 - ((13 / 395) : ℂ) * ζ ^ 19 + ((149 / 1580) : ℂ) * ζ ^ 20 - ((57 / 158) : ℂ) * ζ ^ 21 + ((371 / 1580) : ℂ) * ζ ^ 22 - ((129 / 790) : ℂ) * ζ ^ 23 - ((31 / 395) : ℂ) * ζ ^ 24 + ((29 / 790) : ℂ) * ζ ^ 25 - ((261 / 1580) : ℂ) * ζ ^ 26 + ((78 / 395) : ℂ) * ζ ^ 27 - ((167 / 790) : ℂ) * ζ ^ 28 + ((16 / 395) : ℂ) * ζ ^ 29 - ((22 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_4_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 4 =
      (-((398 / 4345) : ℂ) - ((1687 / 17380) : ℂ) * ζ ^ 1 + ((971 / 17380) : ℂ) * ζ ^ 2 + ((351 / 4345) : ℂ) * ζ ^ 3 - ((873 / 8690) : ℂ) * ζ ^ 5 + ((131 / 4345) : ℂ) * ζ ^ 6 + ((2711 / 17380) : ℂ) * ζ ^ 8 + ((857 / 8690) : ℂ) * ζ ^ 9 + ((112 / 4345) : ℂ) * ζ ^ 11 + ((149 / 8690) : ℂ) * ζ ^ 12 + ((1687 / 17380) : ℂ) * ζ ^ 13 + ((699 / 17380) : ℂ) * ζ ^ 15 + ((1687 / 17380) : ℂ) * ζ ^ 17 - ((137 / 4345) : ℂ) * ζ ^ 18 - ((1213 / 8690) : ℂ) * ζ ^ 21 - ((971 / 17380) : ℂ) * ζ ^ 22 + ((303 / 8690) : ℂ) * ζ ^ 24 + ((59 / 17380) : ℂ) * ζ ^ 25 + ((289 / 8690) : ℂ) * ζ ^ 27 - ((2711 / 17380) : ℂ) * ζ ^ 28 - ((1687 / 17380) : ℂ) * ζ ^ 29 + ((521 / 8690) : ℂ) * ζ ^ 30 - ((112 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((461 / 4345) : ℂ) + ((482 / 4345) : ℂ) * ζ ^ 1 - ((81 / 790) : ℂ) * ζ ^ 2 - ((833 / 17380) : ℂ) * ζ ^ 3 - ((183 / 3476) : ℂ) * ζ ^ 4 - ((499 / 17380) : ℂ) * ζ ^ 5 + ((277 / 4345) : ℂ) * ζ ^ 6 + ((603 / 8690) : ℂ) * ζ ^ 7 - ((217 / 4345) : ℂ) * ζ ^ 8 + ((351 / 8690) : ℂ) * ζ ^ 9 + ((23 / 395) : ℂ) * ζ ^ 10 + ((19 / 17380) : ℂ) * ζ ^ 11 + ((139 / 1580) : ℂ) * ζ ^ 12 + ((117 / 4345) : ℂ) * ζ ^ 13 + ((309 / 8690) : ℂ) * ζ ^ 14 - ((377 / 3476) : ℂ) * ζ ^ 15 - ((226 / 4345) : ℂ) * ζ ^ 16 - ((633 / 17380) : ℂ) * ζ ^ 17 + ((13 / 1580) : ℂ) * ζ ^ 18 + ((626 / 4345) : ℂ) * ζ ^ 19 + ((511 / 17380) : ℂ) * ζ ^ 20 + ((1987 / 17380) : ℂ) * ζ ^ 21 - ((149 / 3476) : ℂ) * ζ ^ 22 - ((344 / 4345) : ℂ) * ζ ^ 23 - ((1081 / 17380) : ℂ) * ζ ^ 24 - ((749 / 8690) : ℂ) * ζ ^ 25 + ((117 / 17380) : ℂ) * ζ ^ 26 + ((31 / 4345) : ℂ) * ζ ^ 27 + ((691 / 17380) : ℂ) * ζ ^ 28 + ((6 / 869) : ℂ) * ζ ^ 29 - ((42 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_4_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 4 =
      (((1 / 22) : ℂ) + ((1 / 22) : ℂ) * ζ ^ 1 - ((1 / 11) : ℂ) * ζ ^ 3 + ((1 / 11) : ℂ) * ζ ^ 5 - ((1 / 11) : ℂ) * ζ ^ 8 + ((1 / 44) : ℂ) * ζ ^ 9 - ((3 / 44) : ℂ) * ζ ^ 11 - ((3 / 44) : ℂ) * ζ ^ 12 - ((1 / 22) : ℂ) * ζ ^ 13 - ((5 / 44) : ℂ) * ζ ^ 15 - ((1 / 22) : ℂ) * ζ ^ 17 + ((1 / 4) : ℂ) * ζ ^ 18 + ((3 / 44) : ℂ) * ζ ^ 21 + ((2 / 11) : ℂ) * ζ ^ 24 - ((1 / 22) : ℂ) * ζ ^ 25 - ((5 / 44) : ℂ) * ζ ^ 27 + ((1 / 11) : ℂ) * ζ ^ 28 + ((1 / 22) : ℂ) * ζ ^ 29 + ((3 / 44) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_4_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 4 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_4_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 4 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_6_4 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        6 4 =
      alternatingSixAmbientRow18TransformedGeneratorA
        6 4 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_6_4_0,
      row18_transformedGeneratorA_term_6_4_1,
      row18_transformedGeneratorA_term_6_4_2,
      row18_transformedGeneratorA_term_6_4_3,
      row18_transformedGeneratorA_term_6_4_4,
      row18_transformedGeneratorA_term_6_4_5,
      row18_transformedGeneratorA_term_6_4_6,
      row18_transformedGeneratorA_term_6_4_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_5_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 5 =
      (((203 / 3476) : ℂ) - ((19 / 1738) : ℂ) * ζ ^ 1 + ((369 / 8690) : ℂ) * ζ ^ 2 - ((1388 / 4345) : ℂ) * ζ ^ 3 - ((239 / 869) : ℂ) * ζ ^ 5 + ((1173 / 4345) : ℂ) * ζ ^ 6 - ((93 / 1738) : ℂ) * ζ ^ 8 + ((355 / 3476) : ℂ) * ζ ^ 9 + ((2711 / 17380) : ℂ) * ζ ^ 11 - ((94 / 869) : ℂ) * ζ ^ 12 + ((19 / 1738) : ℂ) * ζ ^ 13 + ((2773 / 17380) : ℂ) * ζ ^ 15 + ((19 / 1738) : ℂ) * ζ ^ 17 - ((117 / 8690) : ℂ) * ζ ^ 18 - ((23 / 1738) : ℂ) * ζ ^ 21 - ((369 / 8690) : ℂ) * ζ ^ 22 + ((383 / 3476) : ℂ) * ζ ^ 24 + ((459 / 1738) : ℂ) * ζ ^ 25 + ((991 / 17380) : ℂ) * ζ ^ 27 + ((93 / 1738) : ℂ) * ζ ^ 28 - ((19 / 1738) : ℂ) * ζ ^ 29 + ((2073 / 8690) : ℂ) * ζ ^ 30 - ((2711 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((791 / 8690) : ℂ) + ((73 / 17380) : ℂ) * ζ ^ 1 + ((91 / 8690) : ℂ) * ζ ^ 2 + ((4127 / 17380) : ℂ) * ζ ^ 3 + ((251 / 8690) : ℂ) * ζ ^ 4 + ((6837 / 17380) : ℂ) * ζ ^ 5 - ((647 / 4345) : ℂ) * ζ ^ 6 - ((2933 / 17380) : ℂ) * ζ ^ 7 + ((2361 / 17380) : ℂ) * ζ ^ 8 - ((4251 / 17380) : ℂ) * ζ ^ 9 + ((987 / 3476) : ℂ) * ζ ^ 10 + ((1293 / 3476) : ℂ) * ζ ^ 11 + ((1877 / 17380) : ℂ) * ζ ^ 12 + ((388 / 4345) : ℂ) * ζ ^ 13 - ((2631 / 8690) : ℂ) * ζ ^ 14 - ((543 / 4345) : ℂ) * ζ ^ 15 - ((1907 / 17380) : ℂ) * ζ ^ 16 - ((646 / 4345) : ℂ) * ζ ^ 17 - ((1407 / 8690) : ℂ) * ζ ^ 18 - ((159 / 790) : ℂ) * ζ ^ 19 + ((2253 / 17380) : ℂ) * ζ ^ 20 - ((1041 / 17380) : ℂ) * ζ ^ 21 + ((166 / 4345) : ℂ) * ζ ^ 22 + ((3629 / 17380) : ℂ) * ζ ^ 23 - ((721 / 17380) : ℂ) * ζ ^ 24 - ((849 / 17380) : ℂ) * ζ ^ 25 - ((1069 / 8690) : ℂ) * ζ ^ 26 - ((889 / 3476) : ℂ) * ζ ^ 27 - ((1513 / 17380) : ℂ) * ζ ^ 28 - ((7 / 8690) : ℂ) * ζ ^ 29 - ((37 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_5_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 5 =
      (-((3613 / 17380) : ℂ) - ((779 / 4345) : ℂ) * ζ ^ 1 + ((39 / 158) : ℂ) * ζ ^ 2 - ((2021 / 8690) : ℂ) * ζ ^ 3 - ((1843 / 17380) : ℂ) * ζ ^ 5 - ((11 / 316) : ℂ) * ζ ^ 6 - ((1073 / 8690) : ℂ) * ζ ^ 8 + ((1797 / 17380) : ℂ) * ζ ^ 9 + ((973 / 8690) : ℂ) * ζ ^ 11 + ((2091 / 8690) : ℂ) * ζ ^ 12 + ((779 / 4345) : ℂ) * ζ ^ 13 + ((2653 / 17380) : ℂ) * ζ ^ 15 + ((779 / 4345) : ℂ) * ζ ^ 17 - ((81 / 316) : ℂ) * ζ ^ 18 - ((1699 / 8690) : ℂ) * ζ ^ 21 - ((39 / 158) : ℂ) * ζ ^ 22 - ((471 / 17380) : ℂ) * ζ ^ 24 - ((1273 / 17380) : ℂ) * ζ ^ 25 - ((346 / 4345) : ℂ) * ζ ^ 27 + ((1073 / 8690) : ℂ) * ζ ^ 28 - ((779 / 4345) : ℂ) * ζ ^ 29 + ((9 / 158) : ℂ) * ζ ^ 30 - ((973 / 8690) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((877 / 4345) : ℂ) + ((545 / 3476) : ℂ) * ζ ^ 1 - ((2573 / 8690) : ℂ) * ζ ^ 2 + ((4393 / 17380) : ℂ) * ζ ^ 3 - ((471 / 4345) : ℂ) * ζ ^ 4 - ((1571 / 17380) : ℂ) * ζ ^ 5 + ((3697 / 8690) : ℂ) * ζ ^ 6 - ((4369 / 17380) : ℂ) * ζ ^ 7 + ((3001 / 8690) : ℂ) * ζ ^ 8 + ((96 / 869) : ℂ) * ζ ^ 9 - ((1313 / 4345) : ℂ) * ζ ^ 10 + ((77 / 790) : ℂ) * ζ ^ 11 - ((2803 / 8690) : ℂ) * ζ ^ 12 - ((56 / 4345) : ℂ) * ζ ^ 13 + ((57 / 1580) : ℂ) * ζ ^ 14 - ((846 / 4345) : ℂ) * ζ ^ 15 + ((877 / 8690) : ℂ) * ζ ^ 16 - ((23 / 316) : ℂ) * ζ ^ 17 + ((1697 / 8690) : ℂ) * ζ ^ 18 + ((3367 / 17380) : ℂ) * ζ ^ 19 - ((83 / 790) : ℂ) * ζ ^ 20 + ((16 / 79) : ℂ) * ζ ^ 21 + ((138 / 4345) : ℂ) * ζ ^ 22 + ((818 / 4345) : ℂ) * ζ ^ 23 - ((13 / 17380) : ℂ) * ζ ^ 24 + ((24 / 4345) : ℂ) * ζ ^ 25 + ((4943 / 17380) : ℂ) * ζ ^ 26 - ((41 / 17380) : ℂ) * ζ ^ 27 + ((1897 / 17380) : ℂ) * ζ ^ 28 + ((333 / 17380) : ℂ) * ζ ^ 29 + ((666 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_5_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 5 =
      (((607 / 17380) : ℂ) + ((13 / 220) : ℂ) * ζ ^ 1 - ((2339 / 8690) : ℂ) * ζ ^ 2 - ((993 / 17380) : ℂ) * ζ ^ 3 - ((1987 / 8690) : ℂ) * ζ ^ 5 - ((5287 / 17380) : ℂ) * ζ ^ 6 - ((419 / 4345) : ℂ) * ζ ^ 8 - ((4409 / 17380) : ℂ) * ζ ^ 9 - ((291 / 17380) : ℂ) * ζ ^ 11 + ((288 / 4345) : ℂ) * ζ ^ 12 - ((13 / 220) : ℂ) * ζ ^ 13 + ((3607 / 17380) : ℂ) * ζ ^ 15 - ((13 / 220) : ℂ) * ζ ^ 17 + ((4299 / 17380) : ℂ) * ζ ^ 18 - ((489 / 17380) : ℂ) * ζ ^ 21 + ((2339 / 8690) : ℂ) * ζ ^ 22 - ((1191 / 17380) : ℂ) * ζ ^ 24 + ((5001 / 17380) : ℂ) * ζ ^ 25 + ((247 / 8690) : ℂ) * ζ ^ 27 + ((419 / 4345) : ℂ) * ζ ^ 28 + ((13 / 220) : ℂ) * ζ ^ 29 + ((447 / 8690) : ℂ) * ζ ^ 30 + ((291 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((943 / 17380) : ℂ) - ((458 / 4345) : ℂ) * ζ ^ 1 + ((3503 / 17380) : ℂ) * ζ ^ 2 + ((1899 / 17380) : ℂ) * ζ ^ 3 - ((1041 / 17380) : ℂ) * ζ ^ 4 + ((2847 / 8690) : ℂ) * ζ ^ 5 - ((111 / 1580) : ℂ) * ζ ^ 6 - ((126 / 4345) : ℂ) * ζ ^ 7 + ((771 / 17380) : ℂ) * ζ ^ 8 - ((243 / 8690) : ℂ) * ζ ^ 9 + ((1973 / 17380) : ℂ) * ζ ^ 10 + ((89 / 4345) : ℂ) * ζ ^ 11 - ((1351 / 17380) : ℂ) * ζ ^ 12 - ((147 / 1580) : ℂ) * ζ ^ 13 + ((2049 / 8690) : ℂ) * ζ ^ 14 - ((2283 / 17380) : ℂ) * ζ ^ 15 + ((1261 / 8690) : ℂ) * ζ ^ 16 - ((751 / 17380) : ℂ) * ζ ^ 17 - ((557 / 3476) : ℂ) * ζ ^ 18 + ((831 / 17380) : ℂ) * ζ ^ 19 - ((768 / 4345) : ℂ) * ζ ^ 20 - ((181 / 4345) : ℂ) * ζ ^ 21 - ((342 / 4345) : ℂ) * ζ ^ 22 - ((7 / 110) : ℂ) * ζ ^ 23 + ((243 / 3476) : ℂ) * ζ ^ 24 - ((2213 / 17380) : ℂ) * ζ ^ 25 + ((384 / 4345) : ℂ) * ζ ^ 26 + ((91 / 17380) : ℂ) * ζ ^ 27 - ((163 / 3476) : ℂ) * ζ ^ 28 + ((1189 / 8690) : ℂ) * ζ ^ 29 - ((493 / 1738) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_5_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 5 =
      (((101 / 1580) : ℂ) + ((105 / 316) : ℂ) * ζ ^ 1 - ((67 / 790) : ℂ) * ζ ^ 2 + ((153 / 395) : ℂ) * ζ ^ 3 + ((113 / 316) : ℂ) * ζ ^ 5 - ((271 / 1580) : ℂ) * ζ ^ 6 + ((171 / 790) : ℂ) * ζ ^ 8 - ((31 / 316) : ℂ) * ζ ^ 9 - ((94 / 395) : ℂ) * ζ ^ 11 - ((126 / 395) : ℂ) * ζ ^ 12 - ((105 / 316) : ℂ) * ζ ^ 13 - ((503 / 1580) : ℂ) * ζ ^ 15 - ((105 / 316) : ℂ) * ζ ^ 17 + ((17 / 1580) : ℂ) * ζ ^ 18 - ((16 / 79) : ℂ) * ζ ^ 21 + ((67 / 790) : ℂ) * ζ ^ 22 + ((133 / 395) : ℂ) * ζ ^ 24 - ((2 / 79) : ℂ) * ζ ^ 25 - ((44 / 395) : ℂ) * ζ ^ 27 - ((171 / 790) : ℂ) * ζ ^ 28 + ((105 / 316) : ℂ) * ζ ^ 29 - ((493 / 1580) : ℂ) * ζ ^ 30 + ((94 / 395) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((53 / 316) : ℂ) - ((47 / 395) : ℂ) * ζ ^ 1 - ((163 / 1580) : ℂ) * ζ ^ 2 - ((897 / 1580) : ℂ) * ζ ^ 3 - ((25 / 158) : ℂ) * ζ ^ 4 - ((241 / 790) : ℂ) * ζ ^ 5 - ((37 / 158) : ℂ) * ζ ^ 6 + ((107 / 790) : ℂ) * ζ ^ 7 - ((99 / 316) : ℂ) * ζ ^ 8 - ((393 / 1580) : ℂ) * ζ ^ 9 + ((51 / 790) : ℂ) * ζ ^ 10 - ((177 / 790) : ℂ) * ζ ^ 11 + ((6 / 79) : ℂ) * ζ ^ 12 - ((11 / 316) : ℂ) * ζ ^ 13 + ((73 / 1580) : ℂ) * ζ ^ 14 + ((146 / 395) : ℂ) * ζ ^ 15 - ((277 / 1580) : ℂ) * ζ ^ 16 + ((17 / 158) : ℂ) * ζ ^ 17 + ((229 / 790) : ℂ) * ζ ^ 18 - ((233 / 1580) : ℂ) * ζ ^ 19 + ((122 / 395) : ℂ) * ζ ^ 20 + ((413 / 1580) : ℂ) * ζ ^ 21 - ((87 / 1580) : ℂ) * ζ ^ 22 + ((629 / 1580) : ℂ) * ζ ^ 23 - ((287 / 1580) : ℂ) * ζ ^ 24 + ((647 / 1580) : ℂ) * ζ ^ 25 + ((2 / 79) : ℂ) * ζ ^ 26 - ((113 / 790) : ℂ) * ζ ^ 27 + ((579 / 1580) : ℂ) * ζ ^ 28 - ((17 / 395) : ℂ) * ζ ^ 29 + ((87 / 790) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_5_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 5 =
      (((199 / 3476) : ℂ) - ((433 / 3476) : ℂ) * ζ ^ 1 + ((1927 / 4345) : ℂ) * ζ ^ 2 - ((4561 / 17380) : ℂ) * ζ ^ 3 - ((173 / 3476) : ℂ) * ζ ^ 5 + ((2301 / 8690) : ℂ) * ζ ^ 6 - ((265 / 1738) : ℂ) * ζ ^ 8 + ((1021 / 3476) : ℂ) * ζ ^ 9 + ((2669 / 8690) : ℂ) * ζ ^ 11 - ((10 / 869) : ℂ) * ζ ^ 12 + ((433 / 3476) : ℂ) * ζ ^ 13 + ((1071 / 4345) : ℂ) * ζ ^ 15 + ((433 / 3476) : ℂ) * ζ ^ 17 - ((5469 / 17380) : ℂ) * ζ ^ 18 + ((59 / 869) : ℂ) * ζ ^ 21 - ((1927 / 4345) : ℂ) * ζ ^ 22 - ((73 / 3476) : ℂ) * ζ ^ 24 - ((65 / 869) : ℂ) * ζ ^ 25 - ((953 / 4345) : ℂ) * ζ ^ 27 + ((265 / 1738) : ℂ) * ζ ^ 28 - ((433 / 3476) : ℂ) * ζ ^ 29 + ((6141 / 17380) : ℂ) * ζ ^ 30 - ((2669 / 8690) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((239 / 17380) : ℂ) + ((953 / 4345) : ℂ) * ζ ^ 1 - ((342 / 869) : ℂ) * ζ ^ 2 + ((1948 / 4345) : ℂ) * ζ ^ 3 + ((29 / 395) : ℂ) * ζ ^ 4 - ((167 / 1738) : ℂ) * ζ ^ 5 + ((2173 / 8690) : ℂ) * ζ ^ 6 - ((2077 / 17380) : ℂ) * ζ ^ 7 + ((64 / 395) : ℂ) * ζ ^ 8 + ((248 / 4345) : ℂ) * ζ ^ 9 - ((276 / 4345) : ℂ) * ζ ^ 10 + ((233 / 8690) : ℂ) * ζ ^ 11 + ((447 / 17380) : ℂ) * ζ ^ 12 + ((404 / 4345) : ℂ) * ζ ^ 13 - ((1539 / 17380) : ℂ) * ζ ^ 14 - ((1087 / 8690) : ℂ) * ζ ^ 15 + ((1349 / 8690) : ℂ) * ζ ^ 16 - ((63 / 1580) : ℂ) * ζ ^ 17 - ((67 / 3476) : ℂ) * ζ ^ 18 + ((1429 / 17380) : ℂ) * ζ ^ 19 - ((1763 / 17380) : ℂ) * ζ ^ 20 - ((867 / 8690) : ℂ) * ζ ^ 21 + ((211 / 790) : ℂ) * ζ ^ 22 - ((3601 / 17380) : ℂ) * ζ ^ 23 + ((2169 / 17380) : ℂ) * ζ ^ 24 + ((173 / 3476) : ℂ) * ζ ^ 25 - ((1022 / 4345) : ℂ) * ζ ^ 26 + ((1252 / 4345) : ℂ) * ζ ^ 27 - ((793 / 4345) : ℂ) * ζ ^ 28 - ((312 / 4345) : ℂ) * ζ ^ 29 + ((312 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_5_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 5 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_5_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 5 =
      (-((4 / 55) : ℂ) - ((41 / 220) : ℂ) * ζ ^ 1 - ((91 / 220) : ℂ) * ζ ^ 2 + ((17 / 220) : ℂ) * ζ ^ 5 - ((29 / 220) : ℂ) * ζ ^ 6 + ((43 / 220) : ℂ) * ζ ^ 8 + ((7 / 220) : ℂ) * ζ ^ 9 + ((6 / 55) : ℂ) * ζ ^ 12 + ((41 / 220) : ℂ) * ζ ^ 13 + ((41 / 220) : ℂ) * ζ ^ 17 + ((53 / 220) : ℂ) * ζ ^ 18 + ((8 / 55) : ℂ) * ζ ^ 21 + ((91 / 220) : ℂ) * ζ ^ 22 - ((21 / 110) : ℂ) * ζ ^ 24 - ((29 / 110) : ℂ) * ζ ^ 25 - ((43 / 220) : ℂ) * ζ ^ 28 - ((41 / 220) : ℂ) * ζ ^ 29 - ((13 / 55) : ℂ) * ζ ^ 30) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((4 / 55) : ℂ) + ((7 / 220) : ℂ) * ζ ^ 1 + ((17 / 55) : ℂ) * ζ ^ 2 + ((2 / 55) : ℂ) * ζ ^ 4 - ((29 / 110) : ℂ) * ζ ^ 5 - ((43 / 110) : ℂ) * ζ ^ 6 - ((27 / 220) : ℂ) * ζ ^ 8 + ((53 / 220) : ℂ) * ζ ^ 9 + ((23 / 220) : ℂ) * ζ ^ 10 + ((37 / 220) : ℂ) * ζ ^ 12 + ((13 / 55) : ℂ) * ζ ^ 14 - ((7 / 220) : ℂ) * ζ ^ 17 - ((3 / 22) : ℂ) * ζ ^ 18 - ((2 / 55) : ℂ) * ζ ^ 20 + ((9 / 220) : ℂ) * ζ ^ 21 + ((6 / 55) : ℂ) * ζ ^ 22 + ((13 / 110) : ℂ) * ζ ^ 24 - ((1 / 110) : ℂ) * ζ ^ 25 - ((23 / 220) : ℂ) * ζ ^ 26 - ((9 / 110) : ℂ) * ζ ^ 28)

private theorem row18_transformedGeneratorA_term_6_5_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 5 =
      (((41 / 220) : ℂ) - ((3 / 220) : ℂ) * ζ ^ 1 + ((39 / 220) : ℂ) * ζ ^ 3 + ((4 / 55) : ℂ) * ζ ^ 5 - ((19 / 110) : ℂ) * ζ ^ 8 - ((29 / 220) : ℂ) * ζ ^ 9 - ((3 / 55) : ℂ) * ζ ^ 11 + ((21 / 220) : ℂ) * ζ ^ 12 + ((3 / 220) : ℂ) * ζ ^ 13 - ((31 / 220) : ℂ) * ζ ^ 15 + ((3 / 220) : ℂ) * ζ ^ 17 + ((14 / 55) : ℂ) * ζ ^ 21 - ((23 / 220) : ℂ) * ζ ^ 24 - ((19 / 220) : ℂ) * ζ ^ 25 + ((13 / 220) : ℂ) * ζ ^ 27 + ((19 / 110) : ℂ) * ζ ^ 28 - ((3 / 220) : ℂ) * ζ ^ 29 + ((3 / 55) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_6_5 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        6 5 =
      alternatingSixAmbientRow18TransformedGeneratorA
        6 5 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_6_5_0,
      row18_transformedGeneratorA_term_6_5_1,
      row18_transformedGeneratorA_term_6_5_2,
      row18_transformedGeneratorA_term_6_5_3,
      row18_transformedGeneratorA_term_6_5_4,
      row18_transformedGeneratorA_term_6_5_5,
      row18_transformedGeneratorA_term_6_5_6,
      row18_transformedGeneratorA_term_6_5_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_6_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 6 =
      (((125 / 3476) : ℂ) + ((2731 / 17380) : ℂ) * ζ ^ 1 - ((19 / 1738) : ℂ) * ζ ^ 2 - ((1747 / 17380) : ℂ) * ζ ^ 3 - ((1141 / 8690) : ℂ) * ζ ^ 5 + ((249 / 1738) : ℂ) * ζ ^ 6 + ((185 / 869) : ℂ) * ζ ^ 8 - ((1247 / 17380) : ℂ) * ζ ^ 9 - ((1599 / 17380) : ℂ) * ζ ^ 11 - ((29 / 869) : ℂ) * ζ ^ 12 - ((2731 / 17380) : ℂ) * ζ ^ 13 + ((1163 / 17380) : ℂ) * ζ ^ 15 - ((2731 / 17380) : ℂ) * ζ ^ 17 - ((293 / 3476) : ℂ) * ζ ^ 18 - ((2597 / 17380) : ℂ) * ζ ^ 21 + ((19 / 1738) : ℂ) * ζ ^ 22 + ((195 / 1738) : ℂ) * ζ ^ 24 + ((5013 / 17380) : ℂ) * ζ ^ 25 - ((141 / 4345) : ℂ) * ζ ^ 27 - ((185 / 869) : ℂ) * ζ ^ 28 + ((2731 / 17380) : ℂ) * ζ ^ 29 + ((731 / 3476) : ℂ) * ζ ^ 30 + ((1599 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1633 / 17380) : ℂ) - ((3639 / 17380) : ℂ) * ζ ^ 1 + ((227 / 4345) : ℂ) * ζ ^ 2 + ((2553 / 17380) : ℂ) * ζ ^ 3 + ((1893 / 17380) : ℂ) * ζ ^ 4 + ((1211 / 3476) : ℂ) * ζ ^ 5 - ((787 / 8690) : ℂ) * ζ ^ 6 - ((1037 / 17380) : ℂ) * ζ ^ 7 - ((393 / 1738) : ℂ) * ζ ^ 8 - ((1891 / 17380) : ℂ) * ζ ^ 9 + ((963 / 8690) : ℂ) * ζ ^ 10 + ((163 / 790) : ℂ) * ζ ^ 11 + ((3001 / 17380) : ℂ) * ζ ^ 12 - ((97 / 4345) : ℂ) * ζ ^ 13 - ((2531 / 17380) : ℂ) * ζ ^ 14 - ((3219 / 17380) : ℂ) * ζ ^ 15 - ((1069 / 17380) : ℂ) * ζ ^ 16 + ((443 / 8690) : ℂ) * ζ ^ 17 + ((49 / 17380) : ℂ) * ζ ^ 18 + ((227 / 17380) : ℂ) * ζ ^ 19 + ((1641 / 17380) : ℂ) * ζ ^ 20 - ((153 / 8690) : ℂ) * ζ ^ 21 - ((1281 / 17380) : ℂ) * ζ ^ 22 - ((37 / 17380) : ℂ) * ζ ^ 23 + ((819 / 17380) : ℂ) * ζ ^ 24 + ((17 / 1738) : ℂ) * ζ ^ 25 + ((393 / 8690) : ℂ) * ζ ^ 26 - ((307 / 4345) : ℂ) * ζ ^ 27 - ((701 / 17380) : ℂ) * ζ ^ 28 + ((13 / 17380) : ℂ) * ζ ^ 29 - ((17 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_6_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 6 =
      (((1883 / 17380) : ℂ) + ((43 / 4345) : ℂ) * ζ ^ 1 - ((207 / 1738) : ℂ) * ζ ^ 2 - ((2129 / 17380) : ℂ) * ζ ^ 3 + ((1173 / 8690) : ℂ) * ζ ^ 5 - ((285 / 1738) : ℂ) * ζ ^ 6 - ((2589 / 17380) : ℂ) * ζ ^ 8 + ((153 / 8690) : ℂ) * ζ ^ 9 + ((1158 / 4345) : ℂ) * ζ ^ 11 - ((487 / 17380) : ℂ) * ζ ^ 12 - ((43 / 4345) : ℂ) * ζ ^ 13 - ((409 / 17380) : ℂ) * ζ ^ 15 - ((43 / 4345) : ℂ) * ζ ^ 17 + ((5 / 44) : ℂ) * ζ ^ 18 - ((106 / 4345) : ℂ) * ζ ^ 21 + ((207 / 1738) : ℂ) * ζ ^ 22 + ((1361 / 17380) : ℂ) * ζ ^ 24 - ((1087 / 8690) : ℂ) * ζ ^ 25 - ((893 / 17380) : ℂ) * ζ ^ 27 + ((2589 / 17380) : ℂ) * ζ ^ 28 + ((43 / 4345) : ℂ) * ζ ^ 29 + ((139 / 3476) : ℂ) * ζ ^ 30 - ((1158 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((427 / 3476) : ℂ) - ((307 / 4345) : ℂ) * ζ ^ 1 + ((1151 / 17380) : ℂ) * ζ ^ 2 + ((3177 / 17380) : ℂ) * ζ ^ 3 + ((3159 / 17380) : ℂ) * ζ ^ 4 - ((853 / 8690) : ℂ) * ζ ^ 5 + ((507 / 8690) : ℂ) * ζ ^ 6 - ((1911 / 8690) : ℂ) * ζ ^ 7 + ((653 / 17380) : ℂ) * ζ ^ 8 + ((423 / 8690) : ℂ) * ζ ^ 9 - ((327 / 4345) : ℂ) * ζ ^ 10 - ((1069 / 17380) : ℂ) * ζ ^ 11 + ((14 / 395) : ℂ) * ζ ^ 12 + ((31 / 8690) : ℂ) * ζ ^ 13 + ((629 / 4345) : ℂ) * ζ ^ 14 + ((8 / 4345) : ℂ) * ζ ^ 15 - ((1 / 8690) : ℂ) * ζ ^ 16 - ((16 / 395) : ℂ) * ζ ^ 17 - ((101 / 8690) : ℂ) * ζ ^ 18 - ((23 / 869) : ℂ) * ζ ^ 19 - ((411 / 17380) : ℂ) * ζ ^ 20 - ((271 / 4345) : ℂ) * ζ ^ 21 + ((457 / 4345) : ℂ) * ζ ^ 22 - ((107 / 3476) : ℂ) * ζ ^ 23 + ((179 / 8690) : ℂ) * ζ ^ 24 - ((2 / 395) : ℂ) * ζ ^ 25 + ((268 / 4345) : ℂ) * ζ ^ 26 - ((199 / 17380) : ℂ) * ζ ^ 27 - ((296 / 4345) : ℂ) * ζ ^ 28 - ((111 / 4345) : ℂ) * ζ ^ 29)

private theorem row18_transformedGeneratorA_term_6_6_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 6 =
      (-((50 / 869) : ℂ) + ((1189 / 8690) : ℂ) * ζ ^ 1 + ((3629 / 17380) : ℂ) * ζ ^ 2 + ((521 / 17380) : ℂ) * ζ ^ 3 - ((439 / 4345) : ℂ) * ζ ^ 5 + ((1104 / 4345) : ℂ) * ζ ^ 6 + ((829 / 3476) : ℂ) * ζ ^ 8 - ((3211 / 17380) : ℂ) * ζ ^ 9 - ((827 / 4345) : ℂ) * ζ ^ 11 + ((861 / 3476) : ℂ) * ζ ^ 12 - ((1189 / 8690) : ℂ) * ζ ^ 13 - ((436 / 4345) : ℂ) * ζ ^ 15 - ((1189 / 8690) : ℂ) * ζ ^ 17 - ((4177 / 17380) : ℂ) * ζ ^ 18 - ((464 / 4345) : ℂ) * ζ ^ 21 - ((3629 / 17380) : ℂ) * ζ ^ 22 - ((389 / 1738) : ℂ) * ζ ^ 24 + ((2067 / 8690) : ℂ) * ζ ^ 25 + ((433 / 4345) : ℂ) * ζ ^ 27 - ((829 / 3476) : ℂ) * ζ ^ 28 + ((1189 / 8690) : ℂ) * ζ ^ 29 + ((212 / 4345) : ℂ) * ζ ^ 30 + ((827 / 4345) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((50 / 869) : ℂ) - ((1437 / 8690) : ℂ) * ζ ^ 1 - ((101 / 395) : ℂ) * ζ ^ 2 - ((147 / 4345) : ℂ) * ζ ^ 3 - ((214 / 4345) : ℂ) * ζ ^ 4 + ((1326 / 4345) : ℂ) * ζ ^ 5 - ((961 / 17380) : ℂ) * ζ ^ 6 + ((993 / 17380) : ℂ) * ζ ^ 7 - ((4299 / 17380) : ℂ) * ζ ^ 8 + ((31 / 4345) : ℂ) * ζ ^ 9 + ((239 / 8690) : ℂ) * ζ ^ 10 + ((786 / 4345) : ℂ) * ζ ^ 11 - ((124 / 4345) : ℂ) * ζ ^ 12 - ((1051 / 8690) : ℂ) * ζ ^ 13 - ((4743 / 17380) : ℂ) * ζ ^ 14 - ((241 / 3476) : ℂ) * ζ ^ 15 + ((107 / 1580) : ℂ) * ζ ^ 16 + ((2381 / 17380) : ℂ) * ζ ^ 17 + ((1 / 5) : ℂ) * ζ ^ 18 - ((1753 / 17380) : ℂ) * ζ ^ 19 - ((779 / 8690) : ℂ) * ζ ^ 21 + ((507 / 17380) : ℂ) * ζ ^ 22 + ((488 / 4345) : ℂ) * ζ ^ 23 + ((2933 / 17380) : ℂ) * ζ ^ 24 - ((637 / 8690) : ℂ) * ζ ^ 25 + ((278 / 4345) : ℂ) * ζ ^ 26 - ((701 / 4345) : ℂ) * ζ ^ 27 + ((67 / 790) : ℂ) * ζ ^ 28 + ((174 / 4345) : ℂ) * ζ ^ 29 + ((609 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_6_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 6 =
      (-((63 / 790) : ℂ) - ((98 / 395) : ℂ) * ζ ^ 1 - ((379 / 1580) : ℂ) * ζ ^ 2 + ((59 / 316) : ℂ) * ζ ^ 3 + ((239 / 1580) : ℂ) * ζ ^ 5 - ((84 / 395) : ℂ) * ζ ^ 6 - ((231 / 790) : ℂ) * ζ ^ 8 + ((71 / 395) : ℂ) * ζ ^ 9 + ((61 / 316) : ℂ) * ζ ^ 11 - ((73 / 790) : ℂ) * ζ ^ 12 + ((98 / 395) : ℂ) * ζ ^ 13 + ((1 / 79) : ℂ) * ζ ^ 15 + ((98 / 395) : ℂ) * ζ ^ 17 - ((43 / 1580) : ℂ) * ζ ^ 18 + ((167 / 790) : ℂ) * ζ ^ 21 + ((379 / 1580) : ℂ) * ζ ^ 22 - ((3 / 20) : ℂ) * ζ ^ 24 - ((631 / 1580) : ℂ) * ζ ^ 25 + ((7 / 79) : ℂ) * ζ ^ 27 + ((231 / 790) : ℂ) * ζ ^ 28 - ((98 / 395) : ℂ) * ζ ^ 29 - ((42 / 395) : ℂ) * ζ ^ 30 - ((61 / 316) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((21 / 158) : ℂ) - ((18 / 395) : ℂ) * ζ ^ 1 + ((199 / 1580) : ℂ) * ζ ^ 2 - ((171 / 1580) : ℂ) * ζ ^ 3 + ((108 / 395) : ℂ) * ζ ^ 4 - ((177 / 1580) : ℂ) * ζ ^ 5 - ((1 / 790) : ℂ) * ζ ^ 6 + ((1 / 1580) : ℂ) * ζ ^ 7 - ((57 / 1580) : ℂ) * ζ ^ 8 + ((301 / 1580) : ℂ) * ζ ^ 9 + ((12 / 79) : ℂ) * ζ ^ 10 - ((61 / 790) : ℂ) * ζ ^ 11 + ((53 / 316) : ℂ) * ζ ^ 12 + ((17 / 790) : ℂ) * ζ ^ 13 + ((103 / 1580) : ℂ) * ζ ^ 14 + ((29 / 395) : ℂ) * ζ ^ 15 - ((17 / 158) : ℂ) * ζ ^ 16 - ((37 / 790) : ℂ) * ζ ^ 17 + ((131 / 790) : ℂ) * ζ ^ 18 + ((2 / 79) : ℂ) * ζ ^ 19 + ((15 / 158) : ℂ) * ζ ^ 20 - ((171 / 790) : ℂ) * ζ ^ 21 - ((223 / 1580) : ℂ) * ζ ^ 22 - ((47 / 790) : ℂ) * ζ ^ 23 + ((17 / 395) : ℂ) * ζ ^ 24 - ((2 / 395) : ℂ) * ζ ^ 25 + ((19 / 1580) : ℂ) * ζ ^ 26 - ((117 / 790) : ℂ) * ζ ^ 27 + ((11 / 1580) : ℂ) * ζ ^ 28 - ((16 / 395) : ℂ) * ζ ^ 29 + ((1 / 158) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_6_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 6 =
      (-((8 / 4345) : ℂ) - ((577 / 8690) : ℂ) * ζ ^ 1 + ((19 / 869) : ℂ) * ζ ^ 2 + ((327 / 3476) : ℂ) * ζ ^ 3 - ((867 / 17380) : ℂ) * ζ ^ 5 - ((18 / 869) : ℂ) * ζ ^ 6 + ((269 / 4345) : ℂ) * ζ ^ 8 - ((41 / 8690) : ℂ) * ζ ^ 9 - ((225 / 3476) : ℂ) * ζ ^ 11 - ((1877 / 17380) : ℂ) * ζ ^ 12 + ((577 / 8690) : ℂ) * ζ ^ 13 + ((351 / 3476) : ℂ) * ζ ^ 15 + ((577 / 8690) : ℂ) * ζ ^ 17 + ((443 / 3476) : ℂ) * ζ ^ 18 - ((321 / 8690) : ℂ) * ζ ^ 21 - ((19 / 869) : ℂ) * ζ ^ 22 + ((893 / 8690) : ℂ) * ζ ^ 24 - ((287 / 17380) : ℂ) * ζ ^ 25 - ((25 / 869) : ℂ) * ζ ^ 27 - ((269 / 4345) : ℂ) * ζ ^ 28 - ((577 / 8690) : ℂ) * ζ ^ 29 - ((269 / 1738) : ℂ) * ζ ^ 30 + ((225 / 3476) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((71 / 4345) : ℂ) + ((751 / 17380) : ℂ) * ζ ^ 1 - ((1157 / 8690) : ℂ) * ζ ^ 2 - ((163 / 1738) : ℂ) * ζ ^ 3 - ((2653 / 17380) : ℂ) * ζ ^ 4 - ((413 / 17380) : ℂ) * ζ ^ 5 - ((239 / 4345) : ℂ) * ζ ^ 6 + ((1257 / 17380) : ℂ) * ζ ^ 7 + ((931 / 17380) : ℂ) * ζ ^ 8 + ((177 / 3476) : ℂ) * ζ ^ 9 + ((1443 / 8690) : ℂ) * ζ ^ 10 + ((359 / 17380) : ℂ) * ζ ^ 11 + ((265 / 1738) : ℂ) * ζ ^ 12 + ((273 / 4345) : ℂ) * ζ ^ 13 + ((477 / 17380) : ℂ) * ζ ^ 14 - ((362 / 4345) : ℂ) * ζ ^ 15 - ((189 / 4345) : ℂ) * ζ ^ 16 - ((543 / 8690) : ℂ) * ζ ^ 17 + ((1521 / 17380) : ℂ) * ζ ^ 18 + ((532 / 4345) : ℂ) * ζ ^ 19 + ((101 / 1738) : ℂ) * ζ ^ 20 + ((301 / 3476) : ℂ) * ζ ^ 21 - ((117 / 8690) : ℂ) * ζ ^ 22 - ((1459 / 17380) : ℂ) * ζ ^ 23 - ((144 / 869) : ℂ) * ζ ^ 24 - ((97 / 3476) : ℂ) * ζ ^ 25 - ((2153 / 17380) : ℂ) * ζ ^ 26 + ((235 / 3476) : ℂ) * ζ ^ 27 - ((19 / 8690) : ℂ) * ζ ^ 28 - ((6 / 869) : ℂ) * ζ ^ 29 + ((84 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_6_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 6 =
      (((1 / 22) : ℂ) + ((1 / 22) : ℂ) * ζ ^ 1 - ((1 / 11) : ℂ) * ζ ^ 3 + ((1 / 11) : ℂ) * ζ ^ 5 - ((1 / 11) : ℂ) * ζ ^ 8 + ((1 / 44) : ℂ) * ζ ^ 9 - ((3 / 44) : ℂ) * ζ ^ 11 - ((3 / 44) : ℂ) * ζ ^ 12 - ((1 / 22) : ℂ) * ζ ^ 13 - ((5 / 44) : ℂ) * ζ ^ 15 - ((1 / 22) : ℂ) * ζ ^ 17 + ((1 / 4) : ℂ) * ζ ^ 18 + ((3 / 44) : ℂ) * ζ ^ 21 + ((2 / 11) : ℂ) * ζ ^ 24 - ((1 / 22) : ℂ) * ζ ^ 25 - ((5 / 44) : ℂ) * ζ ^ 27 + ((1 / 11) : ℂ) * ζ ^ 28 + ((1 / 22) : ℂ) * ζ ^ 29 + ((3 / 44) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_6_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 6 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_6_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 6 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_6_6 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        6 6 =
      alternatingSixAmbientRow18TransformedGeneratorA
        6 6 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_6_6_0,
      row18_transformedGeneratorA_term_6_6_1,
      row18_transformedGeneratorA_term_6_6_2,
      row18_transformedGeneratorA_term_6_6_3,
      row18_transformedGeneratorA_term_6_6_4,
      row18_transformedGeneratorA_term_6_6_5,
      row18_transformedGeneratorA_term_6_6_6,
      row18_transformedGeneratorA_term_6_6_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_7_0 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 0 *
        alternatingSixAmbientRow18Eigenbasis
          0 7 =
      (-((1061 / 17380) : ℂ) + ((1591 / 8690) : ℂ) * ζ ^ 1 + ((2067 / 8690) : ℂ) * ζ ^ 2 + ((2773 / 17380) : ℂ) * ζ ^ 3 - ((709 / 17380) : ℂ) * ζ ^ 5 - ((421 / 4345) : ℂ) * ζ ^ 6 + ((813 / 17380) : ℂ) * ζ ^ 8 - ((111 / 4345) : ℂ) * ζ ^ 9 - ((1619 / 17380) : ℂ) * ζ ^ 11 - ((929 / 4345) : ℂ) * ζ ^ 12 - ((1591 / 8690) : ℂ) * ζ ^ 13 + ((1313 / 17380) : ℂ) * ζ ^ 15 - ((1591 / 8690) : ℂ) * ζ ^ 17 - ((3437 / 17380) : ℂ) * ζ ^ 18 - ((1739 / 17380) : ℂ) * ζ ^ 21 - ((2067 / 8690) : ℂ) * ζ ^ 22 + ((563 / 17380) : ℂ) * ζ ^ 24 + ((3891 / 17380) : ℂ) * ζ ^ 25 + ((1134 / 4345) : ℂ) * ζ ^ 27 - ((813 / 17380) : ℂ) * ζ ^ 28 + ((1591 / 8690) : ℂ) * ζ ^ 29 + ((457 / 4345) : ℂ) * ζ ^ 30 + ((1619 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((247 / 8690) : ℂ) - ((368 / 4345) : ℂ) * ζ ^ 1 - ((3537 / 17380) : ℂ) * ζ ^ 2 - ((1427 / 3476) : ℂ) * ζ ^ 3 - ((588 / 4345) : ℂ) * ζ ^ 4 + ((1887 / 17380) : ℂ) * ζ ^ 5 + ((2251 / 8690) : ℂ) * ζ ^ 6 + ((5941 / 17380) : ℂ) * ζ ^ 7 + ((175 / 1738) : ℂ) * ζ ^ 8 - ((449 / 1738) : ℂ) * ζ ^ 9 - ((1769 / 8690) : ℂ) * ζ ^ 10 + ((1002 / 4345) : ℂ) * ζ ^ 11 + ((71 / 220) : ℂ) * ζ ^ 12 + ((160 / 869) : ℂ) * ζ ^ 13 + ((229 / 8690) : ℂ) * ζ ^ 14 - ((6267 / 17380) : ℂ) * ζ ^ 15 - ((1388 / 4345) : ℂ) * ζ ^ 16 - ((81 / 1738) : ℂ) * ζ ^ 17 + ((4043 / 17380) : ℂ) * ζ ^ 18 + ((4091 / 17380) : ℂ) * ζ ^ 19 + ((2619 / 8690) : ℂ) * ζ ^ 20 + ((569 / 4345) : ℂ) * ζ ^ 21 - ((809 / 8690) : ℂ) * ζ ^ 22 - ((898 / 4345) : ℂ) * ζ ^ 23 - ((483 / 3476) : ℂ) * ζ ^ 24 + ((2811 / 17380) : ℂ) * ζ ^ 25 + ((94 / 869) : ℂ) * ζ ^ 26 - ((3401 / 17380) : ℂ) * ζ ^ 27 - ((305 / 3476) : ℂ) * ζ ^ 28 + ((7 / 8690) : ℂ) * ζ ^ 29 - ((19 / 8690) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_7_1 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0) *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0) 7 =
      (-((1807 / 4345) : ℂ) - ((974 / 4345) : ℂ) * ζ ^ 1 - ((423 / 1738) : ℂ) * ζ ^ 2 - ((1258 / 4345) : ℂ) * ζ ^ 3 - ((763 / 17380) : ℂ) * ζ ^ 5 - ((115 / 3476) : ℂ) * ζ ^ 6 + ((2756 / 4345) : ℂ) * ζ ^ 8 + ((4377 / 17380) : ℂ) * ζ ^ 9 - ((61 / 220) : ℂ) * ζ ^ 11 + ((3771 / 8690) : ℂ) * ζ ^ 12 + ((974 / 4345) : ℂ) * ζ ^ 13 - ((647 / 17380) : ℂ) * ζ ^ 15 + ((974 / 4345) : ℂ) * ζ ^ 17 + ((987 / 3476) : ℂ) * ζ ^ 18 + ((5167 / 17380) : ℂ) * ζ ^ 21 + ((423 / 1738) : ℂ) * ζ ^ 22 - ((8001 / 17380) : ℂ) * ζ ^ 24 - ((3133 / 17380) : ℂ) * ζ ^ 25 - ((857 / 8690) : ℂ) * ζ ^ 27 - ((2756 / 4345) : ℂ) * ζ ^ 28 - ((974 / 4345) : ℂ) * ζ ^ 29 + ((87 / 3476) : ℂ) * ζ ^ 30 + ((61 / 220) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((7123 / 17380) : ℂ) + ((445 / 1738) : ℂ) * ζ ^ 1 + ((2911 / 8690) : ℂ) * ζ ^ 2 + ((4399 / 17380) : ℂ) * ζ ^ 3 - ((8259 / 17380) : ℂ) * ζ ^ 4 - ((806 / 4345) : ℂ) * ζ ^ 5 - ((6097 / 17380) : ℂ) * ζ ^ 6 - ((4423 / 17380) : ℂ) * ζ ^ 7 - ((4513 / 17380) : ℂ) * ζ ^ 8 - ((1767 / 8690) : ℂ) * ζ ^ 9 + ((755 / 3476) : ℂ) * ζ ^ 10 + ((5509 / 8690) : ℂ) * ζ ^ 11 + ((2899 / 17380) : ℂ) * ζ ^ 12 + ((799 / 17380) : ℂ) * ζ ^ 13 + ((9 / 3476) : ℂ) * ζ ^ 14 - ((1053 / 8690) : ℂ) * ζ ^ 15 + ((146 / 4345) : ℂ) * ζ ^ 16 - ((4223 / 17380) : ℂ) * ζ ^ 17 - ((2599 / 8690) : ℂ) * ζ ^ 18 + ((359 / 3476) : ℂ) * ζ ^ 19 + ((647 / 8690) : ℂ) * ζ ^ 20 + ((2527 / 17380) : ℂ) * ζ ^ 21 + ((87 / 3476) : ℂ) * ζ ^ 22 + ((535 / 3476) : ℂ) * ζ ^ 23 + ((2657 / 17380) : ℂ) * ζ ^ 24 - ((21 / 790) : ℂ) * ζ ^ 25 - ((994 / 4345) : ℂ) * ζ ^ 26 - ((287 / 17380) : ℂ) * ζ ^ 27 - ((859 / 8690) : ℂ) * ζ ^ 28 - ((333 / 17380) : ℂ) * ζ ^ 29 - ((3441 / 17380) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_7_2 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ 7 =
      (-((436 / 4345) : ℂ) - ((3607 / 17380) : ℂ) * ζ ^ 1 - ((437 / 3476) : ℂ) * ζ ^ 2 + ((53 / 316) : ℂ) * ζ ^ 3 + ((959 / 17380) : ℂ) * ζ ^ 5 + ((75 / 1738) : ℂ) * ζ ^ 6 - ((483 / 17380) : ℂ) * ζ ^ 8 + ((7409 / 17380) : ℂ) * ζ ^ 9 + ((1 / 316) : ℂ) * ζ ^ 11 - ((721 / 4345) : ℂ) * ζ ^ 12 + ((3607 / 17380) : ℂ) * ζ ^ 13 - ((7 / 158) : ℂ) * ζ ^ 15 + ((3607 / 17380) : ℂ) * ζ ^ 17 - ((427 / 3476) : ℂ) * ζ ^ 18 - ((741 / 17380) : ℂ) * ζ ^ 21 + ((437 / 3476) : ℂ) * ζ ^ 22 - ((1062 / 4345) : ℂ) * ζ ^ 24 - ((2283 / 8690) : ℂ) * ζ ^ 25 + ((6 / 79) : ℂ) * ζ ^ 27 + ((483 / 17380) : ℂ) * ζ ^ 28 - ((3607 / 17380) : ℂ) * ζ ^ 29 - ((53 / 869) : ℂ) * ζ ^ 30 - ((1 / 316) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((1647 / 8690) : ℂ) + ((3453 / 17380) : ℂ) * ζ ^ 1 + ((3217 / 17380) : ℂ) * ζ ^ 2 - ((2677 / 17380) : ℂ) * ζ ^ 3 - ((866 / 4345) : ℂ) * ζ ^ 4 - ((2319 / 8690) : ℂ) * ζ ^ 5 - ((234 / 4345) : ℂ) * ζ ^ 6 + ((641 / 8690) : ℂ) * ζ ^ 7 + ((1897 / 17380) : ℂ) * ζ ^ 8 - ((1869 / 17380) : ℂ) * ζ ^ 9 + ((431 / 8690) : ℂ) * ζ ^ 10 + ((263 / 3476) : ℂ) * ζ ^ 11 + ((4343 / 17380) : ℂ) * ζ ^ 12 + ((4259 / 17380) : ℂ) * ζ ^ 13 + ((255 / 3476) : ℂ) * ζ ^ 14 + ((111 / 3476) : ℂ) * ζ ^ 15 - ((585 / 3476) : ℂ) * ζ ^ 16 - ((1591 / 17380) : ℂ) * ζ ^ 17 + ((126 / 4345) : ℂ) * ζ ^ 18 - ((1373 / 17380) : ℂ) * ζ ^ 19 + ((2007 / 8690) : ℂ) * ζ ^ 20 + ((29 / 790) : ℂ) * ζ ^ 21 - ((1083 / 17380) : ℂ) * ζ ^ 22 + ((531 / 8690) : ℂ) * ζ ^ 23 - ((29 / 3476) : ℂ) * ζ ^ 24 + ((1527 / 17380) : ℂ) * ζ ^ 25 + ((26 / 4345) : ℂ) * ζ ^ 26 - ((2361 / 17380) : ℂ) * ζ ^ 27 - ((258 / 4345) : ℂ) * ζ ^ 28 - ((1189 / 8690) : ℂ) * ζ ^ 29 - ((116 / 4345) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_7_3 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ 7 =
      (((81 / 790) : ℂ) + ((97 / 1580) : ℂ) * ζ ^ 1 + ((98 / 395) : ℂ) * ζ ^ 2 - ((19 / 79) : ℂ) * ζ ^ 3 - ((1 / 20) : ℂ) * ζ ^ 5 + ((139 / 790) : ℂ) * ζ ^ 6 - ((53 / 790) : ℂ) * ζ ^ 8 - ((619 / 1580) : ℂ) * ζ ^ 9 + ((2 / 79) : ℂ) * ζ ^ 11 - ((193 / 1580) : ℂ) * ζ ^ 12 - ((97 / 1580) : ℂ) * ζ ^ 13 + ((3 / 316) : ℂ) * ζ ^ 15 - ((97 / 1580) : ℂ) * ζ ^ 17 + ((61 / 395) : ℂ) * ζ ^ 18 - ((167 / 790) : ℂ) * ζ ^ 21 - ((98 / 395) : ℂ) * ζ ^ 22 + ((629 / 1580) : ℂ) * ζ ^ 24 + ((44 / 395) : ℂ) * ζ ^ 25 + ((2 / 79) : ℂ) * ζ ^ 27 + ((53 / 790) : ℂ) * ζ ^ 28 + ((97 / 1580) : ℂ) * ζ ^ 29 + ((49 / 1580) : ℂ) * ζ ^ 30 - ((2 / 79) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((51 / 395) : ℂ) + ((15 / 79) : ℂ) * ζ ^ 1 - ((47 / 316) : ℂ) * ζ ^ 2 + ((831 / 1580) : ℂ) * ζ ^ 3 + ((137 / 1580) : ℂ) * ζ ^ 4 - ((111 / 790) : ℂ) * ζ ^ 5 + ((427 / 1580) : ℂ) * ζ ^ 6 - ((37 / 395) : ℂ) * ζ ^ 7 - ((207 / 790) : ℂ) * ζ ^ 8 - ((127 / 1580) : ℂ) * ζ ^ 9 - ((313 / 1580) : ℂ) * ζ ^ 10 - ((1 / 395) : ℂ) * ζ ^ 11 - ((71 / 790) : ℂ) * ζ ^ 12 - ((433 / 1580) : ℂ) * ζ ^ 13 + ((159 / 1580) : ℂ) * ζ ^ 14 - ((3 / 79) : ℂ) * ζ ^ 15 - ((1 / 10) : ℂ) * ζ ^ 16 + ((84 / 395) : ℂ) * ζ ^ 17 - ((163 / 395) : ℂ) * ζ ^ 18 - ((141 / 1580) : ℂ) * ζ ^ 19 + ((37 / 790) : ℂ) * ζ ^ 20 + ((293 / 1580) : ℂ) * ζ ^ 21 + ((15 / 158) : ℂ) * ζ ^ 22 + ((233 / 1580) : ℂ) * ζ ^ 23 + ((4 / 395) : ℂ) * ζ ^ 24 + ((139 / 316) : ℂ) * ζ ^ 25 - ((13 / 1580) : ℂ) * ζ ^ 26 + ((94 / 395) : ℂ) * ζ ^ 27 + ((1 / 10) : ℂ) * ζ ^ 28 + ((17 / 395) : ℂ) * ζ ^ 29 + ((12 / 395) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_7_4 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ 7 =
      (((2319 / 17380) : ℂ) + ((1409 / 4345) : ℂ) * ζ ^ 1 + ((1261 / 17380) : ℂ) * ζ ^ 2 + ((278 / 4345) : ℂ) * ζ ^ 3 + ((1379 / 8690) : ℂ) * ζ ^ 5 + ((1187 / 8690) : ℂ) * ζ ^ 6 - ((5727 / 17380) : ℂ) * ζ ^ 8 - ((3067 / 17380) : ℂ) * ζ ^ 9 + ((2979 / 17380) : ℂ) * ζ ^ 11 - ((4111 / 17380) : ℂ) * ζ ^ 12 - ((1409 / 4345) : ℂ) * ζ ^ 13 + ((1531 / 8690) : ℂ) * ζ ^ 15 - ((1409 / 4345) : ℂ) * ζ ^ 17 + ((168 / 4345) : ℂ) * ζ ^ 18 - ((983 / 4345) : ℂ) * ζ ^ 21 - ((1261 / 17380) : ℂ) * ζ ^ 22 + ((2423 / 17380) : ℂ) * ζ ^ 24 + ((1439 / 8690) : ℂ) * ζ ^ 25 - ((493 / 8690) : ℂ) * ζ ^ 27 + ((5727 / 17380) : ℂ) * ζ ^ 28 + ((1409 / 4345) : ℂ) * ζ ^ 29 - ((1173 / 17380) : ℂ) * ζ ^ 30 - ((2979 / 17380) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (-((1563 / 17380) : ℂ) - ((837 / 3476) : ℂ) * ζ ^ 1 - ((639 / 4345) : ℂ) * ζ ^ 2 - ((691 / 3476) : ℂ) * ζ ^ 3 - ((382 / 4345) : ℂ) * ζ ^ 4 - ((37 / 4345) : ℂ) * ζ ^ 5 - ((291 / 790) : ℂ) * ζ ^ 6 - ((113 / 869) : ℂ) * ζ ^ 7 + ((6233 / 17380) : ℂ) * ζ ^ 8 + ((651 / 17380) : ℂ) * ζ ^ 9 + ((1129 / 4345) : ℂ) * ζ ^ 10 + ((468 / 4345) : ℂ) * ζ ^ 11 + ((130 / 869) : ℂ) * ζ ^ 12 + ((28 / 4345) : ℂ) * ζ ^ 13 - ((808 / 4345) : ℂ) * ζ ^ 14 + ((2317 / 17380) : ℂ) * ζ ^ 15 + ((1193 / 8690) : ℂ) * ζ ^ 16 - ((483 / 4345) : ℂ) * ζ ^ 17 + ((3407 / 17380) : ℂ) * ζ ^ 18 + ((2667 / 17380) : ℂ) * ζ ^ 19 - ((6 / 395) : ℂ) * ζ ^ 20 + ((851 / 8690) : ℂ) * ζ ^ 21 + ((3429 / 17380) : ℂ) * ζ ^ 22 - ((84 / 4345) : ℂ) * ζ ^ 23 - ((817 / 8690) : ℂ) * ζ ^ 24 - ((225 / 869) : ℂ) * ζ ^ 25 - ((1197 / 8690) : ℂ) * ζ ^ 26 - ((769 / 17380) : ℂ) * ζ ^ 27 - ((4651 / 17380) : ℂ) * ζ ^ 28 + ((312 / 4345) : ℂ) * ζ ^ 29 + ((6 / 55) : ℂ) * ζ ^ 30)

private theorem row18_transformedGeneratorA_term_6_7_5 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ 7 =
      0 := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_term_6_7_6 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ 7 =
      (-((23 / 220) : ℂ) - ((9 / 110) : ℂ) * ζ ^ 2 + ((17 / 110) : ℂ) * ζ ^ 3 - ((21 / 110) : ℂ) * ζ ^ 6 + ((6 / 55) : ℂ) * ζ ^ 8 - ((1 / 110) : ℂ) * ζ ^ 11 + ((31 / 110) : ℂ) * ζ ^ 12 - ((51 / 220) : ℂ) * ζ ^ 15 - ((1 / 220) : ℂ) * ζ ^ 18 + ((9 / 110) : ℂ) * ζ ^ 22 + ((29 / 220) : ℂ) * ζ ^ 24 - ((7 / 220) : ℂ) * ζ ^ 27 - ((6 / 55) : ℂ) * ζ ^ 28 - ((13 / 110) : ℂ) * ζ ^ 30 + ((1 / 110) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 (((23 / 220) : ℂ) + ((9 / 110) : ℂ) * ζ ^ 2)

private theorem row18_transformedGeneratorA_term_6_7_7 :
    alternatingSixAmbientRow18InverseTimesGeneratorA
          6 (Fin.succ 0).succ.succ.succ.succ.succ.succ *
        alternatingSixAmbientRow18Eigenbasis
          (Fin.succ 0).succ.succ.succ.succ.succ.succ 7 =
      (((41 / 220) : ℂ) - ((3 / 220) : ℂ) * ζ ^ 1 + ((39 / 220) : ℂ) * ζ ^ 3 + ((4 / 55) : ℂ) * ζ ^ 5 - ((19 / 110) : ℂ) * ζ ^ 8 - ((29 / 220) : ℂ) * ζ ^ 9 - ((3 / 55) : ℂ) * ζ ^ 11 + ((21 / 220) : ℂ) * ζ ^ 12 + ((3 / 220) : ℂ) * ζ ^ 13 - ((31 / 220) : ℂ) * ζ ^ 15 + ((3 / 220) : ℂ) * ζ ^ 17 + ((14 / 55) : ℂ) * ζ ^ 21 - ((23 / 220) : ℂ) * ζ ^ 24 - ((19 / 220) : ℂ) * ζ ^ 25 + ((13 / 220) : ℂ) * ζ ^ 27 + ((19 / 110) : ℂ) * ζ ^ 28 - ((3 / 220) : ℂ) * ζ ^ 29 + ((3 / 55) : ℂ) * ζ ^ 31) := by
  simp [
      alternatingSixAmbientRow18InverseTimesGeneratorA,
      alternatingSixAmbientRow18Eigenbasis,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

private theorem row18_transformedGeneratorA_6_7 :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        6 7 =
      alternatingSixAmbientRow18TransformedGeneratorA
        6 7 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  rw [
      row18_transformedGeneratorA_term_6_7_0,
      row18_transformedGeneratorA_term_6_7_1,
      row18_transformedGeneratorA_term_6_7_2,
      row18_transformedGeneratorA_term_6_7_3,
      row18_transformedGeneratorA_term_6_7_4,
      row18_transformedGeneratorA_term_6_7_5,
      row18_transformedGeneratorA_term_6_7_6,
      row18_transformedGeneratorA_term_6_7_7]
  simp [
      alternatingSixAmbientRow18TransformedGeneratorA,
      alternatingSixCyclotomicValue]
  try close_cyclotomic_row18 0

/-- The checked transformed-generator equality on output row
6 of ambient row 18. -/
theorem alternatingSixAmbientRow18TransformedGeneratorA_fromIntermediate_row6
    (j : Fin 8) :
    (alternatingSixAmbientRow18InverseTimesGeneratorA *
        alternatingSixAmbientRow18Eigenbasis)
        6 j =
      alternatingSixAmbientRow18TransformedGeneratorA
        6 j := by
  fin_cases j
  · exact row18_transformedGeneratorA_6_0
  · exact row18_transformedGeneratorA_6_1
  · exact row18_transformedGeneratorA_6_2
  · exact row18_transformedGeneratorA_6_3
  · exact row18_transformedGeneratorA_6_4
  · exact row18_transformedGeneratorA_6_5
  · exact row18_transformedGeneratorA_6_6
  · exact row18_transformedGeneratorA_6_7


end InductiveMcKay
end McKayConjecture
