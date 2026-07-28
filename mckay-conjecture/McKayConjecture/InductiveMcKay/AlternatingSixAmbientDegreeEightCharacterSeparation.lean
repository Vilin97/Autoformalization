/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import McKayConjecture.Character.CharacterRowSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTableDegreeEightNine
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow16DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow17DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientTwoGeneratorCharacterRow
import McKayConjecture.InductiveMcKay.AlternatingSixCyclotomicNonzero

/-!
# Separating the initial paired degree-eight ambient character rows

Rows `16` and `17` have the same dimension and central-scalar pattern.  Their
exact values at the canonical word `AB` distinguish them.
-/

noncomputable section

open Polynomial

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local notation "ζ" => alternatingSixComplexCyclotomicRoot

macro "close_degree_eight_cyclotomic" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

local instance degreeEightSeparationRow16CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row16.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance degreeEightSeparationRow17CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row17.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

/-- Normalized irreducible-character certificate for ordinary row 16. -/
def alternatingSixAmbientRow16CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow16MatrixCertificate
    |>.characterRowCertificateOfScalarCommutant
      alternatingSixAmbientRow16_scalar_commutant

/-- Normalized irreducible-character certificate for ordinary row 17. -/
def alternatingSixAmbientRow17CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow17MatrixCertificate
    |>.characterRowCertificateOfScalarCommutant
      alternatingSixAmbientRow17_scalar_commutant

@[simp]
theorem alternatingSixAmbientRow16CharacterRowCertificate_representation :
    alternatingSixAmbientRow16CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow16MatrixCertificate.universalCoverRepresentation :=
  rfl

@[simp]
theorem alternatingSixAmbientRow17CharacterRowCertificate_representation :
    alternatingSixAmbientRow17CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow17MatrixCertificate.universalCoverRepresentation :=
  rfl

/-! ### Exact `AB` traces -/

theorem alternatingSixAmbientRow16_matrixAB_trace :
    (alternatingSixFiveAmbient_row16_matrixA *
          alternatingSixFiveAmbient_row16_matrixB).trace =
      alternatingSixCyclotomicValue
        [(1, 0), (-1, 8), (-1, 12), (1, 28)] := by
  change
    (∑ i : Fin 8,
      (alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixFiveAmbient_row16_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row16_matrixA,
    alternatingSixFiveAmbient_row16_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_eight_cyclotomic
    (-(182 / 25 : ℂ) + (182 / 25 : ℂ) * ζ ^ 4 +
      14 * ζ ^ 8 - (126 / 25 : ℂ) * ζ ^ 12 -
      (17 / 25 : ℂ) * ζ ^ 16 - (16 / 25 : ℂ) * ζ ^ 20 -
      (143 / 25 : ℂ) * ζ ^ 24)

theorem alternatingSixAmbientRow17_matrixAB_trace :
    (alternatingSixFiveAmbient_row17_matrixA *
          alternatingSixFiveAmbient_row17_matrixB).trace =
      alternatingSixCyclotomicValue
        [(1, 8), (1, 12), (-1, 28)] := by
  change
    (∑ i : Fin 8,
      (alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixFiveAmbient_row17_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row17_matrixA,
    alternatingSixFiveAmbient_row17_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_eight_cyclotomic
    ((2 : ℂ) - 2 * ζ ^ 4 - 3 * ζ ^ 8 -
      2 * ζ ^ 12 + (9 / 2 : ℂ) * ζ ^ 16 -
      (1 / 4 : ℂ) * ζ ^ 20 + (5 / 2 : ℂ) * ζ ^ 24)

/-! ### Certified character values -/

theorem alternatingSixAmbientRow16_character_generatorAB :
    alternatingSixAmbientRow16CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorAB =
      alternatingSixCyclotomicValue
        [(1, 0), (-1, 8), (-1, 12), (1, 28)] := by
  rw [alternatingSixAmbientRow16CharacterRowCertificate_representation,
    alternatingSixAmbientRow16MatrixCertificate.universalCoverRepresentation_character_generatorAB]
  exact alternatingSixAmbientRow16_matrixAB_trace

theorem alternatingSixAmbientRow17_character_generatorAB :
    alternatingSixAmbientRow17CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorAB =
      alternatingSixCyclotomicValue
        [(1, 8), (1, 12), (-1, 28)] := by
  rw [alternatingSixAmbientRow17CharacterRowCertificate_representation,
    alternatingSixAmbientRow17MatrixCertificate.universalCoverRepresentation_character_generatorAB]
  exact alternatingSixAmbientRow17_matrixAB_trace

/-! ### Nonzero difference and row separation -/

def alternatingSixAmbientRow16Row17DifferencePolynomial : ℚ[X] :=
  Polynomial.C 1 - 2 * X ^ 8 - 2 * X ^ 12 + 2 * X ^ 28

theorem alternatingSixAmbientRow16Row17DifferencePolynomial_ne_zero :
    Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
        alternatingSixAmbientRow16Row17DifferencePolynomial ≠ 0 := by
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientRow16Row17DifferencePolynomial] at hvalue
  · dsimp [alternatingSixAmbientRow16Row17DifferencePolynomial]
    compute_degree
    norm_num

/-- The paired degree-eight rows are distinct irreducible characters. -/
theorem alternatingSixAmbientRow16_character_ne_row17_character :
    alternatingSixAmbientRow16CharacterRowCertificate.irreducibleCharacter ≠
      alternatingSixAmbientRow17CharacterRowCertificate.irreducibleCharacter := by
  apply
    CharacterRowCertificate.irreducibleCharacter_ne_of_character_apply_ne
      alternatingSixAmbientRow16CharacterRowCertificate
      alternatingSixAmbientRow17CharacterRowCertificate
      alternatingSixAmbientCanonicalGeneratorAB
  rw [alternatingSixAmbientRow16_character_generatorAB,
    alternatingSixAmbientRow17_character_generatorAB]
  intro hequal
  apply alternatingSixAmbientRow16Row17DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal]
  simp [
    alternatingSixAmbientRow16Row17DifferencePolynomial,
    alternatingSixCyclotomicValue]
  ring

/-! ### The next degree-eight matrix-trace pair -/

theorem alternatingSixAmbientRow18_matrixAB_trace :
    (alternatingSixFiveAmbient_row18_matrixA *
          alternatingSixFiveAmbient_row18_matrixB).trace =
      alternatingSixCyclotomicValue
        [(-1, 0), (1, 8), (1, 12), (-1, 28)] := by
  change
    (∑ i : Fin 8,
      (alternatingSixFiveAmbient_row18_matrixA *
        alternatingSixFiveAmbient_row18_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row18_matrixA,
    alternatingSixFiveAmbient_row18_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_eight_cyclotomic
    (-(7 / 11 : ℂ) + (7 / 11 : ℂ) * ζ ^ 4 -
      (103 / 55 : ℂ) * ζ ^ 8 + (111 / 55 : ℂ) * ζ ^ 12 -
      (2 / 5 : ℂ) * ζ ^ 16 - (163 / 55 : ℂ) * ζ ^ 20 +
      (89 / 55 : ℂ) * ζ ^ 24)

theorem alternatingSixAmbientRow19_matrixAB_trace :
    (alternatingSixFiveAmbient_row19_matrixA *
          alternatingSixFiveAmbient_row19_matrixB).trace =
      alternatingSixCyclotomicValue
        [(-1, 8), (-1, 12), (1, 28)] := by
  change
    (∑ i : Fin 8,
      (alternatingSixFiveAmbient_row19_matrixA *
        alternatingSixFiveAmbient_row19_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row19_matrixA,
    alternatingSixFiveAmbient_row19_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_eight_cyclotomic
    (-(13 / 11 : ℂ) + (13 / 11 : ℂ) * ζ ^ 4 -
      (7 / 11 : ℂ) * ζ ^ 8 + (42 / 11 : ℂ) * ζ ^ 12 -
      (31 / 11 : ℂ) * ζ ^ 16 + (15 / 11 : ℂ) * ζ ^ 20 +
      ζ ^ 24)

def alternatingSixAmbientRow18Row19DifferencePolynomial : ℚ[X] :=
  Polynomial.C (-1) + 2 * X ^ 8 + 2 * X ^ 12 - 2 * X ^ 28

theorem alternatingSixAmbientRow18Row19DifferencePolynomial_ne_zero :
    Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
        alternatingSixAmbientRow18Row19DifferencePolynomial ≠ 0 := by
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientRow18Row19DifferencePolynomial] at hvalue
  · dsimp [alternatingSixAmbientRow18Row19DifferencePolynomial]
    compute_degree
    norm_num

/-- The exact `AB` traces of the row-18 and row-19 matrix models differ. -/
theorem alternatingSixAmbientRow18_matrixAB_trace_ne_row19_matrixAB_trace :
    (alternatingSixFiveAmbient_row18_matrixA *
          alternatingSixFiveAmbient_row18_matrixB).trace ≠
      (alternatingSixFiveAmbient_row19_matrixA *
          alternatingSixFiveAmbient_row19_matrixB).trace := by
  rw [alternatingSixAmbientRow18_matrixAB_trace,
    alternatingSixAmbientRow19_matrixAB_trace]
  intro hequal
  apply alternatingSixAmbientRow18Row19DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal]
  simp [
    alternatingSixAmbientRow18Row19DifferencePolynomial,
    alternatingSixCyclotomicValue]
  ring

end InductiveMcKay
end McKayConjecture
