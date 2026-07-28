/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import McKayConjecture.Character.CharacterRowSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeOneThreeCharacterRows
import McKayConjecture.InductiveMcKay.AlternatingSixCyclotomicNonzero

/-!
# Separating the paired degree-three ambient character rows

The two positive and two negative order-three scalar rows have the same
dimension and central-scalar pattern.  Their values at the canonical
positive word `AB` distinguish them.  All values below are recomputed
directly from the exact generator matrices.
-/

noncomputable section

open Polynomial

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local notation "ζ" => alternatingSixComplexCyclotomicRoot

local instance degreeThreeSeparationRow02CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row02.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance degreeThreeSeparationRow03CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row03.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance degreeThreeSeparationRow04CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row04.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance degreeThreeSeparationRow05CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row05.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

macro "close_degree_three_cyclotomic" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

/-! ### Exact `AB` traces -/

theorem alternatingSixAmbientRow02_matrixAB_trace :
    (alternatingSixFiveAmbient_row02_matrixA *
          alternatingSixFiveAmbient_row02_matrixB).trace =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 8), (1, 12),
          (1, 16), (-1, 28)] := by
  change
    (∑ i : Fin 3,
      (alternatingSixFiveAmbient_row02_matrixA *
        alternatingSixFiveAmbient_row02_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row02_matrixA,
    alternatingSixFiveAmbient_row02_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_three_cyclotomic
    ((1 : ℂ) - (1 / 2 : ℂ) * ζ ^ 4 +
      (1 / 2 : ℂ) * ζ ^ 8 + ζ ^ 12 -
      (1 / 2 : ℂ) * ζ ^ 16)

theorem alternatingSixAmbientRow03_matrixAB_trace :
    (alternatingSixFiveAmbient_row03_matrixA *
          alternatingSixFiveAmbient_row03_matrixB).trace =
      alternatingSixCyclotomicValue
        [(1, 0), (1, 4), (-1, 8), (-1, 12),
          (-1, 16), (-1, 20), (1, 28)] := by
  change
    (∑ i : Fin 3,
      (alternatingSixFiveAmbient_row03_matrixA *
        alternatingSixFiveAmbient_row03_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row03_matrixA,
    alternatingSixFiveAmbient_row03_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_three_cyclotomic
    ((1 : ℂ) + ζ ^ 4 - 2 * ζ ^ 8 + ζ ^ 12 -
      (1 / 2 : ℂ) * ζ ^ 16 - ζ ^ 20 + ζ ^ 24)

theorem alternatingSixAmbientRow04_matrixAB_trace :
    (alternatingSixFiveAmbient_row04_matrixA *
          alternatingSixFiveAmbient_row04_matrixB).trace =
      alternatingSixCyclotomicValue
        [(1, 4), (-1, 16)] := by
  change
    (∑ i : Fin 3,
      (alternatingSixFiveAmbient_row04_matrixA *
        alternatingSixFiveAmbient_row04_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row04_matrixA,
    alternatingSixFiveAmbient_row04_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_three_cyclotomic
    (-(2 : ℂ) - (1 / 2 : ℂ) * ζ ^ 4 +
      (3 / 2 : ℂ) * ζ ^ 8 - (3 / 2 : ℂ) * ζ ^ 12 +
      (3 / 2 : ℂ) * ζ ^ 16 + (1 / 2 : ℂ) * ζ ^ 20 -
      (1 / 2 : ℂ) * ζ ^ 24)

theorem alternatingSixAmbientRow05_matrixAB_trace :
    (alternatingSixFiveAmbient_row05_matrixA *
          alternatingSixFiveAmbient_row05_matrixB).trace =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 16), (1, 20)] := by
  change
    (∑ i : Fin 3,
      (alternatingSixFiveAmbient_row05_matrixA *
        alternatingSixFiveAmbient_row05_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row05_matrixA,
    alternatingSixFiveAmbient_row05_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_three_cyclotomic
    ((1 : ℂ) + ζ ^ 4 + ζ ^ 8 + ζ ^ 12 - ζ ^ 16)

/-! ### Certified character values -/

theorem alternatingSixAmbientRow02_character_generatorAB :
    alternatingSixAmbientRow02CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorAB =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 8), (1, 12),
          (1, 16), (-1, 28)] := by
  rw [alternatingSixAmbientRow02CharacterRowCertificate_representation,
    alternatingSixAmbientRow02MatrixCertificate.universalCoverRepresentation_character_generatorAB]
  exact alternatingSixAmbientRow02_matrixAB_trace

theorem alternatingSixAmbientRow03_character_generatorAB :
    alternatingSixAmbientRow03CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorAB =
      alternatingSixCyclotomicValue
        [(1, 0), (1, 4), (-1, 8), (-1, 12),
          (-1, 16), (-1, 20), (1, 28)] := by
  rw [alternatingSixAmbientRow03CharacterRowCertificate_representation,
    alternatingSixAmbientRow03MatrixCertificate.universalCoverRepresentation_character_generatorAB]
  exact alternatingSixAmbientRow03_matrixAB_trace

theorem alternatingSixAmbientRow04_character_generatorAB :
    alternatingSixAmbientRow04CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorAB =
      alternatingSixCyclotomicValue
        [(1, 4), (-1, 16)] := by
  rw [alternatingSixAmbientRow04CharacterRowCertificate_representation,
    alternatingSixAmbientRow04MatrixCertificate.universalCoverRepresentation_character_generatorAB]
  exact alternatingSixAmbientRow04_matrixAB_trace

theorem alternatingSixAmbientRow05_character_generatorAB :
    alternatingSixAmbientRow05CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorAB =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 16), (1, 20)] := by
  rw [alternatingSixAmbientRow05CharacterRowCertificate_representation,
    alternatingSixAmbientRow05MatrixCertificate.universalCoverRepresentation_character_generatorAB]
  exact alternatingSixAmbientRow05_matrixAB_trace

/-! ### Nonzero differences and row separation -/

def alternatingSixAmbientRow02Row03DifferencePolynomial : ℚ[X] :=
  Polynomial.C (-2) - 2 * X ^ 4 + 2 * X ^ 8 +
    2 * X ^ 12 + 2 * X ^ 16 + X ^ 20 - 2 * X ^ 28

theorem alternatingSixAmbientRow02Row03DifferencePolynomial_ne_zero :
    Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
        alternatingSixAmbientRow02Row03DifferencePolynomial ≠ 0 := by
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientRow02Row03DifferencePolynomial] at hvalue
  · dsimp [alternatingSixAmbientRow02Row03DifferencePolynomial]
    compute_degree
    norm_num

theorem alternatingSixAmbientRow02_character_ne_row03_character :
    alternatingSixAmbientRow02CharacterRowCertificate.irreducibleCharacter ≠
      alternatingSixAmbientRow03CharacterRowCertificate.irreducibleCharacter := by
  apply
    CharacterRowCertificate.irreducibleCharacter_ne_of_character_apply_ne
      alternatingSixAmbientRow02CharacterRowCertificate
      alternatingSixAmbientRow03CharacterRowCertificate
      alternatingSixAmbientCanonicalGeneratorAB
  rw [alternatingSixAmbientRow02_character_generatorAB,
    alternatingSixAmbientRow03_character_generatorAB]
  intro hequal
  apply alternatingSixAmbientRow02Row03DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal]
  simp [
    alternatingSixAmbientRow02Row03DifferencePolynomial,
    alternatingSixCyclotomicValue]
  ring

def alternatingSixAmbientRow04Row05DifferencePolynomial : ℚ[X] :=
  Polynomial.C 1 + 2 * X ^ 4 - 2 * X ^ 16 - X ^ 20

theorem alternatingSixAmbientRow04Row05DifferencePolynomial_ne_zero :
    Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
        alternatingSixAmbientRow04Row05DifferencePolynomial ≠ 0 := by
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientRow04Row05DifferencePolynomial] at hvalue
  · dsimp [alternatingSixAmbientRow04Row05DifferencePolynomial]
    compute_degree
    norm_num

theorem alternatingSixAmbientRow04_character_ne_row05_character :
    alternatingSixAmbientRow04CharacterRowCertificate.irreducibleCharacter ≠
      alternatingSixAmbientRow05CharacterRowCertificate.irreducibleCharacter := by
  apply
    CharacterRowCertificate.irreducibleCharacter_ne_of_character_apply_ne
      alternatingSixAmbientRow04CharacterRowCertificate
      alternatingSixAmbientRow05CharacterRowCertificate
      alternatingSixAmbientCanonicalGeneratorAB
  rw [alternatingSixAmbientRow04_character_generatorAB,
    alternatingSixAmbientRow05_character_generatorAB]
  intro hequal
  apply alternatingSixAmbientRow04Row05DifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal]
  simp [
    alternatingSixAmbientRow04Row05DifferencePolynomial,
    alternatingSixCyclotomicValue]
  ring

end InductiveMcKay
end McKayConjecture
