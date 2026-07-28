/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.ComputeDegree
import McKayConjecture.Character.CharacterRowSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeFourSixCharacterRows
import McKayConjecture.InductiveMcKay.AlternatingSixCyclotomicNonzero

/-!
# Separating the paired degree-six ambient character rows

Rows `12` and `13`, and rows `14` and `15`, have the same dimensions and
central-scalar patterns.  Their exact values at the canonical second
generator distinguish each pair.
-/

noncomputable section

open Polynomial

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local notation "ζ" => alternatingSixComplexCyclotomicRoot

local instance degreeSixSeparationRow12CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row12.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance degreeSixSeparationRow13CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row13.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance degreeSixSeparationRow14CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row14.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance degreeSixSeparationRow15CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row15.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

/-! ### Exact generator traces -/

theorem alternatingSixAmbientRow12_matrixB_trace :
    alternatingSixFiveAmbient_row12_matrixB.trace =
      alternatingSixCyclotomicValue
        [(-1, 5), (-1, 15), (1, 25)] := by
  change
    (∑ i : Fin 6,
      alternatingSixFiveAmbient_row12_matrixB i i) = _
  simp [alternatingSixFiveAmbient_row12_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring_nf

theorem alternatingSixAmbientRow13_matrixB_trace :
    alternatingSixFiveAmbient_row13_matrixB.trace =
      alternatingSixCyclotomicValue
        [(1, 5), (1, 15), (-1, 25)] := by
  change
    (∑ i : Fin 6,
      alternatingSixFiveAmbient_row13_matrixB i i) = _
  simp [alternatingSixFiveAmbient_row13_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring_nf

theorem alternatingSixAmbientRow14_matrixB_trace :
    alternatingSixFiveAmbient_row14_matrixB.trace =
      alternatingSixCyclotomicValue
        [(-1, 5), (-1, 15), (1, 25)] := by
  change
    (∑ i : Fin 6,
      alternatingSixFiveAmbient_row14_matrixB i i) = _
  simp [alternatingSixFiveAmbient_row14_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring_nf

theorem alternatingSixAmbientRow15_matrixB_trace :
    alternatingSixFiveAmbient_row15_matrixB.trace =
      alternatingSixCyclotomicValue
        [(1, 5), (1, 15), (-1, 25)] := by
  change
    (∑ i : Fin 6,
      alternatingSixFiveAmbient_row15_matrixB i i) = _
  simp [alternatingSixFiveAmbient_row15_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring_nf

/-! ### Certified character values -/

theorem alternatingSixAmbientRow12_character_generatorB :
    alternatingSixAmbientRow12CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorB =
      alternatingSixCyclotomicValue
        [(-1, 5), (-1, 15), (1, 25)] := by
  rw [alternatingSixAmbientRow12CharacterRowCertificate_representation,
    alternatingSixAmbientRow12MatrixCertificate.universalCoverRepresentation_character_generatorB]
  exact alternatingSixAmbientRow12_matrixB_trace

theorem alternatingSixAmbientRow13_character_generatorB :
    alternatingSixAmbientRow13CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorB =
      alternatingSixCyclotomicValue
        [(1, 5), (1, 15), (-1, 25)] := by
  rw [alternatingSixAmbientRow13CharacterRowCertificate_representation,
    alternatingSixAmbientRow13MatrixCertificate.universalCoverRepresentation_character_generatorB]
  exact alternatingSixAmbientRow13_matrixB_trace

theorem alternatingSixAmbientRow14_character_generatorB :
    alternatingSixAmbientRow14CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorB =
      alternatingSixCyclotomicValue
        [(-1, 5), (-1, 15), (1, 25)] := by
  rw [alternatingSixAmbientRow14CharacterRowCertificate_representation,
    alternatingSixAmbientRow14MatrixCertificate.universalCoverRepresentation_character_generatorB]
  exact alternatingSixAmbientRow14_matrixB_trace

theorem alternatingSixAmbientRow15_character_generatorB :
    alternatingSixAmbientRow15CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorB =
      alternatingSixCyclotomicValue
        [(1, 5), (1, 15), (-1, 25)] := by
  rw [alternatingSixAmbientRow15CharacterRowCertificate_representation,
    alternatingSixAmbientRow15MatrixCertificate.universalCoverRepresentation_character_generatorB]
  exact alternatingSixAmbientRow15_matrixB_trace

/-! ### Nonzero difference and row separation -/

def alternatingSixAmbientDegreeSixPairedDifferencePolynomial : ℚ[X] :=
  -2 * X ^ 5 - 2 * X ^ 15 + 2 * X ^ 25

theorem alternatingSixAmbientDegreeSixPairedDifferencePolynomial_ne_zero :
    Polynomial.eval₂ (algebraMap ℚ ℂ) ζ
        alternatingSixAmbientDegreeSixPairedDifferencePolynomial ≠ 0 := by
  apply alternatingSixComplexPolynomial_eval₂_ne_zero
  · intro hzero
    have hvalue :=
      congrArg (Polynomial.eval (2 : ℚ)) hzero
    norm_num [
      alternatingSixAmbientDegreeSixPairedDifferencePolynomial] at hvalue
  · dsimp [alternatingSixAmbientDegreeSixPairedDifferencePolynomial]
    compute_degree
    norm_num

theorem alternatingSixAmbientDegreeSixPairedGeneratorValues_ne :
    alternatingSixCyclotomicValue
        [(-1, 5), (-1, 15), (1, 25)] ≠
      alternatingSixCyclotomicValue
        [(1, 5), (1, 15), (-1, 25)] := by
  intro hequal
  apply alternatingSixAmbientDegreeSixPairedDifferencePolynomial_ne_zero
  rw [← sub_eq_zero.mpr hequal]
  simp [
    alternatingSixAmbientDegreeSixPairedDifferencePolynomial,
    alternatingSixCyclotomicValue]
  ring

/-- The two degree-six rows with positive order-six central scalar are
distinct. -/
theorem alternatingSixAmbientRow12_character_ne_row13_character :
    alternatingSixAmbientRow12CharacterRowCertificate.irreducibleCharacter ≠
      alternatingSixAmbientRow13CharacterRowCertificate.irreducibleCharacter := by
  apply
    CharacterRowCertificate.irreducibleCharacter_ne_of_character_apply_ne
      alternatingSixAmbientRow12CharacterRowCertificate
      alternatingSixAmbientRow13CharacterRowCertificate
      alternatingSixAmbientCanonicalGeneratorB
  rw [alternatingSixAmbientRow12_character_generatorB,
    alternatingSixAmbientRow13_character_generatorB]
  exact alternatingSixAmbientDegreeSixPairedGeneratorValues_ne

/-- The two degree-six rows with negative order-six central scalar are
distinct. -/
theorem alternatingSixAmbientRow14_character_ne_row15_character :
    alternatingSixAmbientRow14CharacterRowCertificate.irreducibleCharacter ≠
      alternatingSixAmbientRow15CharacterRowCertificate.irreducibleCharacter := by
  apply
    CharacterRowCertificate.irreducibleCharacter_ne_of_character_apply_ne
      alternatingSixAmbientRow14CharacterRowCertificate
      alternatingSixAmbientRow15CharacterRowCertificate
      alternatingSixAmbientCanonicalGeneratorB
  rw [alternatingSixAmbientRow14_character_generatorB,
    alternatingSixAmbientRow15_character_generatorB]
  exact alternatingSixAmbientDegreeSixPairedGeneratorValues_ne

end InductiveMcKay
end McKayConjecture
