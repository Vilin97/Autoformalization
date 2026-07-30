/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeEightCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterABSquaredEvaluation

/-!
# Degree-eight values needed for the ambient outer action

This file computes the `AB²` matrix traces for rows `16`, `17`, and `18`.
Together with the already certified row-19 value, these traces identify the
two pairs exchanged by the first canonical outer automorphism.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

macro "close_degree_eight_absquared_cyclotomic" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

theorem alternatingSixAmbientRow16_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row16_matrixA *
          alternatingSixFiveAmbient_row16_matrixB *
          alternatingSixFiveAmbient_row16_matrixB).trace =
      alternatingSixCyclotomicValue
        [(1, 8), (1, 12), (-1, 28)] := by
  change
    (∑ i : Fin 8,
      (alternatingSixFiveAmbient_row16_matrixA *
        alternatingSixFiveAmbient_row16_matrixB *
        alternatingSixFiveAmbient_row16_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row16_matrixA,
    alternatingSixFiveAmbient_row16_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_eight_absquared_cyclotomic
    ((517 / 25 : ℂ) - (517 / 25 : ℂ) * ζ ^ 4 -
      (23 / 25 : ℂ) * ζ ^ 8 + 19 * ζ ^ 12 +
      (71 / 25 : ℂ) * ζ ^ 16 - (8 / 25 : ℂ) * ζ ^ 20 +
      (52 / 25 : ℂ) * ζ ^ 24 + (291 / 25 : ℂ) * ζ ^ 28 -
      (482 / 25 : ℂ) * ζ ^ 32 - (329 / 25 : ℂ) * ζ ^ 36 +
      (293 / 25 : ℂ) * ζ ^ 40 - (44 / 5 : ℂ) * ζ ^ 44 -
      (57 / 5 : ℂ) * ζ ^ 48 + (452 / 25 : ℂ) * ζ ^ 52)

theorem alternatingSixAmbientRow17_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row17_matrixA *
          alternatingSixFiveAmbient_row17_matrixB *
          alternatingSixFiveAmbient_row17_matrixB).trace =
      alternatingSixCyclotomicValue
        [(1, 0), (-1, 8), (-1, 12), (1, 28)] := by
  change
    (∑ i : Fin 8,
      (alternatingSixFiveAmbient_row17_matrixA *
        alternatingSixFiveAmbient_row17_matrixB *
        alternatingSixFiveAmbient_row17_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row17_matrixA,
    alternatingSixFiveAmbient_row17_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_eight_absquared_cyclotomic
    ((1 : ℂ) - ζ ^ 4 - (67 / 8 : ℂ) * ζ ^ 8 +
      (25 / 4 : ℂ) * ζ ^ 12 + (31 / 8 : ℂ) * ζ ^ 16 +
      (57 / 8 : ℂ) * ζ ^ 20 + (23 / 4 : ℂ) * ζ ^ 24 -
      (25 / 2 : ℂ) * ζ ^ 28 - (111 / 8 : ℂ) * ζ ^ 32 +
      (5 / 8 : ℂ) * ζ ^ 36 - (5 / 2 : ℂ) * ζ ^ 40 +
      (37 / 8 : ℂ) * ζ ^ 44 + 14 * ζ ^ 48 + ζ ^ 52)

theorem alternatingSixAmbientRow18_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row18_matrixA *
          alternatingSixFiveAmbient_row18_matrixB *
          alternatingSixFiveAmbient_row18_matrixB).trace =
      alternatingSixCyclotomicValue
        [(-1, 8), (-1, 12), (1, 28)] := by
  change
    (∑ i : Fin 8,
      (alternatingSixFiveAmbient_row18_matrixA *
        alternatingSixFiveAmbient_row18_matrixB *
        alternatingSixFiveAmbient_row18_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row18_matrixA,
    alternatingSixFiveAmbient_row18_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_eight_absquared_cyclotomic
    (-(131 / 55 : ℂ) + (131 / 55 : ℂ) * ζ ^ 4 -
      (201 / 55 : ℂ) * ζ ^ 8 + (221 / 55 : ℂ) * ζ ^ 12 -
      (1 / 11 : ℂ) * ζ ^ 16 + (42 / 11 : ℂ) * ζ ^ 20 -
      (323 / 55 : ℂ) * ζ ^ 24 + (466 / 55 : ℂ) * ζ ^ 28 -
      (321 / 55 : ℂ) * ζ ^ 32 - (97 / 55 : ℂ) * ζ ^ 36 -
      (9 / 11 : ℂ) * ζ ^ 40 + (237 / 55 : ℂ) * ζ ^ 44 -
      (59 / 11 : ℂ) * ζ ^ 48 + (226 / 55 : ℂ) * ζ ^ 52)

/-! ### Packaged character values already available at rows 16 and 17 -/

theorem alternatingSixAmbientRow16_character_generatorABSquared :
    alternatingSixAmbientRow16CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorABSquared =
      alternatingSixCyclotomicValue
        [(1, 8), (1, 12), (-1, 28)] := by
  letI : Nonempty (Fin (.row16 : AlternatingSixAmbientOrdinaryRow).dimension) :=
    Fin.pos_iff_nonempty.mp (.row16 : AlternatingSixAmbientOrdinaryRow).dimension_pos
  rw [alternatingSixAmbientRow16CharacterRowCertificate_representation,
    alternatingSixAmbientRow16MatrixCertificate
      |>.universalCoverRepresentation_character_generatorABSquared]
  exact alternatingSixAmbientRow16_matrixABSquared_trace

theorem alternatingSixAmbientRow17_character_generatorABSquared :
    alternatingSixAmbientRow17CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorABSquared =
      alternatingSixCyclotomicValue
        [(1, 0), (-1, 8), (-1, 12), (1, 28)] := by
  letI : Nonempty (Fin (.row17 : AlternatingSixAmbientOrdinaryRow).dimension) :=
    Fin.pos_iff_nonempty.mp (.row17 : AlternatingSixAmbientOrdinaryRow).dimension_pos
  rw [alternatingSixAmbientRow17CharacterRowCertificate_representation,
    alternatingSixAmbientRow17MatrixCertificate
      |>.universalCoverRepresentation_character_generatorABSquared]
  exact alternatingSixAmbientRow17_matrixABSquared_trace

end InductiveMcKay
end McKayConjecture
