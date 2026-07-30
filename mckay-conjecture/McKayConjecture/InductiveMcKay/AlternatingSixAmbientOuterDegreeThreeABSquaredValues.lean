/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeThreeCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterABSquaredEvaluation

/-!
# Degree-three values needed for the ambient outer action

The first canonical outer automorphism exchanges the `AB` and `AB²`
conjugacy-class families.  This file computes the four required `AB²`
matrix traces directly from the certified generator matrices.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

macro "close_degree_three_absquared_cyclotomic" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

theorem alternatingSixAmbientRow02_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row02_matrixA *
          alternatingSixFiveAmbient_row02_matrixB *
          alternatingSixFiveAmbient_row02_matrixB).trace =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 16), (1, 20)] := by
  change
    (∑ i : Fin 3,
      (alternatingSixFiveAmbient_row02_matrixA *
        alternatingSixFiveAmbient_row02_matrixB *
        alternatingSixFiveAmbient_row02_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row02_matrixA,
    alternatingSixFiveAmbient_row02_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_three_absquared_cyclotomic
    ((3 / 2 : ℂ) + (1 / 2 : ℂ) * ζ ^ 4 +
      (3 / 2 : ℂ) * ζ ^ 8 + 3 * ζ ^ 12 -
      2 * ζ ^ 16 - (5 / 2 : ℂ) * ζ ^ 20 - ζ ^ 24 -
      (5 / 2 : ℂ) * ζ ^ 28 + (1 / 2 : ℂ) * ζ ^ 32 +
      (3 / 2 : ℂ) * ζ ^ 36 + ζ ^ 40 -
      (1 / 2 : ℂ) * ζ ^ 44 + (1 / 2 : ℂ) * ζ ^ 48 -
      (1 / 2 : ℂ) * ζ ^ 52)

theorem alternatingSixAmbientRow03_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row03_matrixA *
          alternatingSixFiveAmbient_row03_matrixB *
          alternatingSixFiveAmbient_row03_matrixB).trace =
      alternatingSixCyclotomicValue [(1, 4), (-1, 16)] := by
  change
    (∑ i : Fin 3,
      (alternatingSixFiveAmbient_row03_matrixA *
        alternatingSixFiveAmbient_row03_matrixB *
        alternatingSixFiveAmbient_row03_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row03_matrixA,
    alternatingSixFiveAmbient_row03_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_three_absquared_cyclotomic
    ((1 : ℂ) + ζ ^ 4 - (11 / 4 : ℂ) * ζ ^ 8 -
      (3 / 4 : ℂ) * ζ ^ 12 - ζ ^ 16 +
      (1 / 4 : ℂ) * ζ ^ 20 + (7 / 4 : ℂ) * ζ ^ 24 +
      2 * ζ ^ 28 + (1 / 2 : ℂ) * ζ ^ 32 -
      (5 / 4 : ℂ) * ζ ^ 36 - (3 / 4 : ℂ) * ζ ^ 44 -
      (1 / 2 : ℂ) * ζ ^ 48 + (1 / 2 : ℂ) * ζ ^ 52)

theorem alternatingSixAmbientRow04_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row04_matrixA *
          alternatingSixFiveAmbient_row04_matrixB *
          alternatingSixFiveAmbient_row04_matrixB).trace =
      alternatingSixCyclotomicValue
        [(1, 0), (1, 4), (-1, 8), (-1, 12),
          (-1, 16), (-1, 20), (1, 28)] := by
  change
    (∑ i : Fin 3,
      (alternatingSixFiveAmbient_row04_matrixA *
        alternatingSixFiveAmbient_row04_matrixB *
        alternatingSixFiveAmbient_row04_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row04_matrixA,
    alternatingSixFiveAmbient_row04_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_three_absquared_cyclotomic
    (-(1 : ℂ) + (5 / 2 : ℂ) * ζ ^ 8 -
      (5 / 2 : ℂ) * ζ ^ 12 + (7 / 4 : ℂ) * ζ ^ 16 -
      (3 / 4 : ℂ) * ζ ^ 20 - (1 / 2 : ℂ) * ζ ^ 24 +
      (3 / 4 : ℂ) * ζ ^ 28 + 2 * ζ ^ 32 -
      (1 / 2 : ℂ) * ζ ^ 36 - (1 / 4 : ℂ) * ζ ^ 48 +
      (1 / 4 : ℂ) * ζ ^ 52)

theorem alternatingSixAmbientRow05_matrixABSquared_trace :
    (alternatingSixFiveAmbient_row05_matrixA *
          alternatingSixFiveAmbient_row05_matrixB *
          alternatingSixFiveAmbient_row05_matrixB).trace =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 8), (1, 12),
          (1, 16), (-1, 28)] := by
  change
    (∑ i : Fin 3,
      (alternatingSixFiveAmbient_row05_matrixA *
        alternatingSixFiveAmbient_row05_matrixB *
        alternatingSixFiveAmbient_row05_matrixB) i i) = _
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_row05_matrixA,
    alternatingSixFiveAmbient_row05_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_degree_three_absquared_cyclotomic
    ((1 : ℂ) + 2 * ζ ^ 4 - ζ ^ 8 - 3 * ζ ^ 16 -
      ζ ^ 20 + 2 * ζ ^ 28 + 2 * ζ ^ 32 -
      ζ ^ 36 + ζ ^ 40 - ζ ^ 44)

/-! ### Packaged character values -/

theorem alternatingSixAmbientRow02_character_generatorABSquared :
    alternatingSixAmbientRow02CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorABSquared =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 16), (1, 20)] := by
  letI : Nonempty (Fin (.row02 : AlternatingSixAmbientOrdinaryRow).dimension) :=
    Fin.pos_iff_nonempty.mp (.row02 : AlternatingSixAmbientOrdinaryRow).dimension_pos
  rw [alternatingSixAmbientRow02CharacterRowCertificate_representation,
    alternatingSixAmbientRow02MatrixCertificate
      |>.universalCoverRepresentation_character_generatorABSquared]
  exact alternatingSixAmbientRow02_matrixABSquared_trace

theorem alternatingSixAmbientRow03_character_generatorABSquared :
    alternatingSixAmbientRow03CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorABSquared =
      alternatingSixCyclotomicValue [(1, 4), (-1, 16)] := by
  letI : Nonempty (Fin (.row03 : AlternatingSixAmbientOrdinaryRow).dimension) :=
    Fin.pos_iff_nonempty.mp (.row03 : AlternatingSixAmbientOrdinaryRow).dimension_pos
  rw [alternatingSixAmbientRow03CharacterRowCertificate_representation,
    alternatingSixAmbientRow03MatrixCertificate
      |>.universalCoverRepresentation_character_generatorABSquared]
  exact alternatingSixAmbientRow03_matrixABSquared_trace

theorem alternatingSixAmbientRow04_character_generatorABSquared :
    alternatingSixAmbientRow04CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorABSquared =
      alternatingSixCyclotomicValue
        [(1, 0), (1, 4), (-1, 8), (-1, 12),
          (-1, 16), (-1, 20), (1, 28)] := by
  letI : Nonempty (Fin (.row04 : AlternatingSixAmbientOrdinaryRow).dimension) :=
    Fin.pos_iff_nonempty.mp (.row04 : AlternatingSixAmbientOrdinaryRow).dimension_pos
  rw [alternatingSixAmbientRow04CharacterRowCertificate_representation,
    alternatingSixAmbientRow04MatrixCertificate
      |>.universalCoverRepresentation_character_generatorABSquared]
  exact alternatingSixAmbientRow04_matrixABSquared_trace

theorem alternatingSixAmbientRow05_character_generatorABSquared :
    alternatingSixAmbientRow05CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalGeneratorABSquared =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 8), (1, 12),
          (1, 16), (-1, 28)] := by
  letI : Nonempty (Fin (.row05 : AlternatingSixAmbientOrdinaryRow).dimension) :=
    Fin.pos_iff_nonempty.mp (.row05 : AlternatingSixAmbientOrdinaryRow).dimension_pos
  rw [alternatingSixAmbientRow05CharacterRowCertificate_representation,
    alternatingSixAmbientRow05MatrixCertificate
      |>.universalCoverRepresentation_character_generatorABSquared]
  exact alternatingSixAmbientRow05_matrixABSquared_trace

end InductiveMcKay
end McKayConjecture
