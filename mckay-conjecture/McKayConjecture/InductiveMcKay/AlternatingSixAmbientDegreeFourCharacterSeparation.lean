/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.Character.CharacterRowSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeFourSixCharacterRows

/-!
# Separating the paired degree-four ambient character rows

Rows `06` and `07` agree on the canonical generator traces and on `AB`.
The fixed positive separator word has exact values `1` and `-2`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local notation "ζ" => alternatingSixComplexCyclotomicRoot
local notation "ω" => ζ ^ 20

local instance degreeFourSeparationRow06CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row06.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance degreeFourSeparationRow07CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row07.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

private theorem alternatingSixDegreeFourComplexRoot_orderSixRelation :
    ζ ^ 40 - ζ ^ 20 + 1 = 0 := by
  have h :=
    congrArg alternatingSixCyclotomicEmbedding
      alternatingSixCyclotomicRoot_orderSixRelation
  simpa only [map_sub, map_add, map_pow, map_one, map_zero,
    alternatingSixCyclotomicEmbedding_root] using h

private theorem alternatingSixDegreeFourComplexRoot_pow_forty :
    ζ ^ 40 = ζ ^ 20 - 1 := by
  linear_combination
    alternatingSixDegreeFourComplexRoot_orderSixRelation

/-! ### Exact separator traces -/

/-- Reduced row-06 matrix for the word `ab`. -/
def alternatingSixAmbientRow06MatrixAB :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![
      ![-ω, 0, 1, -ω],
      ![1 - ω, ω, ω, 1 - ω],
      ![0, -1, -1 + ω, 2 - ω],
      ![1, -1 + ω, -1 + ω, 2 - ω]
    ]

/-- Reduced row-06 matrix for the word `ab²`. -/
def alternatingSixAmbientRow06MatrixABB :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![
      ![ω, -1, -1 + ω, 1],
      ![-1 + ω, 1 - ω, -ω, -1 + 2 * ω],
      ![ω, -1, -ω, ω],
      ![0, 0, -ω, ω]
    ]

/-- Reduced row-06 matrix for the word `ab³`. -/
def alternatingSixAmbientRow06MatrixABBB :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![
      ![0, 0, -ω, -1 + ω],
      ![0, 1 - ω, 1 - ω, -1 + ω],
      ![1 - ω, -1 + ω, ω, 1 - ω],
      ![0, 0, 1, 0]
    ]

private def alternatingSixAmbientRow06SeparatorPrefix :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![
      ![1, -1 + ω, 0, 1 - ω],
      ![-1 + ω, 0, 1 - ω, -1 + ω],
      ![-ω, 0, 0, 1 - ω],
      ![-1, 0, 0, 0]
    ]

/- The public reductions below are reused by the second outer separator. -/

/-- The row-06 generator product is its reduced `ab` matrix. -/
theorem alternatingSixAmbientRow06_matrixAB :
    alternatingSixFiveAmbient_row06_matrixA *
        alternatingSixFiveAmbient_row06_matrixB =
      alternatingSixAmbientRow06MatrixAB := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply] <;>
    simp [alternatingSixFiveAmbient_row06_matrixA,
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixAmbientRow06MatrixAB,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  all_goals try ring_nf
  all_goals
    rw [alternatingSixDegreeFourComplexRoot_pow_forty]
    ring

private theorem alternatingSixAmbientRow06_matrixAB_mul_matrixB :
    alternatingSixAmbientRow06MatrixAB *
        alternatingSixFiveAmbient_row06_matrixB =
      alternatingSixAmbientRow06MatrixABB := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply] <;>
    simp [alternatingSixAmbientRow06MatrixAB,
      alternatingSixAmbientRow06MatrixABB,
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  all_goals try ring_nf
  all_goals
    rw [alternatingSixDegreeFourComplexRoot_pow_forty]
    ring

private theorem alternatingSixAmbientRow06_matrixABB_mul_matrixB :
    alternatingSixAmbientRow06MatrixABB *
        alternatingSixFiveAmbient_row06_matrixB =
      alternatingSixAmbientRow06MatrixABBB := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply] <;>
    simp [alternatingSixAmbientRow06MatrixABB,
      alternatingSixAmbientRow06MatrixABBB,
      alternatingSixFiveAmbient_row06_matrixB,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  all_goals try ring_nf
  all_goals
    rw [alternatingSixDegreeFourComplexRoot_pow_forty]
    ring

private theorem alternatingSixAmbientRow06_matrixAB_mul_matrixABB :
    alternatingSixAmbientRow06MatrixAB *
        alternatingSixAmbientRow06MatrixABB =
      alternatingSixAmbientRow06SeparatorPrefix := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply] <;>
    simp [alternatingSixAmbientRow06MatrixAB,
      alternatingSixAmbientRow06MatrixABB,
      alternatingSixAmbientRow06SeparatorPrefix,
      Fin.sum_univ_succ]
  all_goals try ring_nf
  all_goals
    rw [alternatingSixDegreeFourComplexRoot_pow_forty]
    ring

/-- The row-06 word `ab²` is its reduced matrix. -/
theorem alternatingSixAmbientRow06_matrixABB :
    (alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB) *
        alternatingSixFiveAmbient_row06_matrixB =
      alternatingSixAmbientRow06MatrixABB := by
  rw [alternatingSixAmbientRow06_matrixAB,
    alternatingSixAmbientRow06_matrixAB_mul_matrixB]

/-- The row-06 word `ab³` is its reduced matrix. -/
theorem alternatingSixAmbientRow06_matrixABBB :
    ((alternatingSixFiveAmbient_row06_matrixA *
            alternatingSixFiveAmbient_row06_matrixB) *
          alternatingSixFiveAmbient_row06_matrixB) *
        alternatingSixFiveAmbient_row06_matrixB =
      alternatingSixAmbientRow06MatrixABBB := by
  rw [alternatingSixAmbientRow06_matrixABB,
    alternatingSixAmbientRow06_matrixABB_mul_matrixB]

private theorem alternatingSixAmbientRow06_separator_prefix_mul_abbb_trace :
    (alternatingSixAmbientRow06SeparatorPrefix *
          alternatingSixAmbientRow06MatrixABBB).trace =
      1 := by
  change
    (∑ i : Fin 4,
      (alternatingSixAmbientRow06SeparatorPrefix *
          alternatingSixAmbientRow06MatrixABBB) i i) = 1
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixAmbientRow06SeparatorPrefix,
    alternatingSixAmbientRow06MatrixABBB, Fin.sum_univ_succ]
  ring_nf

theorem alternatingSixAmbientRow06_separator_trace :
    (alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB).trace =
      1 := by
  rw [show
    alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB =
        (alternatingSixFiveAmbient_row06_matrixA *
            alternatingSixFiveAmbient_row06_matrixB) *
          (alternatingSixFiveAmbient_row06_matrixA *
            alternatingSixFiveAmbient_row06_matrixB *
            alternatingSixFiveAmbient_row06_matrixB) *
          (alternatingSixFiveAmbient_row06_matrixA *
            alternatingSixFiveAmbient_row06_matrixB *
            alternatingSixFiveAmbient_row06_matrixB *
            alternatingSixFiveAmbient_row06_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow06_matrixABBB,
    alternatingSixAmbientRow06_matrixABB,
    alternatingSixAmbientRow06_matrixAB,
    alternatingSixAmbientRow06_matrixAB_mul_matrixABB]
  exact alternatingSixAmbientRow06_separator_prefix_mul_abbb_trace

/- The following reduced matrices are also reused by the outer action. -/

/-- Reduced row-07 matrix for the word `ab`. -/
def alternatingSixAmbientRow07MatrixAB :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![
      ![(-1 / 3 : ℂ) + (-1 / 3 : ℂ) * ω,
        (-2 / 3 : ℂ) + (1 / 3 : ℂ) * ω,
        -1 + ω,
        (1 / 3 : ℂ) + (1 / 3 : ℂ) * ω],
      ![1, 0, 1, -ω],
      ![ω, 0, 1, 0],
      ![(2 / 3 : ℂ) + (-1 / 3 : ℂ) * ω,
        (1 / 3 : ℂ) + (1 / 3 : ℂ) * ω,
        0,
        (1 / 3 : ℂ) + (1 / 3 : ℂ) * ω]
    ]

/-- Reduced row-07 matrix for the word `ab²`. -/
def alternatingSixAmbientRow07MatrixABB :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![
      ![ω, 0, 1, 0],
      ![(-1 / 3 : ℂ) + (2 / 3 : ℂ) * ω,
        (1 / 3 : ℂ) + (-2 / 3 : ℂ) * ω,
        0,
        (1 / 3 : ℂ) + (-2 / 3 : ℂ) * ω],
      ![(2 / 3 : ℂ) + (-4 / 3 : ℂ) * ω,
        (1 / 3 : ℂ) + (-2 / 3 : ℂ) * ω,
        -ω,
        (-2 / 3 : ℂ) + (1 / 3 : ℂ) * ω],
      ![(-2 / 3 : ℂ) + (1 / 3 : ℂ) * ω,
        (-1 / 3 : ℂ) + (-1 / 3 : ℂ) * ω,
        -1 + ω,
        (2 / 3 : ℂ) + (2 / 3 : ℂ) * ω]
    ]

/-- Reduced row-07 matrix for the word `ab³`. -/
def alternatingSixAmbientRow07MatrixABBB :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![
      ![(2 / 3 : ℂ) + (-4 / 3 : ℂ) * ω,
        (1 / 3 : ℂ) + (-2 / 3 : ℂ) * ω,
        -ω,
        (-2 / 3 : ℂ) + (1 / 3 : ℂ) * ω],
      ![(-1 / 3 : ℂ) + (-1 / 3 : ℂ) * ω,
        (1 / 3 : ℂ) + (1 / 3 : ℂ) * ω,
        0,
        (1 / 3 : ℂ) + (-2 / 3 : ℂ) * ω],
      ![(-1 / 3 : ℂ) + (2 / 3 : ℂ) * ω,
        (-2 / 3 : ℂ) + (1 / 3 : ℂ) * ω,
        ω,
        (1 / 3 : ℂ) + (-2 / 3 : ℂ) * ω],
      ![0, 0, 1, 0]
    ]

private def alternatingSixAmbientRow07SeparatorPrefix :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![
      ![(2 / 3 : ℂ) + (-1 / 3 : ℂ) * ω,
        (1 / 3 : ℂ) + (1 / 3 : ℂ) * ω,
        0,
        (1 / 3 : ℂ) + (1 / 3 : ℂ) * ω],
      ![1, 0, 2 - ω, -ω],
      ![(-1 / 3 : ℂ) + (-1 / 3 : ℂ) * ω,
        (1 / 3 : ℂ) + (-2 / 3 : ℂ) * ω,
        0,
        (-2 / 3 : ℂ) + (1 / 3 : ℂ) * ω],
      ![(-1 / 3 : ℂ) + (2 / 3 : ℂ) * ω,
        (1 / 3 : ℂ) + (-2 / 3 : ℂ) * ω,
        0,
        (1 / 3 : ℂ) + (1 / 3 : ℂ) * ω]
    ]

/-- The row-07 generator product is its reduced `ab` matrix. -/
theorem alternatingSixAmbientRow07_matrixAB :
    alternatingSixFiveAmbient_row07_matrixA *
        alternatingSixFiveAmbient_row07_matrixB =
      alternatingSixAmbientRow07MatrixAB := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply] <;>
    simp [alternatingSixFiveAmbient_row07_matrixA,
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixAmbientRow07MatrixAB,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  all_goals try ring_nf
  all_goals
    rw [alternatingSixDegreeFourComplexRoot_pow_forty]
    ring

private theorem alternatingSixAmbientRow07_matrixAB_mul_matrixB :
    alternatingSixAmbientRow07MatrixAB *
        alternatingSixFiveAmbient_row07_matrixB =
      alternatingSixAmbientRow07MatrixABB := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply] <;>
    simp [alternatingSixAmbientRow07MatrixAB,
      alternatingSixAmbientRow07MatrixABB,
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  all_goals try ring_nf
  all_goals
    rw [alternatingSixDegreeFourComplexRoot_pow_forty]
    ring

private theorem alternatingSixAmbientRow07_matrixABB_mul_matrixB :
    alternatingSixAmbientRow07MatrixABB *
        alternatingSixFiveAmbient_row07_matrixB =
      alternatingSixAmbientRow07MatrixABBB := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply] <;>
    simp [alternatingSixAmbientRow07MatrixABB,
      alternatingSixAmbientRow07MatrixABBB,
      alternatingSixFiveAmbient_row07_matrixB,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  all_goals try ring_nf
  all_goals
    rw [alternatingSixDegreeFourComplexRoot_pow_forty]
    ring

private theorem alternatingSixAmbientRow07_matrixAB_mul_matrixABB :
    alternatingSixAmbientRow07MatrixAB *
        alternatingSixAmbientRow07MatrixABB =
      alternatingSixAmbientRow07SeparatorPrefix := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply] <;>
    simp [alternatingSixAmbientRow07MatrixAB,
      alternatingSixAmbientRow07MatrixABB,
      alternatingSixAmbientRow07SeparatorPrefix,
      Fin.sum_univ_succ]
  all_goals try ring_nf
  all_goals
    rw [alternatingSixDegreeFourComplexRoot_pow_forty]
    ring

/-- The row-07 word `ab²` is its reduced matrix. -/
theorem alternatingSixAmbientRow07_matrixABB :
    (alternatingSixFiveAmbient_row07_matrixA *
          alternatingSixFiveAmbient_row07_matrixB) *
        alternatingSixFiveAmbient_row07_matrixB =
      alternatingSixAmbientRow07MatrixABB := by
  rw [alternatingSixAmbientRow07_matrixAB,
    alternatingSixAmbientRow07_matrixAB_mul_matrixB]

/-- The row-07 word `ab³` is its reduced matrix. -/
theorem alternatingSixAmbientRow07_matrixABBB :
    ((alternatingSixFiveAmbient_row07_matrixA *
            alternatingSixFiveAmbient_row07_matrixB) *
          alternatingSixFiveAmbient_row07_matrixB) *
        alternatingSixFiveAmbient_row07_matrixB =
      alternatingSixAmbientRow07MatrixABBB := by
  rw [alternatingSixAmbientRow07_matrixABB,
    alternatingSixAmbientRow07_matrixABB_mul_matrixB]

private theorem alternatingSixAmbientRow07_separator_prefix_mul_abbb_trace :
    (alternatingSixAmbientRow07SeparatorPrefix *
          alternatingSixAmbientRow07MatrixABBB).trace =
      -2 := by
  change
    (∑ i : Fin 4,
      (alternatingSixAmbientRow07SeparatorPrefix *
          alternatingSixAmbientRow07MatrixABBB) i i) = -2
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixAmbientRow07SeparatorPrefix,
    alternatingSixAmbientRow07MatrixABBB, Fin.sum_univ_succ]
  ring_nf
  rw [alternatingSixDegreeFourComplexRoot_pow_forty]
  ring

theorem alternatingSixAmbientRow07_separator_trace :
    (alternatingSixFiveAmbient_row07_matrixA *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixA *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixA *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixB).trace =
      -2 := by
  rw [show
    alternatingSixFiveAmbient_row07_matrixA *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixA *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixA *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixB =
        (alternatingSixFiveAmbient_row07_matrixA *
            alternatingSixFiveAmbient_row07_matrixB) *
          (alternatingSixFiveAmbient_row07_matrixA *
            alternatingSixFiveAmbient_row07_matrixB *
            alternatingSixFiveAmbient_row07_matrixB) *
          (alternatingSixFiveAmbient_row07_matrixA *
            alternatingSixFiveAmbient_row07_matrixB *
            alternatingSixFiveAmbient_row07_matrixB *
            alternatingSixFiveAmbient_row07_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow07_matrixABBB,
    alternatingSixAmbientRow07_matrixABB,
    alternatingSixAmbientRow07_matrixAB,
    alternatingSixAmbientRow07_matrixAB_mul_matrixABB]
  exact alternatingSixAmbientRow07_separator_prefix_mul_abbb_trace

/-! ### Certified character values and separation -/

theorem alternatingSixAmbientRow06_character_separator :
    alternatingSixAmbientRow06CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSeparator =
      1 := by
  rw [alternatingSixAmbientRow06CharacterRowCertificate_representation,
    alternatingSixAmbientRow06MatrixCertificate.universalCoverRepresentation_character_separator]
  exact alternatingSixAmbientRow06_separator_trace

theorem alternatingSixAmbientRow07_character_separator :
    alternatingSixAmbientRow07CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSeparator =
      -2 := by
  rw [alternatingSixAmbientRow07CharacterRowCertificate_representation,
    alternatingSixAmbientRow07MatrixCertificate.universalCoverRepresentation_character_separator]
  exact alternatingSixAmbientRow07_separator_trace

/-- The paired degree-four rows are distinct irreducible characters. -/
theorem alternatingSixAmbientRow06_character_ne_row07_character :
    alternatingSixAmbientRow06CharacterRowCertificate.irreducibleCharacter ≠
      alternatingSixAmbientRow07CharacterRowCertificate.irreducibleCharacter := by
  apply
    CharacterRowCertificate.irreducibleCharacter_ne_of_character_apply_ne
      alternatingSixAmbientRow06CharacterRowCertificate
      alternatingSixAmbientRow07CharacterRowCertificate
      alternatingSixAmbientCanonicalSeparator
  rw [alternatingSixAmbientRow06_character_separator,
    alternatingSixAmbientRow07_character_separator]
  norm_num

end InductiveMcKay
end McKayConjecture
