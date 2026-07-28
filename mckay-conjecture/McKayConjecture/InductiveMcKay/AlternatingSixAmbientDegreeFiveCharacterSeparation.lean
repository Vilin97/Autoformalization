/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.Character.CharacterRowSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRelationTableDegreeFiveTenFifteen
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow08DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow09DiagonalCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientTwoGeneratorCharacterRow

/-!
# Separating the paired degree-five ambient character rows

Ordinary rows 08 and 09 have equal dimension and the same trivial central
scalar.  The canonical positive separator word has exact character values
`2` and `-1`, respectively.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local notation "ζ" => alternatingSixComplexCyclotomicRoot
local notation "ω" => ζ ^ 20

local instance degreeFiveSeparationRow08CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row08.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

local instance degreeFiveSeparationRow09CoordinateNonempty :
    Nonempty (Fin AlternatingSixAmbientOrdinaryRow.row09.dimension) :=
  ⟨⟨0, by simp [AlternatingSixAmbientOrdinaryRow.dimension]⟩⟩

/-- Normalized irreducible-character certificate for ordinary row 08. -/
def alternatingSixAmbientRow08CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow08MatrixCertificate
    |>.characterRowCertificateOfScalarCommutant
      alternatingSixAmbientRow08_scalar_commutant

/-- Normalized irreducible-character certificate for ordinary row 09. -/
def alternatingSixAmbientRow09CharacterRowCertificate :
    CharacterRowCertificate AlternatingSixUniversalCover :=
  alternatingSixAmbientRow09MatrixCertificate
    |>.characterRowCertificateOfScalarCommutant
      alternatingSixAmbientRow09_scalar_commutant

@[simp]
theorem alternatingSixAmbientRow08CharacterRowCertificate_representation :
    alternatingSixAmbientRow08CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow08MatrixCertificate.universalCoverRepresentation :=
  rfl

@[simp]
theorem alternatingSixAmbientRow09CharacterRowCertificate_representation :
    alternatingSixAmbientRow09CharacterRowCertificate.representation =
      FDRep.of
        alternatingSixAmbientRow09MatrixCertificate.universalCoverRepresentation :=
  rfl

/-! ### Exact separator traces -/

theorem alternatingSixAmbientRow08_separator_trace :
    (alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB).trace =
      2 := by
  change
    (∑ i : Fin 5,
      (alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB) i i) = 2
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row08_matrixA,
    alternatingSixFiveAmbient_row08_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

private theorem alternatingSixComplexCyclotomicRoot_orderSixRelation :
    ζ ^ 40 - ζ ^ 20 + 1 = 0 := by
  have h :=
    congrArg alternatingSixCyclotomicEmbedding
      alternatingSixCyclotomicRoot_orderSixRelation
  simpa only [map_sub, map_add, map_pow, map_one, map_zero,
    alternatingSixCyclotomicEmbedding_root] using h

private theorem alternatingSixComplexCyclotomicRoot_pow_forty :
    ζ ^ 40 = ζ ^ 20 - 1 := by
  linear_combination
    alternatingSixComplexCyclotomicRoot_orderSixRelation

private def alternatingSixAmbientRow09MatrixAB :
    Matrix (Fin 5) (Fin 5) ℂ :=
  ![
      ![alternatingSixCyclotomicValue [(-1, 0), (1, 20)],
        alternatingSixCyclotomicValue [(1, 0)],
        alternatingSixCyclotomicValue [(1, 20)],
        alternatingSixCyclotomicValue [],
        alternatingSixCyclotomicValue [(1, 20)]],
      ![alternatingSixCyclotomicValue [(1, 0)],
        alternatingSixCyclotomicValue [(1, 20)],
        alternatingSixCyclotomicValue [],
        alternatingSixCyclotomicValue [(-1, 0)],
        alternatingSixCyclotomicValue [(-1, 0)]],
      ![alternatingSixCyclotomicValue [(2, 0), (-1, 20)],
        alternatingSixCyclotomicValue [],
        alternatingSixCyclotomicValue [(1, 0), (-2, 20)],
        alternatingSixCyclotomicValue [(-1, 0), (1, 20)],
        alternatingSixCyclotomicValue []],
      ![alternatingSixCyclotomicValue [(1, 0), (-1, 20)],
        alternatingSixCyclotomicValue [(1, 0), (1, 20)],
        alternatingSixCyclotomicValue [(-1, 0)],
        alternatingSixCyclotomicValue [(-1, 0), (1, 20)],
        alternatingSixCyclotomicValue [(-1, 0), (2, 20)]],
      ![alternatingSixCyclotomicValue [(-2, 0), (1, 20)],
        alternatingSixCyclotomicValue [(-1, 0)],
        alternatingSixCyclotomicValue [(-1, 0), (1, 20)],
        alternatingSixCyclotomicValue [(2, 0), (-1, 20)],
        alternatingSixCyclotomicValue [(1, 0), (-1, 20)]]
    ]

private theorem alternatingSixAmbientRow09_matrixAB :
    alternatingSixFiveAmbient_row09_matrixA *
      alternatingSixFiveAmbient_row09_matrixB =
      alternatingSixAmbientRow09MatrixAB := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [alternatingSixFiveAmbient_row09_matrixA,
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixAmbientRow09MatrixAB,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  all_goals
    first
    | linear_combination
        alternatingSixComplexCyclotomicRoot_orderSixRelation
    | linear_combination
        (-1 : ℂ) *
          alternatingSixComplexCyclotomicRoot_orderSixRelation
    | linear_combination
        (2 : ℂ) *
          alternatingSixComplexCyclotomicRoot_orderSixRelation
    | linear_combination
        (-2 : ℂ) *
          alternatingSixComplexCyclotomicRoot_orderSixRelation
    | ring

private def alternatingSixAmbientRow09MatrixABB :
    Matrix (Fin 5) (Fin 5) ℂ :=
  ![
      ![-1, -ω, -1 + ω, 1, 1 - ω],
      ![-2 * ω, 1, -2, ω, -1 + 2 * ω],
      ![ω, -2 + ω, 1 - ω, -ω, -1 - ω],
      ![-ω, -1, -1 - ω, ω, -1],
      ![2, ω, 1 - ω, -1, -1]
    ]

private def alternatingSixAmbientRow09MatrixABBB :
    Matrix (Fin 5) (Fin 5) ℂ :=
  ![
      ![0, 1 + ω, -1 + ω, 0, -1 + 2 * ω],
      ![0, 0, 0, -1 + ω, 0],
      ![1, 1 - ω, 2 - ω, -1, 1 - ω],
      ![ω, 1, 1, -1, 0],
      ![-ω, 0, -1, 0, -1 + ω]
    ]

private def alternatingSixAmbientRow09SeparatorPrefix :
    Matrix (Fin 5) (Fin 5) ℂ :=
  ![
      ![0, 0, -ω, 0, 0],
      ![-1 - ω, 1 - ω, -1 + ω, 1, 1],
      ![1, ω, 0, -1, -1],
      ![0, 1, 0, 0, 0],
      ![2 - 2 * ω, 0, -2 * ω, -1 + 2 * ω, -1 + ω]
    ]

private theorem alternatingSixAmbientRow09_matrixAB_mul_matrixB :
    alternatingSixAmbientRow09MatrixAB *
        alternatingSixFiveAmbient_row09_matrixB =
      alternatingSixAmbientRow09MatrixABB := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply] <;>
    simp [alternatingSixAmbientRow09MatrixAB,
      alternatingSixAmbientRow09MatrixABB,
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  all_goals try ring_nf
  all_goals
    rw [alternatingSixComplexCyclotomicRoot_pow_forty]
    ring

private theorem alternatingSixAmbientRow09_matrixABB_mul_matrixB :
    alternatingSixAmbientRow09MatrixABB *
        alternatingSixFiveAmbient_row09_matrixB =
      alternatingSixAmbientRow09MatrixABBB := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply] <;>
    simp [alternatingSixAmbientRow09MatrixABB,
      alternatingSixAmbientRow09MatrixABBB,
      alternatingSixFiveAmbient_row09_matrixB,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  all_goals try ring_nf
  all_goals
    rw [alternatingSixComplexCyclotomicRoot_pow_forty]
    ring

private theorem alternatingSixAmbientRow09_matrixAB_mul_matrixABB :
    alternatingSixAmbientRow09MatrixAB *
        alternatingSixAmbientRow09MatrixABB =
      alternatingSixAmbientRow09SeparatorPrefix := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply] <;>
    simp [alternatingSixAmbientRow09MatrixAB,
      alternatingSixAmbientRow09MatrixABB,
      alternatingSixAmbientRow09SeparatorPrefix,
      alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  all_goals try ring_nf
  all_goals
    rw [alternatingSixComplexCyclotomicRoot_pow_forty]
    ring

private theorem alternatingSixAmbientRow09_matrixABB :
    (alternatingSixFiveAmbient_row09_matrixA *
          alternatingSixFiveAmbient_row09_matrixB) *
        alternatingSixFiveAmbient_row09_matrixB =
      alternatingSixAmbientRow09MatrixABB := by
  rw [alternatingSixAmbientRow09_matrixAB,
    alternatingSixAmbientRow09_matrixAB_mul_matrixB]

private theorem alternatingSixAmbientRow09_matrixABBB :
    ((alternatingSixFiveAmbient_row09_matrixA *
            alternatingSixFiveAmbient_row09_matrixB) *
          alternatingSixFiveAmbient_row09_matrixB) *
        alternatingSixFiveAmbient_row09_matrixB =
      alternatingSixAmbientRow09MatrixABBB := by
  rw [alternatingSixAmbientRow09_matrixABB,
    alternatingSixAmbientRow09_matrixABB_mul_matrixB]

private theorem alternatingSixAmbientRow09_separator_prefix_mul_abbb_trace :
    (alternatingSixAmbientRow09SeparatorPrefix *
          alternatingSixAmbientRow09MatrixABBB).trace =
      -1 := by
  change
    (∑ i : Fin 5,
      (alternatingSixAmbientRow09SeparatorPrefix *
          alternatingSixAmbientRow09MatrixABBB) i i) = -1
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixAmbientRow09SeparatorPrefix,
    alternatingSixAmbientRow09MatrixABBB, Fin.sum_univ_succ]
  ring_nf
  rw [alternatingSixComplexCyclotomicRoot_pow_forty]
  ring

theorem alternatingSixAmbientRow09_separator_trace :
    (alternatingSixFiveAmbient_row09_matrixA *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixA *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixA *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixB).trace =
      -1 := by
  rw [show
    alternatingSixFiveAmbient_row09_matrixA *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixA *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixA *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixB =
        (alternatingSixFiveAmbient_row09_matrixA *
            alternatingSixFiveAmbient_row09_matrixB) *
          (alternatingSixFiveAmbient_row09_matrixA *
            alternatingSixFiveAmbient_row09_matrixB *
            alternatingSixFiveAmbient_row09_matrixB) *
          (alternatingSixFiveAmbient_row09_matrixA *
            alternatingSixFiveAmbient_row09_matrixB *
            alternatingSixFiveAmbient_row09_matrixB *
            alternatingSixFiveAmbient_row09_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow09_matrixABBB,
    alternatingSixAmbientRow09_matrixABB,
    alternatingSixAmbientRow09_matrixAB,
    alternatingSixAmbientRow09_matrixAB_mul_matrixABB]
  exact alternatingSixAmbientRow09_separator_prefix_mul_abbb_trace

theorem alternatingSixAmbientRow08_character_separator :
    alternatingSixAmbientRow08CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSeparator =
      2 := by
  rw [alternatingSixAmbientRow08CharacterRowCertificate_representation,
    alternatingSixAmbientRow08MatrixCertificate.universalCoverRepresentation_character_separator]
  exact alternatingSixAmbientRow08_separator_trace

theorem alternatingSixAmbientRow09_character_separator :
    alternatingSixAmbientRow09CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSeparator =
      -1 := by
  rw [alternatingSixAmbientRow09CharacterRowCertificate_representation,
    alternatingSixAmbientRow09MatrixCertificate.universalCoverRepresentation_character_separator]
  exact alternatingSixAmbientRow09_separator_trace

/-- The two degree-five rows are distinct irreducible characters. -/
theorem alternatingSixAmbientRow08_character_ne_row09_character :
    alternatingSixAmbientRow08CharacterRowCertificate.irreducibleCharacter ≠
      alternatingSixAmbientRow09CharacterRowCertificate.irreducibleCharacter := by
  apply
    CharacterRowCertificate.irreducibleCharacter_ne_of_character_apply_ne
      alternatingSixAmbientRow08CharacterRowCertificate
      alternatingSixAmbientRow09CharacterRowCertificate
      alternatingSixAmbientCanonicalSeparator
  rw [alternatingSixAmbientRow08_character_separator,
    alternatingSixAmbientRow09_character_separator]
  norm_num

end InductiveMcKay
end McKayConjecture
