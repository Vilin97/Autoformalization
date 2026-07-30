/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeFourCharacterSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientDegreeFiveCharacterSeparation

/-!
# The second outer separator for the sixfold cover of `A₆`

The second audited outer automorphism interchanges the two long base classes.
The existing ordinary-table separation uses the positive state-77 word.  This
file evaluates the positive state-79 word needed on its inverse image.  The
proof reuses the reduced `ab`, `ab²`, and `ab³` matrices from the ordinary
separation modules.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local notation "ζ" => alternatingSixComplexCyclotomicRoot
local notation "ω" => ζ ^ 20

/-- The positive state-79 word `a b a b³ a b²`. -/
def alternatingSixAmbientCanonicalSecondSeparator :
    AlternatingSixUniversalCover :=
  alternatingSixAmbientCanonicalGeneratorA *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorA *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorA *
    alternatingSixAmbientCanonicalGeneratorB *
    alternatingSixAmbientCanonicalGeneratorB

namespace AlternatingSixSchurMatrixRowCertificate

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
variable (C : AlternatingSixSchurMatrixRowCertificate n)

/-- The second separator acts by the corresponding positive matrix word. -/
theorem universalCoverRepresentation_secondSeparator :
    C.universalCoverRepresentation
        alternatingSixAmbientCanonicalSecondSeparator =
      Matrix.toLin'
        (C.matrixA * C.matrixB * C.matrixA *
          C.matrixB * C.matrixB * C.matrixB *
          C.matrixA * C.matrixB * C.matrixB) := by
  simp only [alternatingSixAmbientCanonicalSecondSeparator,
    map_mul, C.universalCoverRepresentation_generatorA,
    C.universalCoverRepresentation_generatorB,
    Module.End.mul_eq_comp, Matrix.toLin'_mul]

/-- Character value at the second separator as an exact matrix trace. -/
theorem universalCoverRepresentation_character_secondSeparator :
    (FDRep.of C.universalCoverRepresentation).character
        alternatingSixAmbientCanonicalSecondSeparator =
      (C.matrixA * C.matrixB * C.matrixA *
        C.matrixB * C.matrixB * C.matrixB *
        C.matrixA * C.matrixB * C.matrixB).trace :=
  C.universalCoverRepresentation_character_eq_trace_of_action_eq
    alternatingSixAmbientCanonicalSecondSeparator
    (C.matrixA * C.matrixB * C.matrixA *
      C.matrixB * C.matrixB * C.matrixB *
      C.matrixA * C.matrixB * C.matrixB)
    C.universalCoverRepresentation_secondSeparator

end AlternatingSixSchurMatrixRowCertificate

private theorem alternatingSixOuterSecondSeparator_orderSixRelation :
    ζ ^ 40 = ζ ^ 20 - 1 := by
  have h :=
    congrArg alternatingSixCyclotomicEmbedding
      alternatingSixCyclotomicRoot_orderSixRelation
  have hcomplex :
      ζ ^ 40 - ζ ^ 20 + 1 = 0 := by
    simpa only [map_sub, map_add, map_pow, map_one, map_zero,
      alternatingSixCyclotomicEmbedding_root] using h
  linear_combination hcomplex

private theorem alternatingSixOuterSecondSeparator_root_pow_sixty :
    ζ ^ 60 = -1 := by
  calc
    ζ ^ 60 = ζ ^ 40 * ζ ^ 20 := by
      rw [← pow_add]
    _ = (ζ ^ 20 - 1) * ζ ^ 20 := by
      rw [alternatingSixOuterSecondSeparator_orderSixRelation]
    _ = -1 := by
      rw [sub_mul, one_mul, ← pow_add,
        alternatingSixOuterSecondSeparator_orderSixRelation]
      ring

/-! ### Degree-four values -/

private theorem alternatingSixAmbientRow06_secondSeparator_reduced_trace :
    (alternatingSixAmbientRow06MatrixAB *
          alternatingSixAmbientRow06MatrixABBB *
        alternatingSixAmbientRow06MatrixABB).trace =
      -2 := by
  change
    (∑ i : Fin 4,
      (alternatingSixAmbientRow06MatrixAB *
          alternatingSixAmbientRow06MatrixABBB *
        alternatingSixAmbientRow06MatrixABB) i i) = -2
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixAmbientRow06MatrixAB,
    alternatingSixAmbientRow06MatrixABB,
    alternatingSixAmbientRow06MatrixABBB, Fin.sum_univ_succ]
  ring_nf
  rw [alternatingSixOuterSecondSeparator_orderSixRelation,
    alternatingSixOuterSecondSeparator_root_pow_sixty]
  ring

/-- The row-06 value at the positive state-79 word. -/
theorem alternatingSixAmbientRow06_secondSeparator_trace :
    (alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB).trace =
      -2 := by
  rw [show
    alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixA *
          alternatingSixFiveAmbient_row06_matrixB *
          alternatingSixFiveAmbient_row06_matrixB =
        (alternatingSixFiveAmbient_row06_matrixA *
            alternatingSixFiveAmbient_row06_matrixB) *
          (alternatingSixFiveAmbient_row06_matrixA *
            alternatingSixFiveAmbient_row06_matrixB *
            alternatingSixFiveAmbient_row06_matrixB *
            alternatingSixFiveAmbient_row06_matrixB) *
          (alternatingSixFiveAmbient_row06_matrixA *
            alternatingSixFiveAmbient_row06_matrixB *
            alternatingSixFiveAmbient_row06_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow06_matrixABBB,
    alternatingSixAmbientRow06_matrixABB,
    alternatingSixAmbientRow06_matrixAB]
  exact alternatingSixAmbientRow06_secondSeparator_reduced_trace

private theorem alternatingSixAmbientRow07_secondSeparator_reduced_trace :
    (alternatingSixAmbientRow07MatrixAB *
          alternatingSixAmbientRow07MatrixABBB *
        alternatingSixAmbientRow07MatrixABB).trace =
      1 := by
  change
    (∑ i : Fin 4,
      (alternatingSixAmbientRow07MatrixAB *
          alternatingSixAmbientRow07MatrixABBB *
        alternatingSixAmbientRow07MatrixABB) i i) = 1
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixAmbientRow07MatrixAB,
    alternatingSixAmbientRow07MatrixABB,
    alternatingSixAmbientRow07MatrixABBB, Fin.sum_univ_succ]
  ring_nf
  rw [alternatingSixOuterSecondSeparator_orderSixRelation,
    alternatingSixOuterSecondSeparator_root_pow_sixty]
  ring

/-- The row-07 value at the positive state-79 word. -/
theorem alternatingSixAmbientRow07_secondSeparator_trace :
    (alternatingSixFiveAmbient_row07_matrixA *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixA *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixA *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixB).trace =
      1 := by
  rw [show
    alternatingSixFiveAmbient_row07_matrixA *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixA *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixA *
          alternatingSixFiveAmbient_row07_matrixB *
          alternatingSixFiveAmbient_row07_matrixB =
        (alternatingSixFiveAmbient_row07_matrixA *
            alternatingSixFiveAmbient_row07_matrixB) *
          (alternatingSixFiveAmbient_row07_matrixA *
            alternatingSixFiveAmbient_row07_matrixB *
            alternatingSixFiveAmbient_row07_matrixB *
            alternatingSixFiveAmbient_row07_matrixB) *
          (alternatingSixFiveAmbient_row07_matrixA *
            alternatingSixFiveAmbient_row07_matrixB *
            alternatingSixFiveAmbient_row07_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow07_matrixABBB,
    alternatingSixAmbientRow07_matrixABB,
    alternatingSixAmbientRow07_matrixAB]
  exact alternatingSixAmbientRow07_secondSeparator_reduced_trace

/-! ### Degree-five values -/

/-- The row-08 value at the positive state-79 word. -/
theorem alternatingSixAmbientRow08_secondSeparator_trace :
    (alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB).trace =
      -1 := by
  change
    (∑ i : Fin 5,
      (alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixA *
          alternatingSixFiveAmbient_row08_matrixB *
          alternatingSixFiveAmbient_row08_matrixB) i i) = -1
  simp_rw [Matrix.mul_apply]
  simp [
    alternatingSixFiveAmbient_row08_matrixA,
    alternatingSixFiveAmbient_row08_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]

private theorem alternatingSixAmbientRow09_secondSeparator_reduced_trace :
    (alternatingSixAmbientRow09MatrixAB *
          alternatingSixAmbientRow09MatrixABBB *
        alternatingSixAmbientRow09MatrixABB).trace =
      2 := by
  change
    (∑ i : Fin 5,
      (alternatingSixAmbientRow09MatrixAB *
          alternatingSixAmbientRow09MatrixABBB *
        alternatingSixAmbientRow09MatrixABB) i i) = 2
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixAmbientRow09MatrixAB,
    alternatingSixAmbientRow09MatrixABB,
    alternatingSixAmbientRow09MatrixABBB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring_nf
  rw [alternatingSixOuterSecondSeparator_orderSixRelation,
    alternatingSixOuterSecondSeparator_root_pow_sixty]
  ring

/-- The row-09 value at the positive state-79 word. -/
theorem alternatingSixAmbientRow09_secondSeparator_trace :
    (alternatingSixFiveAmbient_row09_matrixA *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixA *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixA *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixB).trace =
      2 := by
  rw [show
    alternatingSixFiveAmbient_row09_matrixA *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixA *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixA *
          alternatingSixFiveAmbient_row09_matrixB *
          alternatingSixFiveAmbient_row09_matrixB =
        (alternatingSixFiveAmbient_row09_matrixA *
            alternatingSixFiveAmbient_row09_matrixB) *
          (alternatingSixFiveAmbient_row09_matrixA *
            alternatingSixFiveAmbient_row09_matrixB *
            alternatingSixFiveAmbient_row09_matrixB *
            alternatingSixFiveAmbient_row09_matrixB) *
          (alternatingSixFiveAmbient_row09_matrixA *
            alternatingSixFiveAmbient_row09_matrixB *
            alternatingSixFiveAmbient_row09_matrixB) by
      simp only [Matrix.mul_assoc]]
  rw [alternatingSixAmbientRow09_matrixABBB,
    alternatingSixAmbientRow09_matrixABB,
    alternatingSixAmbientRow09_matrixAB]
  exact alternatingSixAmbientRow09_secondSeparator_reduced_trace

/-! ### Packaged character values -/

/-- The normalized row-06 representation has second-separator value `-2`. -/
theorem alternatingSixAmbientRow06_character_secondSeparator :
    alternatingSixAmbientRow06CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSecondSeparator =
      -2 := by
  letI : Nonempty (Fin (.row06 : AlternatingSixAmbientOrdinaryRow).dimension) :=
    Fin.pos_iff_nonempty.mp (.row06 : AlternatingSixAmbientOrdinaryRow).dimension_pos
  rw [alternatingSixAmbientRow06CharacterRowCertificate_representation,
    alternatingSixAmbientRow06MatrixCertificate
      |>.universalCoverRepresentation_character_secondSeparator]
  exact alternatingSixAmbientRow06_secondSeparator_trace

/-- The normalized row-07 representation has second-separator value `1`. -/
theorem alternatingSixAmbientRow07_character_secondSeparator :
    alternatingSixAmbientRow07CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSecondSeparator =
      1 := by
  letI : Nonempty (Fin (.row07 : AlternatingSixAmbientOrdinaryRow).dimension) :=
    Fin.pos_iff_nonempty.mp (.row07 : AlternatingSixAmbientOrdinaryRow).dimension_pos
  rw [alternatingSixAmbientRow07CharacterRowCertificate_representation,
    alternatingSixAmbientRow07MatrixCertificate
      |>.universalCoverRepresentation_character_secondSeparator]
  exact alternatingSixAmbientRow07_secondSeparator_trace

/-- The normalized row-08 representation has second-separator value `-1`. -/
theorem alternatingSixAmbientRow08_character_secondSeparator :
    alternatingSixAmbientRow08CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSecondSeparator =
      -1 := by
  letI : Nonempty (Fin (.row08 : AlternatingSixAmbientOrdinaryRow).dimension) :=
    Fin.pos_iff_nonempty.mp (.row08 : AlternatingSixAmbientOrdinaryRow).dimension_pos
  rw [alternatingSixAmbientRow08CharacterRowCertificate_representation,
    alternatingSixAmbientRow08MatrixCertificate
      |>.universalCoverRepresentation_character_secondSeparator]
  exact alternatingSixAmbientRow08_secondSeparator_trace

/-- The normalized row-09 representation has second-separator value `2`. -/
theorem alternatingSixAmbientRow09_character_secondSeparator :
    alternatingSixAmbientRow09CharacterRowCertificate.representation.character
        alternatingSixAmbientCanonicalSecondSeparator =
      2 := by
  letI : Nonempty (Fin (.row09 : AlternatingSixAmbientOrdinaryRow).dimension) :=
    Fin.pos_iff_nonempty.mp (.row09 : AlternatingSixAmbientOrdinaryRow).dimension_pos
  rw [alternatingSixAmbientRow09CharacterRowCertificate_representation,
    alternatingSixAmbientRow09MatrixCertificate
      |>.universalCoverRepresentation_character_secondSeparator]
  exact alternatingSixAmbientRow09_secondSeparator_trace

end InductiveMcKay
end McKayConjecture
