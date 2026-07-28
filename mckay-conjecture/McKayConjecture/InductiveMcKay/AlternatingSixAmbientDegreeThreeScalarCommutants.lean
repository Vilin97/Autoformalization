/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.TwoGeneratorMatrixCommutant
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow03CommutantData
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow04CommutantData
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow05CommutantData

/-!
# Scalar commutants for the remaining degree-three ambient rows

Each result applies the common three-eigenvalue criterion to independently
checked cyclotomic eigenbasis data.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- Every matrix commuting with both row 03 presentation generators is
scalar. -/
theorem alternatingSixAmbientRow03_scalar_commutant
    (X : Matrix (Fin 3) (Fin 3) ℂ)
    (commutesA :
      X * alternatingSixFiveAmbient_row03_matrixA =
        alternatingSixFiveAmbient_row03_matrixA * X)
    (commutesB :
      X * alternatingSixFiveAmbient_row03_matrixB =
        alternatingSixFiveAmbient_row03_matrixB * X) :
    ∃ c : ℂ, X = c • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.scalar_commutant_of_three_eigenvalues
    alternatingSixFiveAmbient_row03_matrixA
    alternatingSixFiveAmbient_row03_matrixB
    alternatingSixAmbientRow03Eigenbasis
    alternatingSixAmbientRow03EigenbasisInverse
    alternatingSixDegreeThreeGeneratorBEigenvalue
    alternatingSixAmbientRow03EigenbasisInverse_mul
    alternatingSixAmbientRow03Eigenbasis_mul_inverse
    alternatingSixAmbientRow03GeneratorB_mul_eigenbasis
    alternatingSixDegreeThreeGeneratorBEigenvalue_injective
  · change alternatingSixAmbientRow03TransformedGeneratorA 0 1 ≠ 0
    rw [alternatingSixAmbientRow03TransformedGeneratorA_entry01]
    exact alternatingSixAmbientRow03Connecting01_ne_zero
  · change alternatingSixAmbientRow03TransformedGeneratorA 0 2 ≠ 0
    rw [alternatingSixAmbientRow03TransformedGeneratorA_entry02]
    exact alternatingSixAmbientRow03Connecting02_ne_zero
  · exact commutesA
  · exact commutesB

/-- Every matrix commuting with both row 04 presentation generators is
scalar. -/
theorem alternatingSixAmbientRow04_scalar_commutant
    (X : Matrix (Fin 3) (Fin 3) ℂ)
    (commutesA :
      X * alternatingSixFiveAmbient_row04_matrixA =
        alternatingSixFiveAmbient_row04_matrixA * X)
    (commutesB :
      X * alternatingSixFiveAmbient_row04_matrixB =
        alternatingSixFiveAmbient_row04_matrixB * X) :
    ∃ c : ℂ, X = c • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.scalar_commutant_of_three_eigenvalues
    alternatingSixFiveAmbient_row04_matrixA
    alternatingSixFiveAmbient_row04_matrixB
    alternatingSixAmbientRow04Eigenbasis
    alternatingSixAmbientRow04EigenbasisInverse
    alternatingSixDegreeThreeGeneratorBEigenvalue
    alternatingSixAmbientRow04EigenbasisInverse_mul
    alternatingSixAmbientRow04Eigenbasis_mul_inverse
    alternatingSixAmbientRow04GeneratorB_mul_eigenbasis
    alternatingSixDegreeThreeGeneratorBEigenvalue_injective
  · change alternatingSixAmbientRow04TransformedGeneratorA 0 1 ≠ 0
    rw [alternatingSixAmbientRow04TransformedGeneratorA_entry01]
    exact alternatingSixAmbientRow04Connecting01_ne_zero
  · change alternatingSixAmbientRow04TransformedGeneratorA 0 2 ≠ 0
    rw [alternatingSixAmbientRow04TransformedGeneratorA_entry02]
    exact alternatingSixAmbientRow04Connecting02_ne_zero
  · exact commutesA
  · exact commutesB

/-- Every matrix commuting with both row 05 presentation generators is
scalar. -/
theorem alternatingSixAmbientRow05_scalar_commutant
    (X : Matrix (Fin 3) (Fin 3) ℂ)
    (commutesA :
      X * alternatingSixFiveAmbient_row05_matrixA =
        alternatingSixFiveAmbient_row05_matrixA * X)
    (commutesB :
      X * alternatingSixFiveAmbient_row05_matrixB =
        alternatingSixFiveAmbient_row05_matrixB * X) :
    ∃ c : ℂ, X = c • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.scalar_commutant_of_three_eigenvalues
    alternatingSixFiveAmbient_row05_matrixA
    alternatingSixFiveAmbient_row05_matrixB
    alternatingSixAmbientRow05Eigenbasis
    alternatingSixAmbientRow05EigenbasisInverse
    alternatingSixDegreeThreeGeneratorBEigenvalue
    alternatingSixAmbientRow05EigenbasisInverse_mul
    alternatingSixAmbientRow05Eigenbasis_mul_inverse
    alternatingSixAmbientRow05GeneratorB_mul_eigenbasis
    alternatingSixDegreeThreeGeneratorBEigenvalue_injective
  · change alternatingSixAmbientRow05TransformedGeneratorA 0 1 ≠ 0
    rw [alternatingSixAmbientRow05TransformedGeneratorA_entry01]
    exact alternatingSixAmbientRow05Connecting01_ne_zero
  · change alternatingSixAmbientRow05TransformedGeneratorA 0 2 ≠ 0
    rw [alternatingSixAmbientRow05TransformedGeneratorA_entry02]
    exact alternatingSixAmbientRow05Connecting02_ne_zero
  · exact commutesA
  · exact commutesB

end InductiveMcKay
end McKayConjecture
