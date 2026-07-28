/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.MatrixScalarIdentity
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientRow18DiagonalCommutantReduction14

/-!
# Scalar common commutant for ambient row 18

This wrapper assembles the independently checked reduced relations, proves
the transformed common commutant is scalar, and transports the conclusion
back to the original generator basis.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

private theorem row18_scalarIdentityRow0
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Matrix.HasScalarIdentityRow
      Y (Y 7 7) 0 := by
  intro j
  fin_cases j
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY00
            Y commutesA commutesDiagonal
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY01
            Y commutesA commutesDiagonal
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 0 2 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 0 3 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 0 4 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 0 5 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 0 6 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 0 7 (by decide)

private theorem row18_scalarIdentityRow1
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Matrix.HasScalarIdentityRow
      Y (Y 7 7) 1 := by
  intro j
  fin_cases j
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY10
            Y commutesA commutesDiagonal
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY11
            Y commutesA commutesDiagonal
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 1 2 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 1 3 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 1 4 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 1 5 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 1 6 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 1 7 (by decide)

private theorem row18_scalarIdentityRow2
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Matrix.HasScalarIdentityRow
      Y (Y 7 7) 2 := by
  intro j
  fin_cases j
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 2 0 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 2 1 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY22
            Y commutesA commutesDiagonal
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY23
            Y commutesA commutesDiagonal
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 2 4 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 2 5 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 2 6 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 2 7 (by decide)

private theorem row18_scalarIdentityRow3
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Matrix.HasScalarIdentityRow
      Y (Y 7 7) 3 := by
  intro j
  fin_cases j
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 3 0 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 3 1 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY32
            Y commutesA commutesDiagonal
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY33
            Y commutesA commutesDiagonal
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 3 4 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 3 5 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 3 6 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 3 7 (by decide)

private theorem row18_scalarIdentityRow4
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Matrix.HasScalarIdentityRow
      Y (Y 7 7) 4 := by
  intro j
  fin_cases j
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 4 0 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 4 1 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 4 2 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 4 3 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY44
            Y commutesA commutesDiagonal
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY45
            Y commutesA commutesDiagonal
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 4 6 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 4 7 (by decide)

private theorem row18_scalarIdentityRow5
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Matrix.HasScalarIdentityRow
      Y (Y 7 7) 5 := by
  intro j
  fin_cases j
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 5 0 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 5 1 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 5 2 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 5 3 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY54
            Y commutesA commutesDiagonal
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY55
            Y commutesA commutesDiagonal
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 5 6 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 5 7 (by decide)

private theorem row18_scalarIdentityRow6
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Matrix.HasScalarIdentityRow
      Y (Y 7 7) 6 := by
  intro j
  fin_cases j
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 6 0 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 6 1 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 6 2 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 6 3 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 6 4 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 6 5 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY66
            Y commutesA commutesDiagonal
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY67
            Y commutesA commutesDiagonal

private theorem row18_scalarIdentityRow7
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    Matrix.HasScalarIdentityRow
      Y (Y 7 7) 7 := by
  intro j
  fin_cases j
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 7 0 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 7 1 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 7 2 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 7 3 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 7 4 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          alternatingSixAmbientRow18_off_block
            Y commutesDiagonal 7 5 (by decide)
  · exact by
        simpa [Matrix.HasScalarIdentityRow] using
          row18_reducedY76
            Y commutesA commutesDiagonal
  · exact by simp [Matrix.HasScalarIdentityRow]


/-- A matrix commuting with both transformed row 18 generators is
scalar. -/
theorem alternatingSixAmbientRow18Transformed_scalar_commutant
    (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      Y * alternatingSixAmbientRow18TransformedGeneratorA =
        alternatingSixAmbientRow18TransformedGeneratorA * Y)
    (commutesDiagonal :
      Y * alternatingSixAmbientRow18GeneratorBDiagonal =
        alternatingSixAmbientRow18GeneratorBDiagonal * Y) :
    ∃ c : ℂ,
      Y = c • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  refine ⟨Y 7 7, ?_⟩
  apply Matrix.eq_smul_one_of_scalar_identity_rows
  intro i
  fin_cases i
  · exact row18_scalarIdentityRow0
      Y commutesA commutesDiagonal
  · exact row18_scalarIdentityRow1
      Y commutesA commutesDiagonal
  · exact row18_scalarIdentityRow2
      Y commutesA commutesDiagonal
  · exact row18_scalarIdentityRow3
      Y commutesA commutesDiagonal
  · exact row18_scalarIdentityRow4
      Y commutesA commutesDiagonal
  · exact row18_scalarIdentityRow5
      Y commutesA commutesDiagonal
  · exact row18_scalarIdentityRow6
      Y commutesA commutesDiagonal
  · exact row18_scalarIdentityRow7
      Y commutesA commutesDiagonal


/-- Every matrix commuting with both original row 18 presentation
generators is scalar. -/
theorem alternatingSixAmbientRow18_scalar_commutant
    (X : Matrix (Fin 8) (Fin 8) ℂ)
    (commutesA :
      X * alternatingSixFiveAmbient_row18_matrixA =
        alternatingSixFiveAmbient_row18_matrixA * X)
    (commutesB :
      X * alternatingSixFiveAmbient_row18_matrixB =
        alternatingSixFiveAmbient_row18_matrixB * X) :
    ∃ c : ℂ,
      X = c • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  apply Matrix.scalar_commutant_of_diagonal_basis
    alternatingSixFiveAmbient_row18_matrixA
    alternatingSixFiveAmbient_row18_matrixB
    alternatingSixAmbientRow18Eigenbasis
    alternatingSixAmbientRow18EigenbasisInverse
    alternatingSixAmbientRow18TransformedGeneratorA
    alternatingSixAmbientRow18GeneratorBEigenvalue
    alternatingSixAmbientRow18EigenbasisInverse_mul
    alternatingSixAmbientRow18Eigenbasis_mul_inverse
    alternatingSixAmbientRow18GeneratorB_mul_eigenbasis
    alternatingSixAmbientRow18TransformedGeneratorA_eq
    alternatingSixAmbientRow18Transformed_scalar_commutant
    X commutesA commutesB

end InductiveMcKay
end McKayConjecture
