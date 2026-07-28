/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.TwoGeneratorMatrixCommutant

/-!
# Scalar commutants in a checked diagonal basis

This file isolates the basis transport used by explicit common-commutant
calculations.  The second matrix becomes diagonal in the checked basis, while
the first matrix is replaced by a separately checked conjugate.
-/

noncomputable section

namespace McKayConjecture
namespace Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Transport a scalar-commutant calculation from a checked diagonal basis
back to the original two matrices. -/
theorem scalar_commutant_of_diagonal_basis
    {K : Type} [Field K]
    (matrixA matrixB eigenbasis eigenbasisInverse transformedA :
      Matrix ι ι K)
    (eigenvalue : ι → K)
    (inverse_mul_eigenbasis :
      eigenbasisInverse * eigenbasis = 1)
    (eigenbasis_mul_inverse :
      eigenbasis * eigenbasisInverse = 1)
    (matrixB_mul_eigenbasis :
      matrixB * eigenbasis =
        eigenbasis * Matrix.diagonal eigenvalue)
    (transformedA_eq :
      eigenbasisInverse * matrixA * eigenbasis = transformedA)
    (scalar_commutant_in_basis :
      ∀ Y : Matrix ι ι K,
        Y * transformedA = transformedA * Y →
        Y * Matrix.diagonal eigenvalue =
          Matrix.diagonal eigenvalue * Y →
        ∃ c : K, Y = c • (1 : Matrix ι ι K)) :
    ∀ X : Matrix ι ι K,
      X * matrixA = matrixA * X →
      X * matrixB = matrixB * X →
      ∃ c : K, X = c • (1 : Matrix ι ι K) := by
  intro X commutesA commutesB
  let diagonalMatrix : Matrix ι ι K :=
    Matrix.diagonal eigenvalue
  let Y : Matrix ι ι K :=
    eigenbasisInverse * X * eigenbasis
  have inverse_mul_matrixB :
      eigenbasisInverse * matrixB =
        diagonalMatrix * eigenbasisInverse := by
    calc
      eigenbasisInverse * matrixB =
          eigenbasisInverse * matrixB *
            (eigenbasis * eigenbasisInverse) := by
        rw [eigenbasis_mul_inverse, mul_one]
      _ = eigenbasisInverse *
          (matrixB * eigenbasis) * eigenbasisInverse := by
        noncomm_ring
      _ = eigenbasisInverse *
          (eigenbasis * diagonalMatrix) *
            eigenbasisInverse := by
        rw [matrixB_mul_eigenbasis]
      _ = (eigenbasisInverse * eigenbasis) *
          diagonalMatrix * eigenbasisInverse := by
        noncomm_ring
      _ = diagonalMatrix * eigenbasisInverse := by
        rw [inverse_mul_eigenbasis, one_mul]
  have commutesDiagonal :
      Y * diagonalMatrix = diagonalMatrix * Y := by
    calc
      Y * diagonalMatrix =
          eigenbasisInverse * X *
            (eigenbasis * diagonalMatrix) := by
        simp [Y, mul_assoc]
      _ = eigenbasisInverse * X *
          (matrixB * eigenbasis) := by
        rw [matrixB_mul_eigenbasis]
      _ = eigenbasisInverse *
          (X * matrixB) * eigenbasis := by
        noncomm_ring
      _ = eigenbasisInverse *
          (matrixB * X) * eigenbasis := by
        rw [commutesB]
      _ = (eigenbasisInverse * matrixB) *
          X * eigenbasis := by
        noncomm_ring
      _ = (diagonalMatrix * eigenbasisInverse) *
          X * eigenbasis := by
        rw [inverse_mul_matrixB]
      _ = diagonalMatrix * Y := by
        simp [Y, mul_assoc]
  have commutesConjugatedA :
      Y * (eigenbasisInverse * matrixA * eigenbasis) =
        (eigenbasisInverse * matrixA * eigenbasis) * Y := by
    calc
      Y * (eigenbasisInverse * matrixA * eigenbasis) =
          (eigenbasisInverse * X * eigenbasis) *
            (eigenbasisInverse * matrixA * eigenbasis) := by
        rfl
      _ = eigenbasisInverse * X *
          (eigenbasis * eigenbasisInverse) *
            matrixA * eigenbasis := by
        noncomm_ring
      _ = eigenbasisInverse * X * matrixA * eigenbasis := by
        rw [eigenbasis_mul_inverse, mul_one]
      _ = eigenbasisInverse *
          (X * matrixA) * eigenbasis := by
        noncomm_ring
      _ = eigenbasisInverse *
          (matrixA * X) * eigenbasis := by
        rw [commutesA]
      _ = eigenbasisInverse * matrixA * X * eigenbasis := by
        noncomm_ring
      _ = eigenbasisInverse * matrixA *
          (eigenbasis * eigenbasisInverse) *
            X * eigenbasis := by
        rw [eigenbasis_mul_inverse, mul_one]
      _ = (eigenbasisInverse * matrixA * eigenbasis) *
          (eigenbasisInverse * X * eigenbasis) := by
        noncomm_ring
      _ = (eigenbasisInverse * matrixA * eigenbasis) * Y := by
        rfl
  have commutesTransformedA :
      Y * transformedA = transformedA * Y := by
    rw [← transformedA_eq]
    exact commutesConjugatedA
  obtain ⟨c, hc⟩ :=
    scalar_commutant_in_basis Y commutesTransformedA
      commutesDiagonal
  refine ⟨c, ?_⟩
  have recoverX :
      X = eigenbasis * Y * eigenbasisInverse := by
    calc
      X = 1 * X * 1 := by simp
      _ = (eigenbasis * eigenbasisInverse) * X *
          (eigenbasis * eigenbasisInverse) := by
        rw [eigenbasis_mul_inverse]
      _ = eigenbasis *
          (eigenbasisInverse * X * eigenbasis) *
            eigenbasisInverse := by
        noncomm_ring
      _ = eigenbasis * Y * eigenbasisInverse := by
        rfl
  rw [recoverX, hc]
  simp [eigenbasis_mul_inverse]

end Matrix
end McKayConjecture
