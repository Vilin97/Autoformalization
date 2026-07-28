/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Character
import Mathlib.Tactic

/-!
# Explicit symmetric squares of two-dimensional representations

For a two-by-two matrix, this file gives the matrix of its action on
homogeneous quadratic polynomials in the ordered basis

`x², xy, y²`.

The construction is multiplicative, hence sends an arbitrary
two-dimensional matrix representation to a three-dimensional
representation.  Its trace is recorded in terms of the trace and
determinant of the original matrix.
-/

noncomputable section

open Matrix

namespace McKayConjecture
namespace SymmetricSquare

variable {R : Type*} [CommRing R]

/-- Matrix of the symmetric-square action, in the basis `x², xy, y²`.
Columns are the images of basis vectors. -/
def matrix (M : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 3) (Fin 3) R :=
  let a := M 0 0
  let b := M 0 1
  let c := M 1 0
  let d := M 1 1
  !![
    a ^ 2, a * b, b ^ 2;
    2 * a * c, a * d + b * c, 2 * b * d;
    c ^ 2, c * d, d ^ 2
  ]

@[simp]
theorem matrix_one :
    matrix (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

/-- Scalars act on the symmetric square by their second power. -/
theorem matrix_scalar (r : R) :
    matrix (Matrix.scalar (Fin 2) r) =
      Matrix.scalar (Fin 3) (r ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.scalar]
  ring

@[simp]
theorem matrix_neg_one :
    matrix (-1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, pow_succ]

theorem matrix_mul
    (M N : Matrix (Fin 2) (Fin 2) R) :
    matrix (M * N) = matrix M * matrix N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_three] <;>
    ring

/-- Symmetric square as a multiplicative map on matrix monoids. -/
def matrixMonoidHom :
    Matrix (Fin 2) (Fin 2) R →*
      Matrix (Fin 3) (Fin 3) R where
  toFun := matrix
  map_one' := matrix_one
  map_mul' := matrix_mul

@[simp]
theorem matrixMonoidHom_apply
    (M : Matrix (Fin 2) (Fin 2) R) :
    matrixMonoidHom M = matrix M :=
  rfl

/-- Symmetric square of an invertible two-by-two matrix. -/
def generalLinearGroupHom :
    Matrix.GeneralLinearGroup (Fin 2) R →*
      Matrix.GeneralLinearGroup (Fin 3) R :=
  Units.map matrixMonoidHom

@[simp]
theorem coe_generalLinearGroupHom
    (M : Matrix.GeneralLinearGroup (Fin 2) R) :
    (generalLinearGroupHom M :
      Matrix (Fin 3) (Fin 3) R) =
      matrix (M : Matrix (Fin 2) (Fin 2) R) :=
  rfl

/-- The trace of a symmetric square depends only on the original trace and
determinant. -/
theorem trace_matrix
    (M : Matrix (Fin 2) (Fin 2) R) :
    Matrix.trace (matrix M) =
      Matrix.trace M ^ 2 - Matrix.det M := by
  simp [matrix, Matrix.trace, Matrix.det_fin_two,
    Fin.sum_univ_three]
  ring

/-- For determinant-one matrices, the symmetric-square trace is
`t² - 1`. -/
theorem trace_matrix_of_det_one
    (M : Matrix (Fin 2) (Fin 2) R)
    (hdet : Matrix.det M = 1) :
    Matrix.trace (matrix M) =
      Matrix.trace M ^ 2 - 1 := by
  rw [trace_matrix, hdet]

section ComplexRepresentation

variable {G : Type*} [Group G]

/-- Symmetric square of a two-dimensional matrix representation. -/
def representation
    (ρ : G →*
      Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    Representation ℂ G (Fin 3 → ℂ) :=
  (Units.coeHom
      ((Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ))).comp
    ((Matrix.GeneralLinearGroup.toLin :
        Matrix.GeneralLinearGroup (Fin 3) ℂ ≃*
          LinearMap.GeneralLinearGroup ℂ (Fin 3 → ℂ))
      |>.toMonoidHom.comp
        (generalLinearGroupHom.comp ρ))

@[simp]
theorem representation_apply
    (ρ : G →*
      Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (g : G) :
    representation ρ g =
      Matrix.toLin'
        (matrix
          (ρ g :
            Matrix (Fin 2) (Fin 2) ℂ)) :=
  rfl

/-- The finite-dimensional object attached to a symmetric-square
representation. -/
abbrev fdRep
    (ρ : G →*
      Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    FDRep ℂ G :=
  FDRep.of (representation ρ)

@[simp]
theorem fdRep_finrank
    (ρ : G →*
      Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    Module.finrank ℂ (fdRep ρ) = 3 := by
  simp [fdRep]

theorem representation_character
    (ρ : G →*
      Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (g : G) :
    (representation ρ).character g =
      Matrix.trace
          (ρ g : Matrix (Fin 2) (Fin 2) ℂ) ^ 2 -
        Matrix.det
          (ρ g : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [show
      (representation ρ).character g =
        LinearMap.trace ℂ (Fin 3 → ℂ)
          (Matrix.toLin'
            (matrix
              (ρ g :
                Matrix (Fin 2) (Fin 2) ℂ))) by
      rfl,
    Matrix.trace_toLin'_eq, trace_matrix]

/-- Character formula for a symmetric square when the original matrices
have determinant one. -/
theorem representation_character_of_det_one
    (ρ : G →*
      Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hdet :
      ∀ g : G,
        Matrix.det
          (ρ g : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (g : G) :
    (representation ρ).character g =
      Matrix.trace
          (ρ g : Matrix (Fin 2) (Fin 2) ℂ) ^ 2 - 1 := by
  rw [representation_character, hdet]

end ComplexRepresentation

end SymmetricSquare
end McKayConjecture
