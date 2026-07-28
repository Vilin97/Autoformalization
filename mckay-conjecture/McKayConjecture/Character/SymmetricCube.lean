/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Character
import Mathlib.Tactic

/-!
# Explicit symmetric cubes of two-dimensional representations

For a two-by-two matrix, this file gives the matrix of its action on
homogeneous cubic polynomials in the ordered basis

`x³, x²y, xy², y³`.

The construction is multiplicative, hence sends an arbitrary
two-dimensional matrix representation to a four-dimensional
representation.  Its trace is also recorded in terms of the trace and
determinant of the original matrix.
-/

noncomputable section

open Matrix

namespace McKayConjecture
namespace SymmetricCube

variable {R : Type*} [CommRing R]

/-- Matrix of the symmetric-cube action, in the basis
`x³, x²y, xy², y³`.  Columns are the images of the basis vectors. -/
def matrix (M : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 4) (Fin 4) R :=
  let a := M 0 0
  let b := M 0 1
  let c := M 1 0
  let d := M 1 1
  !![
    a ^ 3, a ^ 2 * b, a * b ^ 2, b ^ 3;
    3 * a ^ 2 * c, a ^ 2 * d + 2 * a * b * c,
      2 * a * b * d + b ^ 2 * c, 3 * b ^ 2 * d;
    3 * a * c ^ 2, 2 * a * c * d + b * c ^ 2,
      a * d ^ 2 + 2 * b * c * d, 3 * b * d ^ 2;
    c ^ 3, c ^ 2 * d, c * d ^ 2, d ^ 3
  ]

@[simp]
theorem matrix_one :
    matrix (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

/-- Scalars act on the symmetric cube by their third power. -/
theorem matrix_scalar (r : R) :
    matrix (Matrix.scalar (Fin 2) r) =
      Matrix.scalar (Fin 4) (r ^ 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.scalar] <;>
    ring

@[simp]
theorem matrix_neg_one :
    matrix (-1 : Matrix (Fin 2) (Fin 2) R) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, pow_succ]

theorem matrix_mul
    (M N : Matrix (Fin 2) (Fin 2) R) :
    matrix (M * N) = matrix M * matrix N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_four] <;>
    ring

/-- Symmetric cube as a multiplicative map on matrix monoids. -/
def matrixMonoidHom :
    Matrix (Fin 2) (Fin 2) R →*
      Matrix (Fin 4) (Fin 4) R where
  toFun := matrix
  map_one' := matrix_one
  map_mul' := matrix_mul

@[simp]
theorem matrixMonoidHom_apply
    (M : Matrix (Fin 2) (Fin 2) R) :
    matrixMonoidHom M = matrix M :=
  rfl

/-- Symmetric cube of an invertible two-by-two matrix. -/
def generalLinearGroupHom :
    Matrix.GeneralLinearGroup (Fin 2) R →*
      Matrix.GeneralLinearGroup (Fin 4) R :=
  Units.map matrixMonoidHom

@[simp]
theorem coe_generalLinearGroupHom
    (M : Matrix.GeneralLinearGroup (Fin 2) R) :
    (generalLinearGroupHom M :
      Matrix (Fin 4) (Fin 4) R) =
      matrix (M : Matrix (Fin 2) (Fin 2) R) :=
  rfl

/-- The trace of a symmetric cube depends only on the original trace and
determinant. -/
theorem trace_matrix
    (M : Matrix (Fin 2) (Fin 2) R) :
    Matrix.trace (matrix M) =
      Matrix.trace M ^ 3 -
        2 * Matrix.det M * Matrix.trace M := by
  simp [matrix, Matrix.trace, Matrix.det_fin_two,
    Fin.sum_univ_four]
  ring

/-- For determinant-one matrices, the symmetric-cube trace is
`t³ - 2t`. -/
theorem trace_matrix_of_det_one
    (M : Matrix (Fin 2) (Fin 2) R)
    (hdet : Matrix.det M = 1) :
    Matrix.trace (matrix M) =
      Matrix.trace M ^ 3 - 2 * Matrix.trace M := by
  rw [trace_matrix, hdet]
  ring

section ComplexRepresentation

variable {G : Type*} [Group G]

/-- Symmetric cube of a two-dimensional matrix representation. -/
def representation
    (ρ : G →*
      Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    Representation ℂ G (Fin 4 → ℂ) :=
  (Units.coeHom
      ((Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ))).comp
    ((Matrix.GeneralLinearGroup.toLin :
        Matrix.GeneralLinearGroup (Fin 4) ℂ ≃*
          LinearMap.GeneralLinearGroup ℂ (Fin 4 → ℂ))
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

/-- The finite-dimensional object attached to a symmetric-cube
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
    Module.finrank ℂ (fdRep ρ) = 4 := by
  simp [fdRep]

theorem representation_character
    (ρ : G →*
      Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (g : G) :
    (representation ρ).character g =
      Matrix.trace
          (ρ g : Matrix (Fin 2) (Fin 2) ℂ) ^ 3 -
        2 * Matrix.det
          (ρ g : Matrix (Fin 2) (Fin 2) ℂ) *
            Matrix.trace
              (ρ g : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [show
      (representation ρ).character g =
        LinearMap.trace ℂ (Fin 4 → ℂ)
          (Matrix.toLin'
            (matrix
              (ρ g :
                Matrix (Fin 2) (Fin 2) ℂ))) by
      rfl,
    Matrix.trace_toLin'_eq, trace_matrix]

/-- Character formula for a symmetric cube when the original matrices
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
          (ρ g : Matrix (Fin 2) (Fin 2) ℂ) ^ 3 -
        2 * Matrix.trace
          (ρ g : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [representation_character, hdet]
  ring

end ComplexRepresentation

end SymmetricCube
end McKayConjecture
