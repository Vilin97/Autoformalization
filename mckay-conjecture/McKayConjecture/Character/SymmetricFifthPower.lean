/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Character
import Mathlib.Tactic

/-!
# Explicit fifth symmetric powers of two-dimensional representations

For a two-by-two matrix, this file gives the matrix of its action on
homogeneous quintic polynomials in the ordered basis

`x⁵, x⁴y, x³y², x²y³, xy⁴, y⁵`.

The construction is multiplicative, hence sends an arbitrary
two-dimensional matrix representation to a six-dimensional
representation.  Its trace is recorded in terms of the trace and
determinant of the original matrix.
-/

noncomputable section

open Matrix

namespace McKayConjecture
namespace SymmetricFifthPower

variable {R : Type*} [CommRing R]

/-- Matrix of the fifth-symmetric-power action, in the basis
`x⁵, x⁴y, x³y², x²y³, xy⁴, y⁵`.  Columns are the images of basis
vectors. -/
def matrix (M : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 6) (Fin 6) R :=
  let a := M 0 0
  let b := M 0 1
  let c := M 1 0
  let d := M 1 1
  !![
    a ^ 5, a ^ 4 * b, a ^ 3 * b ^ 2, a ^ 2 * b ^ 3,
      a * b ^ 4, b ^ 5;
    5 * a ^ 4 * c, a ^ 4 * d + 4 * a ^ 3 * b * c,
      2 * a ^ 3 * b * d + 3 * a ^ 2 * b ^ 2 * c,
      3 * a ^ 2 * b ^ 2 * d + 2 * a * b ^ 3 * c,
      4 * a * b ^ 3 * d + b ^ 4 * c, 5 * b ^ 4 * d;
    10 * a ^ 3 * c ^ 2,
      4 * a ^ 3 * c * d + 6 * a ^ 2 * b * c ^ 2,
      a ^ 3 * d ^ 2 + 6 * a ^ 2 * b * c * d +
        3 * a * b ^ 2 * c ^ 2,
      3 * a ^ 2 * b * d ^ 2 + 6 * a * b ^ 2 * c * d +
        b ^ 3 * c ^ 2,
      6 * a * b ^ 2 * d ^ 2 + 4 * b ^ 3 * c * d,
      10 * b ^ 3 * d ^ 2;
    10 * a ^ 2 * c ^ 3,
      6 * a ^ 2 * c ^ 2 * d + 4 * a * b * c ^ 3,
      3 * a ^ 2 * c * d ^ 2 + 6 * a * b * c ^ 2 * d +
        b ^ 2 * c ^ 3,
      a ^ 2 * d ^ 3 + 6 * a * b * c * d ^ 2 +
        3 * b ^ 2 * c ^ 2 * d,
      4 * a * b * d ^ 3 + 6 * b ^ 2 * c * d ^ 2,
      10 * b ^ 2 * d ^ 3;
    5 * a * c ^ 4, 4 * a * c ^ 3 * d + b * c ^ 4,
      3 * a * c ^ 2 * d ^ 2 + 2 * b * c ^ 3 * d,
      2 * a * c * d ^ 3 + 3 * b * c ^ 2 * d ^ 2,
      a * d ^ 4 + 4 * b * c * d ^ 3, 5 * b * d ^ 4;
    c ^ 5, c ^ 4 * d, c ^ 3 * d ^ 2, c ^ 2 * d ^ 3,
      c * d ^ 4, d ^ 5
  ]

@[simp]
theorem matrix_one :
    matrix (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

/-- Scalars act on the fifth symmetric power by their fifth power. -/
theorem matrix_scalar (r : R) :
    matrix (Matrix.scalar (Fin 2) r) =
      Matrix.scalar (Fin 6) (r ^ 5) := by
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

private theorem matrix_mul_row_zero
    (M N : Matrix (Fin 2) (Fin 2) R) (j : Fin 6) :
    matrix (M * N) 0 j = (matrix M * matrix N) 0 j := by
  fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private theorem matrix_mul_row_one
    (M N : Matrix (Fin 2) (Fin 2) R) (j : Fin 6) :
    matrix (M * N) 1 j = (matrix M * matrix N) 1 j := by
  fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private theorem matrix_mul_row_two
    (M N : Matrix (Fin 2) (Fin 2) R) (j : Fin 6) :
    matrix (M * N) 2 j = (matrix M * matrix N) 2 j := by
  fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private theorem matrix_mul_row_three
    (M N : Matrix (Fin 2) (Fin 2) R) (j : Fin 6) :
    matrix (M * N) 3 j = (matrix M * matrix N) 3 j := by
  fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private theorem matrix_mul_row_four
    (M N : Matrix (Fin 2) (Fin 2) R) (j : Fin 6) :
    matrix (M * N) 4 j = (matrix M * matrix N) 4 j := by
  fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private theorem matrix_mul_row_five
    (M N : Matrix (Fin 2) (Fin 2) R) (j : Fin 6) :
    matrix (M * N) 5 j = (matrix M * matrix N) 5 j := by
  fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

theorem matrix_mul
    (M N : Matrix (Fin 2) (Fin 2) R) :
    matrix (M * N) = matrix M * matrix N := by
  ext i j
  fin_cases i
  · exact matrix_mul_row_zero M N j
  · exact matrix_mul_row_one M N j
  · exact matrix_mul_row_two M N j
  · exact matrix_mul_row_three M N j
  · exact matrix_mul_row_four M N j
  · exact matrix_mul_row_five M N j

/-- Fifth symmetric power as a multiplicative map on matrix monoids. -/
def matrixMonoidHom :
    Matrix (Fin 2) (Fin 2) R →*
      Matrix (Fin 6) (Fin 6) R where
  toFun := matrix
  map_one' := matrix_one
  map_mul' := matrix_mul

@[simp]
theorem matrixMonoidHom_apply
    (M : Matrix (Fin 2) (Fin 2) R) :
    matrixMonoidHom M = matrix M :=
  rfl

/-- Fifth symmetric power of an invertible two-by-two matrix. -/
def generalLinearGroupHom :
    Matrix.GeneralLinearGroup (Fin 2) R →*
      Matrix.GeneralLinearGroup (Fin 6) R :=
  Units.map matrixMonoidHom

@[simp]
theorem coe_generalLinearGroupHom
    (M : Matrix.GeneralLinearGroup (Fin 2) R) :
    (generalLinearGroupHom M :
      Matrix (Fin 6) (Fin 6) R) =
      matrix (M : Matrix (Fin 2) (Fin 2) R) :=
  rfl

/-- The trace of a fifth symmetric power depends only on the original
trace and determinant. -/
theorem trace_matrix
    (M : Matrix (Fin 2) (Fin 2) R) :
    Matrix.trace (matrix M) =
      Matrix.trace M ^ 5 -
        4 * Matrix.det M * Matrix.trace M ^ 3 +
          3 * Matrix.det M ^ 2 * Matrix.trace M := by
  simp [matrix, Matrix.trace, Matrix.det_fin_two,
    Fin.sum_univ_succ]
  ring

/-- For determinant-one matrices, the fifth-symmetric-power trace is
`t⁵ - 4t³ + 3t`. -/
theorem trace_matrix_of_det_one
    (M : Matrix (Fin 2) (Fin 2) R)
    (hdet : Matrix.det M = 1) :
    Matrix.trace (matrix M) =
      Matrix.trace M ^ 5 -
        4 * Matrix.trace M ^ 3 + 3 * Matrix.trace M := by
  rw [trace_matrix, hdet]
  ring

section ComplexRepresentation

variable {G : Type*} [Group G]

/-- Fifth symmetric power of a two-dimensional matrix representation. -/
def representation
    (ρ : G →*
      Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    Representation ℂ G (Fin 6 → ℂ) :=
  (Units.coeHom
      ((Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ))).comp
    ((Matrix.GeneralLinearGroup.toLin :
        Matrix.GeneralLinearGroup (Fin 6) ℂ ≃*
          LinearMap.GeneralLinearGroup ℂ (Fin 6 → ℂ))
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

/-- The finite-dimensional object attached to a fifth-symmetric-power
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
    Module.finrank ℂ (fdRep ρ) = 6 := by
  simp [fdRep]

theorem representation_character
    (ρ : G →*
      Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (g : G) :
    (representation ρ).character g =
      Matrix.trace
          (ρ g : Matrix (Fin 2) (Fin 2) ℂ) ^ 5 -
        4 * Matrix.det
          (ρ g : Matrix (Fin 2) (Fin 2) ℂ) *
            Matrix.trace
              (ρ g : Matrix (Fin 2) (Fin 2) ℂ) ^ 3 +
        3 * Matrix.det
          (ρ g : Matrix (Fin 2) (Fin 2) ℂ) ^ 2 *
            Matrix.trace
              (ρ g : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [show
      (representation ρ).character g =
        LinearMap.trace ℂ (Fin 6 → ℂ)
          (Matrix.toLin'
            (matrix
              (ρ g :
                Matrix (Fin 2) (Fin 2) ℂ))) by
      rfl,
    Matrix.trace_toLin'_eq, trace_matrix]

/-- Character formula for a fifth symmetric power when the original
matrices have determinant one. -/
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
          (ρ g : Matrix (Fin 2) (Fin 2) ℂ) ^ 5 -
        4 *
          Matrix.trace
            (ρ g : Matrix (Fin 2) (Fin 2) ℂ) ^ 3 +
        3 *
          Matrix.trace
            (ρ g : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [representation_character, hdet]
  ring

end ComplexRepresentation

end SymmetricFifthPower
end McKayConjecture
