/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Construction
import McKayConjecture.Character.IrreducibleCharacterBasis
import McKayConjecture.GroupTheory.SpecialLinearTwoFivePresentation
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# Ambient `3'`-representations of `SL(2, 𝔽₅)`

The two faithful degree-two representations of the binary icosahedral group
are constructed from its balanced presentation.  Their matrices are the
standard embedding of two unit quaternions into `SL(2, ℂ)`.  The two choices
of a root of `T² - T - 1` give the Galois-conjugate representations.
-/

noncomputable section

open CategoryTheory Matrix
open scoped MatrixGroups

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The usual embedding of a complex quaternion coordinate tuple into a
two-by-two complex matrix. -/
def binaryIcosahedralQuaternionMatrix
    (a b c d : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a + b * Complex.I, c + d * Complex.I;
    -c + d * Complex.I, a - b * Complex.I]

@[simp]
theorem binaryIcosahedralQuaternionMatrix_mul
    (a b c d e f g h : ℂ) :
    binaryIcosahedralQuaternionMatrix a b c d *
        binaryIcosahedralQuaternionMatrix e f g h =
      binaryIcosahedralQuaternionMatrix
        (a * e - b * f - c * g - d * h)
        (a * f + b * e + c * h - d * g)
        (a * g - b * h + c * e + d * f)
        (a * h + b * g - c * f + d * e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryIcosahedralQuaternionMatrix,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf
  all_goals
    rw [Complex.I_sq]
    ring

@[simp]
theorem binaryIcosahedralQuaternionMatrix_one :
    binaryIcosahedralQuaternionMatrix 1 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryIcosahedralQuaternionMatrix]

@[simp]
theorem binaryIcosahedralQuaternionMatrix_neg_one :
    binaryIcosahedralQuaternionMatrix (-1) 0 0 0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryIcosahedralQuaternionMatrix]

@[simp]
theorem binaryIcosahedralQuaternionMatrix_det
    (a b c d : ℂ) :
    Matrix.det
        (binaryIcosahedralQuaternionMatrix a b c d) =
      a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  simp [binaryIcosahedralQuaternionMatrix,
    Matrix.det_fin_two]
  ring_nf
  rw [Complex.I_sq]
  ring

@[simp]
theorem binaryIcosahedralQuaternionMatrix_trace
    (a b c d : ℂ) :
    Matrix.trace
        (binaryIcosahedralQuaternionMatrix a b c d) =
      2 * a := by
  simp [binaryIcosahedralQuaternionMatrix,
    Matrix.trace_fin_two]
  ring

/-- The positive golden root, regarded as a complex number. -/
def binaryIcosahedralGoldenRootPlus : ℂ :=
  (1 + (Real.sqrt 5 : ℂ)) / 2

/-- The Galois-conjugate golden root. -/
def binaryIcosahedralGoldenRootMinus : ℂ :=
  (1 - (Real.sqrt 5 : ℂ)) / 2

theorem one_sub_binaryIcosahedralGoldenRootPlus :
    1 - binaryIcosahedralGoldenRootPlus =
      binaryIcosahedralGoldenRootMinus := by
  rw [binaryIcosahedralGoldenRootPlus,
    binaryIcosahedralGoldenRootMinus]
  ring

theorem binaryIcosahedralGoldenRootPlus_sq :
    binaryIcosahedralGoldenRootPlus ^ 2 =
      binaryIcosahedralGoldenRootPlus + 1 := by
  have hsqrt : ((Real.sqrt 5 : ℂ) ^ 2) = 5 := by
    exact_mod_cast
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  rw [binaryIcosahedralGoldenRootPlus]
  field_simp
  linear_combination hsqrt

theorem binaryIcosahedralGoldenRootMinus_sq :
    binaryIcosahedralGoldenRootMinus ^ 2 =
      binaryIcosahedralGoldenRootMinus + 1 := by
  have hsqrt : ((Real.sqrt 5 : ℂ) ^ 2) = 5 := by
    exact_mod_cast
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  rw [binaryIcosahedralGoldenRootMinus]
  field_simp
  linear_combination hsqrt

/-- The order-six quaternion matrix used in both faithful rows. -/
def binaryIcosahedralComplexA :
    Matrix (Fin 2) (Fin 2) ℂ :=
  binaryIcosahedralQuaternionMatrix
    (1 / 2) (1 / 2) (1 / 2) (1 / 2)

/-- The order-ten quaternion matrix depending on a golden root `t`. -/
def binaryIcosahedralComplexB (t : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  binaryIcosahedralQuaternionMatrix
    (t / 2) ((t - 1) / 2) (1 / 2) 0

theorem binaryIcosahedralComplexA_det :
    Matrix.det binaryIcosahedralComplexA = 1 := by
  simp [binaryIcosahedralComplexA]
  ring

@[simp]
theorem binaryIcosahedralComplexA_trace :
    Matrix.trace binaryIcosahedralComplexA = 1 := by
  simp [binaryIcosahedralComplexA]

@[simp]
theorem binaryIcosahedralComplexB_trace (t : ℂ) :
    Matrix.trace (binaryIcosahedralComplexB t) = t := by
  simp [binaryIcosahedralComplexB]
  ring

@[simp]
theorem binaryIcosahedralComplexAB_trace (t : ℂ) :
    Matrix.trace
        (binaryIcosahedralComplexA *
          binaryIcosahedralComplexB t) =
      0 := by
  simp only [binaryIcosahedralComplexA,
    binaryIcosahedralComplexB,
    binaryIcosahedralQuaternionMatrix_mul,
    binaryIcosahedralQuaternionMatrix_trace]
  ring

/-- Trace of the square of a determinant-one two-by-two matrix. -/
theorem trace_pow_two_of_det_one
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hdet : Matrix.det M = 1) :
    Matrix.trace (M ^ 2) =
      Matrix.trace M ^ 2 - 2 := by
  simp [Matrix.trace_fin_two, Matrix.det_fin_two,
    pow_two, Matrix.mul_apply, Fin.sum_univ_two] at hdet ⊢
  linear_combination -2 * hdet

/-- Trace of the cube of a determinant-one two-by-two matrix. -/
theorem trace_pow_three_of_det_one
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hdet : Matrix.det M = 1) :
    Matrix.trace (M ^ 3) =
      Matrix.trace M ^ 3 - 3 * Matrix.trace M := by
  simp [Matrix.trace_fin_two, Matrix.det_fin_two,
    pow_succ, Matrix.mul_apply, Fin.sum_univ_two] at hdet ⊢
  ring_nf at hdet ⊢
  linear_combination
    -3 * (M 0 0 + M 1 1) * hdet

/-- Trace of the fourth power of a determinant-one two-by-two matrix. -/
theorem trace_pow_four_of_det_one
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hdet : Matrix.det M = 1) :
    Matrix.trace (M ^ 4) =
      Matrix.trace M ^ 4 -
        4 * Matrix.trace M ^ 2 + 2 := by
  rw [show M ^ 4 = (M ^ 2) ^ 2 by
    noncomm_ring]
  rw [trace_pow_two_of_det_one
      (M ^ 2) (by simp [Matrix.det_pow, hdet]),
    trace_pow_two_of_det_one M hdet]
  ring

theorem binaryIcosahedralComplexB_det
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    Matrix.det (binaryIcosahedralComplexB t) = 1 := by
  simp [binaryIcosahedralComplexB]
  linear_combination (1 / 2 : ℂ) * ht

theorem binaryIcosahedralComplexA_pow_three :
    binaryIcosahedralComplexA ^ 3 = -1 := by
  simp only [binaryIcosahedralComplexA, pow_succ,
    pow_zero, one_mul,
    binaryIcosahedralQuaternionMatrix_mul]
  norm_num

theorem binaryIcosahedralComplexB_pow_five
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    binaryIcosahedralComplexB t ^ 5 = -1 := by
  simp only [binaryIcosahedralComplexB, pow_succ,
    pow_zero, one_mul,
    binaryIcosahedralQuaternionMatrix_mul]
  have ht3 : t ^ 3 = 2 * t + 1 := by
    calc
      t ^ 3 = t * t ^ 2 := by ring
      _ = t * (t + 1) := by rw [ht]
      _ = 2 * t + 1 := by
        linear_combination ht
  have ht4 : t ^ 4 = 3 * t + 2 := by
    calc
      t ^ 4 = t * t ^ 3 := by ring
      _ = t * (2 * t + 1) := by rw [ht3]
      _ = 3 * t + 2 := by
        linear_combination 2 * ht
  have ht5 : t ^ 5 = 5 * t + 3 := by
    calc
      t ^ 5 = t * t ^ 4 := by ring
      _ = t * (3 * t + 2) := by rw [ht4]
      _ = 5 * t + 3 := by
        linear_combination 3 * ht
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryIcosahedralQuaternionMatrix,
      Complex.I_sq] <;>
    ring_nf
  all_goals
    simp only [ht5, ht4, ht3, ht]
    ring

theorem binaryIcosahedralComplexAB_pow_two
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    (binaryIcosahedralComplexA *
      binaryIcosahedralComplexB t) ^ 2 = -1 := by
  simp only [binaryIcosahedralComplexA,
    binaryIcosahedralComplexB, pow_two,
    binaryIcosahedralQuaternionMatrix_mul]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryIcosahedralQuaternionMatrix,
      Complex.I_sq] <;>
    ring_nf at ht ⊢
  all_goals
    rw [ht]
    ring

/-- The order-six quaternion matrix as an element of `SL(2, ℂ)`. -/
def binaryIcosahedralComplexASL :
    SL(2, ℂ) :=
  ⟨binaryIcosahedralComplexA,
    binaryIcosahedralComplexA_det⟩

/-- The order-ten quaternion matrix as an element of `SL(2, ℂ)`. -/
def binaryIcosahedralComplexBSL
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    SL(2, ℂ) :=
  ⟨binaryIcosahedralComplexB t,
    binaryIcosahedralComplexB_det t ht⟩

/-- Images of the three balanced-presentation generators.  Since the
two-generator presentation uses `a = y`, `b = z`, the eliminated generator
is `x = y z`. -/
def binaryIcosahedralComplexPresentationGenerator
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    Fin 3 → SL(2, ℂ)
  | 0 =>
      binaryIcosahedralComplexASL *
        binaryIcosahedralComplexBSL t ht
  | 1 => binaryIcosahedralComplexASL
  | 2 => binaryIcosahedralComplexBSL t ht

theorem binaryIcosahedralComplexASL_pow_three :
    binaryIcosahedralComplexASL ^ 3 = -1 := by
  apply Subtype.ext
  exact binaryIcosahedralComplexA_pow_three

theorem binaryIcosahedralComplexBSL_pow_five
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    binaryIcosahedralComplexBSL t ht ^ 5 = -1 := by
  apply Subtype.ext
  exact binaryIcosahedralComplexB_pow_five t ht

theorem binaryIcosahedralComplexABSL_pow_two
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    (binaryIcosahedralComplexASL *
      binaryIcosahedralComplexBSL t ht) ^ 2 = -1 := by
  apply Subtype.ext
  exact binaryIcosahedralComplexAB_pow_two t ht

/-- The quaternion matrices kill the balanced binary-icosahedral relators. -/
theorem binaryIcosahedralComplexPresentationGenerator_kills_relators
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    ∀ r ∈ binaryIcosahedralRelators,
      FreeGroup.lift
        (binaryIcosahedralComplexPresentationGenerator t ht) r = 1 := by
  intro r hr
  simp only [binaryIcosahedralRelators,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl
  · simp only [binaryIcosahedralRelatorXY,
      binaryIcosahedralGenerator, map_mul, map_pow,
      FreeGroup.lift_apply_of, map_inv,
      binaryIcosahedralComplexPresentationGenerator]
    rw [binaryIcosahedralComplexABSL_pow_two t ht,
      binaryIcosahedralComplexASL_pow_three]
    simp
  · simp only [binaryIcosahedralRelatorYZ,
      binaryIcosahedralGenerator, map_mul, map_pow,
      FreeGroup.lift_apply_of, map_inv,
      binaryIcosahedralComplexPresentationGenerator]
    rw [binaryIcosahedralComplexASL_pow_three,
      binaryIcosahedralComplexBSL_pow_five t ht]
    simp
  · simp only [binaryIcosahedralRelatorZXYZ,
      binaryIcosahedralGenerator, map_mul, map_pow,
      FreeGroup.lift_apply_of, map_inv,
      binaryIcosahedralComplexPresentationGenerator]
    rw [binaryIcosahedralComplexBSL_pow_five t ht]
    rw [show
      binaryIcosahedralComplexASL *
            binaryIcosahedralComplexBSL t ht *
          binaryIcosahedralComplexASL *
          binaryIcosahedralComplexBSL t ht =
        (binaryIcosahedralComplexASL *
          binaryIcosahedralComplexBSL t ht) ^ 2 by
      simp [pow_two, mul_assoc]]
    rw [binaryIcosahedralComplexABSL_pow_two t ht]
    simp

/-- The faithful two-dimensional `SL(2, ℂ)` model on the balanced presented
group, parameterized by either golden root. -/
def binaryIcosahedralPresentedComplexHom
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    BinaryIcosahedralPresentedGroup →* SL(2, ℂ) :=
  PresentedGroup.toGroup
    (binaryIcosahedralComplexPresentationGenerator_kills_relators t ht)

@[simp]
theorem binaryIcosahedralPresentedComplexHom_x
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    binaryIcosahedralPresentedComplexHom t ht
        binaryIcosahedralPresentedX =
      binaryIcosahedralComplexASL *
        binaryIcosahedralComplexBSL t ht := by
  simp [binaryIcosahedralPresentedComplexHom,
    binaryIcosahedralPresentedX,
    binaryIcosahedralComplexPresentationGenerator]

@[simp]
theorem binaryIcosahedralPresentedComplexHom_y
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    binaryIcosahedralPresentedComplexHom t ht
        binaryIcosahedralPresentedY =
      binaryIcosahedralComplexASL := by
  simp [binaryIcosahedralPresentedComplexHom,
    binaryIcosahedralPresentedY,
    binaryIcosahedralComplexPresentationGenerator]

@[simp]
theorem binaryIcosahedralPresentedComplexHom_z
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    binaryIcosahedralPresentedComplexHom t ht
        binaryIcosahedralPresentedZ =
      binaryIcosahedralComplexBSL t ht := by
  simp [binaryIcosahedralPresentedComplexHom,
    binaryIcosahedralPresentedZ,
    binaryIcosahedralComplexPresentationGenerator]

/-- The two-dimensional complex representation on the balanced presented
group. -/
def binaryIcosahedralPresentedComplexRepresentation
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    Representation ℂ BinaryIcosahedralPresentedGroup
      (Fin 2 → ℂ) where
  toFun g :=
    Matrix.toLin'
      (binaryIcosahedralPresentedComplexHom t ht g : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := by
    rw [map_one]
    exact Matrix.toLin'_one
  map_mul' g h := by
    rw [map_mul]
    exact Matrix.toLin'_mul _ _

/-- The same presented two-dimensional representation, in the general
linear group form consumed by the symmetric-power constructions. -/
def binaryIcosahedralPresentedComplexGeneralLinearHom
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    BinaryIcosahedralPresentedGroup →*
      Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  Matrix.SpecialLinearGroup.toGL.comp
    (binaryIcosahedralPresentedComplexHom t ht)

@[simp]
theorem binaryIcosahedralPresentedComplexGeneralLinearHom_coe
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (g : BinaryIcosahedralPresentedGroup) :
    (binaryIcosahedralPresentedComplexGeneralLinearHom t ht g :
        Matrix (Fin 2) (Fin 2) ℂ) =
      (binaryIcosahedralPresentedComplexHom t ht g :
        Matrix (Fin 2) (Fin 2) ℂ) :=
  rfl

/-- Finite-dimensional object attached to a faithful presented row. -/
abbrev binaryIcosahedralPresentedComplexFDRep
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    FDRep ℂ BinaryIcosahedralPresentedGroup :=
  FDRep.of
    (binaryIcosahedralPresentedComplexRepresentation t ht)

@[simp]
theorem binaryIcosahedralPresentedComplexFDRep_finrank
    (t : ℂ) (ht : t ^ 2 = t + 1) :
    Module.finrank ℂ
        (binaryIcosahedralPresentedComplexFDRep t ht) =
      2 := by
  simp [binaryIcosahedralPresentedComplexFDRep]

theorem binaryIcosahedralPresentedComplexFDRep_character
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (g : BinaryIcosahedralPresentedGroup) :
    (binaryIcosahedralPresentedComplexFDRep t ht).character g =
      Matrix.trace
        (binaryIcosahedralPresentedComplexHom t ht g :
          Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [show
      (binaryIcosahedralPresentedComplexFDRep t ht).character g =
        LinearMap.trace ℂ (Fin 2 → ℂ)
          (Matrix.toLin'
            (binaryIcosahedralPresentedComplexHom t ht g :
              Matrix (Fin 2) (Fin 2) ℂ)) by
      rfl,
    Matrix.trace_toLin'_eq]

theorem binaryIcosahedralPresentedComplexGeneralLinearHom_det
    (t : ℂ) (ht : t ^ 2 = t + 1)
    (g : BinaryIcosahedralPresentedGroup) :
    Matrix.det
        (binaryIcosahedralPresentedComplexGeneralLinearHom t ht g :
          Matrix (Fin 2) (Fin 2) ℂ) =
      1 :=
  Matrix.SpecialLinearGroup.det_coe
    (binaryIcosahedralPresentedComplexHom t ht g)

end InductiveMcKay
end McKayConjecture
