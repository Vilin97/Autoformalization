/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Tactic

/-!
# Explicit generators for `PSL(2, 𝔽₉)`

We construct an element `z` of the canonical field of order nine with
`z² = z + 1`, and use the corrected ATLAS matrices

```
A = (1+z     0)       B = (0    1)
    (2+z  2+2z)           (2  1+z).
```

Both matrices have determinant one.  Their lifts to `SL(2, 𝔽₉)` satisfy

`A² = B⁴ = (AB)⁵ = (AB²)⁵ = -I`.

Consequently, their classes in `PSL(2, 𝔽₉)` satisfy the four standard
relators in the existing presentation of `A₆`.  This file contains only
the finite-field and matrix certificate; the presentation descent and
exceptional isomorphism are kept in a separate file.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open Polynomial

local instance projectiveSpecialLinearTwoOrderNineFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-! ### A quadratic generator of the canonical field of order nine -/

/-- The canonical finite field of order nine. -/
abbrev ProjectiveSpecialLinearTwoOrderNineField : Type :=
  GaloisField 3 2

/-- The irreducible quadratic used to choose a convenient generator of
the field of order nine.  Irreducibility is not needed below: the explicit
divisibility certificate in `X⁹ - X` directly supplies a root. -/
def projectiveSpecialLinearTwoOrderNinePolynomial :
    (ZMod 3)[X] :=
  X ^ 2 - C 1 * X + C (-1)

/-- The chosen quadratic has degree two and is monic. -/
theorem projectiveSpecialLinearTwoOrderNinePolynomial_isMonicOfDegree :
    IsMonicOfDegree
      projectiveSpecialLinearTwoOrderNinePolynomial 2 := by
  exact isMonicOfDegree_sub_add_two 1 (-1)

/-- The chosen quadratic divides `X⁹ - X` over `𝔽₃`. -/
theorem projectiveSpecialLinearTwoOrderNinePolynomial_dvd :
    projectiveSpecialLinearTwoOrderNinePolynomial ∣
      (X ^ 9 - X : (ZMod 3)[X]) := by
  refine
    ⟨X ^ 7 + X ^ 6 + 2 * X ^ 5 + 2 * X ^ 3 +
        2 * X ^ 2 + X, ?_⟩
  simp [projectiveSpecialLinearTwoOrderNinePolynomial]
  ring_nf
  rw [show (3 : (ZMod 3)[X]) = 0 by
    exact CharP.cast_eq_zero ((ZMod 3)[X]) 3]
  simp

/-- The canonical field of order nine contains a root of
`X² - X - 1`. -/
theorem exists_projectiveSpecialLinearTwoOrderNineRoot :
    ∃ z : ProjectiveSpecialLinearTwoOrderNineField,
      z ^ 2 = z + 1 := by
  let F := ProjectiveSpecialLinearTwoOrderNineField
  have hSplits :
      (X ^ 9 - X : F[X]).Splits := by
    simpa [F, GaloisField.card 3 2 (by norm_num)] using
      (FiniteField.splits_X_pow_nat_card_sub_X 3 (K := F))
  have hDvd :
      map (algebraMap (ZMod 3) F)
          projectiveSpecialLinearTwoOrderNinePolynomial ∣
        (X ^ 9 - X : F[X]) := by
    simpa using
      Polynomial.map_dvd
        (algebraMap (ZMod 3) F)
        projectiveSpecialLinearTwoOrderNinePolynomial_dvd
  have hQuadraticSplits :
      (map (algebraMap (ZMod 3) F)
          projectiveSpecialLinearTwoOrderNinePolynomial).Splits :=
    hSplits.of_dvd
      (FiniteField.X_pow_card_sub_X_ne_zero F (by norm_num))
      hDvd
  obtain ⟨z, hz⟩ :=
    hQuadraticSplits.exists_eval_eq_zero (by
      rw [degree_map,
        degree_eq_natDegree
          projectiveSpecialLinearTwoOrderNinePolynomial_isMonicOfDegree.ne_zero,
        projectiveSpecialLinearTwoOrderNinePolynomial_isMonicOfDegree.natDegree_eq]
      norm_num)
  refine ⟨z, ?_⟩
  rw [eval_map] at hz
  simp [projectiveSpecialLinearTwoOrderNinePolynomial] at hz
  linear_combination hz

/-- A fixed root satisfying `z² = z + 1` in the canonical field of order
nine. -/
def projectiveSpecialLinearTwoOrderNineRoot :
    ProjectiveSpecialLinearTwoOrderNineField :=
  Classical.choose exists_projectiveSpecialLinearTwoOrderNineRoot

@[simp]
theorem projectiveSpecialLinearTwoOrderNineRoot_sq :
    projectiveSpecialLinearTwoOrderNineRoot ^ 2 =
      projectiveSpecialLinearTwoOrderNineRoot + 1 :=
  Classical.choose_spec exists_projectiveSpecialLinearTwoOrderNineRoot

/-- Characteristic three, recorded in the form used by the symbolic
matrix certificates. -/
theorem projectiveSpecialLinearTwoOrderNine_three_eq_zero :
    (3 : ProjectiveSpecialLinearTwoOrderNineField) = 0 :=
  CharP.cast_eq_zero ProjectiveSpecialLinearTwoOrderNineField 3

/-! ### The corrected ATLAS matrices -/

/-- The first corrected ATLAS matrix over the canonical field of order
nine. -/
def projectiveSpecialLinearTwoOrderNineMatrixA :
    Matrix (Fin 2) (Fin 2)
      ProjectiveSpecialLinearTwoOrderNineField :=
  let z := projectiveSpecialLinearTwoOrderNineRoot
  !![1 + z, 0; 2 + z, 2 + 2 * z]

/-- The second corrected ATLAS matrix over the canonical field of order
nine. -/
def projectiveSpecialLinearTwoOrderNineMatrixB :
    Matrix (Fin 2) (Fin 2)
      ProjectiveSpecialLinearTwoOrderNineField :=
  let z := projectiveSpecialLinearTwoOrderNineRoot
  !![0, 1; 2, 1 + z]

/-- A reduced form of the product `AB`. -/
private def projectiveSpecialLinearTwoOrderNineMatrixAB :
    Matrix (Fin 2) (Fin 2)
      ProjectiveSpecialLinearTwoOrderNineField :=
  let z := projectiveSpecialLinearTwoOrderNineRoot
  !![0, 1 + z; 1 + z, z]

/-- A reduced form of the product `AB²`. -/
private def projectiveSpecialLinearTwoOrderNineMatrixABSq :
    Matrix (Fin 2) (Fin 2)
      ProjectiveSpecialLinearTwoOrderNineField :=
  let z := projectiveSpecialLinearTwoOrderNineRoot
  !![2 + 2 * z, 2; 2 * z, 2]

theorem projectiveSpecialLinearTwoOrderNineMatrixA_det :
    Matrix.det projectiveSpecialLinearTwoOrderNineMatrixA = 1 := by
  simp [projectiveSpecialLinearTwoOrderNineMatrixA,
    Matrix.det_fin_two]
  linear_combination
    2 * projectiveSpecialLinearTwoOrderNineRoot_sq +
      (1 + 2 * projectiveSpecialLinearTwoOrderNineRoot) *
        projectiveSpecialLinearTwoOrderNine_three_eq_zero

theorem projectiveSpecialLinearTwoOrderNineMatrixB_det :
    Matrix.det projectiveSpecialLinearTwoOrderNineMatrixB = 1 := by
  simp [projectiveSpecialLinearTwoOrderNineMatrixB,
    Matrix.det_fin_two]
  linear_combination
    -projectiveSpecialLinearTwoOrderNine_three_eq_zero

/-- The first lifted generator squares to the negative identity. -/
theorem projectiveSpecialLinearTwoOrderNineMatrixA_sq :
    projectiveSpecialLinearTwoOrderNineMatrixA ^ 2 =
      -(1 :
        Matrix (Fin 2) (Fin 2)
          ProjectiveSpecialLinearTwoOrderNineField) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectiveSpecialLinearTwoOrderNineMatrixA, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination
      projectiveSpecialLinearTwoOrderNineRoot_sq +
        (projectiveSpecialLinearTwoOrderNineRoot + 1) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero
  · linear_combination
      (2 + projectiveSpecialLinearTwoOrderNineRoot) *
        (1 + projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero
  · linear_combination
      4 * projectiveSpecialLinearTwoOrderNineRoot_sq +
        (3 + 4 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero

/-- The second lifted generator has fourth power equal to the negative
identity. -/
theorem projectiveSpecialLinearTwoOrderNineMatrixB_fourth :
    projectiveSpecialLinearTwoOrderNineMatrixB ^ 4 =
      -(1 :
        Matrix (Fin 2) (Fin 2)
          ProjectiveSpecialLinearTwoOrderNineField) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectiveSpecialLinearTwoOrderNineMatrixB, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination
      2 * projectiveSpecialLinearTwoOrderNineRoot_sq +
        (3 + 2 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero
  · linear_combination
      (projectiveSpecialLinearTwoOrderNineRoot + 4) *
          projectiveSpecialLinearTwoOrderNineRoot_sq +
        (3 + 4 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero
  · left
    linear_combination
      (projectiveSpecialLinearTwoOrderNineRoot + 4) *
          projectiveSpecialLinearTwoOrderNineRoot_sq +
        (3 + 4 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero
  · linear_combination
      (projectiveSpecialLinearTwoOrderNineRoot ^ 2 +
          5 * projectiveSpecialLinearTwoOrderNineRoot + 18) *
          projectiveSpecialLinearTwoOrderNineRoot_sq +
        (10 + 13 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero

private theorem projectiveSpecialLinearTwoOrderNineMatrix_mul_eq_AB :
    projectiveSpecialLinearTwoOrderNineMatrixA *
        projectiveSpecialLinearTwoOrderNineMatrixB =
      projectiveSpecialLinearTwoOrderNineMatrixAB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectiveSpecialLinearTwoOrderNineMatrixA,
      projectiveSpecialLinearTwoOrderNineMatrixB,
      projectiveSpecialLinearTwoOrderNineMatrixAB,
      Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination
      (1 + projectiveSpecialLinearTwoOrderNineRoot) *
        projectiveSpecialLinearTwoOrderNine_three_eq_zero
  · linear_combination
      2 * projectiveSpecialLinearTwoOrderNineRoot_sq +
        (2 + 2 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero

private theorem projectiveSpecialLinearTwoOrderNineReducedMatrixAB_fifth :
    projectiveSpecialLinearTwoOrderNineMatrixAB ^ 5 =
      -(1 :
        Matrix (Fin 2) (Fin 2)
          ProjectiveSpecialLinearTwoOrderNineField) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectiveSpecialLinearTwoOrderNineMatrixAB, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination
      (50 + 29 * projectiveSpecialLinearTwoOrderNineRoot +
          13 * projectiveSpecialLinearTwoOrderNineRoot ^ 2 +
          3 * projectiveSpecialLinearTwoOrderNineRoot ^ 3) *
          projectiveSpecialLinearTwoOrderNineRoot_sq +
        (17 + 27 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero
  · linear_combination
      (77 + 44 * projectiveSpecialLinearTwoOrderNineRoot +
          20 * projectiveSpecialLinearTwoOrderNineRoot ^ 2 +
          5 * projectiveSpecialLinearTwoOrderNineRoot ^ 3) *
          projectiveSpecialLinearTwoOrderNineRoot_sq +
        (26 + 42 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero
  · left
    linear_combination
      (29 + 15 * projectiveSpecialLinearTwoOrderNineRoot +
          5 * projectiveSpecialLinearTwoOrderNineRoot ^ 2) *
          projectiveSpecialLinearTwoOrderNineRoot_sq +
        (10 + 16 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero
  · linear_combination
      (98 + 58 * projectiveSpecialLinearTwoOrderNineRoot +
          28 * projectiveSpecialLinearTwoOrderNineRoot ^ 2 +
          8 * projectiveSpecialLinearTwoOrderNineRoot ^ 3) *
          projectiveSpecialLinearTwoOrderNineRoot_sq +
        (33 + 53 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero

/-- The lifted product `AB` has fifth power equal to the negative
identity. -/
theorem projectiveSpecialLinearTwoOrderNineMatrixAB_fifth :
    (projectiveSpecialLinearTwoOrderNineMatrixA *
        projectiveSpecialLinearTwoOrderNineMatrixB) ^ 5 =
      -(1 :
        Matrix (Fin 2) (Fin 2)
          ProjectiveSpecialLinearTwoOrderNineField) := by
  rw [projectiveSpecialLinearTwoOrderNineMatrix_mul_eq_AB]
  exact projectiveSpecialLinearTwoOrderNineReducedMatrixAB_fifth

private theorem projectiveSpecialLinearTwoOrderNineMatrix_mul_sq_eq_ABSq :
    projectiveSpecialLinearTwoOrderNineMatrixA *
        projectiveSpecialLinearTwoOrderNineMatrixB ^ 2 =
      projectiveSpecialLinearTwoOrderNineMatrixABSq := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectiveSpecialLinearTwoOrderNineMatrixA,
      projectiveSpecialLinearTwoOrderNineMatrixB,
      projectiveSpecialLinearTwoOrderNineMatrixABSq, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring_nf
  · linear_combination
      projectiveSpecialLinearTwoOrderNineRoot_sq +
        projectiveSpecialLinearTwoOrderNineRoot *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero
  · linear_combination
      4 * projectiveSpecialLinearTwoOrderNineRoot_sq +
        (4 + 4 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero
  · linear_combination
      (9 + 2 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNineRoot_sq +
        (5 + 8 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero

private theorem projectiveSpecialLinearTwoOrderNineReducedMatrixABSq_fifth :
    projectiveSpecialLinearTwoOrderNineMatrixABSq ^ 5 =
      -(1 :
        Matrix (Fin 2) (Fin 2)
          ProjectiveSpecialLinearTwoOrderNineField) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectiveSpecialLinearTwoOrderNineMatrixABSq, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring_nf
  · linear_combination
      (2688 + 1248 * projectiveSpecialLinearTwoOrderNineRoot +
          320 * projectiveSpecialLinearTwoOrderNineRoot ^ 2 +
          32 * projectiveSpecialLinearTwoOrderNineRoot ^ 3) *
          projectiveSpecialLinearTwoOrderNineRoot_sq +
        (907 + 1472 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero
  · linear_combination
      (992 + 288 * projectiveSpecialLinearTwoOrderNineRoot +
          32 * projectiveSpecialLinearTwoOrderNineRoot ^ 2) *
          projectiveSpecialLinearTwoOrderNineRoot_sq +
        (384 + 640 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero
  · linear_combination
      (1920 + 992 * projectiveSpecialLinearTwoOrderNineRoot +
          288 * projectiveSpecialLinearTwoOrderNineRoot ^ 2 +
          32 * projectiveSpecialLinearTwoOrderNineRoot ^ 3) *
          projectiveSpecialLinearTwoOrderNineRoot_sq +
        (640 + 1024 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero
  · linear_combination
      (768 + 256 * projectiveSpecialLinearTwoOrderNineRoot +
          32 * projectiveSpecialLinearTwoOrderNineRoot ^ 2) *
          projectiveSpecialLinearTwoOrderNineRoot_sq +
        (267 + 448 * projectiveSpecialLinearTwoOrderNineRoot) *
          projectiveSpecialLinearTwoOrderNine_three_eq_zero

/-- The lifted product `AB²` has fifth power equal to the negative
identity. -/
theorem projectiveSpecialLinearTwoOrderNineMatrixABSq_fifth :
    (projectiveSpecialLinearTwoOrderNineMatrixA *
        projectiveSpecialLinearTwoOrderNineMatrixB ^ 2) ^ 5 =
      -(1 :
        Matrix (Fin 2) (Fin 2)
          ProjectiveSpecialLinearTwoOrderNineField) := by
  rw [projectiveSpecialLinearTwoOrderNineMatrix_mul_sq_eq_ABSq]
  exact projectiveSpecialLinearTwoOrderNineReducedMatrixABSq_fifth

/-! ### Special-linear lifts and projective relators -/

/-- The first matrix as an element of `SL(2, 𝔽₉)`. -/
def projectiveSpecialLinearTwoOrderNineSpecialLinearA :
    Matrix.SpecialLinearGroup
      (Fin 2) ProjectiveSpecialLinearTwoOrderNineField :=
  ⟨projectiveSpecialLinearTwoOrderNineMatrixA,
    projectiveSpecialLinearTwoOrderNineMatrixA_det⟩

/-- The second matrix as an element of `SL(2, 𝔽₉)`. -/
def projectiveSpecialLinearTwoOrderNineSpecialLinearB :
    Matrix.SpecialLinearGroup
      (Fin 2) ProjectiveSpecialLinearTwoOrderNineField :=
  ⟨projectiveSpecialLinearTwoOrderNineMatrixB,
    projectiveSpecialLinearTwoOrderNineMatrixB_det⟩

private theorem projectiveSpecialLinearTwoOrderNineSpecialLinearA_sq :
    projectiveSpecialLinearTwoOrderNineSpecialLinearA ^ 2 = -1 := by
  apply Subtype.ext
  exact projectiveSpecialLinearTwoOrderNineMatrixA_sq

private theorem projectiveSpecialLinearTwoOrderNineSpecialLinearB_fourth :
    projectiveSpecialLinearTwoOrderNineSpecialLinearB ^ 4 = -1 := by
  apply Subtype.ext
  exact projectiveSpecialLinearTwoOrderNineMatrixB_fourth

private theorem projectiveSpecialLinearTwoOrderNineSpecialLinearAB_fifth :
    (projectiveSpecialLinearTwoOrderNineSpecialLinearA *
        projectiveSpecialLinearTwoOrderNineSpecialLinearB) ^ 5 =
      -1 := by
  apply Subtype.ext
  exact projectiveSpecialLinearTwoOrderNineMatrixAB_fifth

private theorem projectiveSpecialLinearTwoOrderNineSpecialLinearABSq_fifth :
    (projectiveSpecialLinearTwoOrderNineSpecialLinearA *
        projectiveSpecialLinearTwoOrderNineSpecialLinearB ^ 2) ^ 5 =
      -1 := by
  apply Subtype.ext
  exact projectiveSpecialLinearTwoOrderNineMatrixABSq_fifth

private theorem projectiveSpecialLinearTwoOrderNine_negOne_mem_center :
    (-1 :
        Matrix.SpecialLinearGroup
          (Fin 2) ProjectiveSpecialLinearTwoOrderNineField) ∈
      Subgroup.center
        (Matrix.SpecialLinearGroup
          (Fin 2) ProjectiveSpecialLinearTwoOrderNineField) := by
  rw [Subgroup.mem_center_iff]
  intro g
  simp

/-- The quotient map from the special-linear group to its projective
quotient. -/
private def projectiveSpecialLinearTwoOrderNineQuotient :
    Matrix.SpecialLinearGroup
        (Fin 2) ProjectiveSpecialLinearTwoOrderNineField →*
      Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) ProjectiveSpecialLinearTwoOrderNineField :=
  QuotientGroup.mk'
    (Subgroup.center
      (Matrix.SpecialLinearGroup
        (Fin 2) ProjectiveSpecialLinearTwoOrderNineField))

/-- The first projective generator. -/
def projectiveSpecialLinearTwoOrderNineProjectiveA :
    Matrix.ProjectiveSpecialLinearGroup
      (Fin 2) ProjectiveSpecialLinearTwoOrderNineField :=
  projectiveSpecialLinearTwoOrderNineQuotient
    projectiveSpecialLinearTwoOrderNineSpecialLinearA

/-- The second projective generator. -/
def projectiveSpecialLinearTwoOrderNineProjectiveB :
    Matrix.ProjectiveSpecialLinearGroup
      (Fin 2) ProjectiveSpecialLinearTwoOrderNineField :=
  projectiveSpecialLinearTwoOrderNineQuotient
    projectiveSpecialLinearTwoOrderNineSpecialLinearB

/-- The two projective generators satisfy the four standard relators for
`A₆`. -/
theorem projectiveSpecialLinearTwoOrderNineProjective_relations :
    projectiveSpecialLinearTwoOrderNineProjectiveA ^ 2 = 1 ∧
      projectiveSpecialLinearTwoOrderNineProjectiveB ^ 4 = 1 ∧
      (projectiveSpecialLinearTwoOrderNineProjectiveA *
          projectiveSpecialLinearTwoOrderNineProjectiveB) ^ 5 = 1 ∧
      (projectiveSpecialLinearTwoOrderNineProjectiveA *
          projectiveSpecialLinearTwoOrderNineProjectiveB ^ 2) ^ 5 = 1 := by
  constructor
  · change
      (projectiveSpecialLinearTwoOrderNineQuotient
          projectiveSpecialLinearTwoOrderNineSpecialLinearA) ^ 2 = 1
    rw [← map_pow,
      projectiveSpecialLinearTwoOrderNineSpecialLinearA_sq]
    exact
      (QuotientGroup.eq_one_iff _).2
        projectiveSpecialLinearTwoOrderNine_negOne_mem_center
  constructor
  · change
      (projectiveSpecialLinearTwoOrderNineQuotient
          projectiveSpecialLinearTwoOrderNineSpecialLinearB) ^ 4 = 1
    rw [← map_pow,
      projectiveSpecialLinearTwoOrderNineSpecialLinearB_fourth]
    exact
      (QuotientGroup.eq_one_iff _).2
        projectiveSpecialLinearTwoOrderNine_negOne_mem_center
  constructor
  · change
      (projectiveSpecialLinearTwoOrderNineQuotient
          projectiveSpecialLinearTwoOrderNineSpecialLinearA *
        projectiveSpecialLinearTwoOrderNineQuotient
          projectiveSpecialLinearTwoOrderNineSpecialLinearB) ^ 5 = 1
    rw [← map_mul, ← map_pow,
      projectiveSpecialLinearTwoOrderNineSpecialLinearAB_fifth]
    exact
      (QuotientGroup.eq_one_iff _).2
        projectiveSpecialLinearTwoOrderNine_negOne_mem_center
  · change
      (projectiveSpecialLinearTwoOrderNineQuotient
          projectiveSpecialLinearTwoOrderNineSpecialLinearA *
        (projectiveSpecialLinearTwoOrderNineQuotient
          projectiveSpecialLinearTwoOrderNineSpecialLinearB) ^ 2) ^ 5 = 1
    rw [← map_pow,
      ← map_mul, ← map_pow,
      projectiveSpecialLinearTwoOrderNineSpecialLinearABSq_fifth]
    exact
      (QuotientGroup.eq_one_iff _).2
        projectiveSpecialLinearTwoOrderNine_negOne_mem_center

/-- The second projective generator is nontrivial. -/
theorem projectiveSpecialLinearTwoOrderNineProjectiveB_ne_one :
    projectiveSpecialLinearTwoOrderNineProjectiveB ≠ 1 := by
  intro hOne
  have hCentral :
      projectiveSpecialLinearTwoOrderNineSpecialLinearB ∈
        Subgroup.center
          (Matrix.SpecialLinearGroup
            (Fin 2) ProjectiveSpecialLinearTwoOrderNineField) :=
    (QuotientGroup.eq_one_iff _).1 hOne
  obtain ⟨r, _hr, hScalar⟩ :=
    Matrix.SpecialLinearGroup.mem_center_iff.mp hCentral
  have hEntry :=
    congrArg
      (fun g :
          Matrix (Fin 2) (Fin 2)
            ProjectiveSpecialLinearTwoOrderNineField =>
        g 0 1)
      hScalar
  simpa [projectiveSpecialLinearTwoOrderNineSpecialLinearB,
    projectiveSpecialLinearTwoOrderNineMatrixB,
    Matrix.scalar_apply] using hEntry

end InductiveMcKay
end McKayConjecture
