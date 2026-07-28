/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixCyclotomicField

/-!
# Common eigenvalues in the degree-three ambient rows

The second presentation generator has the same three eigenvalues in all four
degree-three ordinary rows: `1`, `ζ³⁰`, and `-ζ³⁰`.  Their distinctness is
proved once from primitivity of the chosen 120th root.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- The common eigenvalue vector for the degree-three second generator. -/
def alternatingSixDegreeThreeGeneratorBEigenvalue :
    Fin 3 → ℂ :=
  ![1, ζ ^ 30, -(ζ ^ 30)]

private theorem degreeThree_eigenvalue_pow_thirty_ne_one :
    ζ ^ 30 ≠ 1 :=
  alternatingSixComplexCyclotomicRoot_isPrimitive
    |>.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)

private theorem degreeThree_eigenvalue_pow_sixty_ne_one :
    ζ ^ 60 ≠ 1 :=
  alternatingSixComplexCyclotomicRoot_isPrimitive
    |>.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)

private theorem degreeThree_eigenvalue_pow_thirty_ne_zero :
    ζ ^ 30 ≠ 0 :=
  pow_ne_zero 30
    (alternatingSixComplexCyclotomicRoot_isPrimitive.ne_zero
      (by norm_num))

private theorem degreeThree_neg_eigenvalue_ne_one :
    -(ζ ^ 30) ≠ 1 := by
  intro h
  have hroot : ζ ^ 30 = -1 := by
    linear_combination -h
  apply degreeThree_eigenvalue_pow_sixty_ne_one
  calc
    ζ ^ 60 = ζ ^ (30 * 2) := by norm_num
    _ = (ζ ^ 30) ^ 2 := by rw [pow_mul]
    _ = (-1 : ℂ) ^ 2 := by rw [hroot]
    _ = 1 := by norm_num

private theorem degreeThree_eigenvalue_ne_neg_eigenvalue :
    ζ ^ 30 ≠ -(ζ ^ 30) := by
  intro h
  apply degreeThree_eigenvalue_pow_thirty_ne_zero
  linear_combination h / 2

/-- The three common degree-three eigenvalues are pairwise distinct. -/
theorem alternatingSixDegreeThreeGeneratorBEigenvalue_injective :
    Function.Injective
      alternatingSixDegreeThreeGeneratorBEigenvalue := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals
    simp only [alternatingSixDegreeThreeGeneratorBEigenvalue] at hij ⊢
  · exact (degreeThree_eigenvalue_pow_thirty_ne_one hij.symm).elim
  · exact (degreeThree_neg_eigenvalue_ne_one hij.symm).elim
  · exact (degreeThree_eigenvalue_pow_thirty_ne_one hij).elim
  · exact (degreeThree_eigenvalue_ne_neg_eigenvalue hij).elim
  · exact (degreeThree_neg_eigenvalue_ne_one hij).elim
  · exact (degreeThree_eigenvalue_ne_neg_eigenvalue hij.symm).elim

end InductiveMcKay
end McKayConjecture
