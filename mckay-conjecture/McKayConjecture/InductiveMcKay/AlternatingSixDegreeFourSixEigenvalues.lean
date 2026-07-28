/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.FinCases
import McKayConjecture.InductiveMcKay.AlternatingSixCyclotomicField

/-!
# Second-generator eigenvalues in degrees four and six

The relevant second-generator matrices have fourth power either `1` or
`-1`.  Their eigenvalues therefore come from one of the two displayed
four-element lists.  Distinctness is proved directly from primitivity of the
chosen 120th root.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

/-- Exponents for the fourth roots of `1` among the powers of `ζ`. -/
def alternatingSixOrderFourEigenvalueExponent :
    Fin 4 → ℕ :=
  ![0, 30, 60, 90]

/-- The fourth roots of `1` used by the degree-six rows. -/
def alternatingSixOrderFourEigenvalue :
    Fin 4 → ℂ :=
  fun i ↦ ζ ^ alternatingSixOrderFourEigenvalueExponent i

/-- Exponents for the fourth roots of `-1` among the powers of `ζ`. -/
def alternatingSixOrderEightOddEigenvalueExponent :
    Fin 4 → ℕ :=
  ![15, 45, 75, 105]

/-- The fourth roots of `-1` used by the degree-four and degree-six rows. -/
def alternatingSixOrderEightOddEigenvalue :
    Fin 4 → ℂ :=
  fun i ↦ ζ ^ alternatingSixOrderEightOddEigenvalueExponent i

private theorem alternatingSixOrderFourEigenvalueExponent_injective :
    Function.Injective
      alternatingSixOrderFourEigenvalueExponent := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [alternatingSixOrderFourEigenvalueExponent] at hij ⊢

private theorem alternatingSixOrderEightOddEigenvalueExponent_injective :
    Function.Injective
      alternatingSixOrderEightOddEigenvalueExponent := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [alternatingSixOrderEightOddEigenvalueExponent] at hij ⊢

/-- The four selected fourth roots of `1` are pairwise distinct. -/
theorem alternatingSixOrderFourEigenvalue_injective :
    Function.Injective alternatingSixOrderFourEigenvalue := by
  intro i j hij
  apply alternatingSixOrderFourEigenvalueExponent_injective
  apply alternatingSixComplexCyclotomicRoot_isPrimitive.pow_inj
  · fin_cases i <;>
      simp [alternatingSixOrderFourEigenvalueExponent]
  · fin_cases j <;>
      simp [alternatingSixOrderFourEigenvalueExponent]
  · simpa [alternatingSixOrderFourEigenvalue] using hij

/-- The four selected fourth roots of `-1` are pairwise distinct. -/
theorem alternatingSixOrderEightOddEigenvalue_injective :
    Function.Injective alternatingSixOrderEightOddEigenvalue := by
  intro i j hij
  apply alternatingSixOrderEightOddEigenvalueExponent_injective
  apply alternatingSixComplexCyclotomicRoot_isPrimitive.pow_inj
  · fin_cases i <;>
      simp [alternatingSixOrderEightOddEigenvalueExponent]
  · fin_cases j <;>
      simp [alternatingSixOrderEightOddEigenvalueExponent]
  · simpa [alternatingSixOrderEightOddEigenvalue] using hij

end InductiveMcKay
end McKayConjecture
