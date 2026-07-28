/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Linear
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace

/-!
# Degree-one irreducible characters

Every degree-one irreducible complex character is obtained from a unique
homomorphism to `ℂˣ`.  The inverse construction takes the determinant of
the chosen one-dimensional realization.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

universe u v

/-- Trace and determinant agree on a one-dimensional finite module. -/
theorem trace_eq_det_of_finrank_eq_one
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V]
    (hV : Module.finrank ℂ V = 1)
    (f : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V f = LinearMap.det f := by
  let b : Module.Basis (Fin 1) ℂ V :=
    Module.finBasisOfFinrankEq ℂ V hV
  calc
    LinearMap.trace ℂ V f =
        (LinearMap.toMatrix b b f).trace :=
      LinearMap.trace_eq_matrix_trace ℂ b f
    _ = LinearMap.toMatrix b b f 0 0 :=
      Matrix.trace_fin_one _
    _ = (LinearMap.toMatrix b b f).det :=
      (Matrix.det_fin_one _).symm
    _ = LinearMap.det f :=
      LinearMap.det_toMatrix b f

variable {G : Type u} [Group G]

/-- The multiplicative parameter underlying a degree-one irreducible
character. -/
def linearParameterOfDegreeOne
    (χ : IrreducibleCharacter G)
    (_hχ : χ.degree = 1) :
    G →* ℂˣ :=
  LinearEquiv.det.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv
        ℂ χ.realization).toMonoidHom.comp
      χ.realization.ρ.toHomUnits)

@[simp]
theorem linearParameterOfDegreeOne_values
    (χ : IrreducibleCharacter G)
    (hχ : χ.degree = 1)
    (g : G) :
    (linearParameterOfDegreeOne χ hχ g : ℂ) =
      χ.values g := by
  rw [← χ.realization_character]
  simp only [linearParameterOfDegreeOne, MonoidHom.comp_apply,
    LinearEquiv.coe_det]
  change
    LinearMap.det
        (χ.realization.ρ g :
          χ.realization →ₗ[ℂ] χ.realization) =
      LinearMap.trace ℂ χ.realization
        (χ.realization.ρ g :
          χ.realization →ₗ[ℂ] χ.realization)
  exact
    (trace_eq_det_of_finrank_eq_one
      (χ.realization_finrank.trans hχ)
      (χ.realization.ρ g :
        χ.realization →ₗ[ℂ] χ.realization)).symm

/-- Reconstructing the linear character from its determinant parameter
recovers the original degree-one character. -/
theorem linear_linearParameterOfDegreeOne
    (χ : IrreducibleCharacter G)
    (hχ : χ.degree = 1) :
    linear (linearParameterOfDegreeOne χ hχ) = χ := by
  apply IrreducibleCharacter.ext
  funext g
  rw [linear_values, linearParameterOfDegreeOne_values]

/-- Degree-one irreducible characters are exactly multiplicative complex
characters. -/
def degreeOneEquivLinearCharacter :
    {χ : IrreducibleCharacter G // χ.degree = 1} ≃
      (G →* ℂˣ) where
  toFun χ := linearParameterOfDegreeOne χ.1 χ.2
  invFun lam := ⟨linear lam, linear_degree lam⟩
  left_inv χ := by
    apply Subtype.ext
    exact linear_linearParameterOfDegreeOne χ.1 χ.2
  right_inv lam := by
    apply linear_injective
    exact
      linear_linearParameterOfDegreeOne
        (linear lam) (linear_degree lam)

end IrreducibleCharacter
end McKayConjecture
