/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismDual
import McKayConjecture.Character.EndomorphismInteriorAction

/-!
# Contragredient actions and transposition

The contragredient of a linear action `ρ` is the action on `V*`
given by precomposition with `ρ(g⁻¹)`.  Transposition of
endomorphisms intertwines conjugation by `ρ` with conjugation by this
contragredient action.
-/

noncomputable section

namespace Representation

variable {k P V : Type}
variable [Field k] [Group P]
variable [AddCommGroup V] [Module k V]

/-- The contragredient action on the linear dual. -/
def contragredientLinearAction
    (rho : P →* (V ≃ₗ[k] V)) :
    P →* (Module.Dual k V ≃ₗ[k] Module.Dual k V) where
  toFun g := (rho g⁻¹).dualMap
  map_one' := by
    ext phi v
    simp
  map_mul' g h := by
    ext phi v
    simp

@[simp]
theorem contragredientLinearAction_apply
    (rho : P →* (V ≃ₗ[k] V))
    (g : P) (phi : Module.Dual k V) (v : V) :
    contragredientLinearAction rho g phi v =
      phi ((rho g).symm v) := by
  change phi (rho g⁻¹ v) = phi ((rho g).symm v)
  rw [map_inv]
  change phi ((rho g).symm v) = phi ((rho g).symm v)
  rfl

@[simp]
theorem contragredientLinearAction_symm_apply
    (rho : P →* (V ≃ₗ[k] V))
    (g : P) (phi : Module.Dual k V) (v : V) :
    (contragredientLinearAction rho g).symm phi v =
      phi (rho g v) := by
  have h :
      (contragredientLinearAction rho g).symm =
        contragredientLinearAction rho g⁻¹ := by
    symm
    exact map_inv (contragredientLinearAction rho) g
  rw [h, contragredientLinearAction_apply]
  rw [map_inv]
  change phi (rho g v) = phi (rho g v)
  rfl

private theorem endomorphismConjugation_apply_of_action
    {X : Type}
    [AddCommGroup X] [Module k X]
    (rho : P →* (X ≃ₗ[k] X))
    (g : P) (f : Module.End k X) (x : X) :
    letI := endomorphismConjugationMulSemiringAction rho
    (g • f) x =
      rho g (f ((rho g).symm x)) := by
  letI := endomorphismConjugationMulSemiringAction rho
  simp only [endomorphismConjugation_smul,
    Module.End.mul_apply]
  rfl

/-- Transposition is equivariant for conjugation by a linear action
and conjugation by its contragredient action. -/
theorem endomorphismDualLinearEquiv_conjugation
    [FiniteDimensional k V]
    (rho : P →* (V ≃ₗ[k] V))
    (g : P) (f : Module.End k V) :
    letI := endomorphismConjugationMulSemiringAction rho
    letI :=
      endomorphismConjugationMulSemiringAction
        (contragredientLinearAction rho)
    g • endomorphismDualLinearEquiv f =
      endomorphismDualLinearEquiv (g • f) := by
  letI := endomorphismConjugationMulSemiringAction rho
  letI :=
    endomorphismConjugationMulSemiringAction
      (contragredientLinearAction rho)
  apply LinearMap.ext
  intro phi
  apply LinearMap.ext
  intro v
  simp only [endomorphismConjugation_apply_of_action,
    endomorphismDualLinearEquiv_apply_apply,
    contragredientLinearAction_apply,
    contragredientLinearAction_symm_apply]

/-- Algebra-equivalence form of contragredient equivariance. -/
theorem endomorphismDualOppositeAlgEquiv_conjugation
    [FiniteDimensional k V]
    (rho : P →* (V ≃ₗ[k] V))
    (g : P) (f : Module.End k V) :
    letI := endomorphismConjugationMulSemiringAction rho
    letI :=
      endomorphismConjugationMulSemiringAction
        (contragredientLinearAction rho)
    g • endomorphismDualOppositeAlgEquiv (MulOpposite.op f) =
      endomorphismDualOppositeAlgEquiv
        (MulOpposite.op (g • f)) := by
  letI := endomorphismConjugationMulSemiringAction rho
  letI :=
    endomorphismConjugationMulSemiringAction
      (contragredientLinearAction rho)
  exact endomorphismDualLinearEquiv_conjugation rho g f

end Representation
