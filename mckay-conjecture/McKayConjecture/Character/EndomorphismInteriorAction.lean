/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismNormalizer
import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# Interior action attached to a linear representation

A linear action of a group on a module acts on the endomorphism algebra by
conjugation.  The same linear operators, regarded as units of the
endomorphism algebra, implement this action.  Thus every linear
representation canonically determines an interior action.
-/

noncomputable section

namespace Representation

variable {k P V : Type}
variable [Field k] [Group P]
variable [AddCommGroup V] [Module k V]

/-- Forget the inverses in a linear group action and regard it as a
representation by linear maps. -/
def linearActionRepresentation
    (ρ : P →* (V ≃ₗ[k] V)) :
    Representation k P V where
  toFun g := ρ g
  map_one' := by
    exact congrArg LinearEquiv.toLinearMap (map_one ρ)
  map_mul' g h := by
    exact congrArg LinearEquiv.toLinearMap (map_mul ρ g h)

@[simp]
theorem linearActionRepresentation_apply
    (ρ : P →* (V ≃ₗ[k] V))
    (g : P) :
    linearActionRepresentation ρ g =
      (ρ g : Module.End k V) :=
  rfl

/-- Faithfulness is unchanged when a linear action is regarded as a
representation. -/
theorem linearActionRepresentation_injective
    (ρ : P →* (V ≃ₗ[k] V))
    (hρ : Function.Injective ρ) :
    Function.Injective (linearActionRepresentation ρ) := by
  intro g h hgh
  apply hρ
  exact LinearEquiv.toLinearMap_injective hgh

/-- A linear automorphism, regarded as a unit of the endomorphism
algebra. -/
def linearEquivUnit :
    (V ≃ₗ[k] V) ≃* (Module.End k V)ˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).symm

/-- Unit-valued form of a linear group action. -/
def linearActionUnit
    (ρ : P →* (V ≃ₗ[k] V)) :
    P →* (Module.End k V)ˣ :=
  (linearEquivUnit (k := k) (V := V)).toMonoidHom.comp ρ

@[simp]
theorem generalLinearEquiv_linearActionUnit
    (ρ : P →* (V ≃ₗ[k] V)) (g : P) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv k V
        (linearActionUnit ρ g) =
      ρ g :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).apply_symm_apply
    (ρ g)

/-- The conjugation action homomorphism on the endomorphism algebra. -/
def endomorphismConjugationHom
    (ρ : P →* (V ≃ₗ[k] V)) :
    P →* ConjAct (Module.End k V)ˣ :=
  ConjAct.toConjAct.toMonoidHom.comp (linearActionUnit ρ)

/-- The induced semiring action on the endomorphism algebra. -/
abbrev endomorphismConjugationMulSemiringAction
    (ρ : P →* (V ≃ₗ[k] V)) :
    MulSemiringAction P (Module.End k V) :=
  MulSemiringAction.compHom (Module.End k V)
    (endomorphismConjugationHom ρ)

section Conjugation

variable (ρ : P →* (V ≃ₗ[k] V))

@[simp]
theorem endomorphismConjugation_smul
    (g : P) (f : Module.End k V) :
    letI :=
      endomorphismConjugationMulSemiringAction ρ
    g • f =
      (linearActionUnit ρ g : Module.End k V) * f *
        (↑((linearActionUnit ρ g)⁻¹) : Module.End k V) := by
  letI :=
    endomorphismConjugationMulSemiringAction ρ
  rfl

/-- Conjugation by linear automorphisms commutes with the scalar action on
the endomorphism algebra. -/
theorem endomorphismConjugation_smulCommClass :
    letI :=
      endomorphismConjugationMulSemiringAction ρ
    SMulCommClass P k (Module.End k V) := by
  letI :=
    endomorphismConjugationMulSemiringAction ρ
  exact
    { smul_comm := fun g c f ↦ by
        ext v
        simp only [endomorphismConjugation_smul,
          Module.End.mul_apply, LinearMap.smul_apply]
        rw [map_smul] }

/-- The canonical interior action implemented by a linear
representation. -/
def interiorActionOfLinearAction :
    letI :=
      endomorphismConjugationMulSemiringAction ρ
    InteriorAction (P := P) (A := Module.End k V) := by
  letI :=
    endomorphismConjugationMulSemiringAction ρ
  exact
    { unit := linearActionUnit ρ
      smul_eq := fun _ _ ↦ rfl }

end Conjugation
end Representation
