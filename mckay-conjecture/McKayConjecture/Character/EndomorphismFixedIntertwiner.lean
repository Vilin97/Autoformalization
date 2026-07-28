/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismBrauerAction
import McKayConjecture.Character.EndomorphismInteriorAction

/-!
# Fixed endomorphisms and self-intertwiners

For a group representation, the fixed algebra of the conjugation
action on the endomorphism algebra is canonically the algebra of
self-intertwining maps.  This file records that equivalence while
keeping the conjugation-action instances local to the construction.
-/

noncomputable section

namespace Representation

variable {k P V : Type}
variable [Field k] [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]

/-- Regard a group representation by linear maps as a linear action by
automorphisms. -/
def representationLinearAction
    (ρ : Representation k P V) :
    P →* (V ≃ₗ[k] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom.comp
    ρ.toHomUnits

omit [Fintype P] in
@[simp]
theorem representationLinearAction_toLinearMap
    (ρ : Representation k P V)
    (g : P) :
    (representationLinearAction ρ g : Module.End k V) =
      ρ g :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap
    (ρ.toHomUnits g)

omit [Fintype P] in
/-- Forgetting and then reconstructing the inverses of a linear action
recovers the original action. -/
@[simp]
theorem representationLinearAction_linearActionRepresentation
    (σ : P →* (V ≃ₗ[k] V)) :
    representationLinearAction
        (linearActionRepresentation σ) =
      σ := by
  apply MonoidHom.ext
  intro g
  apply LinearEquiv.toLinearMap_injective
  simp

omit [Fintype P] in
@[simp]
theorem linearActionUnit_representationLinearAction
    (ρ : Representation k P V)
    (g : P) :
    (linearActionUnit (representationLinearAction ρ) g :
      Module.End k V) =
        ρ g := by
  have h :=
    generalLinearEquiv_linearActionUnit
      (representationLinearAction ρ) g
  exact congrArg LinearEquiv.toLinearMap h

omit [Fintype P] in
/-- A faithful representation remains faithful when regarded as a
linear action. -/
theorem representationLinearAction_injective
    (ρ : Representation k P V)
    (hρ : Function.Injective ρ) :
    Function.Injective (representationLinearAction ρ) := by
  intro g h hgh
  apply hρ
  have hlinear :=
    congrArg (fun e : V ≃ₗ[k] V ↦
      (e : Module.End k V)) hgh
  simpa using hlinear

/-- The interior action on the endomorphism algebra associated to a
group representation. -/
def representationInteriorAction
    (ρ : Representation k P V) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    InteriorAction (P := P) (A := Module.End k V) := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  exact interiorActionOfLinearAction
    (representationLinearAction ρ)

omit [Fintype P] in
/-- Faithfulness of a representation implies faithfulness of its
implementing unit homomorphism. -/
theorem representationInteriorAction_unit_injective
    (ρ : Representation k P V)
    (hρ : Function.Injective ρ) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    Function.Injective
      (representationInteriorAction ρ).unit := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  intro g h hgh
  apply hρ
  have hval := congrArg Units.val hgh
  change
    (linearActionUnit
        (representationLinearAction ρ) g :
      Module.End k V) =
      (linearActionUnit
        (representationLinearAction ρ) h :
      Module.End k V) at hval
  simpa using hval

/-- The conjugation-fixed endomorphism algebra is canonically the
self-intertwiner algebra. -/
def fixedEndomorphismIntertwinerAlgEquiv
    (ρ : Representation k P V) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    fixedSubalgebra
        (k := k) (P := P) (A := Module.End k V) ≃ₐ[k]
      ρ.IntertwiningMap ρ := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  exact
    { toFun := fun c ↦
        { toLinearMap := c
          isIntertwining' := fun g ↦ by
            apply LinearMap.ext
            intro v
            have hc := c.property g
            rw [endomorphismConjugation_smul] at hc
            have hcomm :
                (linearActionUnit
                    (representationLinearAction ρ) g :
                  Module.End k V) * (c : Module.End k V) =
                  (c : Module.End k V) *
                    (linearActionUnit
                      (representationLinearAction ρ) g :
                        Module.End k V) := by
              have hm := congrArg
                (fun f : Module.End k V ↦
                  f *
                    (linearActionUnit
                      (representationLinearAction ρ) g :
                        Module.End k V))
                hc
              simpa only [mul_assoc, Units.inv_mul, mul_one]
                using hm
            exact LinearMap.congr_fun hcomm.symm v }
      invFun := fun c ↦
        ⟨c.toLinearMap, fun g ↦ by
          rw [endomorphismConjugation_smul]
          apply LinearMap.ext
          intro v
          change
            ρ g (c (ρ g⁻¹ v)) = c v
          rw [IntertwiningMap.isIntertwining
            ρ ρ c g⁻¹ v]
          simp⟩
      left_inv := fun c ↦ by
        apply Subtype.ext
        rfl
      right_inv := fun c ↦ by
        apply IntertwiningMap.ext
        rfl
      map_mul' := fun c d ↦ by
        apply IntertwiningMap.ext
        rfl
      map_add' := fun c d ↦ by
        apply IntertwiningMap.ext
        rfl
      commutes' := fun r ↦ by
        apply IntertwiningMap.ext
        rfl }

end Representation
