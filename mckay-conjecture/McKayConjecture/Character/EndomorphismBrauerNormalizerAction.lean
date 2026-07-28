/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerQuotientEquivariance
import McKayConjecture.Character.EndomorphismBrauerHom
import McKayConjecture.Character.EndomorphismNormalizer
import McKayConjecture.Character.InteriorFaithfulNormalizerAction

/-!
# The normalizer action on a module Brauer quotient

For a faithful linear representation, a unit normalizing the interior
image induces compatible automorphisms of the acting group and the
representation space.  Equivariance of the module Brauer construction
then gives an honest linear action of the full interior normalizer on
the module Brauer quotient.
-/

noncomputable section

namespace Representation

variable {k P V : Type}
variable [Field k] [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]

/-- Compatible automorphism of a faithful representation induced by an
interior normalizer unit. -/
def normalizerCompatibleAutomorphism
    (ρ : Representation k P V)
    (hρ : Function.Injective ρ) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    ∀ _s : (representationInteriorAction ρ).unitNormalizer,
      CompatibleAutomorphism ρ := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  let I := representationInteriorAction ρ
  let hI : Function.Injective I.unit :=
    representationInteriorAction_unit_injective ρ hρ
  intro s
  exact
    { groupEquiv := I.normalizerMulAut hI s
      linearEquiv := I.normalizerLinearEquiv s
      compatible := fun g v ↦ by
        have hunit :=
          I.unit_normalizerMulAut hI s g
        have hcommU :
            (s : (Module.End k V)ˣ) * I.unit g =
              I.unit (I.normalizerMulAut hI s g) *
                (s : (Module.End k V)ˣ) := by
          calc
            (s : (Module.End k V)ˣ) * I.unit g =
                ((s : (Module.End k V)ˣ) * I.unit g *
                  (s : (Module.End k V)ˣ)⁻¹) *
                    (s : (Module.End k V)ˣ) := by
                      simp [mul_assoc]
            _ = I.unit (I.normalizerMulAut hI s g) *
                  (s : (Module.End k V)ˣ) := by
                    rw [← hunit]
        have hcomm :
            ((s : (Module.End k V)ˣ) :
                Module.End k V) * ρ g =
              ρ (I.normalizerMulAut hI s g) *
                ((s : (Module.End k V)ˣ) :
                  Module.End k V) := by
          change
            ((s : (Module.End k V)ˣ) :
                Module.End k V) *
                (I.unit g : Module.End k V) =
              (I.unit (I.normalizerMulAut hI s g) :
                  Module.End k V) *
                ((s : (Module.End k V)ˣ) :
                  Module.End k V)
          exact congrArg Units.val hcommU
        exact LinearMap.congr_fun hcomm v }

/-- The full interior normalizer acts linearly on the module Brauer
quotient. -/
def normalizerBrauerQuotientLinearAction
    (ρ : Representation k P V)
    (hρ : Function.Injective ρ) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    (representationInteriorAction ρ).unitNormalizer →*
      (BrauerQuotient ρ ≃ₗ[k] BrauerQuotient ρ) := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  let I := representationInteriorAction ρ
  exact
    { toFun := fun s ↦
        (normalizerCompatibleAutomorphism ρ hρ s).brauerQuotientEquiv
      map_one' := by
        apply LinearEquiv.ext
        intro z
        obtain ⟨x, rfl⟩ :=
          brauerProjection_surjective ρ z
        rfl
      map_mul' := fun s t ↦ by
        apply LinearEquiv.ext
        intro z
        obtain ⟨x, rfl⟩ :=
          brauerProjection_surjective ρ z
        rfl }

@[simp]
theorem normalizerBrauerQuotientLinearAction_brauerProjection
    (ρ : Representation k P V)
    (hρ : Function.Injective ρ) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    ∀
      (s : (representationInteriorAction ρ).unitNormalizer)
      (x : invariants ρ),
      normalizerBrauerQuotientLinearAction ρ hρ s
          (brauerProjection ρ x) =
        brauerProjection ρ
          ((normalizerCompatibleAutomorphism
            ρ hρ s).invariantsEquiv x) := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  intro s x
  rfl

end Representation
