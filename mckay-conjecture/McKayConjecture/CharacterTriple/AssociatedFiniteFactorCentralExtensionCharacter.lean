/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorNormalizerRestriction
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionCharacter
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionProjectiveExtraction

/-!
# The honest character attached to an associated finite factor set

An associated projective representation is already irreducible: any
ambient-stable subspace is stable under its irreducible normal-subgroup
restriction.  Hence every fixed association-preserving finite-factor
normalization gives an honest irreducible character of the concrete
factor-set extension of the ambient group.

The base-lift values of this character are exactly the traces of the chosen
projective operators, and the coefficient subgroup acts by its defining
root-of-unity character.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

variable {A : Type} [Group A] [Finite A]
variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- An associated projective representation is irreducible because its
restriction to the distinguished normal subgroup is irreducible. -/
theorem projective_isIrreducible
    (R : AssociatedProjectiveRepresentation T V P) :
    P.IsIrreducible := by
  let rhoN : Representation ℂ T.normalSubgroup V :=
    linearRepresentationOfAction R.restriction
  have hrhoN : rhoN.IsIrreducible :=
    CliffordRestriction.isIrreducible_of_simple R.fdRestriction
  refine ⟨inferInstance, ?_⟩
  intro U hU
  have hInvariant :
      ∀ (x : T.normalSubgroup) ⦃v : V⦄,
        v ∈ U → rhoN x v ∈ U := by
    intro x v hv
    change R.restriction x v ∈ U
    rw [R.restriction_apply]
    exact hU (x : A) hv
  let W : Subrepresentation rhoN :=
    { toSubmodule := U
      apply_mem_toSubmodule := hInvariant }
  letI : rhoN.IsIrreducible := hrhoN
  obtain hW | hW := IsSimpleOrder.eq_bot_or_eq_top W
  · left
    exact congrArg Subrepresentation.toSubmodule hW
  · right
    exact congrArg Subrepresentation.toSubmodule hW

namespace AssociatedFiniteFactorNormalization

variable (R : AssociatedProjectiveRepresentation T V P)

/-- The concrete factor-set extension of the ambient group attached to a
fixed association-preserving finite normalization. -/
abbrev AmbientFactorCentralExtensionGroup
    (F : AssociatedFiniteFactorNormalization R) :=
  FactorSet.CentralExtensionGroup
    F.factorSet (F.factorSet_isNormalized R)

/-- The honest representation obtained by linearizing the fixed associated
projective lift on its ambient factor-set extension. -/
def ambientFactorCentralExtensionRepresentation
    (F : AssociatedFiniteFactorNormalization R) :
    Representation ℂ (F.AmbientFactorCentralExtensionGroup R) V :=
  F.projective.centralExtensionRepresentation
    F.factorSet (F.factorSet_isNormalized R)
    (rootsOfUnity (associatedFactorExponent T V) ℂ).subtype
    F.factorSet_coe

/-- The ambient factor-extension representation is irreducible. -/
theorem ambientFactorCentralExtensionRepresentation_isIrreducible
    (F : AssociatedFiniteFactorNormalization R) :
    Representation.IsIrreducible
      (F.ambientFactorCentralExtensionRepresentation R) :=
  F.projective.centralExtensionRepresentation_isIrreducible
    F.factorSet (F.factorSet_isNormalized R)
    (rootsOfUnity (associatedFactorExponent T V) ℂ).subtype
    F.factorSet_coe
    F.associated.projective_isIrreducible

/-- The finite-dimensional representation on the ambient factor
extension. -/
abbrev ambientFactorCentralExtensionFDRep
    (F : AssociatedFiniteFactorNormalization R) :
    FDRep ℂ (F.AmbientFactorCentralExtensionGroup R) :=
  FDRep.of (F.ambientFactorCentralExtensionRepresentation R)

/-- The ambient factor-extension representation is categorically simple. -/
theorem ambientFactorCentralExtensionFDRep_simple
    (F : AssociatedFiniteFactorNormalization R) :
    Simple (F.ambientFactorCentralExtensionFDRep R) := by
  letI :
      Representation.IsIrreducible
        (F.ambientFactorCentralExtensionRepresentation R) :=
    F.ambientFactorCentralExtensionRepresentation_isIrreducible R
  exact
    FDRep.simple_of_representation_isIrreducible
      (F.ambientFactorCentralExtensionRepresentation R)

/-- The honest irreducible character canonically afforded by the fixed
associated finite-factor lift. -/
def ambientFactorCentralExtensionCharacter
    (F : AssociatedFiniteFactorNormalization R) :
    IrreducibleCharacter
      (F.AmbientFactorCentralExtensionGroup R) := by
  letI : Simple (F.ambientFactorCentralExtensionFDRep R) :=
    F.ambientFactorCentralExtensionFDRep_simple R
  exact
    IrreducibleCharacter.ofSimple
      (F.ambientFactorCentralExtensionFDRep R)

@[simp]
theorem ambientFactorCentralExtensionCharacter_degree
    (F : AssociatedFiniteFactorNormalization R) :
    (F.ambientFactorCentralExtensionCharacter R).degree =
      Module.finrank ℂ V := by
  letI : Simple (F.ambientFactorCentralExtensionFDRep R) :=
    F.ambientFactorCentralExtensionFDRep_simple R
  rfl

/-- At a canonical base lift, the honest extension character is the trace
of the chosen projective operator. -/
@[simp]
theorem ambientFactorCentralExtensionCharacter_values_baseLift
    (F : AssociatedFiniteFactorNormalization R)
    (a : A) :
    (F.ambientFactorCentralExtensionCharacter R).values
        (FactorSet.CentralExtensionGroup.baseLift
          F.factorSet (F.factorSet_isNormalized R) a) =
      LinearMap.trace ℂ V
        (F.projective.operator a : V →ₗ[ℂ] V) := by
  letI : Simple (F.ambientFactorCentralExtensionFDRep R) :=
    F.ambientFactorCentralExtensionFDRep_simple R
  change
    LinearMap.trace ℂ V
        (F.ambientFactorCentralExtensionRepresentation R
          (FactorSet.CentralExtensionGroup.baseLift
            F.factorSet (F.factorSet_isNormalized R) a)) =
      LinearMap.trace ℂ V
        (F.projective.operator a : V →ₗ[ℂ] V)
  congr 1
  ext v
  rw [ambientFactorCentralExtensionRepresentation,
    F.projective.centralExtensionRepresentation_apply_vector
      F.factorSet (F.factorSet_isNormalized R)
      (rootsOfUnity (associatedFactorExponent T V) ℂ).subtype
      F.factorSet_coe]
  simp [FactorSet.CentralExtensionGroup.baseLift]

/-- The coefficient subgroup acts by its defining root-of-unity scalar. -/
theorem ambientFactorCentralExtensionCharacter_hasCoefficientCharacter
    (F : AssociatedFiniteFactorNormalization R) :
    FactorSet.CentralExtensionGroup.HasCoefficientCharacter
      F.factorSet (F.factorSet_isNormalized R)
      (rootsOfUnity (associatedFactorExponent T V) ℂ).subtype
      (F.ambientFactorCentralExtensionCharacter R) := by
  intro c
  letI : Simple (F.ambientFactorCentralExtensionFDRep R) :=
    F.ambientFactorCentralExtensionFDRep_simple R
  change
    LinearMap.trace ℂ V
      (F.ambientFactorCentralExtensionRepresentation R
          (FactorSet.CentralExtensionGroup.coefficientEmbedding
            F.factorSet (F.factorSet_isNormalized R) c)) =
      ((c : ℂˣ) : ℂ) * (Module.finrank ℂ V : ℂ)
  rw [ambientFactorCentralExtensionRepresentation,
    F.projective.centralExtensionRepresentation_apply_coefficientEmbedding
      F.factorSet (F.factorSet_isNormalized R)
      (rootsOfUnity (associatedFactorExponent T V) ℂ).subtype
      F.factorSet_coe]
  have hscalar :
      ((scalarLinearEquiv ℂ V
          ((rootsOfUnity
            (associatedFactorExponent T V) ℂ).subtype c) :
          V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) =
        ((c : ℂˣ) : ℂ) •
          (LinearMap.id : Module.End ℂ V) := by
    ext v
    simp
  rw [hscalar, map_smul, LinearMap.trace_id]
  rfl

end AssociatedFiniteFactorNormalization
end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
