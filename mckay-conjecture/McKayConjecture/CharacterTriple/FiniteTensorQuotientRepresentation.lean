/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralQuotientProductClassification
import McKayConjecture.CharacterTriple.FiniteProjectiveTensor

/-!
# Tensor representations descended through a product quotient

An ordinary tensor product representation of a finite dependent product
descends through a surjective quotient whenever the corresponding external
tensor character is trivial on the kernel.  Its descended character is the
irreducible character supplied by the quotient-product classification.

The construction is representation-level: kernel triviality of the chosen
coordinate realizations is recovered from their character and simplicity,
so no compatibility between arbitrary realization choices is assumed.
-/

noncomputable section

open scoped BigOperators TensorProduct
open CategoryTheory

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {ι : Type} [Fintype ι]
variable {X : ι → Type} [∀ i, Group (X i)] [∀ i, Finite (X i)]
variable {H : Type} [Group H]
variable {V : ι → Type}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable [∀ i, Module.Finite ℂ (V i)] [∀ i, Nontrivial (V i)]

local instance piTensorModuleFiniteInstance :
    Module.Finite ℂ (⨂[ℂ] i, V i) :=
  piTensorModuleFinite

/-- The finite-dimensional representation associated to the coordinatewise
action on the dependent tensor product. -/
abbrev piTensorFDRep
    (D : ∀ i, X i →* (V i ≃ₗ[ℂ] V i)) :
    FDRep ℂ (∀ i, X i) :=
  FDRep.of (linearRepresentationOfAction (piTensorLinearAction D))

/-- The character of a tensor of coordinate realizations is the finite
external tensor of their characters. -/
theorem piTensorFDRep_character
    (D : ∀ i, X i →* (V i ≃ₗ[ℂ] V i))
    (χ : ∀ i, IrreducibleCharacter (X i))
    (hcharacter : ∀ i,
      (FDRep.of (linearRepresentationOfAction (D i))).character =
        (χ i).values) :
    (piTensorFDRep D).character =
      (IrreducibleCharacter.finiteExternalTensor χ).values := by
  funext x
  rw [IrreducibleCharacter.finiteExternalTensor_values]
  change
    LinearMap.trace ℂ (⨂[ℂ] i, V i)
        (piTensorLinearAction D x) =
      _
  exact
    (trace_piTensorLinearAction D x).trans <|
      Finset.prod_congr rfl fun i _ ↦ congrFun (hcharacter i) (x i)

/-- A tensor of coordinate realizations of irreducible characters is
irreducible. -/
theorem piTensorFDRep_simple
    (D : ∀ i, X i →* (V i ≃ₗ[ℂ] V i))
    (χ : ∀ i, IrreducibleCharacter (X i))
    (hcharacter : ∀ i,
      (FDRep.of (linearRepresentationOfAction (D i))).character =
        (χ i).values) :
    Simple (piTensorFDRep D) := by
  letI : Fintype (∀ i, X i) := Fintype.ofFinite _
  rw [FDRep.simple_iff_char_is_norm_one]
  have hsimple :
      Simple (IrreducibleCharacter.finiteExternalTensor χ).realization :=
    inferInstance
  have hnorm :=
    (FDRep.simple_iff_char_is_norm_one
      (IrreducibleCharacter.finiteExternalTensor χ).realization).mp hsimple
  rw [piTensorFDRep_character D χ hcharacter,
    ← (IrreducibleCharacter.finiteExternalTensor χ).realization_character]
  exact hnorm

/-- Kernel compatibility of the external tensor character forces the chosen
tensor realization to act trivially on the kernel. -/
theorem piTensorLinearAction_ker_le
    (f : (∀ i, X i) →* H)
    (D : ∀ i, X i →* (V i ≃ₗ[ℂ] V i))
    (χ : IrreducibleCharacter.KernelCompatibleCharacterFamily X f)
    (hcharacter : ∀ i,
      (FDRep.of (linearRepresentationOfAction (D i))).character =
        (χ.1 i).values) :
    f.ker ≤ (piTensorLinearAction D).ker := by
  let hsimple : Simple (piTensorFDRep D) :=
    piTensorFDRep_simple D χ.1 hcharacter
  letI : Simple (piTensorFDRep D) := hsimple
  have htrivial :
      FDRep.IsTrivialOn (piTensorFDRep D) f.ker :=
    (IrreducibleCharacter.trivialOn_iff_of_character_eq
      f.ker
      (IrreducibleCharacter.finiteExternalTensor χ.1)
      (piTensorFDRep D)
      (piTensorFDRep_character D χ.1 hcharacter)).mp χ.2
  intro x hx
  rw [MonoidHom.mem_ker]
  apply LinearEquiv.toLinearMap_injective
  exact htrivial ⟨x, hx⟩

/-- Descend the tensor action through a surjective product homomorphism. -/
def piTensorQuotientLinearAction
    (f : (∀ i, X i) →* H)
    (hf : Function.Surjective f)
    (D : ∀ i, X i →* (V i ≃ₗ[ℂ] V i))
    (χ : IrreducibleCharacter.KernelCompatibleCharacterFamily X f)
    (hcharacter : ∀ i,
      (FDRep.of (linearRepresentationOfAction (D i))).character =
        (χ.1 i).values) :
    H →* ((⨂[ℂ] i, V i) ≃ₗ[ℂ] (⨂[ℂ] i, V i)) :=
  f.liftOfSurjective hf
    ⟨piTensorLinearAction D,
      piTensorLinearAction_ker_le f D χ hcharacter⟩

@[simp]
theorem piTensorQuotientLinearAction_product
    (f : (∀ i, X i) →* H)
    (hf : Function.Surjective f)
    (D : ∀ i, X i →* (V i ≃ₗ[ℂ] V i))
    (χ : IrreducibleCharacter.KernelCompatibleCharacterFamily X f)
    (hcharacter : ∀ i,
      (FDRep.of (linearRepresentationOfAction (D i))).character =
        (χ.1 i).values)
    (x : ∀ i, X i) :
    piTensorQuotientLinearAction f hf D χ hcharacter (f x) =
      piTensorLinearAction D x :=
  f.liftOfRightInverse_comp_apply
    (Function.surjInv hf)
    (Function.rightInverse_surjInv hf)
    ⟨piTensorLinearAction D,
      piTensorLinearAction_ker_le f D χ hcharacter⟩
    x

/-- The finite-dimensional representation furnished by the descended tensor
action. -/
abbrev piTensorQuotientFDRep
    (f : (∀ i, X i) →* H)
    (hf : Function.Surjective f)
    (D : ∀ i, X i →* (V i ≃ₗ[ℂ] V i))
    (χ : IrreducibleCharacter.KernelCompatibleCharacterFamily X f)
    (hcharacter : ∀ i,
      (FDRep.of (linearRepresentationOfAction (D i))).character =
        (χ.1 i).values) :
    FDRep ℂ H :=
  FDRep.of <|
    linearRepresentationOfAction <|
      piTensorQuotientLinearAction f hf D χ hcharacter

/-- The descended tensor representation affords exactly the irreducible
character classified by the kernel-compatible coordinate family. -/
theorem piTensorQuotientFDRep_character
    (f : (∀ i, X i) →* H)
    (hf : Function.Surjective f)
    (D : ∀ i, X i →* (V i ≃ₗ[ℂ] V i))
    (χ : IrreducibleCharacter.KernelCompatibleCharacterFamily X f)
    (hcharacter : ∀ i,
      (FDRep.of (linearRepresentationOfAction (D i))).character =
        (χ.1 i).values) :
    (piTensorQuotientFDRep f hf D χ hcharacter).character =
      (IrreducibleCharacter.quotientProductCharacterEquiv
        X f hf χ).values := by
  funext y
  obtain ⟨x, rfl⟩ := hf y
  rw [IrreducibleCharacter.quotientProductCharacterEquiv_values_apply]
  change
    LinearMap.trace ℂ (⨂[ℂ] i, V i)
        (piTensorQuotientLinearAction f hf D χ hcharacter (f x)) =
      _
  rw [piTensorQuotientLinearAction_product,
    trace_piTensorLinearAction]
  exact
    Finset.prod_congr rfl fun i _ ↦ congrFun (hcharacter i) (x i)

/-- The descended tensor representation is irreducible. -/
theorem piTensorQuotientFDRep_simple
    (f : (∀ i, X i) →* H)
    (hf : Function.Surjective f)
    (D : ∀ i, X i →* (V i ≃ₗ[ℂ] V i))
    (χ : IrreducibleCharacter.KernelCompatibleCharacterFamily X f)
    (hcharacter : ∀ i,
      (FDRep.of (linearRepresentationOfAction (D i))).character =
        (χ.1 i).values) :
    Simple (piTensorQuotientFDRep f hf D χ hcharacter) := by
  letI : Finite H := Finite.of_surjective f hf
  letI : Fintype H := Fintype.ofFinite H
  rw [FDRep.simple_iff_char_is_norm_one]
  have hsimple :
      Simple
        (IrreducibleCharacter.quotientProductCharacterEquiv
          X f hf χ).realization :=
    inferInstance
  have hnorm :=
    (FDRep.simple_iff_char_is_norm_one
      (IrreducibleCharacter.quotientProductCharacterEquiv
        X f hf χ).realization).mp hsimple
  rw [piTensorQuotientFDRep_character f hf D χ hcharacter,
    ← (IrreducibleCharacter.quotientProductCharacterEquiv
      X f hf χ).realization_character]
  exact hnorm

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
