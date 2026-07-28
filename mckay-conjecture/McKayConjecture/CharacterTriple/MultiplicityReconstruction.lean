/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordEquivalence
import McKayConjecture.CharacterTriple.MultiplicityProjective

/-!
# Reconstruction from the projective multiplicity space

For an irreducible ambient representation lying over the invariant normal
character in a character triple, Clifford theory says that its restriction
is isotypic.  Schur's lemma then computes the dimension of its multiplicity
space.  Consequently the evaluation map from the associated projective
representation tensored with that multiplicity space is an isomorphism, not
merely a surjection.

This file supplies the exact dimension calculation and removes the
conditional finrank hypothesis from the reconstruction API in
`MultiplicityProjective`.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra TensorProduct

universe u

namespace McKayConjecture
namespace CharacterTriple
namespace MultiplicityProjective

/-- Intertwiners into an ordinary componentwise function representation are
families of intertwiners into its components. -/
def intertwiningMapToFunctionEquiv
    {L U : Type} [Monoid L]
    [AddCommGroup U] [Module ℂ U]
    (τ : Representation ℂ L U)
    {ι : Type} {M : ι → Type}
    [(i : ι) → AddCommGroup (M i)]
    [(i : ι) → Module ℂ (M i)]
    (ρ : (i : ι) → Representation ℂ L (M i)) :
    τ.IntertwiningMap
        (CliffordEquivalence.functionRepresentation ρ) ≃ₗ[ℂ]
      ((i : ι) → τ.IntertwiningMap (ρ i)) where
  toFun f i :=
    { toLinearMap := LinearMap.proj i ∘ₗ f.toLinearMap
      isIntertwining' := fun g => by
        ext x
        have hf := LinearMap.ext_iff.mp (f.isIntertwining' g) x
        exact congrArg (fun z => z i) hf }
  invFun F :=
    { toLinearMap := LinearMap.pi fun i => (F i).toLinearMap
      isIntertwining' := fun g => by
        ext x i
        exact LinearMap.ext_iff.mp ((F i).isIntertwining' g) x }
  left_inv f := by ext x i; rfl
  right_inv F := by funext i; ext x; rfl
  map_add' f g := by funext i; ext x; rfl
  map_smul' c f := by funext i; ext x; rfl

variable {A₀ V₀ : Type} [Finite A₀] [Group A₀]
variable [AddCommGroup V₀] [Module ℂ V₀]
  [Module.Finite ℂ V₀] [Nontrivial V₀]
variable {T₀ : CharacterTriple A₀}
variable {P₀ : ProjectiveRepresentation ℂ A₀ V₀}

/-- The dimension of an irreducible ambient representation lying over the
triple character is the product of the associated-space dimension and its
multiplicity-space dimension. -/
theorem finrank_space_mul_finrank_eq
    (R : AssociatedProjectiveRepresentation T₀ V₀ P₀)
    (E : FDRep ℂ A₀) [Simple E]
    (hE : ∃ f : T₀.character.realization ⟶
      FDRep.res T₀.normalSubgroup.subtype E, f ≠ 0) :
    Module.finrank ℂ (Space R E.ρ) * Module.finrank ℂ V₀ =
      Module.finrank ℂ E := by
  obtain ⟨f, hf⟩ := hE
  letI : Representation.IsIrreducible E.ρ :=
    CliffordRestriction.isIrreducible_of_simple E
  letI : Representation.IsIrreducible T₀.character.realization.ρ :=
    CliffordRestriction.isIrreducible_of_simple
      T₀.character.realization
  have hinvariant :
      ∀ a : A₀,
        IrreducibleCharacter.conjBy T₀.normalSubgroup a
            T₀.character =
          T₀.character := by
    intro a
    apply IrreducibleCharacter.ext
    funext x
    rw [IrreducibleCharacter.conjBy_values]
    rw [show (MulAut.conjNormal a).symm x =
        MulAut.conjNormal a⁻¹ x by
      apply Subtype.ext
      simp]
    exact T₀.invariant_conjNormal a⁻¹ x
  have hisotypic :=
    CliffordEquivalence.restriction_isIsotypic_realization_of_invariant
      T₀.normalSubgroup T₀.character E f hf hinvariant
  letI :
      IsSemisimpleModule ℂ[T₀.normalSubgroup]
        (Representation.asModule
          (FDRep.res T₀.normalSubgroup.subtype E).ρ) :=
    CliffordRestriction.isSemisimpleModule_resSubgroup
      E T₀.normalSubgroup
  letI :
      Module.Finite ℂ[T₀.normalSubgroup]
        (Representation.asModule
          (FDRep.res T₀.normalSubgroup.subtype E).ρ) :=
    Module.Finite.of_restrictScalars_finite
      ℂ ℂ[T₀.normalSubgroup]
      (Representation.asModule
        (FDRep.res T₀.normalSubgroup.subtype E).ρ)
  obtain ⟨n, ⟨e⟩⟩ := hisotypic.linearEquiv_fun
  let sourceRepresentation :=
    (FDRep.res T₀.normalSubgroup.subtype E).ρ
  let targetRepresentation :=
    CliffordEquivalence.functionRepresentation
      (fun _ : Fin n ↦ T₀.character.realization.ρ)
  let sourceCarrierToModule :
      FDRep.res T₀.normalSubgroup.subtype E ≃ₗ[ℂ]
        Representation.asModule sourceRepresentation :=
    (Representation.asModuleEquiv sourceRepresentation).symm
  let moduleToTargetCarrier :
      (Fin n →
          Representation.asModule
            T₀.character.realization.ρ) ≃ₗ[ℂ]
        (Fin n → T₀.character.realization) :=
    LinearEquiv.piCongrRight
      (fun _ : Fin n ↦
        Representation.asModuleEquiv
          T₀.character.realization.ρ)
  let carrierEquiv :
      FDRep.res T₀.normalSubgroup.subtype E ≃ₗ[ℂ]
        (Fin n → T₀.character.realization) :=
    sourceCarrierToModule.trans
      ((e.restrictScalars ℂ).trans moduleToTargetCarrier)
  let repEquiv :
      Representation.Equiv
        (FDRep.res T₀.normalSubgroup.subtype E).ρ
        (CliffordEquivalence.functionRepresentation
          (fun _ : Fin n ↦ T₀.character.realization.ρ)) := by
    apply Representation.Equiv.mk carrierEquiv
    intro g
    ext v i
    let u :
        Representation.asModule sourceRepresentation :=
      (Representation.asModuleEquiv
        sourceRepresentation).symm v
    have he :=
      e.map_smul
        (MonoidAlgebra.of ℂ T₀.normalSubgroup g) u
    have hsource :
        (MonoidAlgebra.of ℂ T₀.normalSubgroup g) • u =
          (Representation.asModuleEquiv
            sourceRepresentation).symm
              (sourceRepresentation g v) := by
      simpa [u] using
        (Representation.asModuleEquiv_symm_map_rho
          sourceRepresentation g v).symm
    have hei₀ := congrArg (fun z ↦ z i) he
    rw [hsource] at hei₀
    change
      Representation.asModuleEquiv
          T₀.character.realization.ρ
          (e ((Representation.asModuleEquiv
            sourceRepresentation).symm
              (sourceRepresentation g v)) i) =
        T₀.character.realization.ρ g
          (Representation.asModuleEquiv
            T₀.character.realization.ρ
            (e ((Representation.asModuleEquiv
              sourceRepresentation).symm v) i))
    calc
      _ =
          Representation.asModuleEquiv
            T₀.character.realization.ρ
            (((MonoidAlgebra.of ℂ
              T₀.normalSubgroup g) • e u) i) :=
        congrArg
          (Representation.asModuleEquiv
            T₀.character.realization.ρ) hei₀
      _ =
          T₀.character.realization.ρ g
            (Representation.asModuleEquiv
              T₀.character.realization.ρ
              (e u i)) := by
        change
          Representation.asModuleEquiv
              T₀.character.realization.ρ
              ((MonoidAlgebra.of ℂ
                T₀.normalSubgroup g) • e u i) =
            _
        rw [Representation.asModuleEquiv_map_smul,
          Representation.asAlgebraHom_of]
      _ = _ := by rfl
  let homToFunctions :=
    Mackey.postcomposeEquiv
      T₀.character.realization.ρ repEquiv
  let homComponents :=
    intertwiningMapToFunctionEquiv
      T₀.character.realization.ρ
      (fun _ : Fin n ↦ T₀.character.realization.ρ)
  have hhom :
      Module.finrank ℂ
          (Representation.IntertwiningMap
            T₀.character.realization.ρ
            (FDRep.res T₀.normalSubgroup.subtype E).ρ) =
        n := by
    calc
      _ = Module.finrank ℂ
          (Representation.IntertwiningMap
            T₀.character.realization.ρ
            (CliffordEquivalence.functionRepresentation
              (fun _ : Fin n ↦
                T₀.character.realization.ρ))) :=
        homToFunctions.finrank_eq
      _ = Module.finrank ℂ
          (Fin n →
            Representation.IntertwiningMap
              T₀.character.realization.ρ
              T₀.character.realization.ρ) :=
        homComponents.finrank_eq
      _ = ∑ _ : Fin n,
          Module.finrank ℂ
            (Representation.IntertwiningMap
              T₀.character.realization.ρ
              T₀.character.realization.ρ) :=
        Module.finrank_pi_fintype ℂ
      _ = n := by simp
  let categoricalToIntertwining :
      (T₀.character.realization ⟶
          FDRep.res T₀.normalSubgroup.subtype E) ≃ₗ[ℂ]
        Representation.IntertwiningMap
          T₀.character.realization.ρ
          (FDRep.res T₀.normalSubgroup.subtype E).ρ :=
    (FDRep.forget₂HomLinearEquiv
      T₀.character.realization
      (FDRep.res T₀.normalSubgroup.subtype E)).symm |>.trans
        (Rep.homLinearEquiv _ _)
  have hspace : Module.finrank ℂ (Space R E.ρ) = n := by
    calc
      _ = Module.finrank ℂ
          (T₀.character.realization ⟶
            FDRep.res T₀.normalSubgroup.subtype E) :=
        (characterHomEquivSpace R E).finrank_eq.symm
      _ = Module.finrank ℂ
          (Representation.IntertwiningMap
            T₀.character.realization.ρ
            (FDRep.res T₀.normalSubgroup.subtype E).ρ) :=
        categoricalToIntertwining.finrank_eq
      _ = n := hhom
  have hV :
      Module.finrank ℂ V₀ =
        Module.finrank ℂ T₀.character.realization :=
    (FDRep.isoToLinearEquiv
      (restrictionIsoRealization R)).finrank_eq
  have hdim :
      Module.finrank ℂ E =
        n * Module.finrank ℂ T₀.character.realization := by
    have hmodule :
        Module.finrank ℂ
            (Representation.asModule
              T₀.character.realization.ρ) =
          Module.finrank ℂ T₀.character.realization :=
      (Representation.asModuleEquiv
        T₀.character.realization.ρ).finrank_eq
    calc
      _ = Module.finrank ℂ
          (Fin n →
            Representation.asModule
              T₀.character.realization.ρ) :=
        (e.restrictScalars ℂ).finrank_eq
      _ = ∑ _ : Fin n,
          Module.finrank ℂ
            (Representation.asModule
              T₀.character.realization.ρ) :=
        Module.finrank_pi_fintype ℂ
      _ =
          n * Module.finrank ℂ
            T₀.character.realization := by
        simp [hmodule]
  rw [hspace, hV, hdim]

/-- The tensor source of evaluation has exactly the ambient dimension. -/
theorem finrank_tensor_space_eq
    (R : AssociatedProjectiveRepresentation T₀ V₀ P₀)
    (E : FDRep ℂ A₀) [Simple E]
    (hE : ∃ f : T₀.character.realization ⟶
      FDRep.res T₀.normalSubgroup.subtype E, f ≠ 0) :
    Module.finrank ℂ (V₀ ⊗[ℂ] Space R E.ρ) =
      Module.finrank ℂ E := by
  rw [Module.finrank_tensorProduct, mul_comm]
  exact finrank_space_mul_finrank_eq R E hE

/-- Evaluation reconstructs a simple ambient representation from the
associated projective representation and its multiplicity space. -/
def evaluationRepresentationEquiv
    (R : AssociatedProjectiveRepresentation T₀ V₀ P₀)
    (E : FDRep ℂ A₀) [Simple E]
    (hE : ∃ f : T₀.character.realization ⟶
      FDRep.res T₀.normalSubgroup.subtype E, f ≠ 0) :
    Representation.Equiv (tensorRepresentation R E.ρ) E.ρ := by
  letI : Representation.IsIrreducible E.ρ :=
    CliffordRestriction.isIrreducible_of_simple E
  letI : Nontrivial (Space R E.ρ) :=
    space_nontrivial_of_exists_character_hom R E hE
  exact
    evaluationRepresentationEquivOfFinrankEq
      R E.ρ (finrank_tensor_space_eq R E hE)

/-- Linear form of the unconditional evaluation reconstruction. -/
def evaluationLinearEquiv
    (R : AssociatedProjectiveRepresentation T₀ V₀ P₀)
    (E : FDRep ℂ A₀) [Simple E]
    (hE : ∃ f : T₀.character.realization ⟶
      FDRep.res T₀.normalSubgroup.subtype E, f ≠ 0) :
    V₀ ⊗[ℂ] Space R E.ρ ≃ₗ[ℂ] E :=
  (evaluationRepresentationEquiv R E hE).toLinearEquiv

section Character

/-- For a character lying over the triple character, the factor-cancelled
tensor representation on its multiplicity space is its chosen realization. -/
def evaluationRepresentationEquivOfLiesOver
    (R : AssociatedProjectiveRepresentation T₀ V₀ P₀)
    (χ : IrreducibleCharacter A₀)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T₀.normalSubgroup.subtype T₀.character χ) :
    Representation.Equiv
      (tensorRepresentation R χ.realization.ρ)
      χ.realization.ρ :=
  evaluationRepresentationEquiv R χ.realization
    ((CliffordCorrespondence.liesOverAlong_iff_exists_nonzero
      T₀.normalSubgroup.subtype T₀.character χ).mp hχ)

/-- Exact character identity for multiplicity-space reconstruction. -/
theorem tensorRepresentation_character_eq_of_liesOver
    (R : AssociatedProjectiveRepresentation T₀ V₀ P₀)
    (χ : IrreducibleCharacter A₀)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T₀.normalSubgroup.subtype T₀.character χ) :
    (tensorRepresentation R χ.realization.ρ).character =
      χ.values := by
  calc
    (tensorRepresentation R χ.realization.ρ).character =
        χ.realization.character :=
      Representation.char_iso
        (evaluationRepresentationEquivOfLiesOver R χ hχ)
    _ = χ.values := χ.realization_character

end Character

end MultiplicityProjective
end CharacterTriple
end McKayConjecture
