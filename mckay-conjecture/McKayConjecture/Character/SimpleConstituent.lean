/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Burnside
import McKayConjecture.Character.CliffordCorrespondence
import McKayConjecture.Character.CliffordTheorem
import McKayConjecture.Character.Construction
import McKayConjecture.Character.Determination

/-!
# Packaging a simple constituent of a normal-subgroup restriction

Clifford theory supplies a simple group-algebra submodule of a restricted
simple representation.  This file packages that module as an `FDRep`, and
then as an irreducible character, together with its nonzero constituent
map.  This is the bridge between module-level semisimplicity and the
character-level `LiesOverAlong` predicate.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace McKayConjecture

namespace FDRep

variable {K : Type} [Group K]

/-- Converting the constituent module to a representation and back recovers
the original group-algebra module. -/
private def normalSimpleConstituentAsModuleEquiv
    (E : FDRep ℂ K) [Simple E]
    (N : Subgroup K) [N.Normal] :
    let S := CliffordTheorem.simpleConstituent E N
    (Representation.ofModule' (k := ℂ) (G := N) S).asModule
        ≃ₗ[ℂ[N]] S := by
  let S := CliffordTheorem.simpleConstituent E N
  let ρ : Representation ℂ N S :=
    Representation.ofModule' S
  have hAlg :
      ρ.asAlgebraHom = Algebra.lsmul ℂ ℂ S := by
    simp [ρ, Representation.asAlgebraHom_def,
      Representation.ofModule']
  exact
  { ρ.asModuleEquiv with
    map_smul' := by
      intro r x
      change
        ρ.asModuleEquiv (r • x) =
          r • ρ.asModuleEquiv x
      exact
        (ρ.asModuleEquiv_map_smul r x).trans (by
          rw [hAlg]
          rfl) }

/-- A chosen simple constituent of the restriction of a simple
representation to a normal subgroup, packaged as an `FDRep`. -/
def normalSimpleConstituent
    (E : FDRep ℂ K) [Simple E]
    (N : Subgroup K) [N.Normal] :
    FDRep ℂ N := by
  let S := CliffordTheorem.simpleConstituent E N
  letI : Module.Finite ℂ S :=
    Module.Finite.of_injective
      (S.subtype.restrictScalars ℂ) S.subtype_injective
  exact FDRep.of (Representation.ofModule' S)

/-- The packaged normal-subgroup constituent is simple. -/
theorem normalSimpleConstituent_simple
    (E : FDRep ℂ K) [Simple E]
    (N : Subgroup K) [N.Normal] :
    Simple (normalSimpleConstituent E N) := by
  let S := CliffordTheorem.simpleConstituent E N
  letI : Module.Finite ℂ S :=
    Module.Finite.of_injective
      (S.subtype.restrictScalars ℂ) S.subtype_injective
  letI : IsSimpleModule ℂ[N] S :=
    CliffordTheorem.simpleConstituentIsSimple E N
  let ρ : Representation ℂ N S :=
    Representation.ofModule' S
  let e : ρ.asModule ≃ₗ[ℂ[N]] S :=
    normalSimpleConstituentAsModuleEquiv E N
  letI : IsSimpleModule ℂ[N] ρ.asModule :=
    IsSimpleModule.congr e
  letI :
      Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr
      inferInstance
  change
    Simple
      (FDRep.of
        (Representation.ofModule' (k := ℂ) (G := N) S))
  exact
    FDRep.simple_of_representation_isIrreducible
      ρ

/-- The canonical inclusion of the chosen simple constituent into the
restricted representation. -/
def normalSimpleConstituentEmbedding
    (E : FDRep ℂ K) [Simple E]
    (N : Subgroup K) [N.Normal] :
    normalSimpleConstituent E N ⟶ FDRep.resSubgroup N E := by
  let S := CliffordTheorem.simpleConstituent E N
  letI : Module.Finite ℂ S :=
    Module.Finite.of_injective
      (S.subtype.restrictScalars ℂ) S.subtype_injective
  let ρ : Representation ℂ N S :=
    Representation.ofModule' S
  let σ : Representation ℂ N E :=
    (FDRep.resSubgroup N E).ρ
  let e : ρ.asModule ≃ₗ[ℂ[N]] S :=
    normalSimpleConstituentAsModuleEquiv E N
  let inclusionModule :
      ρ.asModule →ₗ[ℂ[N]] σ.asModule :=
    S.subtype.comp e.toLinearMap
  let inclusionIntertwiner :
      Representation.IntertwiningMap ρ σ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      ρ σ).symm inclusionModule
  let inclusionRep :
      Rep.of ρ ⟶ Rep.of σ :=
    Rep.ofHom inclusionIntertwiner
  exact
    FDRep.forget₂HomLinearEquiv
      (normalSimpleConstituent E N)
      (FDRep.resSubgroup N E) inclusionRep

/-- The constituent inclusion is a monomorphism. -/
theorem normalSimpleConstituentEmbedding_mono
    (E : FDRep ℂ K) [Simple E]
    (N : Subgroup K) [N.Normal] :
    Mono (normalSimpleConstituentEmbedding E N) := by
  let S := CliffordTheorem.simpleConstituent E N
  letI : Module.Finite ℂ S :=
    Module.Finite.of_injective
      (S.subtype.restrictScalars ℂ) S.subtype_injective
  apply ConcreteCategory.mono_of_injective
  intro x y hxy
  exact S.subtype_injective hxy

end FDRep

namespace IrreducibleCharacter

variable {K : Type} [Finite K] [Group K]

/-- A chosen irreducible constituent of the restriction of an irreducible
character to a normal subgroup. -/
def normalSimpleConstituent
    (φ : IrreducibleCharacter K)
    (N : Subgroup K) [N.Normal] :
    IrreducibleCharacter N := by
  letI : Simple
      (FDRep.normalSimpleConstituent φ.realization N) :=
    FDRep.normalSimpleConstituent_simple φ.realization N
  exact
    ofSimple
      (FDRep.normalSimpleConstituent φ.realization N)

/-- The chosen constituent really occurs in the restriction. -/
theorem normalSimpleConstituent_liesOver
    (φ : IrreducibleCharacter K)
    (N : Subgroup K) [N.Normal] :
    CliffordCorrespondence.LiesOverAlong N.subtype
      (normalSimpleConstituent φ N) φ := by
  rw [CliffordCorrespondence.liesOverAlong_iff_exists_nonzero]
  let C := FDRep.normalSimpleConstituent φ.realization N
  letI : Simple C :=
    FDRep.normalSimpleConstituent_simple φ.realization N
  let χ := normalSimpleConstituent φ N
  obtain ⟨i : χ.realization ≅ C⟩ :=
    FDRep.nonempty_iso_of_character_eq χ.realization C (by
      rw [χ.realization_character]
      rfl)
  let f :
      χ.realization ⟶
        FDRep.res N.subtype φ.realization :=
    i.hom ≫
      FDRep.normalSimpleConstituentEmbedding φ.realization N
  letI : Mono
      (FDRep.normalSimpleConstituentEmbedding φ.realization N) :=
    FDRep.normalSimpleConstituentEmbedding_mono φ.realization N
  letI : Mono f := by
    dsimp [f]
    infer_instance
  refine ⟨f, ?_⟩
  intro hf
  exact
    Simple.not_isZero χ.realization
      (Limits.IsZero.of_mono_eq_zero f hf)

end IrreducibleCharacter
end McKayConjecture
