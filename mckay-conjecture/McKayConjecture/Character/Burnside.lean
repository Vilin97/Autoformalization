/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordRestriction
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Burnside density for complex representations

This file records the finite-dimensional complex form of Burnside's density
theorem used by tensor-product arguments: an irreducible representation spans
the full endomorphism algebra.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace McKayConjecture

namespace Representation

universe u v

variable {G : Type u} {X : Type v} [Group G]
variable [AddCommGroup X] [Module ℂ X]

/-- Burnside density: the group algebra of an irreducible
finite-dimensional complex representation acts as every linear
endomorphism. -/
theorem asAlgebraHom_surjective_of_isIrreducible
    (ρ : Representation ℂ G X) [ρ.IsIrreducible]
    [Module.Finite ℂ X] :
    Function.Surjective ρ.asAlgebraHom := by
  let D := Module.End ℂ[G] ρ.asModule
  letI : Module.Finite D ρ.asModule :=
    Module.Finite.of_restrictScalars_finite ℂ D ρ.asModule
  have hschur :
      Function.Surjective (algebraMap ℂ D) :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (A := ℂ[G]) (V := ρ.asModule) ℂ).2
  intro e
  let eM : Module.End ℂ ρ.asModule :=
    ρ.asModuleEquiv.symm.toLinearMap ∘ₗ
      e ∘ₗ ρ.asModuleEquiv.toLinearMap
  let f : Module.End D ρ.asModule :=
    { toFun := eM
      map_add' := eM.map_add
      map_smul' := by
        intro d m
        obtain ⟨c, rfl⟩ := hschur d
        change eM (c • m) = c • eM m
        exact eM.map_smul c m }
  obtain ⟨r, hr⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective
      (R := ℂ[G]) (M := ρ.asModule) f
  refine ⟨r, ?_⟩
  apply LinearMap.ext
  intro x
  have hx := DFunLike.congr_fun hr (ρ.asModuleEquiv.symm x)
  have hx' := congrArg ρ.asModuleEquiv hx
  simpa [D, f, eM] using hx'

end Representation

namespace FDRep

universe u

variable {G : Type u} {X : Type} [Group G]
variable [AddCommGroup X] [Module ℂ X] [Module.Finite ℂ X]

/-- Lattice irreducibility of a complex representation gives categorical
simplicity of the associated finite-dimensional representation. -/
theorem simple_of_representation_isIrreducible
    (ρ : Representation ℂ G X) [ρ.IsIrreducible] :
    Simple (FDRep.of ρ) := by
  let R : Rep ℂ G :=
    (forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (FDRep.of ρ)
  letI : IsSimpleModule ℂ[G] ρ.asModule := inferInstance
  letI : Simple (ModuleCat.of ℂ[G] ρ.asModule) := inferInstance
  letI : Simple
      ((Rep.equivalenceModuleMonoidAlgebra
        (k := ℂ) (G := G)).functor.obj R) := by
    change Simple (ModuleCat.of ℂ[G] ρ.asModule)
    infer_instance
  letI : Simple R :=
    Functor.simple_of_simple_obj
      (Rep.equivalenceModuleMonoidAlgebra
        (k := ℂ) (G := G)).functor R
  exact
    Functor.simple_of_simple_obj
      (forget₂ (FDRep ℂ G) (Rep ℂ G)) (FDRep.of ρ)

end FDRep
end McKayConjecture
