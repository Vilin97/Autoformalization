/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RepresentationTheory.Character

/-!
# Restriction of finite-dimensional representations

A monoid homomorphism `f : H →* G` restricts a finite-dimensional
`G`-representation to an `H`-representation by precomposing its action with
`f`.  This file exposes the restriction functor and records its effect on the
action, character, and dimension.

Restriction does not generally preserve simplicity for a proper subgroup.
It does preserve simplicity when the homomorphism is a group isomorphism.
-/

noncomputable section

open CategoryTheory

universe u v w x

namespace FDRep

variable {k : Type u} [Field k]
variable {G : Type v} {H : Type w} {K : Type x}
variable [Monoid G] [Monoid H] [Monoid K]

/-- Restriction of finite-dimensional representations along a monoid
homomorphism. -/
abbrev resFunctor (f : H →* G) : FDRep k G ⥤ FDRep k H :=
  Action.res (FGModuleCat k) f

/-- A finite-dimensional representation restricted along a monoid
homomorphism. -/
abbrev res (f : H →* G) (V : FDRep k G) : FDRep k H :=
  (resFunctor f).obj V

/-- Restriction does not change the underlying finite-dimensional module. -/
theorem res_V (f : H →* G) (V : FDRep k G) :
    (res f V).V = V.V :=
  rfl

/-- Restriction precomposes the representing monoid homomorphism. -/
@[simp]
theorem res_ρ (f : H →* G) (V : FDRep k G) :
    (res f V).ρ = V.ρ.comp f :=
  rfl

/-- Pointwise form of `FDRep.res_ρ`. -/
@[simp]
theorem res_ρ_apply (f : H →* G) (V : FDRep k G) (h : H) :
    (res f V).ρ h = V.ρ (f h) :=
  rfl

/-- Restriction pulls the character back along the homomorphism. -/
@[simp]
theorem res_character_apply (f : H →* G) (V : FDRep k G) (h : H) :
    (res f V).character h = V.character (f h) :=
  rfl

/-- Function-valued form of the character restriction formula. -/
theorem res_character (f : H →* G) (V : FDRep k G) :
    (res f V).character = V.character ∘ f :=
  rfl

/-- Restriction leaves the representation degree unchanged. -/
@[simp]
theorem res_finrank (f : H →* G) (V : FDRep k G) :
    Module.finrank k (res f V) = Module.finrank k V :=
  rfl

/-- Restriction along the identity homomorphism is definitionally the original
representation. -/
@[simp]
theorem res_id (V : FDRep k G) :
    res (MonoidHom.id G) V = V :=
  rfl

/-- Successive restrictions agree with restriction along the composite
homomorphism. -/
@[simp]
theorem res_comp (f : H →* G) (g : K →* H) (V : FDRep k G) :
    res g (res f V) = res (f.comp g) V :=
  rfl

/-- Functorial identity isomorphism for restriction. -/
def resFunctorIdIso :
    resFunctor (k := k) (MonoidHom.id G) ≅ 𝟭 (FDRep k G) :=
  Action.resId (FGModuleCat k)

/-- Functorial composition isomorphism for restriction. -/
def resFunctorCompIso (f : H →* G) (g : K →* H) :
    resFunctor (k := k) f ⋙ resFunctor g ≅ resFunctor (f.comp g) :=
  Action.resComp (FGModuleCat k) g f

/-- Objectwise identity isomorphism for restriction. -/
def resIdIso (V : FDRep k G) :
    res (MonoidHom.id G) V ≅ V :=
  resFunctorIdIso.app V

/-- Objectwise composition isomorphism for restriction. -/
def resCompIso (f : H →* G) (g : K →* H) (V : FDRep k G) :
    res g (res f V) ≅ res (f.comp g) V :=
  (resFunctorCompIso f g).app V

/-- Restriction leaves the underlying morphism of finite-dimensional modules
unchanged. -/
@[simp]
theorem resFunctor_map_hom (f : H →* G) {V W : FDRep k G} (φ : V ⟶ W) :
    ((resFunctor f).map φ).hom = φ.hom :=
  rfl

section Subgroup

variable {G : Type v} [Group G]

/-- Restriction of a finite-dimensional representation to a subgroup. -/
abbrev resSubgroup (S : Subgroup G) (V : FDRep k G) : FDRep k S :=
  res S.subtype V

/-- The functor restricting finite-dimensional representations to a subgroup. -/
abbrev resSubgroupFunctor (S : Subgroup G) : FDRep k G ⥤ FDRep k S :=
  resFunctor S.subtype

@[simp]
theorem resSubgroup_ρ_apply (S : Subgroup G) (V : FDRep k G) (s : S) :
    (resSubgroup S V).ρ s = V.ρ s.1 :=
  rfl

@[simp]
theorem resSubgroup_character_apply (S : Subgroup G) (V : FDRep k G) (s : S) :
    (resSubgroup S V).character s = V.character s.1 :=
  rfl

@[simp]
theorem resSubgroup_finrank (S : Subgroup G) (V : FDRep k G) :
    Module.finrank k (resSubgroup S V) = Module.finrank k V :=
  rfl

end Subgroup

section Isomorphism

variable {G : Type v} {H : Type w} [Group G] [Group H]

/-- Restriction along a group isomorphism preserves simplicity. -/
theorem simple_res_mulEquiv (e : H ≃* G) (V : FDRep k G) [Simple V] :
    Simple (res (e : H →* G) V) := by
  let E : FDRep k G ≌ FDRep k H :=
    Action.resEquiv (FGModuleCat k) e
  change Simple (E.functor.obj V)
  exact CategoryTheory.simple_obj E.functor V

end Isomorphism

end FDRep
