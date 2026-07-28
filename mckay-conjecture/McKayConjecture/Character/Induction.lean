/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.Tactic.Group
import McKayConjecture.Character.ClassFunction
import McKayConjecture.Character.Restriction

/-!
# Induction of finite-dimensional representations and class functions

For a homomorphism `φ : H →* G` with finite target, mathlib's coinvariant
construction of the induced representation is finite-dimensional.  This file
restricts that construction to `FDRep` and packages it as a functor.

For a subgroup `S ≤ G`, it also defines the classical induced class function

`Ind_S^G(θ)(g) = |S|⁻¹ ∑ x : G, θ(x⁻¹ g x)`,

where summands whose conjugate is not in `S` are zero.  The construction is
proved conjugation-invariant and its value at the identity is
`[G : S] θ(1)`.

Mathlib's general induction--restriction adjunction lives in `Rep`; the final
section exposes that linear Hom equivalence directly.  Mathlib does not yet
identify the character of its coinvariant model with the classical
class-function formula, so no such identification is asserted here.
-/

noncomputable section

open CategoryTheory

universe u

namespace FDRep

variable {k : Type u} [Field k]
variable {G H : Type u} [Group G] [Group H] [Finite G]

/-- The finite-dimensional representation induced along `φ : H →* G`.

The common universe hypothesis is inherited from mathlib's
`Representation.IndV`: its carrier contains the group algebra of `G`.
-/
abbrev ind (φ : H →* G) (V : FDRep k H) : FDRep k G :=
  FDRep.of (Representation.ind φ V.ρ)

/-- The action of the induced finite-dimensional representation is mathlib's
coinvariant-model induced action. -/
@[simp]
theorem ind_ρ (φ : H →* G) (V : FDRep k H) :
    (ind φ V).ρ = Representation.ind φ V.ρ :=
  rfl

/-- The character of `FDRep.ind` is the trace of mathlib's induced action. -/
@[simp]
theorem ind_character_apply (φ : H →* G) (V : FDRep k H) (g : G) :
    (ind φ V).character g =
      (Representation.ind φ V.ρ).character g :=
  rfl

/-- Induction on a morphism of finite-dimensional representations. -/
def indMap (φ : H →* G) {V W : FDRep k H} (f : V ⟶ W) :
    ind φ V ⟶ ind φ W := by
  let f' : Representation.IntertwiningMap V.ρ W.ρ :=
    { toLinearMap :=
        ((forget₂ (FGModuleCat k) (ModuleCat k)).map f.hom).hom
      isIntertwining' := fun h => by
        ext x
        exact ConcreteCategory.congr_hom
          ((forget (FGModuleCat k)).congr_map (f.comm h)) x }
  let F : Representation.IntertwiningMap
      (Representation.ind φ V.ρ) (Representation.ind φ W.ρ) :=
    ⟨Representation.Coinvariants.map _ _
      ⟨f'.toLinearMap.lTensor _, by
        simp [LinearMap.lTensor_comp_map, f'.2,
          LinearMap.map_comp_lTensor]⟩,
      fun g => by
        ext
        simp⟩
  exact
    ⟨InducedCategory.homMk (ModuleCat.ofHom F.toLinearMap), fun g => by
      ext1
      exact F.2 g⟩

/-- Induction along a homomorphism with finite target, as a functor on
finite-dimensional representations. -/
def indFunctor (k : Type u) [Field k] {G H : Type u}
    [Group G] [Group H] [Finite G] (φ : H →* G) :
    FDRep k H ⥤ FDRep k G where
  obj V := ind φ V
  map f := indMap φ f
  map_id _ := by
    ext
    rfl
  map_comp _ _ := by
    ext
    rfl

section Subgroup

variable {G : Type u} [Group G] [Finite G]

/-- Induction of a finite-dimensional representation from a subgroup. -/
abbrev indSubgroup (S : Subgroup G) (V : FDRep k S) : FDRep k G :=
  ind S.subtype V

/-- The functor inducing finite-dimensional representations from a subgroup. -/
abbrev indSubgroupFunctor (S : Subgroup G) : FDRep k S ⥤ FDRep k G :=
  indFunctor k S.subtype

end Subgroup

variable {G : Type u} [Group G]

/-- The character of a finite-dimensional complex representation as a bundled
class function. -/
def characterClassFunction (V : FDRep ℂ G) :
    McKayConjecture.ClassFunction G :=
  ⟨V.character, fun g h ↦ FDRep.char_conj V g h⟩

@[simp]
theorem characterClassFunction_apply (V : FDRep ℂ G) (g : G) :
    V.characterClassFunction g = V.character g :=
  rfl

end FDRep

namespace McKayConjecture.ClassFunction

universe v

variable {G : Type v} [Group G]

/-- The `x`-summand in the classical formula for induction from `S`.
It is zero when `x⁻¹ g x` does not belong to `S`. -/
def inductionTerm (S : Subgroup G) (θ : ClassFunction S) (x g : G) : ℂ :=
  by
    classical
    exact if hx : x⁻¹ * g * x ∈ S then
      θ ⟨x⁻¹ * g * x, hx⟩
    else
      0

@[simp]
theorem inductionTerm_of_mem (S : Subgroup G) (θ : ClassFunction S)
    {x g : G} (hx : x⁻¹ * g * x ∈ S) :
    inductionTerm S θ x g = θ ⟨x⁻¹ * g * x, hx⟩ := by
  simp [inductionTerm, hx]

@[simp]
theorem inductionTerm_of_not_mem (S : Subgroup G)
    (θ : ClassFunction S) {x g : G} (hx : x⁻¹ * g * x ∉ S) :
    inductionTerm S θ x g = 0 := by
  simp [inductionTerm, hx]

/-- Conjugating the argument of an induction summand reindexes its `x`
variable by left multiplication. -/
theorem inductionTerm_conj (S : Subgroup G) (θ : ClassFunction S)
    (x g h : G) :
    inductionTerm S θ x (h * g * h⁻¹) =
      inductionTerm S θ (h⁻¹ * x) g := by
  classical
  have heq :
      (h⁻¹ * x)⁻¹ * g * (h⁻¹ * x) =
        x⁻¹ * (h * g * h⁻¹) * x := by
    group
  by_cases hx : x⁻¹ * (h * g * h⁻¹) * x ∈ S
  · have hy : (h⁻¹ * x)⁻¹ * g * (h⁻¹ * x) ∈ S := by
      rwa [heq]
    rw [inductionTerm_of_mem S θ hx, inductionTerm_of_mem S θ hy]
    apply congrArg θ
    exact Subtype.ext heq.symm
  · have hy : (h⁻¹ * x)⁻¹ * g * (h⁻¹ * x) ∉ S := by
      intro hy
      exact hx (by rwa [← heq])
    rw [inductionTerm_of_not_mem S θ hx,
      inductionTerm_of_not_mem S θ hy]

/-- The classical induced complex class function. -/
def induce [Fintype G] (S : Subgroup G) (θ : ClassFunction S) :
    ClassFunction G :=
  ⟨fun g ↦ (Nat.card S : ℂ)⁻¹ * ∑ x : G, inductionTerm S θ x g,
    fun g h ↦ by
      change
        (Nat.card S : ℂ)⁻¹ *
            ∑ x : G, inductionTerm S θ x (h * g * h⁻¹) =
          (Nat.card S : ℂ)⁻¹ *
            ∑ x : G, inductionTerm S θ x g
      congr 1
      refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ ?_
      intro x
      exact inductionTerm_conj S θ x g h⟩

/-- The ordinary induced-character value formula. -/
@[simp]
theorem induce_apply [Fintype G] (S : Subgroup G)
    (θ : ClassFunction S) (g : G) :
    induce S θ g =
      (Nat.card S : ℂ)⁻¹ * ∑ x : G, inductionTerm S θ x g :=
  rfl

/-- The degree formula for an induced class function:
`Ind_S^G(θ)(1) = [G : S] θ(1)`. -/
@[simp]
theorem induce_apply_one [Fintype G] (S : Subgroup G)
    (θ : ClassFunction S) :
    induce S θ (1 : G) = (S.index : ℂ) * θ (1 : S) := by
  rw [induce_apply]
  have hterm :
      ∀ x : G, inductionTerm S θ x (1 : G) = θ (1 : S) := by
    intro x
    have hx : x⁻¹ * (1 : G) * x ∈ S := by simp
    rw [inductionTerm_of_mem S θ hx]
    exact congrArg θ (Subtype.ext (by simp))
  rw [Finset.sum_congr rfl (fun x _ ↦ hterm x),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← S.index_mul_card]
  have hcard : (Nat.card S : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  push_cast
  field_simp

/-- The classical value formula specialized to the character of a
finite-dimensional representation. -/
theorem induce_character_apply [Fintype G] (S : Subgroup G)
    (V : FDRep ℂ S) (g : G) :
    induce S V.characterClassFunction g =
      (Nat.card S : ℂ)⁻¹ *
        ∑ x : G, inductionTerm S V.characterClassFunction x g :=
  rfl

/-- The degree of the character induced from `V` is the subgroup index
times the degree of `V`. -/
@[simp]
theorem induce_character_apply_one [Fintype G] (S : Subgroup G)
    (V : FDRep ℂ S) :
    induce S V.characterClassFunction (1 : G) =
      (S.index : ℂ) * Module.finrank ℂ V := by
  rw [induce_apply_one]
  simp

end McKayConjecture.ClassFunction

namespace McKayConjecture

universe v w

variable {k : Type u} [Field k]
variable {G : Type v} {H : Type w} [Group G] [Group H]

/-- Frobenius reciprocity at mathlib's general representation level:
maps out of an induced representation are linearly equivalent to maps into
the corresponding restriction. -/
def inductionRestrictionHomEquiv (φ : H →* G)
    (V : Rep.{max u v w} k H) (W : Rep.{max u v w} k G) :
    (Rep.ind φ V ⟶ W) ≃ₗ[k] (V ⟶ Rep.res φ W) :=
  Rep.indResHomEquiv φ V W

/-- The induction functor is left adjoint to restriction at the general
representation level. -/
def inductionRestrictionAdjunction (φ : H →* G) :
    Rep.indFunctor.{max u v w} k φ ⊣
      Rep.resFunctor.{max u v w} φ :=
  Rep.indResAdjunction k φ

end McKayConjecture
