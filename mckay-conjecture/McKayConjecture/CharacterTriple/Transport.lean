/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Transport
import McKayConjecture.CharacterTriple.CentralIsomorphism
import McKayConjecture.CharacterTriple.ProjectiveRestriction

/-!
# Transport of character triples

This file transports character triples and their associated projective
representations along isomorphisms of the ambient groups.  It also proves that
a central-isomorphism witness is unchanged by independently relabelling its
left and right ambient groups.

The convention is contravariant: if `e : A' ≃* A` and `T` is a character
triple over `A`, then `T.comap e` is the corresponding triple over `A'`.
-/

noncomputable section

open CategoryTheory

universe u u' v v' w

namespace McKayConjecture
namespace CharacterTriple

section Triple

variable {A : Type u} {A' : Type u'} [Finite A] [Finite A'] [Group A] [Group A']

/-- The isomorphism from the inverse image of `T.X` to `T.X` induced by an
ambient group isomorphism. -/
def normalSubgroupEquiv (T : CharacterTriple A) (e : A' ≃* A) :
    T.normalSubgroup.comap e.toMonoidHom ≃* T.normalSubgroup where
  toFun x := ⟨e x, x.property⟩
  invFun x := ⟨e.symm x, by simp [x.property]⟩
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp
  map_mul' x y := by
    ext
    exact e.map_mul x y

omit [Finite A'] in
@[simp]
theorem coe_normalSubgroupEquiv_apply (T : CharacterTriple A) (e : A' ≃* A)
    (x : T.normalSubgroup.comap e.toMonoidHom) :
    (T.normalSubgroupEquiv e x : A) = e x :=
  rfl

omit [Finite A'] in
@[simp]
theorem coe_normalSubgroupEquiv_symm_apply (T : CharacterTriple A) (e : A' ≃* A)
    (x : T.normalSubgroup) :
    ((T.normalSubgroupEquiv e).symm x :
      T.normalSubgroup.comap e.toMonoidHom) = e.symm x :=
  rfl

/-- Pull a character triple back along an isomorphism of ambient groups. -/
def comap (T : CharacterTriple A) (e : A' ≃* A) : CharacterTriple A' where
  normalSubgroup := T.normalSubgroup.comap e.toMonoidHom
  isNormal := T.isNormal.comap e.toMonoidHom
  character := T.character.comap (T.normalSubgroupEquiv e)
  isInvariant := by
    intro a x
    have hconj :
        T.normalSubgroupEquiv e
            (conjugateNormalElement
              (T.normalSubgroup.comap e.toMonoidHom)
              (T.isNormal.comap e.toMonoidHom) a x) =
          conjugateNormalElement T.normalSubgroup T.isNormal
            (e a) (T.normalSubgroupEquiv e x) := by
      ext
      change e (a * (x : A') * a⁻¹) =
        e a * e (x : A') * (e a)⁻¹
      simp
    change T.character.values
        (T.normalSubgroupEquiv e
          (conjugateNormalElement
            (T.normalSubgroup.comap e.toMonoidHom)
            (T.isNormal.comap e.toMonoidHom) a x)) =
      T.character.values (T.normalSubgroupEquiv e x)
    rw [hconj]
    exact T.isInvariant (e a) (T.normalSubgroupEquiv e x)

@[simp]
theorem comap_normalSubgroup (T : CharacterTriple A) (e : A' ≃* A) :
    (T.comap e).normalSubgroup = T.normalSubgroup.comap e.toMonoidHom :=
  rfl

@[simp]
theorem comap_character_values (T : CharacterTriple A) (e : A' ≃* A)
    (x : (T.comap e).normalSubgroup) :
    (T.comap e).character.values x =
      T.character.values (T.normalSubgroupEquiv e x) :=
  rfl

/-- Centralizing the normal subgroup is invariant under relabelling the
ambient group. -/
theorem mem_centralizer_comap_iff (T : CharacterTriple A) (e : A' ≃* A)
    (a : A') :
    a ∈ Subgroup.centralizer ((T.comap e).normalSubgroup : Set A') ↔
      e a ∈ Subgroup.centralizer (T.normalSubgroup : Set A) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro ha x hx
    let x' : (T.comap e).normalSubgroup :=
      (T.normalSubgroupEquiv e).symm ⟨x, hx⟩
    have hx' : e (x' : A') = x := by
      change e (e.symm x) = x
      simp
    have hcomm := ha (x' : A') x'.property
    change (x' : A') * a = a * x' at hcomm
    simpa only [map_mul, hx'] using congrArg e hcomm
  · intro ha x hx
    apply e.injective
    simpa using ha (e x) hx

end Triple

namespace AssociatedProjectiveRepresentation

variable {A : Type u} {A' : Type u'} [Finite A] [Finite A'] [Group A] [Group A']
variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
variable {T : CharacterTriple A} {P : ProjectiveRepresentation ℂ A V}

/-- Pull an associated projective representation back along an isomorphism of
ambient groups. -/
def comap (R : AssociatedProjectiveRepresentation T V P) (e : A' ≃* A) :
    AssociatedProjectiveRepresentation (T.comap e) V
      (P.comap e.toMonoidHom) where
  restriction :=
    R.restriction.comp (T.normalSubgroupEquiv e).toMonoidHom
  restriction_apply := by
    intro x
    exact R.restriction_apply (T.normalSubgroupEquiv e x)
  restriction_simple := by
    let E : FDRep ℂ T.normalSubgroup ≌
        FDRep ℂ (T.comap e).normalSubgroup :=
      Action.resEquiv (FGModuleCat ℂ) (T.normalSubgroupEquiv e)
    change Simple (E.functor.obj R.fdRestriction)
    exact CategoryTheory.simple_obj E.functor R.fdRestriction
  restriction_character := by
    funext x
    change LinearMap.trace ℂ V
        ((linearRepresentationOfAction
          (R.restriction.comp (T.normalSubgroupEquiv e).toMonoidHom)) x) =
      T.character.values (T.normalSubgroupEquiv e x)
    exact congrFun R.restriction_character (T.normalSubgroupEquiv e x)
  normal_mul := by
    intro x a
    have h := R.normal_mul (T.normalSubgroupEquiv e x) (e a)
    change P.operator (e (x : A') * e a) =
      P.operator (e (x : A')) * P.operator (e a) at h
    change P.operator (e ((x : A') * a)) =
      P.operator (e (x : A')) * P.operator (e a)
    simpa only [map_mul] using h
  mul_normal := by
    intro a x
    have h := R.mul_normal (e a) (T.normalSubgroupEquiv e x)
    change P.operator (e a * e (x : A')) =
      P.operator (e a) * P.operator (e (x : A')) at h
    change P.operator (e (a * (x : A'))) =
      P.operator (e a) * P.operator (e (x : A'))
    simpa only [map_mul] using h

@[simp]
theorem comap_restriction_apply
    (R : AssociatedProjectiveRepresentation T V P) (e : A' ≃* A)
    (x : (T.comap e).normalSubgroup) :
    (R.comap e).restriction x = R.restriction (T.normalSubgroupEquiv e x) :=
  rfl

end AssociatedProjectiveRepresentation

namespace CentralIsomorphismWitness

variable {A : Type u} {A' : Type u'} {B : Type v} {B' : Type v'}
  [Finite A] [Finite A'] [Finite B] [Finite B']
  [Group A] [Group A'] [Group B] [Group B']
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]

/-- Relabel the subgroup embedding in a central-isomorphism witness. -/
def relabelEmbedding (C : CentralIsomorphismWitness T U V W)
    (eA : A' ≃* A) (eB : B' ≃* B) : B' →* A' :=
  eA.symm.toMonoidHom.comp (C.embedding.comp eB.toMonoidHom)

omit [Finite A'] [Finite B'] in
@[simp]
theorem relabelEmbedding_apply (C : CentralIsomorphismWitness T U V W)
    (eA : A' ≃* A) (eB : B' ≃* B) (b : B') :
    C.relabelEmbedding eA eB b = eA.symm (C.embedding (eB b)) :=
  rfl

/-- A central-isomorphism witness is invariant under independent relabelling
of its two ambient groups. -/
def comap (C : CentralIsomorphismWitness T U V W)
    (eA : A' ≃* A) (eB : B' ≃* B) :
    CentralIsomorphismWitness (T.comap eA) (U.comap eB) V W where
  leftProjective := C.leftProjective.comap eA.toMonoidHom
  leftAssociated := C.leftAssociated.comap eA
  rightProjective := C.rightProjective.comap eB.toMonoidHom
  rightAssociated := C.rightAssociated.comap eB
  embedding := C.relabelEmbedding eA eB
  embedding_injective :=
    eA.symm.injective.comp (C.embedding_injective.comp eB.injective)
  centralizer_le := by
    intro a ha
    have ha' := (mem_centralizer_comap_iff T eA a).mp ha
    obtain ⟨b, hb⟩ := C.centralizer_le ha'
    refine ⟨eB.symm b, ?_⟩
    change eA.symm (C.embedding (eB (eB.symm b))) = a
    rw [eB.apply_symm_apply, hb]
    exact eA.symm_apply_apply a
  ambient_eq_product := by
    intro a
    obtain ⟨x, b, hxb⟩ := C.ambient_eq_product (eA a)
    refine ⟨(T.normalSubgroupEquiv eA).symm x, eB.symm b, ?_⟩
    apply eA.injective
    change eA (eA.symm (x : A) *
      eA.symm (C.embedding (eB (eB.symm b)))) = eA a
    simpa only [map_mul, eA.apply_symm_apply, eB.apply_symm_apply] using hxb
  intersection_eq := by
    ext a
    constructor
    · rintro ⟨haX, ⟨b, hb⟩⟩
      have hEmbedding : C.embedding (eB b) = eA a := by
        have h := congrArg eA hb
        simpa only [relabelEmbedding_apply, eA.apply_symm_apply] using h
      have haOld :
          eA a ∈ T.normalSubgroup ⊓ MonoidHom.range C.embedding :=
        ⟨haX, ⟨eB b, hEmbedding⟩⟩
      have haMap : eA a ∈ U.normalSubgroup.map C.embedding := by
        rw [← C.intersection_eq]
        exact haOld
      obtain ⟨m, hm, hmEq⟩ := haMap
      refine ⟨eB.symm m, ?_, ?_⟩
      · simpa using hm
      · apply eA.injective
        simpa only [relabelEmbedding_apply, eA.apply_symm_apply,
          eB.apply_symm_apply] using hmEq
    · rintro ⟨b, hb, hbEq⟩
      have hEmbedding : C.embedding (eB b) = eA a := by
        have h := congrArg eA hbEq
        simpa only [relabelEmbedding_apply, eA.apply_symm_apply] using h
      have haMap : eA a ∈ U.normalSubgroup.map C.embedding :=
        ⟨eB b, hb, hEmbedding⟩
      have haOld :
          eA a ∈ T.normalSubgroup ⊓ MonoidHom.range C.embedding := by
        rw [C.intersection_eq]
        exact haMap
      exact ⟨haOld.1, ⟨b, hbEq⟩⟩
  factor_agreement := by
    intro h k
    change C.leftProjective.factor
        (eA (C.relabelEmbedding eA eB h))
        (eA (C.relabelEmbedding eA eB k)) =
      C.rightProjective.factor (eB h) (eB k)
    simpa using C.factor_agreement (eB h) (eB k)
  scalar_agreement := by
    intro h hh
    have hh' :=
      (mem_centralizer_comap_iff T eA
        (C.relabelEmbedding eA eB h)).mp hh
    change eA (C.relabelEmbedding eA eB h) ∈
      Subgroup.centralizer (T.normalSubgroup : Set A) at hh'
    have hhOld : C.embedding (eB h) ∈
        Subgroup.centralizer (T.normalSubgroup : Set A) := by
      simpa using hh'
    obtain ⟨c, hleft, hright⟩ := C.scalar_agreement (eB h) hhOld
    refine ⟨c, ?_, ?_⟩
    · change C.leftProjective.operator
          (eA (C.relabelEmbedding eA eB h)) =
        scalarLinearEquiv ℂ V c
      simpa using hleft
    · exact hright

/-- Existence of a central-isomorphism witness is preserved by relabelling
both ambient groups. -/
theorem centrallyIsomorphicVia_comap
    (eA : A' ≃* A) (eB : B' ≃* B)
    (h : CentrallyIsomorphicVia T U V W) :
    CentrallyIsomorphicVia (T.comap eA) (U.comap eB) V W := by
  obtain ⟨C⟩ := h
  exact ⟨C.comap eA eB⟩

end CentralIsomorphismWitness

end CharacterTriple
end McKayConjecture
