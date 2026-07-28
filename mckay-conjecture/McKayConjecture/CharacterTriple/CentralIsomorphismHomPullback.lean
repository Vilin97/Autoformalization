/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralIsomorphism
import McKayConjecture.CharacterTriple.ProjectiveRestriction

/-!
# Pullback of central-isomorphism witnesses along homomorphisms

Projective representations pull back along arbitrary group homomorphisms.
The same is true for an associated lift provided that the homomorphism
identifies the distinguished normal subgroup with the old one and preserves
its character.  This file packages that observation and then uses it to pull
back a complete central-isomorphism witness along a commutative square.

Unlike relabelling by group isomorphisms, this construction allows kernels in
the two ambient homomorphisms.  This is essential when an automorphism of an
ambient group becomes trivial after restriction to an intermediate subgroup.
-/

noncomputable section

universe u u' v v'

open CategoryTheory

namespace McKayConjecture
namespace CharacterTriple

namespace AssociatedProjectiveRepresentation

variable {A : Type u} {A' : Type u'}
  [Group A] [Finite A] [Group A'] [Finite A']
variable {T : CharacterTriple A} {T' : CharacterTriple A'}
variable {V : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- Pull an associated projective representation back along a group
homomorphism which identifies the two distinguished normal subgroups. -/
def comapAlong
    (R : AssociatedProjectiveRepresentation T V P)
    (f : A' →* A)
    (e : T'.normalSubgroup ≃* T.normalSubgroup)
    (normal_commutes :
      ∀ x : T'.normalSubgroup,
        f (x : A') = (e x : A))
    (character_agreement :
      ∀ x : T'.normalSubgroup,
        T'.character.values x =
          T.character.values (e x)) :
    AssociatedProjectiveRepresentation T' V (P.comap f) where
  restriction := R.restriction.comp e.toMonoidHom
  restriction_apply x := by
    change R.restriction (e x) = P.operator (f (x : A'))
    rw [R.restriction_apply, normal_commutes x]
  restriction_simple := by
    let E : FDRep ℂ T.normalSubgroup ≌
        FDRep ℂ T'.normalSubgroup :=
      Action.resEquiv (FGModuleCat ℂ) e
    change Simple (E.functor.obj R.fdRestriction)
    exact CategoryTheory.simple_obj E.functor R.fdRestriction
  restriction_character := by
    funext x
    change
      LinearMap.trace ℂ V
          ((linearRepresentationOfAction
            (R.restriction.comp e.toMonoidHom)) x) =
        T'.character.values x
    rw [character_agreement x]
    exact congrFun R.restriction_character (e x)
  normal_mul x a := by
    have h := R.normal_mul (e x) (f a)
    change
      P.operator (f ((x : A') * a)) =
        P.operator (f (x : A')) * P.operator (f a)
    rw [map_mul, normal_commutes x]
    exact h
  mul_normal a x := by
    have h := R.mul_normal (f a) (e x)
    change
      P.operator (f (a * (x : A'))) =
        P.operator (f a) * P.operator (f (x : A'))
    rw [map_mul, normal_commutes x]
    exact h

@[simp]
theorem comapAlong_restriction_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (f : A' →* A)
    (e : T'.normalSubgroup ≃* T.normalSubgroup)
    (normal_commutes :
      ∀ x : T'.normalSubgroup,
        f (x : A') = (e x : A))
    (character_agreement :
      ∀ x : T'.normalSubgroup,
        T'.character.values x =
          T.character.values (e x))
    (x : T'.normalSubgroup) :
    (R.comapAlong f e normal_commutes
      character_agreement).restriction x =
        R.restriction (e x) :=
  rfl

end AssociatedProjectiveRepresentation

namespace CentralIsomorphismWitness

variable {A : Type u} {A' : Type u'}
  {B : Type v} {B' : Type v'}
  [Group A] [Finite A] [Group A'] [Finite A']
  [Group B] [Finite B] [Group B'] [Finite B']
variable {T : CharacterTriple A} {T' : CharacterTriple A'}
  {U : CharacterTriple B} {U' : CharacterTriple B'}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]

/-- A commutative pullback square for a central-isomorphism witness.

The normal-subgroup and character fields are the precise hypotheses needed
to pull back the two associated projective lifts.  The four remaining group
fields are exactly the group-theoretic clauses of a central isomorphism for
the new embedding. -/
structure HomPullbackDiagram
    (C : CentralIsomorphismWitness T U V W)
    (T' : CharacterTriple A') (U' : CharacterTriple B') where
  /-- Homomorphism from the new left ambient group to the old one. -/
  leftHom : A' →* A
  /-- Homomorphism from the new right ambient group to the old one. -/
  rightHom : B' →* B
  /-- The new right-to-left embedding. -/
  embedding : B' →* A'
  /-- The square with the old embedding commutes. -/
  embedding_commutes :
    leftHom.comp embedding =
      C.embedding.comp rightHom
  /-- Identification of the left normal subgroups. -/
  leftNormalEquiv :
    T'.normalSubgroup ≃* T.normalSubgroup
  /-- The left homomorphism induces `leftNormalEquiv`. -/
  left_normal_commutes :
    ∀ x : T'.normalSubgroup,
      leftHom (x : A') = (leftNormalEquiv x : A)
  /-- The left normal characters agree. -/
  left_character_agreement :
    ∀ x : T'.normalSubgroup,
      T'.character.values x =
        T.character.values (leftNormalEquiv x)
  /-- Identification of the right normal subgroups. -/
  rightNormalEquiv :
    U'.normalSubgroup ≃* U.normalSubgroup
  /-- The right homomorphism induces `rightNormalEquiv`. -/
  right_normal_commutes :
    ∀ x : U'.normalSubgroup,
      rightHom (x : B') = (rightNormalEquiv x : B)
  /-- The right normal characters agree. -/
  right_character_agreement :
    ∀ x : U'.normalSubgroup,
      U'.character.values x =
        U.character.values (rightNormalEquiv x)
  /-- The new embedding is injective. -/
  embedding_injective :
    Function.Injective embedding
  /-- The new left centralizer lies in the new right subgroup. -/
  centralizer_le :
    Subgroup.centralizer (T'.normalSubgroup : Set A') ≤
      MonoidHom.range embedding
  /-- The new left ambient group is the product of its normal subgroup and
  the image of the new right group. -/
  ambient_eq_product :
    ∀ a : A',
      ∃ x : T'.normalSubgroup,
        ∃ b : B', (x : A') * embedding b = a
  /-- The new right normal subgroup is the exact intersection. -/
  intersection_eq :
    T'.normalSubgroup ⊓ MonoidHom.range embedding =
      U'.normalSubgroup.map embedding

namespace HomPullbackDiagram

variable
  (C : CentralIsomorphismWitness T U V W)
  (D : HomPullbackDiagram C T' U')

@[simp]
theorem embedding_commutes_apply (b : B') :
    D.leftHom (D.embedding b) =
      C.embedding (D.rightHom b) :=
  DFunLike.congr_fun D.embedding_commutes b

/-- The image of a new centralizing element centralizes the old normal
subgroup. -/
theorem image_embedding_mem_centralizer
    (b : B')
    (hb : D.embedding b ∈
      Subgroup.centralizer (T'.normalSubgroup : Set A')) :
    C.embedding (D.rightHom b) ∈
      Subgroup.centralizer (T.normalSubgroup : Set A) := by
  rw [Subgroup.mem_centralizer_iff] at hb ⊢
  intro x hx
  let x' : T'.normalSubgroup :=
    D.leftNormalEquiv.symm ⟨x, hx⟩
  have hx' :
      (D.leftNormalEquiv x' : A) = x := by
    exact congrArg Subtype.val
      (D.leftNormalEquiv.apply_symm_apply ⟨x, hx⟩)
  have hcomm := hb (x' : A') x'.property
  have hmap := congrArg D.leftHom hcomm
  simpa only [map_mul, D.embedding_commutes_apply C,
    D.left_normal_commutes, hx'] using hmap

end HomPullbackDiagram

/-- Pull a central-isomorphism witness back along a commutative square of
ambient homomorphisms. -/
def pullback
    (C : CentralIsomorphismWitness T U V W)
    (D : HomPullbackDiagram C T' U') :
    CentralIsomorphismWitness T' U' V W where
  leftProjective :=
    C.leftProjective.comap D.leftHom
  leftAssociated :=
    C.leftAssociated.comapAlong
      D.leftHom D.leftNormalEquiv
      D.left_normal_commutes
      D.left_character_agreement
  rightProjective :=
    C.rightProjective.comap D.rightHom
  rightAssociated :=
    C.rightAssociated.comapAlong
      D.rightHom D.rightNormalEquiv
      D.right_normal_commutes
      D.right_character_agreement
  embedding := D.embedding
  embedding_injective := D.embedding_injective
  centralizer_le := D.centralizer_le
  ambient_eq_product := D.ambient_eq_product
  intersection_eq := D.intersection_eq
  factor_agreement b c := by
    change
      C.leftProjective.factor
          (D.leftHom (D.embedding b))
          (D.leftHom (D.embedding c)) =
        C.rightProjective.factor
          (D.rightHom b) (D.rightHom c)
    rw [D.embedding_commutes_apply C,
      D.embedding_commutes_apply C]
    exact C.factor_agreement (D.rightHom b) (D.rightHom c)
  scalar_agreement b hb := by
    have hbOld :=
      D.image_embedding_mem_centralizer C b hb
    obtain ⟨c, hleft, hright⟩ :=
      C.scalar_agreement (D.rightHom b) hbOld
    refine ⟨c, ?_, hright⟩
    change
      C.leftProjective.operator
          (D.leftHom (D.embedding b)) =
        scalarLinearEquiv ℂ V c
    rw [D.embedding_commutes_apply C]
    exact hleft

@[simp]
theorem pullback_embedding
    (C : CentralIsomorphismWitness T U V W)
    (D : HomPullbackDiagram C T' U') :
    (C.pullback D).embedding = D.embedding :=
  rfl

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
