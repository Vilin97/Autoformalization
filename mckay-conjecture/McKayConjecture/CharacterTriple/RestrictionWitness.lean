/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralIsomorphism
import McKayConjecture.CharacterTriple.ProjectiveRestriction

/-!
# Central witnesses from restriction of one projective lift

The most economical way to construct a central isomorphism of character
triples is to use one projective representation on the left ambient group
and restrict it along the right embedding.  Factor-set agreement and scalar
agreement are then automatic.  Only the three group-theoretic conditions and
the assertion that the restricted lift is associated to the right character
remain.

This constructor is useful in the layer reduction: its hard projective
assertion can be stated as association of a restricted lift, without
repeating the factor and scalar equations already forced by restriction.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace CharacterTriple
namespace CentralIsomorphismWitness

variable {A : Type u} {B : Type v}
variable [Finite A] [Group A] [Finite B] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- Construct a central-isomorphism witness by restricting a single
associated projective representation along the right embedding.

Because the right projective representation is definitionally `P.comap e`,
the factor-set and scalar-agreement fields require no additional
character-theoretic hypotheses. -/
def ofProjectiveRestriction
    (leftAssociated :
      AssociatedProjectiveRepresentation T V P)
    (e : B →* A)
    (embedding_injective : Function.Injective e)
    (centralizer_le :
      Subgroup.centralizer
          (T.normalSubgroup : Set A) ≤
        MonoidHom.range e)
    (ambient_eq_product :
      ∀ a : A,
        ∃ x : T.normalSubgroup,
          ∃ h : B, (x : A) * e h = a)
    (intersection_eq :
      T.normalSubgroup ⊓ MonoidHom.range e =
        U.normalSubgroup.map e)
    (rightAssociated :
      AssociatedProjectiveRepresentation U V
        (P.comap e)) :
    CentralIsomorphismWitness T U V V where
  leftProjective := P
  leftAssociated := leftAssociated
  rightProjective := P.comap e
  rightAssociated := rightAssociated
  embedding := e
  embedding_injective := embedding_injective
  centralizer_le := centralizer_le
  ambient_eq_product := ambient_eq_product
  intersection_eq := intersection_eq
  factor_agreement := by
    intro h k
    rfl
  scalar_agreement := by
    intro h hh
    obtain ⟨c, hc⟩ :=
      leftAssociated.operator_centralizer_isScalar
        (e h) hh
    exact ⟨c, hc, hc⟩

@[simp]
theorem ofProjectiveRestriction_leftProjective
    (leftAssociated :
      AssociatedProjectiveRepresentation T V P)
    (e : B →* A)
    (embedding_injective : Function.Injective e)
    (centralizer_le :
      Subgroup.centralizer
          (T.normalSubgroup : Set A) ≤
        MonoidHom.range e)
    (ambient_eq_product :
      ∀ a : A,
        ∃ x : T.normalSubgroup,
          ∃ h : B, (x : A) * e h = a)
    (intersection_eq :
      T.normalSubgroup ⊓ MonoidHom.range e =
        U.normalSubgroup.map e)
    (rightAssociated :
      AssociatedProjectiveRepresentation U V
        (P.comap e)) :
    (ofProjectiveRestriction leftAssociated e
      embedding_injective centralizer_le
      ambient_eq_product intersection_eq
      rightAssociated).leftProjective =
        P :=
  rfl

@[simp]
theorem ofProjectiveRestriction_rightProjective
    (leftAssociated :
      AssociatedProjectiveRepresentation T V P)
    (e : B →* A)
    (embedding_injective : Function.Injective e)
    (centralizer_le :
      Subgroup.centralizer
          (T.normalSubgroup : Set A) ≤
        MonoidHom.range e)
    (ambient_eq_product :
      ∀ a : A,
        ∃ x : T.normalSubgroup,
          ∃ h : B, (x : A) * e h = a)
    (intersection_eq :
      T.normalSubgroup ⊓ MonoidHom.range e =
        U.normalSubgroup.map e)
    (rightAssociated :
      AssociatedProjectiveRepresentation U V
        (P.comap e)) :
    (ofProjectiveRestriction leftAssociated e
      embedding_injective centralizer_le
      ambient_eq_product intersection_eq
      rightAssociated).rightProjective =
        P.comap e :=
  rfl

@[simp]
theorem ofProjectiveRestriction_embedding
    (leftAssociated :
      AssociatedProjectiveRepresentation T V P)
    (e : B →* A)
    (embedding_injective : Function.Injective e)
    (centralizer_le :
      Subgroup.centralizer
          (T.normalSubgroup : Set A) ≤
        MonoidHom.range e)
    (ambient_eq_product :
      ∀ a : A,
        ∃ x : T.normalSubgroup,
          ∃ h : B, (x : A) * e h = a)
    (intersection_eq :
      T.normalSubgroup ⊓ MonoidHom.range e =
        U.normalSubgroup.map e)
    (rightAssociated :
      AssociatedProjectiveRepresentation U V
        (P.comap e)) :
    (ofProjectiveRestriction leftAssociated e
      embedding_injective centralizer_le
      ambient_eq_product intersection_eq
      rightAssociated).embedding =
        e :=
  rfl

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
