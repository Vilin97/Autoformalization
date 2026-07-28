/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Transport
import McKayConjecture.CharacterTriple.CentralIsomorphism
import McKayConjecture.CharacterTriple.ProjectiveRestriction

/-!
# Restricting a character triple to an intermediate subgroup

If `N` is the normal subgroup of a character triple on `A` and `N ≤ B ≤ A`,
then `N` has a canonical copy `N.subgroupOf B` in `B`.  Its character is
obtained from the original character through the canonical equivalence
`N.subgroupOf B ≃* N`.

An associated projective representation restricts along `B.subtype` and
remains associated with this restricted triple.  Keeping this construction
literal is useful when the same normalized factor set is used on both the
ambient group and the intermediate subgroup.
-/

noncomputable section

universe u

open CategoryTheory

namespace McKayConjecture
namespace CharacterTriple

variable {A : Type u} [Finite A] [Group A]

/-- The canonical copy of the normal subgroup of `T` inside an intermediate
subgroup `B`. -/
abbrev normalSubgroupIn
    (T : CharacterTriple A) (B : Subgroup A) :
    Subgroup B :=
  T.normalSubgroup.subgroupOf B

/-- The canonical equivalence from the copy of the normal subgroup in `B`
back to the original normal subgroup. -/
abbrev normalSubgroupInEquiv
    (T : CharacterTriple A) (B : Subgroup A)
    (hNB : T.normalSubgroup ≤ B) :
    T.normalSubgroupIn B ≃* T.normalSubgroup :=
  Subgroup.subgroupOfEquivOfLe hNB

@[simp]
theorem normalSubgroupInEquiv_apply_coe
    (T : CharacterTriple A) (B : Subgroup A)
    (hNB : T.normalSubgroup ≤ B)
    (x : T.normalSubgroupIn B) :
    ((T.normalSubgroupInEquiv B hNB x :
        T.normalSubgroup) : A) =
      ((x : B) : A) :=
  rfl

/-- Restrict a character triple to an intermediate subgroup containing its
normal subgroup. -/
def restrictTo
    (T : CharacterTriple A) (B : Subgroup A)
    (hNB : T.normalSubgroup ≤ B) :
    CharacterTriple B where
  normalSubgroup := T.normalSubgroupIn B
  isNormal := T.isNormal.subgroupOf B
  character :=
    T.character.comap
      (T.normalSubgroupInEquiv B hNB)
  isInvariant := by
    intro b x
    change
      T.character.values
          (T.normalSubgroupInEquiv B hNB
            (conjugateNormalElement
              (T.normalSubgroupIn B)
              (T.isNormal.subgroupOf B) b x)) =
        T.character.values
          (T.normalSubgroupInEquiv B hNB x)
    exact
      T.isInvariant (b : A)
        (T.normalSubgroupInEquiv B hNB x)

@[simp]
theorem restrictTo_normalSubgroup
    (T : CharacterTriple A) (B : Subgroup A)
    (hNB : T.normalSubgroup ≤ B) :
    (T.restrictTo B hNB).normalSubgroup =
      T.normalSubgroupIn B :=
  rfl

@[simp]
theorem restrictTo_character_values
    (T : CharacterTriple A) (B : Subgroup A)
    (hNB : T.normalSubgroup ≤ B)
    (x : (T.restrictTo B hNB).normalSubgroup) :
    (T.restrictTo B hNB).character.values x =
      T.character.values
        (T.normalSubgroupInEquiv B hNB x) :=
  rfl

namespace AssociatedProjectiveRepresentation

variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- The ordinary normal-subgroup action of an associated lift after
restriction to `B`. -/
def restrictionTo
    (R : AssociatedProjectiveRepresentation T V P)
    (B : Subgroup A) (hNB : T.normalSubgroup ≤ B) :
    (T.restrictTo B hNB).normalSubgroup →*
      (V ≃ₗ[ℂ] V) :=
  R.restriction.comp
    (T.normalSubgroupInEquiv B hNB).toMonoidHom

@[simp]
theorem restrictionTo_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (B : Subgroup A) (hNB : T.normalSubgroup ≤ B)
    (x : (T.restrictTo B hNB).normalSubgroup) :
    R.restrictionTo B hNB x =
      (P.comap B.subtype).operator x := by
  change
    R.restriction
        (T.normalSubgroupInEquiv B hNB x) =
      P.operator ((x : B) : A)
  rw [R.restriction_apply]
  rfl

/-- Restrict an associated projective representation to an intermediate
subgroup containing the normal subgroup. -/
def restrictTo
    (R : AssociatedProjectiveRepresentation T V P)
    (B : Subgroup A) (hNB : T.normalSubgroup ≤ B) :
    AssociatedProjectiveRepresentation
      (T.restrictTo B hNB) V
      (P.comap B.subtype) where
  restriction := R.restrictionTo B hNB
  restriction_apply := R.restrictionTo_apply B hNB
  restriction_simple := by
    let E :
        FDRep ℂ T.normalSubgroup ≌
          FDRep ℂ (T.restrictTo B hNB).normalSubgroup :=
      Action.resEquiv (FGModuleCat ℂ)
        (T.normalSubgroupInEquiv B hNB)
    change Simple (E.functor.obj R.fdRestriction)
    exact CategoryTheory.simple_obj E.functor R.fdRestriction
  restriction_character := by
    funext x
    change
      LinearMap.trace ℂ V
          ((linearRepresentationOfAction
            (R.restriction.comp
              (T.normalSubgroupInEquiv B hNB).toMonoidHom)) x) =
        T.character.values
          (T.normalSubgroupInEquiv B hNB x)
    exact
      congrFun R.restriction_character
        (T.normalSubgroupInEquiv B hNB x)
  normal_mul := by
    intro x b
    change
      P.operator (((x : B) : A) * (b : A)) =
        P.operator ((x : B) : A) *
          P.operator (b : A)
    exact
      R.normal_mul
        (T.normalSubgroupInEquiv B hNB x) (b : A)
  mul_normal := by
    intro b x
    change
      P.operator ((b : A) * ((x : B) : A)) =
        P.operator (b : A) *
          P.operator ((x : B) : A)
    exact
      R.mul_normal (b : A)
        (T.normalSubgroupInEquiv B hNB x)

@[simp]
theorem restrictTo_restriction_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (B : Subgroup A) (hNB : T.normalSubgroup ≤ B)
    (x : (T.restrictTo B hNB).normalSubgroup) :
    (R.restrictTo B hNB).restriction x =
      R.restriction
        (T.normalSubgroupInEquiv B hNB x) :=
  rfl

end AssociatedProjectiveRepresentation

end CharacterTriple
end McKayConjecture
