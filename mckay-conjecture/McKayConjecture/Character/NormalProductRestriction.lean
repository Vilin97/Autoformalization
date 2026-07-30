/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Extension
import McKayConjecture.CharacterTriple.AssociatedGeneralExistence
import McKayConjecture.CharacterTriple.AssociatedOperatorTransport
import McKayConjecture.InductiveMcKay.CentralTripleFactorMatchedCharacterEquiv

/-!
# Restriction across a normal product

Let `N` be normal in `G`, let `V ≤ G`, and suppose `N ⊔ V = ⊤`.  If an
invariant irreducible character `α` of `N` restricts irreducibly to a
character `β` of `N ∩ V`, then restriction gives an equivalence

`Irr(G | α) ≃ Irr(V | β)`.

The intersection is represented canonically as `N.subgroupOf V`.  The proof
restricts a canonical associated projective representation from `G` to `V`.
The two associated lifts have literally equal factor sets, so the existing
factor-matched character-triple correspondence applies.  The final theorem
records that this correspondence is ordinary character restriction on
values.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple

open InductiveMcKay

variable {G : Type} [Finite G] [Group G]

/-- The canonical inclusion `N ∩ V → N`, where the intersection is
represented as `N.subgroupOf V`. -/
def normalIntersectionInclusion (N V : Subgroup G) :
    N.subgroupOf V →* N where
  toFun x := ⟨(x : V), x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite G] in
@[simp]
theorem normalIntersectionInclusion_coe
    (N V : Subgroup G) (x : N.subgroupOf V) :
    ((normalIntersectionInclusion N V x : N) : G) =
      ((x : V) : G) :=
  rfl

/-- Restrict a character triple to `V` when its distinguished character
restricts irreducibly to `N ∩ V`.

The hypothesis `hβ` is the value-level assertion that `β` is the
restriction of `T.character` along the canonical inclusion `N ∩ V → N`.
-/
def restrictToIntersection
    (T : CharacterTriple G) (V : Subgroup G)
    (β : IrreducibleCharacter (T.normalSubgroup.subgroupOf V))
    (hβ : IrreducibleCharacter.IsExtensionAlong
      (normalIntersectionInclusion T.normalSubgroup V)
      β T.character) :
    CharacterTriple V where
  normalSubgroup := T.normalSubgroup.subgroupOf V
  isNormal := T.isNormal.subgroupOf V
  character := β
  isInvariant := by
    intro v x
    calc
      β.values (conjugateNormalElement _ _ v x) =
          T.character.values
            (normalIntersectionInclusion T.normalSubgroup V
              (conjugateNormalElement _ _ v x)) :=
        (hβ _).symm
      _ = T.character.values
          (conjugateNormalElement T.normalSubgroup T.isNormal
            (v : G)
            (normalIntersectionInclusion T.normalSubgroup V x)) := by
        congr 2
      _ = T.character.values
          (normalIntersectionInclusion T.normalSubgroup V x) :=
        T.isInvariant _ _
      _ = β.values x := hβ x

@[simp]
theorem restrictToIntersection_normalSubgroup
    (T : CharacterTriple G) (V : Subgroup G)
    (β : IrreducibleCharacter (T.normalSubgroup.subgroupOf V))
    (hβ : IrreducibleCharacter.IsExtensionAlong
      (normalIntersectionInclusion T.normalSubgroup V)
      β T.character) :
    (T.restrictToIntersection V β hβ).normalSubgroup =
      T.normalSubgroup.subgroupOf V :=
  rfl

@[simp]
theorem restrictToIntersection_character
    (T : CharacterTriple G) (V : Subgroup G)
    (β : IrreducibleCharacter (T.normalSubgroup.subgroupOf V))
    (hβ : IrreducibleCharacter.IsExtensionAlong
      (normalIntersectionInclusion T.normalSubgroup V)
      β T.character) :
    (T.restrictToIntersection V β hβ).character = β :=
  rfl

namespace AssociatedProjectiveRepresentation

variable {T : CharacterTriple G}
variable {X : Type}
variable [AddCommGroup X] [Module ℂ X]
  [Module.Finite ℂ X] [Nontrivial X]
variable {P : ProjectiveRepresentation ℂ G X}

/-- Restrict an associated projective representation to the intersection
triple on `V`.

The normal multiplication laws and trace identity are inherited literally
from the original associated lift.
-/
def restrictToIntersection
    (R : AssociatedProjectiveRepresentation T X P)
    (V : Subgroup G)
    (β : IrreducibleCharacter (T.normalSubgroup.subgroupOf V))
    (hβ : IrreducibleCharacter.IsExtensionAlong
      (normalIntersectionInclusion T.normalSubgroup V)
      β T.character) :
    AssociatedProjectiveRepresentation
      (T.restrictToIntersection V β hβ)
      X (P.comap V.subtype) :=
  AssociatedProjectiveRepresentation.ofFactorNormalAndTrace
    (fun x v => by
      change
        P.factor
            (((x : T.normalSubgroup.subgroupOf V) : V) : G)
            (v : G) =
          1
      exact
        R.factor_normal_left
          (normalIntersectionInclusion T.normalSubgroup V x)
          (v : G))
    (fun v x => by
      change
        P.factor
            (v : G)
            (((x : T.normalSubgroup.subgroupOf V) : V) : G) =
          1
      exact
        R.factor_normal_right
          (v : G)
          (normalIntersectionInclusion T.normalSubgroup V x))
    (fun x => by
      change
        LinearMap.trace ℂ X
            (P.operator
                (((x : T.normalSubgroup.subgroupOf V) : V) : G) :
              X →ₗ[ℂ] X) =
          β.values x
      rw [← hβ x]
      exact
        R.traceFunction_normal
          (normalIntersectionInclusion T.normalSubgroup V x))

end AssociatedProjectiveRepresentation

section NormalProductEquivalence

variable (T : CharacterTriple G) (V : Subgroup G)
variable (β : IrreducibleCharacter (T.normalSubgroup.subgroupOf V))
variable (hβ : IrreducibleCharacter.IsExtensionAlong
  (normalIntersectionInclusion T.normalSubgroup V)
  β T.character)

private theorem factorMatchedRestrictionGroupData
    (hsup : T.normalSubgroup ⊔ V = ⊤) :
    FactorMatchedRestrictionGroupData
      T (T.restrictToIntersection V β hβ) V.subtype where
  embedding_injective := Subtype.coe_injective
  ambient_eq_product := by
    intro a
    have ha : a ∈ T.normalSubgroup ⊔ V := by
      rw [hsup]
      trivial
    obtain ⟨n, hn, v, hv, hnv⟩ :=
      Subgroup.mem_sup_of_normal_left.mp ha
    exact ⟨⟨n, hn⟩, ⟨v, hv⟩, hnv⟩
  intersection_eq := by
    change
      T.normalSubgroup ⊓ MonoidHom.range V.subtype =
        (T.normalSubgroup.subgroupOf V).map V.subtype
    rw [V.range_subtype, Subgroup.subgroupOf_map_subtype]

variable {X : Type}
variable [AddCommGroup X] [Module ℂ X]
  [Module.Finite ℂ X] [Nontrivial X]
variable {P : ProjectiveRepresentation ℂ G X}

private def factorMatchedProjectiveComparisonData
    (R : AssociatedProjectiveRepresentation T X P) :
    CompleteFactorMatchedProjectiveComparisonData
      T (T.restrictToIntersection V β hβ) V.subtype where
  leftSpace := X
  rightSpace := X
  leftProjective := P
  leftAssociated := R
  rightProjective := P.comap V.subtype
  rightAssociated := R.restrictToIntersection V β hβ
  factor_agreement := by
    intro _ _
    rfl

private def factorMatchedWitness
    (R : AssociatedProjectiveRepresentation T X P)
    (hsup : T.normalSubgroup ⊔ V = ⊤) :
    FactorMatchedIsomorphismWitness
      T (T.restrictToIntersection V β hβ) X X :=
  ((factorMatchedProjectiveComparisonData T V β hβ R)
    |>.toCompleteFactorMatchedIsomorphismWitness
      (factorMatchedRestrictionGroupData T V β hβ hsup)).witness

private def restrictionOverEquivWith
    (R : AssociatedProjectiveRepresentation T X P)
    (hsup : T.normalSubgroup ⊔ V = ⊤) :
    CliffordCorrespondence.IrreducibleCharactersOverAlong
        T.normalSubgroup.subtype T.character ≃
      CliffordCorrespondence.IrreducibleCharactersOverAlong
        (T.normalSubgroup.subgroupOf V).subtype β := by
  change
    CliffordCorrespondence.IrreducibleCharactersOverAlong
        T.normalSubgroup.subtype T.character ≃
      CliffordCorrespondence.IrreducibleCharactersOverAlong
        (T.restrictToIntersection V β hβ).normalSubgroup.subtype
        (T.restrictToIntersection V β hβ).character
  exact
    (factorMatchedWitness T V β hβ R hsup)
      |>.irreducibleCharactersOverEquiv

/-- Normal-product restriction equivalence.

If `T.normalSubgroup ⊔ V = ⊤` and `T.character` restricts irreducibly to
`β` on `T.normalSubgroup.subgroupOf V`, then ordinary character restriction
gives an equivalence between the two fibres.
-/
def restrictionOverEquiv_of_normal_sup_eq_top
    (hsup : T.normalSubgroup ⊔ V = ⊤) :
    CliffordCorrespondence.IrreducibleCharactersOverAlong
        T.normalSubgroup.subtype T.character ≃
      CliffordCorrespondence.IrreducibleCharactersOverAlong
        (T.normalSubgroup.subgroupOf V).subtype β :=
  restrictionOverEquivWith T V β hβ
    (AssociatedGeneralExistence.associated T) hsup

/-- The normal-product correspondence is literal restriction of character
values from `G` to `V`. -/
@[simp]
theorem restrictionOverEquiv_of_normal_sup_eq_top_apply_values
    (hsup : T.normalSubgroup ⊔ V = ⊤)
    (χ : CliffordCorrespondence.IrreducibleCharactersOverAlong
      T.normalSubgroup.subtype T.character)
    (v : V) :
    ((restrictionOverEquiv_of_normal_sup_eq_top
      T V β hβ hsup χ).1).values v =
      χ.1.values (v : G) := by
  let C :=
    factorMatchedWitness T V β hβ
      (AssociatedGeneralExistence.associated T) hsup
  change
    (C.rightMultiplicityCharacter χ.1 χ.2).values v =
      χ.1.values (v : G)
  rw [C.rightMultiplicityCharacter_values]
  calc
    (C.rightMultiplicityFDRep χ.1 χ.2).character v =
        (C.leftTensorRepresentation
          (C.leftMultiplicityProjective χ.1)
          (C.leftMultiplicity_hasInverseFactorSet χ.1)).character
            (v : G) := by
      rfl
    _ = χ.1.realization.character (v : G) :=
      congrFun
        (Representation.char_iso
          (C.leftMultiplicityEvaluationEquiv χ.1 χ.2))
        (v : G)
    _ = χ.1.values (v : G) :=
      congrFun χ.1.realization_character (v : G)

end NormalProductEquivalence

end CharacterTriple
end McKayConjecture
