/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralCorrespondence
import McKayConjecture.InductiveMcKay.LayerProjectiveRestrictionAssembly

/-!
# Association criteria for a restricted layer projective lift

This file determines exactly what is needed for the literal projective
restriction construction in `LayerProjectiveRestrictionAssembly`.

The group conditions in `CentralRestrictionGroupData` canonically map the
right normal subgroup into the left normal subgroup.  Consequently, once a
left projective lift is associated, both normal-subgroup multiplication laws
for its pullback are automatic.  Equality of its character with the right
triple character also implies simplicity by the character norm criterion.
Thus only that exact character equality remains.

This equality cannot in general be deduced from componentwise central
witnesses.  A literal restriction uses the same vector space on both sides,
so its existence forces equality of the two character degrees.  The
inductive-McKay correspondence does not assert degree preservation.  The
final theorem expresses this obstruction for the layer correspondence as an
equality between the products of source and target coordinate degrees.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open GroupTheory
open CategoryTheory

variable {A : Type} {B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}

namespace CentralRestrictionGroupData

/-- The right normal subgroup maps into the left normal subgroup. -/
theorem map_rightNormal_le_leftNormal
    (g : CentralRestrictionGroupData T U e) :
    U.normalSubgroup.map e ≤ T.normalSubgroup := by
  rw [← g.intersection_eq]
  exact inf_le_left

/-- The normal-subgroup homomorphism underlying projective restriction. -/
def normalMap
    (g : CentralRestrictionGroupData T U e) :
    U.normalSubgroup →* T.normalSubgroup :=
  (e.comp U.normalSubgroup.subtype).codRestrict
    T.normalSubgroup
    (fun x ↦
      g.map_rightNormal_le_leftNormal
        ⟨(x : B), x.property, rfl⟩)

@[simp]
theorem normalMap_coe
    (g : CentralRestrictionGroupData T U e)
    (x : U.normalSubgroup) :
    ((g.normalMap x : T.normalSubgroup) : A) =
      e (x : B) :=
  rfl

end CentralRestrictionGroupData

namespace RestrictedAssociated

variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- The ordinary normal-subgroup action obtained by pulling an associated
left restriction through the normal map supplied by the group data. -/
def normalRestriction
    (R : AssociatedProjectiveRepresentation T V P)
    (g : CentralRestrictionGroupData T U e) :
    U.normalSubgroup →* (V ≃ₗ[ℂ] V) :=
  R.restriction.comp g.normalMap

@[simp]
theorem normalRestriction_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (g : CentralRestrictionGroupData T U e)
    (x : U.normalSubgroup) :
    normalRestriction R g x =
      (P.comap e).operator x := by
  change R.restriction (g.normalMap x) = P.operator (e (x : B))
  rw [R.restriction_apply, g.normalMap_coe]

/-- The left normal-subgroup multiplication law descends automatically to
the literal pullback. -/
theorem comap_normal_mul
    (R : AssociatedProjectiveRepresentation T V P)
    (g : CentralRestrictionGroupData T U e)
    (x : U.normalSubgroup)
    (b : B) :
    (P.comap e).operator ((x : B) * b) =
      (P.comap e).operator x * (P.comap e).operator b := by
  change P.operator (e ((x : B) * b)) =
    P.operator (e (x : B)) * P.operator (e b)
  rw [map_mul, ← g.normalMap_coe x]
  exact R.normal_mul (g.normalMap x) (e b)

/-- The right normal-subgroup multiplication law descends automatically to
the literal pullback. -/
theorem comap_mul_normal
    (R : AssociatedProjectiveRepresentation T V P)
    (g : CentralRestrictionGroupData T U e)
    (b : B)
    (x : U.normalSubgroup) :
    (P.comap e).operator (b * (x : B)) =
      (P.comap e).operator b * (P.comap e).operator x := by
  change P.operator (e (b * (x : B))) =
    P.operator (e b) * P.operator (e (x : B))
  rw [map_mul, ← g.normalMap_coe x]
  exact R.mul_normal (e b) (g.normalMap x)

/-- If the concrete pulled normal action affords the irreducible target
character, then it is simple. -/
theorem normalRestriction_simple_of_character
    (R : AssociatedProjectiveRepresentation T V P)
    (g : CentralRestrictionGroupData T U e)
    (hcharacter :
      (FDRep.of
          (linearRepresentationOfAction
            (normalRestriction R g))).character =
        U.character.values) :
    Simple
      (FDRep.of
        (linearRepresentationOfAction
          (normalRestriction R g))) := by
  letI : Fintype U.normalSubgroup :=
    Fintype.ofFinite U.normalSubgroup
  rw [FDRep.simple_iff_char_is_norm_one]
  have hsimple : Simple U.character.realization :=
    inferInstance
  have hnorm :=
    (FDRep.simple_iff_char_is_norm_one
      U.character.realization).mp hsimple
  rw [hcharacter, ← U.character.realization_character]
  exact hnorm

/-- Construct association for a literal projective restriction from the one
fact which is not a consequence of the left association and the group data:
the target character of the concrete pulled normal action. -/
def comapOfNormalRestriction
    (R : AssociatedProjectiveRepresentation T V P)
    (g : CentralRestrictionGroupData T U e)
    (hcharacter :
      (FDRep.of
          (linearRepresentationOfAction
            (normalRestriction R g))).character =
        U.character.values) :
    AssociatedProjectiveRepresentation U V (P.comap e) where
  restriction := normalRestriction R g
  restriction_apply := normalRestriction_apply R g
  restriction_simple :=
    normalRestriction_simple_of_character R g hcharacter
  restriction_character := hcharacter
  normal_mul := comap_normal_mul R g
  mul_normal := comap_mul_normal R g

/-- The target-character law alone already forces equality of the source and
target degrees. -/
theorem character_degree_eq_of_normalRestriction_character
    (R : AssociatedProjectiveRepresentation T V P)
    (g : CentralRestrictionGroupData T U e)
    (hcharacter :
      (FDRep.of
          (linearRepresentationOfAction
            (normalRestriction R g))).character =
        U.character.values) :
    T.character.degree = U.character.degree := by
  rw [← R.finrank_eq_character_degree]
  apply Nat.cast_injective (R := ℂ)
  have h := congrFun hcharacter (1 : U.normalSubgroup)
  simpa only [FDRep.char_one, IrreducibleCharacter.value_one] using h

/-- A literal associated restriction forces equality of the source and
target normal-character degrees. -/
theorem character_degree_eq_of_associated_comap
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U V (P.comap e)) :
    T.character.degree = U.character.degree := by
  rw [← R.finrank_eq_character_degree,
    ← S.finrank_eq_character_degree]

end RestrictedAssociated

namespace CompleteAssociatedProjectiveLift

variable {V : Type}

/-- The concrete normal action of a bundled associated lift along fixed
central-restriction group data. -/
def restrictedNormalAction
    (R : CompleteAssociatedProjectiveLift T)
    (g : CentralRestrictionGroupData T U e) :
    U.normalSubgroup →*
      (R.space ≃ₗ[ℂ] R.space) :=
  RestrictedAssociated.normalRestriction
    R.associated g

/-- Build complete projective-restriction data from the exact simplicity and
character laws of the concrete restricted normal action. -/
def toCompleteProjectiveRestrictionData
    (R : CompleteAssociatedProjectiveLift T)
    (g : CentralRestrictionGroupData T U e)
    (hcharacter :
      (FDRep.of
          (linearRepresentationOfAction
            (R.restrictedNormalAction g))).character =
        U.character.values) :
    CompleteProjectiveRestrictionData T U e where
  space := R.space
  addCommGroup := R.addCommGroup
  module := R.module
  moduleFinite := R.moduleFinite
  nontrivial := R.nontrivial
  projective := R.projective
  leftAssociated := R.associated
  rightAssociated :=
    RestrictedAssociated.comapOfNormalRestriction
      R.associated g hcharacter

end CompleteAssociatedProjectiveLift

/-! ### The layer degree obstruction -/

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}
variable {D : LayerSylowCoordinateData G p Q}

namespace LayerProjectiveRestrictionAssembly

noncomputable local instance
    layerProjectiveRestrictionAssociationFintypeComponentIndex :
    Fintype (ComponentIndex G) :=
  Fintype.ofFinite (ComponentIndex G)

/-- The associated source lift stored in a two-sided coordinate assembly. -/
abbrev MatchedCoordinatePermutationProjectiveAssembly.sourceLift
    {d : ComponentOrbitLocalData D}
    {hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder}
    {θ : PPrimeIrreducibleCharacter (layer G) p}
    (A :
      MatchedCoordinatePermutationProjectiveAssembly
        d hcoordinate θ) :
    CompleteAssociatedProjectiveLift (sourceTriple θ) :=
  A.charts.sourceAssembly.sourceLift

/-- Exact construction of projective-restriction data from a two-sided chart
assembly and the genuinely additional normal-restriction character law. -/
def MatchedCoordinatePermutationProjectiveAssembly.toCompleteProjectiveRestrictionData
    {d : ComponentOrbitLocalData D}
    {hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder}
    {θ : PPrimeIrreducibleCharacter (layer G) p}
    (A :
      MatchedCoordinatePermutationProjectiveAssembly
        d hcoordinate θ)
    (g :
      CentralRestrictionGroupData
        (sourceTriple θ) (targetTriple d θ)
        (inertiaEmbedding d hcoordinate θ))
    (hcharacter :
      (FDRep.of
          (linearRepresentationOfAction
            (CompleteAssociatedProjectiveLift.restrictedNormalAction
              A.sourceLift g))).character =
        (targetTriple d θ).character.values) :
    CompleteProjectiveRestrictionData
      (sourceTriple θ) (targetTriple d θ)
      (inertiaEmbedding d hcoordinate θ) :=
  CompleteAssociatedProjectiveLift.toCompleteProjectiveRestrictionData
    A.sourceLift g hcharacter

/-- In coordinate form, the target-character law for a literal restriction
forces equality of the products of source and target component degrees.  This
equality is not part of `LocalInductiveMcKayData`. -/
theorem normalRestrictionCharacter_coordinate_degree_eq
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (R : CompleteAssociatedProjectiveLift (sourceTriple θ))
    (g :
      CentralRestrictionGroupData
        (sourceTriple θ) (targetTriple d θ)
        (inertiaEmbedding d hcoordinate θ))
    (hcharacter :
      (FDRep.of
          (linearRepresentationOfAction
            (CompleteAssociatedProjectiveLift.restrictedNormalAction
              R g))).character =
        (targetTriple d θ).character.values) :
    ∏ K,
        (((layerPPrimeCharacterEquiv G p).symm θ).1 K).1.degree =
      ∏ K,
        (d.correspondence K
          (((layerPPrimeCharacterEquiv G p).symm θ).1 K)).1.degree := by
  have hdegree :=
    RestrictedAssociated.character_degree_eq_of_normalRestriction_character
      R.associated g hcharacter
  change
    (CliffordEquivalence.inertiaCopyCharacter (layer G) θ.1).degree =
      (CliffordEquivalence.inertiaCopyCharacter
        d.intermediateComponentLocal
        (d.intermediateComponentLocalPPrimeCharacterEquiv θ).1).degree
    at hdegree
  rw [CliffordEquivalence.inertiaCopyCharacter,
    IrreducibleCharacter.comap_degree,
    CliffordEquivalence.inertiaCopyCharacter,
    IrreducibleCharacter.comap_degree,
    d.intermediateComponentLocalPPrimeCharacterEquiv_degree] at hdegree
  have hsource :=
    layerPPrimeCharacterEquiv_degree
      G p ((layerPPrimeCharacterEquiv G p).symm θ)
  rw [Equiv.apply_symm_apply] at hsource
  exact hsource.symm.trans hdegree

section CanonicalIntersection

variable {P : Sylow p G}
variable
  {D :
    LayerSylowCoordinateData G p
      (layerSylowIntersection P)}

/-- The canonical group data used by the literal restriction criterion in a
minimal counterexample. -/
abbrev minimalCounterexampleRestrictionGroupData
    (d : ComponentOrbitLocalData D)
    (hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder)
    (hminimal : MinimalCounterexampleStructure P)
    (θ : PPrimeIrreducibleCharacter (layer G) p) :=
  d.layerIntermediateInertiaRestrictionGroupData_of_minimalCounterexample
    hcoordinate hminimal θ

/-- Once the exact character law is supplied, all remaining
minimal-counterexample central-witness fields are constructed.  Simplicity
and both multiplication laws are theorems. -/
def MatchedCoordinatePermutationProjectiveAssembly.toCompleteCentralWitness_of_minimalCounterexample
    {d : ComponentOrbitLocalData D}
    {hcoordinate :
      d.toLayerComponentLocalData.IsCoordinateCorrespondenceEquivariant
        d.isConjugationEquivariantUnder}
    {θ : PPrimeIrreducibleCharacter (layer G) p}
    (A :
      MatchedCoordinatePermutationProjectiveAssembly
        d hcoordinate θ)
    (hminimal : MinimalCounterexampleStructure P)
    (hcharacter :
      (FDRep.of
          (linearRepresentationOfAction
            (CompleteAssociatedProjectiveLift.restrictedNormalAction
              A.sourceLift
              (minimalCounterexampleRestrictionGroupData
                d hcoordinate hminimal θ)))).character =
        (targetTriple d θ).character.values) :
    CompleteCentralIsomorphismWitness
      (sourceTriple θ) (targetTriple d θ) := by
  let g :=
    minimalCounterexampleRestrictionGroupData
      d hcoordinate hminimal θ
  exact
    (A.toCompleteProjectiveRestrictionData
      g hcharacter).toCompleteCentralIsomorphismWitness g

end CanonicalIntersection

end LayerProjectiveRestrictionAssembly

end InductiveMcKay
end McKayConjecture
