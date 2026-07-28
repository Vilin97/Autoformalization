/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OverAlongTransport
import McKayConjecture.InductiveMcKay.NormalSubgroupFactorRestrictionInertia
import McKayConjecture.InductiveMcKay.NormalSubgroupRestrictedFactorCharacterEquiv

/-!
# Transport from a restricted inertia triple to the target inertia group

The full preimage of the quotient-Sylow normalizer and the target inertia
group are canonically the same abstract group.  This file records that their
canonical normal-subgroup copies and normal characters agree under the
identity-on-elements equivalence, and transports the corresponding
prime-to-`p` character fibres.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupRestrictedFactorInertiaTransport

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation
open CliffordCorrespondence
open NormalSubgroupFactorRestrictionInertia
open NormalSubgroupAssociatedFactorFibre
open NormalSubgroupInertiaFactorDescent
open NormalSubgroupIntermediateInertia
open NormalSubgroupRestrictedFactorFibre

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G)
variable (N : Subgroup G) [N.Normal]

/-- The canonical target inertia triple. -/
abbrev TargetInertiaTriple
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p) :
    CharacterTriple (targetInertia P N θ) :=
  CharacterTriple.ofInertia
    (internalJoinCenter P N)
    (internalCharacterEquiv P N θ).1

/-- The literally restricted source inertia triple. -/
abbrev RestrictedInertiaTriple
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ) :
    CharacterTriple (factorRestrictionPreimage P N θ hP) :=
  RestrictedTriple
    (inertiaTriple N θ.1)
    (inertiaQuotientSylow N P θ.1 hP)

/-- The ambient identity-on-elements equivalence maps the target normal copy
onto the normal copy in the restricted source triple. -/
theorem map_targetNormalSubgroup_eq_restrictedNormalSubgroup
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ) :
    Subgroup.map
        (targetInertiaEquivFactorRestrictionPreimage
          P N θ hP).toMonoidHom
        (TargetInertiaTriple P N θ).normalSubgroup =
      (RestrictedInertiaTriple P N θ hP).normalSubgroup := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    refine
      ⟨(targetInertiaEquivFactorRestrictionPreimage
          P N θ hP).symm x, ?_, ?_⟩
    · exact hx
    · exact
        (targetInertiaEquivFactorRestrictionPreimage
          P N θ hP).apply_symm_apply x

/-- The identity-on-elements equivalence between the normal copies inside
the target and restricted inertia groups. -/
def targetNormalEquivRestrictedNormal
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ) :
    (TargetInertiaTriple P N θ).normalSubgroup ≃*
      (RestrictedInertiaTriple P N θ hP).normalSubgroup :=
  (MulEquiv.subgroupMap
      (targetInertiaEquivFactorRestrictionPreimage
        P N θ hP)
      (TargetInertiaTriple P N θ).normalSubgroup).trans
    (MulEquiv.subgroupCongr
      (map_targetNormalSubgroup_eq_restrictedNormalSubgroup
        P N θ hP))

@[simp]
theorem targetNormalEquivRestrictedNormal_apply_coe
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ)
    (x : (TargetInertiaTriple P N θ).normalSubgroup) :
    (((targetNormalEquivRestrictedNormal P N θ hP x :
        (RestrictedInertiaTriple P N θ hP).normalSubgroup) :
      factorRestrictionPreimage P N θ hP)) =
        targetInertiaEquivFactorRestrictionPreimage
          P N θ hP (x : targetInertia P N θ) :=
  rfl

/-- The ambient and normal-copy equivalences form a commuting square with
the two subgroup inclusions. -/
theorem targetRestriction_commutes
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ) :
    (targetInertiaEquivFactorRestrictionPreimage
        P N θ hP).toMonoidHom.comp
        (TargetInertiaTriple P N θ).normalSubgroup.subtype =
      (RestrictedInertiaTriple P N θ hP).normalSubgroup.subtype.comp
        (targetNormalEquivRestrictedNormal
          P N θ hP).toMonoidHom := by
  ext x
  rfl

/-- The restricted source normal character pulls back to the target normal
character under the identity-on-elements normal-copy equivalence. -/
theorem restrictedCharacter_comap_targetNormalEquiv
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ) :
    (RestrictedInertiaTriple P N θ hP).character.comap
        (targetNormalEquivRestrictedNormal P N θ hP) =
      (TargetInertiaTriple P N θ).character := by
  apply IrreducibleCharacter.ext
  funext x
  rfl

/-- Relabelling both the ambient group and its normal copy identifies
ordinary prime-to-`p` character fibres of the restricted and target
triples. -/
def restrictedPPrimeCharactersEquivTargetTriple
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ) :
    PPrimeCharactersOver
        (RestrictedInertiaTriple P N θ hP) p ≃
      PPrimeCharactersOver
        (TargetInertiaTriple P N θ) p := by
  let E :=
    pPrimeIrreducibleCharactersOverAlongComapEquiv
        (targetInertiaEquivFactorRestrictionPreimage
          P N θ hP)
        (targetNormalEquivRestrictedNormal P N θ hP)
        (RestrictedInertiaTriple P N θ hP).normalSubgroup.subtype
        (TargetInertiaTriple P N θ).normalSubgroup.subtype
        (targetRestriction_commutes P N θ hP)
        (RestrictedInertiaTriple P N θ hP).character
        p
  rw [restrictedCharacter_comap_targetNormalEquiv P N θ hP] at E
  exact E

/-- The restricted ordinary character fibre is the usual inertia fibre in
the target intermediate group. -/
def restrictedPPrimeCharactersEquivTargetInertia
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ) :
    PPrimeCharactersOver
        (RestrictedInertiaTriple P N θ hP) p ≃
      PPrimeIrreducibleCharactersOverInertia
        (internalJoinCenter P N)
        (internalCharacterEquiv P N θ).1 p :=
  (restrictedPPrimeCharactersEquivTargetTriple
      P N θ hP).trans
    (pPrimeIrreducibleCharactersOverInertiaEquivTriple
        (internalJoinCenter P N)
        (internalCharacterEquiv P N θ).1 p).symm

/-- Restricting the inertia triple does not change the degree of its normal
character, so the prime-to-`p` hypothesis is inherited from `θ`. -/
theorem restrictedInertiaTriple_character_isPPrimeDegree
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ) :
    (RestrictedInertiaTriple P N θ hP).character.IsPPrimeDegree p := by
  exact θ.2

/-- The inverse-coefficient fibre in the literal fixed restricted extension
is canonically the ordinary target inertia fibre. -/
def restrictedInverseCoefficientFibreEquivTargetInertia
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ) :
    RestrictedPPrimeInverseCoefficientFibre
        (inertiaTriple N θ.1)
        (inertiaQuotientSylow N P θ.1 hP) ≃
      PPrimeIrreducibleCharactersOverInertia
        (internalJoinCenter P N)
        (internalCharacterEquiv P N θ).1 p :=
  (restrictedFixedFiniteFactorPPrimeCharacterEquiv
      (inertiaTriple N θ.1)
      (inertiaQuotientSylow N P θ.1 hP)
      (restrictedInertiaTriple_character_isPPrimeDegree
        P N θ hP)).symm.trans
    (restrictedPPrimeCharactersEquivTargetInertia
      P N θ hP)

end NormalSubgroupRestrictedFactorInertiaTransport
end InductiveMcKay
end McKayConjecture
