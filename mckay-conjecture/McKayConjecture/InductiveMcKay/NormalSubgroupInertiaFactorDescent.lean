/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InertiaQuotientIndex
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorQuotient
import McKayConjecture.CharacterTriple.Inertia
import McKayConjecture.GroupTheory.CentralExtensionSylowNormalizer
import McKayConjecture.GroupTheory.IntermediateQuotientSylowNormalizer
import McKayConjecture.InductiveMcKay.NormalSubgroupFactorExtension

/-!
# Central-index descent for inertia-factor extensions

Let `N ◁ G`, put `J = N Z(G)`, and choose
`θ ∈ Irr(J)`.  The canonical inertia triple has ambient group
`I_G(θ)` and normal subgroup the canonical copy of `J`.  Its quotient is
no larger than `G / J`.  If `N` is noncentral, this places the canonical
finite factor extension of the inertia triple strictly below `G` in
central index.

The file also names the quotient Sylow subgroup obtained from any ambient
Sylow subgroup contained in the inertia group, and its unique lift to the
factor extension.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupInertiaFactorDescent

open CharacterTriple
open CliffordEquivalence
open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (N : Subgroup G) [N.Normal]

/-- The inertia group of a character of `N Z(G)`. -/
abbrev inertia
    (θ : IrreducibleCharacter
      (NormalSubgroupJoinCenterReduction.joinCenter N)) :=
  IrreducibleCharacter.inertia
    (NormalSubgroupJoinCenterReduction.joinCenter N) θ

/-- The canonical character triple attached to that inertia group. -/
abbrev inertiaTriple
    (θ : IrreducibleCharacter
      (NormalSubgroupJoinCenterReduction.joinCenter N)) :
    CharacterTriple (inertia N θ) :=
  CharacterTriple.ofInertia
    (NormalSubgroupJoinCenterReduction.joinCenter N) θ

/-- The canonical finite factor-extension group of the inertia triple. -/
abbrev InertiaFactorExtensionGroup
    (θ : IrreducibleCharacter
      (NormalSubgroupJoinCenterReduction.joinCenter N)) :=
  AssociatedProjectiveRepresentation.CanonicalFiniteFactorCentralExtensionGroup
    (inertiaTriple N θ)

/-- The canonical central extension of the inertia quotient. -/
def inertiaFactorCentralExtension
    (θ : IrreducibleCharacter
      (NormalSubgroupJoinCenterReduction.joinCenter N)) :
    CentralExtension
      (InertiaFactorExtensionGroup N θ)
      (inertia N θ ⧸
        CliffordEquivalence.inertiaNormalCopy
          (NormalSubgroupJoinCenterReduction.joinCenter N) θ) :=
  AssociatedProjectiveRepresentation.canonicalFiniteFactorCentralExtension
    (inertiaTriple N θ)

/-- The inertia quotient is strictly below the ambient central index when
`N` is noncentral. -/
theorem card_inertia_quotient_lt_centralIndex
    (hNnoncentral : ¬N ≤ Subgroup.center G)
    (θ : IrreducibleCharacter
      (NormalSubgroupJoinCenterReduction.joinCenter N)) :
    Nat.card
        (inertia N θ ⧸
          CliffordEquivalence.inertiaNormalCopy
            (NormalSubgroupJoinCenterReduction.joinCenter N) θ) <
      centralIndex G :=
  (CliffordEquivalence.card_inertia_quotient_le_card_ambient_quotient
    (NormalSubgroupJoinCenterReduction.joinCenter N) θ).trans_lt
      (NormalSubgroupJoinCenterReduction.card_quotient_joinCenter_lt
        N hNnoncentral)

/-- Hence every canonical finite factor extension of an inertia triple is
available to the central-index induction hypothesis. -/
theorem centralIndex_inertiaFactorExtension_lt
    (hNnoncentral : ¬N ≤ Subgroup.center G)
    (θ : IrreducibleCharacter
      (NormalSubgroupJoinCenterReduction.joinCenter N)) :
    centralIndex (InertiaFactorExtensionGroup N θ) <
      centralIndex G :=
  (AssociatedGeneralExistence.associated
      (inertiaTriple N θ)
    ).associatedFiniteFactorCentralExtension_centralIndex_lt
      (card_inertia_quotient_lt_centralIndex
        N hNnoncentral θ)

/-- A Sylow subgroup contained in the inertia group, viewed internally. -/
abbrev inertiaSylow
    (P : Sylow p G)
    (θ : IrreducibleCharacter
      (NormalSubgroupJoinCenterReduction.joinCenter N))
    (hP :
      (P : Subgroup G) ≤ inertia N θ) :
    Sylow p (inertia N θ) :=
  P.subtype hP

/-- The image of the adapted Sylow subgroup in the inertia quotient. -/
abbrev inertiaQuotientSylow
    (P : Sylow p G)
    (θ : IrreducibleCharacter
      (NormalSubgroupJoinCenterReduction.joinCenter N))
    (hP :
      (P : Subgroup G) ≤ inertia N θ) :
    Sylow p
      (inertia N θ ⧸
        CliffordEquivalence.inertiaNormalCopy
          (NormalSubgroupJoinCenterReduction.joinCenter N) θ) :=
  GroupTheory.quotientSylowInIntermediate
    (inertia N θ)
    (NormalSubgroupJoinCenterReduction.joinCenter N)
    P
    (IrreducibleCharacter.subgroup_le_inertia
      (NormalSubgroupJoinCenterReduction.joinCenter N) θ)
    hP

/-- The unique Sylow lift of the quotient Sylow subgroup to the canonical
factor extension. -/
abbrev inertiaFactorExtensionSylow
    (P : Sylow p G)
    (θ : IrreducibleCharacter
      (NormalSubgroupJoinCenterReduction.joinCenter N))
    (hP :
      (P : Subgroup G) ≤ inertia N θ) :
    Sylow p (InertiaFactorExtensionGroup N θ) :=
  (inertiaFactorCentralExtension N θ).sylowLift
    (inertiaQuotientSylow N P θ hP)

end NormalSubgroupInertiaFactorDescent
end InductiveMcKay
end McKayConjecture
