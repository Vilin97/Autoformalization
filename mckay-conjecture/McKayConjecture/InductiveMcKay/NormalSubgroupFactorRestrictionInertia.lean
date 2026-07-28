/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorNormalizerRestriction
import McKayConjecture.InductiveMcKay.NormalSubgroupInertiaFactorDescent
import McKayConjecture.InductiveMcKay.NormalSubgroupIntermediateInertia

/-!
# Identifying the restricted factor triple with the target inertia group

For a `P`-fixed character `θ` of `J = N Z(G)`, the factor-extension
restriction API uses the full preimage in `I_G(θ)` of the normalizer of the
quotient Sylow subgroup.  The intermediate-inertia API describes the same
subgroup as `J_I N_I(P)`.

This file identifies the two presentations and composes that equality with
the identity-on-elements equivalence from the inertia group in
`J N_G(P)`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupFactorRestrictionInertia

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation
open NormalSubgroupInertiaFactorDescent
open NormalSubgroupIntermediateInertia

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G)
variable (N : Subgroup G) [N.Normal]

/-- The full quotient-normalizer preimage in the presentation used by the
fixed finite-factor restriction. -/
abbrev factorRestrictionPreimage
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ) :
    Subgroup (sourceInertia N θ) :=
  quotientSylowNormalizerPreimage
    (inertiaTriple N θ.1)
    (inertiaQuotientSylow N P θ.1 hP)

/-- The `J_I N_I(P)` and full quotient-normalizer-preimage presentations
are equal. -/
theorem quotientNormalizerPreimage_eq_factorRestrictionPreimage
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ) :
    NormalSubgroupIntermediateInertia.quotientNormalizerPreimage
        P N θ hP =
      factorRestrictionPreimage P N θ hP := by
  exact
    (GroupTheory.Sylow.comap_normalizer_mapQuotient_eq_preimage
      (NormalSubgroupInertiaFactorDescent.inertiaSylow
        N P θ.1 hP)
      (CliffordEquivalence.inertiaNormalCopy
        (joinCenter N) θ.1)).symm

/-- Canonical identity-on-elements equivalence from the target inertia
group in `J N_G(P)` to the ambient subgroup used by the restricted factor
triple. -/
def targetInertiaEquivFactorRestrictionPreimage
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ) :
    targetInertia P N θ ≃*
      factorRestrictionPreimage P N θ hP :=
  (targetInertiaEquivQuotientNormalizerPreimage
    P N θ hP).trans
      (MulEquiv.subgroupCongr
        (quotientNormalizerPreimage_eq_factorRestrictionPreimage
          P N θ hP))

@[simp]
theorem targetInertiaEquivFactorRestrictionPreimage_apply_coe
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ)
    (b : targetInertia P N θ) :
    (((targetInertiaEquivFactorRestrictionPreimage
        P N θ hP b :
      factorRestrictionPreimage P N θ hP) :
      sourceInertia N θ) :
      G) =
        (((b : targetInertia P N θ) :
          intermediate P N) :
          G) :=
  rfl

end NormalSubgroupFactorRestrictionInertia
end InductiveMcKay
end McKayConjecture
